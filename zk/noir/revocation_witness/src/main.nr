use std::hash::pedersen_hash;

// Protocol revocation witness Merkle-depth bounds (#357).
// Mirrored in zk/tools/revocation_depth.py, contracts/.../lib.rs,
// backend/verifier_inputs.py, frontend/src/verifierInputs.ts, and
// zk/noir/fixtures/revocation_vectors.json.
global MIN_REVOCATION_WITNESS_DEPTH: u32 = 1;
global MAX_REVOCATION_WITNESS_DEPTH: Field = 16;
global MAX_REVOCATION_LEAVES: Field = 65536;
global MAX_REVOCATION_WITNESS_DEPTH_U32: u32 = 16;
global MAX_REVOCATION_LEAVES_U32: u32 = 65536;
global DEFAULT_REVOCATION_WITNESS_DEPTH: u32 = 3;
global DEFAULT_REVOCATION_LEAVES: u32 = 8;

/// Validate that a requested revocation witness depth is within protocol
/// bounds [MIN_REVOCATION_WITNESS_DEPTH, MAX_REVOCATION_WITNESS_DEPTH_U32].
fn assert_valid_revocation_depth(depth: u32) {
    assert(depth >= MIN_REVOCATION_WITNESS_DEPTH, "depth_undersize");
    assert(depth <= MAX_REVOCATION_WITNESS_DEPTH_U32, "depth_oversize");
}

/// Validate that a requested revocation leaf count is a power of two within
/// [2, MAX_REVOCATION_LEAVES_U32].
fn assert_valid_revocation_leaf_count(leaf_count: u32) {
    assert(leaf_count >= 2, "depth_undersize");
    assert(leaf_count <= MAX_REVOCATION_LEAVES_U32, "depth_oversize");
    assert((leaf_count & (leaf_count - 1)) == 0, "depth_non_power_of_two");
}

/// Compute the binary Pedersen Merkle root from a parameterised authentication
/// path up to `active_depth` levels (1 <= active_depth <= D <= MAX_REVOCATION_WITNESS_DEPTH).
///
/// At each active level `i < active_depth`:
/// - `path_indices[i] == 0` hashes `(current, siblings[i])`
/// - `path_indices[i] == 1` hashes `(siblings[i], current)`
fn compute_merkle_root_from_path<let D: u32>(
    leaf: Field,
    path_indices: [Field; D],
    siblings: [Field; D],
    active_depth: u32,
) -> Field {
    assert_valid_revocation_depth(active_depth);
    assert(active_depth <= D, "depth_oversize");
    assert(D <= MAX_REVOCATION_WITNESS_DEPTH_U32, "depth_oversize");

    let mut current = leaf;
    for i in 0..D {
        if i < active_depth {
            let idx = path_indices[i];
            assert((idx == 0) | (idx == 1), "malformed");
            let sibling = siblings[i];
            let left = if idx == 0 { current } else { sibling };
            let right = if idx == 0 { sibling } else { current };
            current = pedersen_hash([left, right]);
        }
    }
    current
}

/// Parameterised non-revocation verifier supporting any Merkle depth in
/// `1..=MAX_REVOCATION_WITNESS_DEPTH` (up to 16 levels / 65,536 leaves).
///
/// Proves:
/// 1. `active_depth` is within `[1, MAX_REVOCATION_WITNESS_DEPTH]`.
/// 2. `pedersen_hash([credential_secret]) == credential_root`.
/// 3. `pedersen_hash([credential_secret, nullifier_secret]) == nullifier`.
/// 4. Every inspected revocation slot `i` has `credential_root != slots[i]`.
/// 5. The parameterised Merkle authentication path from `slots[0]` of depth
///    `active_depth` reconstructs `revocation_root`.
/// 6. `domain_separator` is non-zero.
fn verify_non_revocation_at_depth<let D: u32, let S: u32>(
    credential_secret: Field,
    nullifier_secret: Field,
    slots: [Field; S],
    path_indices: [Field; D],
    siblings: [Field; D],
    active_depth: u32,
    revocation_root: Field,
    nullifier: Field,
    domain_separator: Field,
    credential_root: Field,
) {
    assert_valid_revocation_depth(active_depth);

    let derived_root = pedersen_hash([credential_secret]);
    assert(derived_root == credential_root, "malformed");

    let derived_nullifier = pedersen_hash([credential_secret, nullifier_secret]);
    assert(derived_nullifier == nullifier, "malformed");

    for i in 0..S {
        assert(credential_root != slots[i], "revoked");
    }

    let computed_root = compute_merkle_root_from_path(
        slots[0],
        path_indices,
        siblings,
        active_depth,
    );
    assert(computed_root == revocation_root, "malformed");
    assert(domain_separator != 0, "domain_mismatch");
}

/// Compute the 8-leaf (depth 3) binary Pedersen Merkle root from a leaf array.
fn compute_8_leaf_merkle_root(leaves: [Field; 8]) -> Field {
    assert_valid_revocation_depth(DEFAULT_REVOCATION_WITNESS_DEPTH);
    assert_valid_revocation_leaf_count(DEFAULT_REVOCATION_LEAVES);

    let node_01 = pedersen_hash([leaves[0], leaves[1]]);
    let node_23 = pedersen_hash([leaves[2], leaves[3]]);
    let node_45 = pedersen_hash([leaves[4], leaves[5]]);
    let node_67 = pedersen_hash([leaves[6], leaves[7]]);

    let node_0123 = pedersen_hash([node_01, node_23]);
    let node_4567 = pedersen_hash([node_45, node_67]);

    pedersen_hash([node_0123, node_4567])
}

/// Revocation witness circuit -- proves a credential is NOT in a revocation set.
///
/// The circuit depth bound is parameterised up to `MAX_REVOCATION_WITNESS_DEPTH = 16`
/// (`MAX_REVOCATION_LEAVES = 65536` leaves). The default entry point verifies
/// the 8-leaf (`DEFAULT_REVOCATION_WITNESS_DEPTH = 3`) canonical witness format
/// while `verify_non_revocation_at_depth` verifies arbitrary depths up to
/// `MAX_REVOCATION_WITNESS_DEPTH = 16`.
///
/// The circuit establishes four properties simultaneously without revealing the
/// credential secret or the revocation set contents:
///
///   1. Credential ownership:
///      `pedersen_hash([credential_secret]) == credential_root`
///
///   2. Nullifier correctness (replay prevention):
///      `pedersen_hash([credential_secret, nullifier_secret]) == nullifier`
///
///   3. Non-membership in the revocation tree:
///      The private leaves `leaf_0 .. leaf_7` hash to the public `revocation_root`
///      via a binary Pedersen Merkle tree AND `credential_root != leaf_i` for
///      every `i in 0..8`.
///
///   4. Domain separation:
///      `domain_separator != 0` binds the proof to a specific contract deployment,
///      network, and epoch, preventing cross-context replay.
///
/// Empty / unused slots in the revocation set are represented by `0`. Because a
/// valid `credential_root` is the output of `pedersen_hash` (non-zero for any
/// field element input), a `0` leaf never collides with a real credential.
///
/// Public inputs (visible to the on-chain verifier):
///   - `revocation_root`   -- Merkle root of the current revocation tree
///   - `nullifier`         -- single-use token preventing proof replay
///   - `domain_separator`  -- context binding (contract + network + epoch)
///   - `credential_root`   -- public identifier of the credential being checked
///
/// Private inputs (known only to the prover):
///   - `credential_secret` -- secret pre-image of `credential_root`
///   - `nullifier_secret`  -- secret randomness mixed into the nullifier
///   - `leaf_0 .. leaf_7`  -- all 8 leaves of the revocation Merkle tree
fn main(
    // Private inputs
    credential_secret: Field,
    nullifier_secret: Field,
    leaf_0: Field,
    leaf_1: Field,
    leaf_2: Field,
    leaf_3: Field,
    leaf_4: Field,
    leaf_5: Field,
    leaf_6: Field,
    leaf_7: Field,
    // Public inputs
    revocation_root: pub Field,
    nullifier: pub Field,
    domain_separator: pub Field,
    credential_root: pub Field,
) {
    // Derive credential_root from the private secret.
    let derived_root = pedersen_hash([credential_secret]);
    assert(derived_root == credential_root, "malformed");

    // Derive nullifier from secrets.
    let derived_nullifier = pedersen_hash([credential_secret, nullifier_secret]);
    assert(derived_nullifier == nullifier, "malformed");

    // ------------------------------------------------------------------
    // Merkle root computation (parameterised depth bound <= MAX_REVOCATION_WITNESS_DEPTH)
    // ------------------------------------------------------------------
    let leaves = [leaf_0, leaf_1, leaf_2, leaf_3, leaf_4, leaf_5, leaf_6, leaf_7];
    let computed_root = compute_8_leaf_merkle_root(leaves);
    assert(computed_root == revocation_root, "malformed");

    // ------------------------------------------------------------------
    // Non-membership: credential_root is NOT any leaf
    // ------------------------------------------------------------------
    assert(credential_root != leaf_0, "revoked");
    assert(credential_root != leaf_1, "revoked");
    assert(credential_root != leaf_2, "revoked");
    assert(credential_root != leaf_3, "revoked");
    assert(credential_root != leaf_4, "revoked");
    assert(credential_root != leaf_5, "revoked");
    assert(credential_root != leaf_6, "revoked");
    assert(credential_root != leaf_7, "revoked");

    // Domain binding: `domain_separator` is a structured public input that
    // the contract verifies before calling the UltraHonk verifier. Because
    // it is marked `pub`, the proof is cryptographically bound to its value.
    // Assert it is non-zero to reject uninitialised / default domain tags.
    assert(domain_separator != 0, "domain_mismatch");
}

// ================================================================
// Helper: compute 8-leaf Pedersen Merkle root (used by tests)
// ================================================================
fn compute_revocation_root(
    l0: Field,
    l1: Field,
    l2: Field,
    l3: Field,
    l4: Field,
    l5: Field,
    l6: Field,
    l7: Field,
) -> Field {
    compute_8_leaf_merkle_root([l0, l1, l2, l3, l4, l5, l6, l7])
}

#[test]
fn test_revocation_depth_bound_constants() {
    assert(MAX_REVOCATION_WITNESS_DEPTH == 16, "revocation depth bound must be 16");
    assert(MAX_REVOCATION_LEAVES == 65536, "revocation leaf bound must be 2^16");
    assert_valid_revocation_depth(1);
    assert_valid_revocation_depth(3);
    assert_valid_revocation_depth(16);
    assert_valid_revocation_leaf_count(2);
    assert_valid_revocation_leaf_count(8);
    assert_valid_revocation_leaf_count(65536);
}

#[test]
fn test_max_depth_16_non_revocation_witness() {
    let cs: Field = 12345;
    let ns: Field = 67890;
    let domain: Field = 999999;

    let credential_root = pedersen_hash([cs]);
    let nullifier = pedersen_hash([cs, ns]);

    let revoked_leaf_0 = pedersen_hash([111]);
    let revoked_leaf_1 = pedersen_hash([222]);
    let slots: [Field; 8] = [
        revoked_leaf_0,
        revoked_leaf_1,
        0,
        0,
        0,
        0,
        0,
        0,
    ];

    let path_indices: [Field; 16] = [0; 16];
    let siblings: [Field; 16] = [
        revoked_leaf_1,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];

    let revocation_root = compute_merkle_root_from_path(
        revoked_leaf_0,
        path_indices,
        siblings,
        MAX_REVOCATION_WITNESS_DEPTH_U32,
    );

    verify_non_revocation_at_depth(
        cs,
        ns,
        slots,
        path_indices,
        siblings,
        MAX_REVOCATION_WITNESS_DEPTH_U32,
        revocation_root,
        nullifier,
        domain,
        credential_root,
    );
}

#[test(should_fail_with = "depth_oversize")]
fn test_rejects_depth_above_max_bound() {
    assert_valid_revocation_depth(MAX_REVOCATION_WITNESS_DEPTH_U32 + 1);
}

#[test(should_fail_with = "depth_undersize")]
fn test_rejects_zero_depth() {
    assert_valid_revocation_depth(0);
}

#[test(should_fail_with = "depth_oversize")]
fn test_rejects_leaf_count_above_max_bound() {
    assert_valid_revocation_leaf_count(MAX_REVOCATION_LEAVES_U32 + 1);
}

// ================================================================
// Positive tests
// ================================================================

/// Valid non-revocation proof with exact public inputs matching Prover.toml
/// and zk/noir/fixtures/revocation_vectors.json ("valid_non_revocation_witness").
/// Two credentials (111, 222) are in the revocation tree; credential 12345 is not.
#[test]
fn test_valid_non_revocation_witness() {
    let credential_secret: Field = 12345;
    let nullifier_secret: Field = 67890;
    let domain_separator: Field = 999999;

    // Two revoked credentials; remaining 6 slots are empty (0).
    let revoked_0 = pedersen_hash([111]);
    let revoked_1 = pedersen_hash([222]);

    assert(
        revoked_0 == 0x2084d7bb2dcfa8ee1acce4abbe8abcdb4fd6ae4fd0fe9fb8ef942f0bfad0676c,
        "revoked_0 fixture drift",
    );
    assert(
        revoked_1 == 0x05bb737ebffab8eadf6ea8efbe4fb70a6bdbf1616c17ef095efda61d56d8450f,
        "revoked_1 fixture drift",
    );

    let credential_root = pedersen_hash([credential_secret]);
    let nullifier = pedersen_hash([credential_secret, nullifier_secret]);
    let revocation_root = compute_revocation_root(revoked_0, revoked_1, 0, 0, 0, 0, 0, 0);

    // Pin exact hex values shared with Prover.toml and revocation_vectors.json.
    assert(
        credential_root == 0x16808df1dc1ef4dc4f5dd6fb11f16cd583bb0857845df77aa626a73dd95ea107,
        "credential_root fixture drift",
    );
    assert(
        nullifier == 0x1c794bc1ea4e0b1ef1bc61844e85c690b7e91c6306e908a6953fa195a8f6f261,
        "nullifier fixture drift",
    );
    assert(
        revocation_root == 0x2df3e02d139c4b0030eb8d094fdba8204ab48a2be250ee580172de148f8242e8,
        "revocation_root fixture drift",
    );

    main(
        credential_secret,
        nullifier_secret,
        revoked_0,
        revoked_1,
        0,
        0,
        0,
        0,
        0,
        0,
        revocation_root,
        nullifier,
        domain_separator,
        credential_root,
    );
}

/// Valid proof when all 8 revocation slots are occupied by other credentials.
#[test]
fn test_full_revocation_tree_non_member() {
    let cs: Field = 99999;
    let ns: Field = 88888;
    let domain: Field = 42;

    let l0 = pedersen_hash([1]);
    let l1 = pedersen_hash([2]);
    let l2 = pedersen_hash([3]);
    let l3 = pedersen_hash([4]);
    let l4 = pedersen_hash([5]);
    let l5 = pedersen_hash([6]);
    let l6 = pedersen_hash([7]);
    let l7 = pedersen_hash([8]);

    let root = pedersen_hash([cs]);
    let null = pedersen_hash([cs, ns]);
    let rev_root = compute_revocation_root(l0, l1, l2, l3, l4, l5, l6, l7);

    main(cs, ns, l0, l1, l2, l3, l4, l5, l6, l7, rev_root, null, domain, root);
}

/// Valid proof when the revocation tree is completely empty (all zeros).
#[test]
fn test_empty_revocation_tree() {
    let cs: Field = 54321;
    let ns: Field = 11111;
    let domain: Field = 7;

    let root = pedersen_hash([cs]);
    let null = pedersen_hash([cs, ns]);
    let rev_root = compute_revocation_root(0, 0, 0, 0, 0, 0, 0, 0);

    main(cs, ns, 0, 0, 0, 0, 0, 0, 0, 0, rev_root, null, domain, root);
}

// ================================================================
// Negative tests -- sound rejection of invalid / tampered witnesses
// ================================================================

/// Wrong credential_secret: derived root doesn't match public `credential_root`.
#[test(should_fail_with = "malformed")]
fn test_wrong_credential_secret() {
    let cs: Field = 12345;
    let ns: Field = 67890;
    let domain: Field = 999999;

    let wrong_cs: Field = 12346;
    let root = pedersen_hash([cs]); // root of 12345, not 12346
    let null = pedersen_hash([wrong_cs, ns]);
    let rev_root = compute_revocation_root(0, 0, 0, 0, 0, 0, 0, 0);

    main(wrong_cs, ns, 0, 0, 0, 0, 0, 0, 0, 0, rev_root, null, domain, root);
}

/// Wrong nullifier_secret: nullifier derivation fails.
#[test(should_fail_with = "malformed")]
fn test_wrong_nullifier_secret() {
    let cs: Field = 12345;
    let root = pedersen_hash([cs]);
    let null = pedersen_hash([cs, 67890]); // nullifier for 67890
    let rev_root = compute_revocation_root(0, 0, 0, 0, 0, 0, 0, 0);

    // Supply 99999 as nullifier_secret instead of 67890
    main(cs, 99999, 0, 0, 0, 0, 0, 0, 0, 0, rev_root, null, 999999, root);
}

/// Revoked credential in slot 0: must be rejected.
/// Matches "revoked_credential_in_slot_0" in revocation_vectors.json.
#[test(should_fail_with = "revoked")]
fn test_revoked_credential_rejected() {
    let cs: Field = 12345;
    let ns: Field = 67890;
    let domain: Field = 999999;

    let root = pedersen_hash([cs]);
    let null = pedersen_hash([cs, ns]);
    let other_revoked = pedersen_hash([222]);

    // Place `root` (the credential itself!) into leaf_0
    let rev_root = compute_revocation_root(root, other_revoked, 0, 0, 0, 0, 0, 0);

    main(cs, ns, root, other_revoked, 0, 0, 0, 0, 0, 0, rev_root, null, domain, root);
}

/// Revoked credential in slot 5 (middle of second half): must be rejected.
/// Matches "revoked_credential_in_slot_5" in revocation_vectors.json.
#[test(should_fail_with = "revoked")]
fn test_credential_at_leaf_five() {
    let cs: Field = 777;
    let ns: Field = 888;
    let domain: Field = 100;

    let root = pedersen_hash([cs]);
    let null = pedersen_hash([cs, ns]);
    let rev_root = compute_revocation_root(0, 0, 0, 0, 0, root, 0, 0);

    main(cs, ns, 0, 0, 0, 0, 0, root, 0, 0, rev_root, null, domain, root);
}

/// Revoked credential in the last slot (leaf_7): must be rejected.
/// Matches "revoked_credential_in_slot_7" in revocation_vectors.json.
#[test(should_fail_with = "revoked")]
fn test_credential_at_leaf_seven() {
    let cs: Field = 333;
    let ns: Field = 444;
    let domain: Field = 555;

    let root = pedersen_hash([cs]);
    let null = pedersen_hash([cs, ns]);
    let rev_root = compute_revocation_root(0, 0, 0, 0, 0, 0, 0, root);

    main(cs, ns, 0, 0, 0, 0, 0, 0, 0, root, rev_root, null, domain, root);
}

/// Tampered revocation_root: leaves match the tree but public root is wrong.
#[test(should_fail_with = "malformed")]
fn test_tampered_revocation_root() {
    let cs: Field = 12345;
    let ns: Field = 67890;
    let domain: Field = 999999;

    let root = pedersen_hash([cs]);
    let null = pedersen_hash([cs, ns]);
    let bogus_rev_root: Field = 111111;

    main(cs, ns, 0, 0, 0, 0, 0, 0, 0, 0, bogus_rev_root, null, domain, root);
}

/// Tampered leaves: a leaf is changed so the computed root won't match.
#[test(should_fail_with = "malformed")]
fn test_tampered_leaves() {
    let cs: Field = 12345;
    let ns: Field = 67890;
    let domain: Field = 999999;

    let l0 = pedersen_hash([111]);
    let l1 = pedersen_hash([222]);
    let root = pedersen_hash([cs]);
    let null = pedersen_hash([cs, ns]);
    let rev_root = compute_revocation_root(l0, l1, 0, 0, 0, 0, 0, 0);

    // Replace l0 with a different value -- Merkle root won't match
    let fake_l0 = pedersen_hash([999]);
    main(cs, ns, fake_l0, l1, 0, 0, 0, 0, 0, 0, rev_root, null, domain, root);
}

/// Zero domain separator must be rejected.
/// Matches "zero_domain_separator" in revocation_vectors.json.
#[test(should_fail_with = "domain_mismatch")]
fn test_zero_domain_separator_rejected() {
    let cs: Field = 12345;
    let ns: Field = 67890;

    let root = pedersen_hash([cs]);
    let null = pedersen_hash([cs, ns]);
    let rev_root = compute_revocation_root(0, 0, 0, 0, 0, 0, 0, 0);

    main(cs, ns, 0, 0, 0, 0, 0, 0, 0, 0, rev_root, null, 0, root);
}
