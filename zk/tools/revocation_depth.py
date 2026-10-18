"""Protocol revocation witness Merkle-depth bounds (#357).

Mirrored in:
- zk/noir/revocation_witness/src/main.nr
- contracts/contracts/harpocrates-registry/src/lib.rs
- backend/verifier_inputs.py
- frontend/src/verifierInputs.ts
- zk/noir/fixtures/revocation_vectors.json
"""

from __future__ import annotations

MIN_REVOCATION_WITNESS_DEPTH = 1
MAX_REVOCATION_WITNESS_DEPTH = 16
MAX_REVOCATION_LEAVES = 1 << MAX_REVOCATION_WITNESS_DEPTH


class RevocationDepthError(ValueError):
    """Structured revocation Merkle-depth validation failure."""

    def __init__(self, code: str, message: str | None = None) -> None:
        super().__init__(message or code)
        self.code = code


def validate_revocation_depth(depth: int) -> int:
    if isinstance(depth, bool) or not isinstance(depth, int):
        raise RevocationDepthError("depth_not_integer", "revocation depth must be an integer")
    if depth < MIN_REVOCATION_WITNESS_DEPTH:
        raise RevocationDepthError("depth_undersize", "revocation depth must be >= 1")
    if depth > MAX_REVOCATION_WITNESS_DEPTH:
        raise RevocationDepthError(
            "depth_oversize",
            f"revocation depth {depth} exceeds max {MAX_REVOCATION_WITNESS_DEPTH}",
        )
    return depth


def validate_revocation_leaf_count(leaf_count: int) -> int:
    if isinstance(leaf_count, bool) or not isinstance(leaf_count, int):
        raise RevocationDepthError("depth_not_integer", "revocation leaf count must be an integer")
    if leaf_count < (1 << MIN_REVOCATION_WITNESS_DEPTH):
        raise RevocationDepthError("depth_undersize", "revocation leaf count must be >= 2")
    if leaf_count > MAX_REVOCATION_LEAVES:
        raise RevocationDepthError(
            "depth_oversize",
            f"revocation leaf count {leaf_count} exceeds max {MAX_REVOCATION_LEAVES}",
        )
    if leaf_count & (leaf_count - 1):
        raise RevocationDepthError(
            "depth_non_power_of_two",
            "revocation leaf count must be a power of two",
        )
    return leaf_count


def validate_revocation_witness_shape(depth: int, leaf_count: int) -> tuple[int, int]:
    validated_depth = validate_revocation_depth(depth)
    validated_leaves = validate_revocation_leaf_count(leaf_count)
    if validated_leaves != (1 << validated_depth):
        raise RevocationDepthError(
            "depth_leaf_mismatch",
            f"leaf count {validated_leaves} does not match depth {validated_depth}",
        )
    return validated_depth, validated_leaves
