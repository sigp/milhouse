#!/usr/bin/env bash
# Extract the core tree types to Lean via Charon + Aeneas.
#
# Produces `tree.llbc` (Charon's LLBC dump) and `aeneas-lean/` (the Lean
# development). Requires a checkout of https://github.com/AeneasVerif/aeneas
# with `charon` and `aeneas` built; defaults assume it sits next to this repo.
#
# Scope notes:
# - `Tree::tree_hash` is excluded: its closures form a mixed mutually
#   recursive group, and `ethereum_hashing::ZERO_HASHES` has a function
#   pointer in its type (`LazyLock`), neither of which Aeneas supports yet.
# - `UpdateMap::is_empty` is excluded: provided trait method that triggers
#   an Aeneas internal error.
# - serde/ssz/hashing/mem are opaque: signatures only, modelled by hand in
#   `aeneas-lean/FunsExternal.lean` per the Aeneas `-split-files` workflow.

set -euo pipefail
cd "$(dirname "$0")/.."

AENEAS_DIR="${AENEAS_DIR:-../aeneas}"
CHARON="${CHARON:-$AENEAS_DIR/charon/bin/charon}"
AENEAS="${AENEAS:-$AENEAS_DIR/bin/aeneas}"

"$CHARON" cargo --preset=aeneas \
    --start-from 'milhouse::tree' \
    --opaque 'ethereum_hashing' \
    --opaque 'tree_hash' \
    --opaque 'ssz' \
    --opaque 'serde' \
    --opaque 'milhouse::mem' \
    --opaque 'milhouse::serde' \
    --exclude 'milhouse::tree::_::tree_hash' \
    --exclude 'milhouse::update_map::UpdateMap::is_empty' \
    --include 'tree_hash::TreeHashType' \
    --dest-file tree.llbc

"$AENEAS" -backend lean -split-files -dest aeneas-lean tree.llbc
