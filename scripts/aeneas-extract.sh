#!/usr/bin/env bash
# Extract the core tree, builder, and list APIs to Lean via Charon + Aeneas.
#
# Produces `tree.llbc` (Charon's LLBC dump) and regenerates the generated
# files in `aeneas-lean/Tree/` (the hand-written `TypesExternal.lean` and
# `FunsExternal.lean` are not touched; diff the `*_Template.lean` files after
# regenerating to see if the external interface changed). Requires a checkout
# of https://github.com/AeneasVerif/aeneas with `charon` and `aeneas` built;
# defaults assume it sits next to this repo.
#
# Check the result elaborates with: cd aeneas-lean && lake build
#
# Scope notes:
# - `Tree::tree_hash` is excluded: its closures form a mixed mutually
#   recursive group, and `ethereum_hashing::ZERO_HASHES` has a function
#   pointer in its type (`LazyLock`), neither of which Aeneas supports yet.
# - `UpdateMap::is_empty` is excluded: provided trait method that triggers
#   an Aeneas internal error.
# - `Tree::with_updated_leaves` and `PackedLeaf::update` are included since
#   their `FnMut` closures were replaced by closure-free code (the Aeneas
#   Lean backend mistranslates `FnMut` calling conventions).
# - Tree's derived `Debug`/`PartialEq` impls are excluded: recursive trait
#   impls are emitted with forward references (Aeneas Lean-backend bug).
# - serde/ssz/hashing/mem are opaque: signatures only, modelled by hand in
#   `aeneas-lean/Tree/FunsExternal.lean` per the `-split-files` workflow.
# - List methods are selected individually so its serde/ssz trait impls remain
#   outside the extraction boundary. `List::intra_rebase` is opaque because its
#   pointer-sharing and hash-cache effects are intentionally erased in Lean.

set -euo pipefail
cd "$(dirname "$0")/.."

AENEAS_DIR="${AENEAS_DIR:-../aeneas}"
CHARON="${CHARON:-$AENEAS_DIR/charon/bin/charon}"
AENEAS="${AENEAS:-$AENEAS_DIR/bin/aeneas}"

"$CHARON" cargo --preset=aeneas \
    --start-from 'milhouse::tree' \
    --start-from 'milhouse::builder' \
    --start-from 'milhouse::repeat::repeat_list' \
    --start-from 'milhouse::list::_::new' \
    --start-from 'milhouse::list::_::empty' \
    --start-from 'milhouse::list::_::repeat' \
    --start-from 'milhouse::list::_::repeat_slow' \
    --start-from 'milhouse::list::_::to_vec' \
    --start-from 'milhouse::list::_::iter_from' \
    --start-from 'milhouse::list::_::level_iter_from' \
    --start-from 'milhouse::list::_::iter_cow' \
    --start-from 'milhouse::list::_::iter_cow_from' \
    --start-from 'milhouse::list::_::get' \
    --start-from 'milhouse::list::_::get_mut' \
    --start-from 'milhouse::list::_::get_cow' \
    --start-from 'milhouse::list::_::push' \
    --start-from 'milhouse::list::_::is_empty' \
    --start-from 'milhouse::list::_::has_pending_updates' \
    --start-from 'milhouse::list::_::apply_updates' \
    --start-from 'milhouse::list::_::pop_front_slow' \
    --start-from 'milhouse::list::_::pop_front' \
    --start-from 'milhouse::list::_::rebase' \
    --start-from 'milhouse::list::_::intra_rebase' \
    --start-from 'milhouse::progressive_tree::_::empty' \
    --start-from 'milhouse::progressive_tree::_::get_recursive' \
    --start-from 'milhouse::progressive_list::_::empty' \
    --start-from 'milhouse::progressive_list::_::get' \
    --start-from 'milhouse::progressive_list::_::get_mut' \
    --start-from 'milhouse::progressive_list::_::get_cow' \
    --start-from 'milhouse::progressive_list::_::apply_updates' \
    --start-from 'milhouse::progressive_list::_::push' \
    --start-from 'milhouse::progressive_list::_::len' \
    --start-from 'milhouse::progressive_list::_::is_empty' \
    --start-from 'milhouse::progressive_list::_::has_pending_updates' \
    --start-from '{impl core::default::Default for milhouse::progressive_list::ProgressiveList}' \
    --opaque 'ethereum_hashing' \
    --opaque 'tree_hash' \
    --opaque 'ssz' \
    --opaque 'serde' \
    --opaque 'milhouse::mem' \
    --opaque 'milhouse::serde' \
    --opaque 'milhouse::list::_::intra_rebase' \
    --exclude 'milhouse::tree::_::tree_hash' \
    --exclude 'milhouse::update_map::UpdateMap::is_empty' \
    --exclude 'milhouse::builder::{impl core::fmt::Debug for milhouse::builder::Builder<_>}' \
    --exclude 'milhouse::tree::{impl core::fmt::Debug for milhouse::tree::Tree<_>}' \
    --exclude 'milhouse::tree::{impl core::cmp::PartialEq<milhouse::tree::Tree<_>> for milhouse::tree::Tree<_>}' \
    --include 'tree_hash::TreeHashType' \
    --dest-file tree.llbc

"$AENEAS" -backend lean -split-files -dest aeneas-lean/Tree tree.llbc

# Workaround for an Aeneas Lean-backend bug: the `impl_def` for `Eq<(U, T)>`
# fails to resolve its self-referential `assert_fields_are_eq` default method
# ("could not resolve recursive fields"). Replace it with a plain `def` and
# the no-op the default resolves to.
perl -0pi -e 's/impl_def (Pair\.Insts\.CoreCmpEq \{U : Type\} \{T : Type\}.*?assert_fields_are_eq := )core\.cmp\.Eq\.assert_fields_are_eq\.default\n\s*\(Pair\.Insts\.CoreCmpEq cmpEqInst cmpEqInst1\)\n\}/def $1fun _ => ok ()\n}/s' \
    aeneas-lean/Tree/Funs.lean
