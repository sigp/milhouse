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
# - Tree's derived Debug impl is excluded: recursive trait dictionaries are
#   emitted with forward references. Tree/ProgressiveTree equality uses concrete
#   arc_eq helpers that preserve pointer shortcuts and avoid that dictionary.
# - serde/ssz/hashing/mem are opaque: signatures only, modelled by hand in
#   `aeneas-lean/Tree/FunsExternal.lean` per the `-split-files` workflow.
# - List methods are selected individually so its serde/ssz trait impls remain
#   outside the extraction boundary. `List::intra_rebase` is opaque because its
#   pointer-sharing and hash-cache effects are intentionally erased in Lean.
# - Constructor and iterator trait methods need concrete callers to be emitted
#   by Aeneas; explicit roots alone were insufficient (UPSTREAM_BUGS.md issue 12).
#   to_vec also makes the borrowed IntoIterator body reachable.
#   Additional trait callers live in proof_roots, compiled only for extraction.
# - Progressive SSZ encoding uses explicit streaming loops and spells out
#   equivalent trait defaults to avoid adapter and recursive-dictionary errors.
#   Its external encoder state and operations are modeled in Tree/Ssz/Models.lean.
# - Progressive traversal steps use inline helpers to keep borrows out of loop
#   contexts; to_vec uses an explicit loop (UPSTREAM_BUGS.md issue 13).
# - Progressive pop_front uses a concrete iterator-to-builder helper to avoid
#   cloned adapters, early loop returns, and unsupported trait dictionary fields
#   (UPSTREAM_BUGS.md issue 15).
# - Cow metadata helpers and consuming into_mut are included. Concrete helpers
#   and explicit Result matches avoid borrowed trait/adapter failures. Deref
#   and make_mut still hit borrowed-field failures; see UPSTREAM_BUGS.md.
# - MaxMap default/get/insert/len/max_index callers expose the actual wrapper
#   bodies and cached-maximum updates over an abstract inner UpdateMap.
# - Progressive CoW constructors are included; next_cow still loses borrowed
#   symbolic values during translation (UPSTREAM_BUGS.md issue 16).
# - ProgressiveList TreeHash classification and packing rejection are included.
#   Its root method remains excluded: shared hash-cache writes and parallel
#   recursive closures need additional extraction/model support.
# - The arbitrary feature is enabled for the actual ProgressiveList generator
#   and its trait defaults. Tree roots are explicit so unrelated derived
#   Arbitrary implementations and their thread-local recursion guards are not
#   pulled in. The pinned external Vec generator is modeled in Tree/Arbitrary.

set -euo pipefail
cd "$(dirname "$0")/.."

AENEAS_DIR="${AENEAS_DIR:-../aeneas}"
CHARON="${CHARON:-$AENEAS_DIR/charon/bin/charon}"
AENEAS="${AENEAS:-$AENEAS_DIR/bin/aeneas}"

"$CHARON" cargo --preset=aeneas \
    --rustc-arg=--cfg=milhouse_aeneas \
    --start-from 'milhouse::proof_roots' \
    --start-from 'milhouse::tree::_::leaf_unboxed' \
    --start-from 'milhouse::tree::_::node_unboxed' \
    --start-from 'milhouse::tree::_::zero' \
    --start-from 'milhouse::tree::_::leaf_with_hash' \
    --start-from 'milhouse::tree::_::node' \
    --start-from 'milhouse::tree::_::with_updated_leaves' \
    --start-from 'milhouse::tree::_::leaf' \
    --start-from 'milhouse::tree::_::with_updated_leaf' \
    --start-from 'milhouse::tree::_::get_recursive' \
    --start-from 'milhouse::tree::_::empty' \
    --start-from 'milhouse::tree::_::rebase_on' \
    --start-from 'milhouse::tree::_::arc_eq' \
    --start-from 'milhouse::tree::_::zero_unboxed' \
    --start-from 'milhouse::tree::_::compute_len' \
    --start-from 'milhouse::tree::_::intra_rebase' \
    --start-from '{impl core::clone::Clone for milhouse::tree::Tree}' \
    --start-from '{impl core::hash::Hash for milhouse::tree::Tree}' \
    --start-from '{impl core::cmp::PartialEq for milhouse::tree::Tree}' \
    --start-from 'milhouse::builder' \
    --start-from 'milhouse::cow::_::run' \
    --start-from 'milhouse::cow::_::with_max_index' \
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
    --start-from 'milhouse::progressive_tree::_::build_from_iter' \
    --start-from 'milhouse::progressive_tree::_::get_recursive' \
    --start-from 'milhouse::progressive_tree::_::arc_eq' \
    --start-from 'milhouse::progressive_list::_::empty' \
    --start-from 'milhouse::progressive_list::_::new' \
    --start-from 'milhouse::progressive_list::_::try_from_iter' \
    --start-from 'milhouse::progressive_list::_::get' \
    --start-from 'milhouse::progressive_list::_::get_mut' \
    --start-from 'milhouse::progressive_list::_::get_cow' \
    --start-from 'milhouse::progressive_list::_::apply_updates' \
    --start-from 'milhouse::progressive_list::_::push' \
    --start-from 'milhouse::progressive_list::_::len' \
    --start-from 'milhouse::progressive_list::_::is_empty' \
    --start-from 'milhouse::progressive_list::_::has_pending_updates' \
    --start-from 'milhouse::progressive_list::_::iter' \
    --start-from 'milhouse::progressive_list::_::iter_from' \
    --start-from 'milhouse::progressive_list::_::iter_cow' \
    --start-from 'milhouse::progressive_list::_::iter_cow_from' \
    --start-from 'milhouse::progressive_list::_::to_vec' \
    --start-from 'milhouse::progressive_list::_::pop_front' \
    --start-from 'milhouse::progressive_list::_::rebase' \
    --start-from 'milhouse::progressive_list::_::rebase_on' \
    --start-from '{impl core::cmp::PartialEq for milhouse::progressive_list::ProgressiveList}::eq' \
    --start-from '{impl core::iter::Iterator for milhouse::progressive_list::ProgressiveListIter}::next' \
    --start-from '{impl core::iter::Iterator for milhouse::progressive_list::ProgressiveListIter}::size_hint' \
    --start-from '{impl core::iter::ExactSizeIterator for milhouse::progressive_list::ProgressiveListIter}::len' \
    --start-from '{impl core::default::Default for milhouse::progressive_list::ProgressiveList}' \
    --start-from '{impl core::convert::TryFrom for milhouse::progressive_list::ProgressiveList}::try_from' \
    --start-from '{impl ssz::TryFromIter for milhouse::progressive_list::ProgressiveList}::try_from_iter' \
    --opaque 'ethereum_hashing' \
    --opaque 'tree_hash' \
    --opaque 'ssz' \
    --opaque 'serde' \
    --opaque 'arbitrary' \
    --include 'arbitrary::error::Error' \
    --opaque 'milhouse::mem' \
    --opaque 'milhouse::serde' \
    --opaque 'milhouse::list::_::intra_rebase' \
    --exclude '{impl tree_hash::TreeHash for milhouse::progressive_list::ProgressiveList}::tree_hash_root' \
    --exclude 'milhouse::tree::_::tree_hash' \
    --exclude 'milhouse::update_map::UpdateMap::is_empty' \
    --exclude 'milhouse::builder::{impl core::fmt::Debug for milhouse::builder::Builder<_>}' \
    --exclude 'milhouse::tree::{impl core::fmt::Debug for milhouse::tree::Tree<_>}' \
    --include 'tree_hash::TreeHashType' \
    --include 'ssz::decode::DecodeError' \
    --dest-file tree.llbc -- --features arbitrary

"$AENEAS" -backend lean -split-files -dest aeneas-lean/Tree tree.llbc

# The Arbitrary trait's `arbitrary` field shadows its namespace in later
# field types. Qualify those names without changing the generated interface.
python3 scripts/aeneas-qualify-arbitrary.py aeneas-lean/Tree/Types.lean

# The pinned Rust Vec equality uses its slice's element-ne loop. Aeneas's
# built-in Vec.eq calls element eq instead; use the faithful local external
# model so custom eq/ne implementations need no unstated coherence assumption.
perl -0pi -e 's/\balloc\.vec\.partial_eq\.PartialEqVec\.eq\b/milhouse_models.vec_eq/g' \
    aeneas-lean/Tree/Funs.lean

# Workaround for an Aeneas Lean-backend bug: the `impl_def` for `Eq<(U, T)>`
# fails to resolve its self-referential `assert_fields_are_eq` default method
# ("could not resolve recursive fields"). Replace it with a plain `def` and
# the no-op the default resolves to.
perl -0pi -e 's/impl_def (Pair\.Insts\.CoreCmpEq \{U : Type\} \{T : Type\}.*?assert_fields_are_eq := )core\.cmp\.Eq\.assert_fields_are_eq\.default\n\s*\(Pair\.Insts\.CoreCmpEq cmpEqInst cmpEqInst1\)\n\}/def $1fun _ => ok ()\n}/s' \
    aeneas-lean/Tree/Funs.lean

# Aeneas's toStr default proves its byte-size bound with native evaluation,
# adding a native-decide axiom to callers. Supply a kernel-checked proof for
# each emitted literal instead, preserving the same string and function body.
perl -0pi -e 's/\btoStr(\s+"(?:[^"\\]|\\.)*")/toStr$1 (by rw [U32.max_eq]; cbv)/g' \
    aeneas-lean/Tree/Funs.lean

# Error strings are observable in DecodeError::BytesInvalid. Preserve the
# actual derived formatter with local models instead of erasing Arguments to
# Unit. The currently reached fragment uses only default formatting options.
perl -0pi -e 's/\bcore\.fmt\./milhouse_fmt./g' \
    aeneas-lean/Tree/Funs.lean
