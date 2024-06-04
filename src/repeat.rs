use crate::utils::{opt_packing_factor, Length};
use crate::{Arc, Error, Leaf, List, PackedLeaf, Tree, UpdateMap, ValidN, Value};
use smallvec::{smallvec, SmallVec};
use tree_hash::Hash256;

/// Efficiently construct a list from `n` copies of `elem`.
pub fn repeat_list<T, N, U>(elem: T, n: usize) -> Result<List<T, N, U>, Error>
where
    T: Value,
    N: ValidN,
    U: UpdateMap<T>,
{
    if n == 0 {
        return Ok(List::empty());
    }

    // Keep a list of nodes at the current level and their multiplicity.
    // In the common case where `n` is not divisible by the packing factor then part of the
    // tree will be slightly different from the bulk repeated part.
    let packing_factor = opt_packing_factor::<T>();
    let tree_depth = List::<T, N, U>::depth();

    let mut layer: SmallVec<[_; 2]> = if let Some(packing_factor) = packing_factor {
        let repeat_count = n / packing_factor;
        let lonely_count = n % packing_factor;
        let repeat_leaf = Arc::new(Tree::PackedLeaf(PackedLeaf::repeat(
            elem.clone(),
            packing_factor,
        )));
        let lonely_leaf = Arc::new(Tree::PackedLeaf(PackedLeaf::repeat(elem, lonely_count)));
        match (repeat_count, lonely_count) {
            (0, 0) => unreachable!("n != 0"),
            (_, 0) => smallvec![(repeat_leaf, repeat_count)],
            (0, _) => smallvec![(lonely_leaf, 1)],
            (_, _) => {
                smallvec![(repeat_leaf, repeat_count), (lonely_leaf, 1)]
            }
        }
    } else {
        smallvec![(Arc::new(Tree::Leaf(Leaf::new(elem))), n)]
    };

    for depth in 0..tree_depth {
        let new_layer = match &layer[..] {
            [(repeat_leaf, 1)] => {
                smallvec![(
                    Tree::node(repeat_leaf.clone(), Tree::zero(depth), Hash256::zero()),
                    1,
                )]
            }
            [(repeat_leaf, repeat_count)] if repeat_count % 2 == 0 => {
                smallvec![(
                    Tree::node(repeat_leaf.clone(), repeat_leaf.clone(), Hash256::zero()),
                    repeat_count / 2,
                )]
            }
            [(repeat_leaf, repeat_count)] => {
                smallvec![
                    (
                        Tree::node(repeat_leaf.clone(), repeat_leaf.clone(), Hash256::zero()),
                        repeat_count / 2,
                    ),
                    (
                        Tree::node(repeat_leaf.clone(), Tree::zero(depth), Hash256::zero()),
                        1,
                    ),
                ]
            }
            [(repeat_leaf, 1), (lonely_leaf, 1)] => {
                smallvec![(
                    Tree::node(repeat_leaf.clone(), lonely_leaf.clone(), Hash256::zero()),
                    1,
                )]
            }
            [(repeat_leaf, repeat_count), (lonely_leaf, 1)] => {
                if repeat_count % 2 == 0 {
                    smallvec![
                        (
                            Tree::node(repeat_leaf.clone(), repeat_leaf.clone(), Hash256::zero()),
                            repeat_count / 2,
                        ),
                        (
                            Tree::node(lonely_leaf.clone(), Tree::zero(depth), Hash256::zero()),
                            1,
                        ),
                    ]
                } else {
                    smallvec![
                        (
                            Tree::node(repeat_leaf.clone(), repeat_leaf.clone(), Hash256::zero()),
                            repeat_count / 2,
                        ),
                        (
                            Tree::node(repeat_leaf.clone(), lonely_leaf.clone(), Hash256::zero()),
                            1,
                        ),
                    ]
                }
            }
            _ => unreachable!("not possible"),
        };
        drop(std::mem::replace(&mut layer, new_layer));
    }

    let (root, count) = layer.pop().ok_or(Error::BuilderStackEmptyFinalize)?;
    if !layer.is_empty() || count != 1 {
        return Err(Error::BuilderStackLeftover);
    }

    Ok(List::from_parts(root, tree_depth, Length(n)))
}
