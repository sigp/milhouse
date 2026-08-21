use crate::{
    Leaf, PackedLeaf, Tree, Value,
    utils::{Length, opt_packing_depth, opt_packing_factor},
};

#[derive(Debug)]
pub struct Iter<'a, T: Value> {
    root: &'a Tree<T>,
    /// Stack of tree nodes corresponding to the forward cursor.
    front_stack: Vec<&'a Tree<T>>,
    /// The list index corresponding to the forward cursor (next element to be yielded).
    front: usize,
    /// Stack of tree nodes corresponding to the backward cursor.
    back_stack: Vec<&'a Tree<T>>,
    /// Exclusive end index for the backward cursor.
    back: usize,
    /// The `depth` of the root tree.
    full_depth: usize,
    /// Cached packing factor to avoid re-calculating `opt_packing_factor`.
    ///
    /// Initialised to 0 if `T` is not packed.
    packing_factor: usize,
    /// Cached packing depth to avoid re-calculating `opt_packing_depth`.
    packing_depth: usize,
}

impl<'a, T: Value> Iter<'a, T> {
    pub fn from_index(index: usize, root: &'a Tree<T>, depth: usize, length: Length) -> Self {
        let mut front_stack = Vec::with_capacity(depth);
        front_stack.push(root);

        Iter {
            root,
            front_stack,
            front: index,
            back_stack: Vec::with_capacity(depth),
            back: length.as_usize(),
            full_depth: depth,
            packing_factor: opt_packing_factor::<T>().unwrap_or(0),
            packing_depth: opt_packing_depth::<T>().unwrap_or(0),
        }
    }
}

fn descend_to_target<'a, T: Value>(
    stack: &mut Vec<&'a Tree<T>>,
    root: &'a Tree<T>,
    target_index: usize,
    full_depth: usize,
    packing_depth: usize,
) {
    if stack.is_empty() {
        stack.push(root);
    }

    loop {
        match stack.last() {
            Some(Tree::Node { left, right, .. }) => {
                let depth = full_depth - stack.len();
                if (target_index >> (depth + packing_depth)) & 1 == 0 {
                    stack.push(left);
                } else {
                    stack.push(right);
                }
            }
            Some(Tree::Leaf(_)) | Some(Tree::PackedLeaf(_)) => break,
            Some(Tree::Zero(_)) | None => break,
        }
    }
}

fn value_at_top<T: Value>(node: &Tree<T>, index: usize, packing_factor: usize) -> Option<&T> {
    match node {
        Tree::Leaf(Leaf { value, .. }) => Some(value.as_ref()),
        Tree::PackedLeaf(PackedLeaf { values, .. }) => values.get(index % packing_factor),
        Tree::Zero(_) | Tree::Node { .. } => None,
    }
}

fn advance_front<T: Value>(
    stack: &mut Vec<&Tree<T>>,
    index: usize,
    packing_factor: usize,
    packing_depth: usize,
) {
    match stack.last() {
        Some(Tree::Leaf(_)) => {
            for _ in 0..=index.trailing_zeros() {
                stack.pop();
            }
        }
        Some(Tree::PackedLeaf(_)) => {
            let sub_index = (index - 1) % packing_factor;
            if sub_index + 1 == packing_factor {
                let to_pop = index
                    .trailing_zeros()
                    .checked_sub(packing_depth as u32)
                    .expect("index should have at least `packing_depth` trailing zeroes");

                for _ in 0..=to_pop {
                    stack.pop();
                }
            }
        }
        _ => {}
    }
}

fn retreat_back<'a, T: Value>(
    stack: &mut Vec<&'a Tree<T>>,
    root: &'a Tree<T>,
    index: usize,
    front: usize,
    full_depth: usize,
    packing_factor: usize,
    packing_depth: usize,
) {
    if index <= front {
        return;
    }

    match stack.last() {
        Some(Tree::Leaf(_)) => {
            for _ in 0..=index.trailing_zeros() {
                stack.pop();
            }
            if index > 0 {
                descend_to_target(stack, root, index - 1, full_depth, packing_depth);
            }
        }
        Some(Tree::PackedLeaf(_)) => {
            let sub_index = index % packing_factor;
            if sub_index > 0 {
                // Next element is in the same chunk.
            } else if index > 0 {
                let to_pop = index
                    .trailing_zeros()
                    .checked_sub(packing_depth as u32)
                    .expect("index should have at least `packing_depth` trailing zeroes");

                for _ in 0..=to_pop {
                    stack.pop();
                }
                descend_to_target(stack, root, index - 1, full_depth, packing_depth);
            }
        }
        _ => {}
    }
}

impl<'a, T: Value> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.front >= self.back {
            return None;
        }

        match self.front_stack.last() {
            None | Some(Tree::Zero(_)) => None,
            Some(Tree::Leaf(_)) => {
                let node = self.front_stack.last()?;
                let result = value_at_top(node, self.front, self.packing_factor)?;

                self.front += 1;
                advance_front(
                    &mut self.front_stack,
                    self.front,
                    self.packing_factor,
                    self.packing_depth,
                );

                Some(result)
            }
            Some(Tree::PackedLeaf(_)) => {
                let node = self.front_stack.last()?;
                let sub_index = self.front % self.packing_factor;
                let result = value_at_top(node, self.front, self.packing_factor)?;

                self.front += 1;

                if sub_index + 1 == self.packing_factor {
                    advance_front(
                        &mut self.front_stack,
                        self.front,
                        self.packing_factor,
                        self.packing_depth,
                    );
                }

                Some(result)
            }
            Some(Tree::Node { left, right, .. }) => {
                let depth = self.full_depth - self.front_stack.len();

                if (self.front >> (depth + self.packing_depth)) & 1 == 0 {
                    self.front_stack.push(left);
                } else {
                    self.front_stack.push(right);
                }

                self.next()
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.back.saturating_sub(self.front);
        (remaining, Some(remaining))
    }
}

impl<'a, T: Value> DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.front >= self.back {
            return None;
        }

        self.back -= 1;

        if self.back_stack.is_empty() {
            self.back_stack.push(self.root);
            descend_to_target(
                &mut self.back_stack,
                self.root,
                self.back,
                self.full_depth,
                self.packing_depth,
            );
        }

        let node = self.back_stack.last()?;
        let result = value_at_top(node, self.back, self.packing_factor)?;

        retreat_back(
            &mut self.back_stack,
            self.root,
            self.back,
            self.front,
            self.full_depth,
            self.packing_factor,
            self.packing_depth,
        );

        Some(result)
    }
}

impl<T: Value> ExactSizeIterator for Iter<'_, T> {}
