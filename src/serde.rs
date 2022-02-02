use crate::List;
use itertools::process_results;
use serde::Deserialize;
use std::marker::PhantomData;
use tree_hash::TreeHash;
use typenum::Unsigned;

pub struct ListVisitor<T, N> {
    _phantom: PhantomData<(T, N)>,
}

impl<T, N> Default for ListVisitor<T, N> {
    fn default() -> Self {
        Self {
            _phantom: PhantomData,
        }
    }
}

impl<'a, T, N> serde::de::Visitor<'a> for ListVisitor<T, N>
where
    T: Deserialize<'a> + TreeHash + Clone,
    N: Unsigned,
{
    type Value = List<T, N>;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(formatter, "a list of T")
    }

    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
    where
        A: serde::de::SeqAccess<'a>,
    {
        process_results(
            std::iter::from_fn(|| seq.next_element().transpose()),
            |iter| {
                List::try_from_iter(iter).map_err(|e| {
                    serde::de::Error::custom(format!("Error deserializing List: {:?}", e))
                })
            },
        )?
    }
}
