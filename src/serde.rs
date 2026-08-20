use crate::{List, ProgressiveList, UpdateMap, Value};
use itertools::process_results;
use serde::Deserialize;
use std::marker::PhantomData;
use typenum::Unsigned;

pub struct ListVisitor<T, N, U> {
    _phantom: PhantomData<(T, N, U)>,
}

impl<T, N, U> Default for ListVisitor<T, N, U> {
    fn default() -> Self {
        Self {
            _phantom: PhantomData,
        }
    }
}

impl<'a, T, N, U> serde::de::Visitor<'a> for ListVisitor<T, N, U>
where
    T: Deserialize<'a> + Value,
    N: Unsigned,
    U: UpdateMap<T>,
{
    type Value = List<T, N, U>;

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
                    serde::de::Error::custom(format!("Error deserializing List: {e:?}"))
                })
            },
        )?
    }
}

pub struct ProgressiveListVisitor<T, U> {
    _phantom: PhantomData<(T, U)>,
}

impl<T, U> Default for ProgressiveListVisitor<T, U> {
    fn default() -> Self {
        Self {
            _phantom: PhantomData,
        }
    }
}

impl<'a, T, U> serde::de::Visitor<'a> for ProgressiveListVisitor<T, U>
where
    T: Deserialize<'a> + Value,
    U: UpdateMap<T>,
{
    type Value = ProgressiveList<T, U>;

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
                ProgressiveList::try_from_iter(iter).map_err(|e| {
                    serde::de::Error::custom(format!("Error deserializing ProgressiveList: {e:?}"))
                })
            },
        )?
    }
}
