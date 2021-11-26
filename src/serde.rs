use crate::List;
use serde::Deserialize;
use std::marker::PhantomData;
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
    T: Deserialize<'a> + Clone,
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
        let mut list = List::empty();

        while let Some(val) = seq.next_element()? {
            list.push(val).map_err(|e| {
                serde::de::Error::custom(format!(
                    "Deserialization failed. Length cannot be greater than {}. Error: {:?}",
                    N::to_usize(),
                    e
                ))
            })?;
        }
        Ok(list)
    }
}
