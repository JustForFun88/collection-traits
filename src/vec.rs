use super::{Equivalent, ValueCollectionRef, ValueContain};
use smallvec::SmallVec;
use std::collections::{self, vec_deque};

mod vec_ref;
pub use vec_ref::VecCollectionRef;

mod vec_mut;
pub use vec_mut::VecCollectionMut;

pub trait VecCollection<E = <Self as ValueContain>::Value>
where
    Self: ValueCollectionRef<E> + VecCollectionRef<E> + VecCollectionMut<E>,
    E: ?Sized,
{
    type IntoValues: Iterator<Item = Self::Value>;
    fn into_collection_values(self) -> Self::IntoValues;
}

impl<T, E> VecCollection<E> for Vec<T>
where
    E: ?Sized + Equivalent<T>,
{
    type IntoValues = alloc::vec::IntoIter<T>;

    #[inline]
    fn into_collection_values(self) -> Self::IntoValues {
        self.into_iter()
    }
}

impl<T, E> VecCollection<E> for im::Vector<T>
where
    T: Clone,
    E: ?Sized + Equivalent<T>,
{
    type IntoValues = im::vector::ConsumingIter<T>;

    #[inline]
    fn into_collection_values(self) -> Self::IntoValues {
        self.into_iter()
    }
}

impl<T, E> VecCollection<E> for collections::VecDeque<T>
where
    E: ?Sized + Equivalent<T>,
{
    type IntoValues = vec_deque::IntoIter<T>;

    #[inline]
    fn into_collection_values(self) -> Self::IntoValues {
        self.into_iter()
    }
}

impl<T, A, E> VecCollection<E> for SmallVec<A>
where
    A: smallvec::Array<Item = T>,
    E: ?Sized + Equivalent<T>,
{
    type IntoValues = smallvec::IntoIter<A>;

    #[inline]
    fn into_collection_values(self) -> Self::IntoValues {
        self.into_iter()
    }
}
