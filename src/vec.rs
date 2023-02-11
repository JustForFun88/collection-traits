use super::{Equivalent, ValueContain, ValueCollectionRef};
use smallvec::SmallVec;
use std::collections::{self, vec_deque};

mod vec_ref;
pub use vec_ref::VecContainerRef;

mod vec_mut;
pub use vec_mut::VecContainerMut;

pub trait VecContainer<E = <Self as ValueContain>::Value>
where
    Self: ValueCollectionRef<E> + VecContainerRef<E> + VecContainerMut<E>,
    E: ?Sized,
{
    type IntoValues: Iterator<Item = Self::Value>;
    fn into_cont_values(self) -> Self::IntoValues;
}

impl<T, E> VecContainer<E> for Vec<T>
where
    E: ?Sized + Equivalent<T>,
{
    type IntoValues = alloc::vec::IntoIter<T>;

    #[inline]
    fn into_cont_values(self) -> Self::IntoValues {
        self.into_iter()
    }
}

impl<T, E> VecContainer<E> for im::Vector<T>
where
    T: Clone,
    E: ?Sized + Equivalent<T>,
{
    type IntoValues = im::vector::ConsumingIter<T>;

    #[inline]
    fn into_cont_values(self) -> Self::IntoValues {
        self.into_iter()
    }
}

impl<T, E> VecContainer<E> for collections::VecDeque<T>
where
    E: ?Sized + Equivalent<T>,
{
    type IntoValues = vec_deque::IntoIter<T>;

    #[inline]
    fn into_cont_values(self) -> Self::IntoValues {
        self.into_iter()
    }
}

impl<T, A, E> VecContainer<E> for SmallVec<A>
where
    A: smallvec::Array<Item = T>,
    E: ?Sized + Equivalent<T>,
{
    type IntoValues = smallvec::IntoIter<A>;

    #[inline]
    fn into_cont_values(self) -> Self::IntoValues {
        self.into_iter()
    }
}
