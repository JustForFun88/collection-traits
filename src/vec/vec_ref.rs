use crate::{Equivalent, ValueContain, ValueCollectionRef};
use smallvec::SmallVec;
use std::collections;

pub trait VecContainerRef<E = <Self as ValueContain>::Value>
where
    Self: ValueCollectionRef<E> + Sized,
    E: ?Sized,
{
    fn get_value_at(&self, index: usize) -> Option<&Self::Value>;
    fn cont_as_slice(&self) -> Option<&[Self::Value]>;
}

impl<T, E: ?Sized> VecContainerRef<E> for &T
where
    T: VecContainerRef<E>,
{
    #[inline]
    fn get_value_at(&self, index: usize) -> Option<&Self::Value> {
        <T as VecContainerRef<E>>::get_value_at(self, index)
    }
    #[inline]
    fn cont_as_slice(&self) -> Option<&[Self::Value]> {
        <T as VecContainerRef<E>>::cont_as_slice(self)
    }
}

impl<T, E: ?Sized> VecContainerRef<E> for &mut T
where
    T: VecContainerRef<E>,
{
    #[inline]
    fn get_value_at(&self, index: usize) -> Option<&Self::Value> {
        <T as VecContainerRef<E>>::get_value_at(self, index)
    }
    #[inline]
    fn cont_as_slice(&self) -> Option<&[Self::Value]> {
        <T as VecContainerRef<E>>::cont_as_slice(self)
    }
}

impl<T, E> VecContainerRef<E> for Vec<T>
where
    E: ?Sized + Equivalent<T>,
{
    #[inline]
    fn cont_as_slice(&self) -> Option<&[Self::Value]> {
        Some(self.as_slice())
    }
    #[inline]
    fn get_value_at(&self, index: usize) -> Option<&Self::Value> {
        self.get(index)
    }
}

impl<T, E> VecContainerRef<E> for im::Vector<T>
where
    T: Clone,
    E: ?Sized + Equivalent<T>,
{
    #[inline]
    fn cont_as_slice(&self) -> Option<&[Self::Value]> {
        None
    }
    #[inline]
    fn get_value_at(&self, index: usize) -> Option<&Self::Value> {
        self.get(index)
    }
}

impl<T, E> VecContainerRef<E> for collections::VecDeque<T>
where
    E: ?Sized + Equivalent<T>,
{
    #[inline]
    fn cont_as_slice(&self) -> Option<&[Self::Value]> {
        None
    }
    #[inline]
    fn get_value_at(&self, index: usize) -> Option<&Self::Value> {
        self.get(index)
    }
}

impl<T, A, E> VecContainerRef<E> for SmallVec<A>
where
    A: smallvec::Array<Item = T>,
    E: ?Sized + Equivalent<T>,
{
    #[inline]
    fn get_value_at(&self, index: usize) -> Option<&Self::Value> {
        self.get(index)
    }

    #[inline]
    fn cont_as_slice(&self) -> Option<&[Self::Value]> {
        Some(self.as_slice())
    }
}
