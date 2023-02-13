use crate::{Equivalent, ValueCollectionRef, ValueContain};
use smallvec::SmallVec;
use std::collections;

pub trait VecCollectionRef<E = <Self as ValueContain>::Value>
where
    Self: ValueCollectionRef<E> + Sized,
    E: ?Sized,
{
    fn get_value_at(&self, index: usize) -> Option<&Self::Value>;
    fn collection_as_slice(&self) -> Option<&[Self::Value]>;
}

impl<T, E: ?Sized> VecCollectionRef<E> for &T
where
    T: VecCollectionRef<E>,
{
    #[inline]
    fn get_value_at(&self, index: usize) -> Option<&Self::Value> {
        <T as VecCollectionRef<E>>::get_value_at(self, index)
    }
    #[inline]
    fn collection_as_slice(&self) -> Option<&[Self::Value]> {
        <T as VecCollectionRef<E>>::collection_as_slice(self)
    }
}

impl<T, E: ?Sized> VecCollectionRef<E> for &mut T
where
    T: VecCollectionRef<E>,
{
    #[inline]
    fn get_value_at(&self, index: usize) -> Option<&Self::Value> {
        <T as VecCollectionRef<E>>::get_value_at(self, index)
    }
    #[inline]
    fn collection_as_slice(&self) -> Option<&[Self::Value]> {
        <T as VecCollectionRef<E>>::collection_as_slice(self)
    }
}

impl<T, E> VecCollectionRef<E> for Vec<T>
where
    E: ?Sized + Equivalent<T>,
{
    #[inline]
    fn collection_as_slice(&self) -> Option<&[Self::Value]> {
        Some(self.as_slice())
    }
    #[inline]
    fn get_value_at(&self, index: usize) -> Option<&Self::Value> {
        self.get(index)
    }
}

impl<T, E> VecCollectionRef<E> for im::Vector<T>
where
    T: Clone,
    E: ?Sized + Equivalent<T>,
{
    #[inline]
    fn collection_as_slice(&self) -> Option<&[Self::Value]> {
        None
    }
    #[inline]
    fn get_value_at(&self, index: usize) -> Option<&Self::Value> {
        self.get(index)
    }
}

impl<T, E> VecCollectionRef<E> for collections::VecDeque<T>
where
    E: ?Sized + Equivalent<T>,
{
    #[inline]
    fn collection_as_slice(&self) -> Option<&[Self::Value]> {
        None
    }
    #[inline]
    fn get_value_at(&self, index: usize) -> Option<&Self::Value> {
        self.get(index)
    }
}

impl<T, A, E> VecCollectionRef<E> for SmallVec<A>
where
    A: smallvec::Array<Item = T>,
    E: ?Sized + Equivalent<T>,
{
    #[inline]
    fn get_value_at(&self, index: usize) -> Option<&Self::Value> {
        self.get(index)
    }

    #[inline]
    fn collection_as_slice(&self) -> Option<&[Self::Value]> {
        Some(self.as_slice())
    }
}
