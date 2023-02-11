use super::{Equivalent, ValueContain, ValueCollectionRef, VecContainerRef};
use core::slice;
use smallvec::SmallVec;
use std::collections::{self, vec_deque};

pub trait VecContainerMut<E = <Self as ValueContain>::Value>
where
    Self: ValueCollectionRef<E> + VecContainerRef<E>,
    E: ?Sized,
{
    type ValuesMut<'a>: Iterator<Item = &'a mut Self::Value>
    where
        Self: 'a,
        Self::Value: 'a;
    fn get_value_mut(&mut self, key: &E) -> Option<&mut Self::Value>;
    fn get_value_mut_at(&mut self, index: usize) -> Option<&mut Self::Value>;
    fn as_mut_slice(&mut self) -> Option<&mut [Self::Value]>;
    fn cont_append(&mut self, other: &mut Self);
    fn cont_insert(&mut self, index: usize, value: Self::Value);
    fn cont_push(&mut self, value: Self::Value);
    fn cont_pop(&mut self) -> Option<Self::Value>;
    fn cont_remove(&mut self, index: usize) -> Self::Value;
    fn cont_swap(&mut self, i: usize, j: usize);
    fn cont_swap_remove(&mut self, index: usize) -> Self::Value;
    fn cont_clear(&mut self);
    fn cont_retain<F>(&mut self, f: F)
    where
        F: FnMut(&Self::Value) -> bool;
    fn cont_values_mut(&mut self) -> Self::ValuesMut<'_>;
}

impl<T, E: ?Sized> VecContainerMut<E> for &mut T
where
    T: VecContainerMut<E>,
{
    type ValuesMut<'a> = T::ValuesMut<'a>
    where
        Self: 'a,
        Self::Value: 'a;

    #[inline]
    fn cont_append(&mut self, other: &mut Self) {
        <T as VecContainerMut<E>>::cont_append(self, other)
    }

    #[inline]
    fn cont_insert(&mut self, index: usize, value: Self::Value) {
        <T as VecContainerMut<E>>::cont_insert(self, index, value)
    }

    #[inline]
    fn cont_push(&mut self, value: Self::Value) {
        <T as VecContainerMut<E>>::cont_push(self, value)
    }

    #[inline]
    fn cont_pop(&mut self) -> Option<Self::Value> {
        <T as VecContainerMut<E>>::cont_pop(self)
    }

    #[inline]
    fn cont_remove(&mut self, index: usize) -> Self::Value {
        <T as VecContainerMut<E>>::cont_remove(self, index)
    }

    #[inline]
    fn cont_swap(&mut self, i: usize, j: usize) {
        <T as VecContainerMut<E>>::cont_swap(self, i, j)
    }

    #[inline]
    fn cont_swap_remove(&mut self, index: usize) -> Self::Value {
        <T as VecContainerMut<E>>::cont_swap_remove(self, index)
    }

    #[inline]
    fn get_value_mut_at(&mut self, index: usize) -> Option<&mut Self::Value> {
        <T as VecContainerMut<E>>::get_value_mut_at(self, index)
    }

    #[inline]
    fn as_mut_slice(&mut self) -> Option<&mut [Self::Value]> {
        <T as VecContainerMut<E>>::as_mut_slice(self)
    }

    #[inline]
    fn cont_retain<F>(&mut self, f: F)
    where
        F: FnMut(&Self::Value) -> bool,
    {
        <T as VecContainerMut<E>>::cont_retain(self, f)
    }

    #[inline]
    fn cont_clear(&mut self) {
        <T as VecContainerMut<E>>::cont_clear(self)
    }

    #[inline]
    fn get_value_mut(&mut self, key: &E) -> Option<&mut Self::Value> {
        <T as VecContainerMut<E>>::get_value_mut(self, key)
    }

    #[inline]
    fn cont_values_mut(&mut self) -> Self::ValuesMut<'_> {
        <T as VecContainerMut<E>>::cont_values_mut(self)
    }
}

impl<T, E> VecContainerMut<E> for Vec<T>
where
    E: ?Sized + Equivalent<T>,
{
    type ValuesMut<'a> = slice::IterMut<'a, T> where Self: 'a, T: 'a;

    #[inline]
    fn cont_append(&mut self, other: &mut Self) {
        self.append(other)
    }

    #[inline]
    fn cont_insert(&mut self, index: usize, value: Self::Value) {
        self.insert(index, value)
    }

    #[inline]
    fn cont_push(&mut self, value: Self::Value) {
        self.push(value)
    }

    #[inline]
    fn cont_pop(&mut self) -> Option<Self::Value> {
        self.pop()
    }

    #[inline]
    fn cont_remove(&mut self, index: usize) -> Self::Value {
        self.remove(index)
    }

    #[inline]
    fn cont_swap(&mut self, i: usize, j: usize) {
        self.as_mut_slice().swap(i, j)
    }

    #[inline]
    fn cont_swap_remove(&mut self, index: usize) -> Self::Value {
        self.swap_remove(index)
    }

    #[inline]
    fn get_value_mut_at(&mut self, index: usize) -> Option<&mut Self::Value> {
        self.get_mut(index)
    }

    #[inline]
    fn as_mut_slice(&mut self) -> Option<&mut [Self::Value]> {
        Some(self.as_mut_slice())
    }

    #[inline]
    fn cont_retain<F>(&mut self, f: F)
    where
        F: FnMut(&Self::Value) -> bool,
    {
        self.retain(f)
    }

    #[inline]
    fn get_value_mut(&mut self, key: &E) -> Option<&mut Self::Value> {
        self.iter_mut().find(|x| Equivalent::equivalent(key, *x))
    }

    #[inline]
    fn cont_clear(&mut self) {
        self.clear()
    }

    #[inline]
    fn cont_values_mut(&mut self) -> Self::ValuesMut<'_> {
        self.iter_mut()
    }
}

impl<T, E> VecContainerMut<E> for im::Vector<T>
where
    T: Clone,
    E: ?Sized + Equivalent<T>,
{
    type ValuesMut<'a> = im::vector::IterMut<'a, T> where Self: 'a, T: 'a;

    #[inline]
    fn get_value_mut_at(&mut self, index: usize) -> Option<&mut Self::Value> {
        self.get_mut(index)
    }

    #[inline]
    fn as_mut_slice(&mut self) -> Option<&mut [Self::Value]> {
        None
    }

    #[inline]
    fn cont_append(&mut self, other: &mut Self) {
        self.append(other.clone())
    }

    #[inline]
    fn cont_insert(&mut self, index: usize, value: Self::Value) {
        self.insert(index, value)
    }

    #[inline]
    fn cont_push(&mut self, value: Self::Value) {
        self.push_back(value)
    }

    #[inline]
    fn cont_pop(&mut self) -> Option<Self::Value> {
        self.pop_back()
    }

    #[inline]
    fn cont_remove(&mut self, index: usize) -> Self::Value {
        self.remove(index)
    }

    #[inline]
    fn cont_swap(&mut self, i: usize, j: usize) {
        self.swap(i, j)
    }

    #[inline]
    fn cont_swap_remove(&mut self, index: usize) -> Self::Value {
        #[cold]
        #[inline(never)]
        fn assert_failed(index: usize, len: usize) {
            panic!("swap_remove index (is {index}) should be < len (is {len})");
        }

        let len = im::Vector::<T>::len(self);
        if index >= len {
            assert_failed(index, len);
        }
        self.swap(index, len - 1);
        self.pop_back().unwrap()
    }

    #[inline]
    fn cont_retain<F>(&mut self, f: F)
    where
        F: FnMut(&Self::Value) -> bool,
    {
        self.retain(f)
    }

    #[inline]
    fn get_value_mut(&mut self, key: &E) -> Option<&mut Self::Value> {
        self.iter_mut().find(|x| Equivalent::equivalent(key, *x))
    }

    #[inline]
    fn cont_clear(&mut self) {
        self.clear()
    }

    #[inline]
    fn cont_values_mut(&mut self) -> Self::ValuesMut<'_> {
        self.iter_mut()
    }
}

impl<T, E> VecContainerMut<E> for collections::VecDeque<T>
where
    E: ?Sized + Equivalent<T>,
{
    type ValuesMut<'a> = vec_deque::IterMut<'a, T> where Self: 'a, T: 'a;

    #[inline]
    fn get_value_mut_at(&mut self, index: usize) -> Option<&mut Self::Value> {
        self.get_mut(index)
    }

    #[inline]
    fn as_mut_slice(&mut self) -> Option<&mut [Self::Value]> {
        None
    }

    #[inline]
    fn cont_append(&mut self, other: &mut Self) {
        self.append(other)
    }

    #[inline]
    fn cont_insert(&mut self, index: usize, value: Self::Value) {
        self.insert(index, value)
    }

    #[inline]
    fn cont_push(&mut self, value: Self::Value) {
        self.push_back(value)
    }

    #[inline]
    fn cont_pop(&mut self) -> Option<Self::Value> {
        self.pop_back()
    }

    #[inline]
    fn cont_remove(&mut self, index: usize) -> Self::Value {
        #[cold]
        #[inline(never)]
        fn assert_failed(index: usize, len: usize) {
            panic!("remove index (is {index}) should be < len (is {len})");
        }

        let len = collections::VecDeque::<T>::len(self);
        if index >= len {
            assert_failed(index, len);
        }
        self.remove(index).unwrap()
    }

    #[inline]
    fn cont_swap(&mut self, i: usize, j: usize) {
        self.swap(i, j)
    }

    #[inline]
    fn cont_swap_remove(&mut self, index: usize) -> Self::Value {
        #[cold]
        #[inline(never)]
        fn assert_failed(index: usize, len: usize) {
            panic!("swap_remove index (is {index}) should be < len (is {len})");
        }

        let len = collections::VecDeque::<T>::len(self);
        if index >= len {
            assert_failed(index, len);
        }
        self.swap_remove_back(index).unwrap()
    }

    #[inline]
    fn cont_retain<F>(&mut self, f: F)
    where
        F: FnMut(&Self::Value) -> bool,
    {
        self.retain(f)
    }

    #[inline]
    fn get_value_mut(&mut self, key: &E) -> Option<&mut Self::Value> {
        self.iter_mut().find(|x| Equivalent::equivalent(key, *x))
    }

    #[inline]
    fn cont_clear(&mut self) {
        self.clear()
    }

    #[inline]
    fn cont_values_mut(&mut self) -> Self::ValuesMut<'_> {
        self.iter_mut()
    }
}

impl<T, A, E> VecContainerMut<E> for SmallVec<A>
where
    A: smallvec::Array<Item = T>,
    E: ?Sized + Equivalent<T>,
{
    type ValuesMut<'a> = slice::IterMut<'a, T> where Self: 'a, T: 'a;

    #[inline]
    fn cont_append(&mut self, other: &mut Self) {
        self.append(other)
    }

    #[inline]
    fn cont_insert(&mut self, index: usize, value: Self::Value) {
        self.insert(index, value)
    }

    #[inline]
    fn cont_push(&mut self, value: Self::Value) {
        self.push(value)
    }

    #[inline]
    fn cont_pop(&mut self) -> Option<Self::Value> {
        self.pop()
    }

    #[inline]
    fn cont_remove(&mut self, index: usize) -> Self::Value {
        self.remove(index)
    }

    #[inline]
    fn cont_swap(&mut self, i: usize, j: usize) {
        self.as_mut_slice().swap(i, j)
    }

    #[inline]
    fn cont_swap_remove(&mut self, index: usize) -> Self::Value {
        self.swap_remove(index)
    }

    #[inline]
    fn get_value_mut_at(&mut self, index: usize) -> Option<&mut Self::Value> {
        self.get_mut(index)
    }

    #[inline]
    fn as_mut_slice(&mut self) -> Option<&mut [Self::Value]> {
        Some(self.as_mut_slice())
    }

    #[inline]
    fn cont_retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&Self::Value) -> bool,
    {
        self.retain(|x| f(x))
    }

    #[inline]
    fn get_value_mut(&mut self, key: &E) -> Option<&mut Self::Value> {
        self.iter_mut().find(|x| Equivalent::equivalent(key, *x))
    }

    #[inline]
    fn cont_clear(&mut self) {
        self.clear()
    }

    #[inline]
    fn cont_values_mut(&mut self) -> Self::ValuesMut<'_> {
        self.iter_mut()
    }
}
