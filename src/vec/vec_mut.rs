use super::{Equivalent, ValueCollectionRef, ValueContain, VecCollectionRef};
use core::slice;
use smallvec::SmallVec;
use std::collections::{self, vec_deque};

pub trait VecCollectionMut<E = <Self as ValueContain>::Value>
where
    Self: ValueCollectionRef<E> + VecCollectionRef<E>,
    E: ?Sized,
{
    type ValuesMut<'a>: Iterator<Item = &'a mut Self::Value>
    where
        Self: 'a,
        Self::Value: 'a;

    /// Returns a mutable reference to the value in the collection, if any,
    /// that is equal to the given value.
    ///
    /// # Note
    ///
    /// The lookup value `E` must be either a borrowed form of the container's
    /// value type (ie `Self::Value: Borrow<E>`) or, if implemented for this
    /// container, `E: Equivalent<Self::Value>`.
    ///
    /// Note that a container that implements `E: Equivalent<Self::Value>` will
    /// also accept all `E` lookup values such as `Self::Value: Borrow<E>`, but
    /// the converse is not true.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::VecCollectionMut;
    /// use core::borrow::Borrow;
    ///
    /// let mut vec: Vec<String> = vec!["a".into(), "b".into()];
    ///
    /// // You do not need to specify the type E when calling this `VecCollectionMut`
    /// // method directly.
    /// let value = vec.get_value_mut("a").unwrap();
    /// assert_eq!(value, &mut "a");
    /// value.push_str(" char");
    /// assert_eq!(vec.get_value_mut("a char"), Some(&mut "a char".to_owned()));
    ///
    /// // Also, there is no need to specify the type E when using VecCollectionMut
    /// // as a trait bound (although specifying it will give more flexibility).
    /// fn get_value_mut<'a, T>(cont: &'a mut T, key: &T::Value) -> Option<&'a mut T::Value>
    /// where
    ///     T: VecCollectionMut + ?Sized,
    /// {
    ///     cont.get_value_mut(key)
    /// }
    ///
    /// fn get_value_mut_borrow_key<'a, T, Q>(cont: &'a mut T, key: &Q) -> Option<&'a mut T::Value>
    /// where
    ///     Q: ?Sized,
    ///     T: VecCollectionMut<Q> + ?Sized,
    ///     T::Value: Borrow<Q>,
    /// {
    ///     cont.get_value_mut(key)
    /// }
    ///
    /// assert_eq!(
    ///     get_value_mut(&mut vec, &"b".to_string()),
    ///     Some(&mut "b".to_owned())
    /// );
    /// // Err: expected struct `String`, found `str`
    /// // assert_eq!(get_value_mut(&mut vec, "a"), Some(&mut "b".to_owned()));
    ///
    /// assert_eq!(
    ///     get_value_mut_borrow_key(&mut vec, &"b".to_string()),
    ///     Some(&mut "b".to_owned())
    /// );
    /// assert_eq!(
    ///     get_value_mut_borrow_key(&mut vec, "b"),
    ///     Some(&mut "b".to_owned())
    /// );
    /// ```
    fn get_value_mut(&mut self, value: &E) -> Option<&mut Self::Value>;
    fn get_value_mut_at(&mut self, index: usize) -> Option<&mut Self::Value>;
    fn collection_as_mut_slice(&mut self) -> Option<&mut [Self::Value]>;
    fn collection_append(&mut self, other: &mut Self);
    fn collection_insert(&mut self, index: usize, value: Self::Value);
    fn collection_push(&mut self, value: Self::Value);
    fn collection_pop(&mut self) -> Option<Self::Value>;
    fn collection_remove(&mut self, index: usize) -> Self::Value;
    fn collection_swap(&mut self, i: usize, j: usize);
    fn collection_swap_remove(&mut self, index: usize) -> Self::Value;
    fn collection_clear(&mut self);
    fn collection_retain<F>(&mut self, f: F)
    where
        F: FnMut(&Self::Value) -> bool;
    fn collection_values_mut(&mut self) -> Self::ValuesMut<'_>;
}

#[test]
fn test() {
    use crate::VecCollectionMut;
    use core::borrow::Borrow;

    let mut vec: Vec<String> = vec!["a".into(), "b".into()];

    // You do not need to specify the type E when calling this `VecCollectionMut`
    // method directly.
    let value = vec.get_value_mut("a").unwrap();
    assert_eq!(value, &mut "a");
    value.push_str(" char");
    assert_eq!(vec.get_value_mut("a char"), Some(&mut "a char".to_owned()));

    // Also, there is no need to specify the type E when using VecCollectionMut
    // as a trait bound (although specifying it will give more flexibility).
    fn get_value_mut<'a, T>(cont: &'a mut T, key: &T::Value) -> Option<&'a mut T::Value>
    where
        T: VecCollectionMut + ?Sized,
    {
        cont.get_value_mut(key)
    }

    fn get_value_mut_borrow_key<'a, T, Q>(cont: &'a mut T, key: &Q) -> Option<&'a mut T::Value>
    where
        Q: ?Sized,
        T: VecCollectionMut<Q> + ?Sized,
        T::Value: Borrow<Q>,
    {
        cont.get_value_mut(key)
    }

    assert_eq!(
        get_value_mut(&mut vec, &"b".to_string()),
        Some(&mut "b".to_owned())
    );
    // Err: expected struct `String`, found `str`
    // assert_eq!(get_value_mut(&mut vec, "a"), Some(&mut "b".to_owned()));

    assert_eq!(
        get_value_mut_borrow_key(&mut vec, &"b".to_string()),
        Some(&mut "b".to_owned())
    );
    assert_eq!(
        get_value_mut_borrow_key(&mut vec, "b"),
        Some(&mut "b".to_owned())
    );
}

impl<T, E: ?Sized> VecCollectionMut<E> for &mut T
where
    T: VecCollectionMut<E>,
{
    type ValuesMut<'a> = T::ValuesMut<'a>
    where
        Self: 'a,
        Self::Value: 'a;

    #[inline]
    fn collection_append(&mut self, other: &mut Self) {
        <T as VecCollectionMut<E>>::collection_append(self, other)
    }

    #[inline]
    fn collection_insert(&mut self, index: usize, value: Self::Value) {
        <T as VecCollectionMut<E>>::collection_insert(self, index, value)
    }

    #[inline]
    fn collection_push(&mut self, value: Self::Value) {
        <T as VecCollectionMut<E>>::collection_push(self, value)
    }

    #[inline]
    fn collection_pop(&mut self) -> Option<Self::Value> {
        <T as VecCollectionMut<E>>::collection_pop(self)
    }

    #[inline]
    fn collection_remove(&mut self, index: usize) -> Self::Value {
        <T as VecCollectionMut<E>>::collection_remove(self, index)
    }

    #[inline]
    fn collection_swap(&mut self, i: usize, j: usize) {
        <T as VecCollectionMut<E>>::collection_swap(self, i, j)
    }

    #[inline]
    fn collection_swap_remove(&mut self, index: usize) -> Self::Value {
        <T as VecCollectionMut<E>>::collection_swap_remove(self, index)
    }

    #[inline]
    fn get_value_mut_at(&mut self, index: usize) -> Option<&mut Self::Value> {
        <T as VecCollectionMut<E>>::get_value_mut_at(self, index)
    }

    #[inline]
    fn collection_as_mut_slice(&mut self) -> Option<&mut [Self::Value]> {
        <T as VecCollectionMut<E>>::collection_as_mut_slice(self)
    }

    #[inline]
    fn collection_retain<F>(&mut self, f: F)
    where
        F: FnMut(&Self::Value) -> bool,
    {
        <T as VecCollectionMut<E>>::collection_retain(self, f)
    }

    #[inline]
    fn collection_clear(&mut self) {
        <T as VecCollectionMut<E>>::collection_clear(self)
    }

    #[inline]
    fn get_value_mut(&mut self, value: &E) -> Option<&mut Self::Value> {
        <T as VecCollectionMut<E>>::get_value_mut(self, value)
    }

    #[inline]
    fn collection_values_mut(&mut self) -> Self::ValuesMut<'_> {
        <T as VecCollectionMut<E>>::collection_values_mut(self)
    }
}

impl<T, E> VecCollectionMut<E> for Vec<T>
where
    E: ?Sized + Equivalent<T>,
{
    type ValuesMut<'a> = slice::IterMut<'a, T> where Self: 'a, T: 'a;

    #[inline]
    fn collection_append(&mut self, other: &mut Self) {
        self.append(other)
    }

    #[inline]
    fn collection_insert(&mut self, index: usize, value: Self::Value) {
        self.insert(index, value)
    }

    #[inline]
    fn collection_push(&mut self, value: Self::Value) {
        self.push(value)
    }

    #[inline]
    fn collection_pop(&mut self) -> Option<Self::Value> {
        self.pop()
    }

    #[inline]
    fn collection_remove(&mut self, index: usize) -> Self::Value {
        self.remove(index)
    }

    #[inline]
    fn collection_swap(&mut self, i: usize, j: usize) {
        self.as_mut_slice().swap(i, j)
    }

    #[inline]
    fn collection_swap_remove(&mut self, index: usize) -> Self::Value {
        self.swap_remove(index)
    }

    #[inline]
    fn get_value_mut_at(&mut self, index: usize) -> Option<&mut Self::Value> {
        self.get_mut(index)
    }

    #[inline]
    fn collection_as_mut_slice(&mut self) -> Option<&mut [Self::Value]> {
        Some(self.as_mut_slice())
    }

    #[inline]
    fn collection_retain<F>(&mut self, f: F)
    where
        F: FnMut(&Self::Value) -> bool,
    {
        self.retain(f)
    }

    #[inline]
    fn get_value_mut(&mut self, value: &E) -> Option<&mut Self::Value> {
        self.iter_mut().find(|x| Equivalent::equivalent(value, *x))
    }

    #[inline]
    fn collection_clear(&mut self) {
        self.clear()
    }

    #[inline]
    fn collection_values_mut(&mut self) -> Self::ValuesMut<'_> {
        self.iter_mut()
    }
}

impl<T, E> VecCollectionMut<E> for im::Vector<T>
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
    fn collection_as_mut_slice(&mut self) -> Option<&mut [Self::Value]> {
        None
    }

    #[inline]
    fn collection_append(&mut self, other: &mut Self) {
        self.append(other.clone())
    }

    #[inline]
    fn collection_insert(&mut self, index: usize, value: Self::Value) {
        self.insert(index, value)
    }

    #[inline]
    fn collection_push(&mut self, value: Self::Value) {
        self.push_back(value)
    }

    #[inline]
    fn collection_pop(&mut self) -> Option<Self::Value> {
        self.pop_back()
    }

    #[inline]
    fn collection_remove(&mut self, index: usize) -> Self::Value {
        self.remove(index)
    }

    #[inline]
    fn collection_swap(&mut self, i: usize, j: usize) {
        self.swap(i, j)
    }

    #[inline]
    fn collection_swap_remove(&mut self, index: usize) -> Self::Value {
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
    fn collection_retain<F>(&mut self, f: F)
    where
        F: FnMut(&Self::Value) -> bool,
    {
        self.retain(f)
    }

    #[inline]
    fn get_value_mut(&mut self, value: &E) -> Option<&mut Self::Value> {
        self.iter_mut().find(|x| Equivalent::equivalent(value, *x))
    }

    #[inline]
    fn collection_clear(&mut self) {
        self.clear()
    }

    #[inline]
    fn collection_values_mut(&mut self) -> Self::ValuesMut<'_> {
        self.iter_mut()
    }
}

impl<T, E> VecCollectionMut<E> for collections::VecDeque<T>
where
    E: ?Sized + Equivalent<T>,
{
    type ValuesMut<'a> = vec_deque::IterMut<'a, T> where Self: 'a, T: 'a;

    #[inline]
    fn get_value_mut_at(&mut self, index: usize) -> Option<&mut Self::Value> {
        self.get_mut(index)
    }

    #[inline]
    fn collection_as_mut_slice(&mut self) -> Option<&mut [Self::Value]> {
        Some(self.make_contiguous())
    }

    #[inline]
    fn collection_append(&mut self, other: &mut Self) {
        self.append(other)
    }

    #[inline]
    fn collection_insert(&mut self, index: usize, value: Self::Value) {
        self.insert(index, value)
    }

    #[inline]
    fn collection_push(&mut self, value: Self::Value) {
        self.push_back(value)
    }

    #[inline]
    fn collection_pop(&mut self) -> Option<Self::Value> {
        self.pop_back()
    }

    #[inline]
    fn collection_remove(&mut self, index: usize) -> Self::Value {
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
    fn collection_swap(&mut self, i: usize, j: usize) {
        self.swap(i, j)
    }

    #[inline]
    fn collection_swap_remove(&mut self, index: usize) -> Self::Value {
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
    fn collection_retain<F>(&mut self, f: F)
    where
        F: FnMut(&Self::Value) -> bool,
    {
        self.retain(f)
    }

    #[inline]
    fn get_value_mut(&mut self, value: &E) -> Option<&mut Self::Value> {
        self.iter_mut().find(|x| Equivalent::equivalent(value, *x))
    }

    #[inline]
    fn collection_clear(&mut self) {
        self.clear()
    }

    #[inline]
    fn collection_values_mut(&mut self) -> Self::ValuesMut<'_> {
        self.iter_mut()
    }
}

impl<T, A, E> VecCollectionMut<E> for SmallVec<A>
where
    A: smallvec::Array<Item = T>,
    E: ?Sized + Equivalent<T>,
{
    type ValuesMut<'a> = slice::IterMut<'a, T> where Self: 'a, T: 'a;

    #[inline]
    fn collection_append(&mut self, other: &mut Self) {
        self.append(other)
    }

    #[inline]
    fn collection_insert(&mut self, index: usize, value: Self::Value) {
        self.insert(index, value)
    }

    #[inline]
    fn collection_push(&mut self, value: Self::Value) {
        self.push(value)
    }

    #[inline]
    fn collection_pop(&mut self) -> Option<Self::Value> {
        self.pop()
    }

    #[inline]
    fn collection_remove(&mut self, index: usize) -> Self::Value {
        self.remove(index)
    }

    #[inline]
    fn collection_swap(&mut self, i: usize, j: usize) {
        self.as_mut_slice().swap(i, j)
    }

    #[inline]
    fn collection_swap_remove(&mut self, index: usize) -> Self::Value {
        self.swap_remove(index)
    }

    #[inline]
    fn get_value_mut_at(&mut self, index: usize) -> Option<&mut Self::Value> {
        self.get_mut(index)
    }

    #[inline]
    fn collection_as_mut_slice(&mut self) -> Option<&mut [Self::Value]> {
        Some(self.as_mut_slice())
    }

    #[inline]
    fn collection_retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&Self::Value) -> bool,
    {
        self.retain(|x| f(x))
    }

    #[inline]
    fn get_value_mut(&mut self, value: &E) -> Option<&mut Self::Value> {
        self.iter_mut().find(|x| Equivalent::equivalent(value, *x))
    }

    #[inline]
    fn collection_clear(&mut self) {
        self.clear()
    }

    #[inline]
    fn collection_values_mut(&mut self) -> Self::ValuesMut<'_> {
        self.iter_mut()
    }
}
