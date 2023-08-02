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
    ///     T: VecCollectionMut,
    /// {
    ///     cont.get_value_mut(key)
    /// }
    ///
    /// fn get_value_mut_borrow_key<'a, T, Q>(cont: &'a mut T, key: &Q) -> Option<&'a mut T::Value>
    /// where
    ///     Q: ?Sized,
    ///     T: VecCollectionMut<Q>,
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

    /// Returns a mutable reference to the value at the `index` in
    /// the vector, or `None` if the `index` is out of bounds.
    ///
    /// The implementation of the method depends on the container type,
    /// so it can take as `O(1)` so as `O(log n)` time.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::VecCollectionMut;
    /// let mut vec: Vec<String> = vec!["a".into(), "b".into()];
    ///
    /// // Unfortunately, when calling the `VecCollectionMut` methods directly,
    /// // you need to specify the type `E` because the compiler can't infer it.
    /// let value = VecCollectionMut::<str>::get_value_mut_at(&mut vec, 0).unwrap();
    /// assert_eq!(value, &mut "a");
    /// value.push_str(" char");
    /// assert_eq!(
    ///     VecCollectionMut::<str>::get_value_mut_at(&mut vec, 0),
    ///     Some(&mut "a char".to_owned())
    /// );
    ///
    /// // But you do not need to specify the type E when using VecCollectionMut
    /// // as trait bound
    /// fn get_value_mut_at<'a, T>(cont: &'a mut T, idx: usize) -> Option<&'a mut T::Value>
    /// where
    ///     T: VecCollectionMut,
    /// {
    ///     cont.get_value_mut_at(idx)
    /// }
    ///
    /// assert_eq!(get_value_mut_at(&mut vec, 1), Some(&mut "b".to_owned()));
    /// ```
    fn get_value_mut_at(&mut self, index: usize) -> Option<&mut Self::Value>;

    /// Extracts a mutable slice containing the entire vector. This method
    /// does not exist for some container types, so [`Option`] is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::VecCollectionMut;
    /// use std::collections::VecDeque;
    ///
    /// let mut vec = vec!["Tooth".to_owned(), "Easter".into(), "Jack".into()];
    /// // Unfortunately, when calling the `VecCollectionMut` methods directly,
    /// // you need to specify the type `E` because the compiler can't infer it.
    /// assert_eq!(
    ///     &mut ["Tooth", "Easter", "Jack"],
    ///     VecCollectionMut::<str>::collection_as_mut_slice(&mut vec).unwrap()
    /// );
    ///
    /// // But you do not need to specify the type E when using VecCollectionMut
    /// // as trait bound
    /// fn as_mut_slice<T>(collection: &mut T) -> Option<&mut [T::Value]>
    /// where
    ///     T: VecCollectionMut,
    /// {
    ///     collection.collection_as_mut_slice()
    /// }
    /// as_mut_slice(&mut vec)
    ///     .unwrap()
    ///     .into_iter()
    ///     .zip(["fairy", "Bunny", "Frost"])
    ///     .for_each(|(string, str)| {
    ///         string.push(' ');
    ///         string.push_str(str)
    ///     });
    /// assert_eq!(
    ///     &mut ["Tooth fairy", "Easter Bunny", "Jack Frost"],
    ///     as_mut_slice(&mut vec).unwrap()
    /// );
    ///
    /// let mut vec = VecDeque::from(["Joe", "Mike", "Robert"]);
    /// assert_eq!(
    ///     &mut ["Joe", "Mike", "Robert"],
    ///     as_mut_slice(&mut vec).unwrap()
    /// );
    /// ```
    fn collection_as_mut_slice(&mut self) -> Option<&mut [Self::Value]>;

    /// Moves all the elements of `other` into `self`, leaving `other` empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::VecCollectionMut;
    ///
    /// let mut first_vec = vec![1, 2, 3];
    /// let mut second_vec = vec![4, 5, 6];
    ///
    /// // Unfortunately, when calling the `VecCollectionMut` methods directly,
    /// // you need to specify the type `E` because the compiler can't infer it.
    /// VecCollectionMut::<i32>::collection_append(&mut first_vec, &mut second_vec);
    /// assert_eq!(first_vec, [1, 2, 3, 4, 5, 6]);
    /// assert_eq!(second_vec, []);
    ///
    /// // But you do not need to specify the type E when using VecCollectionMut
    /// // as trait bound
    /// fn append<T: VecCollectionMut>(lhs: &mut T, rhs: &mut T) {
    ///     lhs.collection_append(rhs)
    /// }
    ///
    /// let mut third_vec = vec![7, 8, 9];
    /// append(&mut first_vec, &mut third_vec);
    /// assert_eq!(first_vec, [1, 2, 3, 4, 5, 6, 7, 8, 9]);
    /// assert_eq!(third_vec, []);
    /// ```
    fn collection_append(&mut self, other: &mut Self);

    /// Inserts an element at position `index` within the vector.
    ///
    /// # Note
    ///
    /// `Index` must be less than or equal to the length of the vector. Calling
    /// this function may cause shifting all elements after it to the right.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::VecCollectionMut;
    ///
    /// let mut vec = vec![1, 2, 3];
    /// // Unfortunately, when calling the `VecCollectionMut` methods directly,
    /// // you need to specify the type `E` because the compiler can't infer it.
    /// VecCollectionMut::<i32>::collection_insert(&mut vec, 1, 4);
    /// assert_eq!(vec, [1, 4, 2, 3]);
    ///
    /// // But you do not need to specify the type E when using VecCollectionMut
    /// // as trait bound
    /// fn insert<T: VecCollectionMut>(vec: &mut T, idx: usize, value: T::Value) {
    ///     vec.collection_insert(idx, value);
    /// }
    ///
    /// insert(&mut vec, 4, 5);
    /// assert_eq!(vec, [1, 4, 2, 3, 5]);
    /// ```
    fn collection_insert(&mut self, index: usize, value: Self::Value);

    /// Appends an element to the back of a collection.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::VecCollectionMut;
    ///
    /// let mut vec = vec![1, 2, 3];
    /// // Unfortunately, when calling the `VecCollectionMut` methods directly,
    /// // you need to specify the type `E` because the compiler can't infer it.
    /// VecCollectionMut::<i32>::collection_push(&mut vec, 4);
    /// assert_eq!(vec, [1, 2, 3, 4]);
    ///
    /// // But you do not need to specify the type E when using VecCollectionMut
    /// // as trait bound
    /// fn push<T: VecCollectionMut>(vec: &mut T, value: T::Value) {
    ///     vec.collection_push(value);
    /// }
    ///
    /// push(&mut vec, 5);
    /// assert_eq!(vec, [1, 2, 3, 4, 5]);
    /// ```
    fn collection_push(&mut self, value: Self::Value);

    /// Removes the last element from a vector and returns it, or [`None`]
    /// if it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::VecCollectionMut;
    ///
    /// let mut vec = vec![1, 2, 3, 4];
    /// // Unfortunately, when calling the `VecCollectionMut` methods directly,
    /// // you need to specify the type `E` because the compiler can't infer it.
    /// assert_eq!(VecCollectionMut::<i32>::collection_pop(&mut vec), Some(4));
    /// assert_eq!(vec, [1, 2, 3]);
    ///
    /// // But you do not need to specify the type E when using VecCollectionMut
    /// // as trait bound
    /// fn pop<T: VecCollectionMut>(vec: &mut T) -> Option<T::Value> {
    ///     vec.collection_pop()
    /// }
    ///
    /// assert_eq!(pop(&mut vec), Some(3));
    /// assert_eq!(vec, [1, 2]);
    /// ```
    fn collection_pop(&mut self) -> Option<Self::Value>;

    /// Removes and returns the element at position `index` within the vector.
    ///
    /// # Note
    ///
    /// `Index` must be less than or equal to the length of the vector. Calling
    /// this function may cause shifting all elements after it to the left.
    ///
    /// If you don't need the order of elements to be preserved, using
    /// [`collection_swap`] can improve performance.
    ///
    /// [`collection_swap`]: VecCollectionMut::collection_swap
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::VecCollectionMut;
    ///
    /// let mut vec = vec![1, 2, 3, 4];
    /// // Unfortunately, when calling the `VecCollectionMut` methods directly,
    /// // you need to specify the type `E` because the compiler can't infer it.
    /// assert_eq!(VecCollectionMut::<i32>::collection_remove(&mut vec, 3), 4);
    /// assert_eq!(vec, [1, 2, 3]);
    ///
    /// // But you do not need to specify the type E when using VecCollectionMut
    /// // as trait bound
    /// fn remove<T: VecCollectionMut>(vec: &mut T, idx: usize) -> T::Value {
    ///     vec.collection_remove(idx)
    /// }
    ///
    /// assert_eq!(remove(&mut vec, 1), 2);
    /// assert_eq!(vec, [1, 3]);
    /// ```
    fn collection_remove(&mut self, index: usize) -> Self::Value;

    /// Swaps two elements in the slice.
    ///
    /// # Arguments
    ///
    /// * `i` - The index of the first element
    /// * `j` - The index of the second element
    ///
    /// # Note
    ///
    /// Both indices must be less than or equal to the length of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::VecCollectionMut;
    ///
    /// let mut vec = vec!["a", "b", "c", "d", "e"];
    /// // Unfortunately, when calling the `VecCollectionMut` methods directly,
    /// // you need to specify the type `E` because the compiler can't infer it.
    /// VecCollectionMut::<str>::collection_swap(&mut vec, 2, 4);
    /// assert_eq!(vec, ["a", "b", "e", "d", "c"]);
    ///
    /// // But you do not need to specify the type E when using VecCollectionMut
    /// // as trait bound
    /// fn swap<T: VecCollectionMut>(vec: &mut T, i: usize, j: usize) {
    ///     vec.collection_swap(i, j);
    /// }
    ///
    /// swap(&mut vec, 0, 2);
    /// assert_eq!(vec, ["e", "b", "a", "d", "c"]);
    /// ```
    fn collection_swap(&mut self, i: usize, j: usize);

    /// Removes an element from the vector and returns it.
    ///
    /// The removed element is replaced by the last element of the vector.
    ///
    /// This does not preserve ordering. If you need to preserve the element
    /// order, use [`collection_remove`] instead.
    ///
    /// [`collection_remove`]: VecCollectionMut::collection_remove
    ///
    /// # Note
    ///
    /// `Index` must be less than or equal to the length of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::VecCollectionMut;
    ///
    /// let mut vec = vec!["a", "b", "c", "d", "e"];
    /// // Unfortunately, when calling the `VecCollectionMut` methods directly,
    /// // you need to specify the type `E` because the compiler can't infer it.
    /// assert_eq!(
    ///     VecCollectionMut::<str>::collection_swap_remove(&mut vec, 2),
    ///     "c"
    /// );
    /// assert_eq!(vec, ["a", "b", "e", "d"]);
    ///
    /// // But you do not need to specify the type E when using VecCollectionMut
    /// // as trait bound
    /// fn swap_remove<T>(vec: &mut T, idx: usize) -> T::Value
    /// where
    ///     T: VecCollectionMut,
    /// {
    ///     vec.collection_swap_remove(idx)
    /// }
    ///
    /// assert_eq!(swap_remove(&mut vec, 0), "a");
    /// assert_eq!(vec, ["d", "b", "e"]);
    /// ```
    fn collection_swap_remove(&mut self, index: usize) -> Self::Value;

    /// Clears the vector, removing all values.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::VecCollectionMut;
    ///
    /// let mut vec = vec!["a", "b", "c", "d", "e"];
    /// // Unfortunately, when calling the `VecCollectionMut` methods directly,
    /// // you need to specify the type `E` because the compiler can't infer it.
    /// VecCollectionMut::<str>::collection_clear(&mut vec);
    /// assert!(vec.is_empty());
    ///
    /// // But you do not need to specify the type E when using VecCollectionMut
    /// // as trait bound
    /// fn clear<T: VecCollectionMut>(vec: &mut T) {
    ///     vec.collection_clear();
    /// }
    ///
    /// let mut vec = vec![1, 2, 3, 4, 5];
    /// clear(&mut vec);
    /// assert!(vec.is_empty());
    /// ```
    fn collection_clear(&mut self);

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` for which `f(&e)` returns `false`.
    /// This method operates in place, visiting each element exactly once in the
    /// original order, and preserves the order of the retained elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::VecCollectionMut;
    ///
    /// let mut vec = vec![1, 2, 3, 4, 5, 6];
    /// // Unfortunately, when calling the `VecCollectionMut` methods directly,
    /// // you need to specify the type `E` because the compiler can't infer it.
    /// VecCollectionMut::<i32>::collection_retain(&mut vec, |&x| x % 2 == 0);
    /// assert_eq!(vec, [2, 4, 6]);
    ///
    /// // But you do not need to specify the type E when using VecCollectionMut
    /// // as trait bound
    /// fn retain<T: VecCollectionMut, F>(vec: &mut T, fun: F)
    /// where
    ///     F: FnMut(&T::Value) -> bool,
    /// {
    ///     vec.collection_retain(fun);
    /// }
    ///
    /// let mut vec = vec![1, 2, 3, 4, 5, 6];
    /// retain(&mut vec, |&x| x % 2 != 0);
    /// assert_eq!(vec, [1, 3, 5]);
    /// ```
    fn collection_retain<F>(&mut self, f: F)
    where
        F: FnMut(&Self::Value) -> bool;

    /// Returns an iterator that allows modifying each value.
    ///
    /// The iterator yields all items from start to end.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::VecCollectionMut;
    /// use core::ops::MulAssign;
    ///
    /// let mut vec = vec![1, 2, 3, 4, 5, 6];
    /// // Unfortunately, when calling the `VecCollectionMut` methods directly,
    /// // you need to specify the type `E` because the compiler can't infer it.
    /// VecCollectionMut::<i32>::collection_values_mut(&mut vec).for_each(|x| *x *= 2);
    /// assert_eq!(vec, [2, 4, 6, 8, 10, 12]);
    ///
    /// // But you do not need to specify the type E when using VecCollectionMut
    /// // as trait bound
    /// fn square<T: VecCollectionMut>(vec: &mut T) -> &T
    /// where
    ///     T::Value: Clone + MulAssign<T::Value>,
    /// {
    ///     vec.collection_values_mut().for_each(|x| *x *= x.clone());
    ///     vec
    /// }
    ///
    /// assert_eq!(square(&mut vec), &[4, 16, 36, 64, 100, 144]);
    /// ```
    fn collection_values_mut(&mut self) -> Self::ValuesMut<'_>;
}

#[test]
fn test() {
    use crate::VecCollectionMut;
    use core::ops::MulAssign;

    let mut vec = vec![1, 2, 3, 4, 5, 6];
    // Unfortunately, when calling the `VecCollectionMut` methods directly,
    // you need to specify the type `E` because the compiler can't infer it.
    VecCollectionMut::<i32>::collection_values_mut(&mut vec).for_each(|x| *x *= 2);
    assert_eq!(vec, [2, 4, 6, 8, 10, 12]);

    // But you do not need to specify the type E when using VecCollectionMut
    // as trait bound
    fn square<T: VecCollectionMut>(vec: &mut T) -> &T
    where
        T::Value: Clone + MulAssign<T::Value>,
    {
        vec.collection_values_mut().for_each(|x| *x *= x.clone());
        vec
    }

    assert_eq!(square(&mut vec), &[4, 16, 36, 64, 100, 144]);
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
        self.append(other.clone());
        other.clear();
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
