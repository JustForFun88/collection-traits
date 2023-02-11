use core::fmt;
use core::iter::{self, FusedIterator};
use core::mem::{self, MaybeUninit};
use core::ops::Range;
use core::ptr;

/// A by-value [array] iterator.
///
/// # FIXME
///
/// This structure is similar to [`core::array::IntoIter`] and is duplicated here because
/// the [`IntoIter::new_unchecked`] method is not yet stable. Remove this structure in favor
/// of [`core::array::IntoIter`] after [`IntoIter::new_unchecked`] is stabilized.
///
/// [`core::array::IntoIter`]: https://doc.rust-lang.org/stable/core/array/struct.IntoIter.html#
/// [`IntoIter::new_unchecked`]: https://doc.rust-lang.org/stable/std/array/struct.IntoIter.html#method.new_unchecked
pub struct IntoIter<T, const N: usize> {
    /// This is the array we are iterating over.
    ///
    /// Elements with index `i` where `alive.start <= i < alive.end` have not
    /// been yielded yet and are valid array entries. Elements with indices `i
    /// < alive.start` or `i >= alive.end` have been yielded already and must
    /// not be accessed anymore! Those dead elements might even be in a
    /// completely uninitialized state!
    ///
    /// So the invariants are:
    /// - `data[alive]` is alive (i.e. contains valid elements)
    /// - `data[..alive.start]` and `data[alive.end..]` are dead (i.e. the
    ///   elements were already read and must not be touched anymore!)
    data: [MaybeUninit<T>; N],

    /// The elements in `data` that have not been yielded yet.
    ///
    /// Invariants:
    /// - `alive.end <= N`
    ///
    /// (And the `IndexRange` type requires `alive.start <= alive.end`.)
    alive: Range<usize>,
}

impl<T, const N: usize> IntoIter<T, N> {
    /// Creates a new iterator over the given `array`.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::IntoIter;
    /// use std::ops::AddAssign;
    ///
    /// fn create_arr<T, const N: usize>(start: T, step: T) -> [T; N]
    /// where
    ///     T: AddAssign<T> + Copy,
    /// {
    ///     let mut outs: [T; N] = [start; N];
    ///     let mut element = step;
    ///     outs.iter_mut().skip(1).for_each(|v| {
    ///         *v += element;
    ///         element += step;
    ///     });
    ///     outs
    /// }
    ///
    /// let array: [i32; 100] = create_arr(0, 1);
    /// let iter = IntoIter::new(array);
    /// assert_eq!(iter.collect::<Vec<_>>(), (0..100).collect::<Vec<_>>());
    /// ```
    #[inline]
    pub fn new(array: [T; N]) -> Self {
        // SAFETY: The transmute here is actually safe. The docs of `MaybeUninit`
        // promise:
        //
        // > `MaybeUninit<T>` is guaranteed to have the same size and alignment
        // > as `T`.
        //
        // The docs even show a transmute from an array of `MaybeUninit<T>` to
        // an array of `T`.
        //
        // With that, this initialization satisfies the invariants.

        // FIXME(LukasKalbertodt): actually use `mem::transmute` here, once it
        // works with const generics:
        //     `mem::transmute::<[T; N], [MaybeUninit<T>; N]>(array)`
        //
        // Until then, we can use `mem::transmute_copy` to create a bitwise copy
        // as a different type, then forget `array` so that it is not dropped.
        unsafe {
            let iter = IntoIter {
                data: mem::transmute_copy(&array),
                alive: 0..N,
            };
            mem::forget(array);
            iter
        }
    }

    /// Creates an iterator over the elements in a partially-initialized buffer.
    ///
    /// If you have a fully-initialized array, then use [`IntoIterator`].
    /// But this is useful for returning partial results from unsafe code.
    ///
    /// # Safety
    ///
    /// - The `buffer[initialized]` elements must all be initialized.
    /// - The range must be canonical, with `initialized.start <= initialized.end`.
    /// - The range must be in-bounds for the buffer, with `initialized.end <= N`.
    ///   (Like how indexing `[0][100..100]` fails despite the range being empty.)
    ///
    /// It's sound to have more elements initialized than mentioned, though that
    /// will most likely result in them being leaked.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::IntoIter;
    /// use std::mem::{self, MaybeUninit};
    ///
    /// fn next_chunk<T: Copy, const N: usize>(
    ///     it: &mut impl Iterator<Item = T>,
    /// ) -> Result<[T; N], IntoIter<T, N>> {
    ///
    ///     // SAFETY: The `assume_init` is safe because the type we are claiming to have
    ///     // initialized here is a bunch of `MaybeUninit`s, which do not require initialization.
    ///     let mut buffer: [MaybeUninit<T>; N] = unsafe { MaybeUninit::uninit().assume_init() };
    ///     let mut i = 0;
    ///     while i < N {
    ///         match it.next() {
    ///             Some(x) => {
    ///                 buffer[i].write(x);
    ///                 i += 1;
    ///             }
    ///             None => {
    ///                 // SAFETY: We've initialized the first `i` items
    ///                 unsafe {
    ///                     return Err(IntoIter::new_unchecked(buffer, 0..i));
    ///                 }
    ///             }
    ///         }
    ///     }
    ///
    ///     // SAFETY: We've initialized all N items
    ///     Ok(unsafe { mem::transmute_copy(&buffer) })
    /// }
    ///
    /// let r: [_; 4] = next_chunk(&mut (10..16)).unwrap();
    /// assert_eq!(r, [10, 11, 12, 13]);
    /// let r: IntoIter<_, 40> = next_chunk(&mut (10..16)).unwrap_err();
    /// assert_eq!(r.collect::<Vec<_>>(), vec![10, 11, 12, 13, 14, 15]);
    /// ```
    #[inline]
    pub const unsafe fn new_unchecked(
        buffer: [MaybeUninit<T>; N],
        initialized: Range<usize>,
    ) -> Self {
        // SAFETY: one of our safety conditions is that the range is canonical.
        Self {
            data: buffer,
            alive: initialized,
        }
    }

    /// Returns an immutable slice of all elements that have not been yielded yet.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::IntoIter;
    /// use std::ops::AddAssign;
    ///
    /// let array = [1, 2, 3, 4, 5];
    /// let iter = IntoIter::new(array);
    /// assert_eq!(iter.as_slice(), &[1, 2, 3, 4, 5]);
    /// ```
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        unsafe {
            // SAFETY: We know that all elements within `alive` are properly initialized.
            let slice = self.data.get_unchecked(self.alive.clone());
            // SAFETY: casting `slice` to a `*const [T]` is safe since the `slice` is initialized,
            // and `MaybeUninit` is guaranteed to have the same layout as `T`.
            // The pointer obtained is valid since it refers to memory owned by `slice` which is a
            // reference and thus guaranteed to be valid for reads.
            &*(slice as *const [MaybeUninit<T>] as *const [T])
        }
    }

    /// Returns a mutable slice of all elements that have not been yielded yet.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::IntoIter;
    /// use std::ops::AddAssign;
    ///
    /// let array = [1, 2, 3, 4, 5];
    /// let mut iter = IntoIter::new(array);
    /// assert_eq!(iter.as_mut_slice(), &mut [1, 2, 3, 4, 5]);
    /// ```
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        unsafe {
            // SAFETY: We know that all elements within `alive` are properly initialized.
            let slice = self.data.get_unchecked_mut(self.alive.clone());
            // SAFETY: casting `slice` to a `*mut [T]` is safe since the `slice` is initialized,
            // and `MaybeUninit` is guaranteed to have the same layout as `T`.
            // The pointer obtained is valid since it refers to memory owned by `slice` which is a
            // reference and thus guaranteed to be valid for reads and writes.
            &mut *(slice as *mut [MaybeUninit<T>] as *mut [T])
        }
    }
}

impl<T, const N: usize> Iterator for IntoIter<T, N> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        // Get the next index from the front.
        //
        // Increasing `alive.start` by 1 maintains the invariant regarding
        // `alive`. However, due to this change, for a short time, the alive
        // zone is not `data[alive]` anymore, but `data[idx..alive.end]`.
        self.alive.next().map(|idx| {
            // Read the element from the array.
            // SAFETY: `idx` is an index into the former "alive" region of the
            // array. Reading this element means that `data[idx]` is regarded as
            // dead now (i.e. do not touch). As `idx` was the start of the
            // alive-zone, the alive zone is now `data[alive]` again, restoring
            // all invariants.
            unsafe { self.data.get_unchecked(idx).assume_init_read() }
        })
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }

    #[inline]
    fn fold<Acc, Fold>(mut self, init: Acc, mut fold: Fold) -> Acc
    where
        Fold: FnMut(Acc, Self::Item) -> Acc,
    {
        let data = &mut self.data;
        self.alive.by_ref().fold(init, |acc, idx| {
            // SAFETY: idx is obtained by folding over the `alive` range, which implies the
            // value is currently considered alive but as the range is being consumed each value
            // we read here will only be read once and then considered dead.
            fold(acc, unsafe { data.get_unchecked(idx).assume_init_read() })
        })
    }

    #[inline]
    fn count(self) -> usize {
        self.len()
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }
}

impl<T, const N: usize> DoubleEndedIterator for IntoIter<T, N> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        // Get the next index from the back.
        //
        // Decreasing `alive.end` by 1 maintains the invariant regarding
        // `alive`. However, due to this change, for a short time, the alive
        // zone is not `data[alive]` anymore, but `data[alive.start..=idx]`.
        self.alive.next_back().map(|idx| {
            // Read the element from the array.
            // SAFETY: `idx` is an index into the former "alive" region of the
            // array. Reading this element means that `data[idx]` is regarded as
            // dead now (i.e. do not touch). As `idx` was the end of the
            // alive-zone, the alive zone is now `data[alive]` again, restoring
            // all invariants.
            unsafe { self.data.get_unchecked(idx).assume_init_read() }
        })
    }

    #[inline]
    fn rfold<Acc, Fold>(mut self, init: Acc, mut rfold: Fold) -> Acc
    where
        Fold: FnMut(Acc, Self::Item) -> Acc,
    {
        let data = &mut self.data;
        self.alive.by_ref().rfold(init, |acc, idx| {
            // SAFETY: idx is obtained by folding over the `alive` range, which implies the
            // value is currently considered alive but as the range is being consumed each value
            // we read here will only be read once and then considered dead.
            rfold(acc, unsafe { data.get_unchecked(idx).assume_init_read() })
        })
    }
}

impl<T, const N: usize> Drop for IntoIter<T, N> {
    fn drop(&mut self) {
        // SAFETY: This is safe: `as_mut_slice` returns exactly the sub-slice
        // of elements that have not been moved out yet and that remain
        // to be dropped.
        unsafe { ptr::drop_in_place(self.as_mut_slice()) }
    }
}

impl<T, const N: usize> ExactSizeIterator for IntoIter<T, N> {
    #[inline]
    fn len(&self) -> usize {
        self.alive.len()
    }
}

impl<T, const N: usize> FusedIterator for IntoIter<T, N> {}

impl<T: Clone, const N: usize> Clone for IntoIter<T, N> {
    #[inline]
    fn clone(&self) -> Self {
        // Note, we don't really need to match the exact same alive range, so
        // we can just clone into offset 0 regardless of where `self` is.
        //
        // SAFETY: The `assume_init` is safe because the type we are claiming to have
        // initialized here is a bunch of `MaybeUninit`s, which do not require initialization.
        let mut new = Self {
            data: unsafe { MaybeUninit::uninit().assume_init() },
            alive: 0..0,
        };

        // Clone all alive elements.
        for (src, dst) in iter::zip(self.as_slice(), &mut new.data) {
            // Write a clone into the new array, then update its alive range.
            // If cloning panics, we'll correctly drop the previous items.
            dst.write(src.clone());
            // This addition cannot overflow as we're iterating a slice
            new.alive = 0..(new.alive.end + 1);
        }

        new
    }
}

impl<T: fmt::Debug, const N: usize> fmt::Debug for IntoIter<T, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Only print the elements that were not yielded yet: we cannot
        // access the yielded elements anymore.
        f.debug_tuple("IntoIter").field(&self.as_slice()).finish()
    }
}

#[cfg(test)]
mod test {
    use crate::IntoIter;
    #[cfg(not(miri))]
    const N: usize = 64; // must be divisible by 4
    #[cfg(miri)]
    const N: usize = 16; // must be divisible by 4

    #[test]
    #[allow(clippy::unnecessary_fold)]
    fn test() {
        use std::ops::AddAssign;

        fn create_arr<T, const N: usize>(start: T, step: T) -> [T; N]
        where
            T: AddAssign<T> + Copy,
        {
            let mut outs: [T; N] = [start; N];
            let mut element = step;
            outs.iter_mut().skip(1).for_each(|v| {
                *v += element;
                element += step;
            });
            outs
        }

        let mut vec = (0..N).collect::<Vec<_>>();

        let iter = IntoIter::new(create_arr::<usize, N>(0, 1));
        assert_eq!(iter.len(), N);
        assert_eq!(iter.size_hint(), (N, Some(N)));
        assert_eq!(&iter.collect::<Vec<_>>(), &vec);

        let mut iter = IntoIter::new(create_arr::<usize, N>(0, 1));
        assert_eq!(iter.as_slice(), &vec);
        assert_eq!(iter.as_mut_slice(), &mut vec);

        vec.reverse();
        assert_eq!(&iter.rev().collect::<Vec<_>>(), &vec);
        vec.reverse();

        let mut iter = IntoIter::new(create_arr::<usize, N>(0, 1));

        for (num, item) in iter.by_ref().take(N / 4).zip(0..(N / 4)) {
            assert_eq!(item, num);
        }
        assert_eq!(iter.len(), 3 * (N / 4));
        assert_eq!(iter.size_hint(), (3 * (N / 4), Some(3 * (N / 4))));

        for (num, item) in iter
            .by_ref()
            .rev()
            .take(N / 4)
            .zip(((3 * (N / 4))..N).rev())
        {
            assert_eq!(item, num);
        }

        let mut other_iter = iter.clone();

        assert_eq!(iter.len(), N / 2);
        assert_eq!(iter.size_hint(), (N / 2, Some(N / 2)));
        assert_eq!(iter.as_slice(), &vec[(N / 4)..(3 * (N / 4))]);
        assert_eq!(iter.as_mut_slice(), &mut vec[(N / 4)..(3 * (N / 4))]);
        assert_eq!(iter.count(), N / 2);

        assert_eq!(other_iter.len(), N / 2);
        assert_eq!(other_iter.size_hint(), (N / 2, Some(N / 2)));
        assert_eq!(other_iter.as_slice(), &vec[(N / 4)..(3 * (N / 4))]);
        assert_eq!(other_iter.as_mut_slice(), &mut vec[(N / 4)..(3 * (N / 4))]);
        assert_eq!(other_iter.count(), N / 2);

        let iter = IntoIter::new(create_arr::<usize, N>(0, 1));
        assert_eq!(iter.last(), Some(N - 1));

        let iter = IntoIter::new(create_arr::<usize, N>(0, 1));
        let result = iter.fold(0, |acc, x| acc + x);
        assert_eq!(result, (0..N).sum());

        let iter = IntoIter::new(create_arr::<usize, N>(0, 1));
        let result = iter.rfold(0, |acc, x| acc + x);
        assert_eq!(result, (0..N).sum());

        let mut iter = IntoIter::new([1, 2, 3, 4, 5]);
        iter.next();
        iter.next_back();
        assert_eq!(format!("{iter:?}"), "IntoIter([2, 3, 4])");

        let mut iter = IntoIter::new([1, 2, 3, 4, 5].map(|x| x.to_string()));
        iter.next();
        iter.next_back();
        assert_eq!(format!("{iter:?}"), "IntoIter([\"2\", \"3\", \"4\"])");
    }

    #[test]
    #[should_panic = "panic in clone"]
    fn test_panic_clone() {
        struct CheckedCloneDrop {
            text: String,
            panic_in_clone: bool,
            dropped: bool,
        }
        impl Clone for CheckedCloneDrop {
            fn clone(&self) -> Self {
                if self.panic_in_clone {
                    panic!("panic in clone");
                } else {
                    Self {
                        text: self.text.clone(),
                        panic_in_clone: self.panic_in_clone.clone(),
                        dropped: self.dropped.clone(),
                    }
                }
            }
        }
        impl Drop for CheckedCloneDrop {
            fn drop(&mut self) {
                if self.dropped {
                    panic!("double drop");
                }
                self.dropped = true;
            }
        }

        let array = [
            CheckedCloneDrop {
                text: "text".to_owned(),
                panic_in_clone: false,
                dropped: false,
            },
            CheckedCloneDrop {
                text: "text".to_owned(),
                panic_in_clone: false,
                dropped: false,
            },
            CheckedCloneDrop {
                text: "text".to_owned(),
                panic_in_clone: true,
                dropped: false,
            },
        ];
        let iter = IntoIter::new(array);
        let _iter_two = iter.clone();
    }
}
