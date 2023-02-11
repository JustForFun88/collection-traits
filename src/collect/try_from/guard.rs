use core::mem::MaybeUninit;
use core::ptr;

/// Panic guard for incremental initialization of arrays.
///
/// Disarm the guard with `mem::forget` once the array has been initialized.
///
/// # Safety
///
/// All write accesses to this structure are unsafe and must maintain a correct
/// count of `initialized` elements.
///
/// To minimize indirection fields are still pub but callers should at least use
/// `push_unchecked` to signal that something unsafe is going on.
pub(super) struct Guard<'a, T, const N: usize> {
    /// The array to be initialized.
    pub(super) array_mut: &'a mut [MaybeUninit<T>; N],
    /// The number of items that have been initialized so far.
    pub(super) initialized: usize,
}

impl<T, const N: usize> Guard<'_, T, N> {
    /// Adds an item to the array and updates the initialized item counter.
    ///
    /// # Safety
    ///
    /// No more than N elements must be initialized.
    #[inline(always)]
    pub(super) unsafe fn push_unchecked(&mut self, item: T) {
        // SAFETY: If `initialized` was correct before and the caller does not
        // invoke this method more than N times then writes will be in-bounds
        // and slots will not be initialized more than once.
        unsafe {
            self.array_mut
                .get_unchecked_mut(self.initialized)
                .write(item);
            self.initialized += 1;
        }
    }
}

impl<T, const N: usize> Drop for Guard<'_, T, N> {
    fn drop(&mut self) {
        debug_assert!(self.initialized <= N);

        // SAFETY:
        // 1. The `slice` will contain only initialized objects;
        // 2. `MaybeUninit<T>` is `#[repr(transparent)]` so it is guaranteed
        //    to have the same size, alignment, and ABI as T
        //    (https://doc.rust-lang.org/stable/std/mem/union.MaybeUninit.html#layout-1)
        unsafe {
            let slice: *mut [MaybeUninit<T>] = self.array_mut.get_unchecked_mut(..self.initialized);
            ptr::drop_in_place(slice as *mut [T]);
        }
    }
}
