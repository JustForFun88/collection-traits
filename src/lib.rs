#![warn(rustdoc::broken_intra_doc_links)]

extern crate alloc;
use core::borrow::Borrow;

mod some_mod;

mod collect;
pub use collect::{ArrayFromIterator, CollectionArrayFromIterator, IntoIter, TryCollectArray};

mod key_value;
pub use key_value::{KeyContain, ValueContain};

mod any;
pub use any::AnyCollectionRef;

mod value_cont;
pub use value_cont::ValueCollectionRef;

mod base;
pub use base::BaseCollectionMut;

mod im_iters;
pub use im_iters::{
    ImHashDifference, ImHashIntersection, ImHashSymmetricDifference, ImOrdDifference,
    ImOrdIntersection, ImOrdMapValueMut, ImOrdSymmetricDifference,
};

mod map;
pub use map::{MapCollection, MapCollectionMut, MapCollectionRef};

mod set;
pub use set::{SetContainer, SetContainerMut, SetContainerRef};

mod vec;
pub use vec::{VecContainer, VecContainerMut, VecContainerRef};

/// Key equivalence trait.
///
/// This trait allows hash table lookup to be customized.
/// It has one blanket implementation that uses the regular `Borrow` solution,
/// just like `HashMap` and `BTreeMap` do, so that you can pass `&str` to lookup
/// into a map with `String` keys and so on.
///
/// # Correctness
///
/// Equivalent values must hash to the same value.
pub trait Equivalent<K: ?Sized>: hashbrown::Equivalent<K> + indexmap::Equivalent<K> {
    /// Checks if this value is equivalent to the given key.
    ///
    /// Returns `true` if both values are equivalent, and `false` otherwise.
    ///
    /// # Correctness
    ///
    /// When this function returns `true`, both `self` and `key` must hash to
    /// the same value.
    fn equivalent(&self, key: &K) -> bool;
}

impl<Q: ?Sized, K: ?Sized> Equivalent<K> for Q
where
    Q: Eq,
    K: Borrow<Q>,
{
    #[inline]
    fn equivalent(&self, key: &K) -> bool {
        *self == *key.borrow()
    }
}
