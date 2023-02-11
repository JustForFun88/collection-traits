use smallvec::SmallVec;
use std::collections;

/// Auxiliary base trait for all traits that allow abstraction
/// from different types of containers / collections. Has one
/// associated type, which can be thought of as a type of keys
/// inside of the given container/collection.
pub trait KeyContain {
    /// The type of the keys stored in the container/collection.
    ///
    /// Values of this type must indeed be inside the container
    /// and it should be a type that can be thought of as a key
    /// type for the values stored in the container.
    ///
    /// For example for `[T]` - `<[T] as KeyContain>::Key = T` and
    /// for `HashMap<K, V, S>` - `HashMap::<K, V, S>::Key = K`
    type Key;
}

/// Auxiliary base trait for all traits that allow abstraction
/// from different types of containers / collections. Has one
/// associated type, which represent the type of values
/// inside of the given container/collection.
pub trait ValueContain {
    /// The type of the values stored in the container/collection.
    ///
    /// Values of this type must indeed be inside the container.
    ///
    /// For example for `[T]` - `<[T] as ValueContain>::Value = T` and
    /// for `HashMap<K, V, S>` - `HashMap::<K, V, S>::Value = V`
    type Value;
}

impl<T: ?Sized + KeyContain> KeyContain for &T {
    type Key = T::Key;
}

impl<T: ?Sized + KeyContain> KeyContain for &mut T {
    type Key = T::Key;
}

impl<T: ?Sized + ValueContain> ValueContain for &T {
    type Value = T::Value;
}

impl<T: ?Sized + ValueContain> ValueContain for &mut T {
    type Value = T::Value;
}

macro_rules! impl_key_value_for_vec_types {
    ($($type_n:ty)*) => ($(
        impl<T> KeyContain for $type_n {
            type Key = T;
        }

        impl<T> ValueContain for $type_n {
            type Value = T;
        }
    )*)
}

impl_key_value_for_vec_types! {
    [T]
    Vec<T>
    im::Vector<T>
    collections::VecDeque<T>
    collections::LinkedList<T>
    collections::BinaryHeap<T>
    collections::BTreeSet<T>
    im::OrdSet<T>
}

impl<T, A: smallvec::Array<Item = T>> KeyContain for SmallVec<A> {
    type Key = T;
}

impl<T, A: smallvec::Array<Item = T>> ValueContain for SmallVec<A> {
    type Value = T;
}

macro_rules! impl_key_value_for_set_types {
    ($($type_n:ty)*) => ($(
        impl<T, S> KeyContain for $type_n {
            type Key = T;
        }

        impl<T, S> ValueContain for $type_n {
            type Value = T;
        }
    )*)
}

impl_key_value_for_set_types! {
    collections::HashSet<T, S>
    hashbrown::HashSet<T, S>
    indexmap::IndexSet<T, S>
    im::HashSet<T, S>
}

macro_rules! impl_key_value_for_hash_map_types {
    ($($type_n:ty)*) => ($(
        impl<K, V, S> KeyContain for $type_n {
            type Key = K;
        }

        impl<K, V, S> ValueContain for $type_n {
            type Value = V;
        }
    )*)
}

impl_key_value_for_hash_map_types! {
    collections::HashMap<K, V, S>
    hashbrown::HashMap<K, V, S>
    im::HashMap<K, V, S>
    indexmap::IndexMap<K, V, S>
}

macro_rules! impl_key_value_for_ord_map_types {
    ($($type_n:ty)*) => ($(
        impl<K, V> KeyContain for $type_n {
            type Key = K;
        }

        impl<K, V> ValueContain for $type_n {
            type Value = V;
        }
    )*)
}

impl_key_value_for_ord_map_types! {
    collections::BTreeMap<K, V>
    im::OrdMap<K, V>
}

impl<T: KeyContain, const N: usize> KeyContain for [T; N] {
    type Key = T::Key;
}

impl<T: ValueContain, const N: usize> ValueContain for [T; N] {
    type Value = T::Value;
}
