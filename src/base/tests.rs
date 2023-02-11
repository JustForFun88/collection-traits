use super::*;
use crate::TryCollectArray;
use core::fmt::Debug;
use core::ops::AddAssign;

#[cfg(not(miri))]
const N: usize = 50;
#[cfg(miri)]
const N: usize = 10;
const ARRAY_LEN: usize = 3;

fn test_container_mut<T, K, V>(container: &mut T, keys: &[K], values: &[V])
where
    T: BaseCollectionMut<K, Key = K, Value = V> + Debug + ?Sized,
    K: Hash + Eq + Clone + Debug + Ord,
    V: PartialEq + Clone + Debug + Ord + for<'a> AddAssign<&'a V>,
{
    use core::any::type_name;

    let mut container_keys = container.collection_keys().cloned().collect::<Vec<_>>();
    container_keys.sort_unstable();
    assert_eq!(
        container_keys,
        keys,
        "\nContainer type: {}",
        type_name::<T>()
    );

    let mut container_values = container.collection_values().cloned().collect::<Vec<_>>();
    container_values.sort_unstable();
    assert_eq!(
        container_values,
        values,
        "\nContainer type: {}",
        type_name::<T>()
    );

    container_values.clear();
    container_values.extend(container.collection_values_mut().map(|x| x.clone()));
    container_values.sort_unstable();
    assert_eq!(
        container_values,
        values,
        "\nContainer type: {}",
        type_name::<T>()
    );

    container
        .collection_values_mut()
        .for_each(|value| *value += &value.clone());

    container_keys.clear();
    container_keys.extend(container.collection_keys().cloned());
    container_keys.sort_unstable();

    for (key, value) in container_keys.iter().zip(values) {
        let mut value_clone = value.clone();
        value_clone += value;
        assert_eq!(
            container.get_value(key),
            Some(&value_clone),
            "\nKey: {key:?}\nContainer type: {}\nContainer: {container:?}\nValues: {values:?}\n",
            type_name::<T>()
        );
    }

    container_keys.clear();
    container_keys.extend(container.collection_keys().cloned());
    container_keys.sort_unstable();

    for (key, value) in container_keys.iter().zip(values) {
        if let Some(inner) = container.get_value_mut(key) {
            *inner += value;
        }
    }

    container_keys.clear();
    container_keys.extend(container.collection_keys().cloned());
    container_keys.sort_unstable();

    for (key, value) in container_keys.iter().zip(values) {
        let mut value_clone = value.clone();
        value_clone += value;
        value_clone += value;
        assert_eq!(
            container.get_value(key),
            Some(&value_clone),
            "\nKey: {key:?}\nContainer type: {}\nContainer: {container:?}\nValues: {values:?}\n",
            type_name::<T>()
        );
    }
}

fn as_mut_slices_array<T, U, const N: usize>(array: &mut [T; N]) -> [&mut [U]; N]
where
    T: AsMut<[U]>,
{
    use core::mem::MaybeUninit;
    // SAFETY: The `assume_init` is safe because the type we are claiming to have
    // initialized here is a bunch of `MaybeUninit`s, which do not require initialization.
    let mut outputs: [MaybeUninit<&mut [U]>; N] = unsafe { MaybeUninit::uninit().assume_init() };

    for (elem, value) in outputs.iter_mut().zip(array) {
        elem.write(value.as_mut());
    }

    // SAFETY:
    // 1. All elements of the array were populated in the loop above (since both arrays are
    //    the same length);
    // 2. All &mut [U] are guaranteed not to overlap since they are slices from different T's,
    //    so we can return an array of mutable references.
    // 3. `MaybeUninit<T>` is `#[repr(transparent)]` so it is guaranteed to have the same size,
    //    alignment, and ABI as T
    //    (https://doc.rust-lang.org/stable/std/mem/union.MaybeUninit.html#layout-1)
    unsafe { core::mem::transmute_copy(&outputs) }
}

#[test]
fn test_base_container_mut_for_all_vec_types() {
    let iter_arr = (0..ARRAY_LEN).map(|i| (i * N)..((i + 1) * N));

    let mut container: Vec<usize> = (0..N).collect();
    let mut containers_arr: [Vec<usize>; ARRAY_LEN] =
        iter_arr.clone().try_collect_collections_array().unwrap();
    let keys = (0..N).collect::<Vec<_>>();
    let values = (0..N).collect::<Vec<_>>();

    let keys_ext = (0..(N * ARRAY_LEN)).collect::<Vec<_>>();
    let values_ext = keys_ext.clone();

    // Slice
    test_container_mut(container.clone().as_mut_slice(), &keys, &values);
    // Array of Slices
    test_container_mut(
        &mut as_mut_slices_array(&mut containers_arr.clone()),
        &keys_ext,
        &values_ext,
    );

    // collections::Vec
    test_container_mut(&mut container, &keys, &values);
    // Array of collections::Vec
    test_container_mut(&mut containers_arr, &keys_ext, &values_ext);

    // im::Vector
    let mut container: im::Vector<usize> = (0..N).collect();
    let mut containers_arr: [im::Vector<usize>; ARRAY_LEN] =
        iter_arr.clone().try_collect_collections_array().unwrap();
    test_container_mut(&mut container, &keys, &values);
    // Array of im::Vector
    test_container_mut(&mut containers_arr, &keys_ext, &values_ext);

    // collections::VecDeque
    let mut container: collections::VecDeque<usize> = (0..N).collect();
    let mut containers_arr: [collections::VecDeque<usize>; ARRAY_LEN] =
        iter_arr.clone().try_collect_collections_array().unwrap();
    test_container_mut(&mut container, &keys, &values);
    // Array of collections::VecDeque
    test_container_mut(&mut containers_arr, &keys_ext, &values_ext);

    // collections::LinkedList
    let mut container: collections::LinkedList<usize> = (0..N).collect();
    let mut containers_arr: [collections::LinkedList<usize>; ARRAY_LEN] =
        iter_arr.clone().try_collect_collections_array().unwrap();
    test_container_mut(&mut container, &keys, &values);
    // Array of collections::LinkedList
    test_container_mut(&mut containers_arr, &keys_ext, &values_ext);

    // smallVec::SmallVec
    let mut container: SmallVec<[usize; 5]> = (0..N).collect();
    let mut containers_arr: [SmallVec<[usize; 5]>; ARRAY_LEN] =
        iter_arr.clone().try_collect_collections_array().unwrap();
    test_container_mut(&mut container, &keys, &values);
    // Array of smallVec::SmallVec
    test_container_mut(&mut containers_arr, &keys_ext, &values_ext);
}

#[test]
fn test_base_container_mut_for_all_map_types() {
    let iter_arr = (0..ARRAY_LEN).map(|i| ((i * N)..((i + 1) * N)).map(|x| (x, (x + 1000))));

    let keys = (0..N).collect::<Vec<_>>();
    let values = (1000..(N + 1000)).collect::<Vec<_>>();

    let keys_ext = (0..(N * ARRAY_LEN)).collect::<Vec<_>>();
    let values_ext = (1000..((N * ARRAY_LEN) + 1000)).collect::<Vec<_>>();

    // collections::HashMap
    let mut container: collections::HashMap<_, _> = (0..N).map(|x| (x, (x + 1000))).collect();
    let mut containers_arr: [collections::HashMap<_, _>; ARRAY_LEN] =
        iter_arr.clone().try_collect_collections_array().unwrap();
    test_container_mut(&mut container, &keys, &values);
    // Array of collections::HashMap
    test_container_mut(&mut containers_arr, &keys_ext, &values_ext);

    // hashbrown::HashMap
    let mut container: hashbrown::HashMap<_, _> = (0..N).map(|x| (x, (x + 1000))).collect();
    let mut containers_arr: [hashbrown::HashMap<_, _>; ARRAY_LEN] =
        iter_arr.clone().try_collect_collections_array().unwrap();
    test_container_mut(&mut container, &keys, &values);
    // Array of hashbrown::HashMap
    test_container_mut(&mut containers_arr, &keys_ext, &values_ext);

    // im::HashMap
    let mut container: im::HashMap<_, _> = (0..N).map(|x| (x, (x + 1000))).collect();
    let mut containers_arr: [im::HashMap<_, _>; ARRAY_LEN] =
        iter_arr.clone().try_collect_collections_array().unwrap();
    test_container_mut(&mut container, &keys, &values);
    // Array of im::HashMap
    test_container_mut(&mut containers_arr, &keys_ext, &values_ext);

    // indexmap::IndexMap
    let mut container: indexmap::IndexMap<_, _> = (0..N).map(|x| (x, (x + 1000))).collect();
    let mut containers_arr: [indexmap::IndexMap<_, _>; ARRAY_LEN] =
        iter_arr.clone().try_collect_collections_array().unwrap();
    test_container_mut(&mut container, &keys, &values);
    // Array of indexmap::IndexMap
    test_container_mut(&mut containers_arr, &keys_ext, &values_ext);

    // collections::BTreeMap
    let mut container: collections::BTreeMap<_, _> = (0..N).map(|x| (x, (x + 1000))).collect();
    let mut containers_arr: [collections::BTreeMap<_, _>; ARRAY_LEN] =
        iter_arr.clone().try_collect_collections_array().unwrap();
    test_container_mut(&mut container, &keys, &values);
    // Array of collections::BTreeMap
    test_container_mut(&mut containers_arr, &keys_ext, &values_ext);

    // im::OrdMap
    let mut container: im::OrdMap<_, _> = (0..N).map(|x| (x, (x + 1000))).collect();
    let mut containers_arr: [im::OrdMap<_, _>; ARRAY_LEN] =
        iter_arr.clone().try_collect_collections_array().unwrap();
    test_container_mut(&mut container, &keys, &values);
    // Array of im::OrdMap
    test_container_mut(&mut containers_arr, &keys_ext, &values_ext);
}
