use alloc::vec::IntoIter;

pub struct ImOrdMapValueMut<'a, K: 'a, V: 'a> {
    // iterator of the first set
    keys: IntoIter<K>,
    // the second set
    map: &'a mut im::OrdMap<K, V>,
}

impl<K: Ord + Clone, V> ImOrdMapValueMut<'_, K, V> {
    #[inline]
    pub(crate) fn new(map: &mut im::OrdMap<K, V>) -> ImOrdMapValueMut<'_, K, V> {
        let keys = map.keys().cloned().collect::<Vec<_>>().into_iter();
        ImOrdMapValueMut { keys, map }
    }
}

impl<'a, K: Ord + Clone, V: Clone> Iterator for ImOrdMapValueMut<'a, K, V> {
    type Item = &'a mut V;

    #[inline]
    fn next(&mut self) -> Option<&'a mut V> {
        let key = self.keys.next()?;
        if let Some(value) = self.map.get_mut(&key) {
            // FIXME: At the moment, the "borrow checker" is a little dumb and does not
            // understand that the reference will be alive while the map itself, and also
            // that we are not changing the map, but its value, i.e. the reference will be
            // valid for the entire time of the mutable borrowing of the map. Perhaps this
            // will change with the transition to polonius (https://github.com/rust-lang/polonius)
            // or another checker. Thus, for now, the only way out is to cast a mutable reference
            // to a raw pointer and vice versa.
            let value = unsafe { &mut *(value as *mut V) };
            return Some(value);
        }
        None
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.map.len(), Some(self.map.len()))
    }
}

impl<K, V> core::iter::FusedIterator for ImOrdMapValueMut<'_, K, V>
where
    K: Ord + Clone,
    V: Clone,
{
}

impl<K, V> core::iter::ExactSizeIterator for ImOrdMapValueMut<'_, K, V>
where
    K: Ord + Clone,
    V: Clone,
{
}
