use super::*;

#[derive(Clone, Copy, Debug)]
pub struct PermutationGenerator32 {
    nb_elems: u8,
    nb_perms: u128,
    next_idx: u128,
}

impl PermutationGenerator32 {
    const MAX_ELEMENTS: u8 = 32;

    pub fn new(nb_elems: u8) -> PResult<Self> {
        Self::check_nb_elems(nb_elems).map(|_| Self {
            next_idx: 0,
            nb_perms: factorial128(nb_elems),
            nb_elems,
        })
    }

    pub fn next_permutation(&mut self) -> Option<impl Iterator<Item = u8>> {
        self.nth(0)
    }

    pub fn nth_absolute(nb_elems: u8, idx: u128) -> PResult<Option<impl Iterator<Item = u8>>> {
        Self::check_nb_elems(nb_elems)
            .map(|_| SinglePermutation32::new(nb_elems, factorial128(nb_elems), idx))
    }

    pub fn nth(&mut self, step: u128) -> Option<impl Iterator<Item = u8>> {
        let step_result = self.next_idx.saturating_add(step);
        let res = SinglePermutation32::new(self.nb_elems, self.nb_perms, step_result);
        self.next_idx = step_result + 1;
        res
    }

    /// Panics on nb_elems > 20
    pub fn nb_remaining(&self) -> usize {
        match (self.nb_perms - self.next_idx).try_into() {
            Ok(nb) => nb,
            Err(_) => panic!("The size of the iterator owerflowed usize"),
        }
    }

    #[inline]
    fn check_nb_elems(nb_elems: u8) -> PResult<()> {
        if nb_elems > Self::MAX_ELEMENTS {
            Err(PermutationGeneratorError::TooManyElements)
        } else {
            Ok(())
        }
    }
}

impl Iterator for PermutationGenerator32 {
    type Item = impl Iterator<Item = u8>;

    fn next(&mut self) -> Option<Self::Item> {
        self.next_permutation()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let nb_remaining = self.nb_remaining();
        (nb_remaining, Some(nb_remaining))
    }

    fn count(self) -> usize {
        self.nb_remaining()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const NB_ELEMS: u8 = 18;

    fn test_slice(ref_slice: &[u8], some_iter: Option<impl Iterator<Item = u8>>) {
        assert_eq!(ref_slice, some_iter.unwrap().collect::<Vec<_>>().as_slice());
    }

    #[test]
    fn zero() {
        let mut pg = PermutationGenerator32::new(0).unwrap();
        assert!(pg.next_permutation().is_none());
    }

    #[test]
    fn next_permutation() {
        let mut pg = PermutationGenerator32::new(NB_ELEMS).unwrap();
        test_slice(
            &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17],
            pg.next_permutation(),
        );
        test_slice(
            &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 16],
            pg.next_permutation(),
        );
    }

    #[test]
    fn nth_absolute() {
        test_slice(
            &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17],
            PermutationGenerator32::nth_absolute(NB_ELEMS, 0).unwrap(),
        );
        test_slice(
            &[17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0],
            PermutationGenerator32::nth_absolute(NB_ELEMS, factorial128(NB_ELEMS) - 1).unwrap(),
        );

        test_slice(
            (0..30).rev().collect::<Vec<_>>().as_slice(),
            PermutationGenerator32::nth_absolute(30, factorial128(30) - 1).unwrap(),
        )
    }

    #[test]
    fn nth() {
        let mut pg = PermutationGenerator32::new(NB_ELEMS).unwrap();
        test_slice(
            &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17],
            pg.next_permutation(),
        );
        test_slice(
            &[17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0],
            pg.nth(factorial128(NB_ELEMS) - 2),
        );
        assert!(pg.next_permutation().is_none());
    }

    #[test]
    fn iter() {
        let iter = PermutationGenerator32::new(NB_ELEMS).unwrap();
        assert_eq!(factorial128(NB_ELEMS) as usize, iter.count());
    }

    #[test]
    #[should_panic]
    fn iter_panic() {
        let iter = PermutationGenerator32::new(30).unwrap();
        assert_eq!(factorial128(30) as usize, iter.count());
    }
}
