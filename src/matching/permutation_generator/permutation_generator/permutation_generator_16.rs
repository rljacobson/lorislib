use super::*;

#[derive(Clone, Copy, Debug)]
pub struct PermutationGenerator16 {
    nb_elems: u8,
    nb_perms: u64,
    next_idx: u64,
}

impl PermutationGenerator16 {
    const MAX_ELEMENTS: u8 = 16;

    pub fn new(nb_elems: u8) -> PResult<Self> {
        Self::check_nb_elems(nb_elems).map(|_| Self {
            next_idx: 0,
            nb_perms: factorial64(nb_elems),
            nb_elems,
        })
    }

    pub fn next_permutation(&mut self) -> Option<impl Iterator<Item = u8>> {
        self.nth(0)
    }

    pub fn nth_absolute(nb_elems: u8, idx: u64) -> PResult<Option<impl Iterator<Item = u8>>> {
        Self::check_nb_elems(nb_elems)
            .map(|_| SinglePermutation16::new(nb_elems, factorial64(nb_elems), idx))
    }

    pub fn nth(&mut self, step: u64) -> Option<impl Iterator<Item = u8>> {
        let step_result = self.next_idx.saturating_add(step);
        let res = SinglePermutation16::new(self.nb_elems, self.nb_perms, step_result);
        self.next_idx = step_result + 1;
        res
    }

    pub fn nb_remaining(&self) -> usize {
        (self.nb_perms - self.next_idx) as usize
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

impl Iterator for PermutationGenerator16 {
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

    const NB_ELEMS: u8 = 9;

    fn test_slice(ref_slice: &[u8], some_iter: Option<impl Iterator<Item = u8>>) {
        assert_eq!(ref_slice, some_iter.unwrap().collect::<Vec<_>>().as_slice());
    }

    #[test]
    fn zero() {
        let mut pg = PermutationGenerator16::new(0).unwrap();
        assert!(pg.next_permutation().is_none());
    }

    #[test]
    fn next_permutation() {
        let mut pg = PermutationGenerator16::new(NB_ELEMS).unwrap();
        test_slice(&[0, 1, 2, 3, 4, 5, 6, 7, 8], pg.next_permutation());
        test_slice(&[0, 1, 2, 3, 4, 5, 6, 8, 7], pg.next_permutation());
    }

    #[test]
    fn nth_absolute() {
        test_slice(
            &[0, 1, 2, 3, 4, 5, 6, 7, 8],
            PermutationGenerator16::nth_absolute(NB_ELEMS, 0).unwrap(),
        );
        test_slice(
            &[8, 7, 6, 5, 4, 3, 2, 1, 0],
            PermutationGenerator16::nth_absolute(NB_ELEMS, factorial64(NB_ELEMS) - 1).unwrap(),
        );
        test_slice(
            &[1, 0, 2, 3, 4, 5, 6, 7, 8],
            PermutationGenerator16::nth_absolute(NB_ELEMS, factorial64(NB_ELEMS - 1)).unwrap(),
        );
    }

    #[test]
    fn nth() {
        let mut pg = PermutationGenerator16::new(NB_ELEMS).unwrap();
        test_slice(
            &[8, 7, 6, 5, 4, 3, 2, 1, 0],
            pg.nth(factorial64(NB_ELEMS) - 1),
        );
        assert!(pg.next_permutation().is_none());

        let mut pg = PermutationGenerator16::new(NB_ELEMS).unwrap();
        test_slice(&[0, 1, 2, 3, 4, 5, 6, 7, 8], pg.nth(0));
        test_slice(
            &[1, 0, 2, 3, 4, 5, 6, 7, 8],
            pg.nth(factorial64(NB_ELEMS - 1) - 1),
        );
    }

    #[test]
    fn iter() {
        let iter = PermutationGenerator16::new(NB_ELEMS).unwrap();
        assert_eq!(factorial64(NB_ELEMS) as usize, iter.count());
    }
}
