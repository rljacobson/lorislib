use super::*;

#[derive(Clone, Copy, Debug)]
pub struct PermutationGenerator8 {
    nb_elems: u8,
    nb_perms: u16,
    next_idx: u16,
}

impl PermutationGenerator8 {
    const MAX_ELEMENTS: u8 = 8;

    pub fn new(nb_elems: u8) -> PResult<Self> {
        Self::check_nb_elems(nb_elems).map(|_| Self {
            next_idx: 0,
            nb_perms: factorial16(nb_elems),
            nb_elems,
        })
    }

    pub fn next_permutation(&mut self) -> Option<impl Iterator<Item = u8>> {
        self.nth(0)
    }

    pub fn nth_absolute(nb_elems: u8, idx: u16) -> PResult<Option<impl Iterator<Item = u8>>> {
        Self::check_nb_elems(nb_elems)
            .map(|_| SinglePermutation8::new(nb_elems, factorial16(nb_elems), idx))
    }

    pub fn nth(&mut self, step: u16) -> Option<impl Iterator<Item = u8>> {
        let step_result = self.next_idx.saturating_add(step);
        let res = SinglePermutation8::new(self.nb_elems, self.nb_perms, step_result);
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

impl Iterator for PermutationGenerator8 {
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

    const NB_ELEMS: u8 = 4;

    fn test_slice(ref_slice: &[u8], some_iter: Option<impl Iterator<Item = u8>>) {
        assert_eq!(ref_slice, some_iter.unwrap().collect::<Vec<_>>().as_slice());
    }

    #[test]
    fn new() {
        let pg = PermutationGenerator8::new(14);
        assert_eq!(PermutationGeneratorError::TooManyElements, pg.unwrap_err());
    }

    #[test]
    fn zero() {
        let mut pg = PermutationGenerator8::new(0).unwrap();
        assert!(pg.next_permutation().is_none());
    }

    #[test]
    fn next_permutation() {
        let mut pg = PermutationGenerator8::new(NB_ELEMS).unwrap();
        test_slice(&[0, 1, 2, 3], pg.next_permutation());
        test_slice(&[0, 1, 3, 2], pg.next_permutation());

        let mut pg = PermutationGenerator8::new(NB_ELEMS + 1).unwrap();
        test_slice(&[0, 1, 2, 3, 4], pg.next_permutation());
        test_slice(&[0, 1, 2, 4, 3], pg.next_permutation());
    }

    #[test]
    fn nth_absolute() {
        test_slice(
            &[0, 1, 2, 3],
            PermutationGenerator8::nth_absolute(NB_ELEMS, 0).unwrap(),
        );
        test_slice(
            &[3, 2, 1, 0],
            PermutationGenerator8::nth_absolute(NB_ELEMS, factorial16(NB_ELEMS) - 1).unwrap(),
        );
        test_slice(
            &[4, 3, 2, 1, 0],
            PermutationGenerator8::nth_absolute(NB_ELEMS + 1, factorial16(NB_ELEMS + 1) - 1)
                .unwrap(),
        );
    }

    #[test]
    fn nth() {
        let mut pg = PermutationGenerator8::new(NB_ELEMS).unwrap();
        test_slice(&[3, 2, 1, 0], pg.nth(factorial16(NB_ELEMS) - 1));
        assert!(pg.next_permutation().is_none());

        let mut pg = PermutationGenerator8::new(NB_ELEMS).unwrap();
        test_slice(&[0, 1, 2, 3], pg.nth(0));
        test_slice(&[3, 2, 1, 0], pg.nth(factorial16(NB_ELEMS) - 2));
    }

    #[test]
    fn iter() {
        let list = PermutationGenerator8::new(NB_ELEMS)
            .unwrap()
            .map(|perm| perm.collect::<Vec<_>>())
            .collect::<Vec<_>>();
        assert_eq!(factorial16(NB_ELEMS) as usize, list.len());
        assert_eq!(&[0, 1, 2, 3], list[0].as_slice());
        assert_eq!(
            &[3, 2, 1, 0],
            list[factorial16(NB_ELEMS) as usize - 1].as_slice()
        );
    }
}
