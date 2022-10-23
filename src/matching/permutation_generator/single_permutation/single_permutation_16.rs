use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct SinglePermutation16 {
    elems: BitIndex16,
    next_mod: u64,
    current_idx: u64,
}

impl SinglePermutation16 {
    pub(crate) fn new(nb_elems: u8, nb_perms: u64, idx: u64) -> Option<Self> {
        if idx >= nb_perms {
            None
        } else {
            Some(Self {
                elems: BitIndex16::new(nb_elems).unwrap(),
                next_mod: nb_perms / (nb_elems as u64),
                current_idx: idx,
            })
        }
    }

    #[inline]
    fn nb_remaining(&self) -> usize {
        self.elems.nb_elements() as usize
    }
}

impl Iterator for SinglePermutation16 {
    type Item = u8;

    fn next(&mut self) -> Option<Self::Item> {
        if self.elems.nb_elements() == 0 {
            return None;
        }
        let bit_nb = self.current_idx / self.next_mod;
        self.current_idx -= bit_nb * self.next_mod;
        self.next_mod /= (self.elems.nb_elements() as u64).saturating_sub(2) + 1;
        self.elems.pop(bit_nb as u8)
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

    fn single_perm(nb_elems: u8, idx: u64) -> Option<SinglePermutation16> {
        SinglePermutation16::new(nb_elems, factorial64(nb_elems), idx)
    }

    #[test]
    fn new() {
        assert_eq!(None, single_perm(10, 3628800));
    }

    #[test]
    fn new_unchecked_iterator() {
        assert_eq!(
            &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
            single_perm(10, 0).unwrap().collect::<Vec<_>>().as_slice()
        );

        assert_eq!(
            &[1, 0, 2, 3, 4, 5, 6, 7, 8, 9],
            single_perm(10, 362880)
                .unwrap()
                .collect::<Vec<_>>()
                .as_slice()
        );

        assert_eq!(
            &[2, 0, 1, 3, 4, 5, 6, 7, 8, 9],
            single_perm(10, 362880 * 2)
                .unwrap()
                .collect::<Vec<_>>()
                .as_slice()
        );

        assert_eq!(
            &[3, 0, 1, 2, 4, 5, 6, 7, 8, 9],
            single_perm(10, 362880 * 3)
                .unwrap()
                .collect::<Vec<_>>()
                .as_slice()
        );

        assert_eq!(
            &[9, 8, 7, 6, 5, 4, 3, 2, 1, 0],
            single_perm(10, 3628800 - 1)
                .unwrap()
                .collect::<Vec<_>>()
                .as_slice()
        );
    }
}
