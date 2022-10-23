use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct SinglePermutation8 {
    elems: BitIndex8,
    next_mod: u16,
    current_idx: u16,
}

impl SinglePermutation8 {
    pub(crate) fn new(nb_elems: u8, nb_perms: u16, idx: u16) -> Option<Self> {
        if idx >= nb_perms {
            None
        } else {
            Some(Self {
                elems: BitIndex8::new(nb_elems).unwrap(),
                next_mod: nb_perms / (nb_elems as u16),
                current_idx: idx,
            })
        }
    }

    #[inline]
    fn nb_remaining(&self) -> usize {
        self.elems.nb_elements() as usize
    }
}

impl Iterator for SinglePermutation8 {
    type Item = u8;

    fn next(&mut self) -> Option<Self::Item> {
        if self.elems.nb_elements() == 0 {
            return None;
        }
        let bit_nb = self.current_idx / self.next_mod;
        self.current_idx -= bit_nb * self.next_mod;
        self.next_mod /= (self.elems.nb_elements() as u16).saturating_sub(2) + 1;
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

    fn single_perm(nb_elems: u8, idx: u16) -> Option<SinglePermutation8> {
        SinglePermutation8::new(nb_elems, factorial16(nb_elems), idx)
    }

    #[test]
    fn new() {
        assert_eq!(None, single_perm(4, 24));
    }

    #[test]
    fn new_unchecked_iterator() {
        assert_eq!(
            &[0, 1, 2, 3],
            single_perm(4, 0).unwrap().collect::<Vec<_>>().as_slice()
        );

        assert_eq!(
            &[1, 0, 2, 3],
            single_perm(4, 6).unwrap().collect::<Vec<_>>().as_slice()
        );

        assert_eq!(
            &[2, 0, 1, 3],
            single_perm(4, 12).unwrap().collect::<Vec<_>>().as_slice()
        );

        assert_eq!(
            &[3, 0, 1, 2],
            single_perm(4, 18).unwrap().collect::<Vec<_>>().as_slice()
        );

        assert_eq!(
            &[3, 2, 1, 0],
            single_perm(4, 23).unwrap().collect::<Vec<_>>().as_slice()
        );
    }
}
