// #![feature(type_alias_impl_trait)]

use std::convert::TryInto;

use bit_index::*;

mod error;
mod factorial;
mod permutation_generator;
mod single_permutation;

pub use error::*;
pub(crate) use factorial::*;
pub use permutation_generator::*;
pub(crate) use single_permutation::*;

// #[derive(Clone)]
// pub struct PermutationGeneratorWithReferences8<'a, T: 'a + Clone> {
//     pg: PermutationGenerator8,
//     ref_slice: &'a [T],
// }

// impl<'a, T: 'a + Clone> PermutationGeneratorWithReferences8<'a, T> {
//     pub fn new(ref_slice: &'a [T]) -> PResult<Self> {
//         PermutationGenerator8::new(Self::nb_elems(ref_slice)).map(|pg| Self { pg, ref_slice })
//     }

//     pub fn nb_remaining(&self) -> usize {
//         self.pg.nb_remaining()
//     }

//     pub fn nth(&'a mut self, step: u16) -> Option<impl Iterator<Item = &'a T> + 'a> {
//         self.pg
//             .nth(step)
//             .map(move |it| it.map(move |i| self.ref_slice.get(i as usize).unwrap()))
//     }

//     pub fn next_permutation(&'a mut self) -> Option<impl Iterator<Item = &'a T> + 'a> {
//         self.nth(0)
//     }

//     pub fn nth_absolute(ref_slice: &[T], idx: u16) -> PResult<Option<impl Iterator<Item = &T>>> {
//         PermutationGenerator8::nth_absolute(Self::nb_elems(ref_slice), idx).map(move |pg| {
//             pg.map(move |iter| iter.map(move |i| ref_slice.get(i as usize).unwrap()))
//         })
//     }

//     #[inline]
//     fn nb_elems(ref_slice: &[T]) -> u8 {
//         ref_slice.len().try_into().unwrap_or(u8::MAX)
//     }
// }

// #[cfg(test)]
// mod tests {
//     use super::*;

//     #[test]
//     fn new() {
//         let list = ["foo", "bar", "baz"];
//         let mut pgr = PermutationGeneratorWithReferences8::new(&list).unwrap();
//         assert_eq!(6, pgr.nb_remaining());
//         assert_eq!(
//             &["foo", "bar", "baz"],
//             pgr.next_permutation()
//                 .unwrap()
//                 .cloned()
//                 .collect::<Vec<_>>()
//                 .as_slice(),
//         );
//     }
// }
