macro_rules! impl_factorial {
    ($fact:ident, $fact_type:ty) => {
        #[inline]
        pub(crate) fn $fact(nb_elems: u8) -> $fact_type {
            match nb_elems {
                0 | 1 | 2 => nb_elems as $fact_type,
                _ => (1..=nb_elems).map(|i| i as $fact_type).product(),
            }
        }
    };
}

impl_factorial!(factorial16, u16);
impl_factorial!(factorial64, u64);
impl_factorial!(factorial128, u128);
