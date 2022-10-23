#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum PermutationGeneratorError {
    TooManyElements,
    SliceTooSmall,
}
pub type PResult<T> = Result<T, PermutationGeneratorError>;
