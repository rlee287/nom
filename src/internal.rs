//! Basic types to build the parsers

use self::Needed::*;
use crate::error::{self, ErrorKind};
use crate::lib::std::fmt;
use core::num::NonZeroUsize;

/// Holds the result of parsing functions
///
/// It depends on the input type `I`, the output type `O`, and the error type `E`
/// (by default `(I, nom::ErrorKind)`)
///
/// The `Ok` side is a pair containing the remainder of the input (the part of the data that
/// was not parsed) and the produced value. The `Err` side contains an instance of `nom::Err`.
///
/// Outside of the parsing code, you can use the [Finish::finish] method to convert
/// it to a more common result type
pub type IResult<I, O, E = error::Error<I>> = Result<(I, O), Err<I, O, E>>;

/// Helper trait to convert a parser's result to a more manageable type
pub trait Finish<I, O, E> {
  /// converts the parser's result to a type that is more consumable by error
  /// management libraries. It keeps the same `Ok` branch, and merges `Err::Error`
  /// and `Err::Failure` into the `Err` side.
  ///
  /// If the result is `Err(Err::IncompleteFail(_))`, this method will return an error,
  /// while if the resutl is `Err(Err::IncompleteSuccess(_))`, this method will return a successful parse result.
  /// Use `is_incomplete()` on `IResult::Err` if you have more data and want to check
  /// if that data is needed to finish parsing.
  fn finish(self) -> Result<(I, O), E>;
}

impl<I, O, E> Finish<I, O, E> for IResult<I, O, E> {
  fn finish(self) -> Result<(I, O), E> {
    match self {
      Ok(res) => Ok(res),
      Err(Err::Error(e)) | Err(Err::Failure(e)) => Err(e),
      Err(Err::IncompleteFail(e, _)) => Err(e),
      Err(Err::IncompleteSuccess(res, _)) => Ok(res)
    }
  }
}

/// Contains information on needed data if a parser returned `Incomplete`
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[cfg_attr(nightly, warn(rustdoc::missing_doc_code_examples))]
pub enum Needed {
  /// Needs more data, but we do not know how much
  Unknown,
  /// Contains the required data size in bytes
  Size(NonZeroUsize),
}

impl Needed {
  /// Creates `Needed` instance, returns `Needed::Unknown` if the argument is zero
  pub fn new(s: usize) -> Self {
    match NonZeroUsize::new(s) {
      Some(sz) => Needed::Size(sz),
      None => Needed::Unknown,
    }
  }

  /// Indicates if we know how many bytes we need
  pub fn is_known(&self) -> bool {
    *self != Unknown
  }

  /// Maps a `Needed` to `Needed` by applying a function to a contained `Size` value.
  #[inline]
  pub fn map<F: Fn(NonZeroUsize) -> usize>(self, f: F) -> Needed {
    match self {
      Unknown => Unknown,
      Size(n) => Needed::new(f(n)),
    }
  }
}

/// The `Err` enum indicates the parser was not successful
///
/// It has four cases:
///
/// * `IncompleteFail` indicates that more data is needed to decide, but that parsing
/// should fail if no more data is available. The `Needed` enum can contain how many
/// additional bytes are necessary. If you are sure your parser is working on full data,
/// you can wrap your parser with the `complete` combinator to transform that case in `Error`.
/// * `IncompleteSuccess` indicates that more data is needed to decide, but that parsing
/// should succeed if no more data is available. The `Needed` enum can contain how many
/// additional bytes are necessary. If you are sure your parser is working on full data,
/// you can wrap your parser with the `complete` combinator to extract the parse result.
/// * `Error` means some parser did not succeed, but another one might (as an example,
/// when testing different branches of an `alt` combinator)
/// * `Failure` indicates an unrecoverable error. As an example, if you recognize a prefix
/// to decide on the next parser to apply, and that parser fails, you know there's no need
/// to try other parsers, you were already in the right branch, so the data is invalid
///
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(nightly, warn(rustdoc::missing_doc_code_examples))]
pub enum Err<I, O, E> {
  /// There was not enough data, and this should be a failure on end-of-data
  IncompleteFail(E, Needed),
  /// There was not enough data, but this should be a success on end-of-data
  IncompleteSuccess((I, O), Needed),
  /// The parser had an error (recoverable)
  Error(E),
  /// The parser had an unrecoverable error: we got to the right
  /// branch and we know other branches won't work, so backtrack
  /// as fast as possible
  Failure(E),
}

impl<I, O, E> Err<I, O, E> {
  /// Tests if the result is Incomplete
  pub fn is_incomplete(&self) -> bool {
    matches!(self, Self::IncompleteFail(..) | Self::IncompleteSuccess(..))
  }

  /// Applies the given function to the inner error
  pub fn map_err<E2, F>(self, f: F) -> Err<I, O, E2>
  where
    F: FnOnce(E) -> E2,
  {
    match self {
      Err::IncompleteFail(e, n) => Err::IncompleteFail(f(e), n),
      Err::IncompleteSuccess(io, n) => Err::IncompleteSuccess(io, n),
      Err::Failure(t) => Err::Failure(f(t)),
      Err::Error(t) => Err::Error(f(t)),
    }
  }

  // TODO: make these public if there would be a public use for them

  /// Replaces the input of an incomplete success
  pub(crate) fn replace_input<I2>(self, i2: I2) -> Err<I2, O, E> {
    match self {
      Err::IncompleteFail(e, n) => Err::IncompleteFail(e, n),
      Err::IncompleteSuccess((_, o), n) => Err::IncompleteSuccess((i2, o), n),
      Err::Failure(e) => Err::Failure(e),
      Err::Error(e) => Err::Error(e),
    }
  }
  /// Replaces the input type; panics if an input is actually needed
  pub(crate) fn replace_input_type<I2>(self) -> Err<I2, O, E> {
    match self {
      Err::IncompleteFail(e, n) => Err::IncompleteFail(e, n),
      Err::IncompleteSuccess(..) => panic!("Cannot use replace_input_type when input is needed"),
      Err::Failure(e) => Err::Failure(e),
      Err::Error(e) => Err::Error(e),
    }
  }
  /// Replaces the output type; panics if an output is actually needed
  pub(crate) fn replace_output_type<O2>(self) -> Err<I, O2, E> {
    match self {
      Err::IncompleteFail(e, n) => Err::IncompleteFail(e, n),
      Err::IncompleteSuccess(..) => panic!("Cannot use replace_output_type when input is needed"),
      Err::Failure(e) => Err::Failure(e),
      Err::Error(e) => Err::Error(e),
    }
  }

  /// Automatically converts between errors if the underlying type supports it
  pub fn convert<F>(e: Err<I, O, F>) -> Self
  where
    E: From<F>,
  {
    e.map_err(crate::lib::std::convert::Into::into)
  }
}

impl<I, O, T> Err<I, O, (T, ErrorKind)> {
  /// Maps `Err<(T, ErrorKind)>` to `Err<(U, ErrorKind)>` with the given `F: T -> U`
  pub fn map_input<U, F>(self, f: F) -> Err<I, O, (U, ErrorKind)>
  where
    F: FnOnce(T) -> U,
  {
    match self {
      Err::IncompleteFail((input, k), n) => Err::IncompleteFail((f(input), k), n),
      Err::IncompleteSuccess(io, n) => Err::IncompleteSuccess(io, n),
      Err::Failure((input, k)) => Err::Failure((f(input), k)),
      Err::Error((input, k)) => Err::Error((f(input), k)),
    }
  }
}

impl<I, O, T> Err<I, O, error::Error<T>> {
  /// Maps `Err<error::Error<T>>` to `Err<error::Error<U>>` with the given `F: T -> U`
  pub fn map_input<U, F>(self, f: F) -> Err<I, O, error::Error<U>>
  where
    F: FnOnce(T) -> U,
  {
    match self {
      Err::IncompleteFail(error::Error { input, code }, n) => Err::IncompleteFail(error::Error { input: f(input), code }, n),
      Err::IncompleteSuccess(io, n) => Err::IncompleteSuccess(io, n),
      Err::Failure(error::Error { input, code }) => Err::Failure(error::Error {
        input: f(input),
        code,
      }),
      Err::Error(error::Error { input, code }) => Err::Error(error::Error {
        input: f(input),
        code,
      }),
    }
  }
}

#[cfg(feature = "alloc")]
use crate::lib::std::{borrow::ToOwned, string::String, vec::Vec};
#[cfg(feature = "alloc")]
impl<I, O> Err<I, O, (&[u8], ErrorKind)> {
  /// Obtaining ownership
  #[cfg_attr(feature = "docsrs", doc(cfg(feature = "alloc")))]
  pub fn to_owned(self) -> Err<I, O, (Vec<u8>, ErrorKind)> {
    self.map_input(ToOwned::to_owned)
  }
}

#[cfg(feature = "alloc")]
impl<I, O> Err<I, O, (&str, ErrorKind)> {
  /// Obtaining ownership
  #[cfg_attr(feature = "docsrs", doc(cfg(feature = "alloc")))]
  pub fn to_owned(self) -> Err<I, O, (String, ErrorKind)> {
    self.map_input(ToOwned::to_owned)
  }
}

#[cfg(feature = "alloc")]
impl<I, O> Err<I, O, error::Error<&[u8]>> {
  /// Obtaining ownership
  #[cfg_attr(feature = "docsrs", doc(cfg(feature = "alloc")))]
  pub fn to_owned(self) -> Err<I, O, error::Error<Vec<u8>>> {
    self.map_input(ToOwned::to_owned)
  }
}

#[cfg(feature = "alloc")]
impl<I, O> Err<I, O, error::Error<&str>> {
  /// Obtaining ownership
  #[cfg_attr(feature = "docsrs", doc(cfg(feature = "alloc")))]
  pub fn to_owned(self) -> Err<I, O, error::Error<String>> {
    self.map_input(ToOwned::to_owned)
  }
}

impl<I: Eq, O: Eq, E: Eq> Eq for Err<I, O, E> {}

impl<I, O, E> fmt::Display for Err<I, O, E>
where
  E: fmt::Debug,
{
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Err::IncompleteFail(_e, Needed::Size(u)) => write!(f, "Parsing requires {} bytes/chars (would fail if eof)", u),
      Err::IncompleteFail(_e, Needed::Unknown) => write!(f, "Parsing requires more data (would fail if eof)"),
      Err::IncompleteSuccess(_io, Needed::Size(u)) => write!(f, "Parsing requires {} bytes/chars (would succeed if eof)", u),
      Err::IncompleteSuccess(_io, Needed::Unknown) => write!(f, "Parsing requires more data (would succeed if eof)"),
      Err::Failure(c) => write!(f, "Parsing Failure: {:?}", c),
      Err::Error(c) => write!(f, "Parsing Error: {:?}", c),
    }
  }
}

#[cfg(feature = "std")]
use std::error::Error;

#[cfg(feature = "std")]
impl<I, O, E> Error for Err<I, O, E>
where
  I: fmt::Debug,
  O: fmt::Debug,
  E: fmt::Debug,
{
  fn source(&self) -> Option<&(dyn Error + 'static)> {
    None // no underlying error
  }
}

/// Converts an Ok parse result into an IncompleteSuccess
/// Does not replace the Needed value if already an Incomplete
// TODO: should it?
pub(crate) fn to_incomplete_success<I, O, E>(res: IResult<I, O, E>, needed: Needed) -> IResult<I, O, E> {
  match res {
    Ok((i, o)) => Err(Err::IncompleteSuccess((i, o), needed)),
    Err(Err::IncompleteSuccess((i, o), n)) => Err(Err::IncompleteSuccess((i, o), n)),
    Err(e) => Err(e)
  }
}

/// Applies the given function to an IResult's output
pub(crate) fn iresult_map_out<I, O, O2, E, F>(res: IResult<I, O, E>, f: F) -> IResult<I, O2, E>
where
  F: FnOnce(O) -> O2,
{
  match res {
    Ok((i, o)) => Ok((i, f(o))),
    Err(Err::IncompleteFail(e, n)) => Err(Err::IncompleteFail(e, n)),
    Err(Err::IncompleteSuccess((i, o), n)) => Err(Err::IncompleteSuccess((i, f(o)), n)),
    Err(Err::Failure(e)) => Err(Err::Failure(e)),
    Err(Err::Error(e)) => Err(Err::Error(e)),
  }
}

/// All nom parsers implement this trait
pub trait Parser<I, O, E> {
  /// A parser takes in input type, and returns a `Result` containing
  /// either the remaining input and the output value, or an error
  fn parse(&mut self, input: I) -> IResult<I, O, E>;

  /// Maps a function over the result of a parser
  fn map<G, O2>(self, g: G) -> Map<Self, G, O>
  where
    G: Fn(O) -> O2,
    Self: core::marker::Sized,
  {
    Map {
      f: self,
      g,
      phantom: core::marker::PhantomData,
    }
  }

  /// Creates a second parser from the output of the first one, then apply over the rest of the input
  fn flat_map<G, H, O2>(self, g: G) -> FlatMap<Self, G, O>
  where
    G: FnMut(O) -> H,
    H: Parser<I, O2, E>,
    Self: core::marker::Sized,
  {
    FlatMap {
      f: self,
      g,
      phantom: core::marker::PhantomData,
    }
  }

  /// Applies a second parser over the output of the first one
  fn and_then<G, O2>(self, g: G) -> AndThen<Self, G, O>
  where
    G: Parser<O, O2, E>,
    Self: core::marker::Sized,
  {
    AndThen {
      f: self,
      g,
      phantom: core::marker::PhantomData,
    }
  }

  /// Applies a second parser after the first one, return their results as a tuple
  fn and<G, O2>(self, g: G) -> And<Self, G>
  where
    G: Parser<I, O2, E>,
    Self: core::marker::Sized,
  {
    And { f: self, g }
  }

  /// Applies a second parser over the input if the first one failed
  fn or<G>(self, g: G) -> Or<Self, G>
  where
    G: Parser<I, O, E>,
    Self: core::marker::Sized,
  {
    Or { f: self, g }
  }

  /// automatically converts the parser's output and error values to another type, as long as they
  /// implement the `From` trait
  fn into<O2: From<O>, E2: From<E>>(self) -> Into<Self, O, O2, E, E2>
  where
    Self: core::marker::Sized,
  {
    Into {
      f: self,
      phantom_out1: core::marker::PhantomData,
      phantom_err1: core::marker::PhantomData,
      phantom_out2: core::marker::PhantomData,
      phantom_err2: core::marker::PhantomData,
    }
  }
}

impl<'a, I, O, E, F> Parser<I, O, E> for F
where
  F: FnMut(I) -> IResult<I, O, E> + 'a,
{
  fn parse(&mut self, i: I) -> IResult<I, O, E> {
    self(i)
  }
}

#[cfg(feature = "alloc")]
use alloc::boxed::Box;

#[cfg(feature = "alloc")]
impl<'a, I, O, E> Parser<I, O, E> for Box<dyn Parser<I, O, E> + 'a> {
  fn parse(&mut self, input: I) -> IResult<I, O, E> {
    (**self).parse(input)
  }
}

/// Implementation of `Parser::map`
#[cfg_attr(nightly, warn(rustdoc::missing_doc_code_examples))]
pub struct Map<F, G, O1> {
  f: F,
  g: G,
  phantom: core::marker::PhantomData<O1>,
}

impl<'a, I, O1, O2, E, F: Parser<I, O1, E>, G: Fn(O1) -> O2> Parser<I, O2, E> for Map<F, G, O1> {
  fn parse(&mut self, i: I) -> IResult<I, O2, E> {
    iresult_map_out(self.f.parse(i), &mut self.g)
  }
}

/// Implementation of `Parser::flat_map`
#[cfg_attr(nightly, warn(rustdoc::missing_doc_code_examples))]
pub struct FlatMap<F, G, O1> {
  f: F,
  g: G,
  phantom: core::marker::PhantomData<O1>,
}

impl<'a, I, O1, O2, E, F: Parser<I, O1, E>, G: Fn(O1) -> H, H: Parser<I, O2, E>> Parser<I, O2, E>
  for FlatMap<F, G, O1>
{
  fn parse(&mut self, i: I) -> IResult<I, O2, E> {
    match self.f.parse(i) {
      Err(Err::IncompleteSuccess((i, o), n)) => to_incomplete_success((self.g)(o).parse(i), n),
      Err(e) => Err(e.replace_output_type()),
      Ok((i, o)) => (self.g)(o).parse(i),
    }
  }
}

/// Implementation of `Parser::and_then`
#[cfg_attr(nightly, warn(rustdoc::missing_doc_code_examples))]
pub struct AndThen<F, G, O1> {
  f: F,
  g: G,
  phantom: core::marker::PhantomData<O1>,
}

impl<'a, I, O1, O2, E, F: Parser<I, O1, E>, G: Parser<O1, O2, E>> Parser<I, O2, E>
  for AndThen<F, G, O1>
{
  fn parse(&mut self, i: I) -> IResult<I, O2, E> {
    match self.f.parse(i) {
      Ok((i, o1)) => {
        match self.g.parse(o1) {
          Ok((_, o2)) => Ok((i, o2)),
          Err(e) => Err(e.replace_input(i))
        }
      },
      Err(Err::IncompleteSuccess((i, o1), n)) => {
        match self.g.parse(o1) {
          Ok((_, o2)) => Err(Err::IncompleteSuccess((i, o2), n)),
          Err(Err::IncompleteSuccess((_, o2), n2)) => Err(Err::IncompleteSuccess((i, o2), n2)),
          Err(e) => Err(e.replace_input_type())
        }
      },
      Err(e) => Err(e.replace_output_type()),
    }
  }
}

/// Implementation of `Parser::and`
#[cfg_attr(nightly, warn(rustdoc::missing_doc_code_examples))]
pub struct And<F, G> {
  f: F,
  g: G,
}

impl<'a, I, O1, O2, E, F: Parser<I, O1, E>, G: Parser<I, O2, E>> Parser<I, (O1, O2), E>
  for And<F, G>
{
  fn parse(&mut self, i: I) -> IResult<I, (O1, O2), E> {
    match self.f.parse(i) {
      Ok((i, o1)) => iresult_map_out(self.g.parse(i), |o2| (o1, o2)),
      Err(Err::IncompleteSuccess((i, o1), n)) => to_incomplete_success(iresult_map_out(self.g.parse(i), |o2| (o1, o2)), n),
      Err(e) => Err(e.replace_output_type())
    }
  }
}

/// Implementation of `Parser::or`
#[cfg_attr(nightly, warn(rustdoc::missing_doc_code_examples))]
pub struct Or<F, G> {
  f: F,
  g: G,
}

impl<'a, I: Clone, O, E: crate::error::ParseError<I>, F: Parser<I, O, E>, G: Parser<I, O, E>>
  Parser<I, O, E> for Or<F, G>
{
  fn parse(&mut self, i: I) -> IResult<I, O, E> {
    match self.f.parse(i.clone()) {
      Err(Err::Error(e1)) => match self.g.parse(i) {
        Err(Err::Error(e2)) => Err(Err::Error(e1.or(e2))),
        res => res,
      },
      res => res,
    }
  }
}

/// Implementation of `Parser::into`
#[cfg_attr(nightly, warn(rustdoc::missing_doc_code_examples))]
pub struct Into<F, O1, O2: From<O1>, E1, E2: From<E1>> {
  f: F,
  phantom_out1: core::marker::PhantomData<O1>,
  phantom_err1: core::marker::PhantomData<E1>,
  phantom_out2: core::marker::PhantomData<O2>,
  phantom_err2: core::marker::PhantomData<E2>,
}

impl<
    'a,
    I: Clone,
    O1,
    O2: From<O1>,
    E1,
    E2: crate::error::ParseError<I> + From<E1>,
    F: Parser<I, O1, E1>,
  > Parser<I, O2, E2> for Into<F, O1, O2, E1, E2>
{
  fn parse(&mut self, i: I) -> IResult<I, O2, E2> {
    match self.f.parse(i) {
      Ok((i, o)) => Ok((i, o.into())),
      Err(Err::Error(e)) => Err(Err::Error(e.into())),
      Err(Err::Failure(e)) => Err(Err::Failure(e.into())),
      Err(Err::IncompleteFail(e, n)) => Err(Err::IncompleteFail(e.into(), n)),
      Err(Err::IncompleteSuccess((i, o), n)) => Err(Err::IncompleteSuccess((i, o.into()), n))
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::error::ErrorKind;

  #[doc(hidden)]
  #[macro_export]
  macro_rules! assert_size (
    ($t:ty, $sz:expr) => (
      assert_eq!(crate::lib::std::mem::size_of::<$t>(), $sz);
    );
  );

  #[test]
  #[cfg(target_pointer_width = "64")]
  fn size_test() {
    assert_size!(IResult<&[u8], &[u8], (&[u8], u32)>, 40);
    //FIXME: since rust 1.65, this is now 32 bytes, likely thanks to https://github.com/rust-lang/rust/pull/94075
    // deactivating that test for now because it'll have different values depending on the rust version
    // assert_size!(IResult<&str, &str, u32>, 40);
    assert_size!(Needed, 8);
    assert_size!(Err<&[u8], &[u8], u32>, 16);
    assert_size!(ErrorKind, 1);
  }

  #[test]
  fn err_map_test() {
    let e: Err<&[u8], &[u8], i32> = Err::Error(1);
    assert_eq!(e.map_err(|v| v + 1), Err::Error(2));
  }

  #[test]
  fn iresult_map_out_test() {
    let e: Err<&[u8; 1], i32, i32> = Err::IncompleteSuccess((&[2], 4), Needed::Unknown);
    assert_eq!(iresult_map_out(Err(e), |n| n*2), Err(Err::IncompleteSuccess((&[2], 8), Needed::Unknown)))
  }
}
