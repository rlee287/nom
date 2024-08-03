//! Combinators applying parsers in sequence

#[cfg(test)]
mod tests;

use crate::error::ParseError;
use crate::internal::{Err, Needed, IResult, Parser, to_incomplete_success, iresult_map_out};

/// Gets an object from the first parser,
/// then gets another object from the second parser.
///
/// # Arguments
/// * `first` The first parser to apply.
/// * `second` The second parser to apply.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// # use nom::Needed::Size;
/// use nom::sequence::pair;
/// use nom::bytes::complete::tag;
///
/// let mut parser = pair(tag("abc"), tag("efg"));
///
/// assert_eq!(parser("abcefg"), Ok(("", ("abc", "efg"))));
/// assert_eq!(parser("abcefghij"), Ok(("hij", ("abc", "efg"))));
/// assert_eq!(parser(""), Err(Err::Error(("", ErrorKind::Tag))));
/// assert_eq!(parser("123"), Err(Err::Error(("123", ErrorKind::Tag))));
/// ```
pub fn pair<I, O1, O2, E: ParseError<I>, F, G>(
  mut first: F,
  mut second: G,
) -> impl FnMut(I) -> IResult<I, (O1, O2), E>
where
  F: Parser<I, O1, E>,
  G: Parser<I, O2, E>,
{
  move |input: I| {
    match first.parse(input) {
      Ok((input, o1)) => iresult_map_out(second.parse(input), |o2| (o1, o2)),
      Err(Err::IncompleteSuccess((input, o1), n)) => to_incomplete_success(iresult_map_out(second.parse(input), |o2| (o1, o2)), n),
      Err(e) => {
        return Err(e.replace_output_type());
      }
    }
  }
}

/// Matches an object from the first parser and discards it,
/// then gets an object from the second parser.
///
/// # Arguments
/// * `first` The opening parser.
/// * `second` The second parser to get object.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// # use nom::Needed::Size;
/// use nom::sequence::preceded;
/// use nom::bytes::complete::tag;
///
/// let mut parser = preceded(tag("abc"), tag("efg"));
///
/// assert_eq!(parser("abcefg"), Ok(("", "efg")));
/// assert_eq!(parser("abcefghij"), Ok(("hij", "efg")));
/// assert_eq!(parser(""), Err(Err::Error(("", ErrorKind::Tag))));
/// assert_eq!(parser("123"), Err(Err::Error(("123", ErrorKind::Tag))));
/// ```
pub fn preceded<I, O1, O2, E: ParseError<I>, F, G>(
  mut first: F,
  mut second: G,
) -> impl FnMut(I) -> IResult<I, O2, E>
where
  F: Parser<I, O1, E>,
  G: Parser<I, O2, E>,
{
  move |input: I| {
    match first.parse(input) {
      Ok((input, _o1)) => second.parse(input),
      Err(Err::IncompleteSuccess((input, _o1), n)) => to_incomplete_success(second.parse(input), n),
      Err(e) => {
        return Err(e.replace_output_type());
      }
    }
  }
}

/// Gets an object from the first parser,
/// then matches an object from the second parser and discards it.
///
/// # Arguments
/// * `first` The first parser to apply.
/// * `second` The second parser to match an object.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// # use nom::Needed::Size;
/// use nom::sequence::terminated;
/// use nom::bytes::complete::tag;
///
/// let mut parser = terminated(tag("abc"), tag("efg"));
///
/// assert_eq!(parser("abcefg"), Ok(("", "abc")));
/// assert_eq!(parser("abcefghij"), Ok(("hij", "abc")));
/// assert_eq!(parser(""), Err(Err::Error(("", ErrorKind::Tag))));
/// assert_eq!(parser("123"), Err(Err::Error(("123", ErrorKind::Tag))));
/// ```
pub fn terminated<I, O1, O2, E: ParseError<I>, F, G>(
  mut first: F,
  mut second: G,
) -> impl FnMut(I) -> IResult<I, O1, E>
where
  F: Parser<I, O1, E>,
  G: Parser<I, O2, E>,
{
  move |input: I| {
    match first.parse(input) {
      Ok((input, o1)) => iresult_map_out(second.parse(input), |_o2| o1),
      Err(Err::IncompleteSuccess((input, o1), n)) => to_incomplete_success(iresult_map_out(second.parse(input), |_o2| o1), n),
      Err(e) => {
        return Err(e);
      }
    }
  }
}

/// Gets an object from the first parser,
/// then matches an object from the sep_parser and discards it,
/// then gets another object from the second parser.
///
/// # Arguments
/// * `first` The first parser to apply.
/// * `sep` The separator parser to apply.
/// * `second` The second parser to apply.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// # use nom::Needed::Size;
/// use nom::sequence::separated_pair;
/// use nom::bytes::complete::tag;
///
/// let mut parser = separated_pair(tag("abc"), tag("|"), tag("efg"));
///
/// assert_eq!(parser("abc|efg"), Ok(("", ("abc", "efg"))));
/// assert_eq!(parser("abc|efghij"), Ok(("hij", ("abc", "efg"))));
/// assert_eq!(parser(""), Err(Err::Error(("", ErrorKind::Tag))));
/// assert_eq!(parser("123"), Err(Err::Error(("123", ErrorKind::Tag))));
/// ```
pub fn separated_pair<I, O1, O2, O3, E: ParseError<I>, F, G, H>(
  mut first: F,
  mut sep: G,
  mut second: H,
) -> impl FnMut(I) -> IResult<I, (O1, O3), E>
where
  F: Parser<I, O1, E>,
  G: Parser<I, O2, E>,
  H: Parser<I, O3, E>,
{
  move |input: I| {
    let (i, o1, n) = match first.parse(input) {
      Ok((i, o1)) => (i, o1, None),
      Err(Err::IncompleteSuccess((i, o1), n)) => (i, o1, Some(n)),
      Err(e) => return Err(e.replace_output_type())
    };
    let (i, n) = match sep.parse(i) {
      Ok((i, _)) => (i, n),
      Err(Err::IncompleteSuccess((i, _), n2)) => (i, n.or(Some(n2))),
      Err(e) => return Err(e.replace_output_type())
    };
    let second_parse_result = match n {
      Some(n) => to_incomplete_success(second.parse(i), n),
      None => second.parse(i)
    };
    iresult_map_out(second_parse_result, |o3| (o1, o3))
  }
}

/// Matches an object from the first parser and discards it,
/// then gets an object from the second parser,
/// and finally matches an object from the third parser and discards it.
///
/// # Arguments
/// * `first` The first parser to apply and discard.
/// * `second` The second parser to apply.
/// * `third` The third parser to apply and discard.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// # use nom::Needed::Size;
/// use nom::sequence::delimited;
/// use nom::bytes::complete::tag;
///
/// let mut parser = delimited(tag("("), tag("abc"), tag(")"));
///
/// assert_eq!(parser("(abc)"), Ok(("", "abc")));
/// assert_eq!(parser("(abc)def"), Ok(("def", "abc")));
/// assert_eq!(parser(""), Err(Err::Error(("", ErrorKind::Tag))));
/// assert_eq!(parser("123"), Err(Err::Error(("123", ErrorKind::Tag))));
/// ```
pub fn delimited<I, O1, O2, O3, E: ParseError<I>, F, G, H>(
  mut first: F,
  mut second: G,
  mut third: H,
) -> impl FnMut(I) -> IResult<I, O2, E>
where
  F: Parser<I, O1, E>,
  G: Parser<I, O2, E>,
  H: Parser<I, O3, E>,
{
  move |input: I| {
    let (i, n) = match first.parse(input) {
      Ok((i, _o1)) => (i, None),
      Err(Err::IncompleteSuccess((i, _o1), n)) => (i, Some(n)),
      Err(e) => return Err(e.replace_output_type())
    };
    let (i, o2, n) = match second.parse(i) {
      Ok((i, o2)) => (i, o2, n),
      Err(Err::IncompleteSuccess((i, o2), n2)) => (i, o2, n.or(Some(n2))),
      Err(e) => return Err(e.replace_output_type())
    };
    let third_parse_result = match n {
      Some(n) => to_incomplete_success(third.parse(i), n),
      None => third.parse(i)
    };
    iresult_map_out(third_parse_result, |_o3| o2)
  }
}

/// Helper trait for the tuple combinator.
///
/// This trait is implemented for tuples of parsers of up to 21 elements.
pub trait Tuple<I, O, E> {
  /// Parses the input and returns a tuple of results of each parser.
  fn parse(&mut self, input: I) -> IResult<I, O, E>;
}

impl<Input, Output, Error: ParseError<Input>, F: Parser<Input, Output, Error>>
  Tuple<Input, (Output,), Error> for (F,)
{
  fn parse(&mut self, input: Input) -> IResult<Input, (Output,), Error> {
    self.0.parse(input).map(|(i, o)| (i, (o,)))
  }
}

macro_rules! tuple_trait(
  ($name1:ident $ty1:ident, $name2: ident $ty2:ident, $($name:ident $ty:ident),*) => (
    tuple_trait!(__impl $name1 $ty1, $name2 $ty2; $($name $ty),*);
  );
  (__impl $($name:ident $ty: ident),+; $name1:ident $ty1:ident, $($name2:ident $ty2:ident),*) => (
    tuple_trait_impl!($($name $ty),+);
    tuple_trait!(__impl $($name $ty),+ , $name1 $ty1; $($name2 $ty2),*);
  );
  (__impl $($name:ident $ty: ident),+; $name1:ident $ty1:ident) => (
    tuple_trait_impl!($($name $ty),+);
    tuple_trait_impl!($($name $ty),+, $name1 $ty1);
  );
);

macro_rules! tuple_trait_impl(
  ($($name:ident $ty: ident),+) => (
    impl<
      Input: Clone, $($ty),+ , Error: ParseError<Input>,
      $($name: Parser<Input, $ty, Error>),+
    > Tuple<Input, ( $($ty),+ ), Error> for ( $($name),+ ) {

      fn parse(&mut self, input: Input) -> IResult<Input, ( $($ty),+ ), Error> {
        tuple_trait_inner!(0, self, input, (), $($name)+)

      }
    }
  );
);

macro_rules! tuple_trait_inner(
  ($it:tt, $self:expr, $input:expr, (), $head:ident $($id:ident)+) => ({
    let (i, o) = $self.$it.parse($input.clone())?;

    succ!($it, tuple_trait_inner!($self, i, ( o ), $($id)+))
  });
  ($it:tt, $self:expr, $input:expr, ($($parsed:tt)*), $head:ident $($id:ident)+) => ({
    let (i, o) = $self.$it.parse($input.clone())?;

    succ!($it, tuple_trait_inner!($self, i, ($($parsed)* , o), $($id)+))
  });
  ($it:tt, $self:expr, $input:expr, ($($parsed:tt)*), $head:ident) => ({
    let (i, o) = $self.$it.parse($input.clone())?;

    Ok((i, ($($parsed)* , o)))
  });
);

tuple_trait!(FnA A, FnB B, FnC C, FnD D, FnE E, FnF F, FnG G, FnH H, FnI I, FnJ J, FnK K, FnL L,
  FnM M, FnN N, FnO O, FnP P, FnQ Q, FnR R, FnS S, FnT T, FnU U);

// Special case: implement `Tuple` for `()`, the unit type.
// This can come up in macros which accept a variable number of arguments.
// Literally, `()` is an empty tuple, so it should simply parse nothing.
impl<I, E: ParseError<I>> Tuple<I, (), E> for () {
  fn parse(&mut self, input: I) -> IResult<I, (), E> {
    Ok((input, ()))
  }
}

///Applies a tuple of parsers one by one and returns their results as a tuple.
///There is a maximum of 21 parsers
/// ```rust
/// # use nom::{Err, error::ErrorKind};
/// use nom::sequence::tuple;
/// use nom::character::complete::{alpha1, digit1};
/// let mut parser = tuple((alpha1, digit1, alpha1));
///
/// assert_eq!(parser("abc123def"), Ok(("", ("abc", "123", "def"))));
/// assert_eq!(parser("123def"), Err(Err::Error(("123def", ErrorKind::Alpha))));
/// ```
pub fn tuple<I, O, E: ParseError<I>, List: Tuple<I, O, E>>(
  mut l: List,
) -> impl FnMut(I) -> IResult<I, O, E> {
  move |i: I| l.parse(i)
}
