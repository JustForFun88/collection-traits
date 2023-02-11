use core::convert::Infallible;
use core::ops::ControlFlow;

/// The `Try` trait that allows you to abstract over [`Result`], [`Option`] or other
/// error handling structures. At its core, it is a combination of two [`core::ops::Try`]
/// and [`core::ops::FromResidual`] unstable traits  from the standard library.
///
/// # FIXME
///
/// This trait is a combination of [`core::ops::Try`] and [`core::ops::FromResidual`] traits.
/// Remove this trait in favor of them after they are stabilized.
///
/// [`core::ops::Try`]: https://doc.rust-lang.org/core/ops/trait.Try.html
/// [`core::ops::FromResidual`]: https://doc.rust-lang.org/core/ops/trait.FromResidual.html
pub(super) trait Try {
    /// The type of the value produced when *not* short-circuiting. For example,
    /// for [`Option<T>`] it is equal to `T`, for [`Result<T, E>`] it is also equal to `T`.
    ///
    /// Read https://doc.rust-lang.org/core/ops/trait.Try.html#associatedtype.Output for more
    /// information.
    type Output;

    /// The type of the value passed to [`Try::from_residual`] when short-circuiting.
    ///
    /// This represents the possible values of the `Self` type which are *not*
    /// represented by the `Output` type. Unlike the `Output` type, which is a raw generic
    /// type, this type must be some kind of "colored" type in order to be distinguished
    /// from the the residuals of other types.
    ///
    /// For example, you might think that for example for [`Result<T, E>`] you can write the
    /// following implementation:
    ///
    /// ```ignore
    /// impl<T, E> Try for Result<T, E> {
    ///     type Output = T;
    ///     type Residual = E;
    ///     // ...
    /// }
    /// ```
    /// This would be wrong, since then for [`Option<T>`] you would have to write an implementation
    /// like (this implementation simply won't compile because `None` is not a type, but just a variant
    /// of the [`Option`] type):
    ///
    /// ```ignore
    /// impl<T, E> Try for Option<T> {
    ///     type Output = T;
    ///     type Residual = None;
    ///     // ...
    /// }
    /// ```
    /// In addition, in such an `impl<T, E> Try for Result<T, E>`, two raw generic types `T` and `E` do
    /// not make it possible to distinguish `enum Result<T, E>` from, for example, `enum Either< T, E>`.
    ///
    /// That is, `type Residual` must be a quasi-type containing information not only about type residual,
    /// but also information about the type itself, that is, like this:
    ///
    /// ```ignore
    /// enum Infallible {}
    ///
    /// impl<T, E> Try for Result<T, E> {
    ///     type Output = T;
    ///     type Residual = Result<Infallible, E>;
    ///     // ...
    /// }
    ///
    /// impl<T, E> Try for Option<T> {
    ///     type Output = T;
    ///     type Residual = Option<Infallible>;
    ///     // ...
    /// }
    /// ```
    ///
    /// Read https://doc.rust-lang.org/core/ops/trait.Try.html#associatedtype.Residual for more
    /// information.
    type Residual;

    /// Constructs the type from a compatible `Residual` type.
    ///
    /// This should be implemented consistently with the `branch` method such
    /// that `Try::from_residual(r).branch() --> ControlFlow::Break(r)`.
    /// (It must not be an *identical* residual when interconversion is involved.)
    ///
    /// Read https://doc.rust-lang.org/core/ops/trait.FromResidual.html for more
    /// information and examples.
    fn from_residual(residual: Self::Residual) -> Self;

    /// Constructs the type from its `Output` type.
    ///
    /// This should be implemented consistently with the `branch` method such
    /// that `Try::from_output(x).branch() --> ControlFlow::Continue(x)`.
    ///
    /// Read https://doc.rust-lang.org/core/ops/trait.Try.html#tymethod.from_output
    /// for more information and examples.
    fn from_output(output: Self::Output) -> Self;

    /// Used to decide whether the operator should produce a value
    /// (because this returned [`ControlFlow::Continue`])
    /// or propagate a value back to the caller
    /// (because this returned [`ControlFlow::Break`]).
    ///
    /// Read https://doc.rust-lang.org/core/ops/trait.Try.html#tymethod.branch for more
    /// information and examples.
    fn branch(self) -> ControlFlow<Self::Residual, Self::Output>;
}

/// Allows retrieving the canonical type implementing [`Try`] that has this type
/// as its residual and allows it to hold an `O` as its output.
///
/// If you think of the `Try` trait as splitting a type into its [`Try::Output`]
/// and [`Try::Residual`] components, this allows putting them back together.
///
/// The `Residual<O>` can be read as "Some residual of a try type whose output is O".
///
/// For example,
/// `Result<T, E>: Try<Output = T, Residual = Result<Infallible, E>>`,
/// and in the other direction,
/// `<Result<Infallible, E> as Residual<T>>::TryType = Result<T, E>`.
///
/// Read https://doc.rust-lang.org/core/ops/trait.Residual.html for more
/// information and examples.
///
/// # FIXME
///
/// This trait is similar to the [`core::ops::Residual`] trait. Remove that trait
/// in favor of that one after it stabilizes.
pub(super) trait Residual<O> {
    /// The "return" type of this meta-function.
    type TryType: Try<Output = O, Residual = Self>;
}

/// This is a helper type alias to make a bit more readable input-output type association.
///
/// For example if `T` is `Result<U, E>`, so
/// `ChangeOutputType<T, V> = <<Result<U, E> as Try>::Residual as Residual<V>>::TryType = Result<V, E>`
/// where `Result<U, E> as Try>::Residual = Result<Infallible, E>`.
///
/// If `T` is `Option<U>`, so
/// `ChangeOutputType<T, V> = <<Option<U> as Try>::Residual as Residual<V>>::TryType = Option<V>`
/// where `Option<U> as Try>::Residual = Option<Infallible>`.
///
/// If `T` is `NeverShortCircuit<U>`, so
/// `ChangeOutputType<T, V> = <<NeverShortCircuit<U> as Try>::Residual as Residual<V>>::TryType = NeverShortCircuit<V>`
/// where `NeverShortCircuit<U> as Try>::Residual = NeverShortCircuitResidual`.
pub(super) type ChangeOutputType<T, V> = <<T as Try>::Residual as Residual<V>>::TryType;

impl<T> Try for Option<T> {
    type Output = T;
    type Residual = Option<Infallible>;

    #[inline]
    fn from_residual(residual: Self::Residual) -> Self {
        match residual {
            None => None,
            Some(value) => match value {},
        }
    }

    #[inline]
    fn from_output(output: Self::Output) -> Self {
        Some(output)
    }

    #[inline]
    fn branch(self) -> ControlFlow<Self::Residual, Self::Output> {
        match self {
            Some(v) => ControlFlow::Continue(v),
            None => ControlFlow::Break(None),
        }
    }
}

impl<T, E> Try for Result<T, E> {
    type Output = T;
    type Residual = Result<Infallible, E>;

    #[inline]
    fn from_residual(residual: Self::Residual) -> Self {
        match residual {
            Err(error) => Err(error),
            Ok(value) => match value {},
        }
    }

    #[inline]
    fn from_output(output: Self::Output) -> Self {
        Ok(output)
    }

    #[inline]
    fn branch(self) -> ControlFlow<Self::Residual, Self::Output> {
        match self {
            Ok(v) => ControlFlow::Continue(v),
            Err(e) => ControlFlow::Break(Err(e)),
        }
    }
}

impl<B, C> Try for ControlFlow<B, C> {
    type Output = C;
    type Residual = ControlFlow<B, Infallible>;

    #[inline]
    fn from_residual(residual: ControlFlow<B, Infallible>) -> Self {
        match residual {
            ControlFlow::Continue(value) => match value {},
            ControlFlow::Break(x) => ControlFlow::Break(x),
        }
    }
    #[inline]
    fn from_output(output: Self::Output) -> Self {
        ControlFlow::Continue(output)
    }

    #[inline]
    fn branch(self) -> ControlFlow<Self::Residual, Self::Output> {
        match self {
            ControlFlow::Continue(c) => ControlFlow::Continue(c),
            ControlFlow::Break(b) => ControlFlow::Break(ControlFlow::Break(b)),
        }
    }
}

/// An adapter for implementing non-try methods via the `Try` implementation.
///
/// Conceptually the same as `Result<T, !>`, but requiring less work in trait
/// solving and inhabited-ness checking and such, by being an obvious newtype
/// and not having `From` bounds lying around.
#[repr(transparent)]
pub(super) struct NeverShortCircuit<T>(pub(super) T);

/// Companion `Residual` type for `NeverShortCircuit<T>`. Represents an error that
/// can never occur. Because this enum has no variants, a value of this type can never exist.
///
/// See https://doc.rust-lang.org/nomicon/exotic-sizes.html#empty-types for more information.
pub(super) enum NeverShortCircuitResidual {}

impl<T> Try for NeverShortCircuit<T> {
    type Output = T;
    type Residual = NeverShortCircuitResidual;
    #[inline]
    fn from_residual(residual: Self::Residual) -> Self {
        match residual {}
    }
    #[inline]
    fn branch(self) -> ControlFlow<NeverShortCircuitResidual, T> {
        ControlFlow::Continue(self.0)
    }

    #[inline]
    fn from_output(x: T) -> Self {
        NeverShortCircuit(x)
    }
}

impl<T> Residual<T> for Option<Infallible> {
    type TryType = Option<T>;
}

impl<T, E> Residual<T> for Result<Infallible, E> {
    type TryType = Result<T, E>;
}

impl<B, C> Residual<C> for ControlFlow<B, Infallible> {
    type TryType = ControlFlow<B, C>;
}

impl<T> Residual<T> for NeverShortCircuitResidual {
    type TryType = NeverShortCircuit<T>;
}
