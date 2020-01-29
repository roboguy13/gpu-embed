# Representing of pattern matches

## Generic-based

### GPUExp, GPURep and GPURepTy

Within the `GPUExp` type, we have the following constructor:

    data GPUExp t where
      CaseExp :: (GPURep a) => GPUExp a -> SumMatch (GPURepTy a) t -> GPUExp t
      ...

The first argument (the `GPUExp a`) of the `CaseExp` constructor is the
expression being scrutinized by the `case` expression; that is, it is the `e` in
the following:

    case e of ...

The `GPURepTy a` type is actually a type family associated to the `GPURep` type
class. This type family is a type level function that will take in any
non-recursive type with a `Generic` instance and give you back an isomorphic
type expressed only in terms of `(,)`, `Either` and base types (like `Int`). We
will call this the "canonical form" of that type.

So, for example, if we have

    data Example5 = A1 Float Float | A2 Int deriving (Generic)

    instance GPURep Example5

then `GPURepTy Example5` = `Either (Float, Float) Int` and we say the canonical
form of `Example5` is `Either (Float, Float) Int`.

Also note that we did not have to provide a body for the `GPURep` instance. The
implementation is automatically generated using `Example5`'s `Generic` instance.

### SumMatch

This brings us to `SumMatch`. Recall the definition of the `CaseExp`
constructor:

    CaseExp :: (GPURep a) => GPUExp a -> SumMatch (GPURepTy a) t -> GPUExp t

Here, `SumMatch` takes in the canonical form of `a` and the type variable `t`
(note that this `t` appears again in the result type of the `CaseExp`
constructor).

The `SumMatch` type has the following definition:

    data SumMatch s t where
      SumMatch ::
        (GPURep a, GPURep b, GPURepTy b ~ b)
            => ProdMatch a r -> SumMatch b r -> SumMatch (Either a b) r

      EmptyMatch :: SumMatch () r

      OneSumMatch :: (GPURep a, GPURep b, GPURepTy a ~ a) => ProdMatch a b -> SumMatch a b

The `EmptyMatch` constructor represents an empty collection of match
alternatives (something like `case e of {}`). The `OneSumMatch` constructor
represents exactly one match (something like `case e of { C a b c ... -> ...
}`).

The more complicated case is the `SumMatch` constructor. It is similar to the
`(:)` constructor, except that it is, to an extent, heterogenous in its
elements.

In the type `SumMatch s t`, the `s` is the canonical form of the type being
matched on and `t` is the type of the result of the match. For instance, in
`case e of C -> x`, the `s` type would be the canonical form of the type of `e`
and `t` type would be the type of `x`.

Before giving an example, we must at least partially describe the `ProdMatch`
type. For the purposes of this first example, we will focus on one of its
constructors right now:

    data ProdMatch s t where
      ...
      OneProdMatch :: (GPURep a) => (GPUExp a -> GPUExp r) -> ProdMatch a r
      ...

This represents a match on a product type which has exactly one field: `C x -> ...`.

To put these things together in an example, an example of a `SumMatch` value with type
`SumMatch (Either Int (Either Char Bool)) Int` is:

    exampleSM :: SumMatch (Either Int (Either Bool Float)) Float
    exampleSM =
      SumMatch (OneProdMatch (\int -> FromIntegral int))
               (SumMatch (OneProdMatch (\bool -> FromIntegral (FromEnum bool)))
                         (OneSumMatch (OneProdMatch (\float -> Sub float (Lit 1.0)))))


If we combine this with the `CaseExp` constructor from the `GPUExp` type:

    caseExpExample :: GPUExp Float
    caseExpExample = CaseExp x exampleSM

This expression represents the `case` match:

    case x of
      Left int -> fromIntegral int
      Right (Left bool) -> fromIntegral (fromEnum bool)
      Right (Right float) -> float - 1.0

as well as an equivalent `case` match on any type that is structurally
identitical to `Either Int (Either Char Bool)` (that is, any type whose
canonical form is `Either Int (Either Char Bool)`).

### The rest of ProdMatch

A value of type `ProdMatch s t` corresponds to a match on a value of a product
type (that is, a type which is isomorphic to a tuple).



