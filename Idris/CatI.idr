module CatI

%default total

{- A category is very much like a graph. It has vertices
   named objects and vertices named arrows. Each arrow goes
   from an object to an object (possibly the same!). -}
interface Cat (obj: Type) (arr: obj -> obj -> Type) where
  {- For each object, there is an arrow called `id` which
    goes from the object to itself. -}
  id: {o: obj} -> arr o o

  {- Given an arrow `f` from object `a` to `b` and an arrow
      `g` from `b` to `c`. We can compose these arrow. The
      result is an arrow from `a` to `c`. -}
  compose: {a, b, c: obj} -> arr a b -> arr b c -> arr a c

  -- Here comes some properties of `id` and `compose`

  {- For any arrow `f`, compose id f = f -}
  neutralLeft:  {a, b: obj} -> (f: arr a b) -> compose id f = f

  {- For any arrow `f`, compose f id = f  -}
  neutralRight: {a, b: obj} -> (f: arr a b) -> compose f id = f

  {- For any arrows `f`, `g` and `h`,
      composing f with g, and then the result with h
      gives exatctly the same result as
      composing f with the result of the composition of g and h

      Which means, like string concatenation than we can commpose
      the way we preserve the order of each element in the sequence.-}
  associativity: {a, b, c, d: obj} ->
                  (f: arr a b) -> (g: arr b c) -> (h: arr c d) ->
                  compose f (compose g h) = compose (compose f g) h

{- `LE n m` encode the property that `n ≤ m`
    i.e. `n` is less or equal to `m` -}
data LE : Nat -> Nat -> Type where
  LERefl : {o: Nat} -> LE o o
  LENext : {a, b: Nat} -> LE a b -> LE a (S b)

{- Taking naturals as objects and `LE` as arrows,
   this actually forms a category! -}
[natPoset] Cat Nat LE where
  ???