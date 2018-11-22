(* A category is very much like a graph. It has vertices
   named objects and vertices named arrows. Each arrow goes
   from an object to an object (possibly the same!). *)
Record Cat (obj: Type) (arr: obj -> obj -> Type) : Type :=
  MkCat {
    (* For each object, there is an arrow called `id` which
       goes from the object to itself. *)
    id: forall {o: obj}, arr o o;

    (* Given an arrow `f` from object `a` to `b` and an arrow
       `g` from `b` to `c`. We can compose these arrow. The
       result is an arrow from `a` to `c`. *)
    compose: forall {a b c: obj}, arr a b -> arr b c -> arr a c;
              
    (* Here comes some properties of `id` and `compose` *)

    (* For any arrow `f`, compose id f = f *)
    neutralLeft:   forall {a b: obj} (f: arr a b), compose id f = f;

    (* For any arrow `f`, compose f id = f  *)
    neutralRight:  forall {a b: obj} (f: arr a b), compose f id = f;

    (* For any arrows `f`, `g` and `h`,
        composing f with g, and then the result with h
       gives exatctly the same result as
        composing f with the result of the composition of g and h

       Which means, like string concatenation than we can commpose
       the way we preserve the order of each element in the sequence. *)    
    associativity: forall {a b c d: obj} (f: arr a b) (g: arr b c) (h: arr c d),
                     compose (compose f g) h = compose f (compose g h);
  }.

Arguments MkCat {_} {_}.

(* `LE n m` encode the property that `n ≤ m`
    i.e. `n` is less or equal to `m` *)  
Inductive LE : nat -> nat -> Prop :=
    LERefl: forall {o: nat}, LE o o
  | LENext: forall {a b: nat}, LE a b -> LE a (S b)
.

(* Taking naturals as objects and `LE` as arrows,
   this actually forms a category! *)
Definition natPoset: Cat nat LE := ???
.