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

Definition idLE: forall {o: nat}, LE o o := @LERefl.

Fixpoint composeLE {a b c: nat} (f: LE a b) (g: LE b c) {struct g}: LE a c :=
  match g in LE x y return (LE a x -> LE a y) with
    | LERefl    => fun f0: LE a _ => f0
    | LENext hr => fun f0: LE a _ => LENext (composeLE f0 hr)
  end f
.

Definition neutralRightLE {a b: nat} (f: LE a b): composeLE f idLE = f := eq_refl.

Definition leibniz {a b: Type} {x y: a} (p: x = y) (f: a -> b): f x = f y :=
  match p with
    | eq_refl => eq_refl
  end
.

Fixpoint neutralLeftLE {a b: nat} (f: LE a b): composeLE idLE f = f :=
  match f with
    | LERefl   => eq_refl
    | LENext h => let hr := neutralLeftLE h
                  in leibniz hr LENext
  end
.

Fixpoint associativityLE
    {a b c d: nat} (f: LE a b) (g: LE b c) (h: LE c d) :
    composeLE (composeLE f g) h = composeLE f (composeLE g h)
  :=
  match h as h' in LE c' d'
          return  (forall {a' b': nat} (f': LE a' b') (g': LE b' c'),
                     composeLE (composeLE f' g') h' = composeLE f' (composeLE g' h')
                  )
          with
    | LERefl => fun {a' b': nat} (f': LE a' b') (g': LE b' _) => eq_refl
    | LENext p => fun {a' b': nat} (f': LE a' b') (g': LE b' _) =>
                    let HR := associativityLE f' g' p
                    in leibniz HR LENext
  end a b f g
.

(* Taking naturals as objects and `LE` as arrows,
   this actually forms a category! *)
Definition natPoset: Cat nat LE :=
  MkCat (@LERefl)
        (@composeLE)
        (@neutralLeftLE)
        (@neutralRightLE)
        (@associativityLE)
.