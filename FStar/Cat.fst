module Cat

(* A category is very much like a graph. It has vertices
   named objects and vertices named arrows. Each arrow goes
   from an object to an object (possibly the same!). *)
noeq type cat (obj:Type) (arr: obj -> obj -> Type): Type =
  | MkCat: (* For each object, there is an arrow called `id` which
              goes from the object to itself. *)
           id:(#o:obj -> arr o o) ->

           (* Given an arrow `f` from object `a` to `b` and an arrow
              `g` from `b` to `c`. We can compose these arrow. The
              result is an arrow from `a` to `c`. *)
           compose:(#a:obj -> #b:obj -> #c:obj ->
                    f:arr a b -> g: arr b c ->
                    arr a c) ->

           // For any arrow `f`, compose id f = f
           neutralLeft:(#a:obj -> #b:obj -> f:arr a b -> Lemma (compose id f == f)) ->

           // For any arrow `f`, compose f id = f
           neutralRight:(#a:obj -> #b:obj -> f:arr a b -> Lemma (compose f id == f)) ->

           (* For any arrows `f`, `g` and `h`,
               composing f with g, and then the result with h
              gives exatctly the same result as
               composing f with the result of the composition of g and h

              Which means, like string concatenation than we can commpose
              the way we preserve the order of each element in the sequence. *)
           associativity:(#a:obj -> #b:obj -> #c:obj -> #d:obj ->
                          f:arr a b -> g:arr b c -> h:arr c d ->
                          Lemma (compose f (compose g h) == compose (compose f g) h)
                         ) ->
           cat obj arr

(* `LE n m` encode the property that `n ≤ m`
   i.e. `n` is less or equal to `m` *)
type le : nat -> nat -> Type =
  | LERefl : #n:nat -> le n n
  | LENext : #n:nat -> #m:nat -> le n m -> le n (m + 1)

val id': #n:nat -> le n n
let id' = LERefl

val compose': #a:nat -> #b:nat -> #c:nat ->le a b -> le b c -> le a c
let rec compose' #_ #_ #_ f g =
  match g with
  | LERefl   -> f
  | LENext h -> LENext (compose' f h)


val neutralLeft': #a:nat -> #b:nat -> f:le a b -> Lemma (compose' id' f == f)
let rec neutralLeft' #_ #_ f =
  match f with
  | LERefl -> ()
  | LENext h -> neutralLeft' h

val neutralRight': #a:nat -> #b:nat -> f:le a b -> Lemma (compose' f id' == f)
let neutralRight' #_ #_ f = ()

val associativity': #a:nat -> #b:nat -> #c:nat -> #d:nat ->
                    f:le a b -> g:le b c -> h:le c d ->
                    Lemma (compose' f (compose' g h) == compose' (compose' f g) h)
let rec associativity' #_ #_ #_ #_ f g h =
  match h with
  | LERefl -> ()
  | LENext x -> associativity' f g x


(* Taking naturals as objects and `LE` as arrows,
   this actually forms a category! *)
val natPoset : cat nat le
let natPoset = MkCat id'
                     compose'
                     neutralLeft'
                     neutralRight'
                     associativity'
