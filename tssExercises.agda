module tssExercises where

-- exercise 1 - Natural numbers: define Nat, _+_, mult and prove _+_ is associative.

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

_+N_ : (n m : Nat) -> Nat
zero +N m = m
suc n +N m = suc (n +N m)

_*N_ : (n m : Nat) -> Nat
zero *N m = zero
suc n *N m = m +N (n *N m)

data _==_ {A : Set}: A -> A -> Set where
  refl : (x : A) -> x == x

_=$=_ : {A B : Set} {x x' : A}{f f' : A -> B} -> f == f' -> x == x' -> f x == f' x'
(refl f )=$= (refl x) = refl (f x)


assoc : (x y z : Nat) -> (x +N (y +N z)) == ((x +N y) +N z)
assoc zero y z = refl (y +N z)
assoc (suc x) y z =  (refl suc) =$= (assoc x y z)

-- exercise 2 - Vectors: define fixed length vectors, repeat, application _<*>_, map and zip

data Vec (A : Set) : Nat -> Set where
  []V : Vec A zero
  _::V_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

rep : {A : Set}{n : Nat} -> A -> Vec A n
rep {n = zero} a = []V
rep {n = suc n} a = a ::V (rep {_} {n} a)

_<*>V_ : {A B : Set} {n : Nat} -> Vec (A -> B) n -> Vec A n -> Vec B n
fs <*>V []V = []V
(f1 ::V fs) <*>V (x ::V xs) = f1 x ::V (fs <*>V xs)

mapV : {A B : Set}{n : Nat} -> (A -> B) -> Vec A n -> Vec B n
mapV f xs = rep f <*>V xs

zip : {A B C : Set}{n : Nat} -> (A -> B -> C) -> Vec A n -> Vec B n -> Vec C n
zip f as bs = (rep f <*>V as) <*>V bs

-- exerise 3 - Finite Sets: define representatives for Nat-indexed finite sets, define an isomorphism between (Fin n -> A) and Vec A n

data Zero : Set where

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc : {n : Nat} -> Fin n -> Fin (suc n)

empty : Fin zero -> Zero
empty ()

_!_ : {A : Set}{n : Nat} -> Vec A n -> Fin n -> A
[]V ! ()
(a ::V as) ! fzero = a
(a ::V as) ! fsuc k  = as ! k

{-pred : {n : Nat} -> Fin n -> Fin n
pred fzero = fzero
pred (fsuc fzero) = fzero
pred (fsuc (fsuc k)) = fsuc (pred (fsuc k))

res : {A : Set} {n : Nat} -> (Fin (suc n) -> A) -> (Fin n -> A)
res f x = f (pred (fsuc (x))) -}

_<<<_ : {A B C : Set} -> (B -> C) -> (A -> B) -> (A -> C)
(g <<< f) a = g (f a)

tabulate : {A : Set} {n : Nat} -> (Fin n -> A) -> Vec A n
tabulate {n = zero} f = []V
tabulate {n = suc k} f = f fzero ::V tabulate  (f <<< fsuc)

-- exercise 4 - Prediates over Lists : define lists, map, append, Some and All for predicates over lists 

data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

mapL : {A B : Set} -> (A -> B) -> List A -> List B
mapL f [] = []
mapL f (a :: as) = (f a) :: mapL f as

_++_ : {A : Set} -> List A -> List A -> List A
[] ++ as2 = as2
(x :: as1) ++ as2 = x :: (as1 ++ as2)

data All {A : Set}(P : A -> Set) : List A -> Set where
  vacA : (All P [])
  sucA : {a : A}{as : List A} -> P a -> All P as -> All P (a :: as)

data Some {A : Set}(P : A -> Set) : List A -> Set where
  headS : {a : A} {as : List A} -> P a -> Some P (a :: as)
  tailS : {a : A} {as : List A} -> Some P as -> Some P (a :: as)


pullbackFamily : {A B : Set} -> (A -> Set) -> (B -> A) -> (B -> Set)
pullbackFamily P f b = P (f b)

mapFact : {A B : Set} {vs : List B} {P : A -> Set}{f : B -> A} -> All P (mapL f vs) -> All (pullbackFamily P f) vs
mapFact {vs = []} vacA = vacA
mapFact {vs = x :: vs} (sucA pf1 pfs) = sucA pf1 (mapFact pfs)

left++Fact : {A : Set} {as bs : List A} {P : A -> Set} -> Some P as -> Some P (as ++ bs)
left++Fact (headS x) = headS x
left++Fact {as = a :: as'} (tailS pf) = tailS (left++Fact pf)

right++Fact : {A : Set} {as bs : List A} {P : A -> Set} -> Some P bs -> Some P (as ++ bs)
right++Fact {bs = []} ()
right++Fact {as = []} {b :: bs'} pf = pf
right++Fact {as = a :: as'} {bs = b :: bs' } pf = tailS (right++Fact {_} {as'} pf)

_∈_ : {A : Set} -> A -> List A -> Set
a ∈ as = Some (\ b ->   a == b) as

record One : Set where
<> : One
<> = record {}

NatL = List One

zeroL : NatL
zeroL = []

sucL : NatL -> NatL
sucL n = <> :: n


Vec' : (A : Set) -> NatL -> Set
Vec' A nl = All (\_ -> A) nl

Fin' : NatL -> Set
Fin' nl = Some (\_ -> One) nl

data Sg (A : Set)(B : A -> Set) : Set where
  _,_ : (x : A) -> B x -> Sg A B

_x_ : (A B : Set) -> Set
A x B = Sg A (\_ -> B)

_!int_ : {A : Set}{xs : List A}{P : A -> Set}{Q : A -> Set} ->
       All P xs -> Some Q xs -> Sg A (\z -> (P z) x (Q z))
sucA p1 allPs !int headS q1 = _ , (p1 , q1)
sucA {as = []} p1 allPs !int tailS ()
sucA {as = x :: as} p1 allPs !int tailS someQ = allPs !int someQ


¬_ : Set -> Set
¬ P = P -> Zero


data _+_ (A B : Set) : Set where
  inl : A -> A + B
  inr : B -> A + B

data Bool : Set where
  false : Bool
  true : Bool

data IsTrue : Bool -> Set where
 isTrue : (IsTrue true)

Holds : {A : Set} -> (A -> Bool) -> A -> Set
Holds p x = IsTrue (p x)


decide : {A : Set} (p : A -> Bool)(x : A) -> ( (Holds p x) + (¬ (Holds p x)))
decide p x with p x
decide p x | false = inr (λ ())
decide p x | true = inl isTrue

all : {A : Set}(p : A -> Bool)(xs : List A) ->
      All (Holds p) xs + Some (\ x -> ¬ (Holds p x)) xs
all p [] = inl vacA
all p (x :: xs') with (decide p x)
all p (x :: xs') | inl hld with all p xs'
all p (x :: xs') | inl hld | inl hlds = inl (sucA hld hlds)
all p (x :: xs') | inl hld | inr nhlds = inr (tailS nhlds)
all p (x :: xs') | inr nhold = inr (headS nhold)

