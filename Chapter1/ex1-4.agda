module ex1-4 where

-- | Propositional Equality
infix 4 _==_
data _==_ {a} {A : Set a} (x : A) : A -> Set a where
  refl : x == x
{-# BUILTIN EQUALITY _==_ #-}

sym : {A : Set} -> {x : A} -> {y : A} -> (x == y) -> y == x
sym {A} {x} {y} refl = refl

trans : {A : Set} -> {x : A} -> {y : A} -> {z : A} -> (x == y) -> (y == z) -> (x == z)
trans {A} {x} {y} {z} refl refl = refl

cong : {A B : Set} -> (f : A -> B) -> {x : A} -> {y : A}
       -> (x == y) -> (f x == f y)
cong f {x} {y} refl = refl

-- | Equational reasoning constructions for propositional equality
infix  1 begin_
infixr 2 _==⟨⟩_ _==⟨_⟩_
infix  3 _∎

-- | Open an equational reasoning block.
begin_ : {A : Set} -> {x y : A} → x == y → x == y
begin x==y  =  x==y

-- | Implicit reflexivity step
_==⟨⟩_ : {A : Set} -> (x : A) {y : A} → x == y → x == y
x ==⟨⟩ x==y  =  x==y

-- | Step with explicit witness
_==⟨_⟩_ : {A : Set} -> (x : A) {y z : A} → x == y → y == z → x == z
x ==⟨ x==y ⟩ y==z  =  trans x==y y==z

-- | QED
_∎ : {A : Set} -> (x : A) → x == x
x ∎  =  refl

-- | Natural numbers
data Nat : Set where
  z : Nat
  suc : Nat -> Nat

-- | Induction on Naturals
indNat : (C : Nat -> Set) -> C z -> ((n : Nat) -> C n -> C (suc n)) -> (n : Nat) -> C n
indNat C c0 cind z = c0
indNat C c0 cind (suc n) = cind n ((indNat C c0 cind n))

-- | Products
infix 4 _×_
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

-- | The recursor on products (aka uncurry)
rec× : {A B C : Set} -> (A -> B -> C) -> (A × B -> C)
rec× f (x , y) = f x y

-- | Equality on pairs
infix 4 _=×=_
_=×=_ :  {A B : Set} -> {a c : A} -> {b d : B}
        -> (a == c) -> (b == d) -> ((a , b) == (c , d))
_=×=_ refl refl = refl

-- | Deconstruct the equality of a pair.
destroy-=×= : {A B : Set} -> {a c : A}  -> {b d : B}
                -> ((a , b) == (c , d)) -> ((a == c) × (b == d))
destroy-=×= refl = (refl , refl)

-- | Iteration from the exercise.
iter : (C : Set) -> C -> (C -> C) -> Nat -> C
iter C c0 cs z = c0
iter C c0 cs (suc n) = cs (iter C c0 cs n)

-- | Auxiliary recursor, which remembers its natural number
rec' : (C : Set) -> C -> (Nat × C -> C) -> Nat -> (Nat × C)
rec' C c0 cs = iter (Nat × C) (z , c0) (\{ (n , c) -> (suc n , cs (n , c))})

-- | Recursor on natural numbers, defined using rec'
rec : (C : Set) -> C -> (Nat -> C -> C) -> Nat -> C
rec C c0 cs n = _×_.snd (rec' C c0 (rec× cs) n)


-------------------------------------------------------------------------------
-- Proofs for rec'

-- | Data type witnessing the equations for rec'
-- rec C c0 cs 0 = (0,c0)
-- rec C c0 cs (n + 1) = cs (rec' C c0 cs n)
data Eq' (C : Set) (c0 : C) (cs : Nat × C -> C) : Nat -> Set where
  eqz' : (rec' C c0 cs z == (z , c0)) -> Eq' C c0 cs z
  eqsuc' : {n : Nat}
         -> (rec' C c0 cs (suc n) == (suc n , cs (rec' C c0 cs n)))
         -> Eq' C c0 cs (suc n)

-- | Base case
p0 : {C : Set} -> {c0 : C} -> {cs : Nat × C -> C} -> rec' C c0 cs z == (z , c0)
p0 {C} {c0} {cs} = refl

-- | Induction case
pn : {C : Set} -> {c0 : C} -> {cs : Nat × C -> C} -> {n : Nat}
   -> (rec' C c0 cs (suc n) == (suc n , cs (rec' C c0 cs n)))
   -> (rec' C c0 cs (suc (suc n)) == ((suc (suc n) , cs (rec' C c0 cs (suc n)))))
pn {C} {c0} {cs} {n} ih =
  begin
     rec' C c0 cs (suc (suc n))
  ==⟨ refl ⟩
    iter (Nat × C) (z , c0) f (suc (suc n))
  ==⟨ refl ⟩
    f (iter (Nat × C) (z , c0) f (suc n))
  ==⟨ cong f refl ⟩
    f (rec' C c0 cs (suc n))
  ==⟨ cong f ih ⟩
    f (suc n , cs (rec' C c0 cs n))
  ==⟨ refl ⟩
    (suc (suc n) , cs (suc n , cs (rec' C c0 cs n)))
  ==⟨ refl =×= (cong cs (sym ih)) ⟩
     (suc (suc n), cs (rec' C c0 cs (suc n)))
  ∎
    where
    f : Nat × C -> (Nat × C)
    f (n , c) = (suc n , cs (n , c))
--pn ih = (cong suc (cong _×_.fst ih)) =×= refl

-- | Witness for Eq' C c0 cs n
eq' : (C : Set) -> (c0 : C) -> (cs : Nat × C -> C) -> (n : Nat) -> Eq' C c0 cs n
eq' C c0 cs = indNat (Eq' C c0 cs) basis induction where
  basis = eqz' (p0 {C} {c0} {cs})
  induction : (n : Nat) -> Eq' C c0 cs n -> Eq' C c0 cs (suc n)
  induction z (eqz' x) = eqsuc' refl
  induction (suc n) (eqsuc' ih) = eqsuc' (pn ih)

-------------------------------------------------------------------------------
-- Proofs for rec

l1 :  (C : Set) -> (c0 : C) -> (cs : Nat × C -> C) -> (n : Nat)
   -> (_×_.fst (rec' C c0 cs n) == n)
l1 C c0 cs z with eq' C c0 cs z
... | eqz' e = cong _×_.fst e
l1 C c0 cs (suc n) with eq' C c0 cs (suc n)
... | eqsuc' e = cong _×_.fst e

-- | Important lemma
l3 : (C : Set) -> (c0 : C) -> (cs : Nat -> C -> C) -> (n : Nat)
   -> (rec' C c0 (rec× cs) n == (n , rec C c0 cs n))
l3 C c0 cs n =
  begin
    rec' C c0 (rec× cs) n
  ==⟨ (l1 C c0 (rec× cs) n) =×= refl ⟩
    (n , rec C c0 cs n)
  ∎

l4 : (C : Set) -> (c0 : C) -> (cs : Nat -> C -> C)
   -> (rec C c0 cs z == c0)
l4 C c0 cs =
  begin
    rec C c0 cs z
  ==⟨ refl ⟩
    _×_.snd (rec' C c0 (rec× cs) z)
  ==⟨ refl ⟩
    c0
  ∎
--_×_.snd (destroy-=×= (l3 C c0 cs z))

l5 : (C : Set) -> (c0 : C) -> (cs : Nat -> C -> C) -> (n : Nat)
     -> ((suc n , rec× cs (rec' C c0 (rec× cs) n)) == (suc n , rec C c0 cs (suc n)))
l5 C c0 cs n with eq' C c0 (rec× cs) (suc n)
... | eqsuc' e =
  begin
    (suc n , rec× cs (rec' C c0 (rec× cs) n))
  ==⟨ sym e ⟩
    rec' C c0 (rec× cs) (suc n)
  ==⟨ l3 C c0 cs (suc n) ⟩
    (suc n , rec C c0 cs (suc n))
  ∎
-- trans (sym e) (l3 C c0 cs ((suc n)))

l6 : (C : Set) -> (c0 : C) -> (cs : Nat -> C -> C) -> (n : Nat)
   -> (rec× cs (rec' C c0 (rec× cs) n) == rec C c0 cs (suc n))
l6 C c0 cs n =
  begin
    rec× cs (rec' C c0 (rec× cs) n)
  ==⟨ refl ⟩
    _×_.snd (suc n , rec× cs (rec' C c0 (rec× cs) n))
  ==⟨ cong _×_.snd (l5 C c0 cs n) ⟩
    _×_.snd ((suc n , rec C c0 cs (suc n) ))
  ==⟨ refl ⟩
    rec C c0 cs (suc n)
  ∎
-- _×_.snd (destroy-=×= (l5 C c0 cs n))

l7 : (C : Set) -> (c0 : C) -> (cs : Nat -> C -> C) -> (n : Nat)
   -> (rec× cs (rec' C c0 (rec× cs) n) == rec× cs (n , rec C c0 cs n))
l7 C c0 cs n =
  begin
    rec× cs (rec' C c0 (rec× cs) n)
  ==⟨ cong (rec× cs) (l3 C c0 cs n) ⟩
    rec× cs (n , rec C c0 cs n)
  ∎
-- cong (rec× cs) (l3 C c0 cs n)

l8 : (C : Set) -> (c0 : C) -> (cs : Nat -> C -> C) -> (n : Nat)
   -> (rec× cs (n , rec C c0 cs n) == cs n (rec C c0 cs n))
l8 C c0 cs n = refl

-- | Important lemma
l9 : (C : Set) -> (c0 : C) -> (cs : Nat -> C -> C) -> (n : Nat)
   -> (cs n (rec C c0 cs n) == rec C c0 cs (suc n))
l9 C c0 cs n with eq' C c0 (rec× cs) (suc n)
... | eqsuc' e =
  begin
    cs n (rec C c0 cs n)
  ==⟨ refl ⟩
    rec× cs (n , rec C c0 cs n)
  ==⟨ cong (rec× cs) (sym (l3 C c0 cs n)) ⟩
    rec× cs (rec' C c0 (rec× cs) n)
  ==⟨ refl ⟩
     _×_.snd (suc n , rec× cs (rec' C c0 (rec× cs) n))
  ==⟨ cong _×_.snd (sym e) ⟩
    _×_.snd (rec' C c0 (rec× cs) (suc n))
  ==⟨ refl ⟩
    rec C c0 cs (suc n)
  ∎
--  trans (sym (l8 C c0 cs n)) (trans (sym (l7 C c0 cs n)) (l6 C c0 cs n))

-- | Datatype witnessing equalities for rec:
-- rec C c0 cs 0 = c0
-- rec C c0 cs (n + 1) = cs n (rec C c0 cs n)
data Eq (C : Set) (c0 : C) (cs : Nat -> C -> C) : Nat -> Set where
  eqz : (rec C c0 cs z == c0) -> Eq C c0 cs z
  eqsuc : {n : Nat} -> (rec C c0 cs (suc n) == cs n (rec C c0 cs n)) -> Eq C c0 cs (suc n)

-- Theorem: rec satisfies the recursor's equations.
eq : (C : Set) -> (c0 : C) -> (cs : Nat -> C -> C) -> (n : Nat) -> Eq C c0 cs n
eq C c0 cs z = eqz (l4 C c0 cs)
eq C c0 cs (suc n) = eqsuc (sym (l9 C c0 cs n))
