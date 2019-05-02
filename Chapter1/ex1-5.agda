-- | Booleans
data Bool : Set where
  true : Bool
  false : Bool

-- | Induction on booleans
indBool : (C : Bool -> Set) -> C true -> C false -> (b : Bool) -> C b
indBool C ct cf true = ct
indBool C ct cf false = cf

-- | Sigma types
data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (a : A) → (b : B a) → Σ A B

infixr 4 _,_

-- | Sum types in terms of sigma and bool
_+_ : Set -> Set -> Set
A + B = Σ Bool (\{ true -> A ; false -> B })

-- | Left injector
inl : {A B : Set} -> A -> A + B
inl x = (true , x)

-- | Right injector
inr : {A B : Set} -> B -> A + B
inr x = (false , x)

-- | Induction on sum types
ind+ : {A B : Set} -> (C : (A + B) -> Set)
     -> ((a : A) -> C (inl a))
     -> ((b : B) -> C (inr b))
     -> (s : (A + B))
     -> C s
ind+ C g0 g1 (true , c) = g0 c
ind+ C g0 g1 (false , c) = g1 c

-- | Propositional equality
infix 4 _==_
data _==_ {a} {A : Set a} (x : A) : A -> Set a where
  refl : x == x
{-# BUILTIN EQUALITY _==_ #-}

-------------------------------------------------------------------------------
-- Proofs

-- | ind+ satisfies ind+ C g0 g1 (inl a) = g0 a
p0 : {A B : Set} -> (C : (A + B) -> Set)
   -> (g0 : (a : A) -> C (inl a))
   -> (g1 : (b : B) -> C (inr b))
   -> (a : A)
   -> (ind+ C g0 g1 (inl a) == g0 a)
p0 C g0 g1 a = refl

-- | ind+ satisfies ind+ C g0 g1 (inr b) = g1 a
p1 : {A B : Set} -> (C : (A + B) -> Set)
   -> (g0 : (a : A) -> C (inl a))
   -> (g1 : (b : B) -> C (inr b))
   -> (b : B)
   -> (ind+ C g0 g1 (inr b) == g1 b)
p1 C g0 g1 b = refl
