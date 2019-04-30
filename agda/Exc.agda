module Exc where

--                                                   \sqcup
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
--                          \u+  inj\_1 inj\_2
open import Data.Sum using (_⊎_; inj₁; inj₂)

-- Natural numbers

data Nat
  : Set where
  O : Nat
  S : (n : Nat) → Nat

-- \bN
ℕ = Nat

{-# BUILTIN NATURAL Nat #-}

recNat : {i : Level} →
  (C : Set i) → C → (ℕ → C → C) → ℕ → C
recNat C c₀ cₛ O = c₀
recNat C c₀ cₛ (S n) = cₛ n (recNat C c₀ cₛ n)

indNat : {i : Level} →
  (C : ℕ → Set i) → C O → ((n : ℕ) → C n → C (S n)) → (n : ℕ) → C n
indNat C c₀ cₛ O = c₀
indNat C c₀ cₛ (S n) = cₛ n (indNat C c₀ cₛ n)

-- Booleans

data Bool
  : Set where
  false : Bool
  true : Bool

-- \bB
𝔹 = Bool

-- Product Types

record Prod {i j : Level}
  (A : Set i) (B : Set j) : Set (i ⊔ j) where
  constructor _,_
  field
    pr₁ : A
    pr₂ : B

-- \x
_×_ = Prod

recProd : {i j k : Level} {A : Set i} {B : Set j} →
  (C : Set k) → (A → B → C) → A × B → C
recProd C g (a , b) = g a b

-- Dependent Pair Types

record Sigma {i j} (A : Set i) (B : A → Set j) : Set (i ⊔ j) where
  constructor _,_
  field
    -- pr\_1
    pr₁ : A
    -- pr\_2
    pr₂ : B (pr₁)

-- \Sigma
Σ = Sigma

recSigma : {i j k : Level} {A : Set i} {B : A → Set j} →
  (C : Set k) → ((x : A) → B x → C) → Σ A B → C
recSigma C g (a , b) = g a b

indSigma : {i j k : Level} {A : Set i} {B : A → Set j} →
  (C : Σ A B → Set k) → ((a : A) → (b : B a) → C (a , b)) → (p : Σ A B) → C p
indSigma C g (a , b) = g a b

-- CoProduct Types

recCoProd : {i j k : Level} {A : Set i} {B : Set j} →
  (C : Set k) → (A → C) → (B → C) → A ⊎ B → C
recCoProd C g₀ g₁ (inj₁ a) = g₀ a
recCoProd C g₀ g₁ (inj₂ b) = g₁ b

indCoProd : {i j k : Level} {A : Set i} {B : Set j} →
  (C : A ⊎ B → Set k) → ((a : A) → C (inj₁ a)) → ((b : B) → C (inj₂ b)) → (x : A ⊎ B) → C x
indCoProd C g₀ g₁ (inj₁ a) = g₀ a
indCoProd C g₀ g₁ (inj₂ b) = g₁ b

-- Unit Type

record Unit : Set where
  constructor unit

recUnit : {i : Level} →
  (C : Set i) → C → Unit → C
recUnit C c unit = c

-- Empty Type

data Void : Set where

-- \bot
⊥ = Void

not : ∀ {i} (A : Set i) → Set i
not A = A → ⊥

-- \lnot
¬ = not

-- Equality

data Eq {i : Level} {A : Set i}
  : (a b : A) -> Set i where
  refl : {a : A} → Eq a a

-- \==
_≡_ = Eq

-- indiscernibility of identicals
indisc : {i j : Level} {A : Set i} →
  (C : A → Set j) →
  (x : A) → (y : A) → (p : x ≡ y) → C x → C y
indisc _ _ _ refl cx = cx

example1 : 2 ≡ 2
example1 = indisc (λ a → a ≡ 2) (S 1) 2 refl refl

-- path induction
pathind : {i j : Level} {A : Set i} →
  (C : (x : A) → (y : A) → x ≡ y → Set j) → (c : (x : A) → C x x refl) →
  (x : A) → (y : A) → (p : x ≡ y) → C x y p
pathind _ c x _ refl = c x

-- 1.9

Fin1 : ℕ → Set
Fin1 O = ⊥
Fin1 (S n) = Unit ⊎ (Fin1 n)

Fin2 : ℕ → Set
Fin2 = recNat Set ⊥ (λ n r → Unit ⊎ r)

-- 1.15

indisc2 : {i j : Level} {A : Set i} →
  (C : A → Set j) →
  (x : A) → (y : A) → (p : x ≡ y) → C x → C y
indisc2 C x _ refl cx = pathind (λ _ _ refl → C x) (λ _ → cx) x x refl
