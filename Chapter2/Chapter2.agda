-- Formalisations for the HoTT book, Chapter 2.

-- | Products
infix 4 _×_
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

data Σ (A : Set) (P : A -> Set) : Set where
  _,_ : (x : A) -> P x -> Σ A P

-- | Propositional Equality
infix 4 _==_
data _==_ {a} {A : Set a} (x : A) : A -> Set a where
  refl : x == x
{-# BUILTIN EQUALITY _==_ #-}

ind== : {A : Set}
      -> (C : (x y : A) -> (p : x == y) -> Set)
      -> (c : (x : A) -> C x x refl)
      -> (x : A) -> (y : A)
      -> (p : x == y)
      -> C x y p
ind== C crefl x .x refl = crefl x

-- symmetry (inverse)
inv : {A : Set} -> {x : A} -> {y : A} -> (x == y) -> y == x
inv {A} {x} {y} p = ind== C (\x -> refl) x y p where
  C : (x y : A) -> (p : x == y) -> Set
  C x y p = (y == x)

-- transitivity (composition)
_∙_ : {A : Set} -> {x : A} -> {y : A} -> {z : A} -> (x == y) -> (y == z) -> (x == z)
(_∙_) {A} {x} {y} {z} x==y y==z = ind== C c x y x==y z y==z where
  C : (x y : A) -> (p : x == y) -> Set
  C x y p = (z : A) -> (y == z) -> (x == z)
  c : (x : A) -> C x x refl -- C x x refl = (z : A) -> (x == z) -> (x == z)
  c x z q = q

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
x ==⟨ x==y ⟩ y==z  =  x==y ∙ y==z

-- | QED
_∎ : {A : Set} -> (x : A) → x == x
x ∎  =  refl

-------------------------------------------------------------------------------
-- Lemma 2.1.4

right-unit : {A : Set} -> (x y : A) -> (p : x == y) -> (p == p ∙ refl)
right-unit {A} x y p = ind== C c x y p where
  C : (x y : A) -> (p : x == y) -> Set
  C x y p = p == p ∙ refl
  c : (x : A) -> C x x refl
  c x = begin refl ==⟨⟩ (refl ∙ refl) ∎
left-unit : {A : Set} -> (x y : A) -> (p : x == y) -> (p == refl ∙ p)
left-unit {A} x y p = ind== C c x y p where
  C : (x y : A) -> (p : x == y) -> Set
  C x y p = p == refl ∙ p
  c : (x : A) -> C x x refl
  c x = begin refl ==⟨⟩ (refl ∙ refl) ∎

left-inverse : {A : Set} -> (x y : A) -> (p : x == y) -> (inv p ∙ p == refl)
left-inverse {A} x y p = ind== C c x y p where
  C : (x y : A) -> (p : x == y) -> Set
  C x y p = (inv p ∙ p) == refl
  c : (x : A) -> C x x refl
  c x = begin inv refl ∙ refl ==⟨⟩ refl ∎
right-inverse : {A : Set} -> (x y : A) -> (p : x == y) -> (p ∙ inv p == refl)
right-inverse {A} x y p = ind== C c x y p where
  C : (x y : A) -> (p : x == y) -> Set
  C x y p = (p ∙ inv p) == refl
  c : (x : A) -> C x x refl
  c x = begin refl ∙ inv refl ==⟨⟩ refl ∎

inv-inv : {A : Set} -> (x y : A) -> (p : x == y) -> (inv (inv p) == p)
inv-inv {A} x y p = ind== C c x y p where
  C : (x y : A) -> (p : x == y) -> Set
  C x y p = inv (inv p) == p
  c : (x : A) -> C x x refl
  c x =
    begin
      inv (inv refl)
    ==⟨⟩
      inv refl
    ==⟨⟩
      refl
    ∎

associativity : {A : Set}
              -> (x y z w : A)
              -> (p : x == y) -> (q : y == z) -> (r : z == w)
              -> (p ∙ (q ∙ r)) == ((p ∙ q) ∙ r)
associativity {A} x y z w p q r = ind== C c x y p z w q r where
  C : (x y : A) -> (p : x == y) -> Set
  C x y p =
    (z w : A) -> (q : y == z) -> (r : z == w) -> (p ∙ (q ∙ r)) == ((p ∙ q) ∙ r)
  c : (x : A) -> C x x refl
  c x z w q r =
    begin
      (refl ∙ (q ∙ r))
    ==⟨⟩ -- ==⟨ inv (right-unit x w (q ∙ r)) ⟩
      q ∙ r
    ==⟨⟩
      ((refl ∙ q) ∙ r)
    ∎
-- in HoTT this requires a lot more induction steps?

-------------------------------------------------------------------------------
-- Eckman-Hilton

-- right whisker
_∙r_ : {A : Set} -> {a b c : A} -> {p q : a == b}
     -> (α : p == q) -> (r : b == c) -> p ∙ r == q ∙ r
_∙r_ {A} {a} {b} {c} {p} {q} α r = ind== D d b c r a p q α where
  D : (b c : A) -> (r : b == c) -> Set
  D b c r = (a : A) -> (p q : a == b) -> (α : p == q) -> p ∙ r == q ∙ r
  d : (b : A) -> D b b refl
  d b a p q α =
    begin
      p ∙ refl
    ==⟨ inv (right-unit a b p) ⟩
      p ==⟨ α ⟩ q
    ==⟨ right-unit a b q ⟩
      q ∙ refl
    ∎

-- left whisker
_∙l_ : {A : Set} -> {a b c : A} -> {r s : b == c}
     -> (q : a == b) -> (β : r == s) -> (q ∙ r) == (q ∙ s)
(_∙l_) {A} {a} {b} {c} {r} {s} q β = ind== D d a b q c r s β where
  D : (a b : A) -> (q : a == b) -> Set
  D a b q = (c : A) -> (r s : b == c) -> (β : r == s) -> (q ∙ r == q ∙ s)
  d : (a : A) -> D a a refl
  d a c r s β =
    begin
      (refl ∙ r)
    ==⟨ inv (left-unit a c r) ⟩
      r
    ==⟨ β ⟩
      s
    ==⟨ left-unit a c s ⟩
      (refl ∙ s)
    ∎

_⋆_ : {A : Set} -> {a b c : A} -> {p q : a == b} -> {r s : b == c}
    -> (α : p == q) -> (β : r == s) -> (p ∙ r) == (q ∙ s)
(_⋆_) {A} {a} {b} {c} {p} {q} {r} {s} α β = (α ∙r r) ∙ (q ∙l β)

_⋆'_ : {A : Set} -> {a b c : A} -> {p q : a == b} -> {r s : b == c}
    -> (α : p == q) -> (β : r == s) -> (p ∙ r) == (q ∙ s)
(_⋆'_) {A} {a} {b} {c} {p} {q} {r} {s} α β = (p ∙l β) ∙ (α ∙r s)


e-h1 : {A : Set} -> {a : A} -> (α β : refl == refl) -> (α ⋆ β == α ∙ β)
e-h1 {A} {a} α β =
  begin
    α ⋆ β
  ==⟨⟩
    (α ∙r refl) ∙ (refl ∙l β)
  ==⟨⟩
    (inv (right-unit a a refl) ∙ (α ∙ right-unit a a refl)) ∙ (refl ∙l β)
  ==⟨⟩
    (inv (right-unit a a refl) ∙ (α ∙ right-unit a a refl))
    ∙
    (inv (left-unit a a refl) ∙ (β ∙ left-unit a a refl))
  ==⟨⟩
    ((inv refl ∙ (α ∙ refl)) ∙ (inv refl ∙ (β ∙ refl)))
  ==⟨⟩
    ((refl ∙ (α ∙ refl)) ∙ (refl ∙ (β ∙ refl)))
  ==⟨⟩
    ((α ∙ refl) ∙ (β ∙ refl))
  ==⟨ associativity refl refl refl refl (α ∙ refl) β refl ⟩
    ((α ∙ refl) ∙ β) ∙ refl
  ==⟨ inv (right-unit refl refl ((α ∙ refl) ∙ β)) ⟩
    ((α ∙ refl) ∙ β)
  ==⟨ inv (associativity refl refl refl refl α refl β) ⟩
    α ∙ (refl ∙ β)
  ==⟨⟩
    (α ∙ β)
  ∎


e-h2 : {A : Set} -> {a : A} -> (α β : refl == refl) -> (α ⋆' β == β ∙ α)
e-h2 {A} {a} α β =
  begin
    α ⋆' β
  ==⟨⟩
    (refl ∙l β) ∙ (α ∙r refl)
  ==⟨⟩
    (inv (left-unit a a refl) ∙ (β ∙ left-unit a a refl)) ∙ (α ∙r refl)
  ==⟨⟩
    (inv (left-unit a a refl) ∙ (β ∙ left-unit a a refl))
    ∙
    (inv (right-unit a a refl) ∙ (α ∙ left-unit a a refl))
  ==⟨⟩
     (refl ∙ (β ∙ refl)) ∙ (refl ∙ (α ∙ refl))
  ==⟨⟩
     (β ∙ refl) ∙ (α ∙ refl)
  ==⟨ associativity refl refl refl refl (β ∙ refl) α refl ⟩
     ((β ∙ refl) ∙ α) ∙ refl
  ==⟨ inv (right-unit refl refl ((β ∙ refl) ∙ α)) ⟩
     (β ∙ refl) ∙ α
  ==⟨ inv (associativity refl refl refl refl β refl α) ⟩       
   β ∙ (refl ∙ α)
  ==⟨⟩
    (β ∙ α)
  ∎

⋆==⋆'
  :  {A : Set} -> {a b c : A} -> {p q : a == b} -> {r s : b == c}
  -> (α : p == q) -> (β : r == s)
  -> (α ⋆ β) == (α ⋆' β)
⋆==⋆' {A} {a} {b} {c} {p} {q} {r} {s} α β =
  ind== I1 i1 p q α r s β where
    I1 : (p q : a == b) -> (α : p == q) -> Set
    I1 p q α = (r s : b == c) -> (β : r == s) -> (α ⋆ β) == (α ⋆' β)
    i1 : (p : a == b) -> I1 p p refl
    i1 p r s β = ind== I2 i2 a b p r s β where
      I2 : (a b : A) -> (p : a == b) -> Set
      I2 a b p =
        (r s : b == c) -> (β : r == s)
        -> (_⋆_ {A} {a} {b} {c} {p} {p} {r} {s} refl β)
        == (_⋆'_ {A} {a} {b} {c} {p} {p} {r} {s} refl β)
      i2 : (a : A) -> I2 a a refl
      i2 a r s β = ind== I3 i3 r s β where
        I3 : (r s : a == c) -> (β : r == s) -> Set
        I3 r s β = (_⋆_ {A} {a} {a} {c} {refl} {refl} {r} {s} refl β) == (refl ⋆' β)
        i3 : (r : a == c) -> I3 r r refl
        i3 r = ind== I4 i4 a c r where
          I4 : (x z : A) -> (r : x == z) -> Set
          I4 x z r =
            (_⋆_ {A} {x} {x} {z} {refl} {refl} {r} {r} refl refl) == (refl ⋆' refl)
          i4 : (x : A) -> I4 x x refl
          i4 x = refl

eckmann-hamilton
  : {A : Set} -> {a : A}
  ->  (α β : _==_ {_} {a == a} refl refl)
  -> (α ∙ β) == (β ∙ α)
eckmann-hamilton {A} {a} α β =
  begin
    (α ∙ β)
  ==⟨ inv (e-h1 α β) ⟩
    (α ⋆ β)
  ==⟨ ⋆==⋆' α β ⟩
    (α ⋆' β)
  ==⟨ e-h2 α β ⟩
    (β ∙ α)
  ∎

-------------------------------------------------------------------------------
-- Functions are Functors

-- congruence
ap : {A B : Set} -> (f : A -> B) -> {x : A} -> {y : A}
       -> (x == y) -> (f x == f y)
ap {A} {B} f {x} {y} x==y = ind== C c x y x==y where
 C : (x y : A) -> (p : x == y) -> Set
 C x y p = f x == f y
 c : (x : A) -> C x x refl
 c x = refl

-- Lemma 2.2.2
lemma-2-2-2i
  : {A B : Set} -> {x y z : A} -> (f : A -> B) -> (p : x == y) -> (q : y == z)
  -> ap f (p ∙ q) == ap f p ∙ ap f q
lemma-2-2-2i {A} {B} {x} {y} {z} f p q = ind== I1 i1 x y p z q where
  I1 : (x y : A) -> (p : x == y) -> Set
  I1 x y p = (z : A) -> (q : y == z) -> ap f (p ∙ q) == ap f p ∙ ap f q
  i1 : (x : A) -> I1 x x refl
  i1 x z q = ind== I2 i2 x z q where
    I2 : (x z : A) -> (q : x == z) -> Set
    I2 x z q = ap f (refl ∙ q) == ap f refl ∙ ap f q
    i2 : (x : A) -> I2 x x refl
    i2 x =
      begin
        ap f (refl ∙ refl)
      ==⟨⟩
        ap f refl
      ==⟨⟩
        (ap f refl ∙ refl)
      ==⟨⟩
        (ap f refl ∙ ap f refl)
      ∎

lemma2-2-2ii
  : {A B : Set} -> {x y : A} -> (f : A -> B) -> (p : x == y)
  -> ap f (inv p) == inv (ap f p)
lemma2-2-2ii {A} {B} {x} {y} f p = ind== I i x y p where
  I : (x y : A) -> (p : x == y) -> Set
  I x y p = ap f (inv p) == inv (ap f p)
  i : (x : A) -> I x x refl
  i x = refl
 
_∘_ : {A B C : Set} -> (g : B -> C) -> (f : A -> B) -> A -> C
g ∘ f = λ x → g (f x) 

lemma2-2-2iii
  : {A B C : Set} -> {x y : A} -> (f : A -> B) -> (g : B -> C) -> (p : x == y)
   -> ap g (ap f p) == ap (g ∘ f) p
lemma2-2-2iii {A} {B} {C} {x} {y} f g p = ind== I i x y p where
  I : (x y : A) -> (p : x == y) -> Set
  I x y p = ap g (ap f p) == ap (g ∘ f) p
  i : (x : A) -> I x x refl
  i x = 
    begin
      ap g (ap f refl)
    ==⟨⟩
      ap g refl
    ==⟨⟩
      refl
    ==⟨⟩
      ap (g ∘ f) refl
    ∎

id : {A : Set} -> A -> A
id x = x

lemma2-2-2iv
  : {A : Set} -> {x y : A} -> (p : x == y) -> ap id p == p
lemma2-2-2iv {A} {x} {y} p = ind== I i x y p where
  I : (x y : A) -> (p : x == y) -> Set
  I x y p = ap id p == p
  i : (x : A) -> I x x refl
  i x = refl

-------------------------------------------------------------------------------
-- Type families are Fibrations

-- Transport lemma
transport
  : {A : Set} -> {P : A -> Set} -> {x y : A} -> (p : x == y) -> P x -> P y
transport {A} {P} {x} {y} p px = ind== I i x y p px where
  I : (x y : A) -> (p : x == y) -> Set
  I x y p = P x -> P y
  i : (x : A) -> I x x refl
  i x px = px

-- Path lifting lemma
lift
  : {A : Set} -> {P : A -> Set} -> {x y : A}
  -> (u : P x) -> (p : x == y)
  -> _==_ {_} {Σ A P} (x , u) (y , transport p u)
lift {A} {P} {x} {y} u p = ind== I i x y p u where
  I : (x y : A) -> (p : x == y) -> Set
  I x y p = (u : P x) -> _==_ {_} {Σ A P} (x , u) (y , transport p u)
  i : (x : A) -> I x x refl
  i x u = 
    begin
      (x , u)
    ==⟨⟩
      (x , id u)
    ==⟨⟩
      (x , transport {A} {P} refl u)
    ∎

-- Dependent congruence
apd : {A : Set} -> {P : A -> Set}
    -> (f : (x : A) -> P x) -> {x y : A}
    -> (p : x == y) -> transport p (f x) == f y
apd {A} {P} f {x} {y} p = ind== I i x y p where
  I : (x y : A) -> (p : x == y) -> Set
  I x y p = transport p (f x) == f y
  i : (x : A) -> I x x refl
  i x = begin transport {A} {P} refl (f x) ==⟨⟩ id (f x) ==⟨⟩ f x ∎

transportconst
  : {A : Set} -> {x y : A} -> {B : Set}
  -> (p : x == y) -> (b : B)
  -> transport {A} {λ x → B} p b == b
transportconst {A} {x} {y} {B} p b = ind== I i x y p where
  P : A -> Set
  P x = B
  I : (x y : A) -> (p : x == y) -> Set
  I x y p = transport {A} {λ x → B} p b == b
  i : (x : A) -> I x x refl
  i x =
    begin
      transport {_} {P} {x} {x} refl b
    ==⟨⟩
      id b
    ==⟨⟩
      b
    ∎

lemma2-3-8
  : {A B : Set} -> {x y : A} (f : A -> B) -> (p : x == y)
  -> apd f p == transportconst p (f x) ∙ ap f p
lemma2-3-8 {A} {B} {x} {y} f p = ind== I i x y p where
  I : (x y : A) -> (p : x == y) -> Set
  I x y p = apd f p == transportconst p (f x) ∙ ap f p
  i : (x : A) -> I x x refl
  i x =
    begin
      apd f refl
    ==⟨ refl ⟩
      refl
    ==⟨ refl ⟩
      (refl ∙ refl)
    ==⟨ refl ⟩
      transportconst {A} {x} {x} refl (f x) ∙ ap f refl
    ∎

lemma2-3-9
  : {A : Set} -> {x y z : A}
  -> (P : A -> Set) -> (p : x == y) -> (q : y == z)  -> (u : P x)
  -> transport {A} {P} q (transport {A} {P} p u) == transport {A} {P} (p ∙ q) u
lemma2-3-9 {A} {x} {y} {z} P p q u = ind== I i x y p z q u where
  I : (x y : A) -> (p : x == y) -> Set
  I x y p =
    (z : A) -> (q : y == z) -> (u : P x)
    -> transport {A} {P} q (transport {A} {P} p u)
       == transport {A} {P} (p ∙ q) u
  i : (x : A) -> I x x refl
  i x z q u = ind== I2 i2 x z q u where
    I2 : (x z : A) -> (q : x == z) -> Set
    I2 x z q =
      (u : P x)
      -> transport {A} {P} q (transport {A} {P} refl u)
      ==  transport {A} {P} (refl ∙ q) u
    i2 : (z : A) -> I2 z z refl
    i2 z u =
      begin
        transport {A} {P} refl (transport {A} {P} refl u)
      ==⟨⟩
        transport {A} {P} refl (id u)
      ==⟨⟩
        transport {A} {P} refl u
      ==⟨⟩
        transport {A} {P} (refl ∙ refl) u
      ∎
      
-------------------------------------------------------------------------------
-- Homotopies and Equivalences

data _~_ {A : Set} {P : A -> Set} (f g : (x : A) -> P x) : Set where
  homotopy : ((x : A) -> (f x == g x)) -> f ~ g

app~
  : {A : Set} -> {P : A -> Set}
  -> {f g : (x : A) -> P x} -> f ~ g -> (x : A) -> f x == g x
app~ (homotopy h) x = h x

lemma2-4-2i : {A : Set} -> {P : A -> Set} -> (f : (x : A) -> P x) -> f ~ f
lemma2-4-2i {A} {P} f = homotopy (λ x → refl)

lemma2-4-2ii
  : {A : Set} -> {P : A -> Set} -> (f g : (x : A) -> P x) -> (f ~ g) -> (g ~ f)
lemma2-4-2ii {A} {P} f g (homotopy f~g) = homotopy (λ x → inv (f~g x))

lemma2-4-2iii
  : {A : Set} -> {P : A -> Set} -> (f g h : (x : A) -> P x)
  -> (f ~ g) -> (g ~ h) -> (f ~ h)
lemma2-4-2iii {A} {P} f g h (homotopy f~g) (homotopy g~h) =
  homotopy (λ x → begin f x ==⟨ f~g x ⟩ g x ==⟨ g~h x ⟩ h x ∎)

lemma2-4-3
  : {A B : Set} -> (f g : A -> B) -> (x y : A) -> (p : x == y) -> (H : f ~ g)
  -> app~ H x ∙ ap g p == ap f p ∙ app~ H y
lemma2-4-3 {A} {B} f g x y p H = ind== I i x y p f g H where
  I : (x y : A) -> (p : x == y) -> Set
  I x y p =
    (f g : A -> B) -> (H : f ~ g) -> app~ H x ∙ ap g p == ap f p ∙ app~ H y
  i : (x : A) -> I x x refl
  i x f g (homotopy f~g) = 
    begin
      f~g x ∙ ap g refl
    ==⟨⟩
      f~g x ∙ refl
    ==⟨ inv (right-unit (f x) (g x) (f~g x)) ⟩
      f~g x
    ==⟨ left-unit (f x) (g x) (f~g x) ⟩
      refl ∙ f~g x
    ==⟨⟩
      ap f refl ∙ f~g x
    ∎

coro2-4-4
  : (A : Set) -> (f : A -> A) -> (H : f ~ id) -> (x : A)
  -> app~ H (f x) == ap f (app~ H x)
coro2-4-4 A f H x = {!!} where
  p : ap f (app~ H x) ∙ app~ H x == app~ H (f x) ∙ app~ H x
  p =
    begin
      ap f (app~ H x) ∙ app~ H x
    ==⟨ inv (lemma2-4-3 f id (f x) x (app~ H x) H) ⟩
      app~ H (f x) ∙ ap id (app~ H x)
    ==⟨ {!!} ⟩
      app~ H (f x) ∙ id (app~ H x)
    ==⟨ {!!} ⟩
      app~ H (f x) ∙ app~ H x
    ∎
