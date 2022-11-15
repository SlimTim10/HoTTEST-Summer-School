{-# OPTIONS --without-K --safe #-}

-- https://www.youtube.com/watch?v=d02hIwhdFTk

-- Type = Set
open import general-notation
open import 01-mynotes hiding (𝟘 ; 𝟙 ; D)

-- empty type
-- \b0
data 𝟘 : Type where

-- HoTT notation: Π x ꞉ X , A x
-- Agda notation: (x : X) → A x

𝟘-elim : {A : 𝟘 → Type} (x : 𝟘) → A x
𝟘-elim ()

-- Recall, 𝟘 acts like false

-- Negation
-- \neg
¬_ : Type → Type
¬ A = A → 𝟘

infix 1000 ¬_

𝟘-nondep-elim : {B : Type} → 𝟘 → B
𝟘-nondep-elim {B} = 𝟘-elim {λ _ → B}

-- When A ≡ λ _ → B,
-- Π x : X , A x ≡ Π x : X , B ≡ X → B
-- i.e., when A is the constant type family B, the dependent product (function) type is the same as a regular function type

-- Synonym for clarity
is-empty : Type → Type
is-empty A = A → 𝟘

-- 𝟘-is-empty : ¬ 𝟘
𝟘-is-empty : is-empty 𝟘
𝟘-is-empty = 𝟘-nondep-elim

𝟘-is-empty' : is-empty 𝟘
𝟘-is-empty' = id

𝟘-is-empty'' : is-empty 𝟘
𝟘-is-empty'' = λ ()

-- Unit type, different syntax from previous lecture
-- Record definitions satisfy a certain "η" rule
-- Recall, 𝟙 acts like true
record 𝟙 : Type where
  constructor
    ⋆

-- To access constructors of a record
open 𝟙 public

-- 𝟙-is-nonempty : ¬ ¬ 𝟙
𝟙-is-nonempty : ¬ is-empty 𝟙
-- 𝟙-is-nonempty = λ x → x ⋆
𝟙-is-nonempty = λ x → x ⋆

𝟙-is-nonempty' : ¬ is-empty 𝟙
𝟙-is-nonempty' f = f ⋆


-- Γ , ⋆ : 𝟙 ⊢ P(⋆) type
-------------------------------------------
-- Γ ⊢ ind₁ : P(⋆) → Π x : 𝟙 , P(x)
--
-- HoTT: P(⋆) type
-- Agda: P : 𝟙 → Type
-- Remember, type families are functions from _ to Type
𝟙-elim
  : {P : 𝟙 → Type}
  → P ⋆ -- P(⋆)
  → (x : 𝟙)
  → P x -- P(x)
𝟙-elim p ⋆ = p
-- 𝟙-elim p x = p -- works when 𝟙 is defined as record
-- 𝟙-elim p = λ ⋆ → p

𝟙-nondep-elim
  : {P : Type}
  → P
  → 𝟙 → P
𝟙-nondep-elim {P} = 𝟙-elim {λ _ → P}

-- Binary digits, isomorphic to Bool
-- \B for bold digits
data 𝟚 : Type where
  𝟎 𝟏 : 𝟚

--    Γ , x : 𝟚 ⊢ P(x) type    Γ ⊢ a : P(𝟏)    Γ ⊢ b : P(𝟎)
--    --------------------------------------------------------------------------
--    Γ , x : 𝟚 ⊢ ind₂ (a , b , x) : P(x)
--
-- This is like the dependent if[]_then_else from lecture 1
𝟚-elim
  : {P : 𝟚 → Type}
  → P 𝟎
  → P 𝟏
  → (x : 𝟚)
  → P x
𝟚-elim p₀ p₁ 𝟎 = p₀
𝟚-elim p₀ p₁ 𝟏 = p₁

-- This is like the non-dependent if_then_else from lecture 1
𝟚-nondep-elim
  : {P : Type}
  → P
  → P
  → 𝟚
  → P
𝟚-nondep-elim {P} = 𝟚-elim {λ _ → P}

-- Eliminators are important to understand what type theory is, but they're inconvenient to use in practice. So in Agda, instead of using eliminators, we use pattern matching. It is proven that definitions by pattern matching are equivalent to definitions using eliminators (provided we are using --without-K).

-- Π types in Agda are primitive.
-- 
-- The HoTT type Π x : X , A x is written in Agda as
-- 
-- 		(x : X) → A x			or
-- 		∀ (x : X) → A x		or
-- 		∀ x → A x				(if Agda can infer X).
--
-- We can introduce Π-syntax if we wish:

Pi : (A : Type) (B : A → Type) → Type
Pi A B = (x : A) → B x
-- For special colon, type "\:4"
syntax Pi A (λ x → b) = Π x ꞉ A , b

-- Function composition

-- Private in a useless module because this definition is just for learning. This is the normal composition we're used to seeing.
module _ where
  private
    _∘_ : {A B C : Type} → (B → C) → (A → B) → (A → C)
    (g ∘ f) x = g (f x)

-- Function composition should be dependent (more general)
_∘_
  : {A B : Type} {C : B → Type}
  → (Π y ꞉ B , C y)
  → (f : A → B)
  → Π x ꞉ A , C (f x)
(g ∘ f) x = g (f x)

-- The types-as-mathematical-statements (or types-as-proofs) reading of dependent function composition is:
-- If (for all y : B we have that C y) and f : A → B is any function, then for all x : A we have that C (f x).

-- Σ-types:

module _ where
  private

    data Σ {A : Type} (B : A → Type) : Type where
      _,_ : (x : A) (y : B x) → Σ {A} B -- Curly brackets means A can be inferred

    -- pr₁ : {A : Type} {B : A → Type} → Σ {A} B → A
    pr₁ : {A : Type} {B : A → Type} → Σ B → A
    pr₁ (x , y) = x

    pr₂ : {A : Type} {B : A → Type} → (z : Σ B) → B (pr₁ z)
    pr₂ (x , y) = y

-- Our preferred definition:
record Σ {A : Type} (B : A → Type) : Type where
  constructor
    _,_
  field
    pr₁ : A
    pr₂ : B pr₁
-- This satisfies the η-rule z = (pr₁ z , pr₂ z), which the previous definition using "data" doesn't.

open Σ public
infixr 0 _,_

-- pr₁' : {A : Type} {B : A → Type} → Σ {A} B → A
pr₁' : {A : Type} {B : A → Type} → Σ B → A
pr₁' = pr₁

-- pr₂' : {A : Type} {B : A → Type} → (z : Σ B) → B (pr₁ z)
pr₂' : {A : Type} {B : A → Type} → ((x , y) : Σ B) → B x -- pattern matching works because of η-rule
pr₂' = pr₂

Sigma : (A : Type) (B : A → Type) → Type
Sigma A B = Σ {A} B

-- \:4
syntax Sigma A (λ x → b) = Σ x ꞉ A , b
infix -1 Sigma

-- Recall that we defined D as follows in lecture 1
-- In Agda, dependent types are simply functions
D : Bool → Type
D true = ℕ
D false = Bool

-- Examples
Σ-example₁ Σ-example₂ : Σ b ꞉ Bool , D b
Σ-example₁ = (true , 17)
Σ-example₂ = (false , true)

-- Σ-elim is "uncurry":
Σ-elim
  : {A : Type} {B : A → Type} {C : (Σ x ꞉ A , B x) → Type}
  → ((x : A) (y : B x) → C (x , y))
  → (z : (Σ x ꞉ A , B x)) → C z -- *
-- *Remember, for any elimination rule, we want to prove that for any element (z) of the new type (Σ), some property holds (C).
Σ-elim f (x , y) = f x y

Σ-curry
  : {A : Type} {B : A → Type} {C : (Σ x ꞉ A , B x) → Type}
  → ((z : (Σ x ꞉ A , B x)) → C z)
  → (x : A) (y : B x) → C (x , y)
Σ-curry f x y = f (x , y)

-- non-dependent pair, AKA cartesian product
_×_ : Type → Type → Type
A × B = Σ x ꞉ A , B

infixr 2 _×_

-- Binary products are special cases of products.
-- We will have that A₀ × A₁ ≅ Π (n ꞉ 2) , A n ≅ ((n : 𝟚) → A n)
--   where
--     A 𝟎 = A₀
--     A 𝟏 = A₁
--     A : 𝟚 → Type
--
-- f ↦ (f 𝟎 , f 𝟏)
-- (a₀ , a₁) ↦ 𝟚-elim a₀ a₁
-- But we need function extensionality to prove that this works.

-- Various uses of Σ:
--
-- 

-- Binary sums
-- \.+
data _∔_ (A B : Type) : Type where
  inl : A → A ∔ B
  inr : B → A ∔ B

-- Mathematically A ∔ B is (disjoint) union.
-- Logically, it is "or" (disjunction).

infixr 20 _∔_

∔-elim
  : {A B : Type} (C : A ∔ B → Type)
  → ((x : A) → C (inl x)) -- f
  → ((y : B) → C (inr y)) -- g
  → (z : A ∔ B) → C z
∔-elim C f g (inl x) = f x
∔-elim C f g (inr y) = g y

-- "If (A implies C) and (B implies C), then (A or B implies C)."
∔-nondep-elim
  : {A B C : Type}
  → (A → C)
  → (B → C)
  → (A ∔ B → C)
∔-nondep-elim {A} {B} {C} = ∔-elim (λ z → C)

-- Binary sums are special cases of sums.
-- We will have that A₀ ∔ A₁ ≅ Σ (n : 𝟚) , A n
--   where
--     A 𝟎 = A₀
--     A 𝟏 = A₁
--
-- inl a₀ ↦ (𝟎 , a₀)
-- inr a₁ ↦ (𝟏 , a₁)

-- The identity type.
--
-- We call an element of the identity type x ≡ y an "identification" or a "path".
-- This is a type family instead of a simple type.
data _≡_ {A : Type} : A → A → Type where
  refl : (x : A) → x ≡ x

-- refl x is a proof that x is equal to itself.

infix 0 _≡_

-- The following is also called "J"
≡-elim
  : {X : Type} (A : (x y : X) → x ≡ y → Type)
  → ((x : X) → A x x (refl x)) -- f
  → (x y : X) (p : x ≡ y) → A x y p
≡-elim A f x x (refl x) = f x

-- To conclude that a property A x y p of identifications p of elements x and y holds for all x, y, and p, it is enough to show that A x x (refl x) holds for all x.
-- The reason this works is confusing and mysterious, but that's ok.

≡-nondep-elim
  : {X : Type} (A : X → X → Type)
  → ((x : X) → A x x)
  → (x y : X) → x ≡ y → A x y
≡-nondep-elim A = ≡-elim (λ x y _ → A x y)

-- Transitivity of ≡
trans : {A : Type} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans p (refl y) = p

-- Symmetry of ≡
sym : {A : Type} {x y : A} → x ≡ y → y ≡ x
sym (refl x) = refl x

ap : {A B : Type} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap f (refl x) = refl (f x)

ap₂
  : {A B C : Type} (f : A → B → C) {x x' : A} {y y' : B}
  → x ≡ x'
  → y ≡ y'
  → f x y ≡ f x' y'
ap₂ f (refl x) (refl y) = refl (f x y)
-- ap₂ f (refl x) y = ap (f x) y

-- For all x and y, if x and y are equal, then any property that holds for x also holds for y. Part of Leibniz principle.
transport
  : {X : Type} (A : X → Type)
  → {x y : X}
  → x ≡ y
  → A x → A y
transport A (refl x) a = a

_∙_
  : {A : Type} {x y z : A}
  → x ≡ y
  → y ≡ z
  → x ≡ z
-- refl x ∙ refl y = refl x
_∙_ = trans

infixl 7 _∙_

_⁻¹ : {A : Type} {x y : A} → x ≡ y → y ≡ x
_⁻¹ = sym

infix 40 _⁻¹

_≤_ : ℕ → ℕ → Type
0 ≤ y = 𝟙
suc x ≤ 0 = 𝟘
suc x ≤ suc y = x ≤ y

_≥_ : ℕ → ℕ → Type
x ≥ y = y ≤ x

_*_ : ℕ → ℕ → ℕ
0 * y = 0
suc x * y = (x * y) + y

infixr 30 _*_

-- The following are statements of theorems. Not proofs.
-- A type is a statement of a theorem. An element (or "inhabitant") of a type is a proof of a theorem.

-- An important idea here is that logic is not separate from mathematics. All of logic is contained inside these mathematical ideas (Σ, Π, etc.).

_divides_ : ℕ → ℕ → Type
x divides y = Σ z ꞉ ℕ , x * z ≡ y

is-prime : ℕ → Type
is-prime p = (p ≥ 2) × (((x y : ℕ) → (x * y) ≡ p → (x ≡ 1) ∔ (x ≡ p)))

twin-prime-conjecture : Type
twin-prime-conjecture =
  (n : ℕ)
  → Σ p ꞉ ℕ
    , (p ≥ n)
    × is-prime p
    × is-prime (p + 2)

-- A proof of the twin prime conjecture would look like:
--   some-proof : twin-prime-conjecture
--   some-proof = ?

there-are-infinitely-many-primes : Type
there-are-infinitely-many-primes =
  (n : ℕ)
  → Σ p ꞉ ℕ , (p ≥ n) × is-prime p
