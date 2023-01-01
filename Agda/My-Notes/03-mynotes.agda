{-# OPTIONS --without-K --safe #-}

-- Σ types and universes
-- https://www.youtube.com/watch?v=W3sM9bRsIvQ

-- A lot of this is redefining things that we defined before. Before, we were pretending universes didn't exist. Now that we are using them, we have to redefine things to be generalized with universes.

open import general-notation
open import 01-mynotes hiding (𝟘 ; 𝟙 ; ⋆ ; D ; _≣_)
open import 02-mynotes using (is-prime ; _*_ ; 𝟘 ; 𝟙 ; ⋆ ; _≥_)

-- ⊔ "\lub" (least upper bound, basically maximum)
-- 𝓤 "\MCU"
open import Agda.Primitive
  using (Level ; lzero ; lsuc ; _⊔_)
  renaming (Set to 𝓤)
  public

-- Let i, j, and k range over universe levels
variable i j k : Level

-- General sigma type with universes:
record Σ {A : 𝓤 i} (B : A → 𝓤 j) : 𝓤 (i ⊔ j) where
  constructor
    _,_
  field
    pr₁ : A
    pr₂ : B pr₁

open Σ public
infixr 1 _,_

-- i, j, k are not mentioned in the definition, but they are implicit parameters.
-- Everything declared with a variable becomes an implicit parameter, in the order that it is used.
Sigma : (A : 𝓤 i) (B : A → 𝓤 j) → 𝓤 (i ⊔ j)
Sigma {i} {j} A B = Σ {i} {j} {A} B

syntax Sigma A (λ x → b) = Σ x ꞉ A , b

infix -1 Sigma

_×_ : 𝓤 i → 𝓤 j → 𝓤 (i ⊔ j)
A × B = Σ x ꞉ A , B

infixr 2 _×_

-- More general type of negation:
¬_ : 𝓤 i → 𝓤 i
¬ A = A → 𝟘

-- Give the identity type more general universe assignments:
data _≡_ {X : 𝓤 i} : X → X → 𝓤 i where
  refl : (x : X) → x ≡ x

infix 0 _≡_

-- ≢ "\==n"
_≢_ : {X : 𝓤 i} → X → X → 𝓤 i
x ≢ y = ¬ (x ≡ y)

≡-elim
  : {X : 𝓤 i} (A : (x y : X) → x ≡ y → 𝓤 j)
  → ((x : X) → A x x (refl x))
  → (x y : X) (p : x ≡ y) → A x y p
≡-elim A f x x (refl x) = f x

≡-nondep-elim
  : {X : 𝓤 i} (A : X → X → 𝓤 j)
  → ((x : X) → A x x)
  → (x y : X) → x ≡ y → A x y
≡-nondep-elim A = ≡-elim (λ x y _ → A x y)

trans : {A : 𝓤 i} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans p (refl y) = p

sym : {A : 𝓤 i} {x y : A} → x ≡ y → y ≡ x
sym (refl x) = refl x

ap : {A : 𝓤 i} {B : 𝓤 j} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap f (refl x) = refl (f x)

ap₂
  : {A : 𝓤 i} {B : 𝓤 j} {C : 𝓤 k} (f : A → B → C) {x x' : A} {y y' : B}
  → x ≡ x'
  → y ≡ y'
  → f x y ≡ f x' y'
ap₂ f (refl x) (refl y) = refl (f x y)

transport
  : {X : 𝓤 i} (A : X → 𝓤 j)
  → {x y : X}
  → x ≡ y
  → A x → A y
transport A (refl x) a = a

_∙_
  : {A : 𝓤 i} {x y z : A}
  → x ≡ y
  → y ≡ z
  → x ≡ z
-- refl x ∙ refl y = refl x
_∙_ = trans

infixl 7 _∙_

_⁻¹ : {A : 𝓤 i} {x y : A} → x ≡ y → y ≡ x
_⁻¹ = sym

infix 40 _⁻¹

-- The (sub)type of prime numbers. We can use a sigma type.
-- "P is the type of natural numbers, p, such that p is prime."
-- This works because the elements of this type are pairs: a natural number p, and a proof that p is prime.
ℙ : 𝓤₀
ℙ = Σ p ꞉ ℕ , is-prime p

ℙ-inclusion : ℙ → ℕ
ℙ-inclusion = pr₁
-- ℙ-inclusion (p , _) = p

-- We can prove that this map is left-cancellable, i.e., it satisfies
--   ℙ-inclusion u ≡ ℙ-inclusion u → u ≡ v
-- Moreover, this map is an embedding (we haven't defined this concept yet).

-- (Not quite) the type of composite numbers:
CN : 𝓤
CN = Σ x ꞉ ℕ , Σ (y , z) ꞉ ℕ × ℕ , x ≡ y * z
-- CN = Σ x ꞉ ℕ , Σ (y , z) ꞉ ℕ × ℕ , (y ≥ 2) × (z ≥ 2) × (x ≡ y * z)

CN-projection : CN → ℕ
CN-projection = pr₁

-- This map is not left-cancellable, and hence can't be considered to be an inclusion.
counter-example
  : CN-projection (6 , (3 , 2) , refl 6)
  ≡ CN-projection (6 , (2 , 3), refl 6)
counter-example = refl 6

-- But how do we prove that these two tuples are *different*? They certainly do look different. We'll do this later.

-- We will need to define
--
-- CN = Σ x ꞉ ℕ , ∥ Σ (y , z) ꞉ ℕ × ℕ , x ≡ y * z ∥, or equivalently
-- CN = Σ x ꞉ ℕ , ∃ (y , z) ꞉ ℕ × ℕ , x ≡ y * z
--
-- to really get a *subtype* of composite numbers.

-- Another use of Σ. To define mathematical structures, like the type of monoids.

-- X is a proposition if it has at most one element.
is-prop : 𝓤 i → 𝓤 i
is-prop X = (x y : X) → x ≡ y

-- X is a set if, given any two elements, there is at most one way in which these two elements are equal.
-- For example, ℕ is a set.
is-set : 𝓤 i → 𝓤 i
is-set X = (x y : X) → is-prop (x ≡ y)

-- A monoid is not a set.
-- Not because it's too big, but because x ≡ y fails. Monoids can be equal in more than one way.
-- 𝟏 "\B1"
-- · "\cdot"
Mon : 𝓤 (lsuc i)
Mon {i} = Σ X ꞉ 𝓤 i -- data
  , is-set X -- property
  × (Σ 𝟏 ꞉ X -- data
    , Σ _·_ ꞉ (X → X → X) -- data
      , (((x : X) → (x · 𝟏 ≡ x)) -- (1) property
      × ((x : X) → (𝟏 · x ≡ x)) -- (2) property
      × ((x y z : X) → (x · (y · z)) ≡ ((x · y) · z)))) -- (3) property
-- The definition can be read as: "a monoid is a type that is a set and comes equipped with two pieces of data (unit and multiplication) and has the properties (1), (2), and (3)."
-- "comes equipped with" is a use of Σ.

-- This can also be defined using a record in Agda:
record Mon' : 𝓤 (lsuc i) where
  constructor mon
  field
    carrier : 𝓤 i
    carrier-is-set : is-set carrier
    𝟏 : carrier
    _·_ : carrier → carrier → carrier
    left-unit-law : (x : carrier) → x · 𝟏 ≡ x
    right-unit-law : (x : carrier) → 𝟏 · x ≡ x
    assoc-law : (x y z : carrier) → (x · (y · z)) ≡ ((x · y) · z)
    
-- Advantages of using records:
--   - The code becomes more clear.
--   - You can use elements of the record (e.g., carrier-is-set) as projections to extract elements out of the record.
--   - The goals are more readable when you're proving something using the record.
--
-- Disadvantages of using records:
--   - In HoTT, we prove lots of properties using Σ (e.g., a sum of sets is a set). We can't use these if using a record.
--
-- Two solutions to this problem:
--   1. Use only Σ. (This is what Martin and Egbert do.)
--   2. Define everything twice (Σ and record). (This is what the cubical Agda library does, using metaprogramming that automatically generates the Σ from the record.)

-- Converting between Σ and record definitions of Mon:
α : Mon {i} → Mon' {i}
α (X , X-is-set , 𝟏 , _·_ , l , r , a) = mon X X-is-set 𝟏 _·_ l r a

β : Mon' {i} → Mon {i}
β (mon X X-is-set 𝟏 _·_ l r a) = (X , X-is-set , 𝟏 , _·_ , l , r , a)

βα : (M : Mon {i}) → β (α M) ≡ M
βα = refl

αβ : (M : Mon' {i}) → α (β M) ≡ M
αβ = refl

-- The above also proves that the two definitions are equivalent. So it's up to you which one to choose.

-- This kind of proof doesn't belong to the realm of MLTT:
false-is-not-true[not-an-MLTT-proof] : false ≢ true
false-is-not-true[not-an-MLTT-proof] ()

-- Proof in MLTT, which requires a universe (Cf. Ulrik's 2nd HoTT lecture):

_≣_ : Bool → Bool → 𝓤₀
true ≣ true = 𝟙
true ≣ false = 𝟘
false ≣ true = 𝟘
false ≣ false = 𝟙

≡-gives-≣ : {x y : Bool} → x ≡ y → x ≣ y
≡-gives-≣ {.true} {.true} (refl true) = ⋆
≡-gives-≣ {.false} {.false} (refl false) = ⋆

false-is-not-true : ¬ (false ≡ true)
false-is-not-true p = II
  where
    I : false ≣ true
    I = ≡-gives-≣ p

    II : 𝟘
    II = I

-- Not as readable
false-is-not-true' : ¬ (false ≡ true)
false-is-not-true' = ≡-gives-≣

-- The above proof is different from the one given by Ulrik in the Hott track.
-- Exercise: implement Ulrik's proof in Agda.
is-true : Bool → 𝓤₀
is-true false = 𝟘
is-true true = 𝟙

true-not-false-Ulrik : ¬ (true ≡ false)
true-not-false-Ulrik p = transport is-true {true} {false} p ⋆

-- Exercise: prove that ¬ (0 ≡ 1) in the natural numbers in MLTT style without using ().
_≣'_ : ℕ → ℕ → 𝓤₀
0 ≣' 0 = 𝟙
0 ≣' suc y = 𝟘
suc x ≣' 0 = 𝟘
suc x ≣' suc y = x ≣' y

≡-gives-≣' : {x y : ℕ} → x ≡ y → x ≣' y
≡-gives-≣' {.zero} {.zero} (refl zero) = ⋆
≡-gives-≣' {.(suc x)} {.(suc x)} (refl (suc x)) = {!!}

zero-not-one : ¬ (0 ≡ 1)
-- zero-not-one = ≡-gives-≣'
zero-not-one p = {!II!}
  where
    I : 0 ≡ 1
    I = {!!}

    II : 𝟘
    II = {!I!}

-- Contrapositives:
contrapositive : {A : 𝓤 i} {B : 𝓤 j} → (A → B) → (¬ B → ¬ A)
contrapositive f g a = g (f a)

Π-¬-gives-¬-Σ
  : {X : 𝓤 i} {A : X → 𝓤 j}
  → ((x : X) → ¬ A x)
  → ¬ (Σ x ꞉ X , A x)
Π-¬-gives-¬-Σ ϕ (x , a) = ϕ x a

¬-Σ-gives-Π-¬
  : {X : 𝓤 i} {A : X → 𝓤 j}
  → ¬ (Σ x ꞉ X , A x)
  → ((x : X) → ¬ A x)
¬-Σ-gives-Π-¬ γ x a = γ (x , a)

-- Equality in Σ types.

-- Agda technique: multiple functions are going to use the same parameters, so we make an anonymous module to avoid repeating them.
module _
  {X : 𝓤 i}
  {A : X → 𝓤 j}
  {(x , a) (y , b) : Σ A}
  {A' : 𝓤 j}
  {(x' , a') (y' , b') : X × A'}
  where

  -- If two pairs are equal, then both of their respective elements are equal.
  from-×-≡
    : (x' , a') ≡ (y' , b')
    → (x' ≡ y') × (a' ≡ b')
  from-×-≡ (refl (x' , a')) = (refl x' , refl a')

  -- If the respective elements of two pairs are equal, then the pairs themselves are equal.
  to-×-≡
    : (x' ≡ y') × (a' ≡ b')
    → (x' , a') ≡ (y' , b')
  to-×-≡ (refl x' , refl a') = refl (x' , a')

  contra-from-×-≡
    : ¬ ((x' ≡ y') × (a' ≡ b'))
    → (x' , a') ≢ (y' , b')
  contra-from-×-≡ = contrapositive from-×-≡

  contra-to-×-≡
    : (x' , a') ≢ (y' , b')
    → ¬ ((x' ≡ y') × (a' ≡ b'))
  contra-to-×-≡ = contrapositive to-×-≡

  -- Dependent versions.
  -- We need to transport because a and b are not in the same type.
  -- x y : X
  -- a : A x
  -- b : A y
  from-Σ-≡
    : (x , a) ≡ (y , b)
    → Σ p ꞉ (x ≡ y) , ((transport A p a) ≡ b)
  from-Σ-≡ (refl (x , a)) = (refl x , refl a)

  to-Σ-≡
    : (Σ p ꞉ (x ≡ y) , (transport A p a ≡ b))
    → (x , a) ≡ (y , b)
  to-Σ-≡ (refl x , refl a) = refl (x , a)

  contra-from-Σ-≡
    : ¬ (Σ p ꞉ (x ≡ y) , (transport A p a ≡ b))
    → (x , a) ≢ (y , b)
  contra-from-Σ-≡ = contrapositive from-Σ-≡

  contra-to-Σ-≡
    : (x , a) ≢ (y , b)
    → ¬ (Σ p ꞉ (x ≡ y) , (transport A p a ≡ b))
  contra-to-Σ-≡ = contrapositive to-Σ-≡

  to-Σ-≢
    : ((p : x ≡ y) → transport A p a ≢ b)
    → (x , a) ≢ (y , b)
  to-Σ-≢ u = contra-from-Σ-≡ (Π-¬-gives-¬-Σ u)

  from-Σ-≢
    : (x , a) ≢ (y , b)
    → ((p : x ≡ y) → transport A p a ≢ b)
  from-Σ-≢ v = ¬-Σ-gives-Π-¬ (contra-to-Σ-≡ v)
