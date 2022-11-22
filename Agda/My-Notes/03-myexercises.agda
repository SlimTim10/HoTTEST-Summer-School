{-# OPTIONS --without-K --allow-unsolved-metas #-}

module 03-myexercises where

open import prelude hiding (_∼_)

-- Part I -- Homotopies

module _
  {A : Type}
  {B : A → Type}
  where

  _∼_ : ((x : A) → B x) → ((x : A) → B x) → Type
  -- f ∼ g = ∀ x → f x ≡ g x
  f ∼ g = Π x ꞉ A , (f x ≡ g x)

-- Exercise 1

  ∼-refl : (f : (x : A) → B x) → f ∼ f
  -- ∼-refl : (f : Π x ꞉ A , B x) → f ∼ f
  ∼-refl f x = refl (f x)

  -- H for homotopy
  ∼-inv : (f g : (x : A) → B x) → (f ∼ g) → (g ∼ f)
  -- ∼-inv f g H x = sym (H x)
  ∼-inv f g H x = (H x) ⁻¹

  ∼-concat
    : (f g h : (x : A) → B x)
    → f ∼ g
    → g ∼ h
    → f ∼ h
  -- ∼-concat f g h H K x = trans (H x) (K x)
  ∼-concat f g h H K x = H x ∙ K x

  infix 0 _∼_ -- low precedence

-- Part II - Isomorphisms

record is-bijection {A B : Type} (f : A → B) : Type where
  constructor
    Inverse
  field
    inverse : B → A
    η : inverse ∘ f ∼ id
    ε : f ∘ inverse ∼ id

record _≅_ (A B : Type) : Type where
  constructor
    Isomorphism
  field
    bijection : A → B
    bijectivity : is-bijection bijection

infix 0 _≅_

-- Exercise 2

-- Reformulate the same definitions using Sigma-types.
is-bijection' : {A B : Type} → (A → B) → Type
-- WRONG -- don't need first part
-- is-bijection' {A} {B} f = Σ (a , b) ꞉ A × B
--   , (Σ g ꞉ (B → A) -- "g" = "inverse"
--     , (g ∘ f ∼ id)
--     × (f ∘ g ∼ id))
is-bijection' {A} {B} f = Σ g ꞉ (B → A) , (g ∘ f ∼ id) × (f ∘ g ∼ id) -- "g" = "inverse"

_≅'_ : Type → Type → Type
A ≅' B = Σ f ꞉ (A → B) , is-bijection' f -- "f" = "bijection"

-- Exercise 3

data 𝟚 : Type where
  𝟎 𝟏 : 𝟚

-- Prove that 𝟚 and Bool are isomorphic.
Bool-𝟚-isomorphism : Bool ≅ 𝟚
Bool-𝟚-isomorphism = record { bijection = f ; bijectivity = f-is-bijection }
  where
    f : Bool → 𝟚
    f false = 𝟎
    f true = 𝟏

    g : 𝟚 → Bool
    g 𝟎 = false
    g 𝟏 = true

    gf : g ∘ f ∼ id
    gf true = refl true
    gf false = refl false

    fg : f ∘ g ∼ id
    fg 𝟎 = refl 𝟎
    fg 𝟏 = refl 𝟏

    f-is-bijection : is-bijection f
    f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

-- Using pattern matching with agda is easier for solving. See: https://youtu.be/HhOTIOFyoZk?t=2131
-- May be harder to read though, since everything is anonymous.
Bool-𝟚-isomorphism' : Bool ≅ 𝟚
Bool-𝟚-isomorphism' =
  Isomorphism
    (λ { true → 𝟏 ; false → 𝟎 })
    (Inverse
      (λ { 𝟎 → false ; 𝟏 → true })
      (λ { true → refl true ; false → refl false })
      λ { 𝟎 → refl 𝟎 ; 𝟏 → refl 𝟏 })

-- Part III -- Finite Types

-- First definition
data Fin : ℕ → Type where
  zero : {n : ℕ} → Fin (suc n) -- "pt" in HoTT WS4
  suc : {n : ℕ} → Fin n → Fin (suc n) -- "i" in HoTT WS4

-- Exercise 4

-- Prove the elimination principle of Fin.
Fin-elim
  : (A : {n : ℕ} → Fin n → Type)
  → ({n : ℕ} → A {suc n} zero)
  → ({n : ℕ} (k : Fin n) → A k → A (suc k))
  → {n : ℕ} (k : Fin n) → A k
Fin-elim A a f = h
  where
    h : {n : ℕ} (k : Fin n) → A k
    h zero = a
    h (suc k) = f k (h k)

-- The other definition
Fin' : ℕ → Type
Fin' 0 = 𝟘
Fin' (suc n) = 𝟙 ∔ Fin' n

zero' : {n : ℕ} → Fin' (suc n)
zero' = inl ⋆

suc' : {n : ℕ} → Fin' n → Fin' (suc n)
suc' = inr

-- Exercise 5

-- Prove that Fin n and Fin' n are isomorphic for every n.
Fin-isomorphism : (n : ℕ) → Fin n ≅ Fin' n
Fin-isomorphism n = record {bijection = f n ; bijectivity = f-is-bijection n }
  where
    f : (n : ℕ) → Fin n → Fin' n
    f (suc n) zero = zero'
    f (suc n) (suc k) = suc' (f n k)

    g : (n : ℕ) → Fin' n → Fin n
    g (suc n) (inl ⋆) = zero
    g (suc n) (inr k) = suc (g n k)

    gf : (n : ℕ) → g n ∘ f n ∼ id
    gf (suc n) zero = refl zero
    gf (suc n) (suc k) = γ
      where
        IH : g n (f n k) ≡ k
        IH = gf n k

        γ =
          g (suc n) (f (suc n) (suc k)) ≡⟨ refl _ ⟩
          g (suc n) (suc' (f n k)) ≡⟨ refl _ ⟩
          suc (g n (f n k)) ≡⟨ ap suc IH ⟩
          suc k ∎

    fg : (n : ℕ) → f n ∘ g n ∼ id
    fg (suc n) (inl ⋆) = refl (inl ⋆)
    fg (suc n) (inr k) = γ
      where
        IH : f n (g n k) ≡ k
        IH = fg n k

        γ =
          f (suc n) (g (suc n) (suc' k)) ≡⟨ refl _ ⟩
          f (suc n) (suc (g n k)) ≡⟨ refl _ ⟩
          suc' (f n (g n k)) ≡⟨ ap suc' IH ⟩
          suc' k ∎

    f-is-bijection : (n : ℕ) → is-bijection (f n)
    f-is-bijection n = record { inverse = g n ; η = gf n ; ε = fg n }

Fin-isomorphism' : (n : ℕ) → Fin n ≅ Fin' n
Fin-isomorphism' =
  λ n →
    Isomorphism
      (λ { zero → inl ⋆ ; (suc x) → (suc' {!!})}) -- stuck because we can't use recursion
      (Inverse
        (λ x → {!zero!}) -- stuck because we can't use recursion
        (λ { zero → {!!} ; (suc x) → {!!}})
        {!!})

-- Part IV -- minimal elements in the natural numbers

-- Exercise 6

-- Give the recursive definition of the less than or equals relation on the natural numbers.
_≤₁_ : ℕ → ℕ → Type
0 ≤₁ y = 𝟙
suc x ≤₁ 0 = 𝟘
suc x ≤₁ suc y = x ≤₁ y

-- Exercise 7

-- Given a type family "P" over the naturals, a lower bound "n" is a natural number such that for all other naturals "m", we have that if P(m) holds, then n ≤₁ m.
-- Translate this definition into HoTT.
_≢_ : ℕ → ℕ → Type
x ≢ y = ¬ (x ≡ y)

is-lower-bound : (P : ℕ → Type) (n : ℕ) → Type
is-lower-bound P n = (m : ℕ) → (m ≢ n) → P m → (n ≤₁ m)

-- We define the type of minimal elements of a type family over the naturals.
minimal-element : (P : ℕ → Type) → Type
minimal-element P = Σ n ꞉ ℕ , (P n) × (is-lower-bound P n)

-- Exercise 8

-- Prove that all numbers are at least as large as zero.
leq-zero : (n : ℕ) → 0 ≤₁ n
leq-zero n = ⋆

--
-- The following exercises are too hard and weren't covered in problem session video.
--

-- Part V -- The well-ordering principle of ℕ

-- The well-ordering principle states that every non-empty set of natural numbers has a least element.
-- In HoTT, such subsets can be translated as being a decidable type family.

-- Decidability:
open import decidability
  using (is-decidable; is-decidable-predicate)
-- is-decidable is like the law of excluded middle (A ∔ ¬ A)

-- The well-ordering principle reads:
Well-ordering-principle
  = (P : ℕ → Type)
  → (d : is-decidable-predicate P)
  → (n : ℕ)
  → P n → minimal-element P

-- We shell prove this statement via induction on "n". In order to make the proof more readable, we first prove two lemmas.

-- Exercise 9

-- What is the statement of "is-minimal-element-suc" under the Curry-Howard interpretation?
-- Prove this lemma.
is-minimal-element-suc
  : (P : ℕ → Type) (d : is-decidable-predicate P)
  (m : ℕ) (pm : P (suc m))
  (is-lower-bound-m : is-lower-bound (λ x → P (suc x)) m)
  → ¬ (P 0) → is-lower-bound P (suc m)
is-minimal-element-suc P d zero p1 is-lower-bound neg-p0 m q pm = {!!}
is-minimal-element-suc P d (suc m) pm is-lower-bound neg-p0 = {!!}
