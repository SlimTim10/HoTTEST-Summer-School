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

  ∼-inv : (f g : (x : A) → B x) → (f ∼ g) → (g ∼ f)
  ∼-inv f g H x = sym (H x)

  ∼-concat
    : (f g h : (x : A) → B x)
    → f ∼ g
    → g ∼ h
    → f ∼ h
  ∼-concat f g h H K x = trans (H x) (K x)

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
is-bijection' {A} {B} f = Σ (a , b) ꞉ A × B
  , (Σ g ꞉ (B → A) -- "g" = "inverse"
    , (g ∘ f ∼ id)
    × (f ∘ g ∼ id))

_≅'_ : Type → Type → Type
A ≅' B = Σ (a , b) ꞉ A × B
  , (Σ f ꞉ (A → B) , is-bijection' f) -- "f" = "bijection"

-- Exercise 3

data 𝟚 : Type where
  𝟎 𝟏 : 𝟚

-- Prove that 𝟚 and Bool are isomorphic
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

-- Part III -- Finite Types
