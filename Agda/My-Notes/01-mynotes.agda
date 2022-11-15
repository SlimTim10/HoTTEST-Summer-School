{-# OPTIONS --without-K --safe #-}
-- without-K is important for HoTT

-- https://www.youtube.com/watch?v=fJxWLQaaCX4

-- Type = Set
open import general-notation

data Bool : Type where
  true false : Bool

-- \to
not : Bool → Bool
not true = false
not false = true

not' : Bool → Bool
not' true = false
not' false = true

idBool : Bool → Bool
idBool x = x

idBool' : Bool → Bool
idBool' = λ (x : Bool) → x

-- The following is a Π type
id' : (X : Type) → X → X
id' X x = x

-- Implicit type
id : {X : Type} → X → X
id x = x

idBool'' : Bool → Bool
-- idBool'' = id' Bool
-- idBool'' = id' _
-- idBool'' = id {Bool}
idBool'' = id


-- "propositions as types" or "mathematical statements as types"
example : {P Q : Type} → P → (Q → P)
example {P} {Q} p = f
  where
    f : Q → P
    f _ = p

-- same as proof from HoTT lecture 1
-- https://www.youtube.com/watch?v=HvYYCHMeM-8
example' : {P Q : Type} → P → (Q → P)
example' p = λ q → p


open import binary-products

-- "x" is "and" in propositions as types
-- \times
ex : {P Q : Type} → P × Q → Q × P
ex (p , q) = (q , p)


-- \bN
data ℕ : Type where
  zero : ℕ
  suc : ℕ → ℕ

three : ℕ
three = suc (suc (suc zero))

{-# BUILTIN NATURAL ℕ #-}

-- synonym for the above
three' : ℕ
three' = 3


-- Dependent types
-- In Agda, dependent types are simply functions
D : Bool → Type
D true = ℕ
D false = Bool

-- "mix-fix" operator (3rd sense of "_" in Agda)
-- Without dependent types
if_then_else_ : {X : Type} → Bool → X → X → X
if true then x else y = x
if false then x else y = y

-- Generalization (with dependent types)
if[_]_then_else_
  : (X : Bool → Type)
  → (b : Bool)
  → X true
  → X false
  → X b
if[ X ] true then x else y = x
if[ X ] false then x else y = y

-- ∏ (b : Bool) (D b)
-- The two branches can have different types, thanks to dependent types
unfamiliar : (b : Bool) → D b
unfamiliar b = if[ D ] b then 3 else false


-- Another dependent type example, List
data List (A : Type) : Type where
  [] : List A -- empty list
  _::_ : A → List A → List A

-- List is a function (Type → Type)
ff : Type → Type
ff = List

-- Right-associative, precedence 10, so we don't need brackets
infixr 10 _::_

sample-list₀ : List ℕ
sample-list₀ = 0 :: 1 :: 2 :: []

length : {X : Type} → List X → ℕ
length [] = 0
length (x :: xs) = suc (length xs) -- this is allowed because xs is structurally smaller than the argument (x :: xs)


-- In HoTT (and MLTT), you don't have recursive definitions. The only thing you have is the elimination principles.

-- This is the only recursive definition in MLTT ever!
-- Principle of induction on ℕ
-- "In order to prove (∀n . A n) holds, you have to prove the base case and the induction step."
ℕ-elim
  : {A : ℕ → Type}
  → A 0 -- base case
  → ((k : ℕ) → A k → A (suc k)) -- induction step
  → (n : ℕ) → A n
ℕ-elim {A} a₀ f = h
  where
    h : (n : ℕ) → A n
    h zero = a₀
    h (suc n) = f n IH
      where
        -- induction hypothesis (assume that the hypothesis holds for n)
        IH : A n
        IH = h n -- recursion!

-- Every other recursion in MLTT has to be done by calling the elimination principle.

ℕ-elim'
  : {A : ℕ → Type}
  → A 0 -- base case
  → ((k : ℕ) → A k → A (suc k)) -- induction step
  → (n : ℕ) → A n
ℕ-elim' {A} a₀ f zero = a₀
ℕ-elim' {A} a₀ f (suc n) = f n (ℕ-elim' a₀ f n)

List-elim
  : {X : Type} (A : List X → Type)
  → A []
  → ((x : X) (xs : List X) → A xs → A (x :: xs))
  → (xs : List X) → A xs
List-elim {X} A a f = h
  where
    h : (xs : List X) → A xs
    h [] = a
    -- h (x :: xs) = f x xs (h xs)
    h (x :: xs) = f x xs IH
      where
        IH : A xs
        IH = h xs

-- Exercise: Try to define the length function using List-elim (instead of explicit recursion)

length' : {X : Type} → List X → ℕ
length' [] = 0
-- length' (x :: xs) = ℕ-elim {λ _ → ℕ} 1 (λ k _ → suc k) 0
length' {X} (x :: xs) = List-elim {X} (λ _ → ℕ) 1 (λ _ _ y → y) xs
-- Is this correct???


-- Acts like false
-- \b0
data 𝟘 : Type where

-- Acts like true
-- \b1, \star
data 𝟙 : Type where
  ⋆ : 𝟙

_≣_ : ℕ → ℕ → Type
zero ≣ zero = 𝟙
zero ≣ suc y = 𝟘
suc x ≣ zero = 𝟘
suc x ≣ suc y = x ≣ y

infix 0 _≣_

ℕ-refl : (x : ℕ) → x ≣ x
ℕ-refl zero = ⋆
ℕ-refl (suc x) = ℕ-refl x

_+_ : ℕ → ℕ → ℕ
zero + y = y
suc x + y = suc (x + y) -- (1 + x) + y = 1 + (x + y)

_++_ : {A : Type} → List A → List A → List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

lh
  : {X : Type} (xs ys : List X)
  → length (xs ++ ys) ≣ length xs + length ys
lh [] ys = ℕ-refl (length ys)
lh (x :: xs) ys = IH
  where
    IH : length (xs ++ ys) ≣ (length xs + length ys)
    IH = lh xs ys

-- length ((x :: xs) ++ ys) ≣ (length (x :: xs) + length ys)
-- suc (length (xs ++ ys)) ≣ suc (length xs) + length ys
-- suc (length (xs ++ ys)) ≣ suc (length xs + length ys)
-- length (xs ++ ys) ≣ length xs + length ys
