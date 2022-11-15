{-# OPTIONS --without-K --allow-unsolved-metas #-}

open import prelude
open import decidability
open import sums

-- Part I: Propositions as types

-- Exercise 1

uncurry : {A B X : Type} → (A → B → X) → (A × B → X)
uncurry f (a , b) = f a b

curry : {A B X : Type} → (A × B → X) → (A → B → X)
curry f a b = f (a , b)

-- Exercise 2

[i] : {A B C : Type} → (A × B) ∔ C → (A ∔ C) × (B ∔ C)
[i] (inl (a , b)) = inl a , inl b
[i] (inr c) = inr c , inr c

[ii] : {A B C : Type} → (A ∔ B) × C → (A × C) ∔ (B × C)
[ii] (inl a , c) = inl (a , c)
[ii] (inr b , c) = inr (b , c)

-- review this
[iii] : {A B : Type} → ¬ (A ∔ B) → ¬ A × ¬ B
-- [iii] nab = (λ a → nab (inl a)) , λ a → nab (inr a)
pr₁ ([iii] f) a = f (inl a)
pr₂ ([iii] f) b = f (inr b)

-- not provable because we can't make an element of the empty type
-- [iv] : {A B : Type} → ¬ (A × B) → ¬ A ∔ ¬ B
-- [iv] nab = {!!}

[v] : {A B : Type} → (A → B) → ¬ B → ¬ A
[v] f g a = g (f a)

-- not provable because we can't make an element of the empty type
-- [vi] : {A B : Type} → (¬ A → ¬ B) → B → A
-- [vi] nab b = {!!}

-- not provable because we can't produce an element of type B
-- [vii] : {A B : Type} → ((A → B) → A) → A
-- [vii] f = f (λ a → {!!})

[viii]
  : {A : Type} {B : A → Type}
  → ¬ (Σ a ꞉ A , B a)
  → (a : A)
  → ¬ B a
[viii] f a bₐ = f (a , bₐ)

-- not provable because we can't produce an element of type A
-- [ix]
--   : {A : Type} {B : A → Type}
--   → ¬ ((a : A) → B a)
--   → (Σ a ꞉ A , ¬ B a)
-- [ix] f = {!!} , {!!}

-- review this
[x]
  : {A B : Type} {C : A → B → Type}
  → ((a : A) → (Σ b ꞉ B , C a b))
  → Σ f ꞉ (A → B) , ((a : A) → C a (f a))
-- [x] f = (λ a → pr₁ (f a)) , λ a → pr₂ (f a)
pr₁ ([x] f) a = pr₁ (f a)
pr₂ ([x] f) a = pr₂ (f a)

-- Exercise 3

¬¬_ : Type → Type
¬¬ A = ¬ (¬ A)

¬¬¬ : Type → Type
¬¬¬ A = ¬ (¬¬ A)

tne : ∀ {A : Type} → ¬¬¬ A → ¬ A
tne f a = f (λ g → g a)

-- Exercise 4

¬¬-functor : {A B : Type} → (A → B) → ¬¬ A → ¬¬ B
-- ¬¬-functor f g h = g (λ a → h (f a))
¬¬-functor f = [v] ([v] f)

¬¬-kleisli : {A B : Type} → (A → ¬¬ B) → ¬¬ A → ¬¬ B
-- ¬¬-kleisli f g h = g (λ a → f a h)
-- ¬¬-kleisli f nna nb = tne (λ z → z (λ z₁ → nna (λ z₂ → z₁ z₂ nb))) f
¬¬-kleisli f g = tne (¬¬-functor f g)

-- Part II: _≡_ for Bool

-- Exercise 1

bool-as-type : Bool → Type
bool-as-type true = 𝟙
bool-as-type false = 𝟘

-- Exercise 2

-- review this
bool-≡-char₁ : ∀ (b b' : Bool) → b ≡ b' → (bool-as-type b ⇔ bool-as-type b')
-- bool-≡-char₁ b b (refl b) = id , id
bool-≡-char₁ b b (refl b) = ⇔-refl
  where
    ⇔-refl : {X : Type} → X ⇔ X
    -- ⇔-refl = (λ x → x) , (λ x → x)
    (pr₁ ⇔-refl) x = x
    (pr₂ ⇔-refl) x = x

-- Exercise 3

-- review this syntax
true≢false : ¬ (true ≡ false)
-- true≢false ()
-- true≢false b = pr₁ (bool-≡-char₁ true false b) ⋆
true≢false b = bool-≡-char₁ true false b .pr₁ ⋆

-- Exercise 4

-- review this
bool-≡-char₂ : ∀ (b b' : Bool) → (bool-as-type b ⇔ bool-as-type b') → b ≡ b'
bool-≡-char₂ true true (l , r) = refl true
bool-≡-char₂ true false (l , r) = 𝟘-elim (l ⋆)
bool-≡-char₂ false true (l , r) = 𝟘-elim (r ⋆)
bool-≡-char₂ false false (l , r) = refl false

-- Part III: HoTT

has-bool-dec-fct : Type → Type
has-bool-dec-fct A = Σ f ꞉ (A → A → Bool) , (∀ x y → x ≡ y ⇔ (f x y) ≡ true)

-- too difficult
decidable-equality-char : (A : Type) → has-decidable-equality A ⇔ has-bool-dec-fct A
-- decidable-equality-char A = (λ f → (λ a a' → true) , λ x y → (λ _ → refl true) , λ p → {!!}) , λ g → λ x y → {!!}
-- decidable-equality-char A = (λ f → (λ _ _ → true) , λ x y → (λ _ → refl true) , λ t → {!f x y!}) , λ g → λ x y → {!!}
pr₁ (decidable-equality-char A) discA = f , f-dec
  where
    f' : (x y : A) → (x ≡ y) ∔ (x ≡ y → 𝟘) → Bool
    -- f' x y = ∔-nondep-elim (λ _ → true) (λ _ → false)
    f' x y (inl _) = true
    f' x y (inr _) = false
    
    f : A → A → Bool
    f x y = f' x y (discA x y)
    
    f-dec : (x y : A) → x ≡ y ⇔ (f x y) ≡ true
    f-dec x y = (λ p → {!!}) , {!!}
    -- pr₁ (f-dec x .x) (refl .x) = {!!}
    -- pr₂ (f-dec x y) p = {!!}
    
pr₂ (decidable-equality-char A) = {!!}
