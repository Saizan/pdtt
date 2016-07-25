{-# OPTIONS --type-in-type --copatterns --rewriting #-}
module PDTT.HardCells where

--this file contains hard cells: the endpoints are on the nose.

open import PDTT.Basic public
open import Function public

data DHBrid (A : El (ι 𝔹) → Set) : (x : A b0) (y : A b1) → Set where
  hbrid : (x : (i : El (ι 𝔹)) → A i) → DHBrid A (x b0) (x b1)
out-hbrid : ∀{A x y} → DHBrid A x y → (i : El (ι 𝔹)) → A i
out-hbrid (hbrid x) = x
out-hbrid0 : ∀{A x0 x1} → {x⌢ : DHBrid A x0 x1} → (out-hbrid x⌢ b0 ≡ x0)
out-hbrid0 {x⌢ = hbrid x} = refl
out-hbrid1 : ∀{A x0 x1} → {x⌢ : DHBrid A x0 x1} → (out-hbrid x⌢ b1 ≡ x1)
out-hbrid1 {x⌢ = hbrid x} = refl
{-# REWRITE out-hbrid0 #-}
{-# REWRITE out-hbrid1 #-}

HBrid : {A : Set} (x y : A) → Set
HBrid {A} x y = DHBrid (λ _ → A) x y

data DHPath (A : I → Set) : (x : A i0) (y : A i1) → Set where
  hpath : (x : (i : I) → A i) → DHPath A (x i0) (x i1)
h-unpath : ∀{A x y} → DHPath A x y → (i : I) → A i
h-unpath (hpath x) = x

HPath : {A : Set} (x y : A) → Set
HPath {A} x y = DHPath (λ _ → A) x y

data DHIsPath (A : I → Set) : ((i : El (ι 𝔹)) → A (ι i)) → Set where
  h-ispath : (x : (i : I) → A i) → DHIsPath A (x ∘ ι)
out-h-ispath : ∀{A x} → DHIsPath A x → ((i : I) → A i)
out-h-ispath (h-ispath x) = x
under-out-h-ispath : ∀{A x i} → {p : DHIsPath A x} → out-h-ispath p (ι i) ≡ x i
under-out-h-ispath {p = h-ispath x} = refl
{-# REWRITE under-out-h-ispath #-}

theHBridge : HBrid b0 b1
theHBridge = hbrid (λ i → i)

theHPath : HPath i0 i1
theHPath = hpath (λ i → i)

h-under : ∀{A : Set}{x y : A} → HPath x y → HBrid x y
h-under (hpath x) = hbrid (x ∘ ι)

⌢ap : {A : El (ι 𝔹) → Set} {B : (i : El (ι 𝔹)) → A i → Set} {f0 : (a : A b0) → B b0 a} {f1 : (a : A b1) → B b1 a}
  → (f⌢ : DHBrid (λ i → (a : A i) → B i a) f0 f1)
  → ((a0 : A b0)(a1 : A b1)(a⌢ : DHBrid A a0 a1) → DHBrid (λ i → B i (out-hbrid a⌢ i)) (f0 a0) (f1 a1))
⌢ap (hbrid f) _ _ (hbrid a) = hbrid (λ i → f i (a i))

postulate
  ⌢ext : {A : El (ι 𝔹) → Set} {B : (i : El (ι 𝔹)) → A i → Set} {f0 : (a : A b0) → B b0 a} {f1 : (a : A b1) → B b1 a}
    → ((a0 : A b0)(a1 : A b1)(a⌢ : DHBrid A a0 a1) → DHBrid (λ i → B i (out-hbrid a⌢ i)) (f0 a0) (f1 a1))
    → DHBrid (λ i → (a : A i) → B i a) f0 f1
  ⌢β : ∀{A B f0 f1 k} → ⌢ap {A}{B}{f0}{f1} (⌢ext {A}{B}{f0}{f1} k) ≡ k
  ⌢η : ∀{A B f0 f1 f⌢} → ⌢ext {A}{B}{f0}{f1} (⌢ap {A}{B}{f0}{f1} f⌢) ≡ f⌢

{-# REWRITE ⌢β #-}

ispath-ap : {A : I → Set} {B : (i : I) → A i → Set} {f : (i : El (ι 𝔹)) → (a : A (ι i)) → B (ι i) a}
  → (f-ispath : DHIsPath (λ i → (a : A i) → B i a) f)
  → (
    (a : (i : El (ι 𝔹)) → A (ι i)) → (a-ispath : DHIsPath A a) →
    DHIsPath (λ i → B i (out-h-ispath {A}{a} a-ispath i)) (λ i → f i (a i))
  )
ispath-ap (h-ispath f) _ (h-ispath a) = h-ispath (λ i → f i (a i))

postulate
  ispath-ext : ∀ {A : I → Set} → {B : (i : I) → A i → Set} → {f : (i : El (ι 𝔹)) → (a : A (ι i)) → B (ι i) a}
    → (
      (a : (i : El (ι 𝔹)) → A (ι i)) → (a-ispath : DHIsPath A a) →
      DHIsPath (λ i → B i (out-h-ispath {A}{a} a-ispath i)) (λ i → f i (a i))
    )
    → (DHIsPath (λ i → (a : A i) → B i a) f)
  ispath-β : ∀{A B f k} → ispath-ap {A}{B}{f} (ispath-ext {A}{B}{f} k) ≡ k
  ispath-η : ∀{A B f f-ispath} → ispath-ext {A}{B}{f} (ispath-ap {A}{B}{f} f-ispath) ≡ f-ispath
{-# REWRITE ispath-β #-}

