{-# OPTIONS --type-in-type --copatterns --rewriting #-}
module PDTT where

open import PDTT.Basic public
open import PDTT.SoftCells public
open import Data.Unit
open import Data.Bool
open import Data.Nat

--THIS FILE IS A MESS. NEEDS CLEANUP.


-- postulate
--   path-ext : {A : El (ι 𝔹) → U} (let A0 = El (ι (A b0)); A1 = El (ι (A b1)))
--               {α : A0 → A0} {β : A1 → A1}
-- A path between functions (over a bridge),
-- is iso to (a map from bridges to bridges that sends paths to paths) (over the functions) (over the bridge)



postulate
  push : ∀ {A B} → (f : El (ι A) → El (ι B)) → (i : I) → (a : El (ι A)) → El (=-elim (⌢-univ {A} {B} f) i)
  pushi0 : ∀ {A B} (f : El (ι A) → El (ι B)) → (a : El (ι A)) → push {A} {B} f i0 a ≡ a
  pushi1 : ∀ {A B} (f : El (ι A) → El (ι B)) → (a : El (ι A)) → push {A} {B} f i1 a ≡ f a

  pull : ∀ {A B} → (f : El (ι A) → El (ι B)) → (i : I) → El (=-elim (⌢-univ {A} {B} f) i) → El (ι B)
  pulli0 : ∀ {A B} (f : El (ι A) → El (ι B)) x → pull {A} {B} f i0 x ≡ f x
  pulli1 : ∀ {A B} (f : El (ι A) → El (ι B)) x → pull {A} {B} f i1 x ≡ x

{-# REWRITE pushi0 #-}
{-# REWRITE pushi1 #-}
{-# REWRITE pulli0 #-}
{-# REWRITE pulli1 #-}


id : (X : U ⁼) → El X → El X
id _ x = x

postulate
  lemma : ∀ (Y : U ⁼) → El (=-elim (λ X → (X `→ X)) Y) ≡ ((x : El Y) -> El Y)

{-# REWRITE lemma #-}
paired-param-id : (Y : U ⁼) → El (ι (`∃[ X ∈ `U ] (X `→ X)))
paired-param-id Y = σ (Y , id Y )

paired-param-id-paths : ∀ {A B} → (f : El (ι A) → El (ι B)) → paired-param-id (ι A) ─ paired-param-id (ι B)
_─_.path (paired-param-id-paths {A} {B} f) i = paired-param-id (=-elim ((⌢-univ {A} {B} f)) i)
_─_.eq0 (paired-param-id-paths {A} {B} f) = refl
_─_.eq1 (paired-param-id-paths {A} {B} f) = refl


paired-param-id-paths' : {A B : U} → (El (ι A) → El (ι B)) → σ (ι A , (λ x → x)) ─ σ (ι B , (λ x → x))
paired-param-id-paths' = paired-param-id-paths

module IsId (f : (X : U ⁼) → El X → El X) (A : U) (a : El (ι A)) where

  g : ⊤ → El (ι A)
  g _ = a

  X : El (ι 𝔹) → U
  X = ⌢-univ {`⊤} {A} g

  isid : a ─ f (ι A) a
  _─_.path isid = λ i → pull {`⊤} {A} g i (f (=-elim X i) (push {`⊤} {A} g i tt))
  _─_.eq0 isid = refl
  _─_.eq1 isid = refl

open import Data.Sum
module IsBool' (f : (X : U ⁼) → El X → El X -> El X) (A : U) (a b : El (ι A)) where

  g : Bool → El (ι A)
  g false = a
  g true = b

  X = ⌢-univ {`Bool} {A} g

  isbool' : g (f (ι `Bool) false true) ─ f (ι A) a b
  _─_.path isbool' = λ i → pull {`Bool} {A} g i (f (=-elim X i) (push {`Bool} {A} g i false) (push {`Bool} {A} g i true))
  _─_.eq0 isbool' = refl
  _─_.eq1 isbool' = refl

module IsBool (f : (X : U ⁼) → El X → El X -> El X) (A : U) where
  open IsBool' f A

  isbool : (∀ a b → a ─ f (ι A) a b) ⊎ (∀ a b → b ─ f (ι A) a b)
  isbool with (f (ι `Bool) false true) | isbool'
  isbool | false | f-is-a = inj₁ f-is-a
  isbool | true  | f-is-b = inj₂ f-is-b

{-
--bridges
⌢ap : {A : El (ι 𝔹) → Set} {B : (i : El (ι 𝔹)) → A i → Set} {f0 : (a : A b0) → B b0 a} {f1 : (a : A b1) → B b1 a}
  → (f⌢ : (λ i → (a : A i) → B i a) $ f0 ⌢ f1) → {a0 : A b0}{a1 : A b1}(a⌢ : A $ a0 ⌢ a1)
  → (λ i → B i (_$_⌢_.bridge a⌢ i)) $ {!!} ⌢ {!!}
⌢ap = {!!}
{-
⌢ap : {A : El (ι 𝔹) → Set} {B : (i : El (ι 𝔹)) → A i → Set} (f : (i : El (ι 𝔹)) → (a : A i) → B i a)
  → (x : (i : El (ι 𝔹)) → A i) → ((i : El (ι 𝔹)) → B i (x i))
⌢ap {A}{B} f x i = f i (x i)
-}

postulate
  ⌢ext : {A : El (ι 𝔹) → Set} {B : (i : El (ι 𝔹)) → A i → Set} (f0 : (a : A b0) → B b0 a) (f1 : (a : A b1) → B b1 a)
    → {!!}
-}

{-
module IsNat (f : (X : U ⁼) → El X → (El X -> El X) -> El X) (A : U) (a0 : El (ι A)) (as : El (ι A) → El (ι A)) where

  g : ℕ → El (ι A)
  g zero = a0
  g (suc n) = as (g n)

  ImG : U
  ImG = `Σ `ℕ (λ n → `Σ A λ a → _`≡_ {ι A} (g n) a)

  p1 : El (ι ImG) -> ℕ
  p1 (n , _) = n

  p2 : El (ι ImG) -> El (ι A)
  p2 (n , a , _) = a

  img0 : El (ι ImG)
  img0 = 0 , (a0 , refl)
  img1 : El (ι ImG) → El (ι ImG)
  img1 (n , _ , refl) = (suc n , _ , refl)

  postulate
    foo2 : p2 (f (ι ImG) img0 img1) ─ f (ι A) a0 as
    foo1 : p1 (f (ι ImG) img0 img1) ─ f (ι `ℕ) zero suc
-}
