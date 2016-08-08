{-# OPTIONS --type-in-type --copatterns --rewriting #-}
module PDTT.Basic where

open import Relation.Binary.PropositionalEquality public
open import Data.Product public
{-# BUILTIN REWRITE _≡_ #-}

postulate
  U : Set
  `U : U
  _⁼ : Set -> Set
  El : U ⁼ -> Set

El⁼ : _ -> _
El⁼ = λ x → (El x) ⁼


postulate
  ι : ∀ {A} → A → A ⁼
  =-elim : ∀ {A}{B : A ⁼ → Set} → ((x : A) → B (ι x)) → (x : A ⁼) → (B x) ⁼

  =-beta : ∀ {A B} f a → =-elim {A} {B} f (ι a) ≡ ι (f a)

postulate
  `U-El : El (ι `U) ≡ U

{-# REWRITE `U-El #-}
{-# REWRITE =-beta #-}

postulate
  `Π : (A : U) → (B : El (ι A) → U) → U
  `Π-El : ∀ {A B} → El (ι (`Π A B)) ≡ ((x : El (ι A)) → El (ι (B x)))

  `∀ : (A : U) → (B : El (ι A) → U) → U
  `∀-El : ∀ {A : U}{B : El (ι A) → U} → El (ι (`∀ A B)) ≡ ((x : El⁼ (ι A)) → El (=-elim B x))

syntax `Π A (λ a → B) = `Π[ a ∈ A ] B
syntax `∀ A (λ a → B) = `∀[ a ∈ A ] B

_`→_ : (A B : U) → U
A `→ B = `Π[ _ ∈ A ] B

{-# REWRITE `Π-El #-}
{-# REWRITE `∀-El #-}


postulate
  ∫ : Set → Set
  σ : ∀ {A} → A → ∫ A
  ∫∫-elim : ∀ {A}{B : ∫ A → Set} → ((x : A) → B (σ x)) → (x : ∫ A ) → ∫ (B x)
  -- shouldnt we write A → ∫ B?
  ∫-elim : ∀ {A}{B : ∫ A → U ⁼} → ((x : A) → El (B (σ x))) → (x : ∫ A ) → El (B x)
  ∫-beta : ∀ {A B} f a → ∫-elim {A} {B} f (σ a) ≡ f a

  ∫∫-beta : ∀ {A B} f a → ∫∫-elim {A} {B} f (σ a) ≡ σ (f a)

  `Σ : (A : U) → (B : El (ι A) → U) → U
  `Σ-El : ∀ {A B} → El (ι (`Σ A B)) ≡ Σ (El (ι A)) λ x → El (ι (B x))

  `∃ : (A : U) → (B : El (ι A) → U) → U
  `∃-El : ∀ {A B} → El (ι (`∃ A B)) ≡ (∫ (Σ (El⁼ (ι A)) (λ x → El (=-elim B x))))

syntax `Σ A (λ a → B) = `Σ[ a ∈ A ] B
syntax `∃ A (λ a → B) = `∃[ a ∈ A ] B


{-# REWRITE `Σ-El #-}
{-# REWRITE `∃-El #-}
{-# REWRITE ∫-beta #-}
{-# REWRITE ∫∫-beta #-}

postulate
  𝔹 : U
  b0 b1 : El (ι 𝔹)

I = El (ι 𝔹) ⁼

i0 = ι b0
i1 = ι b1

postulate
  ⌢-univ : ∀ {A B} → (f : El (ι A) → El (ι B)) → El (ι 𝔹) → U
  ⌢-univb0 : ∀ {A B} → (f : El (ι A) → El (ι B)) → ⌢-univ {A} {B} f b0 ≡ A
  ⌢-univb1 : ∀ {A B} → (f : El (ι A) → El (ι B)) → ⌢-univ {A} {B} f b1 ≡ B

{-# REWRITE   ⌢-univb0 #-}
{-# REWRITE   ⌢-univb1 #-}

open import Data.Unit

postulate
 `⊤ : U
 `⊤-El : El (ι `⊤) ≡ ⊤

{-# REWRITE `⊤-El #-}

open import Data.Bool

postulate
 `Bool : U
 `Bool-El : El (ι `Bool) ≡ Bool

{-# REWRITE `Bool-El #-}

open import Data.Nat
postulate
 `ℕ : U
 `ℕ-El : El (ι `ℕ) ≡ ℕ
 _`≡_ : {A : U ⁼} → El A → El A → U
 `≡-El : ∀ {X A B} → El (ι (_`≡_ {A = X} A B)) ≡ (A ≡ B)

{-# REWRITE `ℕ-El #-}
{-# REWRITE `≡-El #-}
