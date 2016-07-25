{-# OPTIONS --type-in-type --copatterns --rewriting #-}
module PDTT.SoftCells where

open import PDTT.Basic public

--Here we have 'soft' bridges and paths:
--they contain a function and proofs that the function's endpoints are the bridge/path's endpoints.

record _$_⌢_ (A : El (ι 𝔹) → Set) (x : A b0) (y : A b1) : Set where
   constructor con
   field
     bridge : (i : El (ι 𝔹)) -> A i
     eq0 : bridge b0 ≡ x
     eq1 : bridge b1 ≡ y

record _⌢_ {A : Set} (x y : A) : Set where
   constructor con
   field
     bridge : El (ι 𝔹) -> A
     eq0 : bridge b0 ≡ x
     eq1 : bridge b1 ≡ y

theBridge : b0 ⌢ b1
_⌢_.bridge theBridge x = x
_⌢_.eq0 theBridge = refl
_⌢_.eq1 theBridge = refl


record _P─_ {A : El (ι 𝔹) → U} (x : El (ι (A b0)) )(y : El (ι (A b1))) : Set where
   constructor con
   field
     path : (i : I) -> El (=-elim A i)
     eq0 : path i0 ≡ x
     eq1 : path i1 ≡ y


record _─_ {A : Set} (x y : A) : Set where
   constructor con
   field
     path : I -> A
     eq0 : path i0 ≡ x
     eq1 : path i1 ≡ y

thePath : i0 ─ i1
_─_.path thePath = λ x → x
_─_.eq0 thePath  = refl
_─_.eq1 thePath  = refl

under : ∀ {A : Set}{x y : A} → x ─ y → x ⌢ y
_⌢_.bridge (under (con path eq0 eq1)) = λ x → path (ι x)
_⌢_.eq0 (under (con path eq0 eq1)) = eq0
_⌢_.eq1 (under (con path eq0 eq1)) = eq1

IsPath : ∀ {A : Set}{x y : A} → x ⌢ y → Set
IsPath b = Σ (_ ─ _) λ p → under p ≡ b

