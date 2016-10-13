{-# OPTIONS --copatterns --rewriting  #-}

module ParamDTT where

open import Data.Product
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Function
{-# BUILTIN REWRITE _≡_ #-}

{-
  The idea is to represent contexts by making them empty using λ-abstraction.
  Changes in contexts will be represented by applying their right adjoint to the type.

  We think of Set as U^Psh, the cloesd type whose terms correspond directly to types in the same context.
-}

postulate
  funext : {A : Set } {B : A → Set} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g

--=============================================
--CONTEXT MODIFICATIONS AND THEIR RIGHT ADJOINT
--=============================================

postulate
  {-
    T : Γ → Set means Γ ⊢ T type.
    Then λ γ → # T γ : Γ → Set means Γ ⊢ (#T)[ι] type
  -}
  #_ : Set → Set

{-
  Assume T : Γ → Set, i.e. Γ ⊢ T type
  t : (γ : Γ) → # T γ means Γ ⊢ t : # T [ι], which is in correspondence with ♭ Γ (≅ Γ ⁰) ⊢ t' : T [κ]
  Thus, we can think of t : (γ : Γ) → ♭⊢ (T γ) as ♭ Γ ⊢ t : T
-}
♭⊢_ : Set → Set
♭⊢ T = # T

postulate
  --T : Γ → ¶Set means Γ ⊢ T : ¶ U^Psh
  ¶Set : Set
  --This is #Γ ⊢ U^Psh : U^Psh
  --¶Set-in-¶Set : ¶Set

--Think of T : Γ → #⊢Set as # Γ ⊢ T type
#⊢Set : Set
#⊢Set = ¶Set

--#⊢[#⊢Set] : #⊢Set
--#⊢[#⊢Set] = ¶Set-in-¶Set

postulate
  {-
    T : Γ → ¶Set means #Γ ⊢ T type
    Then λ γ → ¶ T γ : Γ → Set means Γ ⊢ (¶ T)[ι] type
  -}
  ¶_ : ¶Set → Set

{-
  Assume T : Γ → #⊢Set, i.e. # Γ ⊢ T type.
  Then we can consider # Γ ⊢ t : T or equivalently Γ ⊢ t' : (¶T)[ι], which we encode as t : (γ : Γ) → #⊢ T.
-}
#⊢_ : #⊢Set → Set
#⊢_ T = ¶ T

infix 10 #_ ♭⊢_ ¶_ #⊢_

postulate
  ## : ∀{A} → # # A ≡ # A
  #¶ : ∀{A} → # ¶ A ≡ ¶ A
  --¶# : ∀{A} → ¶ # A ≡ # A
{-# REWRITE ## #-}
{-# REWRITE #¶ #-}
♭♭⊢ : ∀{A} → ♭⊢ ♭⊢ A ≡ ♭⊢ A
♭♭⊢ {A} = refl
#♭⊢ : ∀{A} → ♭⊢ #⊢ A ≡ #⊢ A
#♭⊢ {A} = refl

--==============================================
--SUBSTITUTIONS AND THEIR TYPE-SIDE COUNTERPARTS
--==============================================

postulate
  ι_ : ∀{T} → T → # T

_[κ] : ∀{T} → T → ♭⊢ T
t [κ] = ι t

postulate
  Setϑ_ : ¶Set → Set
  --SetϑSet : Setϑ ¶Set-in-¶Set ≡ ¶Set
--{-# REWRITE SetϑSet #-}

_Set[ι] : #⊢Set → Set
T Set[ι] = Setϑ T
--SetSet[ι] : #⊢[#⊢Set] Set[ι] ≡ #⊢Set
--SetSet[ι] = refl

postulate
  --This is ϑ^[ι]
  ϑ_ : ∀{T} → ¶ T → Setϑ T

_[ι] : ∀{T} → #⊢ T → T Set[ι]
t [ι] = ϑ t

postulate
  ι# : ∀{T} → ι_ {# T} ≡ id
{-# REWRITE ι# #-}
[κ♭] : ∀{T} → _[κ] {♭⊢ T} ≡ id
[κ♭] = refl

--=============
--APPLICATIVITY
--=============
{-
  Because # and ¶ correspond to modifications to the context, we can allow function type construction and function application
-}

postulate
  _¶→Set : (A : ¶Set) → ¶Set
  Π¶ : (A : ¶Set) → (B : ¶ (A ¶→Set)) → ¶Set

_#⊢→Set : (A : #⊢Set) → #⊢Set
A #⊢→Set = A ¶→Set
  
#⊢Π : (A : #⊢Set) → (B : #⊢ (A #⊢→Set)) → #⊢Set
#⊢Π A B = Π¶ A B

postulate
  ap# : {A : Set} → (B : # A → Set) → # ((a : A) → B (ι a)) → (a : # A) → # (B a)
  ap¶Set : {A : ¶Set} → ¶(A ¶→Set) → ¶ A → ¶Set
  ap¶ : {A : ¶Set} → (B : ¶ (A ¶→Set)) → ¶ (Π¶ A B) → (a : ¶ A) → ¶ (ap¶Set B a)

♭⊢ap : {A : Set} → (B : ♭⊢ A → Set) → ♭⊢ ((a : A) → B (a [κ])) → (a : ♭⊢ A) → ♭⊢ (B a)
♭⊢ap B f a = ap# B f a
#⊢apSet : {A : #⊢Set} → #⊢ (A #⊢→Set) → #⊢ A → #⊢Set
#⊢apSet F a = ap¶Set F a
#⊢ap : {A : #⊢Set} → (B : #⊢ (A #⊢→Set)) → #⊢ (#⊢Π A B) → (a : #⊢ A) → #⊢ (#⊢apSet B a)
#⊢ap B f a = ap¶ B f a

postulate
  --If B (ι a) itself happens to be sharp, this rule makes ι disappear altogether
  ap#ι : {A : Set} → {B : # A → Set} → (f : (a : A) → B (ι a)) → (a : A) → ap# B (ι f) (ι a) ≡ (ι (f a))
{-# REWRITE ap#ι #-}

--WHAT IS NEEDED TO MAKE ¶ WORK?

--=====================
--PATH AND BRIDGE TYPES
--=====================

postulate
  --The type of paths in U^Psh
  PaSet : Set
  BrSet : Set
  Pa : PaSet → Set
  Br : BrSet → Set
  
postulate
  _*Refl : Set → PaSet
  _*Under : PaSet → BrSet
  _*Src : BrSet → Set
  _*Tgt : BrSet → Set
  *Refl*Under*Src : ∀{A} → A *Refl *Under *Src ≡ A
  *Refl*Under*Tgt : ∀{A} → A *Refl *Under *Tgt ≡ A
{-# REWRITE *Refl*Under*Src #-}
{-# REWRITE *Refl*Under*Tgt #-}

postulate
  _*refl : ∀{T} → T → Pa (T *Refl)
  _*under : ∀{T} → Pa T → Br (T *Under)
  _*src : ∀{T} → Br T → T *Src
  _*tgt : ∀{T} → Br T → T *Tgt
  *refl*under*src : ∀{T} → {t : T} → t *refl *under *src ≡ t
  *refl*under*tgt : ∀{T} → {t : T} → t *refl *under *tgt ≡ t
{-# REWRITE *refl*under*src #-}
{-# REWRITE *refl*under*tgt #-}

infix 10 _*Refl _*Under _*Src _*Tgt _*refl _*under _*src _*tgt

postulate
  _Br→Set : (A : BrSet) → BrSet
  _Pa→Set : (A : PaSet) → PaSet
  ΠBr : (A : BrSet) → (B : Br (A Br→Set)) → BrSet
  ΠPa : (A : PaSet) → (B : Pa (A Pa→Set)) → PaSet

postulate
  apBrSet : {A : BrSet} → Br(A Br→Set) → Br A → BrSet
  apBr : {A : BrSet} → (B : Br (A Br→Set)) → Br (ΠBr A B) → (a : Br A) → Br (apBrSet B a)

--NOW WHAT IF YOU HAVE TWO BRIDGES IN THE CONTEXT!?
