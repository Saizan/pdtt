{-# OPTIONS --copatterns --rewriting --no-positivity-check  #-}

module Postulates4 where

open import Data.Product
open import Data.Nat
open import Data.Unit
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function renaming (id to idf ; _∘_ to _f∘_)
{-# BUILTIN REWRITE _≡_ #-}

postulate
  funext : {A : Set } {B : A → Set} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g

--=================================
--CONTEXTS, SUBSTITUTIONS AND TYPES
--=================================

postulate
  Var : Set -- set of variables; if you prefer to ignore variables, think of this as Unit
  IVar : Set -- same, but for the interval
  CtxVar : Set -- set of context variables.
  AbsTy : CtxVar → Set -- Think of this as TyDisc(Ω)
  AbsTm : (Φ : CtxVar) → (T : AbsTy Φ) → Set -- Think of this as the set of terms Ω ⊢ T
  AbsTm# : (Φ : CtxVar) → (T : AbsTy Φ) → Set -- Think of this as the set of terms Ω ⊢ T^#
  Abs𝔹 : CtxVar → Set -- Think of this as the set of presheaf maps Ω → 𝔹
  Absℙ : CtxVar → Set -- Think of this as the set of presheaf maps Ω → # 𝔹
  absι : ∀{Φ T} → AbsTm Φ T → AbsTm# Φ T
  absunder : ∀{Φ} → Abs𝔹 Φ → Absℙ Φ
  abs0 abs1 : ∀{Φ} → Abs𝔹 Φ
  --_t⊥t_ : ∀{Φ S T} → AbsTm# Φ S → AbsTm# Φ T → Set
  _t⊥i_ : ∀{Φ T} → AbsTm# Φ T → Absℙ Φ → Set
  _i⊥i_ : ∀{Φ} → (i j : Absℙ Φ) → Set
  --t⊥t-sym : ∀{Φ S T} → {s : AbsTm# Φ S} → {t : AbsTm# Φ T} → s t⊥t t → t t⊥t s
  i⊥i-sym : ∀{Φ} → {i j : Absℙ Φ} → i i⊥i j → j i⊥i i

_i⊥t_ : ∀{Φ T} → Absℙ Φ → AbsTm# Φ T → Set
i i⊥t t = t t⊥i i

data Ctx : Set
data AbsSub (Φ : CtxVar) : Ctx → Set
--_⊥t_ : ∀{Φ Γ T} → (γ : AbsSub Φ Γ) → (t : AbsTm# Φ T) → Set
_⊥i_ : ∀{Φ Γ} → (γ : AbsSub Φ Γ) → (i : Absℙ Φ) → Set
--_⊥_ : ∀{Φ Γ Δ} → (γ : AbsSub Φ Γ) → (δ : AbsSub Φ Δ) → Set

Ty : Ctx → Set
Ty Γ = (Φ : CtxVar) → (γ : AbsSub Φ Γ) → AbsTy Φ

data Ctx where
  • : Ctx --\bu
  _„_∈_♭ : (Γ : Ctx) → Var → (T : Ty Γ) → Ctx
  _„_∈_# : (Γ : Ctx) → Var → (T : Ty Γ) → Ctx
  _!_∈𝔹 : (Γ : Ctx) → IVar → Ctx
  _!_∈ℙ : (Γ : Ctx) → IVar → Ctx

data AbsSub Φ where
  • : AbsSub Φ •
  _“_♭∋_/_ : {Γ : Ctx} → (γ : AbsSub Φ Γ) → (T : Ty Γ) → (t : AbsTm Φ (T Φ γ)) → (x : Var) → AbsSub Φ (Γ „ x ∈ T ♭)
  _“_#∋_/_ : {Γ : Ctx} → (γ : AbsSub Φ Γ) → (T : Ty Γ) → (t : AbsTm# Φ (T Φ γ)) → (x : Var) → AbsSub Φ (Γ „ x ∈ T #)
  _!_/_∈𝔹[_] : {Γ : Ctx} → (γ : AbsSub Φ Γ) → (β : Abs𝔹 Φ) → (i : IVar) → (γ ⊥i absunder β) → AbsSub Φ (Γ ! i ∈𝔹)
  _!_/_∈ℙ[_] : {Γ : Ctx} → (γ : AbsSub Φ Γ) → (β : Absℙ Φ) → (i : IVar) → (γ ⊥i β) → AbsSub Φ (Γ ! i ∈ℙ)

{-
_⊥t_ {Γ = •} γ t = ⊤
_⊥t_ {Γ = Γ „ .x ∈ .S ♭} (γ “ S ♭∋ s / x) t = (γ ⊥t t) × (absι s t⊥t t)
_⊥t_ {Γ = Γ „ .x ∈ .S #} (γ “ S #∋ s / x) t = (γ ⊥t t) × (s t⊥t t)
_⊥t_ {Γ = .i ∈𝔹} (i* / i ∈𝔹) t = absunder i* i⊥t t
_⊥t_ {Γ = .i ∈ℙ} (i* / i ∈ℙ) t = i* i⊥t t
_⊥t_ {Γ = Γ ! Δ} (γ ¡ δ [ p ]) t = (γ ⊥t t) × (δ ⊥t t)

-}

_⊥i_ {Γ = •} γ j = ⊤
_⊥i_ {Γ = Γ „ .x ∈ .S ♭} (γ “ S ♭∋ s / x) j = (γ ⊥i j) × (absι s t⊥i j)
_⊥i_ {Γ = Γ „ .x ∈ .S #} (γ “ S #∋ s / x) j = (γ ⊥i j) × (s t⊥i j)
_⊥i_ {Γ = Γ ! .i ∈𝔹} (γ ! β / i ∈𝔹[ _ ]) j = (γ ⊥i j) × (absunder β i⊥i j)
_⊥i_ {Γ = Γ ! .i ∈ℙ} (γ ! β / i ∈ℙ[ x ]) j = (γ ⊥i j) × (β i⊥i j)

--_⊥_ {Φ}{Γ}{Δ} γ δ = {!!}

infix 10 _“_#∋_/_ _“_♭∋_/_
infix 8 _„_∈_♭ _„_∈_#
