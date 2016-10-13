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

data Variance : Set where
  # : Variance
  ♭ : Variance

data Endpoint : Set where
  src : Endpoint
  tgt : Endpoint

postulate
  Var : Set -- set of variables; if you prefer to ignore variables, think of this as Unit
  IVar : Set -- same, but for the interval
  CtxVar : Set -- set of context variables.
  AbsTy : CtxVar → Set -- Think of this as TyDisc(#Ω)
  AbsTm : (Φ : CtxVar) → (T : AbsTy Φ) → Set -- Think of this as the set of terms Ω ⊢ T
  AbsTm# : (Φ : CtxVar) → (T : AbsTy Φ) → Set -- Think of this as the set of terms Ω ⊢ T^# or ♭Ω ⊢ T
  Abs𝔹 : CtxVar → Set -- Think of this as the set of presheaf maps Ω → 𝔹
  Absℙ : CtxVar → Set -- Think of this as the set of presheaf maps Ω → # 𝔹
  absι : ∀{Φ T} → AbsTm Φ T → AbsTm# Φ T
  absu : ∀{Φ} → Abs𝔹 Φ → Absℙ Φ
  absend : ∀{Φ} → Endpoint → Abs𝔹 Φ
  _t⊥i_ : ∀{Φ T} → AbsTm# Φ T → Absℙ Φ → Set
  _i⊥i_ : ∀{Φ} → (ai aj : Absℙ Φ) → Set
  i⊥i-sym : ∀{Φ} → {ai aj : Absℙ Φ} → ai i⊥i aj → aj i⊥i ai
  t⊥end : ∀{Φ T e} → {at : AbsTm# Φ T} → at t⊥i absu (absend e)
  i⊥end : ∀{Φ e} → {ai : Absℙ Φ} → ai i⊥i absu (absend e)

_i⊥t_ : ∀{Φ T} → Absℙ Φ → AbsTm# Φ T → Set
ai i⊥t at = at t⊥i ai

data Ctx : Set
data AbsSub (Φ : CtxVar) : Ctx → Set
_⊥i_ : ∀{Φ Γ} → (γ : AbsSub Φ Γ) → (i : Absℙ Φ) → Set

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
  _!_/_∈𝔹[_] : {Γ : Ctx} → (γ : AbsSub Φ Γ) → (β : Abs𝔹 Φ) → (xi : IVar) → (γ ⊥i absu β) → AbsSub Φ (Γ ! xi ∈𝔹)
  _!_/_∈ℙ[_] : {Γ : Ctx} → (γ : AbsSub Φ Γ) → (β : Absℙ Φ) → (xi : IVar) → (γ ⊥i β) → AbsSub Φ (Γ ! xi ∈ℙ)

_⊥i_ {Γ = •} γ j = ⊤
_⊥i_ {Γ = Γ „ .x ∈ .S ♭} (γ “ S ♭∋ as / x) aj = (γ ⊥i aj) × (absι as t⊥i aj)
_⊥i_ {Γ = Γ „ .x ∈ .S #} (γ “ S #∋ as / x) aj = (γ ⊥i aj) × (as t⊥i aj)
_⊥i_ {Γ = Γ ! .xi ∈𝔹} (γ ! ai / xi ∈𝔹[ _ ]) aj = (γ ⊥i aj) × (absu ai i⊥i aj)
_⊥i_ {Γ = Γ ! .xi ∈ℙ} (γ ! ai / xi ∈ℙ[ _ ]) aj = (γ ⊥i aj) × (ai i⊥i aj)

infix 10 _“_#∋_/_ _“_♭∋_/_
infix 8 _„_∈_♭ _„_∈_#

Sub : Ctx → Ctx → Set
Sub Δ Γ = (Φ : CtxVar) → AbsSub Φ Δ → AbsSub Φ Γ
--Think of AbsSub Φ Δ → AbsSub Φ Γ as Sub Δ Γ = ∀ Ω . Sub Ω Δ → Sub Ω Γ

id : ∀{Γ} → Sub Γ Γ
id Φ γ = γ

_∘_ : ∀{Θ Δ Γ} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
(σ ∘ τ) Φ θ = σ Φ (τ Φ θ)

id∘ : ∀{Δ Γ} → {σ : Sub Δ Γ} → id ∘ σ ≡ σ
id∘ = refl
∘id : ∀{Δ Γ} → {σ : Sub Δ Γ} → σ ∘ id ≡ σ
∘id = refl
∘∘ : ∀{Λ Θ Δ Γ} → {σ : Sub Δ Γ} → {τ : Sub Θ Δ} → {υ : Sub Λ Θ} → (σ ∘ τ) ∘ υ ≡ σ ∘ (τ ∘ υ)
∘∘ = refl
_T[_] : {Δ Γ : Ctx} → Ty Γ → Sub Δ Γ → Ty Δ
T T[ σ ] = λ Φ → λ δ → T Φ (σ Φ δ)
subT = _T[_]
T[id] : ∀{Γ} → {T : Ty Γ} → T T[ id ] ≡ T
T[id] = refl

--================================
--TERMS AND SUBSTITUTION EXTENSION
--================================
infix 5 _⊢_♭ _⊢_#
_⊢_♭ : (Γ : Ctx) → Ty Γ → Set -- set of terms of T ♭
Γ ⊢ T ♭ = (Φ : CtxVar) → (γ : AbsSub Φ Γ) → AbsTm Φ (T Φ γ)
_⊢_# : (Γ : Ctx) → Ty Γ → Set -- set of terms of T #
Γ ⊢ T # = (Φ : CtxVar) → (γ : AbsSub Φ Γ) → AbsTm# Φ (T Φ γ)
--Think of this as Γ ⊢ T = ∀ Ω . (γ : Sub Ω Γ) → Ω ⊢ T[γ]

_[_]♭ : ∀{Δ Γ} → {T : Ty Γ} → (Γ ⊢ T ♭) → (σ : Sub Δ Γ) → (Δ ⊢ T T[ σ ] ♭)
t [ σ ]♭ = λ Φ δ → t Φ (σ Φ δ)
_[_]# : ∀{Δ Γ} → {T : Ty Γ} → (Γ ⊢ T #) → (σ : Sub Δ Γ) → (Δ ⊢ T T[ σ ] #)
t [ σ ]# = λ Φ δ → t Φ (σ Φ δ)
[id]♭ : ∀{Γ} → {T : Ty Γ} → {t : Γ ⊢ T ♭} → t [ id ]♭ ≡ t
[id]♭ = refl
[][]♭ : ∀{Θ Δ Γ} → {T : Ty Γ} → {t : Γ ⊢ T ♭} → {σ : Sub Δ Γ} → {τ : Sub Θ Δ} → t [ σ ]♭ [ τ ]♭ ≡ t [ σ ∘ τ ]♭
[][]♭ = refl

infix 10 _„_♭∋_/_ _„_#∋_/_
_„_♭∋_/_ : ∀ {Δ Γ} → (σ : Sub Δ Γ) → (T : Ty Γ) → Δ ⊢ T T[ σ ] ♭ → (x : Var) → Sub Δ (Γ „ x ∈ T ♭)
(σ „ T ♭∋ t / x) Φ δ = (σ Φ δ) “ T ♭∋ (t Φ δ) / x
_„_#∋_/_ : ∀ {Δ Γ} → (σ : Sub Δ Γ) → (T : Ty Γ) → Δ ⊢ T T[ σ ] # → (x : Var) → Sub Δ (Γ „ x ∈ T #)
(σ „ T #∋ t / x) Φ δ = (σ Φ δ) “ T #∋ (t Φ δ) / x
_„_/_∈𝔹 : ∀ {Δ Γ} → (σ : Sub Δ Γ) → (e : Endpoint) → (xi : IVar) → Sub Δ (Γ ! xi ∈𝔹)
(σ „ e / xi ∈𝔹) Φ δ = (σ Φ δ) ! absend e / xi ∈𝔹[ {!!} ]

--Make a type Variance
--Make a type Endpoint
