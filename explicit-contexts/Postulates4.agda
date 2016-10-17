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
  AbsTm : (Φ : CtxVar) → (T : AbsTy Φ) → Variance → Set -- Think of this as the set of terms Ω ⊢ T ^ v
  Abs𝔹 : CtxVar → Variance → Set -- Think of this as the set of presheaf maps Ω → 𝔹
  absι : ∀{Φ T} → AbsTm Φ T ♭ → AbsTm Φ T #
  absι𝔹 : ∀{Φ} → Abs𝔹 Φ ♭ → Abs𝔹 Φ #
  absend : ∀{Φ} → Endpoint → Abs𝔹 Φ ♭
  _t⊥i_ : ∀{Φ T} → AbsTm Φ T # → Abs𝔹 Φ # → Set
  _i⊥i_ : ∀{Φ} → (ai aj : Abs𝔹 Φ #) → Set
  i⊥i-sym : ∀{Φ} → {ai aj : Abs𝔹 Φ #} → ai i⊥i aj → aj i⊥i ai
  t⊥end : ∀{Φ T e} → {at : AbsTm Φ T #} → at t⊥i absι𝔹 (absend e)
  i⊥end : ∀{Φ e} → {ai : Abs𝔹 Φ #} → ai i⊥i absι𝔹 (absend e)

absι' : ∀{v Φ T} → AbsTm Φ T v → AbsTm Φ T #
absι' {♭} at = absι at
absι' {#} at = at

absκ' : ∀{v Φ T} → AbsTm Φ T ♭ → AbsTm Φ T v
absκ' {#} at = absι at
absκ' {♭} at = at

absι'𝔹 : ∀{v Φ} → Abs𝔹 Φ v → Abs𝔹 Φ #
absι'𝔹 {♭} i = absι𝔹 i
absι'𝔹 {#} i = i

absκ'𝔹 : ∀{v Φ} → Abs𝔹 Φ ♭ → Abs𝔹 Φ v
absκ'𝔹 {#} i = absι𝔹 i
absκ'𝔹 {♭} i = i

_i⊥t_ : ∀{Φ T} → Abs𝔹 Φ # → AbsTm Φ T # → Set
ai i⊥t at = at t⊥i ai

data Ctx : Set
data AbsSub (Φ : CtxVar) : Ctx → Set
_⊥i_ : ∀{Φ Γ} → (γ : AbsSub Φ Γ) → (i : Abs𝔹 Φ #) → Set

Ty : Ctx → Set
Ty Γ = (Φ : CtxVar) → (γ : AbsSub Φ Γ) → AbsTy Φ

data Ctx where
  • : Ctx --\bu
  _„_∈_^_ : (Γ : Ctx) → Var → (T : Ty Γ) → Variance → Ctx
  _!_∈𝔹_ : (Γ : Ctx) → IVar → Variance → Ctx

data AbsSub Φ where
  • : AbsSub Φ •
  _“_^_∋_/_ : {Γ : Ctx} → (γ : AbsSub Φ Γ) → (T : Ty Γ) → (v : Variance) → (t : AbsTm Φ (T Φ γ) v) →
    (x : Var) → AbsSub Φ (Γ „ x ∈ T ^ v)
  _!𝔹_∋_/_&_ : {Γ : Ctx} → (γ : AbsSub Φ Γ) → (v : Variance) → (β : Abs𝔹 Φ v) → (xi : IVar) →
    (γ ⊥i absι'𝔹 β) → AbsSub Φ (Γ ! xi ∈𝔹 v)

_⊥i_ {Γ = •} γ j = ⊤
_⊥i_ {Γ = Γ „ .x ∈ .S ^ .v} (γ “ S ^ v ∋ as / x) aj = (γ ⊥i aj) × (absι' as t⊥i aj)
_⊥i_ {Γ = Γ ! .xi ∈𝔹 .v} (γ !𝔹 v ∋ ai / xi & _) aj = (γ ⊥i aj) × (absι'𝔹 ai i⊥i aj)

⊥end : ∀{Φ Γ e} → (γ : AbsSub Φ Γ) → γ ⊥i absι𝔹 (absend e)
⊥end {Γ = •} γ = tt
⊥end {Φ}{Γ „ .x ∈ T ^ .v}{e} (γ “ .T ^ v ∋ t / x) = ⊥end γ , t⊥end
⊥end {Φ}{Γ = Γ ! .x ∈𝔹 .v}{e} (γ !𝔹 v ∋ β / x & o) = ⊥end γ , i⊥end

infix 10 _“_^_∋_/_
infix 8 _„_∈_^_

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

postulate
  σ⊥i : ∀{Φ Δ Γ} → (σ : Sub Δ Γ) → (δ : AbsSub Φ Δ) → {i : Abs𝔹 Φ #} → (δ ⊥i i) → (σ Φ δ ⊥i i)

--================================
--TERMS AND SUBSTITUTION EXTENSION
--================================
infix 5 _⊢_^_
_⊢_^_ : (Γ : Ctx) → Ty Γ → Variance → Set -- set of terms of T v
Γ ⊢ T ^ v = (Φ : CtxVar) → (γ : AbsSub Φ Γ) → AbsTm Φ (T Φ γ) v
--Think of this as Γ ⊢ T = ∀ Ω . (γ : Sub Ω Γ) → Ω ⊢ T[γ]

_[_] : ∀{v Δ Γ} → {T : Ty Γ} → (Γ ⊢ T ^ v) → (σ : Sub Δ Γ) → (Δ ⊢ T T[ σ ] ^ v)
t [ σ ] = λ Φ δ → t Φ (σ Φ δ)
[id] : ∀{v Γ} → {T : Ty Γ} → {t : Γ ⊢ T ^ v} → t [ id ] ≡ t
[id] = refl
[][] : ∀{v Θ Δ Γ} → {T : Ty Γ} → {t : Γ ⊢ T ^ v} → {σ : Sub Δ Γ} → {τ : Sub Θ Δ} → t [ σ ] [ τ ] ≡ t [ σ ∘ τ ]
[][] = refl

infix 10 _„_^_∋_/_ _!𝔹_∋_/_
_„_^_∋_/_ : ∀ {Δ Γ} → (σ : Sub Δ Γ) → (T : Ty Γ) → (v : Variance) →  Δ ⊢ T T[ σ ] ^ v → (x : Var) → Sub Δ (Γ „ x ∈ T ^ v)
(σ „ T ^ v ∋ t / x) Φ δ = (σ Φ δ) “ T ^ v ∋ (t Φ δ) / x

_!𝔹_∋_/_ : ∀ {Δ Γ} → (σ : Sub Δ Γ) → (v : Variance) → (e : Endpoint) → (xi : IVar) → Sub Δ (Γ ! xi ∈𝔹 v)
(σ !𝔹 ♭ ∋ e / xi) Φ δ = (σ Φ δ) !𝔹 ♭ ∋ absκ'𝔹 (absend e) / xi & ⊥end (σ Φ δ)
(σ !𝔹 # ∋ e / xi) Φ δ = (σ Φ δ) !𝔹 # ∋ absκ'𝔹 (absend e) / xi & ⊥end (σ Φ δ)

_!id : ∀{v Δ Γ xi} → (σ : Sub Δ Γ) → Sub (Δ ! xi ∈𝔹 v) (Γ ! xi ∈𝔹 v)
(σ !id) Φ (δ !𝔹 v ∋ i / xi & o) = (σ Φ δ) !𝔹 v ∋ i / xi & σ⊥i σ δ o

_!u : ∀{Δ Γ xi} → (σ : Sub Δ Γ) → Sub (Δ ! xi ∈𝔹 ♭) (Γ ! xi ∈𝔹 #)
(σ !u) Φ (δ !𝔹 .♭ ∋ i / xi & o) = (σ Φ δ) !𝔹 # ∋ absι𝔹 i / xi & σ⊥i σ δ o

--THINKING ABOUT TYPES:
--let AbsTy Φ be the types over #Ω.
--let Ty Γ be the types over #Γ
--define functoriality of # and ♭
--There will be mutual dependencies between these things.
