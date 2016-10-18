{-# OPTIONS --copatterns --rewriting --no-positivity-check  #-}

module Postulates5 where

open import Data.Product
open import Data.Nat
open import Data.Unit
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning
open import Function renaming (id to idf ; _∘_ to _f∘_)
{-# BUILTIN REWRITE _≡_ #-}

postulate
  funext : {A : Set } {B : A → Set} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g
  
map≡ : {A B : Set} (f : A → B) → ∀{x y} → x ≡ y → f x ≡ f y
map≡ f refl = refl
sym≡ : {A : Set} → {x y : A} → x ≡ y → y ≡ x
sym≡ refl = refl

--=================================
--CONTEXTS, SUBSTITUTIONS AND TYPES
--=================================

data Variance : Set where
  # : Variance
  ♭ : Variance

data CtxVariance : Set where
  ♭ : CtxVariance
  ∫ : CtxVariance
  ⊕ : CtxVariance

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
  ιatm : ∀{Φ T} → AbsTm Φ T ♭ → AbsTm Φ T #
  ι𝔹 : ∀{Φ} → Abs𝔹 Φ ♭ → Abs𝔹 Φ #
  end𝔹 : ∀{Φ} → Endpoint → Abs𝔹 Φ ♭
  _t⊥i_ : ∀{Φ T} → AbsTm Φ T # → Abs𝔹 Φ # → Set
  _i⊥i_ : ∀{Φ} → (ai aj : Abs𝔹 Φ #) → Set
  i⊥i-sym : ∀{Φ} → {ai aj : Abs𝔹 Φ #} → ai i⊥i aj → aj i⊥i ai
  t⊥end : ∀{Φ T e} → {at : AbsTm Φ T #} → at t⊥i ι𝔹 (end𝔹 e)
  i⊥end : ∀{Φ e} → {ai : Abs𝔹 Φ #} → ai i⊥i ι𝔹 (end𝔹 e)

_i⊥t_ : ∀{Φ T} → Abs𝔹 Φ # → AbsTm Φ T # → Set
ai i⊥t at = at t⊥i ai

ι'atm : ∀{v Φ T} → AbsTm Φ T v → AbsTm Φ T #
ι'atm {♭} at = ιatm at
ι'atm {#} at = at

κ'atm : ∀{v Φ T} → AbsTm Φ T ♭ → AbsTm Φ T v
κ'atm {#} at = ιatm at
κ'atm {♭} at = at

ι'𝔹 : ∀{v Φ} → Abs𝔹 Φ v → Abs𝔹 Φ #
ι'𝔹 {♭} i = ι𝔹 i
ι'𝔹 {#} i = i

κ'𝔹 : ∀{v Φ} → Abs𝔹 Φ ♭ → Abs𝔹 Φ v
κ'𝔹 {#} i = ι𝔹 i
κ'𝔹 {♭} i = i

ι'𝔹∘κ'𝔹 : ∀{v Φ} → {i : Abs𝔹 Φ ♭} → ι'𝔹 (κ'𝔹 {v} i) ≡ ι𝔹 i
ι'𝔹∘κ'𝔹 {#} = refl
ι'𝔹∘κ'𝔹 {♭} = refl
{-# REWRITE ι'𝔹∘κ'𝔹 #-}

data Ctx : Set
c# : Ctx → Ctx
c♭ : Ctx → Ctx
postulate
  c## : ∀{Γ} → c# (c# Γ) ≡ c# Γ
  c#♭ : ∀{Γ} → c# (c♭ Γ) ≡ c# Γ
{-# REWRITE c## #-}
{-# REWRITE c#♭ #-}
data AbsSub (Φ : CtxVar) : Ctx → Set

c-radj : CtxVariance → Ctx → Ctx
c-radj ⊕ = idf
c-radj ∫ = c♭
c-radj ♭ = c#

radj : CtxVariance → Variance → Variance
radj ⊕ v = v
radj ∫ v = ♭
radj ♭ v = #

GAbsSub : (u : CtxVariance) → (Φ : CtxVar) → (Γ : Ctx) → Set
GAbsSub u Φ Γ = AbsSub Φ (c-radj u Γ)

Sub : Ctx → Ctx → Set
Sub Δ Γ = (u : CtxVariance) → (Φ : CtxVar) → GAbsSub u Φ Δ → GAbsSub u Φ Γ
--Think of AbsSub Φ Δ → AbsSub Φ Γ as Sub Δ Γ = ∀ Ω . Sub Ω Δ → Sub Ω Γ

id : ∀ Γ → Sub Γ Γ
id Γ u Φ γ = γ

_∘_ : ∀{Θ Δ Γ} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
(σ ∘ τ) u Φ θ = σ u Φ (τ u Φ θ)

_⊥i_ : ∀{Φ Γ} → (γ : AbsSub Φ Γ) → (i : Abs𝔹 Φ #) → Set
postulate
  σ⊥i : ∀{u Φ Δ Γ} → (σ : Sub Δ Γ) → (δ : GAbsSub u Φ Δ) → {i : Abs𝔹 Φ #} → (δ ⊥i i) → (σ u Φ δ ⊥i i)

Ty : Ctx → Set
Ty Γ = (Φ : CtxVar) → (γ : AbsSub Φ (c# Γ)) → AbsTy Φ
data Ctx where
  • : Ctx --\bu
  _„_∈_^_ : (Γ : Ctx) → Var → (T : Ty Γ) → (v : Variance) → Ctx
  _!_∈𝔹_ : (Γ : Ctx) → IVar → (v : Variance) → Ctx

c# • = •
c# (Γ „ x ∈ T ^ v) = c# Γ „ x ∈ T ^ #
c# (Γ ! x ∈𝔹 v) = c# Γ ! x ∈𝔹 #

c♭ • = •
c♭ (Γ „ x ∈ T ^ v) = c♭ Γ „ x ∈ T ^ ♭
c♭ (Γ ! x ∈𝔹 v) = c♭ Γ ! x ∈𝔹 ♭

c-radj-• : ∀{u} → c-radj u • ≡ •
c-radj-• {⊕} = refl
c-radj-• {∫} = refl
c-radj-• {♭} = refl
{-# REWRITE c-radj-• #-}

cι : ∀{Γ} → Sub Γ (c# Γ)
postulate
  cι# : ∀{Γ} → cι {c# Γ} ≡ id(c# Γ)
--{-# REWRITE cι# #-}

data AbsSub Φ where
  • : AbsSub Φ •
  _“_^_∋_/_ : {Γ : Ctx} → (γ : AbsSub Φ Γ) → (T : Ty Γ) → (v : Variance) → (t : AbsTm Φ (T Φ (cι ⊕ Φ γ)) v) →
    (x : Var) → AbsSub Φ (Γ „ x ∈ T ^ v)
  _!𝔹_∋_/_&_ : {Γ : Ctx} → (γ : AbsSub Φ Γ) → (v : Variance) → (β : Abs𝔹 Φ v) → (xi : IVar) →
    .(γ ⊥i ι'𝔹 β) → AbsSub Φ (Γ ! xi ∈𝔹 v)
{-
cι {•} u Φ • = •
cι {Γ „ .x ∈ .T ^ .v} u Φ (γ “ T ^ v ∋ t / x) = (cι Φ γ) “ T ^ # ∋ ι'atm t / x
cι {Γ ! .xi ∈𝔹 .v} u Φ (γ !𝔹 v ∋ β / xi & o) = (cι Φ γ) !𝔹 # ∋ (ι'𝔹 β) / xi & σ⊥i cι γ o
-}
cι = {!!}

_⊥i_ {Γ = •} γ j = ⊤
_⊥i_ {Γ = Γ „ .x ∈ .S ^ .v} (γ “ S ^ v ∋ as / x) aj = (γ ⊥i aj) × (ι'atm as t⊥i aj)
_⊥i_ {Γ = Γ ! .xi ∈𝔹 .v} (γ !𝔹 v ∋ ai / xi & _) aj = (γ ⊥i aj) × (ι'𝔹 ai i⊥i aj)

⊥end : ∀{Φ Γ e} → (γ : AbsSub Φ Γ) → γ ⊥i ι𝔹 (end𝔹 e)
⊥end {Γ = •} γ = tt
⊥end {Φ}{Γ „ .x ∈ T ^ .v}{e} (γ “ .T ^ v ∋ t / x) = ⊥end γ , t⊥end
⊥end {Φ}{Γ = Γ ! .x ∈𝔹 .v}{e} (γ !𝔹 v ∋ β / x & o) = ⊥end γ , i⊥end

infix 10 _“_^_∋_/_
infix 8 _„_∈_^_

id∘ : ∀{Δ Γ} → {σ : Sub Δ Γ} → id Γ ∘ σ ≡ σ
id∘ = refl
∘id : ∀{Δ Γ} → {σ : Sub Δ Γ} → σ ∘ id Δ ≡ σ
∘id = refl
∘∘ : ∀{Λ Θ Δ Γ} → {σ : Sub Δ Γ} → {τ : Sub Θ Δ} → {υ : Sub Λ Θ} → (σ ∘ τ) ∘ υ ≡ σ ∘ (τ ∘ υ)
∘∘ = refl

_T[_] : {Δ Γ : Ctx} → Ty Γ → Sub Δ Γ → Ty Δ
T T[ σ ] = λ Φ → λ δ → T Φ {!sub# σ Φ δ!}
subT = _T[_]
T[id] : ∀{Γ} → {T : Ty Γ} → T T[ id Γ ] ≡ T
T[id] = {!refl!}
T[][] : ∀{Θ Δ Γ} → {T : Ty Γ} → {σ : Sub Δ Γ} → {τ : Sub Θ Δ} → T T[ σ ] T[ τ ] ≡ T T[ σ ∘ τ ]
T[][] = {!refl!}
