{-# OPTIONS --copatterns --rewriting #-}

module Postulates2 where

open import Data.Product
open import Data.Nat
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function renaming (id to idf ; _∘_ to _f∘_)
{-# BUILTIN REWRITE _≡_ #-}

_sa_ : (T : Set) → T → T
T sa t = t

postulate
  Var : Set -- set of variables; if you prefer to ignore variables, think of this as Unit
  Ctx : Set -- set of contexts
  SubΩ : Ctx → Set
    -- Think of SubΩ Γ as Sub Ω Γ for some fixed Ω.
    -- We only provide operations for SubΩ that work for any Ω, we should have natural transformations Ob → Sub Δ for any Δ.
  TyΩ : Set -- Think fo this as Ty(Ω)
  
Sub : Ctx → Ctx → Set
Sub Δ Γ = SubΩ Δ → SubΩ Γ
--Think of this as Sub Δ Γ = ∀ Ω . Sub Ω Δ → Sub Ω Γ

Ty : Ctx → Set
Ty Γ = (γ : SubΩ Γ) → TyΩ

infix 5 Ω⊢_
postulate
  Ω⊢_ : (T : TyΩ) → Set
  -- Think of this as the set of terms Ω ⊢ T

id : ∀{Γ} → Sub Γ Γ
id γ = γ

_∘_ : ∀{Θ Δ Γ} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
(σ ∘ τ) = λ θ → σ (τ θ)

id∘ : ∀{Δ Γ} → {σ : Sub Δ Γ} → id ∘ σ ≡ σ
id∘ = refl
∘id : ∀{Δ Γ} → {σ : Sub Δ Γ} → σ ∘ id ≡ σ
∘id = refl
∘∘ : ∀{Λ Θ Δ Γ} → {σ : Sub Δ Γ} → {τ : Sub Θ Δ} → {υ : Sub Λ Θ} → (σ ∘ τ) ∘ υ ≡ σ ∘ (τ ∘ υ)
∘∘ = refl
_T[_] : {Δ Γ : Ctx} → Ty Γ → Sub Δ Γ → Ty Δ
T T[ σ ] = λ δ → T (σ δ)
subT = _T[_]
T[id] : ∀{Γ} → {T : Ty Γ} → T T[ id ] ≡ T
T[id] = refl

--Terms---------------------------------------------
----------------------------------------------------
infix 5 _⊢_
_⊢_ : (Γ : Ctx) → Ty Γ → Set -- set of terms
Γ ⊢ T = (γ : SubΩ Γ) → Ω⊢ T γ
--Think of this as Γ ⊢ T = ∀ Ω . (γ : Sub Ω Γ) → (γt : Sub Ω Γ.T) × (π ∘ γt = γ)

_[_] : ∀{Δ Γ} → {T : Ty Γ} → (Γ ⊢ T) → (σ : Sub Δ Γ) → (Δ ⊢ T T[ σ ])
t [ σ ] = λ δ → t (σ δ)
subt = _[_]
[id] : ∀{Γ} → {T : Ty Γ} → {t : Γ ⊢ T} → t [ id ] ≡ t
[id] = refl
[][] : ∀{Θ Δ Γ} → {T : Ty Γ} → {t : Γ ⊢ T} → {σ : Sub Δ Γ} → {τ : Sub Θ Δ} → t [ σ ] [ τ ] ≡ t [ σ ∘ τ ]
[][] = refl

--Context extension---------------------------------
----------------------------------------------------
infix 10 _“_∋_/_
infix 10 _„_∋_/_
infix 8 _„_∈_

data SubΩPair (Γ : Ctx) : Var → (T : Ty Γ) → Set where
  _“_∋_/_ : (γ : SubΩ Γ) → (T : Ty Γ) → (t : Ω⊢ T γ) → (x : Var) → SubΩPair Γ x T

postulate
  _„_∈_ : (Γ : Ctx) → Var → Ty Γ → Ctx  --\glqq
  rwr-SubΩ : ∀ {Γ x T} → SubΩ (Γ „ x ∈ T) ≡ SubΩPair Γ x T
  
{-# REWRITE rwr-SubΩ #-}

_„_∋_/_ : ∀ {Δ Γ} → (σ : Sub Δ Γ) → (T : Ty Γ) → Δ ⊢ subT {Δ}{Γ} T σ → (x : Var) → Sub Δ (Γ „ x ∈ T)
(σ „ T ∋ t / x) δ = (σ δ) “ T ∋ (t δ) / x

π : ∀{Γ x} → {T : Ty Γ} → Sub (Γ „ x ∈ T) Γ
--π : ∀{Γ x} → {T : Ty Γ} → SubΩPair Γ x T → SubΩ Γ
π (γ “ T ∋ t / x) = γ
_Tπ : ∀{Γ x} → {S : Ty Γ} → Ty Γ → Ty (Γ „ x ∈ S)
_Tπ {Γ}{x}{S} T = subT{Γ „ x ∈ S}{Γ} T π
ξ : ∀{Γ} → (x : Var) → {T : Ty Γ} → Γ „ x ∈ T ⊢ T Tπ
ξ x (γ “ T ∋ t / .x) = t

{-
ξ[„] : ∀{Δ Γ x T} → {σ : Sub Δ Γ} → {t : Δ ⊢ subT {Δ}{Γ} T σ} → ξ x [ σ „ T ∋ t / x ] ≡ t
ξ[„] = {!!}
π„ξ : ∀{Δ Γ x T} → {τ : Sub Δ (Γ „ x ∈ T)} → (π ∘ τ „ T ∋ ξ x [ τ ] / x) ≡ τ
π„ξ = {!!}
„∘ : ∀{Θ Δ Γ x T} → {σ : Sub Δ Γ} → {t : Δ ⊢ subT {Δ}{Γ} T σ} → {τ : Sub Θ Δ} → (σ „ T ∋ t / x) ∘ τ ≡ σ ∘ τ „ T ∋ t [ τ ] / x
„∘ = {!!}
-}
