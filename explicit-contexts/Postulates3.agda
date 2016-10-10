{-# OPTIONS --copatterns --rewriting --no-positivity-check  #-}

module Postulates3 where

open import Data.Product
open import Data.Nat
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function renaming (id to idf ; _∘_ to _f∘_)
{-# BUILTIN REWRITE _≡_ #-}

_sa_ : (T : Set) → T → T
T sa t = t

postulate
  funext : {A : Set } {B : A → Set} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g

---------------------------------------------------------

postulate
  Var : Set -- set of variables; if you prefer to ignore variables, think of this as Unit
  TyΩ : Set -- Think of this as Ty(Ω)
  Ω⊢_ : (T : TyΩ) → Set -- Think of this as the set of terms Ω ⊢ T
infix 5 Ω⊢_

data Ctx : Set
data SubΩ : Ctx → Set
Ty : Ctx → Set
Ty Γ = (γ : SubΩ Γ) → TyΩ
data Ctx where
  • : Ctx --\bu
  _„_∈_ : (Γ : Ctx) → Var → Ty Γ → Ctx
data SubΩ where
  • : SubΩ •
  _“_∋_/_ : {Γ : Ctx} → (γ : SubΩ Γ) → (T : Ty Γ) → (t : Ω⊢ T γ) → (x : Var) → SubΩ (Γ „ x ∈ T)
infix 10 _“_∋_/_
infix 8 _„_∈_
  
Sub : Ctx → Ctx → Set
Sub Δ Γ = SubΩ Δ → SubΩ Γ
--Think of this as Sub Δ Γ = ∀ Ω . Sub Ω Δ → Sub Ω Γ

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
infix 10 _„_∋_/_
_„_∋_/_ : ∀ {Δ Γ} → (σ : Sub Δ Γ) → (T : Ty Γ) → Δ ⊢ T T[ σ ] → (x : Var) → Sub Δ (Γ „ x ∈ T)
(σ „ T ∋ t / x) δ = (σ δ) “ T ∋ (t δ) / x

π : ∀{Γ x} → {T : Ty Γ} → Sub (Γ „ x ∈ T) Γ
π (γ “ T ∋ t / x) = γ
--_Tπ : ∀{Γ x} → {S : Ty Γ} → Ty Γ → Ty (Γ „ x ∈ S)
--_Tπ {Γ}{x}{S} T = T T[ π ]
ξ : ∀{Γ} → (x : Var) → {T : Ty Γ} → Γ „ x ∈ T ⊢ T T[ π ]
ξ x (γ “ T ∋ t / .x) = t
π∘„ : ∀{Δ Γ T} → {σ : Sub Δ Γ} → {t : Δ ⊢ T T[ σ ]} → {x : Var} → π ∘ (σ „ T ∋ t / x) ≡ σ
π∘„ = refl
ξ[„] : ∀{Δ Γ x T} → {σ : Sub Δ Γ} → {t : Δ ⊢ T T[ σ ]} → ξ x [ σ „ T ∋ t / x ] ≡ t
ξ[„] = refl
π„ξ : ∀{Δ Γ x T} → {τ : Sub Δ (Γ „ x ∈ T)} → (π ∘ τ „ T ∋ ξ x [ τ ] / x) ≡ τ
π„ξ {Δ}{Γ}{x}{T}{τ} = funext λ δ → case τ δ return (λ γt → π γt “ T ∋ ξ x γt / x ≡ γt) of (λ { (γ “ .T ∋ t / .x) → refl })
„∘ : ∀{Θ Δ Γ x T} → {σ : Sub Δ Γ} → {t : Δ ⊢ T T[ σ ]} → {τ : Sub Θ Δ} → (σ „ T ∋ t / x) ∘ τ ≡ σ ∘ τ „ T ∋ t [ τ ] / x
„∘ = refl

--Sharp and flat------------------------------------
----------------------------------------------------
postulate
  ♯_ : TyΩ → TyΩ
  ♭_ : TyΩ → TyΩ
  ♯♯ : ∀{T} → ♯ ♯ T ≡ ♯ T
  ♯♭ : ∀{T} → ♯ ♭ T ≡ ♯ T
  ♭♯ : ∀{T} → ♭ ♯ T ≡ ♭ T
  ♭♭ : ∀{T} → ♭ ♭ T ≡ ♭ T
{-# REWRITE ♯♯ #-}
{-# REWRITE ♯♭ #-}
{-# REWRITE ♭♯ #-}
{-# REWRITE ♭♭ #-}

postulate
  ι_ : ∀{T} → Ω⊢ T → Ω⊢ ♯ T
  κ_ : ∀{T} → Ω⊢ ♭ T → Ω⊢ T
  ι♯ : ∀{T} → {t : Ω⊢ ♯ T} → ι t ≡ t
  κ♯ : ∀{T} → {t : Ω⊢ ♭ ♯ T} → κ t ≡ ι t
  κ♭ : ∀{T} → {t : Ω⊢ ♭ ♭ T} → κ t ≡ t
{-# REWRITE ι♯ #-}
{-# REWRITE κ♯ #-}
{-# REWRITE κ♭ #-}

c♭ : Ctx → Ctx
cκ : ∀{Γ} → Sub (c♭ Γ) Γ
c♭ • = •
c♭ (Γ „ x ∈ T) = c♭ Γ „ x ∈ (λ γ → ♭ T (cκ γ))
cκ {•} _ = •
cκ {Γ „ .x ∈ T} (γ “ _ ∋ t / x) = (cκ γ) “ T ∋ κ t / x

{-
c♯ : Ctx → Ctx
cι : ∀{Γ} → Sub Γ (c♯ Γ)
c♯ • = •
c♯ (Γ „ x ∈ T) = c♯ Γ „ x ∈ (λ γ → {!!})
cι {•} _ = •
cι {Γ „ x ∈ T} = {!!}
-}
