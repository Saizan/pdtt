{-# OPTIONS --copatterns --rewriting --no-positivity-check  #-}

module Postulates3 where

open import Data.Product
open import Data.Nat
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function renaming (id to idf ; _∘_ to _f∘_)
{-# BUILTIN REWRITE _≡_ #-}

--_sa_ : (T : Set) → T → T
--T sa t = t

postulate
  funext : {A : Set } {B : A → Set} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g

---------------------------------------------------------

postulate
  Var : Set -- set of variables; if you prefer to ignore variables, think of this as Unit
  CtxVar : Set -- set of context variables.
  AbsTy : CtxVar → Set -- Think of this as Ty(Ω)
  AbsTm : (Φ : CtxVar) → (T : AbsTy Φ) → Set -- Think of this as the set of terms Ω ⊢ T
--infix 5 Ω⊢_

data Ctx : Set
data AbsSub (Φ : CtxVar) : Ctx → Set
Ty : Ctx → Set
Ty Γ = (Φ : CtxVar) → (γ : AbsSub Φ Γ) → AbsTy Φ
data Ctx where
  • : Ctx --\bu
  _„_∈_ : (Γ : Ctx) → Var → Ty Γ → Ctx
data AbsSub Φ where
  • : AbsSub Φ •
  _“_∋_/_ : {Γ : Ctx} → (γ : AbsSub Φ Γ) → (T : Ty Γ) → (t : AbsTm Φ (T Φ γ)) → (x : Var) → AbsSub Φ (Γ „ x ∈ T)
infix 10 _“_∋_/_
infix 8 _„_∈_

Sub : Ctx → Ctx → Set
Sub Δ Γ = (Φ : CtxVar) → AbsSub Φ Δ → AbsSub Φ Γ
--Think of this as Sub Δ Γ = ∀ Ω . Sub Ω Δ → Sub Ω Γ

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
  
--Terms---------------------------------------------
----------------------------------------------------
infix 5 _⊢_
_⊢_ : (Γ : Ctx) → Ty Γ → Set -- set of terms
Γ ⊢ T = (Φ : CtxVar) → (γ : AbsSub Φ Γ) → AbsTm Φ (T Φ γ)
--Think of this as Γ ⊢ T = ∀ Ω . (γ : Sub Ω Γ) → Ω ⊢ T[γ]

_[_] : ∀{Δ Γ} → {T : Ty Γ} → (Γ ⊢ T) → (σ : Sub Δ Γ) → (Δ ⊢ T T[ σ ])
t [ σ ] = λ Φ δ → t Φ (σ Φ δ)
subt = _[_]
[id] : ∀{Γ} → {T : Ty Γ} → {t : Γ ⊢ T} → t [ id ] ≡ t
[id] = refl
[][] : ∀{Θ Δ Γ} → {T : Ty Γ} → {t : Γ ⊢ T} → {σ : Sub Δ Γ} → {τ : Sub Θ Δ} → t [ σ ] [ τ ] ≡ t [ σ ∘ τ ]
[][] = refl

--Context extension---------------------------------
----------------------------------------------------
infix 10 _„_∋_/_
_„_∋_/_ : ∀ {Δ Γ} → (σ : Sub Δ Γ) → (T : Ty Γ) → Δ ⊢ T T[ σ ] → (x : Var) → Sub Δ (Γ „ x ∈ T)
(σ „ T ∋ t / x) Φ δ = (σ Φ δ) “ T ∋ (t Φ δ) / x

π : ∀{Γ x} → {T : Ty Γ} → Sub (Γ „ x ∈ T) Γ
π Φ (γ “ T ∋ t / x) = γ
--_Tπ : ∀{Γ x} → {S : Ty Γ} → Ty Γ → Ty (Γ „ x ∈ S)
--_Tπ {Γ}{x}{S} T = T T[ π ]
ξ : ∀{Γ} → (x : Var) → {T : Ty Γ} → Γ „ x ∈ T ⊢ T T[ π ]
ξ x Φ (γ “ T ∋ t / .x) = t
π∘„ : ∀{Δ Γ T} → {σ : Sub Δ Γ} → {t : Δ ⊢ T T[ σ ]} → {x : Var} → π ∘ (σ „ T ∋ t / x) ≡ σ
π∘„ = refl
ξ[„] : ∀{Δ Γ x T} → {σ : Sub Δ Γ} → {t : Δ ⊢ T T[ σ ]} → ξ x [ σ „ T ∋ t / x ] ≡ t
ξ[„] = refl
π„ξ : ∀{Δ Γ x T} → {τ : Sub Δ (Γ „ x ∈ T)} → (π ∘ τ „ T ∋ ξ x [ τ ] / x) ≡ τ
π„ξ {Δ}{Γ}{x}{T}{τ} = funext λ Φ → funext λ δ → case τ Φ δ return (λ γt → π Φ γt “ T ∋ ξ x Φ γt / x ≡ γt) of (λ { (γ “ .T ∋ t / .x) → refl })
„∘ : ∀{Θ Δ Γ x T} → {σ : Sub Δ Γ} → {t : Δ ⊢ T T[ σ ]} → {τ : Sub Θ Δ} → (σ „ T ∋ t / x) ∘ τ ≡ σ ∘ τ „ T ∋ t [ τ ] / x
„∘ = refl

--Sharp and flat------------------------------------
----------------------------------------------------
postulate
  --♯_ : {Φ : CtxVar} → AbsTy Φ → AbsTy Φ
  ♭_ : {Φ : CtxVar} → AbsTy Φ → AbsTy Φ
  --♯♯ : ∀{Φ} → {T : AbsTy Φ} → ♯ ♯ T ≡ ♯ T
  --♯♭ : ∀{Φ} → {T : AbsTy Φ} → ♯ ♭ T ≡ ♯ T
  --♭♯ : ∀{Φ} → {T : AbsTy Φ} → ♭ ♯ T ≡ ♭ T
  ♭♭ : ∀{Φ} → {T : AbsTy Φ} → ♭ ♭ T ≡ ♭ T
--{-# REWRITE ♯♯ #-}
--{-# REWRITE ♯♭ #-}
--{-# REWRITE ♭♯ #-}
{-# REWRITE ♭♭ #-}

postulate
  --ι_ : ∀{Φ} → {T : AbsTy Φ} → AbsTm Φ T → AbsTm Φ (♯ T)
  κ_ : ∀{Φ} → {T : AbsTy Φ} → AbsTm Φ (♭ T) → AbsTm Φ T
  --ι♯ : ∀{Φ} → {T : AbsTy Φ} → {t : AbsTm Φ (♯ T)} → ι t ≡ t
  --κ♯ : ∀{Φ} → {T : AbsTy Φ} → {t : AbsTm Φ (♭ ♯ T)} → κ t ≡ ι t
  κ♭ : ∀{Φ} → {T : AbsTy Φ} → {t : AbsTm Φ (♭ ♭ T)} → κ t ≡ t
--{-# REWRITE ι♯ #-}
--{-# REWRITE κ♯ #-}
{-# REWRITE κ♭ #-}

c♭ : Ctx → Ctx
cκ : ∀{Γ} → Sub (c♭ Γ) Γ
c♭ • = •
c♭ (Γ „ x ∈ T) = c♭ Γ „ x ∈ (λ Φ γ → ♭ T Φ (cκ Φ γ))
cκ {•} _ _ = •
cκ {Γ „ .x ∈ T} Φ (γ “ _ ∋ t / x) = (cκ Φ γ) “ T ∋ κ t / x


{-
postulate
  ♯map : ∀{Γ} → {S T : Ty Γ} →
    ((Φ : CtxVar) → (γ : AbsSub Φ Γ) → AbsTm Φ (S Φ γ) → AbsTm Φ (T Φ γ)) →
    ((Φ : CtxVar) → (γ : AbsSub Φ Γ) → AbsTm Φ (♯ (S Φ γ)) → AbsTm Φ (♯ (T Φ γ)))
  ♯map-ι : ∀{Γ} → {S T : Ty Γ} →
    {f : ((Φ : CtxVar) → (γ : AbsSub Φ Γ) → AbsTm Φ (S Φ γ) → AbsTm Φ (T Φ γ))}
    → ∀{Φ γ t} → (♯map{Γ}{S}{T} f Φ γ (ι t)) ≡ (ι f Φ γ t)
{-# REWRITE ♯map-ι #-}
-}

c♯ : Ctx → Ctx
cι : ∀{Γ} → Sub Γ (c♯ Γ)

postulate
  abs♯ : ∀{Φ} → AbsTy Φ → AbsTy Φ
  T♯ : ∀{Γ} → Ty Γ → Ty (c♯ Γ)
  T♯[ι] : ∀{Γ Φ} → {γ : AbsSub Φ Γ} → {T : Ty Γ} → T♯ T Φ (cι Φ γ) ≡ abs♯ (T Φ γ)
{-# REWRITE T♯[ι] #-}

♯ : ∀{Γ} → Ty Γ → Ty Γ
♯ T Φ γ = abs♯ (T Φ γ)

T♯[ι]' : ∀{Γ} → {T : Ty Γ} → (T♯ T) T[ cι ] ≡ ♯ T
T♯[ι]' = refl

postulate
  absι : ∀{Γ Φ} → (γ : AbsSub Φ Γ) → (T : Ty Γ) → AbsTm Φ (T Φ γ) → AbsTm Φ (abs♯ (T Φ γ))
  t♯ : ∀{Γ T} → Γ ⊢ T → c♯ Γ ⊢ T♯ T
  t♯[ι] : ∀{Γ Φ} → {γ : AbsSub Φ Γ} → {T : Ty Γ} → {t : Γ ⊢ T} → t♯ t Φ (cι Φ γ) ≡ absι γ T (t Φ γ)
{-# REWRITE t♯[ι] #-}

ι : ∀{Γ} → {T : Ty Γ} → (t : Γ ⊢ T) → Γ ⊢ ♯ T
ι {Γ}{T} t Φ γ = absι γ T (t Φ γ)

t♯[ι]' : ∀{Γ} → {T : Ty Γ} → {t : Γ ⊢ T} → (t♯ t) [ cι ] ≡ ι t
t♯[ι]' = refl

c♯ • = •
c♯ (Γ „ x ∈ T) = c♯ Γ „ x ∈ T♯ T
cι {•} Φ _ = •
cι {Γ „ .x ∈ .T} Φ (γ “ T ∋ t / x) = (cι Φ γ) “ T♯ T ∋ absι γ T t / x
