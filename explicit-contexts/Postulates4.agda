{-# OPTIONS --copatterns --rewriting --no-positivity-check  #-}

module Postulates4 where

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

_i⊥t_ : ∀{Φ T} → Abs𝔹 Φ # → AbsTm Φ T # → Set
ai i⊥t at = at t⊥i ai

data Ctx : Set
c# : Ctx → Ctx
postulate
  c## : ∀{Γ} → c# (c# Γ) ≡ c# Γ
{-# REWRITE c## #-}
data AbsSub (Φ : CtxVar) : Ctx → Set

Sub : Ctx → Ctx → Set
Sub Δ Γ = (Φ : CtxVar) → AbsSub Φ Δ → AbsSub Φ Γ
--Think of AbsSub Φ Δ → AbsSub Φ Γ as Sub Δ Γ = ∀ Ω . Sub Ω Δ → Sub Ω Γ

id : ∀{Γ} → Sub Γ Γ
id Φ γ = γ

_∘_ : ∀{Θ Δ Γ} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
(σ ∘ τ) Φ θ = σ Φ (τ Φ θ)

_⊥i_ : ∀{Φ Γ} → (γ : AbsSub Φ Γ) → (i : Abs𝔹 Φ #) → Set
postulate
  σ⊥i : ∀{Φ Δ Γ} → (σ : Sub Δ Γ) → (δ : AbsSub Φ Δ) → {i : Abs𝔹 Φ #} → (δ ⊥i i) → (σ Φ δ ⊥i i)

Ty : Ctx → Set
Ty Γ = (Φ : CtxVar) → (γ : AbsSub Φ (c# Γ)) → AbsTy Φ

data Ctx where
  • : Ctx --\bu
  _„_∈_^_ : (Γ : Ctx) → Var → (T : Ty Γ) → (v : Variance) → Ctx
  _!_∈𝔹_ : (Γ : Ctx) → IVar → (v : Variance) → Ctx

c# • = •
c# (Γ „ x ∈ T ^ v) = c# Γ „ x ∈ T ^ #
c# (Γ ! x ∈𝔹 v) = c# Γ ! x ∈𝔹 #

cι : ∀{Γ} → Sub Γ (c# Γ)
postulate
  cι# : ∀{Γ} → cι {c# Γ} ≡ id
{-# REWRITE cι# #-}
data AbsSub Φ where
  • : AbsSub Φ •
  _“_^_∋_/_ : {Γ : Ctx} → (γ : AbsSub Φ Γ) → (T : Ty Γ) → (v : Variance) → (t : AbsTm Φ (T Φ (cι Φ γ)) v) →
    (x : Var) → AbsSub Φ (Γ „ x ∈ T ^ v)
  _!𝔹_∋_/_&_ : {Γ : Ctx} → (γ : AbsSub Φ Γ) → (v : Variance) → (β : Abs𝔹 Φ v) → (xi : IVar) →
    .(γ ⊥i ι'𝔹 β) → AbsSub Φ (Γ ! xi ∈𝔹 v)
cι {•} Φ • = •
cι {Γ „ .x ∈ .T ^ .v} Φ (γ “ T ^ v ∋ t / x) = (cι Φ γ) “ T ^ # ∋ ι'atm t / x
cι {Γ ! .xi ∈𝔹 .v} Φ (γ !𝔹 v ∋ β / xi & o) = (cι Φ γ) !𝔹 # ∋ (ι'𝔹 β) / xi & σ⊥i cι γ o

_⊥i_ {Γ = •} γ j = ⊤
_⊥i_ {Γ = Γ „ .x ∈ .S ^ .v} (γ “ S ^ v ∋ as / x) aj = (γ ⊥i aj) × (ι'atm as t⊥i aj)
_⊥i_ {Γ = Γ ! .xi ∈𝔹 .v} (γ !𝔹 v ∋ ai / xi & _) aj = (γ ⊥i aj) × (ι'𝔹 ai i⊥i aj)

⊥end : ∀{Φ Γ e} → (γ : AbsSub Φ Γ) → γ ⊥i ι𝔹 (end𝔹 e)
⊥end {Γ = •} γ = tt
⊥end {Φ}{Γ „ .x ∈ T ^ .v}{e} (γ “ .T ^ v ∋ t / x) = ⊥end γ , t⊥end
⊥end {Φ}{Γ = Γ ! .x ∈𝔹 .v}{e} (γ !𝔹 v ∋ β / x & o) = ⊥end γ , i⊥end

infix 10 _“_^_∋_/_
infix 8 _„_∈_^_

id∘ : ∀{Δ Γ} → {σ : Sub Δ Γ} → id ∘ σ ≡ σ
id∘ = refl
∘id : ∀{Δ Γ} → {σ : Sub Δ Γ} → σ ∘ id ≡ σ
∘id = refl
∘∘ : ∀{Λ Θ Δ Γ} → {σ : Sub Δ Γ} → {τ : Sub Θ Δ} → {υ : Sub Λ Θ} → (σ ∘ τ) ∘ υ ≡ σ ∘ (τ ∘ υ)
∘∘ = refl

postulate
  sub# : ∀{Δ Γ} → Sub Δ Γ → Sub (c# Δ) (c# Γ)
  sub#-id : ∀{Γ Φ} → {γ : AbsSub Φ (c# Γ)} → sub# id Φ γ ≡ γ
  sub#-∘ : ∀{Θ Δ Γ Φ} → {τ : Sub Θ Δ} → {σ : Sub Δ Γ} → {θ : AbsSub Φ (c# Θ)}
    → (sub# σ) Φ (sub# τ Φ θ) ≡ sub# (σ ∘ τ) Φ θ 
  cι-nat : ∀{Δ Γ} → {σ : Sub Δ Γ} → ∀{Φ} → {δ : AbsSub Φ Δ} → sub# σ Φ (cι Φ δ) ≡ (cι ∘ σ) Φ δ
  sub## : ∀{Δ Γ} → {σ : Sub Δ Γ} → sub# (sub# σ) ≡ sub# σ
{-# REWRITE sub#-id #-}
{-# REWRITE sub#-∘ #-}
{-# REWRITE cι-nat #-}
{-# REWRITE sub## #-}

_T[_] : {Δ Γ : Ctx} → Ty Γ → Sub Δ Γ → Ty Δ
T T[ σ ] = λ Φ → λ δ → T Φ (sub# σ Φ δ)
subT = _T[_]
T[id] : ∀{Γ} → {T : Ty Γ} → T T[ id ] ≡ T
T[id] = refl
T[][] : ∀{Θ Δ Γ} → {T : Ty Γ} → {σ : Sub Δ Γ} → {τ : Sub Θ Δ} → T T[ σ ] T[ τ ] ≡ T T[ σ ∘ τ ]
T[][] = refl

--================================
--TERMS AND SUBSTITUTION EXTENSION
--================================
infix 5 _⊢_^_
_⊢_^_ : (Γ : Ctx) → Ty Γ → Variance → Set -- set of terms of T v
Γ ⊢ T ^ v = (Φ : CtxVar) → (γ : AbsSub Φ Γ) → AbsTm Φ (T Φ (cι Φ γ)) v
--Think of this as Γ ⊢ T = ∀ Ω . (γ : Sub Ω Γ) → Ω ⊢ T[γ]

_∋_[_] : ∀{v Δ Γ} → (T : Ty Γ) → (Γ ⊢ T ^ v) → (σ : Sub Δ Γ) → (Δ ⊢ T T[ σ ] ^ v)
T ∋ t [ σ ] = λ Φ δ → t Φ (σ Φ δ)
[id] : ∀{v Γ} → {T : Ty Γ} → {t : Γ ⊢ T ^ v} → T ∋ t [ id ] ≡ t
[id] = refl
[][] : ∀{v Θ Δ Γ} → {T : Ty Γ} → {t : Γ ⊢ T ^ v} → {σ : Sub Δ Γ} → {τ : Sub Θ Δ}
  → (T T[ σ ]) ∋ (T ∋ t [ σ ]) [ τ ] ≡ T ∋ t [ σ ∘ τ ]
[][] = refl
infix 10 _∋_[_]

infix 10 _„_^_∋_/_ _!𝔹_∋_/_
_„_^_∋_/_ : ∀ {Δ Γ} → (σ : Sub Δ Γ) → (T : Ty Γ) → (v : Variance) →  Δ ⊢ T T[ σ ] ^ v → (x : Var) → Sub Δ (Γ „ x ∈ T ^ v)
(σ „ T ^ v ∋ t / x) Φ δ = (σ Φ δ) “ T ^ v ∋ (t Φ δ) / x

_!𝔹_∋_/_ : ∀ {Δ Γ} → (σ : Sub Δ Γ) → (v : Variance) → (e : Endpoint) → (xi : IVar) → Sub Δ (Γ ! xi ∈𝔹 v)
(σ !𝔹 ♭ ∋ e / xi) Φ δ = (σ Φ δ) !𝔹 ♭ ∋ κ'𝔹 (end𝔹 e) / xi & ⊥end (σ Φ δ)
(σ !𝔹 # ∋ e / xi) Φ δ = (σ Φ δ) !𝔹 # ∋ κ'𝔹 (end𝔹 e) / xi & ⊥end (σ Φ δ)

_!id : ∀{v Δ Γ xi} → (σ : Sub Δ Γ) → Sub (Δ ! xi ∈𝔹 v) (Γ ! xi ∈𝔹 v)
(σ !id) Φ (δ !𝔹 v ∋ i / xi & o) = (σ Φ δ) !𝔹 v ∋ i / xi & σ⊥i σ δ o

_!u : ∀{Δ Γ xi} → (σ : Sub Δ Γ) → Sub (Δ ! xi ∈𝔹 ♭) (Γ ! xi ∈𝔹 #)
(σ !u) Φ (δ !𝔹 .♭ ∋ i / xi & o) = (σ Φ δ) !𝔹 # ∋ ι𝔹 i / xi & σ⊥i σ δ o

--==================================
--FLAT
--==================================

c♭ : Ctx → Ctx
postulate
  c#♭ : ∀{Γ} → c# (c♭ Γ) ≡ c# Γ
{-# REWRITE c#♭ #-}
c♭ • = •
c♭ (Γ „ x ∈ T ^ v) = c♭ Γ „ x ∈ T ^ ♭
c♭ (Γ ! x ∈𝔹 v) = c♭ Γ ! x ∈𝔹 ♭

cκ : ∀{Γ} → Sub (c♭ Γ) Γ
postulate
  cι∘cκ : ∀{Γ Φ} → {γ : AbsSub Φ (c♭ Γ)} → cι Φ (cκ{Γ} Φ γ) ≡ cι Φ γ
{-# REWRITE cι∘cκ #-}
cκ {•} Φ • = •
cκ {Γ „ .x ∈ .T ^ v} Φ (γ “ T ^ .♭ ∋ t / x) = (cκ Φ γ) “ T ^ v ∋ κ'atm t / x
cκ {Γ ! .xi ∈𝔹 v} Φ (γ !𝔹 .♭ ∋ β / xi & o) = (cκ Φ γ) !𝔹 v ∋ (κ'𝔹 β) / xi & σ⊥i cκ γ o

postulate
  sub♭ : ∀{Δ Γ} → Sub Δ Γ → Sub (c♭ Δ) (c♭ Γ)
  sub♭-id : ∀{Γ Φ} → {γ : AbsSub Φ (c♭ Γ)} → sub♭ id Φ γ ≡ γ
  sub♭-∘ : ∀{Θ Δ Γ Φ} → {τ : Sub Θ Δ} → {σ : Sub Δ Γ} → {θ : AbsSub Φ (c♭ Θ)}
    → (sub♭ σ) Φ (sub♭ τ Φ θ) ≡ sub♭ (σ ∘ τ) Φ θ 
  cκ-nat : ∀{Δ Γ} → {σ : Sub Δ Γ} → ∀{Φ} → {δ : AbsSub Φ (c♭ Δ)} → cκ Φ (sub♭ σ Φ δ) ≡ σ Φ (cκ Φ δ)
{-# REWRITE sub♭-id #-}
{-# REWRITE sub♭-∘ #-}
--{-# REWRITE cκ-nat #-}

--=====================================
--Universe
--=====================================

postulate
  ATU : (n : ℕ) → ∀{Φ} → AbsTy Φ

TU : (Γ : Ctx) → (n : ℕ) → Ty Γ
TU Γ n Φ γ = ATU n
TU[] : ∀{n Δ Γ} → {σ : Sub Δ Γ} → TU Γ n T[ σ ] ≡ TU Δ n
TU[] = refl


postulate
  tX : Var
  TEl0 : ∀{n} → Ty (• „ tX ∈ TU • n ^ #)
--  ATEl : ∀{Φ n} → AbsTm Φ (ATU n) ♭ → AbsTy Φ

TEl : ∀{n Γ} → (tA : Γ ⊢ TU Γ n ^ ♭) → Ty Γ
TEl {n}{Γ} tA Φ γ = (TEl0 T[ sub# ((λ Ψ γ' → •) „ TU • n ^ ♭ ∋ tA / tX) ]) Φ γ
--TEl : ∀{n Γ} → (tA : c♭ Γ ⊢ TU (c♭ Γ) n ^ ♭) → Ty Γ
--TEl {n}{Γ} tA Φ γ = ATEl (tA Φ {!!})

TEl[] : ∀{n Δ Γ} → {σ : Sub Δ Γ} → {tA : Γ ⊢ TU Γ n ^ ♭} → (TEl tA) T[ σ ] ≡ TEl (TU Γ n ∋ tA [ σ ])
TEl[] {n}{Δ}{Γ}{σ}{tA} = funext (λ Φ → funext (λ δ → map≡ (TEl0 Φ) (
    begin
      sub# (sub# (λ Φ₁ δ₁ → • “ (λ Φ₂ γ → ATU n) ^ ♭ ∋ tA Φ₁ δ₁ / tX)) Φ (sub# σ Φ δ)
    ≡⟨ map≡ (λ τ → τ Φ (sub# σ Φ δ)) (sub## {_}{_}{λ Φ₁ δ₁ → • “ (λ Φ₂ γ → ATU n) ^ ♭ ∋ tA Φ₁ δ₁ / tX}) ⟩
      sub# (λ Φ₁ θ → • “ (λ Φ₂ γ → ATU n) ^ ♭ ∋ tA Φ₁ (σ Φ₁ θ) / tX) Φ δ
    ≡⟨ sym≡ (map≡ (λ τ → τ Φ δ) (sub## {_}{_} {λ Φ₁ δ₁ → • “ (λ Φ₂ γ → ATU n) ^ ♭ ∋ tA Φ₁ (σ Φ₁ δ₁) / tX})) ⟩
      sub# (sub# (λ Φ₁ δ₁ → • “ (λ Φ₂ γ → ATU n) ^ ♭ ∋ tA Φ₁ (σ Φ₁ δ₁) / tX)) Φ δ
    ∎
  )))
--THIS SHOULDN'T BE NECESSARY 

{-
TEl : ∀{n Γ} → (tA : c♭ Γ ⊢ TU (c♭ Γ) n ^ ♭) → Ty Γ
TEl {n}{Γ} tA Φ γ = (TEl0 T[ sub# ((λ Ψ γ' → •) „ TU • n ^ ♭ ∋ tA / tX) ]) Φ γ
--TEl : ∀{n Γ} → (tA : c♭ Γ ⊢ TU (c♭ Γ) n ^ ♭) → Ty Γ
--TEl {n}{Γ} tA Φ γ = ATEl (tA Φ {!!})

TEl[] : ∀{n Δ Γ} → {σ : Sub Δ Γ} → {tA : c♭ Γ ⊢ TU (c♭ Γ) n ^ ♭} → (TEl tA) T[ σ ] ≡ TEl (TU (c♭ Γ) n ∋ tA [ sub♭ σ ])
TEl[] = {!!}
-}
