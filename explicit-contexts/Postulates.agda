{-# OPTIONS --copatterns --rewriting #-}

module Postulates where

open import Data.Product
open import Data.Nat
open import Relation.Binary.PropositionalEquality hiding ([_])
{-# BUILTIN REWRITE _≡_ #-}

_sa_ : (T : Set) → T → T
T sa t = t

postulate
  Ctx : Set -- set of contexts
  Var : Set -- set of variables; if you prefer to ignore variables, think of this as Unit
  Ty : (Γ : Ctx) → Set -- set of types
  _⊢_ : (Γ : Ctx) → Ty Γ → Set -- set of terms
  
infix 5 _⊢_

--Substitutions-------------------
postulate
  Sub : Ctx → Ctx → Set
  id : ∀{Γ} → Sub Γ Γ
  _∘_ : ∀{Θ Δ Γ} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
  _T[_] : ∀{Δ Γ} → Ty Γ → Sub Δ Γ → Ty Δ
  id∘ : ∀{Δ Γ} → {σ : Sub Δ Γ} → id ∘ σ ≡ σ
  ∘id : ∀{Δ Γ} → {σ : Sub Δ Γ} → σ ∘ id ≡ σ
  ∘∘ : ∀{Λ Θ Δ Γ} → {σ : Sub Δ Γ} → {τ : Sub Θ Δ} → {υ : Sub Λ Θ} → (σ ∘ τ) ∘ υ ≡ σ ∘ (τ ∘ υ)
  T[id] : ∀{Γ} → {T : Ty Γ} → T T[ id ] ≡ T
  T[][] : ∀{Θ Δ Γ} → {T : Ty Γ} → {σ : Sub Δ Γ} → {τ : Sub Θ Δ} → T T[ σ ] T[ τ ] ≡ T T[ σ ∘ τ ]
{-# REWRITE id∘ #-}
{-# REWRITE ∘id #-}
{-# REWRITE ∘∘ #-}
{-# REWRITE T[id] #-}
{-# REWRITE T[][] #-}
postulate
  _[_] : ∀{Δ Γ} → {T : Ty Γ} → (Γ ⊢ T) → (σ : Sub Δ Γ) → (Δ ⊢ T T[ σ ])
  [id] : ∀{Γ} → {T : Ty Γ} → (t : Γ ⊢ T) → t [ id ] ≡ t
  [][] : ∀{Θ Δ Γ} → {T : Ty Γ} → {t : Γ ⊢ T} → {σ : Sub Δ Γ} → {τ : Sub Θ Δ} → t [ σ ] [ τ ] ≡ t [ σ ∘ τ ]
{-# REWRITE [id] #-}
{-# REWRITE [][] #-}

infixr 15 _∘_
infix 10 _T[_] _[_]

--Context extension---------------
postulate 
  _„_∈_ : (Γ : Ctx) → Var → Ty Γ → Ctx  --\glqq
  π : ∀{Γ x} → {T : Ty Γ} → Sub (Γ „ x ∈ T) Γ
  ξ : ∀{Γ} → (x : Var) → {T : Ty Γ} → Γ „ x ∈ T ⊢ T T[ π ]
  _„_∋_/_ : ∀ {Δ Γ} → (σ : Sub Δ Γ) → (T : Ty Γ) → Δ ⊢ T T[ σ ] → (x : Var) → Sub Δ (Γ „ x ∈ T)
  π∘„ : ∀{Δ Γ T} → {σ : Sub Δ Γ} → {t : Δ ⊢ T T[ σ ]} → {x : Var} → π ∘ (σ „ T ∋ t / x) ≡ σ
{-# REWRITE π∘„ #-}
postulate
  ξ[„] : ∀{Δ Γ x T} → {σ : Sub Δ Γ} → {t : Δ ⊢ T T[ σ ]} → ξ x [ σ „ T ∋ t / x ] ≡ t
  π„ξ : ∀{Δ Γ x T} → {τ : Sub Δ (Γ „ x ∈ T)} → (π ∘ τ „ T ∋ ξ x [ τ ] / x) ≡ τ
  „∘ : ∀{Θ Δ Γ x T} → {σ : Sub Δ Γ} → {t : Δ ⊢ T T[ σ ]} → {τ : Sub Θ Δ} → (σ „ T ∋ t / x) ∘ τ ≡ σ ∘ τ „ T ∋ t [ τ ] / x
{-# REWRITE ξ[„] #-}
{-# REWRITE π„ξ #-}
{-# REWRITE „∘ #-}

{-
test1 : ∀{Δ Γ x T} → {σ : Sub Δ Γ} → {t : Δ ⊢ T T[ σ ]} → ξ x [ σ „ T ∋ t / x ] ≡ t
test1 = refl
test2 : ∀{Δ x T} → {t : Δ ⊢ T} → ξ x [ id „ T ∋ t / x ] ≡ t
test2 = refl
test3 : ∀{Δ Γ x S} → {σ : Sub Δ Γ} → {t : Δ ⊢ S T[ σ ]} → ξ x [ id „ S T[ σ ] ∋ t / x ] ≡ t
test3 {Δ}{Γ}{x}{S}{σ}{t} = refl --test2{Δ}{x}{S T[ σ ]}{t}
-}

--ξ y [ id „ S T[ σ ] ∋ s [ σ ] / y ]

infix 10 _„_∋_/_
infix 8 _„_∈_
{-
postulate --Flat (º in the notes)---------------
  -- ♭ for contexts
  c♭ : Ctx → Ctx
  c♭² : ∀{Γ} → c♭ (c♭ Γ) ≡ c♭ Γ
{-# REWRITE c♭² #-}
postulate
  -- ♭ for types
  ♭ : ∀{Γ} → Ty Γ → Ty Γ
  ♭[] : ∀{Δ Γ} → {σ : Sub Δ Γ} → {T : Ty Γ} → ♭ T T[ σ ] ≡ ♭ (T T[ σ ])
{-# REWRITE ♭[] #-}
postulate
  -- κ between contexts
  κ : ∀{Γ} → Sub (c♭ Γ) Γ
  c♭„ : ∀{Γ x T} → c♭(Γ „ x ∈ T) ≡ c♭ Γ „ x ∈ ♭ T T[ κ ]
{-# REWRITE c♭„ #-}
postulate
  π∘κ : ∀{Γ x T} → π ∘ κ{Γ „ x ∈ T} ≡ κ ∘ π
{-# REWRITE π∘κ #-}
postulate
  -- κ between types
  tκ : ∀{Γ T} → Γ ⊢ ♭ T → Γ ⊢ T
  tκ[] : ∀{Δ Γ T} → {σ : Sub Δ Γ} → {t : Γ ⊢ ♭ T} → tκ(t)[ σ ] ≡ tκ (t [ σ ])
{-# REWRITE tκ[] #-}
postulate
  ξ[κ] : ∀{Γ x T} → ξ x [ κ{Γ „ x ∈ T} ] ≡ tκ (ξ x)
{-# REWRITE ξ[κ] #-}

postulate --Sharp-----------------------------
  -- # for contexts
  c# : Ctx → Ctx
  c#² : ∀{Γ} → c# (c# Γ) ≡ c# Γ
  c#♭ : ∀{Γ} → c# (c♭ Γ) ≡ c# Γ
{-# REWRITE c#² #-}
{-# REWRITE c#♭ #-}
postulate
  -- # for types
  # : ∀{Γ} → Ty Γ → Ty Γ
  #[] : ∀{Δ Γ} → {σ : Sub Δ Γ} → {T : Ty Γ} → # T T[ σ ] ≡ # (T T[ σ ])
{-# REWRITE #[] #-}
postulate
  -- # for substitutions
  s# : ∀{Δ Γ} → Sub Δ Γ → Sub (c# Δ) (c# Γ)
  s#-id : ∀{Γ} → s# (id{Γ}) ≡ id
  s#-∘ : ∀{Θ Δ Γ} → {σ : Sub Δ Γ} → {τ : Sub Θ Δ} → s# (σ ∘ τ) ≡ s# σ ∘ s# τ
{-# REWRITE s#-id #-}
{-# REWRITE s#-∘ #-}
postulate
  -- ι between contexts
  ι : ∀{Γ} → Sub Γ (c# Γ)
  s#ι : ∀{Γ} → s# (ι{Γ}) ≡ id
  c#„ : ∀{Γ x T} → c#(Γ „ x ∈ T T[ ι ]) ≡ (c# Γ) „ x ∈ # T
{-# REWRITE s#ι #-}
{-# REWRITE c#„ #-}
postulate
  π∘ι : ∀{Γ x T} → π ∘ ι{Γ „ x ∈ T T[ ι ]} ≡ ι ∘ π
{-# REWRITE π∘ι #-}
postulate
  -- ι between types
  tι : ∀{Γ T} → Γ ⊢ T → Γ ⊢ # T
  tι[] : ∀{Δ Γ T} → {σ : Sub Δ Γ} → {t : Γ ⊢ T} → tι(t)[ σ ] ≡ tι (t [ σ ])
{-# REWRITE tι[] #-}
postulate
  ξ[ι] : ∀{Γ x T} → ξ x [ ι{Γ „ x ∈ T T[ ι ]} ] ≡ tι (ξ x)
{-# REWRITE ξ[ι] #-}

postulate --Universe--------------------------
  U : (n : ℕ) → ∀{Γ} → Ty Γ
  U[] : ∀{n Δ Γ} → {σ : Sub Δ Γ} → U n T[ σ ] ≡ U n
{-# REWRITE U[] #-}
postulate
  Elprim : ∀{n Γ} → Γ ⊢ U n → Ty (c# Γ)
  Elprim[] : ∀{n Δ Γ} → {σ : Sub Δ Γ} → {tA : Γ ⊢ U n} → (Elprim tA)T[ s# σ ] ≡ Elprim (tA [ σ ])
{-# REWRITE Elprim[] #-}

El : ∀{n Γ} → c♭ Γ ⊢ U n → Ty Γ
El tA = Elprim tA T[ ι ]

postulate
  tU : (n : ℕ) → ∀{Γ} → Γ ⊢ U (suc n)
  tU[] : ∀{n Δ Γ} → {σ : Sub Δ Γ} → tU n [ σ ] ≡ tU n
  Elprim-tU : ∀{n Γ} → Elprim{Γ = Γ}(tU n) ≡ U n
{-# REWRITE tU[] #-}
{-# REWRITE Elprim-tU #-}

postulate --Σ-type---------------------------
  TΣ : ∀{Γ} → (S : Ty Γ) → ((x : Var) → Ty(Γ „ x ∈ S)) → Ty Γ
  TΣ[] : ∀{Δ Γ S T} → {σ : Sub Δ Γ} → (TΣ S T) T[ σ ] ≡ TΣ (S T[ σ ]) (λ x → T x T[ σ ∘ π „ S ∋ ξ x / x ])
{-# REWRITE TΣ[] #-}
postulate
  t[_,_] : ∀{Γ S T} →
    (s : Γ ⊢ S) →
    (t : (y : Var) → Γ ⊢ T y T[ id „ S ∋ s / y ]) →
    ----------------------
    Γ ⊢ TΣ S T
  t[,][] : ∀{Δ Γ S T s t} → {σ : Sub Δ Γ} →
    t[_,_] {Γ}{S}{T} s t [ σ ] ≡
    t[ s [ σ ] , (λ y → {!(Δ ⊢ T y T[ {!!} ]) sa ({!t y [ σ ]!})!}) ]
  tp1 : ∀{Γ S T} →
    (p : Γ ⊢ TΣ S T) →
    -------------------
    Γ ⊢ S
  tp2 : ∀{Γ S T} →
    (p : Γ ⊢ TΣ S T) →
    -------------------
    (x : Var) → Γ ⊢ T x T[ id „ S ∋ tp1 p / x ]
  βΣ1 : ∀{Γ S T s t} → tp1{Γ}{S}{T} t[ s , t ] ≡ s
{-# REWRITE βΣ1 #-}
postulate
  βΣ2 : ∀{Γ S T s t} → tp2{Γ}{S}{T} t[ s , t ] ≡ t
{-# REWRITE βΣ2 #-}
postulate
  ηΣ : ∀{Γ S T p} → t[ tp1{Γ}{S}{T} p , tp2 p ] ≡ p
{-# REWRITE ηΣ #-}

postulate --Π-type-----------------------------
  TΠ : ∀{Γ} → (S : Ty Γ) → ((x : Var) → Ty(Γ „ x ∈ S)) → Ty Γ
  TΠ[] : ∀{Δ Γ S T} → {σ : Sub Δ Γ} → (TΠ S T) T[ σ ] ≡ TΠ (S T[ σ ]) (λ x → T x T[ σ ∘ π „ S ∋ ξ x / x ])
{-# REWRITE TΠ[] #-}
postulate
  tλ : ∀{Γ S T} →
    (t : (x : Var) → Γ „ x ∈ S ⊢ T x) →
    ---------------------------------
    Γ ⊢ TΠ S T
  tap : ∀{Γ S T} →
    (f : Γ ⊢ TΠ S T) →
    (s : Γ ⊢ S) →
    --------------------------
    (x : Var) → Γ ⊢ T x T[ id „ S ∋ s / x ]
  βΠ : ∀{Γ S T t s} → tap{Γ}{S}{T} (tλ t) s ≡ (λ x → t x [ id „ S ∋ s / x ])
  ηΠ : ∀{Γ S T f} → tλ{Γ}{S}{T} {!tap (f [ π ]) ?!} ≡ f
-}
