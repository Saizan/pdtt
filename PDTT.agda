{-# OPTIONS --type-in-type --copatterns --rewriting #-}
module PDTT where

open import Relation.Binary.PropositionalEquality
{-# BUILTIN REWRITE _≡_ #-}

postulate
  U : Set
  `U : U
  _⁼ : Set -> Set
  El : U ⁼ -> Set

El⁼ : _ -> _
El⁼ = \ x → (El x) ⁼


postulate
  ι : ∀ {A} → A → A ⁼
  =-elim : ∀ {A}{B : A ⁼ → Set} → ((x : A) → B (ι x)) → (x : A ⁼) → (B x) ⁼

  =-beta : ∀ {A B} f a → =-elim {A} {B} f (ι a) ≡ ι (f a)

postulate
  `U-El : El (ι `U) ≡ U

{-# REWRITE `U-El #-}
{-# REWRITE =-beta #-}

postulate
  `Π : (A : U) → (B : El (ι A) → U) → U
  `Π-El : ∀ {A B} → El (ι (`Π A B)) ≡ ((x : El (ι A)) → El (ι (B x)))

  `∀ : (A : U) → (B : El (ι A) → U) → U
  `∀-El : ∀ {A : U}{B : El (ι A) → U} → El (ι (`∀ A B)) ≡ ((x : El⁼ (ι A)) → El (=-elim B x))

{-# REWRITE `Π-El #-}
{-# REWRITE `∀-El #-}

open import Data.Product

postulate
  ∫ : Set → Set
  σ : ∀ {A} → A → ∫ A
  ∫∫-elim : ∀ {A}{B : ∫ A → Set} → ((x : A) → B (σ x)) → (x : ∫ A ) → ∫ (B x)
  ∫-elim : ∀ {A}{B : ∫ A → U ⁼} → ((x : A) → El (B (σ x))) → (x : ∫ A ) → El (B x)
  ∫-beta : ∀ {A B} f a → ∫-elim {A} {B} f (σ a) ≡ f a

  ∫∫-beta : ∀ {A B} f a → ∫∫-elim {A} {B} f (σ a) ≡ σ (f a)

  `Σ : (A : U) → (B : El (ι A) → U) → U
  `Σ-El : ∀ {A B} → El (ι (`Σ A B)) ≡ Σ (El (ι A)) \ x → El (ι (B x))

  `∃ : (A : U) → (B : El (ι A) → U) → U
  `∃-El : ∀ {A B} → El (ι (`∃ A B)) ≡ (∫ (Σ (El⁼ (ι A)) (\ x → El (=-elim B x))))


{-# REWRITE `Σ-El #-}
{-# REWRITE `∃-El #-}
{-# REWRITE ∫-beta #-}
{-# REWRITE ∫∫-beta #-}

postulate
  𝔹 : U
  b0 b1 : El (ι 𝔹)

I = El (ι 𝔹) ⁼

i0 = ι b0
i1 = ι b1


record _⌢_ {A : Set} (x y : A) : Set where
   constructor con
   field
     bridge : El (ι 𝔹) -> A
     eq0 : bridge b0 ≡ x
     eq1 : bridge b1 ≡ y


theBridge : b0 ⌢ b1
_⌢_.bridge theBridge x = x
_⌢_.eq0 theBridge = refl
_⌢_.eq1 theBridge = refl


record _P─_ {A : El (ι 𝔹) → U} (x : El (ι (A b0)) )(y : El (ι (A b1))) : Set where
   constructor con
   field
     path : (i : I) -> El (=-elim A i)
     eq0 : path i0 ≡ x
     eq1 : path i1 ≡ y


record _─_ {A : Set} (x y : A) : Set where
   constructor con
   field
     path : I -> A
     eq0 : path i0 ≡ x
     eq1 : path i1 ≡ y

thePath : i0 ─ i1
_─_.path thePath = \ x → x
_─_.eq0 thePath  = refl
_─_.eq1 thePath  = refl


under : ∀ {A : Set}{x y : A} → x ─ y → x ⌢ y
_⌢_.bridge (under (con path eq0 eq1)) = λ x → path (ι x)
_⌢_.eq0 (under (con path eq0 eq1)) = eq0
_⌢_.eq1 (under (con path eq0 eq1)) = eq1


IsPath : ∀ {A : Set}{x y : A} → x ⌢ y → Set
IsPath b = Σ (_ ─ _) \ p → under p ≡ b

-- postulate
--   path-ext : {A : El (ι 𝔹) → U} (let A0 = El (ι (A b0)); A1 = El (ι (A b1)))
--               {α : A0 → A0} {β : A1 → A1}
-- A path between functions (over a bridge),
-- is iso to (a map from bridges to bridges that sends paths to paths) (over the functions) (over the bridge)


postulate
  ⌢-univ : ∀ {A B} → (f : El (ι A) → El (ι B)) → El (ι 𝔹) → U
  ⌢-univb0 : ∀ {A B} → (f : El (ι A) → El (ι B)) → ⌢-univ {A} {B} f b0 ≡ A
  ⌢-univb1 : ∀ {A B} → (f : El (ι A) → El (ι B)) → ⌢-univ {A} {B} f b1 ≡ B

{-# REWRITE   ⌢-univb0 #-}
{-# REWRITE   ⌢-univb1 #-}


postulate
  push : ∀ {A B} → (f : El (ι A) → El (ι B)) → (i : I) → (a : El (ι A)) → El (=-elim (⌢-univ {A} {B} f) i)
  pushi0 : ∀ {A B} (f : El (ι A) → El (ι B)) → (a : El (ι A)) → push {A} {B} f i0 a ≡ a
  pushi1 : ∀ {A B} (f : El (ι A) → El (ι B)) → (a : El (ι A)) → push {A} {B} f i1 a ≡ f a

  pull : ∀ {A B} → (f : El (ι A) → El (ι B)) → (i : I) → El (=-elim (⌢-univ {A} {B} f) i) → El (ι B)
  pulli0 : ∀ {A B} (f : El (ι A) → El (ι B)) x → pull {A} {B} f i0 x ≡ f x
  pulli1 : ∀ {A B} (f : El (ι A) → El (ι B)) x → pull {A} {B} f i1 x ≡ x

{-# REWRITE pushi0 #-}
{-# REWRITE pushi1 #-}
{-# REWRITE pulli0 #-}
{-# REWRITE pulli1 #-}


id : (X : U ⁼) → El X → El X
id _ x = x

postulate
  lemma : ∀ (Y : U ⁼) → El (=-elim (λ X → `Π X (λ _ → X)) Y) ≡ ((x : El Y) -> El Y)

{-# REWRITE lemma #-}
foo : (Y : U ⁼) → El (ι (`∃ `U \ X → `Π X (\ _ → X)))
foo = \ Y → σ (Y , id Y )

bar : ∀ {A B} → (f : El (ι A) → El (ι B)) → foo (ι A) ─ foo (ι B)
_─_.path (bar {A} {B} f) i = foo (=-elim ((⌢-univ {A} {B} f)) i)
_─_.eq0 (bar {A} {B} f) = refl
_─_.eq1 (bar {A} {B} f) = refl


baz : {A B : U} → (El (ι A) → El (ι B)) → σ (ι A , (λ x → x)) ─ σ (ι B , (λ x → x))
baz = bar

open import Data.Unit

postulate
 `⊤ : U
 `⊤-El : El (ι `⊤) ≡ ⊤

{-# REWRITE `⊤-El #-}

module IsId (f : (X : U ⁼) → El X → El X) where


  isid : ∀ A a → a ─ f (ι A) a
  _─_.path (isid A a) = let â : ⊤ → El (ι A)
                            â _ = a
                            X = ⌢-univ {`⊤} {A} â
                         in λ i → pull {`⊤} {A} â i (f (=-elim X i) (push {`⊤} {A} â i _))
  _─_.eq0 (isid A a) = refl
  _─_.eq1 (isid A a) = refl

open import Data.Bool

postulate
 `Bool : U
 `Bool-El : El (ι `Bool) ≡ Bool

{-# REWRITE `Bool-El #-}

open import Data.Sum
module IsBool (f : (X : U ⁼) → El X → El X -> El X) (A : U) (a b : El (ι A)) where

  g : Bool → El (ι A)
  g false = a
  g true = b

  X = ⌢-univ {`Bool} {A} g

  isbool' : g (f (ι `Bool) false true) ─ f (ι A) a b
  _─_.path isbool' = \ i → pull {`Bool} {A} g i (f (=-elim X i) (push {`Bool} {A} g i false) (push {`Bool} {A} g i true))
  _─_.eq0 isbool' = refl
  _─_.eq1 isbool' = refl


  isbool : (a ─ f (ι A) a b) ⊎ (b ─ f (ι A) a b)
  isbool with (f (ι `Bool) false true) | isbool'
  isbool | false | z = inj₁ z
  isbool | true  | z = inj₂ z


open import Data.Nat
postulate
 `ℕ : U
 `ℕ-El : El (ι `ℕ) ≡ ℕ
 _`≡_ : {A : U ⁼} → El A → El A → U
 `≡-El : ∀ {X A B} → El (ι (_`≡_ {A = X} A B)) ≡ (A ≡ B)

{-# REWRITE `ℕ-El #-}
{-# REWRITE `≡-El #-}

module IsNat (f : (X : U ⁼) → El X → (El X -> El X) -> El X) (A : U) (a0 : El (ι A)) (as : El (ι A) → El (ι A)) where

  g : ℕ → El (ι A)
  g zero = a0
  g (suc n) = as (g n)

  ImG : U
  ImG = `Σ `ℕ (λ n → `Σ A \ a → _`≡_ {ι A} (g n) a)

  p1 : El (ι ImG) -> ℕ
  p1 (n , _) = n

  p2 : El (ι ImG) -> El (ι A)
  p2 (n , a , _) = a

  img0 : El (ι ImG)
  img0 = 0 , (a0 , refl)
  img1 : El (ι ImG) → El (ι ImG)
  img1 (n , _ , refl) = (suc n , _ , refl)

  postulate
    foo2 : p2 (f (ι ImG) img0 img1) ─ f (ι A) a0 as
    foo1 : p1 (f (ι ImG) img0 img1) ─ f (ι `ℕ) zero suc
