    module church.Subtyping where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥; ⊥-elim)

infixr 7 _⇒_
infixr 7 _&_
infix 5 _⇜_⇝_

data Type : Set where
  Int : Type
  Top : Type
  _⇒_ : Type → Type → Type
  _&_ : Type → Type → Type

-- l~ r~
data _⇜_⇝_ : Type → Type → Type → Set where
  sp-& : ∀ {A B}
    → A ⇜ A & B ⇝ B

  sp-⇒ : ∀ {A B B₁ B₂}
    → B₁ ⇜ B ⇝ B₂
    → A ⇒ B₁ ⇜ A ⇒ B ⇝ A ⇒ B₂

infix 5 ord_

data ord_ : Type → Set where
  ord-top :
      ord Top

  ord-int :
      ord Int

  ord-⇒ : ∀ {A B}
    → ord B
    → ord A ⇒ B

-- cuR cuL
infix 5 ⌉_⌈

data ⌉_⌈ : Type → Set where
  tl-top :
      ⌉ Top ⌈

  tl-& : ∀ {A B}
    → ⌉ A ⌈
    → ⌉ B ⌈
    → ⌉ A & B ⌈

  tl-⇒ : ∀ {A B}
    → ⌉ B ⌈
    → ⌉ A ⇒ B ⌈  

infix 5 _≤_

data _≤_ : Type → Type → Set where
  ≤-int :
      Int ≤ Int
  
  ≤-top : ∀ {A B}
    → ord B
    → ⌉ B ⌈
    → A ≤ B

  ≤-⇒ : ∀ {A B C D}
    → C ≤ A
    → B ≤ D
    → ord D
    → A ⇒ B ≤ C ⇒ D

  ≤-& : ∀ {A B B₁ B₂}
    → B₁ ⇜ B ⇝ B₂
    → A ≤ B₁
    → A ≤ B₂
    → A ≤ B

  ≤-&-l : ∀ {A B C}
    → A ≤ C
    → ord C
    → A & B ≤ C

  ≤-&-r : ∀ {A B C}
    → B ≤ C
    → ord C
    → A & B ≤ C


data proper : Type → Set where
  pr-int :
    proper Int

  pr-top :
    proper Top

  pr-fun : ∀ {A B}
    → ord B
    → proper A
    → proper B
    → proper (A ⇒ B)

  pr-split : ∀ {A A₁ A₂}
    → A₁ ⇜ A ⇝ A₂
    → proper A₁
    → proper A₂
    → proper A

proper-⇒ : ∀ {A B : Type}
  → proper A
  → proper B
  → proper (A ⇒ B)
proper-⇒ pA pr-int = pr-fun ord-int pA pr-int
proper-⇒ pA pr-top = pr-fun ord-top pA pr-top
proper-⇒ pA (pr-fun x pB pB₁) = pr-fun (ord-⇒ x) pA (proper-⇒ pB pB₁)
proper-⇒ pA (pr-split x pB pB₁) = pr-split (sp-⇒ x) (proper-⇒ pA pB) (proper-⇒ pA pB₁)

proper-complete : ∀ (A : Type) → proper A
proper-complete Int = pr-int
proper-complete Top = pr-top
proper-complete (A ⇒ B) = proper-⇒ (proper-complete A) (proper-complete B)
proper-complete (A & B) = pr-split sp-& (proper-complete A) (proper-complete B)

split-toplike-l : ∀ {A A₁ A₂ : Type}
  → A₁ ⇜ A ⇝ A₂
  → ⌉ A ⌈
  → ⌉ A₁ ⌈
split-toplike-l sp-& (tl-& tl₁ tl₂) = tl₁
split-toplike-l (sp-⇒ Aˢ) (tl-⇒ tl) = tl-⇒ (split-toplike-l Aˢ tl)

split-toplike-r : ∀ {A A₁ A₂ : Type}
  → A₁ ⇜ A ⇝ A₂
  → ⌉ A ⌈
  → ⌉ A₂ ⌈
split-toplike-r sp-& (tl-& tl₁ tl₂) = tl₂
split-toplike-r (sp-⇒ Aˢ) (tl-⇒ tl) = tl-⇒ (split-toplike-r Aˢ tl)


≤-toplike : ∀ {A B : Type} → ⌉ A ⌈ → B ≤ A
≤-toplike {A} {B} = ≤-toplike-p {A} {B} {proper-complete A}
  where
  ≤-toplike-p : ∀ {A} {B} {p : proper A} → ⌉ A ⌈ → B ≤ A
  ≤-toplike-p {p = pr-top} tl = ≤-top ord-top tl
  ≤-toplike-p {p = pr-fun x p p₁} tl = ≤-top (ord-⇒ x) tl
  ≤-toplike-p {p = pr-split Aᵒ p₁ p₂} tl = ≤-& Aᵒ (≤-toplike-p {p = p₁} (split-toplike-l Aᵒ tl)) (≤-toplike-p {p = p₂} (split-toplike-r Aᵒ tl))

_ : ∀ {A} → ⌉ A ⌈ → Int ≤ A
_ = ≤-toplike

-- https://github.com/agda/agda/blob/v2.6.1/CHANGELOG.md#termination-checking

-- split or ordinary
data Split (A : Type) : Set where
  sp-step : ∀ {A₁ A₂}
    → A₁ ⇜ A ⇝ A₂
    → Split A

  sp-done :
      ord A
    → Split A
    
split : ∀ (A : Type) → Split A
split Int = sp-done ord-int
split Top = sp-done ord-top
split (A ⇒ B) with split B
... | sp-step Bˢ = sp-step (sp-⇒ Bˢ)
... | sp-done Bᵒ = sp-done (ord-⇒ Bᵒ)
split (A & B) = sp-step sp-&

-- fully generated proof
≤-⇒-gen : ∀ {A B C D}
  → B ≤ D
  → C ≤ A
  → A ⇒ B ≤ C ⇒ D
≤-⇒-gen ≤-int ≤₂ = ≤-⇒ ≤₂ ≤-int ord-int
≤-⇒-gen (≤-top x x₁) ≤₂ = ≤-⇒ ≤₂ (≤-top x x₁) x
≤-⇒-gen (≤-⇒ ≤₁ ≤₃ x) ≤₂ = ≤-⇒ ≤₂ (≤-⇒-gen ≤₃ ≤₁) (ord-⇒ x)
≤-⇒-gen (≤-& x ≤₁ ≤₃) ≤₂ = ≤-& (sp-⇒ x) (≤-⇒-gen ≤₁ ≤₂) (≤-⇒-gen ≤₃ ≤₂)
≤-⇒-gen (≤-&-l ≤₁ x) ≤₂ = ≤-⇒ ≤₂ (≤-&-l ≤₁ x) x
≤-⇒-gen (≤-&-r ≤₁ x) ≤₂ = ≤-⇒ ≤₂ (≤-&-r ≤₁ x) x

-- fully generated proof
≤-&-l-gen : ∀ {A B C}
  → A ≤ C
  → A & B ≤ C
≤-&-l-gen ≤-int = ≤-&-l ≤-int ord-int
≤-&-l-gen (≤-top x x₁) = ≤-top x x₁
≤-&-l-gen (≤-⇒ s s₁ x) = ≤-&-l (≤-⇒ s s₁ x) (ord-⇒ x)
≤-&-l-gen (≤-& x s s₁) = ≤-& x (≤-&-l-gen s) (≤-&-l-gen s₁)
≤-&-l-gen (≤-&-l s x) = ≤-&-l (≤-&-l-gen s) x
≤-&-l-gen (≤-&-r s x) = ≤-&-l (≤-&-r s x) x

-- fully generated proof
≤-&-r-gen : ∀ {A B C}
  → B ≤ C
  → A & B ≤ C
≤-&-r-gen ≤-int = ≤-&-r ≤-int ord-int
≤-&-r-gen (≤-top x x₁) = ≤-top x x₁
≤-&-r-gen (≤-⇒ s s₁ x) = ≤-&-r (≤-⇒ s s₁ x) (ord-⇒ x)
≤-&-r-gen (≤-& x s s₁) = ≤-& x (≤-&-r-gen s) (≤-&-r-gen s₁)
≤-&-r-gen (≤-&-l s x) = ≤-&-r (≤-&-l s x) x
≤-&-r-gen (≤-&-r s x) = ≤-&-r (≤-&-r-gen s) x

≤-refl : ∀ {A}
  → A ≤ A
≤-refl {Int} = ≤-int
≤-refl {Top} = ≤-top ord-top tl-top
≤-refl {A ⇒ B} = ≤-⇒-gen ≤-refl ≤-refl
≤-refl {A & B} = ≤-& sp-& (≤-&-l-gen ≤-refl) (≤-&-r-gen ≤-refl)

sp-≤-l : ∀ {A A₁ A₂}
  → A₁ ⇜ A ⇝ A₂
  → A ≤ A₁
sp-≤-l sp-& = ≤-&-l-gen ≤-refl
sp-≤-l (sp-⇒ Bˢ) = ≤-⇒-gen (sp-≤-l Bˢ) ≤-refl

sp-≤-r : ∀ {A A₁ A₂}
  → A₁ ⇜ A ⇝ A₂
  → A ≤ A₂
sp-≤-r sp-& = ≤-&-r-gen ≤-refl
sp-≤-r (sp-⇒ Bˢ) = ≤-⇒-gen (sp-≤-r Bˢ) ≤-refl

sp-determinism₁ : ∀ {A A₁ A₂ A₃ A₄}
  → A₁ ⇜ A ⇝ A₂
  → A₃ ⇜ A ⇝ A₄
  → A₁ ≡ A₃
sp-determinism₁ sp-& sp-& = refl
sp-determinism₁ (sp-⇒ {B} Aˢ₁) (sp-⇒ {B} Aˢ₂) = cong (_⇒_ B) (sp-determinism₁ Aˢ₁ Aˢ₂)

sp-determinism₂ : ∀ {A A₁ A₂ A₃ A₄}
  → A₁ ⇜ A ⇝ A₂
  → A₃ ⇜ A ⇝ A₄
  → A₂ ≡ A₄
sp-determinism₂ sp-& sp-& = refl
sp-determinism₂ (sp-⇒ {B} Aˢ₁) (sp-⇒ {B} Aˢ₂) = cong (_⇒_ B) (sp-determinism₂ Aˢ₁ Aˢ₂)

sp-¬ord : ∀ {A A₁ A₂}
  → A₁ ⇜ A ⇝ A₂
  → ¬ ord A
sp-¬ord (sp-⇒ Aˢ) (ord-⇒ Aᵒ) = sp-¬ord Aˢ Aᵒ

≤-sp-l : ∀ {A B B₁ B₂}
  → A ≤ B
  → B₁ ⇜ B ⇝ B₂
  → A ≤ B₁
≤-sp-l (≤-top Bᵒ tl) Bˢ = ⊥-elim (sp-¬ord Bˢ Bᵒ)
≤-sp-l (≤-⇒ B≤D C≤A Dᵒ) (sp-⇒ Dˢ) = ⊥-elim (sp-¬ord Dˢ Dᵒ)
≤-sp-l (≤-& Bˢ₁ A≤B₃ A≤B₄) Bˢ₂ rewrite sp-determinism₁ Bˢ₁ Bˢ₂ = A≤B₃
≤-sp-l (≤-&-l A≤B₂ B₂ᵒ) B₂ˢ = ⊥-elim (sp-¬ord B₂ˢ B₂ᵒ)
≤-sp-l (≤-&-r B≤B₂ B₂ᵒ) B₂ˢ = ⊥-elim (sp-¬ord B₂ˢ B₂ᵒ)

≤-trans-p : ∀ {A B C : Type} {p : proper B} → A ≤ B → B ≤ C → A ≤ C
≤-trans-p {B = .Int} {p = pr-int} A≤B ≤-int = A≤B
≤-trans-p {B = .Int} {p = pr-int} A≤B (≤-top x x₁) = ≤-top x x₁
≤-trans-p {B = .Int} {p = pr-int} A≤B (≤-& x B≤C B≤C₁) = ≤-& x (≤-trans-p {p = pr-int} A≤B B≤C) (≤-trans-p {p = pr-int} A≤B B≤C₁)
≤-trans-p {B = .Top} {p = pr-top} A≤B (≤-top x x₁) = ≤-top x x₁
≤-trans-p {B = .Top} {p = pr-top} A≤B (≤-& x B≤C B≤C₁) = ≤-& x (≤-trans-p {p = pr-top} A≤B B≤C) (≤-trans-p {p = pr-top} A≤B B≤C₁)
≤-trans-p {B = .(_ ⇒ _)} {p = pr-fun Bᵒ p₁ p₂} A≤B (≤-top x x₁) = ≤-top x x₁
≤-trans-p {B = .(_ ⇒ _)} {p = pr-fun Bᵒ p₁ p₂} A≤B (≤-⇒ B≤C B≤C₁ x) = {!!}
≤-trans-p {B = .(_ ⇒ _)} {p = pr-fun Bᵒ p₁ p₂} A≤B (≤-& x B≤C B≤C₁) = ≤-& x (≤-trans-p {p = pr-fun Bᵒ p₁ p₂} A≤B B≤C) (≤-trans-p {p = pr-fun Bᵒ p₁ p₂} A≤B B≤C₁)
≤-trans-p {B = B} {p = pr-split x p p₁} A≤B B≤C = {!!}

≤-trans : ∀ {A B C}
  → A ≤ B
  → B ≤ C
  → A ≤ C
≤-trans = {!!}  
