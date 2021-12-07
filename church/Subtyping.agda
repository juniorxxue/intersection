module church.Subtyping where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; subst)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

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

sp-toplike : ∀ {A A₁ A₂}
  → A₁ ⇜ A ⇝ A₂
  → ⌉ A₁ ⌈
  → ⌉ A₂ ⌈
  → ⌉ A ⌈
sp-toplike sp-& tl₁ tl₂ = tl-& tl₁ tl₂
sp-toplike (sp-⇒ sp) (tl-⇒ tl₁) (tl-⇒ tl₂) = tl-⇒ (sp-toplike sp tl₁ tl₂)

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

sp-iso : ∀ {A A₁ A₂}
  → A₁ ⇜ A ⇝ A₂
  → A ≤ (A₁ & A₂)
sp-iso sp-A = ≤-& sp-& (sp-≤-l sp-A) (sp-≤-r sp-A)

≤-inv-sp-ord : ∀ {A A₁ A₂ B}
  → A ≤ B
  → A₁ ⇜ A ⇝ A₂
  → ord B
  → (A₁ ≤ B) ⊎ (A₂ ≤ B)
≤-inv-sp-ord (≤-top x x₁) sp-A ord-B = inj₁ (≤-top ord-B x₁)
≤-inv-sp-ord (≤-⇒ C≤A B≤D x) (sp-⇒ sp-B) (ord-⇒ ord-D) with ≤-inv-sp-ord B≤D sp-B ord-D
... | inj₁ y = inj₁ (≤-⇒ C≤A y x)
... | inj₂ y = inj₂ (≤-⇒ C≤A y x)
≤-inv-sp-ord (≤-& x A≤B A≤B₁) sp-A ord-B = ⊥-elim (sp-¬ord x ord-B)
≤-inv-sp-ord (≤-&-l A≤B x) sp-& ord-B = inj₁ A≤B
≤-inv-sp-ord (≤-&-r A≤B x) sp-& ord-B = inj₂ A≤B

≤-inv-sp-l : ∀ {A B B₁ B₂}
  → A ≤ B
  → B₁ ⇜ B ⇝ B₂
  → A ≤ B₁
≤-inv-sp-l (≤-top Bᵒ tl) Bˢ = ⊥-elim (sp-¬ord Bˢ Bᵒ)
≤-inv-sp-l (≤-⇒ B≤D C≤A Dᵒ) (sp-⇒ Dˢ) = ⊥-elim (sp-¬ord Dˢ Dᵒ)
≤-inv-sp-l (≤-& Bˢ₁ A≤B₃ A≤B₄) Bˢ₂ rewrite sp-determinism₁ Bˢ₁ Bˢ₂ = A≤B₃
≤-inv-sp-l (≤-&-l A≤B₂ B₂ᵒ) B₂ˢ = ⊥-elim (sp-¬ord B₂ˢ B₂ᵒ)
≤-inv-sp-l (≤-&-r B≤B₂ B₂ᵒ) B₂ˢ = ⊥-elim (sp-¬ord B₂ˢ B₂ᵒ)

≤-inv-sp-r : ∀ {A B B₁ B₂}
  → A ≤ B
  → B₁ ⇜ B ⇝ B₂
  → A ≤ B₂
≤-inv-sp-r (≤-top Bᵒ tl) Bˢ = ⊥-elim (sp-¬ord Bˢ Bᵒ)
≤-inv-sp-r (≤-⇒ B≤D C≤A Dᵒ) (sp-⇒ Dˢ) = ⊥-elim (sp-¬ord Dˢ Dᵒ)
≤-inv-sp-r (≤-& Bˢ₁ A≤B₃ A≤B₄) Bˢ₂ rewrite sp-determinism₂ Bˢ₁ Bˢ₂ = A≤B₄
≤-inv-sp-r (≤-&-l A≤B₂ B₂ᵒ) B₂ˢ = ⊥-elim (sp-¬ord B₂ˢ B₂ᵒ)
≤-inv-sp-r (≤-&-r B≤B₂ B₂ᵒ) B₂ˢ = ⊥-elim (sp-¬ord B₂ˢ B₂ᵒ)

≤-inv-sp : ∀ {A B B₁ B₂}
  → A ≤ B
  → B₁ ⇜ B ⇝ B₂
  → (A ≤ B₁) × (A ≤ B₂)
≤-inv-sp A≤B sp-B = ⟨ ≤-inv-sp-l A≤B sp-B , ≤-inv-sp-r A≤B sp-B ⟩

≤-toplike-preservation : ∀ {A B : Type}
  → ⌉ A ⌈
  → A ≤ B
  → ⌉ B ⌈
≤-toplike-preservation tl-A (≤-top x x₁) = x₁
≤-toplike-preservation (tl-⇒ tl-A) (≤-⇒ A≤B A≤B₁ x) = tl-⇒ (≤-toplike-preservation tl-A A≤B₁)
≤-toplike-preservation tl-A (≤-& x A≤B A≤B₁) = sp-toplike x (≤-toplike-preservation tl-A A≤B) (≤-toplike-preservation tl-A A≤B₁)
≤-toplike-preservation (tl-& tl-A tl-A₁) (≤-&-l A≤B x) = ≤-toplike-preservation tl-A A≤B
≤-toplike-preservation (tl-& tl-A tl-A₁) (≤-&-r A≤B x) = ≤-toplike-preservation tl-A₁ A≤B

≤-trans-p : ∀ {A B C : Type} → proper B → proper C → A ≤ B → B ≤ C → A ≤ C
≤-trans-p pr-int pC A≤B ≤-int = A≤B
≤-trans-p pr-int pC A≤B (≤-top ord-C tl-C) = ≤-top ord-C tl-C
≤-trans-p pr-int pC A≤B (≤-& {B₁ = B₁} {B₂ = B₂} sp-C ≤₁ ≤₂) = ≤-& sp-C (≤-trans-p pr-int (proper-complete B₁) A≤B ≤₁) (≤-trans-p pr-int (proper-complete B₂) A≤B ≤₂)
≤-trans-p pr-top pC A≤B (≤-top ord-C tl-C) = ≤-top ord-C tl-C
≤-trans-p pr-top pC A≤B (≤-& {B₁ = B₁} {B₂ = B₂} sp-C ≤₁ ≤₂) = ≤-& sp-C (≤-trans-p pr-top (proper-complete B₁) A≤B ≤₁) (≤-trans-p pr-top (proper-complete B₂) A≤B ≤₂)
≤-trans-p (pr-fun ord-B p₁ p₂) pC A≤B (≤-top ord-C tl-C) = ≤-top ord-C tl-C
≤-trans-p (pr-fun ord-B p₁ p₂) pC (≤-top (ord-⇒ ord-B′) (tl-⇒ tl-B)) (≤-⇒ ≤₁ ≤₂ ord-D) = ≤-top (ord-⇒ ord-D) (tl-⇒ (≤-toplike-preservation tl-B ≤₂))
≤-trans-p (pr-fun ord-B p₁ p₂) pC (≤-⇒ {A = A} ≤₃ ≤₄ ord-B₁) (≤-⇒ {D = D} ≤₁ ≤₂ ord-D) = ≤-⇒ (≤-trans-p p₁ (proper-complete A) ≤₁ ≤₃) (≤-trans-p p₂ (proper-complete D) ≤₄ ≤₂) ord-D
≤-trans-p (pr-fun ord-B p₁ p₂) pC (≤-& (sp-⇒ sp-B) ≤₃ ≤₄) (≤-⇒ ≤₁ ≤₂ ord-D) = ⊥-elim (sp-¬ord sp-B ord-B)
≤-trans-p (pr-fun ord-B p₁ p₂) pC (≤-&-l A≤B (ord-⇒ ord-B₁)) (≤-⇒ ≤₁ ≤₂ ord-D) = ≤-&-l-gen (≤-trans-p (pr-fun ord-B₁ p₁ p₂) pC A≤B (≤-⇒ ≤₁ ≤₂ ord-D))
≤-trans-p (pr-fun ord-B p₁ p₂) pC (≤-&-r A≤B (ord-⇒ ord-B₁)) (≤-⇒ ≤₁ ≤₂ ord-D) = ≤-&-r-gen (≤-trans-p (pr-fun ord-B₁ p₁ p₂) pC A≤B (≤-⇒ ≤₁ ≤₂ ord-D))
≤-trans-p (pr-fun ord-B p₁ p₂) pC A≤B (≤-& {B₁ = B₁} {B₂ = B₂} sp-C ≤₁ ≤₂) = ≤-& sp-C (≤-trans-p (pr-fun ord-B p₁ p₂) (proper-complete B₁) A≤B ≤₁) (≤-trans-p (pr-fun ord-B p₁ p₂) (proper-complete B₂) A≤B ≤₂)
≤-trans-p (pr-split sp-B p₁ p₂) pr-int A≤B B≤C with ≤-inv-sp-ord B≤C sp-B ord-int
... | inj₁ x = ≤-trans-p p₁ pr-int {!!} x
... | inj₂ y = ≤-trans-p p₂ pr-int (proj₂ (≤-inv-sp A≤B sp-B)) y
≤-trans-p (pr-split sp-B p₁ p₂) pr-top A≤B B≤C = ≤-top ord-top tl-top
≤-trans-p (pr-split sp-B p₁ p₂) (pr-fun ord-B p₃ p₄) A≤B B≤C with ≤-inv-sp-ord B≤C sp-B (ord-⇒ ord-B)
... | inj₁ x = ≤-trans-p p₁ (pr-fun ord-B p₃ p₄) (proj₁ (≤-inv-sp A≤B sp-B)) x
... | inj₂ y = ≤-trans-p p₂ {!!} {!!} y
≤-trans-p (pr-split sp-B p₁ p₂) (pr-split x pC pC₁) A≤B B≤C = {!!}

≤-trans : {A B C : Type} → A ≤ B → B ≤ C → A ≤ C
≤-trans {B = B} A≤B B≤C with proper-complete B
≤-trans {B = .Int} A≤B ≤-int | pr-int = A≤B
≤-trans {B = .Int} A≤B (≤-top x x₁) | pr-int = ≤-top x x₁
≤-trans {B = .Int} A≤B (≤-& x B≤C B≤C₁) | pr-int = ≤-& x (≤-trans A≤B B≤C) (≤-trans A≤B B≤C₁)
≤-trans {B = .Top} A≤B (≤-top x x₁) | pr-top = ≤-top x x₁
≤-trans {B = .Top} A≤B (≤-& x B≤C B≤C₁) | pr-top = ≤-& x (≤-trans A≤B B≤C) (≤-trans A≤B B≤C₁)
≤-trans {B = .(_ ⇒ _)} A≤B (≤-top x₁ x₂) | pr-fun x ors ors₁ = ≤-top x₁ x₂
≤-trans {B = .(_ ⇒ _)} (≤-top (ord-⇒ x₂) (tl-⇒ x₃)) (≤-⇒ B≤C B≤C₁ x₁) | pr-fun x ors ors₁ = ≤-top (ord-⇒ x₁) (tl-⇒ (≤-toplike-preservation x₃ B≤C₁))
≤-trans {B = .(_ ⇒ _)} (≤-⇒ A≤B A≤B₁ x₂) (≤-⇒ B≤C B≤C₁ x₁) | pr-fun x ors ors₁ = ≤-⇒ (≤-trans B≤C A≤B) (≤-trans A≤B₁ B≤C₁) x₁
≤-trans {B = .(_ ⇒ _)} (≤-& (sp-⇒ x₂) A≤B A≤B₁) (≤-⇒ B≤C B≤C₁ x₁) | pr-fun x ors ors₁ = ⊥-elim (sp-¬ord x₂ x)
≤-trans {B = .(_ ⇒ _)} (≤-&-l A≤B (ord-⇒ x₂)) (≤-⇒ B≤C B≤C₁ x₁) | pr-fun x ors ors₁ = ≤-&-l (≤-trans A≤B (≤-⇒ B≤C B≤C₁ x₁)) (ord-⇒ x₁)
≤-trans {B = .(_ ⇒ _)} (≤-&-r A≤B x₂) (≤-⇒ B≤C B≤C₁ x₁) | pr-fun x ors ors₁ = ≤-&-r (≤-trans A≤B (≤-⇒ B≤C B≤C₁ x₁)) (ord-⇒ x₁)
≤-trans {B = .(_ ⇒ _)} A≤B (≤-& x₁ B≤C B≤C₁) | pr-fun x ors ors₁ = ≤-& x₁ (≤-trans A≤B B≤C) (≤-trans A≤B B≤C₁)
≤-trans {A = A} {C = C} A≤B B≤C | pr-split {A₂ = A₂} x ors ors₁ with proper-complete C
≤-trans {A = A} {_} {C = .Int} A≤B B≤C | pr-split {A₂ = A₂} x ors ors₁ | pr-int with ≤-trans (≤-inv-sp-l A≤B x) | ≤-inv-sp-ord B≤C x ord-int
... | rec | inj₁ x₁ = rec x₁
... | rec | inj₂ y = {!!}
≤-trans {A = A} {_} {C = .Top} A≤B B≤C | pr-split {A₂ = A₂} x ors ors₁ | pr-top = {!!}
≤-trans {A = A} {_} {C = .(_ ⇒ _)} A≤B B≤C | pr-split {A₂ = A₂} x ors ors₁ | pr-fun x₁ orcs orcs₁ = {!!}
≤-trans {A = A} {_} {C = C} A≤B B≤C | pr-split {A₂ = A₂} x ors ors₁ | pr-split x₁ orcs orcs₁ = {!!}
