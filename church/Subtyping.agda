module church.Subtyping where

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
