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
