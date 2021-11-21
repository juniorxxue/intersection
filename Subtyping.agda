module intersection.Subtyping where

data Typ : Set where
  TInt : Typ
  TTop : Typ
  _⇒_  : Typ → Typ → Typ
  _∧_ : Typ → Typ → Typ

data _≤_ : Typ → Typ → Set where
  SInt :
      TInt ≤ TInt
  STop : ∀ {A : Typ}
    → A ≤ TTop
  STopArr : ∀ {A C D : Typ}
    → A ≤ (C ⇒ D)
  SArr : ∀ {A B C D : Typ}
    → C ≤ A
    → B ≤ D
    → (A ⇒ B) ≤ (C ⇒ D)
  SAnd : ∀ {A B C : Typ}
    → A ≤ B
    → A ≤ C
    → A ≤ (B ∧ C)
  SAndL : ∀ {A B C : Typ}
    → A ≤ C
    → (A ∧ B) ≤ C
  SAndR : ∀ {A B C : Typ}
    → B ≤ C
    → (A ∧ B) ≤ C
    
≤-refl : (A : Typ) → (A ≤ A)
≤-refl TInt = SInt
≤-refl TTop = STop
≤-refl (A ⇒ A₁) = SArr (≤-refl A) (≤-refl A₁)
≤-refl (A ∧ A₁) = SAnd (SAndL (≤-refl A)) (SAndR (≤-refl A₁))
