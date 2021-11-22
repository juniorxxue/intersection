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
    → TTop ≤ D
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
≤-refl (A ⇒ B) = SArr (≤-refl A) (≤-refl B)
≤-refl (A ∧ B) = SAnd (SAndL (≤-refl A)) (SAndR (≤-refl B))

≤-and-inv-l : {A B C : Typ} → A ≤ (B ∧ C) → A ≤ B
≤-and-inv-l (SAnd H H₁) = H
≤-and-inv-l (SAndL H) = SAndL (≤-and-inv-l H)
≤-and-inv-l (SAndR H) = SAndR (≤-and-inv-l H)

≤-and-inv-r : {A B C : Typ} → A ≤ (B ∧ C) → A ≤ C
≤-and-inv-r (SAnd H H₁) = H₁
≤-and-inv-r (SAndL H) = SAndL (≤-and-inv-r H)
≤-and-inv-r (SAndR H) = SAndR (≤-and-inv-r H)

≤-trans : {A B C : Typ} → (A ≤ B) → (B ≤ C) → (A ≤ C)
≤-trans A≤B SInt = A≤B
≤-trans A≤B STop = STop
≤-trans A≤B (STopArr B≤C) = STopArr B≤C
≤-trans (STopArr A≤B) (SArr B≤C B≤C₁) = STopArr (≤-trans A≤B B≤C₁)
≤-trans (SArr A≤B A≤B₁) (SArr B≤C B≤C₁) = SArr (≤-trans B≤C A≤B) (≤-trans A≤B₁ B≤C₁)
≤-trans (SAndL A≤B) (SArr B≤C B≤C₁) = SAndL (≤-trans A≤B (SArr B≤C B≤C₁))
≤-trans (SAndR A≤B) (SArr B≤C B≤C₁) = SAndR (≤-trans A≤B (SArr B≤C B≤C₁))
≤-trans A≤B (SAnd B≤C B≤C₁) = SAnd (≤-trans A≤B B≤C) (≤-trans A≤B B≤C₁)
≤-trans A≤B (SAndL B≤C) = ≤-trans (≤-and-inv-l A≤B) B≤C
≤-trans A≤B (SAndR B≤C) = ≤-trans (≤-and-inv-r A≤B) B≤C
