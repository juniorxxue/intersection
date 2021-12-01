module church.Lambda where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness)

infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_

infix  5 ƛ_
infixl 7 _∙_
infix  9 S_
infix  9 #_

data Type : Set where
  _⇒_ : Type → Type → Type
  Unit : Type

data Context : Set where
  ∅ : Context
  _,_ : Context → Type → Context

data _∋_ : Context → Type → Set where
  Z : ∀ {Γ A}
    → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ A
    → Γ , B ∋ A

data _⊢_ : Context → Type → Set where
  * : ∀ {Γ}
    → Γ ⊢ Unit

  var : ∀ {Γ A}
    → Γ ∋ A
    → Γ ⊢ A

  ƛ_ : ∀ {Γ A B}
    → Γ , A ⊢ B
    → Γ ⊢ A ⇒ B

  _∙_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
    → Γ ⊢ B

length : Context → ℕ
length ∅ = zero
length (Γ , _) = suc (length Γ)

lookup : {Γ : Context} → {n : ℕ} → (p : n < length Γ) → Type
lookup {(_ , A)} {zero} (s≤s z≤n) = A
lookup {(Γ , _)} {(suc n)} (s≤s p) = lookup p

count : ∀ {Γ} → {n : ℕ} → (p : n < length Γ) → Γ ∋ lookup p
count {_ , _} {zero}    (s≤s z≤n)  =  Z
count {Γ , _} {(suc n)} (s≤s p)    =  S (count p)

#_ : ∀ {Γ}
  → (n : ℕ)
    → {n∈Γ : True (suc n ≤? length Γ)}
  → Γ ⊢ lookup (toWitness n∈Γ)
#_ n {n∈Γ}  =  var (count (toWitness n∈Γ))

ext : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
  → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z = Z
ext ρ (S x) = S ρ x

rename : ∀ {Γ Δ}
       → (∀ {A} → Γ ∋ A → Δ ∋ A)
       → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ * = *
rename ρ (var x) = var (ρ x)
rename ρ (ƛ N) = ƛ rename (ext ρ) N
rename ρ (L ∙ M) = rename ρ L ∙ rename ρ M

exts : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ⊢ A)
  → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)
exts σ Z = var Z
exts σ (S x) = rename S_ (σ x)

subst : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ⊢ A)
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
subst σ * = *
subst σ (var x) = σ x
subst σ (ƛ N) = ƛ subst (exts σ) N
subst σ (L ∙ M) = subst σ L ∙ subst σ M

_[_] : ∀ {Γ A B}
  → Γ , B ⊢ A
  → Γ ⊢ B
  → Γ ⊢ A
_[_] {Γ} {A} {B} N M = subst {Γ , B} {Γ} σ {A} N
  where
  σ : ∀ {A} → Γ , B ∋ A → Γ ⊢ A
  σ Z = M
  σ (S N) = var N

data Value : ∀ {Γ A} → Γ ⊢ A → Set where
  V-* : ∀ {Γ}
    → Value (* {Γ})

  V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
    → Value (ƛ N)
  
infix 2 _⟿_

data _⟿_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where
  ξ-app₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L ⟿ L′
    → L ∙ M ⟿ L′ ∙ M

  ξ-app₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M ⟿ M′
    → V ∙ M ⟿ V ∙ M′

  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
    → Value W
    → (ƛ N) ∙ W ⟿ N [ W ]

data Progress {A} (M : ∅ ⊢ A) : Set where
  step : ∀ {N : ∅ ⊢ A}
    → M ⟿ N
    → Progress M

  done :
    Value M
    → Progress M

progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
progress * = done V-*
progress (ƛ M) = done V-ƛ
progress (L ∙ M) with progress L
... | step L⟿L′ = step (ξ-app₁ L⟿L′)
... | done V-ƛ with progress M
...     | step M⟿M′ = step (ξ-app₂ V-ƛ M⟿M′)
...     | done VM = step (β-ƛ VM)
