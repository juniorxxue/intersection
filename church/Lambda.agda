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
exts σ ∈ = {!!}
