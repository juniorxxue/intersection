module DeBruijn where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)

infix  4 _∋_⦂_
infix  4 _⊢_⦂_
infixl 5 _,_
infixr 7 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  Unit : Type
  
data Term : ℕ → Set where
  *   : ∀ {n : ℕ} → Term n
  var : ∀ {n : ℕ} → Fin n → Term n
  abs : ∀ {n : ℕ} → Type → Term (suc n) → Term n
  app : ∀ {n : ℕ} → Term n → Term n → Term n


data Context : ℕ → Set where
  ∅ : Context 0
  _,_ : ∀ {n : ℕ} → Context n → Type → Context (suc n)

find : ∀ {n : ℕ} → Context n → Fin n → Type
find (Γ , x) fzero = x
find (Γ , x) (fsuc n) = find Γ n

demo₁ : Type
demo₁ = find (∅ , (Unit ⇒ Unit) ⇒ Unit , Unit , Unit ⇒ Unit) (fsuc (fsuc fzero))

data _∋_⦂_ : ∀ {n : ℕ} → Context n → Fin n → Type → Set where
  vzero :
    ∀ {A : Type} {n : ℕ} {Γ : Context n}
    → Γ , A ∋ fzero ⦂ A
    
  vsuc :
    ∀ {A B : Type} {n : ℕ} {v : Fin n} {Γ : Context n}
    → Γ ∋ v ⦂ A
    → Γ , B ∋ fsuc v ⦂ A


data _⊢_⦂_ : ∀ {n : ℕ} → Context n → Term n → Type → Set where
  ⊢unit :
    ∀ {n : ℕ} {Γ : Context n}
    → Γ ⊢ * ⦂ Unit


  ⊢var :
    {n : ℕ} {Γ : Context n} {A : Type} {x : Fin n}
    → Γ ∋ x ⦂ A
    → Γ ⊢ var x ⦂ A

  ⊢abs :
    ∀ {n : ℕ} {Γ : Context n} {A B : Type} {e : Term (suc n)}
    → Γ , A ⊢ e ⦂ B
    → Γ ⊢ abs A e ⦂ A ⇒ B

  ⊢app :
    ∀ {n : ℕ} {Γ : Context n} {A B : Type} {e₁ e₂ : Term n}
    → Γ ⊢ e₁ ⦂ A ⇒ B
    → Γ ⊢ e₂ ⦂ A
    → Γ ⊢ app e₁ e₂ ⦂ B
