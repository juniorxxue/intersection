module intersection.DeBruijn where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; _≟_ ; punchIn; punchOut) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
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

private
  variable
    n : ℕ
    x : Fin n
    Γ : Context n
    A B : Type
    e e' e₁ e₂ e₁' e₂' : Term n

find : ∀ {n : ℕ} → Context n → Fin n → Type
find (Γ , x) fzero = x
find (Γ , x) (fsuc n) = find Γ n

demo₁ : Type
demo₁ = find (∅ , (Unit ⇒ Unit) ⇒ Unit , Unit , Unit ⇒ Unit) (fsuc (fsuc fzero))

data _∋_⦂_ : Context n → Fin n → Type → Set where
  ∋-zero :
      Γ , A ∋ fzero ⦂ A
    
  ∋-suc :
      Γ ∋ x ⦂ A
    → Γ , B ∋ fsuc x ⦂ A

data _⊢_⦂_ : Context n → Term n → Type → Set where
  ⊢unit :
      Γ ⊢ * ⦂ Unit

  ⊢var :
      Γ ∋ x ⦂ A
    → Γ ⊢ var x ⦂ A

  ⊢abs :
      Γ , A ⊢ e ⦂ B
    → Γ ⊢ abs A e ⦂ A ⇒ B

  ⊢app :
      Γ ⊢ e₁ ⦂ A ⇒ B
    → Γ ⊢ e₂ ⦂ A
    → Γ ⊢ app e₁ e₂ ⦂ B


demo₂ : ∅ ⊢ app (abs Unit (var fzero)) * ⦂ Unit
demo₂ = ⊢app (⊢abs (⊢var ∋-zero)) ⊢unit


demo₃ : ∅ ⊢ abs (Unit ⇒ Unit) (abs Unit (app (var (fsuc fzero)) (var fzero))) ⦂ (Unit ⇒ Unit) ⇒ Unit ⇒ Unit
demo₃ = ⊢abs (⊢abs (⊢app (⊢var (∋-suc ∋-zero)) (⊢var ∋-zero)))

shift : Term n → Fin (suc n) → Term (suc n)
shift (abs A e) x = abs A (shift e (fsuc x))
shift (app e₁ e₂) x = app (shift e₁ x) (shift e₂ x)
shift (var y) x = var (punchIn x y)
shift * x = *

infix 7 _[_≔_]

_[_≔_] : Term (suc n) → Fin (suc n) → Term n → Term n
(abs A e) [ v ≔ x ] = abs A (e [ fsuc v ≔ shift x fzero ])
(app e₁ e₂) [ v ≔ x ] = app (e₁ [ v ≔ x ]) (e₂ [ v ≔ x ])
(var z) [ v ≔ x ] with v ≟ z
... | yes refl = x
... | no neq = var (punchOut {i = v} {j = z} λ {refl → neq (sym refl)})
* [ v ≔ x ] = *

data Value {n} : Term n → Set where
  v-abs :
    Value (abs A e)

  v-* :
    Value *

infix 4 _↦_

data _↦_ : Term n → Term n → Set where
  ξ-app₁ :
     e₁ ↦ e₁'
    → app e₁ e₂ ↦ app e₁' e₂

  ξ-app₂ :
      Value e₁
    → e₂ ↦ e₂'
    → app e₁ e₂ ↦ app e₁ e₂'

  β-app :
      Value e₂
    → app (abs A e) e₂ ↦ e [ fzero ≔ e₂ ]


data Progress : (e : Term n) → Set where

  step :
       e ↦ e'
     → Progress e


  done :
       Value e
     → Progress e

infix 4 Canonical_⦂_

data Canonical_⦂_ : Term n → Type → Set where
  C-abs :
      ∅ , A ⊢ e ⦂ B
    → Canonical (abs A e) ⦂ A ⇒ B

  C-* :
      Canonical * ⦂ Unit

progress : ∅ ⊢ e ⦂ A → Progress e
progress ⊢unit = done v-*
progress (⊢abs ⊢) = done v-abs
progress (⊢app ⊢e₁ ⊢e₂) with progress ⊢e₁
... | step e₁↦ = step (ξ-app₁ e₁↦)
... | done ve₁ with progress ⊢e₂
...     | step e₂↦ = step (ξ-app₂ ve₁ e₂↦)
...     | done ve₂ = {!!}
