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
  *   : {n : ℕ} → Term n
  var : {n : ℕ} → Fin n → Term n
  abs : {n : ℕ} → Type → Term (suc n) → Term n
  app : {n : ℕ} → Term n → Term n → Term n

data Context : ℕ → Set where
  ∅ : Context 0
  _,_ : ∀ {n : ℕ} → Context n → Type → Context (suc n)

find : ∀ {n : ℕ} → Context n → Fin n → Type
find (Γ , x) fzero = x
find (Γ , x) (fsuc n) = find Γ n

demo₁ : Type
demo₁ = find (∅ , (Unit ⇒ Unit) ⇒ Unit , Unit , Unit ⇒ Unit) (fsuc (fsuc fzero))

data _∋_⦂_ : {n : ℕ} → Context n → Fin n → Type → Set where
  ∋-zero : ∀ {n : ℕ} {Γ : Context n} {A : Type}
    → Γ , A ∋ fzero ⦂ A
    
  ∋-suc : ∀ {n : ℕ} {Γ : Context n} {A B : Type} {x : Fin n}
    → Γ ∋ x ⦂ A
    → Γ , B ∋ fsuc x ⦂ A

data _⊢_⦂_ {n : ℕ} : Context n → Term n → Type → Set where
  ⊢unit : ∀ {Γ : Context n}
    → Γ ⊢ * ⦂ Unit

  ⊢var : ∀ {Γ : Context n} {A : Type} {x : Fin n}
    → Γ ∋ x ⦂ A
    → Γ ⊢ var x ⦂ A

  ⊢abs : ∀ {Γ : Context n} {A B : Type} {e : Term (suc n)}
    → Γ , A ⊢ e ⦂ B
    → Γ ⊢ abs A e ⦂ A ⇒ B

  ⊢app : ∀ {Γ : Context n} {A B : Type} {e₁ e₂ : Term n}
    → Γ ⊢ e₁ ⦂ A ⇒ B
    → Γ ⊢ e₂ ⦂ A
    → Γ ⊢ app e₁ e₂ ⦂ B

demo₂ : ∅ ⊢ app (abs Unit (var fzero)) * ⦂ Unit
demo₂ = ⊢app (⊢abs (⊢var ∋-zero)) ⊢unit

demo₃ : ∅ ⊢ abs (Unit ⇒ Unit) (abs Unit (app (var (fsuc fzero)) (var fzero))) ⦂ (Unit ⇒ Unit) ⇒ Unit ⇒ Unit
demo₃ = ⊢abs (⊢abs (⊢app (⊢var (∋-suc ∋-zero)) (⊢var ∋-zero)))

shift : {n : ℕ} → Term n → Fin (suc n) → Term (suc n)
shift (abs A e) x = abs A (shift e (fsuc x))
shift (app e₁ e₂) x = app (shift e₁ x) (shift e₂ x)
shift (var y) x = var (punchIn x y)
shift * x = *

infix 7 _[_≔_]

_[_≔_] : {n : ℕ} → Term (suc n) → Fin (suc n) → Term n → Term n
(abs A e) [ v ≔ x ] = abs A (e [ fsuc v ≔ shift x fzero ])
(app e₁ e₂) [ v ≔ x ] = app (e₁ [ v ≔ x ]) (e₂ [ v ≔ x ])
(var z) [ v ≔ x ] with v ≟ z
... | yes refl = x
... | no neq = var (punchOut {i = v} {j = z} λ {refl → neq (sym refl)})
* [ v ≔ x ] = *

data Value {n : ℕ} : Term n → Set where
  v-abs : ∀ {e : Term (suc n)} {A : Type}
    → Value (abs A e)

  v-* :
      Value *

infix 4 _↦_

data _↦_ {n : ℕ} : Term n → Term n → Set where
  ξ-app₁ : ∀ {e₁ e₁' e₂ : Term n}
    → e₁ ↦ e₁'
    → app e₁ e₂ ↦ app e₁' e₂

  ξ-app₂ : ∀ {e₁ e₂ e₂' : Term n}
    → Value e₁
    → e₂ ↦ e₂'
    → app e₁ e₂ ↦ app e₁ e₂'

  β-app : ∀ {e : Term (suc n)} {e₂ : Term n} {A : Type}
    → Value e₂
    → app (abs A e) e₂ ↦ e [ fzero ≔ e₂ ]


data Progress {n : ℕ} : (e : Term n) → Set where
  step : ∀ {e e' : Term n}
     → e ↦ e'
     → Progress e

  done : ∀ {e : Term n}
     → Value e
     → Progress e

infix 4 Canonical_⦂_

data Canonical_⦂_ : Term 0 → Type → Set where
  C-abs : ∀ {e : Term 1} {A B : Type}
    → ∅ , A ⊢ e ⦂ B
    → Canonical (abs A e) ⦂ A ⇒ B

  C-* :
      Canonical * ⦂ Unit

canonical : ∀ {v : Term 0} {A : Type}
  → ∅ ⊢ v ⦂ A
  → Value v
  → Canonical v ⦂ A
canonical ⊢unit V = C-*
canonical (⊢abs ⊢) V = C-abs ⊢
canonical (⊢app ⊢e₁ ⊢e₂) ()

progress : ∀ {e A}
  → ∅ ⊢ e ⦂ A
  → Progress e
progress ⊢unit = done v-*
progress (⊢abs ⊢) = done v-abs
progress (⊢app ⊢e₁ ⊢e₂) with progress ⊢e₁
... | step e₁↦ = step (ξ-app₁ e₁↦)
... | done ve₁ with progress ⊢e₂
...    | step e₂↦ = step (ξ-app₂ ve₁ e₂↦)
...    | done ve₂ with canonical ⊢e₁ ve₁
...      | C-abs _ = step (β-app ve₂)
