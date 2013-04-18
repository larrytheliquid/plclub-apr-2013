open import Types
module Exp where

----------------------------------------------------------------------

data Expr : Context → Type → Set where
  `tt : ∀{Γ} → Expr Γ `⊤
  `λ : ∀{Γ A B} → Expr (Γ , A) B → Expr Γ (A `→ B)
  _`,_ : ∀{Γ A B} → Expr Γ A → Expr Γ B → Expr Γ (A `× B)


