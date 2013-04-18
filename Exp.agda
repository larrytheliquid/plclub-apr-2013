open import Types
module Exp where

----------------------------------------------------------------------

data Expr : Context → Type → Set where
  `tt : ∀{Γ} → Expr Γ `⊤
  `λ : ∀{Γ A B} → Expr (Γ , A) B → Expr Γ (A `→ B)
  _`,_ : ∀{Γ A B} → Expr Γ A → Expr Γ B → Expr Γ (A `× B)

  `var : ∀{Γ A} → Var Γ A → Expr Γ A
  _`$_ : ∀{Γ A B} → Expr Γ (A `→ B) → Expr Γ A → Expr Γ B
  `proj₁ : ∀{Γ A B} → Expr Γ (A `× B) → Expr Γ A
  `proj₂ : ∀{Γ A B} → Expr Γ (A `× B) → Expr Γ B

postulate
  subExpr : ∀{Γ A B} → Expr Γ B → (i : Var Γ A) → Expr (Γ - i) A → Expr (Γ - i) B

evalExpr : ∀{Γ A} → Expr Γ A → Expr Γ A
evalExpr `tt = `tt
evalExpr (`λ f) = `λ (evalExpr f)
evalExpr (a `, b) = evalExpr a `, evalExpr b
evalExpr (`var i) = `var i
evalExpr (f `$ a) with evalExpr f | evalExpr a
... | `λ f′ | a′ = evalExpr (subExpr f′ here a′)
... | f′ | a′ = f′ `$ a′
evalExpr (`proj₁ ab) with evalExpr ab
... | a `, b = a
... | ab′ = `proj₁ ab′
evalExpr (`proj₂ ab) with evalExpr ab
... | a `, b = b
... | ab′ = `proj₂ ab′

----------------------------------------------------------------------



----------------------------------------------------------------------
