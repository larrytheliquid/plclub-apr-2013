open import Types
open import Relation.Binary.PropositionalEquality
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

wknExpr : ∀{A Γ B} (i : Var Γ A) → Expr (Γ - i) B → Expr Γ B
wknExpr i `tt = `tt
wknExpr i (`λ f) = `λ (wknExpr (there i) f)
wknExpr i (a `, b) = wknExpr i a `, wknExpr i b
wknExpr i (`var j) = `var (wknVar i j)
wknExpr i (f `$ a) = wknExpr i f `$ wknExpr i a
wknExpr i (`proj₁ ab) = `proj₁ (wknExpr i ab) 
wknExpr i (`proj₂ ab) = `proj₂ (wknExpr i ab) 

subExpr : ∀{Γ A B} → Expr Γ B → (i : Var Γ A) → Expr (Γ - i) A → Expr (Γ - i) B
subExpr `tt i x = `tt
subExpr (`λ f) i x = `λ (subExpr f (there i) (wknExpr here x))
subExpr (a `, b) i x = subExpr a i x `, subExpr b i x
subExpr (`var j) i x with compare i j
subExpr (`var .i) i x | same = x
subExpr (`var .(wknVar i j)) i x | diff .i j = `var j
subExpr (f `$ a) i x = subExpr f i x `$ subExpr a i x
subExpr (`proj₁ ab) i x = `proj₁ (subExpr ab i x)
subExpr (`proj₂ ab) i x = `proj₂ (subExpr ab i x)

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

`id : ∀{Γ} → Expr Γ (`⊤ `→ `⊤)
`id = `λ (`var here)

`arg : ∀{Γ} → Expr Γ ((`⊤ `→ `⊤) `× `⊤)
`arg = `id `, `tt

`app : ∀{Γ} → Expr Γ ((`⊤ `→ `⊤) `× `⊤ `→ `⊤)
`app = `λ ((`proj₁ (`var here)) `$ (`proj₂ (`var here)))

`result : Expr ∅ `⊤
`result = evalExpr (`app `$ `arg)

`result≡tt : `result ≡ `tt
`result≡tt = refl

----------------------------------------------------------------------
