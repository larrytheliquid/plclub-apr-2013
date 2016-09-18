open import Types
open import Relation.Binary.PropositionalEquality
module SubExpr where

----------------------------------------------------------------------

data Expr : Context → Type → Set where
  `tt : ∀{Γ} → Expr Γ `⊤
  _`,_ : ∀{Γ A B} → Expr Γ A → Expr Γ B → Expr Γ (A `× B)
  `λ : ∀{Γ A B} → Expr (Γ , A) B → Expr Γ (A `→ B)

  `var : ∀{Γ A} → Var Γ A → Expr Γ A
  `proj₁ : ∀{Γ A B} → Expr Γ (A `× B) → Expr Γ A
  `proj₂ : ∀{Γ A B} → Expr Γ (A `× B) → Expr Γ B
  _`$_ : ∀{Γ A B} → Expr Γ (A `→ B) → Expr Γ A → Expr Γ B

----------------------------------------------------------------------

wknExpr : ∀{Γ A B} (i : Var Γ A) → Expr (Γ - i) B → Expr Γ B
wknExpr i `tt = `tt
wknExpr i (a `, b) = wknExpr i a `, wknExpr i b
wknExpr i (`λ f) = `λ (wknExpr (there i) f)
wknExpr i (`var j) = `var (wknVar i j)
wknExpr i (`proj₁ ab) = `proj₁ (wknExpr i ab)
wknExpr i (`proj₂ ab) = `proj₂ (wknExpr i ab)
wknExpr i (f `$ a) = wknExpr i f `$ wknExpr i a

----------------------------------------------------------------------

subExpr : ∀{Γ A B} → Expr Γ B → (i : Var Γ A) → Expr (Γ - i) A → Expr (Γ - i) B
subExpr `tt i x = `tt
subExpr (a `, b) i x = subExpr a i x `, subExpr b i x
subExpr (`λ f) i x = `λ (subExpr f (there i) (wknExpr here x))
subExpr (`var j) i x with compare i j
subExpr (`var .i) i x | same = x
subExpr (`var .(wknVar i j)) i x | diff .i j = `var j
subExpr (`proj₁ ab) i x = `proj₁ (subExpr ab i x)
subExpr (`proj₂ ab) i x = `proj₂ (subExpr ab i x)
subExpr (f `$ a) i x = subExpr f i x `$ subExpr a i x

----------------------------------------------------------------------

{-# NO_TERMINATION_CHECK #-}
eval₁ : ∀{Γ A} → Expr Γ A → Expr Γ A
eval₁ `tt = `tt
eval₁ (a `, b) = eval₁ a `, eval₁ b
eval₁ (`λ f) = `λ (eval₁ f)
eval₁ (`var i) = `var i
eval₁ (`proj₁ ab) with eval₁ ab
... | a `, b = a
... | ab′ = `proj₁ ab′
eval₁ (`proj₂ ab) with eval₁ ab
... | a `, b = b
... | ab′ = `proj₂ ab′
eval₁ (f `$ a) with eval₁ f | eval₁ a
... | `λ f′ | a′ = eval₁ (subExpr f′ here a′)
... | f′ | a′ = f′ `$ a′

----------------------------------------------------------------------

eval`proj₁ : ∀{Γ A B} → Expr Γ (A `× B) → Expr Γ A
eval`proj₁ (a `, b) = a
eval`proj₁ ab = `proj₁ ab

eval`proj₂ : ∀{Γ A B} → Expr Γ (A `× B) → Expr Γ B
eval`proj₂ (a `, b) = b
eval`proj₂ ab = `proj₂ ab

----------------------------------------------------------------------

{-# NO_TERMINATION_CHECK #-}
mutual
  eval`$ : ∀{Γ A B} → Expr Γ (A `→ B) → Expr Γ A → Expr Γ B
  eval`$ (`λ f) a = eval (subExpr f here a)
  eval`$ f a = f `$ a

  eval : ∀{Γ A} → Expr Γ A → Expr Γ A
  eval `tt = `tt
  eval (a `, b) = eval a `, eval b
  eval (`λ f) = `λ (eval f)
  eval (`var i) = `var i
  eval (`proj₁ ab) = eval`proj₁ (eval ab)
  eval (`proj₂ ab) = eval`proj₂ (eval ab)
  eval (f `$ a) = eval`$ (eval f) (eval a)

----------------------------------------------------------------------

`id : ∀{Γ} → Expr Γ (`⊤ `→ `⊤)
`id = `λ (`var here)

`arg : ∀{Γ} → Expr Γ ((`⊤ `→ `⊤) `× `⊤)
`arg = `id `, `tt

`app : ∀{Γ} → Expr Γ ((`⊤ `→ `⊤) `× `⊤ `→ `⊤)
`app = `λ (`id `$ (`proj₁ (`var here) `$ `proj₂ (`var here)))

----------------------------------------------------------------------

`result : Expr ∅ `⊤
`result = eval (`app `$ `arg)

`test-result : `result ≡ `tt
`test-result = refl

----------------------------------------------------------------------

`intermediate-result : Expr ∅ ((`⊤ `→ `⊤) `× `⊤ `→ `⊤)
`intermediate-result = eval `app

`test-intermediate-result :
  `intermediate-result ≡
  `λ (`proj₁ (`var here) `$ `proj₂ (`var here))
`test-intermediate-result = refl

----------------------------------------------------------------------
