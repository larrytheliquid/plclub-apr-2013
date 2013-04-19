open import Types
open import Relation.Binary.PropositionalEquality
module Exp where

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

wkn : ∀{Γ A B} (i : Var Γ A) → Expr (Γ - i) B → Expr Γ B
wkn i `tt = `tt
wkn i (a `, b) = wkn i a `, wkn i b
wkn i (`λ f) = `λ (wkn (there i) f)
wkn i (`var j) = `var (wknVar i j)
wkn i (`proj₁ ab) = `proj₁ (wkn i ab) 
wkn i (`proj₂ ab) = `proj₂ (wkn i ab)
wkn i (f `$ a) = wkn i f `$ wkn i a

----------------------------------------------------------------------

sub : ∀{Γ A B} → Expr Γ B → (i : Var Γ A) → Expr (Γ - i) A → Expr (Γ - i) B
sub `tt i x = `tt
sub (a `, b) i x = sub a i x `, sub b i x
sub (`λ f) i x = `λ (sub f (there i) (wkn here x))
sub (`var j) i x with compare i j
sub (`var .i) i x | same = x
sub (`var .(wknVar i j)) i x | diff .i j = `var j
sub (`proj₁ ab) i x = `proj₁ (sub ab i x)
sub (`proj₂ ab) i x = `proj₂ (sub ab i x)
sub (f `$ a) i x = sub f i x `$ sub a i x

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
... | `λ f′ | a′ = eval₁ (sub f′ here a′)
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
eval`$ : ∀{Γ A B} → Expr Γ (A `→ B) → Expr Γ A → Expr Γ B
eval : ∀{Γ A} → Expr Γ A → Expr Γ A

eval`$ (`λ f) a = eval (sub f here a)
eval`$ f a = f `$ a

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
