open import Types
open import Relation.Binary.PropositionalEquality
open import SubExpr using
  ( Expr ; `tt ; _`,_ ; `λ ; `var ; `proj₁ ; `proj₂ ; _`$_ ;
    `id ; `arg ; `app )
module HSubNeutral where

----------------------------------------------------------------------

mutual
  data Value : Context → Type → Set where
    `tt : ∀{Γ} → Value Γ `⊤
    _`,_ : ∀{Γ A B} → Value Γ A → Value Γ B → Value Γ (A `× B)
    `λ : ∀{Γ A B} → Value (Γ , A) B → Value Γ (A `→ B)
    `neutral : ∀{Γ A} → Neutral Γ A → Value Γ A

  data Neutral : Context → Type → Set where
    `var : ∀{Γ A} → Var Γ A → Neutral Γ A
    `proj₁ : ∀{Γ A B} → Neutral Γ (A `× B) → Neutral Γ A
    `proj₂ : ∀{Γ A B} → Neutral Γ (A `× B) → Neutral Γ B
    _`$_ : ∀{Γ A B} → Neutral Γ (A `→ B) → Value Γ A → Neutral Γ B

----------------------------------------------------------------------

mutual
  wknValue : ∀{Γ A B} (i : Var Γ A) → Value (Γ - i) B → Value Γ B
  wknValue i `tt = `tt
  wknValue i (a `, b) = wknValue i a `, wknValue i b
  wknValue i (`λ f) = `λ (wknValue (there i) f)
  wknValue i (`neutral n) = `neutral (wknNeutral i n)

  wknNeutral :  ∀{Γ A B} (i : Var Γ A) → Neutral (Γ - i) B → Neutral Γ B
  wknNeutral i (`var j) = `var (wknVar i j)
  wknNeutral i (`proj₁ n) = `proj₁ (wknNeutral i n)
  wknNeutral i (`proj₂ n) = `proj₂ (wknNeutral i n)
  wknNeutral i (n `$ a) = wknNeutral i n `$ wknValue i a

----------------------------------------------------------------------

eval`proj₁ : ∀{Γ A B} → Value Γ (A `× B) → Value Γ A
eval`proj₁ (a `, b) = a
eval`proj₁ (`neutral ab) = `neutral (`proj₁ ab)

eval`proj₂ : ∀{Γ A B} → Value Γ (A `× B) → Value Γ B
eval`proj₂ (a `, b) = b
eval`proj₂ (`neutral ab) = `neutral (`proj₂ ab)

----------------------------------------------------------------------

{-# NO_TERMINATION_CHECK #-}
mutual
  eval`$ : ∀{Γ A B} → Value Γ (A `→ B) → Value Γ A → Value Γ B
  eval`$ (`λ f) a = hsubValue f here a
  eval`$ (`neutral f) a = `neutral (f `$ a)

  hsubValue : ∀{Γ A B} → Value Γ B → (i : Var Γ A) → Value (Γ - i) A → Value (Γ - i) B
  hsubValue `tt i v = `tt
  hsubValue (a `, b) i v = hsubValue a i v `, hsubValue b i v
  hsubValue (`λ f) i v = `λ (hsubValue f (there i) (wknValue here v))
  hsubValue (`neutral n) i v = hsubNeutral n i v

  hsubNeutral : ∀{Γ A B} → Neutral Γ B → (i : Var Γ A) → Value (Γ - i) A → Value (Γ - i) B
  hsubNeutral (`var j) i v with compare i j
  hsubNeutral (`var .i) i x | same = x
  hsubNeutral (`var .(wknVar i j)) i x | diff .i j = `neutral (`var j)
  hsubNeutral (`proj₁ ab) i v = eval`proj₁ (hsubNeutral ab i v)
  hsubNeutral (`proj₂ ab) i v = eval`proj₂ (hsubNeutral ab i v)
  hsubNeutral (f `$ a) i v = eval`$ (hsubNeutral f i v) (hsubValue a i v)

----------------------------------------------------------------------

eval : ∀{Γ A} → Expr Γ A → Value Γ A
eval `tt = `tt
eval (a `, b) = eval a `, eval b
eval (`λ f) = `λ (eval f)
eval (`var i) = `neutral (`var i)
eval (`proj₁ ab) = eval`proj₁ (eval ab)
eval (`proj₂ ab) = eval`proj₂ (eval ab)
eval (f `$ a) = eval`$ (eval f) (eval a)

----------------------------------------------------------------------

`result : Value ∅ `⊤
`result = eval (`app `$ `arg)

`test-result : `result ≡ `tt
`test-result = refl

----------------------------------------------------------------------

`intermediate-result : Value ∅ ((`⊤ `→ `⊤) `× `⊤ `→ `⊤)
`intermediate-result = eval `app

`test-intermediate-result :
  `intermediate-result ≡
  `λ (`neutral (`proj₁ (`var here) `$ `neutral (`proj₂ (`var here))))
`test-intermediate-result = refl

----------------------------------------------------------------------
