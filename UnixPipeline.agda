open import Types
open import Relation.Binary.PropositionalEquality
open import SubExpr using
  ( Expr ; `tt ; _`,_ ; `λ ; `var ; `proj₁ ; `proj₂ ; _`$_ ;
    `id ; `arg ; `app )
module UnixPipeline where

infixr 9 `|return `|proj₁ `|proj₂ `|$

----------------------------------------------------------------------

mutual
  data Value : Context → Type → Set where
    `tt : ∀{Γ} → Value Γ `⊤
    _`,_ : ∀{Γ A B} → Value Γ A → Value Γ B → Value Γ (A `× B)
    `λ : ∀{Γ A B} → Value (Γ , A) B → Value Γ (A `→ B)
    `neutral : ∀{Γ A} → Neutral Γ A → Value Γ A

  data Neutral : Context → Type → Set where
    `run : ∀{Γ A B} → Var Γ A → Command Γ A B → Neutral Γ B

  data Command : Context → Type → Type → Set where
    `|return : ∀{A Γ} → Command Γ A A
    `|proj₁ : ∀{Γ A B C} → Command Γ A C → Command Γ (A `× B) C
    `|proj₂ : ∀{Γ A B C} → Command Γ B C → Command Γ (A `× B) C
    `|$ : ∀{Γ A B C} → Value Γ A → Command Γ B C → Command Γ (A `→ B) C

----------------------------------------------------------------------

mutual
  wknValue : ∀{Γ A B} (i : Var Γ A) → Value (Γ - i) B → Value Γ B
  wknValue i `tt = `tt
  wknValue i (a `, b) = wknValue i a `, wknValue i b
  wknValue i (`λ f) = `λ (wknValue (there i) f)
  wknValue i (`neutral (`run j n)) = `neutral (`run (wknVar i j) (wknCommand i n))

  wknCommand :  ∀{Γ A B C} (i : Var Γ A) → Command (Γ - i) B C → Command Γ B C
  wknCommand i `|return = `|return
  wknCommand i (`|proj₁ c) = `|proj₁ (wknCommand i c)
  wknCommand i (`|proj₂ c) = `|proj₂ (wknCommand i c)
  wknCommand i (`|$ a c) = `|$ (wknValue i a) (wknCommand i c)

----------------------------------------------------------------------

append`proj₁ : ∀{Γ A B C} → Command Γ C (A `× B) → Command Γ C A
append`proj₁ `|return = `|proj₁ `|return
append`proj₁ (`|proj₁ c) = `|proj₁ (append`proj₁ c)
append`proj₁ (`|proj₂ c) = `|proj₂ (append`proj₁ c)
append`proj₁ (`|$ a c) = `|$ a (append`proj₁ c)

append`proj₂ : ∀{Γ A B C} → Command Γ C (A `× B) → Command Γ C B
append`proj₂ `|return = `|proj₂ `|return
append`proj₂ (`|proj₁ c) = `|proj₁ (append`proj₂ c)
append`proj₂ (`|proj₂ c) = `|proj₂ (append`proj₂ c)
append`proj₂ (`|$ a c) = `|$ a (append`proj₂ c)

append`$ : ∀{Γ A B C} → Command Γ C (A `→ B) → Value Γ A → Command Γ C B
append`$ `|return v = `|$ v `|return
append`$ (`|proj₁ c) v = `|proj₁ (append`$ c v)
append`$ (`|proj₂ c) v = `|proj₂ (append`$ c v)
append`$ (`|$ a c) v = `|$ a (append`$ c v)

----------------------------------------------------------------------

eval`proj₁ : ∀{Γ A B} → Value Γ (A `× B) → Value Γ A
eval`proj₁ (a `, b) = a
eval`proj₁ (`neutral (`run i c)) = `neutral (`run i (append`proj₁ c))

eval`proj₂ : ∀{Γ A B} → Value Γ (A `× B) → Value Γ B
eval`proj₂ (a `, b) = b
eval`proj₂ (`neutral (`run i c)) = `neutral (`run i (append`proj₂ c))

----------------------------------------------------------------------

mutual
  eval`$ : ∀{Γ A B} → Value Γ (A `→ B) → Value Γ A → Value Γ B
  eval`$ (`λ f) a = hsubValue f here a
  eval`$ (`neutral (`run i c)) a = `neutral (`run i (append`$ c a))

  hsubValue : ∀{Γ A B} → Value Γ B → (i : Var Γ A) → Value (Γ - i) A → Value (Γ - i) B
  hsubValue `tt i v = `tt
  hsubValue (a `, b) i v = hsubValue a i v `, hsubValue b i v
  hsubValue (`λ f) i v = `λ (hsubValue f (there i) (wknValue here v))
  hsubValue (`neutral n) i v = hsubNeutral n i v

  hsubNeutral : ∀{Γ A B} → Neutral Γ B → (i : Var Γ A) → Value (Γ - i) A → Value (Γ - i) B
  hsubNeutral (`run j c) i v with compare i j
  hsubNeutral (`run .i c) i v | same = eval`| v (hsubCommand c i v)
  hsubNeutral (`run .(wknVar i j) n) .i v | diff i j = `neutral (`run j (hsubCommand n i v))

  hsubCommand : ∀{Γ A B C} → Command Γ B C → (i : Var Γ A) → Value (Γ - i) A → Command (Γ - i) B C
  hsubCommand `|return i v = `|return
  hsubCommand (`|proj₁ c) i ab = `|proj₁ (hsubCommand c i ab)
  hsubCommand (`|proj₂ c) i ab = `|proj₂ (hsubCommand c i ab)
  hsubCommand (`|$ a c) i f = `|$ (hsubValue a i f) (hsubCommand c i f)

  eval`| : ∀{Γ A B} → Value Γ A → Command Γ A B → Value Γ B
  eval`| v `|return = v
  eval`| ab (`|proj₁ c) = eval`| (eval`proj₁ ab) c
  eval`| ab (`|proj₂ c) = eval`| (eval`proj₂ ab) c
  eval`| f (`|$ a c) = eval`| (eval`$ f a) c

----------------------------------------------------------------------

eval : ∀{Γ A} → Expr Γ A → Value Γ A
eval `tt = `tt
eval (a `, b) = eval a `, eval b
eval (`λ f) = `λ (eval f)
eval (`var i) = `neutral (`run i `|return)
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
  `λ
  (`neutral (`run here
    (`|proj₁ (`|$ (`neutral (`run here (`|proj₂ `|return))) `|return))))
`test-intermediate-result = refl

----------------------------------------------------------------------
