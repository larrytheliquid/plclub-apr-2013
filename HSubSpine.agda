open import Types
open import Relation.Binary.PropositionalEquality
open import SubExpr using
  ( Expr ; `tt ; _`,_ ; `λ ; `var ; `proj₁ ; `proj₂ ; _`$_ ;
    `id ; `arg ; `app )
module HSubSpine where

----------------------------------------------------------------------

mutual
  data Value : Context → Type → Set where
    `tt : ∀{Γ} → Value Γ `⊤
    _`,_ : ∀{Γ A B} → Value Γ A → Value Γ B → Value Γ (A `× B)
    `λ : ∀{Γ A B} → Value (Γ , A) B → Value Γ (A `→ B)
    `neutral : ∀{Γ A} → Neutral Γ A → Value Γ A

  data Neutral : Context → Type → Set where
    `spine : ∀{Γ A B} → Var Γ A → Spine Γ A B → Neutral Γ B

  data Spine : Context → Type → Type → Set where
    `yield : ∀{A Γ} → Spine Γ A A
    `proj₁ : ∀{Γ A B C} → Spine Γ A C → Spine Γ (A `× B) C
    `proj₂ : ∀{Γ A B C} → Spine Γ B C → Spine Γ (A `× B) C
    _`$_ : ∀{Γ A B C} → Spine Γ B C → Value Γ A → Spine Γ (A `→ B) C

----------------------------------------------------------------------

mutual
  wknValue : ∀{Γ A B} (i : Var Γ A) → Value (Γ - i) B → Value Γ B
  wknValue i `tt = `tt
  wknValue i (a `, b) = wknValue i a `, wknValue i b
  wknValue i (`λ f) = `λ (wknValue (there i) f)
  wknValue i (`neutral (`spine j n)) = `neutral (`spine (wknVar i j) (wknSpine i n))

  wknSpine :  ∀{Γ A B C} (i : Var Γ A) → Spine (Γ - i) B C → Spine Γ B C
  wknSpine i `yield = `yield
  wknSpine i (`proj₁ n) = `proj₁ (wknSpine i n)
  wknSpine i (`proj₂ n) = `proj₂ (wknSpine i n)
  wknSpine i (n `$ a) = wknSpine i n `$ wknValue i a

----------------------------------------------------------------------

append`proj₁ : ∀{Γ A B C} → Spine Γ C (A `× B) → Spine Γ C A
append`proj₁ `yield = `proj₁ `yield
append`proj₁ (`proj₁ s) = `proj₁ (append`proj₁ s)
append`proj₁ (`proj₂ s) = `proj₂ (append`proj₁ s)
append`proj₁ (s `$ a) = append`proj₁ s `$ a

append`proj₂ : ∀{Γ A B C} → Spine Γ C (A `× B) → Spine Γ C B
append`proj₂ `yield = `proj₂ `yield
append`proj₂ (`proj₁ s) = `proj₁ (append`proj₂ s)
append`proj₂ (`proj₂ s) = `proj₂ (append`proj₂ s)
append`proj₂ (s `$ a) = append`proj₂ s `$ a

append`$ : ∀{Γ A B C} → Spine Γ C (A `→ B) → Value Γ A → Spine Γ C B
append`$ `yield v = `yield `$ v
append`$ (`proj₁ s) v = `proj₁ (append`$ s v)
append`$ (`proj₂ s) v = `proj₂ (append`$ s v)
append`$ (s `$ a) v = append`$ s v `$ a

----------------------------------------------------------------------

eval`proj₁ : ∀{Γ A B} → Value Γ (A `× B) → Value Γ A
eval`proj₁ (a `, b) = a
eval`proj₁ (`neutral (`spine i s)) = `neutral (`spine i (append`proj₁ s))

eval`proj₂ : ∀{Γ A B} → Value Γ (A `× B) → Value Γ B
eval`proj₂ (a `, b) = b
eval`proj₂ (`neutral (`spine i s)) = `neutral (`spine i (append`proj₂ s))

----------------------------------------------------------------------

mutual
  eval`$ : ∀{Γ A B} → Value Γ (A `→ B) → Value Γ A → Value Γ B
  --    A `→ B                      A
  eval`$ (`λ f) a = hsubValue f here a
  eval`$ (`neutral (`spine i s)) a = `neutral (`spine i (append`$ s a))

  hsubValue : ∀{Γ A B} → Value Γ B → (i : Var Γ A) → Value (Γ - i) A → Value (Γ - i) B
  hsubValue `tt i v = `tt
  hsubValue (a `, b) i v = hsubValue a i v `, hsubValue b i v
  hsubValue (`λ f) i v = `λ (hsubValue f (there i) (wknValue here v))
  --                     v = v ∧ (n < `neutral n)
  hsubValue (`neutral n) i v = hsubNeutral n i v

  hsubNeutral : ∀{Γ A B} → Neutral Γ B → (i : Var Γ A) → Value (Γ - i) A → Value (Γ - i) B
  hsubNeutral (`spine j s) i v with compare i j
  --                                          v = v    v = v ∧ s < (`spine i s) 
  hsubNeutral (`spine .i s) i v | same = eval`spine v (hsubSpine s i v)
  hsubNeutral (`spine .(wknVar i j) n) .i v | diff i j = `neutral (`spine j (hsubSpine n i v))

  hsubSpine : ∀{Γ A B C} → Spine Γ B C → (i : Var Γ A) → Value (Γ - i) A → Spine (Γ - i) B C
  hsubSpine `yield i v = `yield
  hsubSpine (`proj₁ s) i ab = `proj₁ (hsubSpine s i ab)
  hsubSpine (`proj₂ s) i ab = `proj₂ (hsubSpine s i ab)
  --             f = f   ∧  (s < s `$ a)     f = f ∧ a < (s `$ a)
  hsubSpine (s `$ a) i f = hsubSpine s i f `$ hsubValue a i f

  eval`spine : ∀{Γ A B} → Value Γ A → Spine Γ A B → Value Γ B
  eval`spine v `yield = v
  eval`spine ab (`proj₁ s) = eval`spine (eval`proj₁ ab) s
  eval`spine ab (`proj₂ s) = eval`spine (eval`proj₂ ab) s
  -- (A₁ `→ A₂) < A₂                
  eval`spine f (s `$ a) = eval`spine (eval`$ f a) s

----------------------------------------------------------------------

eval : ∀{Γ A} → Expr Γ A → Value Γ A
eval `tt = `tt
eval (a `, b) = eval a `, eval b
eval (`λ f) = `λ (eval f)
eval (`var i) = `neutral (`spine i `yield)
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
  `λ (`neutral (`spine here
        (`proj₁ (`yield `$ `neutral (`spine here (`proj₂ `yield))))))
`test-intermediate-result = refl

----------------------------------------------------------------------

`intermediate-free-type : Neutral (∅ , ((`⊤ `→ `⊤) `× `⊤)) `⊤
`intermediate-free-type = `spine here (`proj₁ (`yield `$ `neutral (`spine here (`proj₂ `yield))))

`intermediate-free-type₂ : Spine (∅ , ((`⊤ `→ `⊤) `× `⊤)) ((`⊤ `→ `⊤) `× `⊤) `⊤
`intermediate-free-type₂ = `proj₁ (`yield `$ `neutral (`spine here (`proj₂ `yield)))

----------------------------------------------------------------------

`eg-spine₀ : Spine ∅ `⊤ `⊤
`eg-spine₀ = `yield

`eg-spine₁ : Spine ∅ (`⊤ `→ `⊤) (`⊤ `→ `⊤)
`eg-spine₁ = `yield

`eg-spine₂ : Spine ∅ (`⊤ `→ `⊤) `⊤
`eg-spine₂ = `yield `$ `tt

`eg-spine₃ : Spine ∅ ((`⊤ `→ `⊤) `× `⊤) `⊤
`eg-spine₃ = `proj₁ (`yield `$ `tt)

`eg-spine5 : Spine ∅ (`⊤ `→ (`⊤ `× `⊤)) `⊤
`eg-spine5 = (`proj₁ `yield) `$ `tt

-- Normally: ab ⊢ ((proj₁ ab) $ tt)
-- But now:  ab ⊢ (proj₁ (ab′ $ tt))

-- Alternative syntax:
-- `|proj₁ (`|$ a (`|return))
-- Right associative:
-- `|proj₁ `|$ a `|return

`eg-spine₄ : Spine ∅ ((`⊤ `→ `⊤) `× `⊤) `⊤
`eg-spine₄ = `proj₂ `yield

----------------------------------------------------------------------
