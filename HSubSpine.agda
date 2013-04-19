open import Types
module HSubSpine where

----------------------------------------------------------------------

mutual
  data Value : Context → Type → Set where
    `tt : ∀{Γ} → Value Γ `⊤
    _`,_ : ∀{Γ A B} → Value Γ A → Value Γ B → Value Γ (A `× B)
    `λ : ∀{Γ A B} → Value (Γ , A) B → Value Γ (A `→ B)
    `neutral : ∀{Γ} → Neutral Γ `⊤ → Value Γ `⊤

  data Neutral : Context → Type → Set where
    `spine : ∀{Γ A B} → Var Γ A → Spine Γ A B → Neutral Γ B

  data Spine : Context → Type → Type → Set where
    `id : ∀{A Γ} → Spine Γ A A
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
  wknSpine i `id = `id
  wknSpine i (`proj₁ n) = `proj₁ (wknSpine i n)
  wknSpine i (`proj₂ n) = `proj₂ (wknSpine i n)
  wknSpine i (n `$ a) = wknSpine i n `$ wknValue i a

----------------------------------------------------------------------

mutual
  hsubValue : ∀{Γ A B} → Value Γ B → (i : Var Γ A) → Value (Γ - i) A → Value (Γ - i) B
  hsubValue `tt i v = `tt
  hsubValue (a `, b) i v = hsubValue a i v `, hsubValue b i v
  hsubValue (`λ f) i v = `λ (hsubValue f (there i) (wknValue here v))
  hsubValue (`neutral n) i v = hsubNeutral n i v

  hsubNeutral : ∀{Γ A} → Neutral Γ `⊤ → (i : Var Γ A) → Value (Γ - i) A → Value (Γ - i) `⊤
  hsubNeutral (`spine j s) i v with compare i j
  hsubNeutral (`spine .i s) i v | same = eval`spine v (hsubSpine s i v)
  hsubNeutral (`spine .(wknVar i j) n) .i v | diff i j = `neutral (`spine j (hsubSpine n i v))

  hsubSpine : ∀{Γ A B C} → Spine Γ B C → (i : Var Γ A) → Value (Γ - i) A → Spine (Γ - i) B C
  hsubSpine `id i v = `id
  hsubSpine (`proj₁ s) i ab = `proj₁ (hsubSpine s i ab)
  hsubSpine (`proj₂ s) i ab = `proj₂ (hsubSpine s i ab)
  hsubSpine (s `$ a) i f = hsubSpine s i f `$ hsubValue a i f

  eval`spine : ∀{Γ A B} → Value Γ A → Spine Γ A B → Value Γ B
  eval`spine v `id = v
  eval`spine (a `, b) (`proj₁ s) = eval`spine a s
  eval`spine (a `, b) (`proj₂ s) = eval`spine b s
  eval`spine (`λ f) (s `$ a) = eval`spine (hsubValue f here a) s

----------------------------------------------------------------------
