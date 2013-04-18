open import Types
module HSub where

----------------------------------------------------------------------

mutual
  data Value : Context → Type → Set where
    `tt : ∀{Γ} → Value Γ `⊤
    `λ : ∀{Γ A B} → Value (Γ , A) B → Value Γ (A `→ B)
    _`,_ : ∀{Γ A B} → Value Γ A → Value Γ B → Value Γ (A `× B)
    `neutral : ∀{Γ} → Neutral Γ `⊤ → Value Γ `⊤

  data Neutral : Context → Type → Set where
    `spine : ∀{Γ A B} → Var Γ A → Spine Γ A B → Neutral Γ B

  data Spine : Context → Type → Type → Set where
    `id : ∀{A Γ} → Spine Γ A A
    _`$_ : ∀{Γ A B C} → Spine Γ B C → Value Γ A → Spine Γ (A `→ B) C
    `proj₁ : ∀{Γ A B C} → Spine Γ A C → Spine Γ (A `× B) C
    `proj₂ : ∀{Γ A B C} → Spine Γ B C → Spine Γ (A `× B) C

----------------------------------------------------------------------

wknValue : ∀{A Γ B} (i : Var Γ A) → Value (Γ - i) B → Value Γ B
wknSpine :  ∀{A Γ B C} (i : Var Γ A) → Spine (Γ - i) B C → Spine Γ B C

wknValue i `tt = `tt
wknValue i (`λ f) = `λ (wknValue (there i) f)
wknValue i (a `, b) = wknValue i a `, wknValue i b
wknValue i (`neutral (`spine j n)) = `neutral (`spine (wknVar i j) (wknSpine i n))

wknSpine i `id = `id
wknSpine i (n `$ a) = wknSpine i n `$ wknValue i a
wknSpine i (`proj₁ n) = `proj₁ (wknSpine i n)
wknSpine i (`proj₂ n) = `proj₂ (wknSpine i n)

----------------------------------------------------------------------

subValue : ∀{A Γ B} → Value Γ B → (i : Var Γ A) → Value (Γ - i) A → Value (Γ - i) B
subNeutral : ∀{A Γ} → Neutral Γ `⊤ → (i : Var Γ A) → Value (Γ - i) A → Value (Γ - i) `⊤
subSpine : ∀{Γ A B C} → Spine Γ B C → (i : Var Γ A) → Value (Γ - i) A → Spine (Γ - i) B C
evalSpine : ∀{B Γ A} → Spine Γ A B → Value Γ A → Value Γ B

subValue `tt i v = `tt
subValue (`λ f) i v = `λ (subValue f (there i) (wknValue here v))
subValue (a `, b) i v = subValue a i v `, subValue b i v
subValue (`neutral n) i v = subNeutral n i v

subNeutral (`spine j s) i v with compare i j
subNeutral (`spine .i s) i v | same = evalSpine (subSpine s i v) v
subNeutral (`spine .(wknVar i j) n) .i v | diff i j = `neutral (`spine j (subSpine n i v))

subSpine `id i v = `id
subSpine (s `$ a) i f = subSpine s i f `$ subValue a i f
subSpine (`proj₁ s) i ab = `proj₁ (subSpine s i ab)
subSpine (`proj₂ s) i ab = `proj₂ (subSpine s i ab)

evalSpine `id v = v
evalSpine (s `$ a) (`λ f) = evalSpine s (subValue f here a)
evalSpine (`proj₁ s) (a `, b) = evalSpine s a
evalSpine (`proj₂ s) (a `, b) = evalSpine s b

----------------------------------------------------------------------
