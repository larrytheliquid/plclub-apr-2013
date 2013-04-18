 module HSub where

----------------------------------------------------------------------

data Type : Set where
  `⊤ : Type
  _`→_ _`×_ : Type → Type → Type

----------------------------------------------------------------------

data Context : Set where
  ∅ : Context
  _,_ : Context → Type → Context

data Var : Context → Type → Set where
  here : ∀{Γ A} → Var (Γ , A) A
  there : ∀{Γ A B} → Var Γ A → Var (Γ , B) A

_-_ : {A : Type} (Γ : Context) → Var Γ A → Context
∅ - ()
(Γ , A) - here = Γ
(Γ , B) - (there x) = (Γ - x) , B

wknVar : ∀{Γ A B} (i : Var Γ A) → Var (Γ - i) B → Var Γ B
wknVar here j = there j
wknVar (there i) here = here
wknVar (there i) (there j) = there (wknVar i j)

----------------------------------------------------------------------

data Compare {Γ : Context} : {A B : Type} → Var Γ A → Var Γ B → Set where
  same : ∀{A} {i : Var Γ A} → Compare i i
  diff : ∀{A B} (i : Var Γ A) → (j : Var (Γ - i) B) → Compare i (wknVar i j)

compare : ∀{Γ A B} (i : Var Γ A) (j : Var Γ B) → Compare i j
compare here here = same
compare here (there j) = diff here j
compare (there i) here = diff (there i) here
compare (there i) (there j) with compare i j
compare (there i) (there .i) | same = same
compare (there .i) (there .(wknVar i j)) | (diff i j) = diff (there i) (there j)

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
subSpine (n `$ a) i f = subSpine n i f `$ subValue a i f
subSpine (`proj₁ n) i ab = `proj₁ (subSpine n i ab)
subSpine (`proj₂ n) i ab = `proj₂ (subSpine n i ab)

evalSpine `id v = v
evalSpine (s `$ a) (`λ f) = evalSpine s (subValue f here a)
evalSpine (`proj₁ s) (a `, b) = evalSpine s a
evalSpine (`proj₂ s) (a `, b) = evalSpine s b

----------------------------------------------------------------------
