open import Types
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

append`proj₁ : ∀{Γ A B C} → Spine Γ C (A `× B) → Spine Γ C A
append`proj₁ `id = `proj₁ `id
append`proj₁ (`proj₁ s) = `proj₁ (append`proj₁ s)
append`proj₁ (`proj₂ s) = `proj₂ (append`proj₁ s)
append`proj₁ (s `$ a) = append`proj₁ s `$ a

append`proj₂ : ∀{Γ A B C} → Spine Γ C (A `× B) → Spine Γ C B
append`proj₂ `id = `proj₂ `id
append`proj₂ (`proj₁ s) = `proj₁ (append`proj₂ s)
append`proj₂ (`proj₂ s) = `proj₂ (append`proj₂ s)
append`proj₂ (s `$ a) = append`proj₂ s `$ a

append`$ : ∀{Γ A B C} → Spine Γ C (A `→ B) → Value Γ A → Spine Γ C B
append`$ `id v = `id `$ v
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
  eval`$ (`λ f) a = hsubValue f here a
  eval`$ (`neutral (`spine i s)) a = `neutral (`spine i (append`$ s a))

  hsubValue : ∀{Γ A B} → Value Γ B → (i : Var Γ A) → Value (Γ - i) A → Value (Γ - i) B
  hsubValue `tt i v = `tt
  hsubValue (a `, b) i v = hsubValue a i v `, hsubValue b i v
  hsubValue (`λ f) i v = `λ (hsubValue f (there i) (wknValue here v))
  hsubValue (`neutral n) i v = hsubNeutral n i v

  hsubNeutral : ∀{Γ A B} → Neutral Γ B → (i : Var Γ A) → Value (Γ - i) A → Value (Γ - i) B
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
  eval`spine ab (`proj₁ s) = eval`spine (eval`proj₁ ab) s
  eval`spine ab (`proj₂ s) = eval`spine (eval`proj₂ ab) s
  eval`spine f (s `$ a) = eval`spine (eval`$ f a) s

----------------------------------------------------------------------
