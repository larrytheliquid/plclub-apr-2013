module Types where

----------------------------------------------------------------------

infixr 3 _`→_
infixr 4 _`×_

data Type : Set where
  `⊤ `Bool : Type
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
