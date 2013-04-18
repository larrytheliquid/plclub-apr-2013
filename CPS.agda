open import Data.Bool
open import Data.Product
open import Function
module CPS where

`id : {C : Set} → Bool → (Bool → C) → C
`id = λ x → λ f → f x

`eg : {C : Set} → Bool → C
`eg = `id true {!!}


