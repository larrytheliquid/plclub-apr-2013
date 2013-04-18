open import Data.Bool
open import Data.Product
open import Function 
module Agda where

`id : Bool → Bool
`id = λ x → x

`const : Bool → Bool → Bool
`const = λ x → λ y → x

`app : ((Bool → Bool) × Bool) → Bool
`app = λ ab → proj₁ ab $ proj₂ ab

`result : Bool
`result = `app $ (not , true)

