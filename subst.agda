data List (A : Set) : Set where
  ⟨⟩ : List A
  _∷_ : A → List A → List A

⟨_⟩ : {A : Set} → (x : A) → List A
⟨ x ⟩ = x ∷ ⟨⟩

_^_ : {A : Set} → List A → List A → List A
⟨⟩ ^ ys = ys
(x ∷ xs) ^ ys = x ∷ (xs ^ ys)

infixl 6 _^_

open import Relation.Binary.PropositionalEquality as PropEq
open import Data.Product using (∃) renaming (_×_ to _∧_)

data P {A : Set} : List A → List A → Set where
  nil : (s : List A) → (prf : s ≡ ⟨⟩) → P s ⟨⟩
  sbt : (x : A) (s t : List A)
        → (∃ λ u → ∃ λ v → P s (u ^ v) ∧ t ≡ u ^ ⟨ x ⟩ ^ v)
        → P (⟨ x ⟩ ^ s) t  

refl-law : {A : Set} {x : List A} → P x x
refl-law = {!!}

sym-law : {A : Set} {x y : List A} → P x y → P y x
sym-law = {!!}

trans-law : {A : Set} {x y z : List A} → P x y → P y z → P x z
trans-law = {!!}
