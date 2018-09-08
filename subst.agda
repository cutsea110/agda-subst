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
open import Data.Product using (∃; _,_) renaming (_×_ to _∧_)
open import Data.Empty

data P {A : Set} : List A → List A → Set where
  nil : (s : List A) → (prf : s ≡ ⟨⟩) → P s ⟨⟩
  sbt : (x : A) (s t : List A)
        → (∃ λ u → ∃ λ v → P s (u ^ v) ∧ t ≡ u ^ ⟨ x ⟩ ^ v)
        → P (⟨ x ⟩ ^ s) t  

⟨⟩≢xs≡⟨x⟩ : {A : Set} → (x : A) (xs : List A) → ⟨⟩ ≢ xs ^ ⟨ x ⟩
⟨⟩≢xs≡⟨x⟩ x ⟨⟩ ()
⟨⟩≢xs≡⟨x⟩ x (x₁ ∷ xs) ()
⟨⟩≢xs^⟨z⟩^ys : {A : Set} → (xs : List A) (z : A) (ys : List A) → ⟨⟩ ≢ xs ^ ⟨ z ⟩ ^ ys
⟨⟩≢xs^⟨z⟩^ys ⟨⟩ z ys ()
⟨⟩≢xs^⟨z⟩^ys (x ∷ xs) z ys ()

refl-law : {A : Set} {xs : List A} → P xs xs
refl-law {xs = ⟨⟩} = nil ⟨⟩ refl
refl-law {xs = x ∷ xs} = sbt x xs (x ∷ xs) (⟨⟩ , xs , refl-law , refl)

sym-law : {A : Set} {xs ys : List A} → P xs ys → P ys xs
sym-law {xs = ⟨⟩} {.⟨⟩} (nil .⟨⟩ refl) = nil ⟨⟩ refl
sym-law {xs = x ∷ xs} {⟨⟩} (nil .(x ∷ xs) ())
sym-law {xs = x ∷ xs} {⟨⟩} (sbt .x .xs .⟨⟩ (proj₁ , proj₂ , proj₃ , proj₄)) = ⊥-elim (⟨⟩≢xs^⟨z⟩^ys proj₁ x proj₂ proj₄)
sym-law {xs = x ∷ xs} {y ∷ ys} prf = {!!}

trans-law : {A : Set} {xs ys zs : List A} → P xs ys → P ys zs → P xs zs
trans-law p q = {!!}
