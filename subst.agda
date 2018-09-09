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

xs^⟨⟩≡xs : {A : Set} → (xs : List A) → xs ^ ⟨⟩ ≡ xs
xs^⟨⟩≡xs ⟨⟩ = refl
xs^⟨⟩≡xs (x ∷ xs) = cong (x ∷_) (xs^⟨⟩≡xs xs)
xs≡xs^⟨⟩ : {A : Set} → (xs : List A) → xs ≡ xs ^ ⟨⟩
xs≡xs^⟨⟩ ⟨⟩ = refl
xs≡xs^⟨⟩ (x ∷ xs) = cong (x ∷_) (xs≡xs^⟨⟩ xs)

refl-law : {A : Set} {xs : List A} → P xs xs
sym-law : {A : Set} {xs ys : List A} → P xs ys → P ys xs
trans-law : {A : Set} {xs ys zs : List A} → P xs ys → P ys zs → P xs zs

push-in : {A : Set}(x : A)(xs ys : List A) → P (x ∷ xs ^ ys) (xs ^ ⟨ x ⟩ ^ ys)
push-in x xs ys = {!!}

push-out : {A : Set}(x : A)(xs ys : List A) → P (xs ^ ⟨ x ⟩ ^ ys) (x ∷ xs ^ ys)
push-out x xs ys = sym-law (push-in x xs ys)

refl-law {xs = ⟨⟩} = nil ⟨⟩ refl
refl-law {xs = x ∷ xs} = sbt x xs (x ∷ xs) (⟨⟩ , xs , refl-law , refl)

cong-P : {A : Set}{x y : A}{xs ys : List A} → x ≡ y → P xs ys → P (x ∷ xs) (y ∷ ys)
cong-P {x = x} refl (nil .⟨⟩ refl) = sbt x ⟨⟩ (x ∷ ⟨⟩) (⟨⟩ , ⟨⟩ , nil ⟨⟩ refl , refl)
cong-P {x = x} refl (sbt x₁ s t x₂) = sbt x (x₁ ∷ s) (x ∷ t) (⟨⟩ , t , sbt x₁ s t x₂ , refl)

assoc-list : {A : Set}(xs ys zs : List A) → xs ^ (ys ^ zs) ≡ (xs ^ ys) ^ zs
assoc-list ⟨⟩ ys zs = refl
assoc-list (x ∷ xs) ys zs = cong (x ∷_) (assoc-list xs ys zs)

sym-law {xs = ⟨⟩} {.⟨⟩} (nil .⟨⟩ prf) = nil ⟨⟩ refl
sym-law {xs = x ∷ xs} {.⟨⟩} (nil .(x ∷ xs) ())
sym-law {xs = x ∷ xs} {.t} (sbt .x .xs t (proj₁ , proj₂ , proj₃ , proj₄)) = ?

trans-law (nil .⟨⟩ refl) q = q
trans-law (sbt x s .⟨⟩ (⟨⟩ , proj₂ , proj₃ , ())) (nil .⟨⟩ refl)
trans-law (sbt x s .⟨⟩ ((x₁ ∷ proj₁) , proj₂ , proj₃ , ())) (nil .⟨⟩ refl)
trans-law (sbt x s .(y ∷ t) (p₁ , p₂ , p₃ , p₄)) (sbt y t .(q₁ ^ ⟨ y ⟩ ^ q₂) (q₁ , q₂ , q₃ , refl)) = {!!}
