open import Data.List renaming ([] to ⟨⟩; [_] to ⟨_⟩; _++_ to _^_)
open import Relation.Binary.PropositionalEquality as PropEq
open import Data.Product using (∃; _,_) renaming (_×_ to _∧_)

data P {A : Set} : List A → List A → Set where
  nil : (s : List A) → (prf : s ≡ ⟨⟩) → P s ⟨⟩
  sbt : (x : A) (s t : List A)
        → (∃ λ u → ∃ λ v → P s (u ^ v) ∧ t ≡ u ^ ⟨ x ⟩ ^ v)
        → P (⟨ x ⟩ ^ s) t  

refl-law : {A : Set} {xs : List A} → P xs xs
sym-law : {A : Set} {xs ys : List A} → P xs ys → P ys xs
trans-law : {A : Set} {xs ys zs : List A} → P xs ys → P ys zs → P xs zs

push-in : {A : Set}(x : A)(xs ys : List A) → P (x ∷ xs ^ ys) (xs ^ ⟨ x ⟩ ^ ys)
push-in x xs ys = sbt x (xs ^ ys) (xs ^ ⟨ x ⟩ ^ ys) (xs , ys , refl-law , refl)

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
sym-law {xs = x ∷ xs} {.(p₁ ^ ⟨ x ⟩ ^ p₂)} (sbt .x .xs .(p₁ ^ ⟨ x ⟩ ^ p₂) (p₁ , p₂ , p₃ , refl)) = {!!}

trans-law (nil .⟨⟩ refl) q = q
trans-law (sbt x s .⟨⟩ (⟨⟩ , proj₂ , proj₃ , ())) (nil .⟨⟩ refl)
trans-law (sbt x s .⟨⟩ ((x₁ ∷ proj₁) , proj₂ , proj₃ , ())) (nil .⟨⟩ refl)
trans-law (sbt x s .(y ∷ t) (p₁ , p₂ , p₃ , p₄)) (sbt y t .(q₁ ^ ⟨ y ⟩ ^ q₂) (q₁ , q₂ , q₃ , refl)) = {!!}
