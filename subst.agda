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
refl-law {xs = ⟨⟩} = nil ⟨⟩ refl
refl-law {xs = x ∷ xs} = sbt x xs (x ∷ xs) (⟨⟩ , xs , refl-law , refl)

cong-P : {A : Set}{x y : A}{xs ys : List A} → x ≡ y → P xs ys → P (x ∷ xs) (y ∷ ys)
cong-P {x = x} refl (nil .⟨⟩ refl) = sbt x ⟨⟩ (x ∷ ⟨⟩) (⟨⟩ , ⟨⟩ , nil ⟨⟩ refl , refl)
cong-P {x = x} refl (sbt x₁ s t x₂) = sbt x (x₁ ∷ s) (x ∷ t) (⟨⟩ , t , sbt x₁ s t x₂ , refl)

lemma₂ : {A : Set}(w : A)(xs ys us vs : List A) → P (xs ^ ys) (us ^ vs) → P (xs ^ ⟨ w ⟩ ^ ys) (us ^ ⟨ w ⟩ ^ vs)
lemma₂ = {!!}

lemma₁ : {A : Set}(w : A)(xs ys zs : List A) → P (w ∷ (xs ^ ys)) zs → P (xs ^ ⟨ w ⟩ ^ ys) zs
lemma₁ w ⟨⟩ ys zs prf = prf
lemma₁ w (x ∷ xs) ys .⟨⟩ (nil .(w ∷ (x ∷ (xs ^ ys))) ())
lemma₁ w (x ∷ xs) ys zs (sbt .w .(x ∷ (xs ^ ys)) .zs (proj₁ , proj₂ , proj₃ , proj₄))
  rewrite proj₄ with cong-P {x = w} {y = w} refl proj₃
... | prf = lemma₂ w (x ∷ xs) ys proj₁ proj₂ proj₃

lemma₀ : {A : Set}(v w : A)(xs ys zs : List A) → P (v ∷ (xs ^ ⟨ w ⟩ ^ ys)) zs → P (w ∷ (xs ^ ⟨ v ⟩ ^ ys)) zs
lemma₀ v w xs ys .⟨⟩ (nil .(v ∷ (xs ^ (w ∷ ⟨⟩) ^ ys)) ())
lemma₀ v w xs ys zs (sbt .v .(xs ^ (w ∷ ⟨⟩) ^ ys) .zs (proj₁ , proj₂ , proj₃ , proj₄)) with cong-P {x = v} {y = v} refl proj₃
... | p = {!!}


sym-law : {A : Set} {xs ys : List A} → P xs ys → P ys xs

lemma : {A : Set}(w : A)(xs ys zs : List A) → P xs (ys ^ zs) → P (ys ^ ⟨ w ⟩ ^ zs) (w ∷ xs)
lemma w ⟨⟩ ⟨⟩ .⟨⟩ (nil .⟨⟩ refl) = sbt w ⟨⟩ (w ∷ ⟨⟩) (⟨⟩ , ⟨⟩ , nil ⟨⟩ refl , refl)
lemma w ⟨⟩ (x ∷ ys) zs ()
lemma w (x ∷ xs) ⟨⟩ .⟨⟩ (nil .(x ∷ xs) ())
lemma w (x ∷ xs) ⟨⟩ zs (sbt .x .xs .zs (proj₁ , proj₂ , proj₃ , proj₄)) rewrite proj₄
  = cong-P refl (lemma x xs proj₁ proj₂ proj₃)
lemma w (x ∷ xs) (y ∷ ys) zs prf = lemma₀ w y ys zs (w ∷ (x ∷ xs)) (cong-P refl (lemma₁ y ys zs (x ∷ xs) (sym-law prf)))

sym-law {xs = ⟨⟩} {.⟨⟩} (nil .⟨⟩ refl) = nil ⟨⟩ refl
sym-law {xs = x ∷ xs} {.⟨⟩} (nil .(x ∷ xs) ())
sym-law {xs = x ∷ xs} {.(proj₁ ^ (x ∷ ⟨⟩) ^ proj₂)} (sbt .x .xs .(proj₁ ^ (x ∷ ⟨⟩) ^ proj₂) (proj₁ , proj₂ , proj₃ , refl))
  = lemma x xs proj₁ proj₂ proj₃

trans-law : {A : Set} {xs ys zs : List A} → P xs ys → P ys zs → P xs zs
trans-law p q = {!!}
