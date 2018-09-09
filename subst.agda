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

congP : {A : Set}{x : A}{xs ys : List A} → P xs ys → P (x ∷ xs) (x ∷ ys)
congP {x = x} (nil .⟨⟩ refl) = sbt x ⟨⟩ (x ∷ ⟨⟩) (⟨⟩ , ⟨⟩ , nil ⟨⟩ refl , refl)
congP {x = x} (sbt x₁ s t x₂) = sbt x (x₁ ∷ s) (x ∷ t) (⟨⟩ , t , sbt x₁ s t x₂ , refl)

push-in : {A : Set}(x : A)(xs ys : List A) → P (x ∷ xs ^ ys) (xs ^ ⟨ x ⟩ ^ ys)
push-in x xs ys = sbt x (xs ^ ys) (xs ^ ⟨ x ⟩ ^ ys) (xs , ys , refl-law , refl)

swap : {A : Set}(x y : A)(xs : List A) → P (x ∷ y ∷ xs) (y ∷ x ∷ xs)
swap x y xs = push-in x (⟨ y ⟩) xs

swap-far : {A : Set}(v w : A)(xs ys : List A) → P (v ∷ xs ^ ⟨ w ⟩ ^ ys) (w ∷ xs ^ ⟨ v ⟩ ^ ys)
swap-far v w ⟨⟩ ⟨⟩ = sbt v (w ∷ ⟨⟩) (w ∷ v ∷ ⟨⟩) (w ∷ ⟨⟩ , ⟨⟩ , sbt w ⟨⟩ (w ∷ ⟨⟩) (⟨⟩ , ⟨⟩ , nil ⟨⟩ refl , refl) , refl)
swap-far v w ⟨⟩ (x ∷ ys) = swap v w (x ∷ ys)
swap-far v w (x ∷ xs) ys with congP {x = x} (swap-far v w xs ys)
... | prf with swap v x (xs ^ w ∷ ys) | swap x w (xs ^ v ∷ ys)
... | sw₁ | sw₂ = trans-law (trans-law sw₁ prf) sw₂

down : {A : Set}(x : A)(xs ys : List A) → P (x ∷ xs) (x ∷ ys) → P xs ys
down x xs ys (sbt .x .xs .(x ∷ ys) (⟨⟩ , .ys , p₃ , refl)) = p₃
down x xs .(p₁ ^ x ∷ p₂) (sbt .x .xs .(x ∷ p₁ ^ x ∷ p₂) (.x ∷ p₁ , p₂ , p₃ , refl)) = trans-law p₃ (push-in x p₁ p₂)

refl-law {xs = ⟨⟩} = nil ⟨⟩ refl
refl-law {xs = x ∷ xs} = sbt x xs (x ∷ xs) (⟨⟩ , xs , refl-law , refl)
-- assoc-list : {A : Set}(xs ys zs : List A) → xs ^ (ys ^ zs) ≡ (xs ^ ys) ^ zs
-- assoc-list ⟨⟩ ys zs = refl
-- assoc-list (x ∷ xs) ys zs = cong (x ∷_) (assoc-list xs ys zs)

sym-law {xs = ⟨⟩} (nil .⟨⟩ refl) = nil ⟨⟩ refl
sym-law {xs = x ∷ xs} (nil .(x ∷ xs) ())
sym-law {xs = x ∷ xs} (sbt .x .xs .(p₁ ^ x ∷ p₂) (p₁ , p₂ , p₃ , refl)) with push-in x p₁ p₂
sym-law {_} {x ∷ xs} (sbt .x .xs .(⟨⟩ ^ ⟨ x ⟩ ^ p₂) (⟨⟩ , p₂ , p₃ , refl))
  | sbt .x .p₂ .(x ∷ p₂) x₁ = congP (sym-law p₃)
sym-law {_} {x ∷ xs} (sbt .x .xs .((x₁ ∷ p₁) ^ ⟨ x ⟩ ^ p₂) (x₁ ∷ p₁ , p₂ , p₃ , refl))
  | sbt .x .(x₁ ∷ p₁ ^ p₂) .(x₁ ∷ p₁ ^ x ∷ p₂) (q₁ , q₂ , q₃ , q₄) = {!!}



trans-law (nil .⟨⟩ refl) q = q
trans-law (sbt x s .⟨⟩ (⟨⟩ , proj₂ , proj₃ , ())) (nil .⟨⟩ refl)
trans-law (sbt x s .⟨⟩ ((x₁ ∷ proj₁) , proj₂ , proj₃ , ())) (nil .⟨⟩ refl)
trans-law (sbt x s .(y ∷ t) (p₁ , p₂ , p₃ , p₄)) (sbt y t .(q₁ ^ ⟨ y ⟩ ^ q₂) (q₁ , q₂ , q₃ , refl)) = {!!}
