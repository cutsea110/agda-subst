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

push-out : {A : Set}(x : A)(xs ys : List A) → P (xs ^ ⟨ x ⟩ ^ ys) (x ∷ xs ^ ys)
push-out x ⟨⟩ ⟨⟩ = sbt x ⟨⟩ (x ∷ ⟨⟩) (⟨⟩ , ⟨⟩ , nil ⟨⟩ refl , refl)
push-out x ⟨⟩ (y ∷ ys) = refl-law
push-out x (x₁ ∷ xs) ys = sbt x₁ (xs ^ ⟨ x ⟩ ^ ys) (⟨ x ⟩ ^ ⟨ x₁ ⟩ ^ (xs ^ ys)) (⟨ x ⟩ , xs ^ ys , push-out x xs ys , refl)

swap : {A : Set}(x y : A)(xs : List A) → P (x ∷ y ∷ xs) (y ∷ x ∷ xs)
swap x y xs = push-in x (⟨ y ⟩) xs

add : {A : Set}{xs ys : List A}(x : A) → P xs ys → P (x ∷ xs) (x ∷ ys)
add x (nil .⟨⟩ refl) = sbt x ⟨⟩ (x ∷ ⟨⟩) (⟨⟩ , ⟨⟩ , nil ⟨⟩ refl , refl)
add x (sbt x₁ s t x₂) = sbt x (x₁ ∷ s) (x ∷ t) (⟨⟩ , t , sbt x₁ s t x₂ , refl)

del : {A : Set}(x : A)(xs ys : List A) → P (x ∷ xs) (x ∷ ys) → P xs ys
del x xs ys (sbt .x .xs .(x ∷ ys) (⟨⟩ , .ys , p₃ , refl)) = p₃
del x xs .(p₁ ^ x ∷ p₂) (sbt .x .xs .(x ∷ p₁ ^ x ∷ p₂) (.x ∷ p₁ , p₂ , p₃ , refl)) = trans-law p₃ (push-in x p₁ p₂)

exch : {A : Set}(v w : A)(xs ys : List A) → P (v ∷ xs ^ ⟨ w ⟩ ^ ys) (w ∷ xs ^ ⟨ v ⟩ ^ ys)
exch v w ⟨⟩ ⟨⟩ = sbt v (w ∷ ⟨⟩) (w ∷ v ∷ ⟨⟩) (w ∷ ⟨⟩ , ⟨⟩ , sbt w ⟨⟩ (w ∷ ⟨⟩) (⟨⟩ , ⟨⟩ , nil ⟨⟩ refl , refl) , refl)
exch v w ⟨⟩ (x ∷ ys) = swap v w (x ∷ ys)
exch v w (x ∷ xs) ys with add x (exch v w xs ys)
... | prf with swap v x (xs ^ w ∷ ys) | swap x w (xs ^ v ∷ ys)
... | sw₁ | sw₂ = trans-law (trans-law sw₁ prf) sw₂

refl-law {xs = ⟨⟩} = nil ⟨⟩ refl
refl-law {xs = x ∷ xs} = sbt x xs (x ∷ xs) (⟨⟩ , xs , refl-law , refl)

sym-law {xs = ⟨⟩} (nil .⟨⟩ refl) = nil ⟨⟩ refl
sym-law {xs = x ∷ xs} (nil .(x ∷ xs) ())
sym-law {xs = x ∷ xs} (sbt .x .xs .(p₁ ^ x ∷ p₂) (p₁ , p₂ , p₃ , refl)) with push-in x p₁ p₂
sym-law {_} {x ∷ xs} (sbt .x .xs .(⟨⟩ ^ ⟨ x ⟩ ^ p₂) (⟨⟩ , p₂ , p₃ , refl))
  | sbt .x .p₂ .(x ∷ p₂) x₁ = add x (sym-law p₃)
sym-law {_} {x ∷ xs} (sbt .x .xs .((x₁ ∷ p₁) ^ ⟨ x ⟩ ^ p₂) (x₁ ∷ p₁ , p₂ , p₃ , refl))
  | sbt .x .(x₁ ∷ p₁ ^ p₂) .(x₁ ∷ p₁ ^ x ∷ p₂) (q₁ , q₂ , q₃ , q₄) = {!!}

trans-law {xs = .⟨⟩} {.⟨⟩} {zs} (nil .⟨⟩ refl) q = q
trans-law {xs = .(x ∷ s)} {.⟨⟩} {.⟨⟩} (sbt x s .⟨⟩ (⟨⟩ , p₂ , p₃ , ())) (nil .⟨⟩ refl)
trans-law {xs = .(x ∷ s)} {.⟨⟩} {.⟨⟩} (sbt x s .⟨⟩ (x₁ ∷ p₁ , p₂ , p₃ , ())) (nil .⟨⟩ refl)
trans-law {xs = .(x₁ ∷ ⟨⟩)} {.(x₁ ∷ ⟨⟩)} {.t} (sbt .x₁ .⟨⟩ .(x₁ ∷ ⟨⟩) (⟨⟩ , .⟨⟩ , nil .⟨⟩ refl , refl)) (sbt x₁ .⟨⟩ t (q₁ , q₂ , q₃ , q₄))
  = sbt x₁ ⟨⟩ t (q₁ , q₂ , q₃ , q₄)
trans-law {xs = .(x₁ ∷ x ∷ s)} {.(x₁ ∷ s₁)} {.t} (sbt .x₁ .(x ∷ s) .(x₁ ∷ s₁) (⟨⟩ , .s₁ , sbt x s .s₁ x₂ , refl)) (sbt x₁ s₁ t (q₁ , q₂ , q₃ , q₄))
  = sbt x₁ (x ∷ s) t (q₁ , q₂ , trans-law (sbt x s s₁ x₂) q₃ , q₄)
trans-law {xs = .(x ∷ s)} {.(x₁ ∷ p₁ ^ x ∷ p₂)} {.(q₁ ^ x₁ ∷ q₂)} (sbt x s .(x₁ ∷ p₁ ^ x ∷ p₂) (.x₁ ∷ p₁ , p₂ , p₃ , refl)) (sbt x₁ .(p₁ ^ x ∷ p₂) .(q₁ ^ x₁ ∷ q₂) (q₁ , q₂ , q₃ , refl)) = {!!}


