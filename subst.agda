open import Data.List renaming ([] to ⟨⟩; [_] to ⟨_⟩; _++_ to _^_)
open import Relation.Binary.PropositionalEquality as PropEq
open import Data.Product using (∃; _,_) renaming (_×_ to _∧_)

data P {A : Set} : List A → List A → Set where
  nil : (s : List A) → (prf : s ≡ ⟨⟩) → P s ⟨⟩
  sbt : (x : A) (s t : List A)
        → (∃ λ u → ∃ λ v → P s (u ^ v) ∧ t ≡ u ^ ⟨ x ⟩ ^ v)
        → P (⟨ x ⟩ ^ s) t

-- | list properties
assoc-list : {A : Set}(x y z : List A) → (x ^ y) ^ z ≡ x ^ (y ^ z)
assoc-list ⟨⟩ ys zs = refl
assoc-list (x ∷ xs) ys zs = cong (x ∷_) (assoc-list xs ys zs)

-- | independent
refl-law : {A : Set} {xs : List A} → P xs xs
refl-law {xs = ⟨⟩} = nil ⟨⟩ refl
refl-law {xs = x ∷ xs} = sbt x xs (x ∷ xs) (⟨⟩ , xs , refl-law , refl)

sym-law : {A : Set} {xs ys : List A} → P xs ys → P ys xs
trans-law : {A : Set} {xs ys zs : List A} → P xs ys → P ys zs → P xs zs

-- | depends on just only refl-law
push-in : {A : Set}(x : A)(xs ys : List A) → P (⟨ x ⟩ ^ xs ^ ys) (xs ^ ⟨ x ⟩ ^ ys)
push-in x xs ys = sbt x (xs ^ ys) (xs ^ ⟨ x ⟩ ^ ys) (xs , ys , refl-law , refl)

-- | depends on just only refl-law
push-out : {A : Set}(x : A)(xs ys : List A) → P (xs ^ ⟨ x ⟩ ^ ys) (⟨ x ⟩ ^ xs ^ ys)
push-out x ⟨⟩ ⟨⟩ = sbt x ⟨⟩ (x ∷ ⟨⟩) (⟨⟩ , ⟨⟩ , nil ⟨⟩ refl , refl)
push-out x ⟨⟩ (y ∷ ys) = refl-law
push-out x (x₁ ∷ xs) ys = sbt x₁ (xs ^ ⟨ x ⟩ ^ ys) (⟨ x ⟩ ^ ⟨ x₁ ⟩ ^ (xs ^ ys)) (⟨ x ⟩ , xs ^ ys , push-out x xs ys , refl)

-- | depends on just only refl-law
swap : {A : Set}(x y : A)(xs : List A) → P (⟨ x ⟩ ^ ⟨ y ⟩ ^ xs) (⟨ y ⟩ ^ ⟨ x ⟩ ^ xs)
swap x y xs = push-in x (⟨ y ⟩) xs

-- | independent
ins : {A : Set}{xs ys : List A}(x : A) → P xs ys → P (⟨ x ⟩ ^ xs) (⟨ x ⟩ ^ ys)
ins x (nil .⟨⟩ refl) = sbt x ⟨⟩ (x ∷ ⟨⟩) (⟨⟩ , ⟨⟩ , nil ⟨⟩ refl , refl)
ins x (sbt x₁ s t x₂) = sbt x (x₁ ∷ s) (x ∷ t) (⟨⟩ , t , sbt x₁ s t x₂ , refl)

add : {A : Set}{xs ys : List A}(x : A) → P xs ys → P (xs ^ ⟨ x ⟩) (ys ^ ⟨ x ⟩)
add x (nil .⟨⟩ refl) = sbt x ⟨⟩ (x ∷ ⟨⟩) (⟨⟩ , ⟨⟩ , nil ⟨⟩ refl , refl)
add x (sbt x₁ s .(p₁ ^ x₁ ∷ p₂) (p₁ , p₂ , p₃ , refl))
  = sbt x₁ (s ^ ⟨ x ⟩) ((p₁ ^ ⟨ x₁ ⟩ ^ p₂) ^ ⟨ x ⟩) (p₁ , p₂ ^ ⟨ x ⟩ , help p₁ p₂ s (add x p₃) , assoc-list p₁ (⟨ x₁ ⟩ ^ p₂) ⟨ x ⟩)
  where
    help : {A : Set} (p₁ p₂ s : List A) {x : A} → P (s ^ ⟨ x ⟩) ((p₁ ^ p₂) ^ ⟨ x ⟩) → P (s ^ ⟨ x ⟩) (p₁ ^ p₂ ^ ⟨ x ⟩)
    help p₁ p₂ s {x} p rewrite assoc-list p₁ p₂ ⟨ x ⟩ = p

del : {A : Set}(x : A)(xs ys : List A) → P (x ∷ xs) (x ∷ ys) → P xs ys
del x xs ys (sbt .x .xs .(x ∷ ys) (⟨⟩ , .ys , p₃ , refl)) = p₃
del x xs .(p₁ ^ x ∷ p₂) (sbt .x .xs .(x ∷ p₁ ^ x ∷ p₂) (.x ∷ p₁ , p₂ , p₃ , refl)) = trans-law p₃ (push-in x p₁ p₂)

exch : {A : Set}(v w : A)(xs ys : List A) → P (v ∷ xs ^ ⟨ w ⟩ ^ ys) (w ∷ xs ^ ⟨ v ⟩ ^ ys)
exch v w ⟨⟩ ⟨⟩ = sbt v (w ∷ ⟨⟩) (w ∷ v ∷ ⟨⟩) (w ∷ ⟨⟩ , ⟨⟩ , sbt w ⟨⟩ (w ∷ ⟨⟩) (⟨⟩ , ⟨⟩ , nil ⟨⟩ refl , refl) , refl)
exch v w ⟨⟩ (x ∷ ys) = swap v w (x ∷ ys)
exch v w (x ∷ xs) ys with ins x (exch v w xs ys)
... | prf with swap v x (xs ^ w ∷ ys) | swap x w (xs ^ v ∷ ys)
... | sw₁ | sw₂ = trans-law (trans-law sw₁ prf) sw₂

sym-law {xs = ⟨⟩} {.⟨⟩} (nil .⟨⟩ refl) = nil ⟨⟩ refl
sym-law {xs = x ∷ xs} {.⟨⟩} (nil .(x ∷ xs) ())
sym-law {xs = x ∷ xs} {.(p₁ ^ x ∷ p₂)} (sbt .x .xs .(p₁ ^ x ∷ p₂) (p₁ , p₂ , p₃ , refl))
  with push-out x p₁ p₂ | ins x (sym-law p₃)
... | q₁ | q₂ = trans-law q₁ q₂

open import Data.Empty

⟨⟩≢xs^w∷ys : {A : Set}(w : A)(xs ys : List A) → ⟨⟩ ≢ xs ^ w ∷ ys
⟨⟩≢xs^w∷ys w ⟨⟩ ys ()
⟨⟩≢xs^w∷ys w (x ∷ xs) ys ()

trans-law {xs = ⟨⟩} {.⟨⟩} {zs} (nil .⟨⟩ refl) q = q
trans-law {xs = x ∷ xs} {.⟨⟩} {zs} (nil .(x ∷ xs) ()) q
trans-law {xs = x ∷ xs} {.⟨⟩} {.⟨⟩} (sbt .x .xs .⟨⟩ (p₁ , p₂ , p₃ , p₄)) (nil .⟨⟩ refl) = ⊥-elim (⟨⟩≢xs^w∷ys x p₁ p₂ p₄)
trans-law {xs = x ∷ xs} {.(x₁ ∷ s)} {.t} (sbt .x .xs .(x₁ ∷ s) (p₁ , p₂ , p₃ , p₄)) (sbt x₁ s t x₂) = {!!}
