open import Data.List renaming ([] to ⟨⟩; [_] to ⟨_⟩; _++_ to _⌢_)
open import Relation.Binary.PropositionalEquality as PropEq
open import Data.Product using (∃; _,_) renaming (_×_ to _∧_)
open import Data.Empty

data P {A : Set} : List A → List A → Set where
  ∅_ : {t : List A} → (prf : ⟨⟩ ≡ t) → P ⟨⟩ t
  ⟨_⟩⌢_≌_with-⟦_⟧ : (x : A) (s t : List A)
         → (∃ λ u → ∃ λ v → P s (u ⌢ v) ∧ t ≡ u ⌢ ⟨ x ⟩ ⌢ v)
         → P (⟨ x ⟩ ⌢ s) t

reflexivity : {A : Set} (xs : List A) → P xs xs
reflexivity ⟨⟩ = ∅ refl
reflexivity (x ∷ xs) = ⟨ x ⟩⌢ xs ≌ ⟨ x ⟩ ⌢ xs with-⟦ ⟨⟩ , xs , reflexivity xs , refl ⟧

symmetricity : {A : Set} (xs ys : List A) → P xs ys → P ys xs
symmetricity xs ys prf = {!!}

{--
-- | list properties
⟨⟩≢xs⌢w∷ys : {A : Set}(w : A)(xs ys : List A) → ⟨⟩ ≢ xs ⌢ w ∷ ys
⟨⟩≢xs⌢w∷ys w ⟨⟩ ys ()
⟨⟩≢xs⌢w∷ys w (x ∷ xs) ys ()

p⌢q≡⟨⟩⇒p≡⟨⟩∧q≡⟨⟩ : {A : Set}{p q : List A} → p ⌢ q ≡ ⟨⟩ → p ≡ ⟨⟩ ∧ q ≡ ⟨⟩
p⌢q≡⟨⟩⇒p≡⟨⟩∧q≡⟨⟩ {p = ⟨⟩} {.⟨⟩} refl = refl , refl
p⌢q≡⟨⟩⇒p≡⟨⟩∧q≡⟨⟩ {p = x ∷ p} {q} ()

assoc-list : {A : Set}(x y z : List A) → (x ⌢ y) ⌢ z ≡ x ⌢ (y ⌢ z)
assoc-list ⟨⟩ ys zs = refl
assoc-list (x ∷ xs) ys zs = cong (x ∷_) (assoc-list xs ys zs)

⟨⟩-cancel : {A : Set}(xs : List A) → xs ⌢ ⟨⟩ ≡ xs
⟨⟩-cancel ⟨⟩ = refl
⟨⟩-cancel (x ∷ xs) = cong (x ∷_) (⟨⟩-cancel xs)

push-in-l : {A : Set}(w : A)(xs ys : List A){zs : List A} → P (xs ⌢ ⟨ w ⟩ ⌢ ys) zs → P (⟨ w ⟩ ⌢ xs ⌢ ys) zs
push-in-l w xs ys prf = {!!}

-- | independent
refl-law : {A : Set} {xs : List A} → P xs xs
refl-law {xs = ⟨⟩} = nil ⟨⟩ refl
refl-law {xs = x ∷ xs} = sbt x xs (x ∷ xs) (⟨⟩ , xs , refl-law , refl)

-- | independent (depends on ⟨⟩-cancel which is list level property)
del-⟨⟩-r : {A : Set}{xs ys : List A} → P xs (ys ⌢ ⟨⟩) → P xs ys
del-⟨⟩-r {ys = ⟨⟩} prf = prf
del-⟨⟩-r {ys = x ∷ ys} (nil .(x ∷ ys ⌢ ⟨⟩) ())
del-⟨⟩-r {ys = x₁ ∷ ys} (sbt x s .(x₁ ∷ ys ⌢ ⟨⟩) (p₁ , p₂ , p₃ , p₄))
  = sbt x s (x₁ ∷ ys) (p₁ , p₂ , p₃ , trans (sym (⟨⟩-cancel (⟨ x₁ ⟩ ⌢ ys))) p₄)

-- | independent
del-⟨⟩-l : {A : Set}{xs ys : List A} → P (xs ⌢ ⟨⟩) ys → P xs ys
del-⟨⟩-l {xs = ⟨⟩} prf = prf
del-⟨⟩-l {xs = x ∷ xs} (sbt .x .(xs ⌢ ⟨⟩) t (p₁ , p₂ , p₃ , p₄))
  = sbt x xs t (p₁ , p₂ , del-⟨⟩-l {xs = xs} {p₁ ⌢ p₂} p₃ , p₄)

-- | independent (depends on ⟨⟩-cancel which is list level property)
add-⟨⟩-r : {A : Set}{xs ys : List A} → P xs ys → P xs (ys ⌢ ⟨⟩)
add-⟨⟩-r {ys = ⟨⟩} prf = prf
add-⟨⟩-r {ys = x ∷ ys} (nil .(x ∷ ys) ())
add-⟨⟩-r {ys = x₁ ∷ ys} (sbt x s .(x₁ ∷ ys) (p₁ , p₂ , p₃ , p₄))
  = sbt x s (x₁ ∷ ys ⌢ ⟨⟩) (p₁ , p₂ , p₃ , trans (⟨⟩-cancel (⟨ x₁ ⟩ ⌢ ys)) p₄)

-- | independent
add-⟨⟩-l : {A : Set}{xs ys : List A} → P xs ys → P (xs ⌢ ⟨⟩) ys
add-⟨⟩-l {xs = ⟨⟩} prf = prf
add-⟨⟩-l {xs = x ∷ xs} (sbt .x .xs t (p₁ , p₂ , p₃ , p₄))
  = sbt x (xs ⌢ ⟨⟩) t (p₁ , p₂ , add-⟨⟩-l {xs = xs} {p₁ ⌢ p₂} p₃ , p₄)

-- | independent
flip : {A : Set}(xs ys : List A) → P (xs ⌢ ys) (ys ⌢ xs)
flip ⟨⟩ ys = add-⟨⟩-r refl-law
flip (x ∷ xs) ys = sbt x (xs ⌢ ys) (ys ⌢ x ∷ xs) (ys , xs , flip xs ys , refl)

-- | independent
assoc-l : {A : Set}{xs ys zs ws : List A} → P (xs ⌢ (ys ⌢ zs)) ws → P ((xs ⌢ ys) ⌢ zs) ws
assoc-l {xs = ⟨⟩} {ys} {zs} prf = prf
assoc-l {xs = x ∷ xs} {ys} {zs} (sbt .x .(xs ⌢ ys ⌢ zs) t (p₁ , p₂ , p₃ , p₄))
  = sbt x ((xs ⌢ ys) ⌢ zs) t (p₁ , p₂ , assoc-l {xs = xs} p₃ , p₄)

-- | independent
rev-assoc-l : {A : Set}{xs ys zs ws : List A} → P ((xs ⌢ ys) ⌢ zs) ws → P (xs ⌢ (ys ⌢ zs)) ws
rev-assoc-l {xs = ⟨⟩} {ys} {zs} prf = prf
rev-assoc-l {xs = x ∷ xs} {ys} {zs} (sbt .x .((xs ⌢ ys) ⌢ zs) t (p₁ , p₂ , p₃ , p₄))
  = sbt x (xs ⌢ ys ⌢ zs) t (p₁ , p₂ , rev-assoc-l {xs = xs} p₃ , p₄)

-- | independent (depends on assoc-list which is list level property)
assoc-r : {A : Set}{xs ys zs ws : List A} → P ws (xs ⌢ (ys ⌢ zs)) → P ws ((xs ⌢ ys) ⌢ zs)
assoc-r {xs = ⟨⟩} {ys} {zs} prf = prf
assoc-r {xs = x ∷ xs} {ys} {zs} (nil .(x ∷ xs ⌢ ys ⌢ zs) ())
assoc-r {xs = x₁ ∷ xs} {ys} {zs} (sbt x s .(x₁ ∷ xs ⌢ ys ⌢ zs) (p₁ , p₂ , p₃ , p₄))
  = sbt x s (x₁ ∷ (xs ⌢ ys) ⌢ zs) (p₁ , p₂ , p₃ , trans (cong (x₁ ∷_) (assoc-list xs ys zs)) p₄)

-- | independent
rev-assoc-r : {A : Set}{xs ys zs ws : List A} → P ws ((xs ⌢ ys) ⌢ zs) → P ws (xs ⌢ (ys ⌢ zs))
rev-assoc-r {xs = ⟨⟩} {ys} {zs} prf = prf
rev-assoc-r {xs = x ∷ xs} {ys} {zs} (nil .(x ∷ (xs ⌢ ys) ⌢ zs) ())
rev-assoc-r {xs = x₁ ∷ xs} {ys} {zs} (sbt x s .(x₁ ∷ (xs ⌢ ys) ⌢ zs) (p₁ , p₂ , p₃ , p₄))
  = sbt x s (x₁ ∷ xs ⌢ ys ⌢ zs) (p₁ , p₂ , p₃ , trans (sym (cong (x₁ ∷_) (assoc-list xs ys zs))) p₄)

-- | depends on just only refl-law
push-in : {A : Set}(x : A)(xs ys : List A) → P (⟨ x ⟩ ⌢ xs ⌢ ys) (xs ⌢ ⟨ x ⟩ ⌢ ys)
push-in x xs ys = sbt x (xs ⌢ ys) (xs ⌢ ⟨ x ⟩ ⌢ ys) (xs , ys , refl-law , refl)

-- | depends on just only refl-law
pull-out : {A : Set}(x : A)(xs ys : List A) → P (xs ⌢ ⟨ x ⟩ ⌢ ys) (⟨ x ⟩ ⌢ xs ⌢ ys)
pull-out x ⟨⟩ ⟨⟩ = sbt x ⟨⟩ (x ∷ ⟨⟩) (⟨⟩ , ⟨⟩ , nil ⟨⟩ refl , refl)
pull-out x ⟨⟩ (y ∷ ys) = refl-law
pull-out x (x₁ ∷ xs) ys = sbt x₁ (xs ⌢ ⟨ x ⟩ ⌢ ys) (⟨ x ⟩ ⌢ ⟨ x₁ ⟩ ⌢ (xs ⌢ ys)) (⟨ x ⟩ , xs ⌢ ys , pull-out x xs ys , refl)

-- | depends on just only refl-law
swap : {A : Set}(x y : A)(xs : List A) → P (⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ xs) (⟨ y ⟩ ⌢ ⟨ x ⟩ ⌢ xs)
swap x y xs = push-in x (⟨ y ⟩) xs

-- | independent
ins : {A : Set}(x : A){xs ys : List A} → P xs ys → P (⟨ x ⟩ ⌢ xs) (⟨ x ⟩ ⌢ ys)
ins x (nil .⟨⟩ refl) = sbt x ⟨⟩ (x ∷ ⟨⟩) (⟨⟩ , ⟨⟩ , nil ⟨⟩ refl , refl)
ins x (sbt x₁ s t x₂) = sbt x (x₁ ∷ s) (x ∷ t) (⟨⟩ , t , sbt x₁ s t x₂ , refl)

-- | independent
ins' : {A : Set}{xs ys : List A}(zs : List A) → P xs ys → P (zs ⌢ xs) (zs ⌢ ys)
ins' ⟨⟩ prf = prf
ins' {xs = xs} {ys} (x ∷ zs) prf = sbt x (zs ⌢ xs) (x ∷ zs ⌢ ys) (⟨⟩ , zs ⌢ ys , ins' {xs = xs} {ys} zs prf , refl)

-- | depends on list level properties only.
add : {A : Set}(x : A){xs ys : List A} → P xs ys → P (xs ⌢ ⟨ x ⟩) (ys ⌢ ⟨ x ⟩)
add x (nil .⟨⟩ refl) = sbt x ⟨⟩ (x ∷ ⟨⟩) (⟨⟩ , ⟨⟩ , nil ⟨⟩ refl , refl)
add x (sbt x₁ s .(p₁ ⌢ x₁ ∷ p₂) (p₁ , p₂ , p₃ , refl))
  = sbt x₁ (s ⌢ ⟨ x ⟩) ((p₁ ⌢ ⟨ x₁ ⟩ ⌢ p₂) ⌢ ⟨ x ⟩) (p₁ , p₂ ⌢ ⟨ x ⟩ , help p₁ p₂ s (add x p₃) , assoc-list p₁ (⟨ x₁ ⟩ ⌢ p₂) ⟨ x ⟩)
  where
    help : {A : Set} (p₁ p₂ s : List A) {x : A} → P (s ⌢ ⟨ x ⟩) ((p₁ ⌢ p₂) ⌢ ⟨ x ⟩) → P (s ⌢ ⟨ x ⟩) (p₁ ⌢ p₂ ⌢ ⟨ x ⟩)
    help p₁ p₂ s {x} p rewrite assoc-list p₁ p₂ ⟨ x ⟩ = p

-- | depends on add which depends on list level properties only.
add' : {A : Set}{xs ys : List A}(zs : List A) → P xs ys → P (xs ⌢ zs) (ys ⌢ zs)
add' {xs = xs} {ys} ⟨⟩ p = add-⟨⟩-l {xs = xs} {ys ⌢ ⟨⟩} (add-⟨⟩-r {xs = xs} {ys} p)
add' {xs = xs} {ys} (x ∷ zs) p with add' {xs = xs ⌢ ⟨ x ⟩} {ys ⌢ ⟨ x ⟩} zs (add x {xs} {ys} p)
... | q = rev-assoc-l {xs = xs} {⟨ x ⟩} (rev-assoc-r {xs = ys} {⟨ x ⟩} {zs} q)

sym-law : {A : Set} {xs ys : List A} → P xs ys → P ys xs
sym-law {xs = .⟨⟩} {.⟨⟩} (nil .⟨⟩ refl) = nil ⟨⟩ refl
sym-law {xs = .(x ∷ ⟨⟩)} {.t} (sbt x .⟨⟩ t (p₁ , p₂ , nil .(p₁ ⌢ p₂) prf , p₄)) with p⌢q≡⟨⟩⇒p≡⟨⟩∧q≡⟨⟩ {p = p₁} {p₂} prf
... | refl , refl rewrite p₄ = sbt x ⟨⟩ (⟨ x ⟩) (⟨⟩ , ⟨⟩ , nil ⟨⟩ refl , refl)
sym-law {xs = .(x ∷ x₁ ∷ s)} {.t} (sbt x .(x₁ ∷ s) t (p₁ , p₂ , sbt x₁ s .(p₁ ⌢ p₂) (q₁ , q₂ , q₃ , q₄) , p₄)) = {!!}

trans-law : {A : Set} {xs ys zs : List A} → P xs ys → P ys zs → P xs zs
trans-law {xs = xs} {ys} {zs} p q = {!!}

trans-law {xs = .⟨⟩} {⟨⟩} {zs} (nil .⟨⟩ refl) q = q
trans-law {xs = .(x ∷ s)} {⟨⟩} {zs} (sbt x s .⟨⟩ (p₁ , p₂ , p₃ , p₄)) q = ⊥-elim (⟨⟩≢xs⌢w∷ys x p₁ p₂ p₄)
trans-law {xs = xs} {x ∷ ys} {.⟨⟩} p (nil .(x ∷ ys) ())
trans-law {xs = ⟨⟩} {x ∷ ys} {.(p₁ ⌢ x ∷ p₂)} () (sbt .x .ys .(p₁ ⌢ x ∷ p₂) (p₁ , p₂ , p₃ , refl))
trans-law {xs = .x ∷ xs} {x ∷ ys} {.(p₁ ⌢ x ∷ p₂)} (sbt .x .xs .(x ∷ ys) (⟨⟩ , .ys , q₃ , refl)) (sbt .x .ys .(p₁ ⌢ x ∷ p₂) (p₁ , p₂ , p₃ , refl))
  = sbt x xs (p₁ ⌢ x ∷ p₂) (p₁ , p₂ , trans-law q₃ p₃ , refl)
trans-law {xs = x₁ ∷ xs} {x ∷ .(q₁ ⌢ x₁ ∷ q₂)} {.(p₁ ⌢ x ∷ p₂)} (sbt .x₁ .xs .(x ∷ q₁ ⌢ x₁ ∷ q₂) (.x ∷ q₁ , q₂ , q₃ , refl)) (sbt .x .(q₁ ⌢ x₁ ∷ q₂) .(p₁ ⌢ x ∷ p₂) (p₁ , p₂ , p₃ , refl)) = {!!}

sym-law {xs = ⟨⟩} {.⟨⟩} (nil .⟨⟩ refl) = nil ⟨⟩ refl
sym-law {xs = x ∷ xs} {.⟨⟩} (nil .(x ∷ xs) ())
sym-law {xs = x ∷ xs} {.(p₁ ⌢ x ∷ p₂)} (sbt .x .xs .(p₁ ⌢ x ∷ p₂) (p₁ , p₂ , p₃ , refl))
  with pull-out x p₁ p₂ | ins x (sym-law p₃)
... | q₁ | q₂ = trans-law q₁ q₂

del : {A : Set}(x : A)(xs ys : List A) → P (x ∷ xs) (x ∷ ys) → P xs ys
del x xs ys (sbt .x .xs .(x ∷ ys) (⟨⟩ , .ys , p₃ , refl)) = p₃
del x xs .(p₁ ⌢ x ∷ p₂) (sbt .x .xs .(x ∷ p₁ ⌢ x ∷ p₂) (.x ∷ p₁ , p₂ , p₃ , refl)) = trans-law p₃ (push-in x p₁ p₂)

exch : {A : Set}(v w : A)(xs ys : List A) → P (v ∷ xs ⌢ ⟨ w ⟩ ⌢ ys) (w ∷ xs ⌢ ⟨ v ⟩ ⌢ ys)
exch v w ⟨⟩ ⟨⟩ = sbt v (w ∷ ⟨⟩) (w ∷ v ∷ ⟨⟩) (w ∷ ⟨⟩ , ⟨⟩ , sbt w ⟨⟩ (w ∷ ⟨⟩) (⟨⟩ , ⟨⟩ , nil ⟨⟩ refl , refl) , refl)
exch v w ⟨⟩ (x ∷ ys) = swap v w (x ∷ ys)
exch v w (x ∷ xs) ys with ins x (exch v w xs ys)
... | prf with swap v x (xs ⌢ w ∷ ys) | swap x w (xs ⌢ v ∷ ys)
... | sw₁ | sw₂ = trans-law (trans-law sw₁ prf) sw₂

--}
