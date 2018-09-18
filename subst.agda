open import Data.List renaming ([] to ⟨⟩; [_] to ⟨_⟩; _++_ to _⌢_)
open import Relation.Binary.PropositionalEquality as PropEq
open import Data.Product using (∃; _,_) renaming (_×_ to _∧_)
open import Data.Empty
open import Relation.Nullary

data P {A : Set} : List A → List A → Set where
  ∅_ : {t : List A} → (prf : ⟨⟩ ≡ t) → P ⟨⟩ t
  ⟨_⟩⌢_≌_with-⟦_⟧ : (x : A) (s t : List A)
         → (∃ λ u → ∃ λ v → P s (u ⌢ v) ∧ t ≡ u ⌢ ⟨ x ⟩ ⌢ v)
         → P (⟨ x ⟩ ⌢ s) t

-- | list level utility
⟨⟩≢xs⌢w∷ys : {A : Set}(w : A)(xs ys : List A) → ⟨⟩ ≢ xs ⌢ w ∷ ys
⟨⟩≢xs⌢w∷ys w ⟨⟩ ys ()
⟨⟩≢xs⌢w∷ys w (x ∷ xs) ys ()

-- | list level utility
⟨⟩-cancel : {A : Set}(xs : List A) → xs ⌢ ⟨⟩ ≡ xs
⟨⟩-cancel ⟨⟩ = refl
⟨⟩-cancel (x ∷ xs) = cong (x ∷_) (⟨⟩-cancel xs)

-- | list level utility
assoc-list : {A : Set}(x y z : List A) → (x ⌢ y) ⌢ z ≡ x ⌢ (y ⌢ z)
assoc-list ⟨⟩ ys zs = refl
assoc-list (x ∷ xs) ys zs = cong (x ∷_) (assoc-list xs ys zs)

-- | add ⟨⟩ for rhs on P
add-⟨⟩-rhs : {A : Set}{xs ys : List A} → P xs ys → P xs (ys ⌢ ⟨⟩)
add-⟨⟩-rhs {xs = .⟨⟩} {.⟨⟩} (∅ refl) = ∅ refl
add-⟨⟩-rhs {xs = .(x ∷ s)} {.t} ⟨ x ⟩⌢ s ≌ t with-⟦ u , v , P , p ⟧
  = ⟨ x ⟩⌢ s ≌ t ⌢ ⟨⟩ with-⟦ u , v , P , trans (cong (_⌢ ⟨⟩) p) (⟨⟩-cancel (u ⌢ ⟨ x ⟩ ⌢ v)) ⟧

-- | add ⟨ x ⟩ for rhs on P
add : {A : Set}{xs ys : List A}(x : A) → P xs ys → P (⟨ x ⟩ ⌢ xs) (ys ⌢ ⟨ x ⟩)
add {xs = xs} {ys} x p = ⟨ x ⟩⌢ xs ≌ (ys ⌢ ⟨ x ⟩ ⌢ ⟨⟩) with-⟦ ys , ⟨⟩ , add-⟨⟩-rhs p , refl ⟧

-- | insert ⟨ x ⟩ for rhs on P
insert : {A : Set}{xs ys : List A}(x : A) → P xs ys → P (⟨ x ⟩ ⌢ xs) (⟨ x ⟩ ⌢ ys)
insert {xs = xs} {ys} x p = ⟨ x ⟩⌢ xs ≌ ⟨ x ⟩ ⌢ ys with-⟦ ⟨⟩ , ys , p , refl ⟧

-- | interpose ⟨ x ⟩ for rhs on P
interpose : {A : Set}{xs ys zs : List A}(x : A) → P xs (ys ⌢ zs) → P (⟨ x ⟩ ⌢ xs) (ys ⌢ ⟨ x ⟩ ⌢ zs)
interpose {xs = .⟨⟩} {⟨⟩} {.⟨⟩} x (∅ refl) = ⟨ x ⟩⌢ ⟨⟩ ≌ ⟨ x ⟩ ⌢ ⟨⟩ with-⟦ ⟨⟩ , ⟨⟩ , (∅ refl) , refl ⟧
interpose {xs = .⟨⟩} {x₁ ∷ ys} {zs} x (∅ ())
interpose {xs = .(x₁ ∷ s)} {ys} {zs} x ⟨ x₁ ⟩⌢ s ≌ .(ys ⌢ zs) with-⟦ u , v , P , p ⟧
  = ⟨ x ⟩⌢ x₁ ∷ s ≌ ys ⌢ x ∷ zs with-⟦ ys , zs , ⟨ x₁ ⟩⌢ s ≌ ys ⌢ zs with-⟦ u , v , P , p ⟧ , refl ⟧

del-⟨⟩-lhs : {A : Set}{xs ys : List A} → P (xs ⌢ ⟨⟩) ys → P xs ys
del-⟨⟩-lhs {xs = ⟨⟩} {ys} p = p
del-⟨⟩-lhs {xs = x ∷ xs} {.t} ⟨ .x ⟩⌢ .(xs ⌢ ⟨⟩) ≌ t with-⟦ u , v , P , p ⟧
  = ⟨ x ⟩⌢ xs ≌ t with-⟦ u , v , del-⟨⟩-lhs {xs = xs} {u ⌢ v} P , p ⟧

¬P[x∷xs]⟨⟩ : {A : Set}{x : A}{xs : List A} → ¬ (P (⟨ x ⟩ ⌢ xs) ⟨⟩)
¬P[x∷xs]⟨⟩ {xs = .s} ⟨ x ⟩⌢ s ≌ .⟨⟩ with-⟦ u , v , P , p ⟧ = ⊥-elim (⟨⟩≢xs⌢w∷ys x u v p)

-- 
inverse : {A : Set}(x : A) (u v s : List A) → P (u ⌢ v) s → P (u ⌢ ⟨ x ⟩ ⌢ v) (⟨ x ⟩ ⌢ s)
inverse x ⟨⟩ v s p = insert x p
inverse x (x₁ ∷ u) v .(u₂ ⌢ x₁ ∷ v₂) ⟨ .x₁ ⟩⌢ .(u ⌢ v) ≌ .(u₂ ⌢ x₁ ∷ v₂) with-⟦ u₂ , v₂ , P₂ , refl ⟧ with inverse x u v (u₂ ⌢ v₂) P₂
... | q = ⟨ x₁ ⟩⌢ u ⌢ x ∷ v ≌ x ∷ u₂ ⌢ x₁ ∷ v₂ with-⟦ x ∷ u₂ , v₂ , q , refl ⟧

-- | 1
x≌x : {A : Set}(x : A) → P (⟨ x ⟩ ⌢ ⟨⟩) (⟨⟩ ⌢ ⟨ x ⟩)
x≌x x = ⟨ x ⟩⌢ ⟨⟩ ≌ ⟨ x ⟩ with-⟦ ⟨⟩ , ⟨⟩ , (∅ refl) , refl ⟧


-- | 2
xy≌xy : {A : Set}(x y : A) → P (⟨ x ⟩ ⌢ ⟨ y ⟩) (⟨ x ⟩ ⌢ ⟨ y ⟩)
xy≌xy x y = ⟨ x ⟩⌢ ⟨ y ⟩ ≌ ⟨ x ⟩ ⌢  ⟨ y ⟩ with-⟦ ⟨⟩ , ⟨ y ⟩ , x≌x y , refl ⟧

xy≌yx : {A : Set}(x y : A) → P (⟨ x ⟩ ⌢ ⟨ y ⟩) (⟨ y ⟩ ⌢ ⟨ x ⟩)
xy≌yx x y = ⟨ x ⟩⌢ ⟨ y ⟩ ≌ ⟨ y ⟩ ⌢ ⟨ x ⟩ with-⟦ ⟨ y ⟩ , ⟨⟩ , x≌x y , refl ⟧

-- | 3
xyz≌xyz : {A : Set}(x y z : A) → P (⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩)  (⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩)
xyz≌xyz x y z = ⟨ x ⟩⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ≌ ⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ with-⟦ ⟨⟩ , ⟨ y ⟩ ⌢ ⟨ z ⟩ , xy≌xy y z , refl ⟧

xyz≌yxz : {A : Set}(x y z : A) → P (⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩) (⟨ y ⟩ ⌢ ⟨ x ⟩ ⌢ ⟨ z ⟩)
xyz≌yxz x y z  = ⟨ x ⟩⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ≌ ⟨ y ⟩ ⌢ ⟨ x ⟩ ⌢ ⟨ z ⟩ with-⟦ ⟨ y ⟩ , ⟨ z ⟩ , xy≌xy y z , refl ⟧

xyz≌yzx : {A : Set}(x y z : A) → P (⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩) (⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ x ⟩)
xyz≌yzx x y z = ⟨ x ⟩⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ≌ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ x ⟩ with-⟦ ⟨ y ⟩ ⌢ ⟨ z ⟩ , ⟨⟩ , xy≌xy y z , refl ⟧

xyz≌xzy : {A : Set}(x y z : A) → P (⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩) (⟨ x ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ y ⟩)
xyz≌xzy x y z = ⟨ x ⟩⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ≌ ⟨ x ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ y ⟩ with-⟦ ⟨⟩ ,  ⟨ z ⟩ ⌢ ⟨ y ⟩ , xy≌yx y z , refl ⟧

xyz≌zxy : {A : Set}(x y z : A) → P (⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩) (⟨ z ⟩ ⌢ ⟨ x ⟩ ⌢ ⟨ y ⟩)
xyz≌zxy x y z = ⟨ x ⟩⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ≌ ⟨ z ⟩ ⌢ ⟨ x ⟩ ⌢ ⟨ y ⟩ with-⟦ ⟨ z ⟩ , ⟨ y ⟩ , xy≌yx y z , refl ⟧

xyz≌zyx : {A : Set}(x y z : A) → P (⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩) (⟨ z ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ x ⟩)
xyz≌zyx x y z = ⟨ x ⟩⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ≌ ⟨ z ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ x ⟩ with-⟦ ⟨ z ⟩ ⌢ ⟨ y ⟩ , ⟨⟩ , xy≌yx y z , refl ⟧

-- | 4
xyzw≌xyzw : {A : Set}(x y z w : A) → P (⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩) (⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩)
xyzw≌xyzw x y z w = ⟨ x ⟩⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩ ≌ ⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩ with-⟦ ⟨⟩ , ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩ , xyz≌xyz y z w , refl ⟧

xyzw≌yxzw : {A : Set}(x y z w : A) → P (⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩) (⟨ y ⟩ ⌢ ⟨ x ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩)
xyzw≌yxzw x y z w = ⟨ x ⟩⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩ ≌ ⟨ y ⟩ ⌢ ⟨ x ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩ with-⟦ ⟨ y ⟩ ,  ⟨ z ⟩ ⌢ ⟨ w ⟩ , xyz≌xyz y z w , refl ⟧

xyzw≌yzxw : {A : Set}(x y z w : A) → P (⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩) (⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ x ⟩ ⌢ ⟨ w ⟩)
xyzw≌yzxw x y z w = ⟨ x ⟩⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩ ≌ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ x ⟩ ⌢ ⟨ w ⟩ with-⟦ ⟨ y ⟩ ⌢ ⟨ z ⟩ , ⟨ w ⟩ , xyz≌xyz y z w , refl ⟧

xyzw≌yzwx : {A : Set}(x y z w : A) → P (⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩) (⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩ ⌢ ⟨ x ⟩)
xyzw≌yzwx x y z w = ⟨ x ⟩⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩ ≌ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩ ⌢ ⟨ x ⟩ with-⟦ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩ , ⟨⟩ , xyz≌xyz y z w , refl ⟧

xyzw≌xzyw : {A : Set}(x y z w : A) → P (⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩) (⟨ x ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ w ⟩)
xyzw≌xzyw x y z w = ⟨ x ⟩⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩ ≌ ⟨ x ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ w ⟩ with-⟦ ⟨⟩ , ⟨ z ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ w ⟩ ,  xyz≌yxz y z w , refl ⟧

xyzw≌zxyw : {A : Set}(x y z w : A) → P (⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩) (⟨ z ⟩ ⌢ ⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ w ⟩)
xyzw≌zxyw x y z w = ⟨ x ⟩⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩ ≌ ⟨ z ⟩ ⌢ ⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ w ⟩ with-⟦ ⟨ z ⟩ , ⟨ y ⟩ ⌢ ⟨ w ⟩ , xyz≌yxz y z w , refl ⟧

xyzw≌zyxw : {A : Set}(x y z w : A) → P (⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩) (⟨ z ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ x ⟩ ⌢ ⟨ w ⟩)
xyzw≌zyxw x y z w = ⟨ x ⟩⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩ ≌ ⟨ z ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ x ⟩ ⌢ ⟨ w ⟩ with-⟦ ⟨ z ⟩ ⌢ ⟨ y ⟩ , ⟨ w ⟩ , xyz≌yxz y z w , refl ⟧

xyzw≌zywx : {A : Set}(x y z w : A) → P (⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩) (⟨ z ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ w ⟩ ⌢ ⟨ x ⟩)
xyzw≌zywx x y z w = ⟨ x ⟩⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩ ≌ ⟨ z ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ w ⟩ ⌢ ⟨ x ⟩ with-⟦ ⟨ z ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ w ⟩ , ⟨⟩ , xyz≌yxz y z w , refl ⟧

xyzw≌xzwy : {A : Set}(x y z w : A) → P (⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩) (⟨ x ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩ ⌢ ⟨ y ⟩)
xyzw≌xzwy x y z w = ⟨ x ⟩⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩ ≌ ⟨ x ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩ ⌢ ⟨ y ⟩ with-⟦ ⟨⟩ , ⟨ z ⟩ ⌢ ⟨ w ⟩ ⌢ ⟨ y ⟩ , xyz≌yzx y z w , refl ⟧

xyzw≌zxwy : {A : Set}(x y z w : A) → P (⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩) (⟨ z ⟩ ⌢ ⟨ x ⟩ ⌢ ⟨ w ⟩ ⌢ ⟨ y ⟩)
xyzw≌zxwy x y z w = ⟨ x ⟩⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩ ≌ ⟨ z ⟩ ⌢ ⟨ x ⟩ ⌢ ⟨ w ⟩ ⌢ ⟨ y ⟩ with-⟦ ⟨ z ⟩ , ⟨ w ⟩ ⌢ ⟨ y ⟩ , xyz≌yzx y z w , refl ⟧

xyzw≌zwxy : {A : Set}(x y z w : A) → P (⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩) (⟨ z ⟩ ⌢ ⟨ w ⟩ ⌢ ⟨ x ⟩ ⌢ ⟨ y ⟩)
xyzw≌zwxy x y z w = ⟨ x ⟩⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩ ≌ ⟨ z ⟩ ⌢ ⟨ w ⟩ ⌢ ⟨ x ⟩ ⌢ ⟨ y ⟩ with-⟦ ⟨ z ⟩ ⌢ ⟨ w ⟩ , ⟨ y ⟩ , xyz≌yzx y z w , refl ⟧

xyzw≌zwyx : {A : Set}(x y z w : A) → P (⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩) (⟨ z ⟩ ⌢ ⟨ w ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ x ⟩)
xyzw≌zwyx x y z w = ⟨ x ⟩⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩ ≌ ⟨ z ⟩ ⌢ ⟨ w ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ x ⟩ with-⟦ ⟨ z ⟩ ⌢ ⟨ w ⟩ ⌢ ⟨ y ⟩ , ⟨⟩ , xyz≌yzx y z w , refl ⟧

xyzw≌xywz : {A : Set}(x y z w : A) → P (⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩) (⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ w ⟩ ⌢ ⟨ z ⟩)
xyzw≌xywz x y z w = ⟨ x ⟩⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩ ≌ ⟨ x ⟩ ⌢  ⟨ y ⟩ ⌢ ⟨ w ⟩ ⌢ ⟨ z ⟩ with-⟦ ⟨⟩ , ⟨ y ⟩ ⌢ ⟨ w ⟩ ⌢ ⟨ z ⟩ , xyz≌xzy y z w , refl ⟧

xyzw≌yxwz : {A : Set}(x y z w : A) → P (⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩) (⟨ y ⟩ ⌢ ⟨ x ⟩ ⌢ ⟨ w ⟩ ⌢ ⟨ z ⟩)
xyzw≌yxwz x y z w = ⟨ x ⟩⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩ ≌ ⟨ y ⟩ ⌢ ⟨ x ⟩ ⌢ ⟨ w ⟩ ⌢ ⟨ z ⟩ with-⟦ ⟨ y ⟩ , ⟨ w ⟩ ⌢ ⟨ z ⟩ , xyz≌xzy y z w , refl ⟧

xyzw≌ywxz : {A : Set}(x y z w : A) → P (⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩) (⟨ y ⟩ ⌢ ⟨ w ⟩ ⌢ ⟨ x ⟩ ⌢ ⟨ z ⟩)
xyzw≌ywxz x y z w = ⟨ x ⟩⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩ ≌ ⟨ y ⟩ ⌢ ⟨ w ⟩ ⌢ ⟨ x ⟩ ⌢ ⟨ z ⟩ with-⟦ ⟨ y ⟩ ⌢ ⟨ w ⟩ , ⟨ z ⟩ , xyz≌xzy y z w , refl ⟧

xyzw≌ywzx : {A : Set}(x y z w : A) → P (⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩) (⟨ y ⟩ ⌢ ⟨ w ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ x ⟩)
xyzw≌ywzx x y z w = ⟨ x ⟩⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩ ≌ ⟨ y ⟩ ⌢ ⟨ w ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ x ⟩ with-⟦ ⟨ y ⟩ ⌢ ⟨ w ⟩ ⌢ ⟨ z ⟩ , ⟨⟩ , xyz≌xzy y z w , refl ⟧

xyzw≌xwyz : {A : Set}(x y z w : A) → P (⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩) (⟨ x ⟩ ⌢ ⟨ w ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩)
xyzw≌xwyz x y z w = ⟨ x ⟩⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩ ≌ ⟨ x ⟩ ⌢ ⟨ w ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ with-⟦ ⟨⟩ , ⟨ w ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ , xyz≌zxy y z w , refl ⟧

xyzw≌wxyz : {A : Set}(x y z w : A) → P (⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩) (⟨ w ⟩ ⌢ ⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩)
xyzw≌wxyz x y z w = ⟨ x ⟩⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩ ≌ ⟨ w ⟩ ⌢ ⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ with-⟦ ⟨ w ⟩ , ⟨ y ⟩ ⌢ ⟨ z ⟩ , xyz≌zxy y z w , refl ⟧

xyzw≌wyxz : {A : Set}(x y z w : A) → P (⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩) (⟨ w ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ x ⟩ ⌢ ⟨ z ⟩)
xyzw≌wyxz x y z w = ⟨ x ⟩⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩ ≌ ⟨ w ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ x ⟩ ⌢ ⟨ z ⟩ with-⟦ ⟨ w ⟩ ⌢ ⟨ y ⟩ , ⟨ z ⟩ , xyz≌zxy y z w , refl ⟧

xyzw≌wyzx : {A : Set}(x y z w : A) → P (⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩) (⟨ w ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ x ⟩)
xyzw≌wyzx x y z w = ⟨ x ⟩⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩ ≌ ⟨ w ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ x ⟩ with-⟦ ⟨ w ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ , ⟨⟩ , xyz≌zxy y z w , refl ⟧

xyzw≌xwzy : {A : Set}(x y z w : A) → P (⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩) (⟨ x ⟩ ⌢ ⟨ w ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ y ⟩)
xyzw≌xwzy x y z w = ⟨ x ⟩⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩ ≌ ⟨ x ⟩ ⌢ ⟨ w ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ y ⟩ with-⟦ ⟨⟩ , ⟨ w ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ y ⟩ , xyz≌zyx y z w , refl ⟧

xyzw≌wxzy : {A : Set}(x y z w : A) → P (⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩) (⟨ w ⟩ ⌢ ⟨ x ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ y ⟩)
xyzw≌wxzy x y z w = ⟨ x ⟩⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩ ≌ ⟨ w ⟩ ⌢ ⟨ x ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ y ⟩ with-⟦ ⟨ w ⟩ , ⟨ z ⟩ ⌢ ⟨ y ⟩ , xyz≌zyx y z w , refl ⟧

xyzw≌wzxy : {A : Set}(x y z w : A) → P (⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩) (⟨ w ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ x ⟩ ⌢ ⟨ y ⟩)
xyzw≌wzxy x y z w = ⟨ x ⟩⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩ ≌ ⟨ w ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ x ⟩ ⌢ ⟨ y ⟩ with-⟦ ⟨ w ⟩ ⌢ ⟨ z ⟩ , ⟨ y ⟩ , xyz≌zyx y z w , refl ⟧

xyzw≌wzyx : {A : Set}(x y z w : A) → P (⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩) (⟨ w ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ x ⟩)
xyzw≌wzyx x y z w = ⟨ x ⟩⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ w ⟩ ≌ ⟨ w ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ x ⟩ with-⟦ ⟨ w ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ y ⟩ , ⟨⟩ , xyz≌zyx y z w , refl ⟧

-- | Law I
reflexivity : {A : Set} (xs : List A) → P xs xs
reflexivity ⟨⟩ = ∅ refl
reflexivity (x ∷ xs) = ⟨ x ⟩⌢ xs ≌ ⟨⟩ ⌢ ⟨ x ⟩ ⌢ xs with-⟦ ⟨⟩ , xs , reflexivity xs , refl ⟧

-- | Law II
symmetricity : {A : Set} {xs ys : List A} → P xs ys → P ys xs
symmetricity {xs = xs} {ys} p = {!!}

-- | Law III
transitivity : {A : Set} {xs ys zs : List A} → P xs ys → P ys zs → P xs zs
transitivity {xs = xs} {ys} {zs} p q = {!!}

{--
-- | independent
ins : {A : Set}(x : A){xs ys : List A} → P xs ys → P (⟨ x ⟩ ⌢ xs) (⟨ x ⟩ ⌢ ys)
ins x {.⟨⟩} {.⟨⟩} (∅ refl) = ⟨ x ⟩⌢ ⟨⟩ ≌ x ∷ ⟨⟩ with-⟦ ⟨⟩ , ⟨⟩ , (∅ refl) , refl ⟧
ins x {.(x₁ ∷ s)} {.t} ⟨ x₁ ⟩⌢ s ≌ t with-⟦ u , v , P , p ⟧
  = ⟨ x ⟩⌢ x₁ ∷ s ≌ x ∷ t with-⟦ ⟨⟩ , t , ⟨ x₁ ⟩⌢ s ≌ t with-⟦ u , v , P , p ⟧ , refl ⟧


p⌢q≡⟨⟩⇒p≡⟨⟩∧q≡⟨⟩ : {A : Set}{p q : List A} → p ⌢ q ≡ ⟨⟩ → p ≡ ⟨⟩ ∧ q ≡ ⟨⟩
p⌢q≡⟨⟩⇒p≡⟨⟩∧q≡⟨⟩ {p = ⟨⟩} {.⟨⟩} refl = refl , refl
p⌢q≡⟨⟩⇒p≡⟨⟩∧q≡⟨⟩ {p = x ∷ p} {q} ()

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
