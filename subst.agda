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
⟨⟩≡xs⌢ys⇒xs≡⟨⟩∧ys≡⟨⟩ : {A : Set}(xs ys : List A) → ⟨⟩ ≡ xs ⌢ ys → xs ≡ ⟨⟩ ∧ ys ≡ ⟨⟩
⟨⟩≡xs⌢ys⇒xs≡⟨⟩∧ys≡⟨⟩ xs ys = {!!}

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

-- | inverse constructor for Definition of P's
inverse : {A : Set}(x : A) (u v s : List A) → P (u ⌢ v) s → P (u ⌢ ⟨ x ⟩ ⌢ v) (⟨ x ⟩ ⌢ s)
inverse x ⟨⟩ v s p = ⟨ x ⟩⌢ v ≌ x ∷ s with-⟦ ⟨⟩ , s , p , refl ⟧
inverse x (x₁ ∷ u) v .(u₂ ⌢ x₁ ∷ v₂) ⟨ .x₁ ⟩⌢ .(u ⌢ v) ≌ .(u₂ ⌢ x₁ ∷ v₂) with-⟦ u₂ , v₂ , P₂ , refl ⟧
  = ⟨ x₁ ⟩⌢ u ⌢ x ∷ v ≌ x ∷ u₂ ⌢ x₁ ∷ v₂ with-⟦ x ∷ u₂ , v₂ , inverse x u v (u₂ ⌢ v₂) P₂ , refl ⟧

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
symmetricity {xs = .⟨⟩} {.⟨⟩} (∅ refl) = ∅ refl
symmetricity {xs = .(x ∷ s)} {.(u ⌢ x ∷ v)} ⟨ x ⟩⌢ s ≌ .(u ⌢ x ∷ v) with-⟦ u , v , P₁ , refl ⟧ = inverse x u v s (symmetricity P₁)

swap : {A : Set}(x y : A)(xs ys : List A) → P (⟨ x ⟩ ⌢ xs ⌢ ⟨ y ⟩ ⌢ ys) (⟨ y ⟩ ⌢ xs ⌢ ⟨ x ⟩ ⌢ ys)
swap x y xs ys = ⟨ x ⟩⌢ xs ⌢ ⟨ y ⟩ ⌢ ys ≌ ⟨ y ⟩ ⌢ xs ⌢ ⟨ x ⟩ ⌢ ys with-⟦ ⟨ y ⟩ ⌢ xs , ys , inverse y xs ys (xs ⌢ ys) (reflexivity (xs ⌢ ys)) , refl ⟧

test : {A : Set}(x y z : A)
  → P (⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩) (⟨ y ⟩ ⌢ ⟨ x ⟩ ⌢ ⟨ z ⟩)
  → P (⟨ y ⟩ ⌢ ⟨ x ⟩ ⌢ ⟨ z ⟩) (⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ x ⟩)
  → P (⟨ x ⟩ ⌢ ⟨ y ⟩ ⌢ ⟨ z ⟩) (⟨ y ⟩ ⌢ ⟨ z ⟩ ⌢ ⟨ x ⟩)
test x y z ⟨ .x ⟩⌢ .(y ∷ z ∷ ⟨⟩) ≌ .(y ∷ x ∷ z ∷ ⟨⟩) with-⟦ u , v , ⟨ .y ⟩⌢ .(z ∷ ⟨⟩) ≌ .(u ⌢ v) with-⟦ u₁ , v₁ , ⟨ .z ⟩⌢ .⟨⟩ ≌ .(u₁ ⌢ v₁) with-⟦ u₂ , v₂ , (∅ prf) , p₂ ⟧ , p₁ ⟧ , p ⟧ q = {!!}


-- | Law III
transitivity : {A : Set} {xs ys zs : List A} → P xs ys → P ys zs → P xs zs
transitivity {xs = .⟨⟩} {.⟨⟩} {zs} (∅ refl) q = q
transitivity {xs = .(x ∷ s)} {.⟨⟩} {.⟨⟩} ⟨ x ⟩⌢ s ≌ .⟨⟩ with-⟦ x₁ ⟧ (∅ refl) = ⊥-elim (¬P[x∷xs]⟨⟩ ⟨ x ⟩⌢ s ≌ ⟨⟩ with-⟦ x₁ ⟧)
transitivity {xs = .(x ∷ s)} {.(x₁ ∷ s₁)} {.t} ⟨ x ⟩⌢ s ≌ .(x₁ ∷ s₁) with-⟦ u₁ , v₁ , P₁ , p₁ ⟧ ⟨ x₁ ⟩⌢ s₁ ≌ t with-⟦ u₂ , v₂ , P₂ , p₂ ⟧ = {!!}

transposition : {A : Set}(i j : A)(xs ys zs : List A) → P (xs ⌢ ⟨ i ⟩ ⌢ ys ⌢ ⟨ j ⟩ ⌢ zs) (xs ⌢ ⟨ j ⟩ ⌢ ys ⌢ ⟨ i ⟩ ⌢ zs)
transposition i j ⟨⟩ ys zs
  = ⟨ i ⟩⌢ ys ⌢ ⟨ j ⟩ ⌢ zs ≌ ⟨ j ⟩ ⌢ ys ⌢ ⟨ i ⟩ ⌢ zs with-⟦ ⟨ j ⟩ ⌢ ys , zs , inverse j ys zs (ys ⌢ zs) (reflexivity (ys ⌢ zs)) , refl ⟧
transposition i j (x ∷ xs) ys zs with swap x i xs (ys ⌢ ⟨ j ⟩ ⌢ zs) | swap i j (xs ⌢ ⟨ x ⟩ ⌢ ys) zs | swap j x xs (ys ⌢ ⟨ i ⟩ ⌢ zs)
... | ⟨ .x ⟩⌢ .(xs ⌢ ⟨ i ⟩ ⌢ ys ⌢ ⟨ j ⟩ ⌢ zs) ≌ .(⟨ i ⟩ ⌢ xs ⌢ ⟨ x ⟩ ⌢ ys ⌢ ⟨ j ⟩ ⌢ zs) with-⟦ u₁ , v₁ , P₁ , p₁ ⟧
    | ⟨ .i ⟩⌢ .((xs ⌢ ⟨ x ⟩ ⌢ ys) ⌢ ⟨ j ⟩ ⌢ zs) ≌ .(⟨ j ⟩ ⌢ (xs ⌢ ⟨ x ⟩ ⌢ ys) ⌢ ⟨ i ⟩ ⌢ zs) with-⟦ u₂ , v₂ , P₂ , p₂ ⟧
    | ⟨ .j ⟩⌢ .(xs ⌢ ⟨ x ⟩ ⌢ ys ⌢ ⟨ i ⟩ ⌢ zs) ≌ .(⟨ x ⟩ ⌢ xs ⌢ ⟨ j ⟩ ⌢ ys ⌢ ⟨ i ⟩ ⌢ zs) with-⟦ u₃ , v₃ , P₃ , p₃ ⟧
    = {!!}
