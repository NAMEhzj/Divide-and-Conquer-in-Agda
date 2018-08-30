
{-# OPTIONS --no-universe-polymorphism #-}
open import Data.Product hiding (map)
open import Relation.Binary.Core hiding (Total)
open import Relation.Nullary
open import Data.Nat
import Level as L using (zero)
open import Data.List
open import Data.Unit using (⊤)
open import Data.Empty

open import DivideEtImpera
open import Equivalence
open import BagEquality
open import Lists

module Quicksort where


splitWith : {A : Set} {P Q : A → Set} → (∀ x → P x ⊕ Q x) → List A → List A × List A
splitWith _ []   = ([] , [])
splitWith decPQ (x ∷ xs) with (decPQ x)
splitWith decPQ (x ∷ xs) | (inj₁ _) = (x ∷ (proj₁ res), proj₂ res) where
                                                        res = splitWith decPQ xs
splitWith decPQ (x ∷ xs) | (inj₂ _) = (proj₁ res , x ∷ (proj₂ res)) where
                                                        res = splitWith decPQ xs


splitWithProp1 : {A : Set} {P Q : A → Set} → (decPQ : ∀ x → P x ⊕ Q x) → (xs : List A) → (z : A) → z ∈ proj₁ (splitWith decPQ xs) → P z
splitWithProp1 decPQ [] z zIn1 = ⊥-elim zIn1
splitWithProp1 decPQ (x ∷ xs) z zIn with (decPQ x)
splitWithProp1 decPQ (x ∷ xs) .x (inj₁ refl) | (inj₁ pfP) = pfP 
splitWithProp1 decPQ (x ∷ xs) z  (inj₂ zIn)  | (inj₁ _  ) = splitWithProp1 decPQ xs z zIn
splitWithProp1 decPQ (x ∷ xs) z  zIn         | (inj₂ _  ) = splitWithProp1 decPQ xs z zIn

splitWithProp2 : {A : Set} {P Q : A → Set} → (decPQ : ∀ x → P x ⊕ Q x) → (xs : List A) → (z : A) → z ∈ proj₂ (splitWith decPQ xs) → Q z
splitWithProp2 decPQ [] z zIn1 = ⊥-elim zIn1
splitWithProp2 decPQ (x ∷ xs) z zIn with (decPQ x)
splitWithProp2 decPQ (x ∷ xs) .x (inj₁ refl) | (inj₂ pfQ) = pfQ 
splitWithProp2 decPQ (x ∷ xs) z  (inj₂ zIn)  | (inj₂ _  ) = splitWithProp2 decPQ xs z zIn
splitWithProp2 decPQ (x ∷ xs) z  zIn         | (inj₁ _  ) = splitWithProp2 decPQ xs z zIn

×-join : {A B C : Set} → (pair : A × B) → (op : A → B → C) → C
×-join (a , b) op = op a b



splitWith-cong : {A : Set} {P Q : A → Set} → (decPQ : ∀ x → P x ⊕ Q x) → (xs : List A) → (proj₁ (splitWith decPQ xs)) ++ (proj₂ (splitWith decPQ xs)) ≈ xs
splitWith-cong _ [] z = ⊥ □↔
splitWith-cong decPQ (x ∷ xs) z with (decPQ x)
splitWith-cong decPQ (x ∷ xs) z | (inj₁ _) = let (res1 , res2) = splitWith decPQ xs
                                                   in (z ≡ x) ⊕ Any (z ≡_) (res1 ++ res2) ↔⟨ ⊕-cong ((z ≡ x) □↔) (splitWith-cong decPQ xs z) ⟩
                                                      (z ≡ x) ⊕ Any (z ≡_) xs □↔  
splitWith-cong decPQ (x ∷ xs) z | (inj₂ _) = let (res1 , res2) = splitWith decPQ xs
                                                   in Any (z ≡_) (res1 ++ x ∷ res2) ↔⟨ ++-comm res1 (x ∷ res2) z ⟩
                                                      (z ≡ x) ⊕ Any (z ≡_) (res2 ++ res1) ↔⟨ ⊕-cong ((z ≡ x) □↔) (++-comm res2 res1 z) ⟩
                                                      (z ≡ x) ⊕ Any (z ≡_) (res1 ++ res2) ↔⟨ ⊕-cong ((z ≡ x) □↔) (splitWith-cong decPQ xs z) ⟩
                                                      (z ≡ x) ⊕ Any (z ≡_) xs □↔

≤′-suc : {n m : ℕ} → n ≤′ m → suc n ≤′ suc m
≤′-suc ≤′-refl = ≤′-refl
≤′-suc (≤′-step pf) = ≤′-step (≤′-suc pf)


splitWith-length1 : {A : Set} {P Q : A → Set} → (decPQ : ∀ x → P x ⊕ Q x) → (xs : List A) → length (proj₁ (splitWith decPQ xs)) ≤′ length xs
splitWith-length1 _ [] = ≤′-refl
splitWith-length1 decPQ (x ∷ xs) with (decPQ x)
splitWith-length1 decPQ (x ∷ xs) | (inj₁ _) = ≤′-suc (splitWith-length1 decPQ xs)
splitWith-length1 decPQ (x ∷ xs) | (inj₂ _) = ≤′-step (splitWith-length1 decPQ xs)


splitWith-length2 : {A : Set} {P Q : A → Set} → (decPQ : ∀ x → P x ⊕ Q x) → (xs : List A) → length (proj₂ (splitWith decPQ xs)) ≤′ length xs
splitWith-length2 _ [] = ≤′-refl
splitWith-length2 decPQ (x ∷ xs) with (decPQ x)
splitWith-length2 decPQ (x ∷ xs) | (inj₁ _) = ≤′-step (splitWith-length2 decPQ xs)
splitWith-length2 decPQ (x ∷ xs) | (inj₂ _) = ≤′-suc (splitWith-length2 decPQ xs)








qs-DecompCond : {A : Set} → Rel A L.zero → List A → (A × List A × List A) → Set
qs-DecompCond LEQ xs (piv , ys , zs) = (piv ∷ (ys ++ zs) ≈ xs) × (∀ y → y ∈ ys → LEQ y piv) × (∀ z → z ∈ zs → LEQ piv z)


qs-InputCond : {A : Set} → List A → Set
qs-InputCond x = ⊤

qs-OutputCond : {A : Set} → Rel A L.zero → List A → List A → Set
qs-OutputCond LEQ xs ys = ys ≈ xs × Ordered LEQ ys

qs-G-InputCond : {A : Set} → A → Set
qs-G-InputCond x = ⊤

qs-G-OutputCond : {A : Set} → A → A → Set
qs-G-OutputCond x y = x ≡ y

qs-CompCond : {A : Set} → (A × List A × List A) → List A → Set
qs-CompCond (piv , xs , ys) zs = xs ++ piv ∷ ys ≡ zs

qs-InductionLemma : {A : Set} → (LEQ : Rel A L.zero) → ∀{x₀ x₁ x₂ x₃ z₀ z₁ z₂ z₃} → qs-DecompCond LEQ x₀ (x₁ , x₂ , x₃ ) → qs-G-OutputCond x₁ z₁  →
                             qs-OutputCond LEQ x₂ z₂ → qs-OutputCond LEQ x₃ z₃ → qs-CompCond (z₁ , z₂ , z₃) z₀ → qs-OutputCond LEQ x₀ z₀
qs-InductionLemma LEQ {xs} {piv} {ys₁} {ys₂} {ws} {.piv} {zs₁} {zs₂} (piv∷ys₁++ys₂≈xs , ltPiv , gtPiv) refl (zs₁≈ys₁ , ord₁) (zs₂≈ys₂ , ord₂) refl
                                         = (λ x → x ∈ (zs₁ ++ piv ∷ zs₂) ↔⟨ ++-comm zs₁ (piv ∷ zs₂) x ⟩
                                                  (x ∈ ((piv ∷ zs₂) ++ zs₁)) ↔⟨ Any-++ (λ z → x ≡ z) (piv ∷ zs₂) zs₁ ⟩
                                                  ((x ≡ piv) ⊕ x ∈ zs₂) ⊕ x ∈ zs₁  ↔⟨ ↔sym ⊕-assoc  ⟩
                                                  (x ≡ piv) ⊕ (x ∈ zs₂ ⊕ x ∈ zs₁) ↔⟨ ⊕-cong ((x ≡ piv) □↔) (⊕-cong (zs₂≈ys₂ x) (zs₁≈ys₁ x)) ⟩
                                                  (x ≡ piv) ⊕ (x ∈ ys₂ ⊕ x ∈ ys₁) ↔⟨ ⊕-cong ((x ≡ piv) □↔) ⊕-comm ⟩
                                                  (x ≡ piv) ⊕ (x ∈ ys₁ ⊕ x ∈ ys₂) ↔⟨ ⊕-cong ((x ≡ piv) □↔) (↔sym (Any-++ (λ z → x ≡ z) ys₁ ys₂)) ⟩
                                                  x ∈ (piv ∷ (ys₁ ++ ys₂)) ↔⟨ piv∷ys₁++ys₂≈xs x ⟩
                                                  x ∈ xs □↔) ,
                                                       ++-Order-cong (λ x x∈zs₁ → ltPiv x (_↔_.to (zs₁≈ys₁ x) x∈zs₁)) ord₁
                                                     (cons-Order-cong (λ x x∈zs₂ → gtPiv x (_↔_.to (zs₂≈ys₂ x) x∈zs₂)) ord₂)



qs-Decomp : {A : Set} → {LEQ : Rel A L.zero} → Total LEQ → (xs : List A) → ⊤ → ¬ ListPrimitive xs → Σ (A × List A × List A)
                                                                λ y → qs-G-InputCond (proj₁ y) × (qs-InputCond (proj₁ (proj₂ y))) × (qs-InputCond (proj₂ (proj₂ y))) ×
                                                                      ((proj₁ (proj₂ y)) <l xs) × ((proj₂ (proj₂ y)) <l xs) × (qs-DecompCond LEQ xs y)
qs-Decomp total [] _ notPrim = ⊥-elim (notPrim (NilIsPrim))
qs-Decomp total (x ∷ xs) _ _ = ( x , splitWith (λ y → total y x) xs) ,  (⊤.tt , ⊤.tt , ⊤.tt , ≤′-suc (splitWith-length1 (λ y → total y x) xs) , ≤′-suc (splitWith-length2 (λ y → total y x) xs) ,
                                                                             ((λ z → (z ≡ x) ⊕ z ∈ (proj₁ (splitWith (λ y → total y x) xs) ++ proj₂ (splitWith (λ y → total y x) xs))
                                                                                                  ↔⟨ ⊕-cong ((z ≡ x) □↔) (splitWith-cong (λ y → total y x) xs z) ⟩
                                                                                     (z ≡ x) ⊕ z ∈ xs □↔) ,
                                                                              splitWithProp1 (λ y → total y x) xs ,
                                                                              splitWithProp2 (λ y → total y x) xs)) 

qs-G : {A : Set} → (x : A) → ⊤ → Σ A (qs-G-OutputCond x)
qs-G x _ = (x , refl)

qs-Comp : {A : Set} → (y : A × (List A × List A)) → Σ (List A) (qs-CompCond y) 
qs-Comp (piv , xs , ys) = (xs ++ piv ∷ ys , refl)

qs-DirSolve : {A : Set} → (LEQ : Rel A L.zero) → (xs : List A) → ⊤ → ListPrimitive xs → Σ (List A) (qs-OutputCond LEQ xs)
qs-DirSolve _ []      _ _    = ([] , (λ z → z ∈ [] □↔) , NilIsOrd)
qs-DirSolve _ (_ ∷ _) _ prim = ⊥-elim (consIsNotPrim prim)

quicksort : {A : Set} → {LEQ : Rel A L.zero} → Total LEQ → (xs : List A) → Σ (List A) (λ ys → ys ≈ xs × Ordered LEQ ys)
quicksort {LEQ = LEQ} total xs = makeD&C2 <l-wellFounded
                                          primDec
                                          (qs-Decomp total)
                                          qs-Comp
                                          qs-G
                                          (qs-DirSolve LEQ)
                                          (qs-InductionLemma LEQ)
                                          xs ⊤.tt


_≤_-total : Total _≤_
_≤_-total zero    n       = inj₁ z≤n
_≤_-total n       zero    = inj₂ z≤n
_≤_-total (suc n) (suc m) with (_≤_-total n m)
_≤_-total (suc n) (suc m) | (inj₁ n≤m) = inj₁ (s≤s n≤m)
_≤_-total (suc n) (suc m) | (inj₂ m≤n) = inj₂ (s≤s m≤n)


nat-quicksort = quicksort _≤_-total
