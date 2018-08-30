{-# OPTIONS --no-universe-polymorphism #-}

open import Data.List
open import Data.Product
open import Data.Unit hiding (_≤_)
open import Data.Nat
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.Core hiding (Total)
import Level as L using (zero)

open import Lists
open import BagEquality
open import Equivalence
open import DivideEtImpera

module Mergesort where


merge : {A : Set} → {_<_ : Rel A L.zero} → Total _<_ → List A → List A → List A
merge _ [] ys = ys
merge _ (x ∷ xs) [] = (x ∷ xs)
merge total (x ∷ xs) (y ∷ ys) with (total x y)
merge total (x ∷ xs) (y ∷ ys) | (inj₁ x≤y) = x ∷ merge total xs (y ∷ ys)
merge total (x ∷ xs) (y ∷ ys) | (inj₂ y≤x) = y ∷ merge total (x ∷ xs) ys


merge-cong : {A : Set} → {_<_ : Rel A L.zero} → (total : Total _<_) → (xs ys : List A) → merge total xs ys ≈ (xs ++ ys)
merge-cong _ [] ys = λ z → z ∈ ys □↔
merge-cong _ (x ∷ xs) [] = λ z → z ∈ (x ∷ xs) ↔⟨ ++-comm [] (x ∷ xs) z ⟩
                                       z ∈ ((x ∷ xs) ++ [])  □↔
merge-cong total (x ∷ xs) (y ∷ ys) with (total x y)
merge-cong total (x ∷ xs) (y ∷ ys) | (inj₁ x≤y) = λ z →
               (z ≡ x) ⊕ z ∈ merge total xs (y ∷ ys)  ↔⟨ ⊕-cong ((z ≡ x) □↔) (merge-cong total xs (y ∷ ys) z) ⟩
               (z ≡ x) ⊕ z ∈ (xs ++ (y ∷ ys)) □↔
                                                           
merge-cong total (x ∷ xs) (y ∷ ys) | (inj₂ y≤x) = λ z →
               (z ≡ y) ⊕ z ∈ merge total (x ∷ xs) ys  ↔⟨ ⊕-cong ((z ≡ y) □↔) (merge-cong total (x ∷ xs) ys z) ⟩
               (z ≡ y) ⊕ z ∈ ((x ∷ xs) ++ ys)         ↔⟨ ⊕-cong ((z ≡ y) □↔) (++-comm (x ∷ xs) ys z) ⟩
               (z ≡ y) ⊕ z ∈ (ys ++ (x ∷ xs))         ↔⟨ ++-comm (y ∷ ys) (x ∷ xs) z ⟩
               z ∈ ((x ∷ xs) ++ (y ∷ ys)) □↔ 

SmallerThanHead : {A : Set} → Rel A L.zero → A → List A → Set
SmallerThanHead _ x [] = ⊤
SmallerThanHead _<_ x (y ∷ ys) = _<_ x y 

ord : {A : Set} → {_<_ : Rel A L.zero} → {x : A} → {xs : List A} → SmallerThanHead _<_ x xs →  Ordered _<_ xs → Ordered _<_ (x ∷ xs)
ord {xs = []} _ _ = SingleIsOrd
ord {xs = (y ∷ ys)} x≤y ordXs = HeadTailOrd x≤y ordXs



merge-order : {A : Set} → {_<_ : Rel A L.zero} → (total : Total _<_) → (xs ys : List A)
                               → Ordered _<_ xs → Ordered _<_ ys → Ordered _<_ (merge total xs ys)
merge-order _ []        ys _ ysOrd = ysOrd
merge-order _ (x ∷ xs) [] xsOrd _ = xsOrd
merge-order total (x ∷ xs) (y ∷ ys) _ _  with (total x y)
merge-order total (x ∷ xs) (y ∷ ys) _ _     | (inj₁ x≤y) with xs
merge-order total (x ∷ xs) (y ∷ ys) _ ysOrd | (inj₁ x≤y) | [] = HeadTailOrd x≤y ysOrd
merge-order {_<_ = _<_} total (x ∷ xs) (y ∷ ys) (HeadTailOrd x≤x₂ xsOrd)  ysOrd | (inj₁ x≤y) | (x₂ ∷ xs₂)
                      = ord x≤z (merge-order total (x₂ ∷ xs₂) (y ∷ ys) xsOrd ysOrd) where
                             x≤z : SmallerThanHead _<_ x (merge total (x₂ ∷ xs₂) (y ∷ ys))
                             x≤z with (total x₂ y)
                             x≤z | (inj₁ _) = x≤x₂
                             x≤z | (inj₂ _) = x≤y
merge-order total (x ∷ xs) (y ∷ ys) _ _     | (inj₂ y≤x) with ys
merge-order total (x ∷ xs) (y ∷ ys) xsOrd _ | (inj₂ y≤x) | [] = HeadTailOrd y≤x xsOrd
merge-order {_<_ = _<_} total (x ∷ xs) (y ∷ ys) xsOrd (HeadTailOrd y≤y₂ ysOrd) | (inj₂ y≤x) | (y₂ ∷ ys₂)
                      = ord y≤z (merge-order total (x ∷ xs) (y₂ ∷ ys₂) xsOrd ysOrd) where
                               y≤z : SmallerThanHead _<_ y (merge total (x ∷ xs) (y₂ ∷ ys₂))
                               y≤z with (total x y₂)
                               y≤z | (inj₁ _) = y≤x
                               y≤z | (inj₂ _) = y≤y₂


minus : ℕ → ℕ → ℕ
minus n zero          = n
minus zero (suc m)    = zero
minus (suc n) (suc m) = minus n m

minus-suc : {n m : ℕ} → m ≤ n → minus (suc n) m ≡ suc (minus n m)
minus-suc z≤n      = refl
minus-suc (s≤s pf) = minus-suc pf 

bisect : {A : Set} → List A → (List A × List A)
bisect xs = splitAt ⌊ length xs /2⌋ xs


splitAtLen1 : {A : Set} →  (n : ℕ) → (xs : List A) → n ≤ (length xs) → length (proj₁ (splitAt n xs)) ≡ n
splitAtLen1 zero xs _ = refl 
splitAtLen1 (suc n) [] ()  
splitAtLen1 (suc n) (x ∷ xs) (s≤s pf) = suc (length (proj₁ (splitAt n xs))) =⟨ splitAtLen1 n xs pf under suc ⟩
                                        suc n □= 

splitAtLen2 : {A : Set} →  (n : ℕ) → (xs : List A) → length (proj₂ (splitAt n xs)) ≡ minus (length xs) n 
splitAtLen2 zero xs = refl
splitAtLen2 (suc n) [] = refl
splitAtLen2 (suc n) (x ∷ xs) = length (proj₂ (splitAt n xs)) =⟨ splitAtLen2 n xs ⟩
                                minus (length xs) n □=


s≤′s : {n m : ℕ} → n ≤′ m → suc n ≤′ suc m
s≤′s ≤′-refl      = ≤′-refl
s≤′s (≤′-step pf) = ≤′-step (s≤′s pf)

lte-cong : {n m : ℕ} → (n ≤ m) ⇔ (n ≤′ m)
lte-cong = record { to   = to' ;
                    from = from' } where
                            to' : {n m : ℕ} → n ≤ m → n ≤′ m
                            to' {m = zero}  z≤n = ≤′-refl
                            to' {m = suc m} z≤n = ≤′-step (to' z≤n)
                            to' (s≤s pf) = s≤′s (to' pf)
                            from' : {n m : ℕ} → n ≤′ m → n ≤ m
                            from' {zero} ≤′-refl = z≤n
                            from' {suc n} ≤′-refl = s≤s (from' ≤′-refl)
                            from' (≤′-step pf) = ≤-step (from' pf) where
                                   ≤-step : {n m : ℕ} → n ≤ m → n ≤ (suc m)
                                   ≤-step z≤n = z≤n
                                   ≤-step (s≤s pf) = s≤s (≤-step pf) 



eq-rel-cong : {A : Set} → {rel : Rel A L.zero} →  {x y z : A} → x ≡ y → rel y z → rel x z
eq-rel-cong refl pf = pf 

halfLte1 : (n : ℕ) → ⌊ n /2⌋ ≤′ n
halfLte1 zero          = ≤′-refl
halfLte1 (suc zero)    = ≤′-step ≤′-refl
halfLte1 (suc (suc n)) = ≤′-step (s≤′s (halfLte1 n))

halfLt1 : (n : ℕ) → ⌊ (suc (suc n)) /2⌋ <′ (suc (suc n))
halfLt1 n = s≤′s (s≤′s (halfLte1 n))

halfLte2 : (n : ℕ) → (minus n ⌊ n /2⌋) ≤′ n
halfLte2 zero          = ≤′-refl
halfLte2 (suc zero)    = ≤′-refl
halfLte2 (suc (suc n)) = ≤′-step (eq-rel-cong {rel = _≤′_} {x = minus (suc n) ⌊ n /2⌋} {y = suc (minus n ⌊ n /2⌋)}
                          (minus-suc (_⇔_.from lte-cong (halfLte1 n))) (s≤′s (halfLte2 n)))

halfLt2 : (n : ℕ) → (minus (suc (suc n)) ⌊ (suc (suc n)) /2⌋) <′ (suc (suc n))
halfLt2 n = s≤′s (eq-rel-cong {rel = _≤′_} {x = minus (suc n) ⌊ n /2⌋} {y = suc (minus n ⌊ n /2⌋)}
                          (minus-suc (_⇔_.from lte-cong (halfLte1 n))) (s≤′s (halfLte2 n)))

bisectPf1 : {A : Set} → (x y : A) → (zs : List A) → proj₁ (bisect (x ∷ y ∷ zs)) <l (x ∷ y ∷ zs)
bisectPf1 x y zs = eq-rel-cong {rel = _<′_} 
        (splitAtLen1 ⌊ (suc (suc (length zs))) /2⌋ (x ∷ y ∷ zs) (_⇔_.from lte-cong (halfLte1 (suc (suc (length zs))))))
                   (halfLt1 (length zs))


bisectPf2 : {A : Set} → (x y : A) → (zs : List A) → proj₂ (bisect (x ∷ y ∷ zs)) <l (x ∷ y ∷ zs)
bisectPf2 x y zs = eq-rel-cong {rel = _<′_} 
        (splitAtLen2 ⌊ (suc (suc (length zs))) /2⌋ (x ∷ y ∷ zs))
                   (halfLt2 (length zs))

splitAt-cong : {A : Set} → (n : ℕ) → (xs : List A) → proj₁ (splitAt n xs) ++ proj₂ (splitAt n xs) ≈ xs
splitAt-cong zero xs           z = z ∈ xs □↔
splitAt-cong (suc n) []        z = ⊥ □↔
splitAt-cong (suc n) (x ∷ xs) z = (z ≡ x) ⊕ z ∈ (proj₁ (splitAt n xs) ++ proj₂ (splitAt n xs))
                                             ↔⟨ ⊕-cong ((z ≡ x) □↔) (splitAt-cong n xs z) ⟩
                                   (z ≡ x) ⊕ z ∈ xs □↔ 


ms-inputCond : {A : Set} → List A → Set
ms-inputCond _ = ⊤

ms-decompCond : {A : Set} → List A → (⊤ × List A × List A) → Set
ms-decompCond xs (_ , ys , zs ) = ys ++ zs ≈ xs

ms-compCond : {A : Set} → Rel A L.zero → (⊤ × List A × List A) → List A → Set
ms-compCond rel (_ , xs , ys ) zs = zs ≈ xs ++ ys × (Ordered rel xs → Ordered rel ys → Ordered rel zs)

ms-outputCond : {A : Set} → Rel A L.zero → List A → List A → Set
ms-outputCond rel xs zs = (zs ≈ xs) × Ordered rel zs

ms-G : ⊤ → ⊤ → Σ ⊤ (λ x → ⊤)
ms-G _ _ = (⊤.tt , ⊤.tt)

ms-decomp : {A : Set} → (xs : List A) → ⊤ → ¬ ListPrimitive2 xs → Σ (⊤ × List A × List A)
              (λ z → ⊤ × ⊤ × ⊤ × (proj₁ (proj₂ z) <l xs) × (proj₂ (proj₂ z) <l xs) × ms-decompCond xs z)
ms-decomp [] _ notPrim = ⊥-elim (notPrim NilIsPrim2)
ms-decomp (x ∷ []) _ notPrim = ⊥-elim (notPrim SingleIsPrim2)
ms-decomp (x ∷ y ∷ zs)  _ _ = (⊤.tt , bisect (x ∷ y ∷ zs)) , (⊤.tt , ⊤.tt , ⊤.tt ,
                                                        bisectPf1 x y zs ,
                                                        bisectPf2 x y zs ,
                                                        splitAt-cong ⌊ (suc (suc (length zs))) /2⌋ (x ∷ y ∷ zs))

ms-comp : {A : Set} → {rel : Rel A L.zero} → Total rel → (z : (⊤ × List A × List A)) → Σ (List A) (ms-compCond rel z)
ms-comp total ( _ , xs , ys) = (merge total xs ys) , (merge-cong total xs ys , merge-order total xs ys)

ms-dirSolve : {A : Set} → (rel : Rel A L.zero) → (xs : List A) → ⊤ → ListPrimitive2 xs → Σ (List A) (ms-outputCond rel xs)
ms-dirSolve _ []             _ _    = [] , ((λ z → ⊥ □↔) , NilIsOrd)
ms-dirSolve _ (x ∷ [])      _ _    = (x ∷ []) , ((λ z → z ∈ (x ∷ []) □↔) , SingleIsOrd)
ms-dirSolve _ (x ∷ y ∷ zs) _ prim = ⊥-elim (consConsIsNotPrim2 prim)

ms-lemma : {A : Set} → (rel : Rel A L.zero) → ∀{xs ys₁ ys₂ zs₁ zs₂ ws} → ms-decompCond xs (⊤.tt , ys₁ , ys₂)
                           → ⊤ → ms-outputCond rel ys₁ zs₁ → ms-outputCond rel ys₂ zs₂
                              → ms-compCond rel (⊤.tt , zs₁ , zs₂) ws → ms-outputCond rel xs ws
ms-lemma rel {xs} {ys₁} {ys₂} {zs₁} {zs₂} {ws} ys₁++ys₂≈xs _ ( ys₁≈zs₁ , zs₁Ord ) ( ys₂≈zs₂ , zs₂Ord ) ( ws≈zs₁++zs₂ , compOrd)
                 = (λ z → z ∈ ws              ↔⟨ ws≈zs₁++zs₂ z ⟩
                           z ∈ (zs₁ ++ zs₂)    ↔⟨ Any-++ (z ≡_) zs₁ zs₂ ⟩
                           z ∈ zs₁ ⊕ z ∈ zs₂ ↔⟨ ⊕-cong (ys₁≈zs₁ z) (ys₂≈zs₂ z) ⟩
                           z ∈ ys₁ ⊕ z ∈ ys₂ ↔⟨ ↔sym (Any-++ (z ≡_) ys₁ ys₂) ⟩
                           z ∈ (ys₁ ++ ys₂)    ↔⟨ ys₁++ys₂≈xs z ⟩
                           z ∈ xs □↔) ,
                   compOrd zs₁Ord zs₂Ord


mergesort : {A : Set} → {rel : Rel A L.zero} → Total rel → (xs : List A) → Σ (List A) (λ zs → (zs ≈ xs) × Ordered rel zs)
mergesort {rel = rel} total xs = makeD&C2 <l-wellFounded
                                          prim2Dec
                                          ms-decomp
                                          (ms-comp total)
                                          ms-G
                                          (ms-dirSolve rel)
                                          (ms-lemma rel)
                                          xs ⊤.tt

