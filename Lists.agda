{-# OPTIONS --no-universe-polymorphism #-}
open import Induction.WellFounded as WF
open import Induction.Nat
open import Relation.Binary.Core hiding (Total)
open import Relation.Unary as U using (Decidable)
open import Relation.Nullary
open import Function using (_on_)
open import Data.Nat
import Level as L using (zero)
open import Data.List

open import BagEquality


module Lists where

infixr 8 _<l_

_<l_ : {A : Set} → Rel (List A) L.zero
_<l_ = Data.Nat._<′_ on length



<l-wellFounded : {A : Set} → Well-founded (_<l_ {A = A})
<l-wellFounded = newWf where
          module InverseOfProj = WF.Inverse-image length  
          newWf = InverseOfProj.well-founded <′-well-founded
                                        

data Ordered  : {A : Set} → Rel A _ → List A → Set where
                 NilIsOrd : {A : Set} {LEQ : Rel A _} → Ordered LEQ []
                 SingleIsOrd : {A : Set} {LEQ : Rel A _} {x : A} → Ordered LEQ [ x ]
                 HeadTailOrd : {A : Set} {LEQ : Rel A _} {x y : A} {zs : List A} → LEQ x y → Ordered LEQ (y ∷ zs) → Ordered LEQ (x ∷ (y ∷ zs))


cons-Order-cong : {A : Set} → {LEQ : Rel A L.zero} → {x : A} → {ys : List A} → (∀ z → z ∈ ys → LEQ x z) → Ordered LEQ ys → Ordered LEQ (x ∷ ys)
cons-Order-cong {A} {LEQ} {y} {[]} _ _ = SingleIsOrd
cons-Order-cong {A} {LEQ} {x} {y ∷ ys} xLEQ ord-ys = HeadTailOrd (xLEQ y (inj₁ refl)) ord-ys

++-Order-cong : {A : Set} {LEQ : Rel A L.zero} → {xs ys : List A} {y : A} → (∀ z → z ∈ xs → LEQ z y) → Ordered LEQ xs → Ordered LEQ (y ∷ ys) → Ordered LEQ (xs ++ (y ∷ ys))
++-Order-cong {A} {LEQ} {[]}             {ys} {y} _        _                          ord-y∷ys = ord-y∷ys
++-Order-cong {A} {LEQ} {x ∷ []}         {ys} {y} yGEQ     _                          ord-y∷ys = HeadTailOrd (yGEQ x (inj₁ refl)) ord-y∷ys
++-Order-cong {A} {LEQ} {x₁ ∷ (x₂ ∷ xs)} {ys} {y} yGEQ (HeadTailOrd x₁LEQx₂ ord-x∷xs) ord-y∷ys = HeadTailOrd x₁LEQx₂ (++-Order-cong (λ z zIn → yGEQ z (inj₂ zIn)) ord-x∷xs ord-y∷ys)


Total : {A : Set} → Rel A L.zero → Set
Total {A} LEQ = (x y : A) → LEQ x y ⊕ LEQ y x


data ListPrimitive : {A : Set} → List A → Set where
            NilIsPrim : ∀{A} → ListPrimitive {A = A} []

consIsNotPrim : {A : Set} → {x : A} → {xs : List A} → ¬ ListPrimitive (x ∷ xs)
consIsNotPrim ()

primDec : {A : Set} → U.Decidable (ListPrimitive {A = A})
primDec []       = yes NilIsPrim
primDec (x ∷ xs) = no consIsNotPrim

data ListPrimitive2 : {A : Set} → List A → Set where
           NilIsPrim2 : ∀{A} → ListPrimitive2 {A = A} []
           SingleIsPrim2 : ∀{A} {x : A} → ListPrimitive2 (x ∷ [])

consConsIsNotPrim2 : {A : Set} → {x y : A} → {zs : List A} → ¬ ListPrimitive2 (x ∷ (y ∷ zs))
consConsIsNotPrim2 () 

prim2Dec : {A : Set} → U.Decidable (ListPrimitive2 {A = A})
prim2Dec [] = yes NilIsPrim2
prim2Dec (x ∷ []) = yes SingleIsPrim2
prim2Dec (x ∷ (y ∷ zs)) = no consConsIsNotPrim2
