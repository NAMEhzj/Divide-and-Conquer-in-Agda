{-# OPTIONS --no-universe-polymorphism #-}

open import Relation.Binary.Core
open import Function


module Equivalence where

infixr 5 _⇔_

record _⇔_ (A B : Set) : Set where
   field to   : A → B
         from : B → A

infixr 3 _↔_

record _↔_ (A B : Set) : Set where
   field to   : A → B
         from : B → A
         from-to : ∀ a → from (to a) ≡ a
         to-from : ∀ b → to (from b) ≡ b




infixr 3 _=⟨_⟩_

_=⟨_⟩_ : {A : Set} (x : A) { y z : A} → x ≡ y → y ≡ z → x ≡ z
_=⟨_⟩_  _ refl refl = refl

=sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
=sym refl = refl


infixr 5 _under_

_under_ : {A B : Set} → {x y : A} → x ≡ y → (f : A → B) → f x ≡ f y
_under_ refl f = refl



infixr 4 _□=

_□= : {A : Set} → (x : A) → x ≡ x
_□= x = refl  



⇔sym : {A B : Set} → A ⇔ B → B ⇔ A  
⇔sym p = record {to   = _⇔_.from p ;
                 from = _⇔_.to  p }

infixr 4 _□⇔

_□⇔ : (A : Set) → A ⇔ A
_□⇔ A = record {to      = λ x → x;
                from    = λ x → x}

infixr 3 _⇔⟨_⟩_

_⇔⟨_⟩_ : (A : Set) {B C : Set} → A ⇔ B → B ⇔ C → A ⇔ C
_⇔⟨_⟩_ A {B} {C} AisB BisC = record {to   = (_⇔_.to   BisC) ∘ (_⇔_.to   AisB);
                                     from = (_⇔_.from AisB) ∘ (_⇔_.from BisC) }




↔sym : {A B : Set} → A ↔ B → B ↔ A  
↔sym p = record {to      = _↔_.from    p ;
                 from    = _↔_.to      p ;
                 from-to = _↔_.to-from p ;
                 to-from = _↔_.from-to p }

infixr 4 _□↔

_□↔ : (A : Set) → A ↔ A
_□↔ A = record {to      = λ x → x;
                from    = λ x → x;
                from-to = λ a → refl;
                to-from = λ b → refl}

infixr 3 _↔⟨_⟩_

_↔⟨_⟩_ : (A : Set) {B C : Set} → A ↔ B → B ↔ C → A ↔ C
_↔⟨_⟩_ A {B} {C} AisB BisC = record {to      = to₂   ∘ to₁   ;
                                     from    = from₁ ∘ from₂ ;
                                     from-to = λ a → (from₁ ∘ from₂ ∘ to₂ ∘ to₁) a =⟨ from-to₂ (to₁ a) under from₁ ⟩
                                                      from₁ (to₁ a)                =⟨ from-to₁ a ⟩
                                                      a □= ;
                                      to-from = λ c → (to₂ ∘ to₁ ∘ from₁ ∘ from₂) c =⟨ to-from₁ (from₂ c) under to₂ ⟩
                                                       to₂ (from₂ c)                =⟨ to-from₂ c ⟩
                                                       c □= } where
                                        to₁      = _↔_.to AisB
                                        to₂      = _↔_.to BisC
                                        from₁    = _↔_.from AisB
                                        from₂    = _↔_.from BisC
                                        from-to₁ = _↔_.from-to AisB
                                        from-to₂ = _↔_.from-to BisC
                                        to-from₁ = _↔_.to-from AisB
                                        to-from₂ = _↔_.to-from BisC
