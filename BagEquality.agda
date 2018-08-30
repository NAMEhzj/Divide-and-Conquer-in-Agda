
{-# OPTIONS --no-universe-polymorphism #-}
open import Data.Product hiding (map)
open import Relation.Binary.Core
open import Function
open import Data.List
open import Data.Unit using (⊤)
open import Data.Empty

open import Equivalence


module BagEquality where

infixr 5 _⊕_

data _⊕_ (A B : Set) : Set where
             inj₁ : A → A ⊕ B
             inj₂ : B → A ⊕ B

uninhabited : {A : Set} → (A → ⊥) → A ↔ ⊥
uninhabited pf = record {to = pf;
                         from = ⊥-elim;
                         from-to = λ a → ⊥-elim (pf a);
                         to-from = λ false → ⊥-elim false} 


Any : {A : Set} → (A → Set) → List A → Set
Any P []       = ⊥
Any P (x ∷ xs) = P x ⊕ Any P xs

infix 6 _∈_
_∈_ : {A : Set} → A → List A → Set
z ∈ xs = Any (λ y → z ≡ y) xs



infixr 4 _≈_

_≈_ : {A : Set} → List A → List A → Set
xs ≈ ys = ∀ z → z ∈ xs ↔ z ∈ ys





infix 10 _>>=_

_>>=_ : {A B : Set} → List A → (A → List B) → List B
xs >>= f = concat (map f xs)


⊕-left-identity : {A : Set} → ⊥ ⊕ A ↔ A
⊕-left-identity {A} = record { to      = to'        ;
                               from    = inj₂       ;
                               from-to = from-to'   ;
                               to-from = λ a → refl } where
                                    to' : ⊥ ⊕ A → A
                                    to' (inj₁ b) = ⊥-elim b
                                    to' (inj₂ a) = a
                                    from-to' : (s : ⊥ ⊕ A) → inj₂ (to' s) ≡ s
                                    from-to' (inj₁ b) = ⊥-elim b
                                    from-to' (inj₂ a) = refl


⊕-assoc : {A B C : Set} → A ⊕ (B ⊕ C) ↔ (A ⊕ B) ⊕ C
⊕-assoc {A} {B} {C} = record {to      = to'      ;
                              from    = from'    ;
                              from-to = from-to' ;
                              to-from = to-from' } where
                                  to' : A ⊕ (B ⊕ C) → (A ⊕ B) ⊕ C
                                  to' (inj₁ a)        = inj₁ (inj₁ a)
                                  to' (inj₂ (inj₁ b)) = inj₁ (inj₂ b)
                                  to' (inj₂ (inj₂ c)) = inj₂ c
                                  from' : (A ⊕ B) ⊕ C → A ⊕ (B ⊕ C)
                                  from' (inj₁ (inj₁ a)) = inj₁ a
                                  from' (inj₁ (inj₂ b)) = inj₂ (inj₁ b)
                                  from' (inj₂ c)        = inj₂ (inj₂ c)
                                  from-to' : (x : A ⊕ (B ⊕ C)) → from' (to' x) ≡ x
                                  from-to' (inj₁ _)        = refl
                                  from-to' (inj₂ (inj₁ _)) = refl
                                  from-to' (inj₂ (inj₂ _)) = refl
                                  to-from' : (y : (A ⊕ B) ⊕ C) → to' (from' y) ≡ y
                                  to-from' (inj₁ (inj₁ _)) = refl
                                  to-from' (inj₁ (inj₂ _)) = refl
                                  to-from' (inj₂ _)        = refl

⊕-comm : {A B : Set} → A ⊕ B ↔ B ⊕ A
⊕-comm {A} {B} = record {to      = to'      ;
                         from    = from'    ;
                         from-to = from-to' ;
                         to-from = to-from' } where
                               to' : A ⊕ B → B ⊕ A
                               to' (inj₁ a) = inj₂ a
                               to' (inj₂ b) = inj₁ b
                               from' : B ⊕ A → A ⊕ B
                               from' (inj₁ b) = inj₂ b
                               from' (inj₂ a) = inj₁ a
                               from-to' : (x : A ⊕ B) → from' (to' x) ≡ x
                               from-to' (inj₁ _) = refl
                               from-to' (inj₂ _) = refl
                               to-from' : (x : B ⊕ A) → to' (from' x) ≡ x
                               to-from' (inj₁ _) = refl
                               to-from' (inj₂ _) = refl
                           


⊕-cong : {A₁ A₂ B₁ B₂ : Set} → A₁ ↔ A₂ → B₁ ↔ B₂ → A₁ ⊕ B₁ ↔ A₂ ⊕ B₂
⊕-cong {A₁} {A₂} {B₁} {B₂} A↔ B↔ = record { to = to';
                                            from = from';
                                            from-to = from-to';
                                            to-from = to-from' } where
                                               to' :  A₁ ⊕ B₁ → A₂ ⊕ B₂
                                               to' (inj₁ a) = inj₁ (_↔_.to A↔ a)
                                               to' (inj₂ b) = inj₂ (_↔_.to B↔ b)
                                               from' :  A₂ ⊕ B₂ → A₁ ⊕ B₁
                                               from' (inj₁ a) = inj₁ (_↔_.from A↔ a)
                                               from' (inj₂ b) = inj₂ (_↔_.from B↔ b)
                                               from-to' : (x : A₁ ⊕ B₁) → from' (to' x) ≡ x
                                               from-to' (inj₁ a) = _↔_.from-to A↔ a under inj₁                                     
                                               from-to' (inj₂ b) = _↔_.from-to B↔ b under inj₂
                                               to-from' : (x : A₂ ⊕ B₂) → to' (from' x) ≡ x
                                               to-from' (inj₁ a) = _↔_.to-from A↔ a under inj₁                            
                                               to-from' (inj₂ b) = _↔_.to-from B↔ b under inj₂


×-cong : {A₁ A₂ B₁ B₂ : Set} → A₁ ↔ A₂ → B₁ ↔ B₂ → (A₁ × B₁) ↔ (A₂ × B₂)
×-cong {A₁} {A₂} {B₁} {B₂} A↔ B↔ = record { to      = to';
                                            from    = from';
                                            from-to = from-to';
                                            to-from = to-from' } where
                                               to'    :  A₁ × B₁ → A₂ × B₂
                                               to'   (a , b) = (_↔_.to A↔ a , _↔_.to B↔ b)
                                               from'  :  A₂ × B₂ → A₁ × B₁
                                               from' (a , b) = (_↔_.from A↔ a , _↔_.from B↔ b)
                                               pairEq : {A B : Set} {x y : A} {u v : B} → x ≡ y → u ≡ v → (x , u) ≡ (y , v)
                                               pairEq refl refl = refl
                                               from-to' : (x : A₁ × B₁) → from' (to' x) ≡ x
                                               from-to' (a , b) = pairEq (_↔_.from-to A↔ a) (_↔_.from-to B↔ b)
                                               to-from' : (y : A₂ × B₂) → to' (from' y) ≡ y
                                               to-from' (a , b) = pairEq (_↔_.to-from A↔ a) (_↔_.to-from B↔ b)







Any-++ : {A : Set} (P : A → Set) (xs ys : List A) → Any P (xs ++ ys) ↔ Any P xs ⊕ Any P ys

Any-++ P [] ys       = Any P ys ↔⟨ ↔sym ⊕-left-identity ⟩
                       ⊥ ⊕ Any P ys □↔ 
                                   
Any-++ P (x ∷ xs) ys = P x ⊕ Any P (xs ++ ys)        ↔⟨ ⊕-cong (P x □↔) (Any-++ P xs ys) ⟩
                       P x ⊕ (Any P xs ⊕ Any P ys)   ↔⟨ ⊕-assoc ⟩
                       (P x ⊕ Any P xs) ⊕ Any P ys   □↔ 


-- ++-assoc : {A : Set} (xs ys zs : List A) → ((xs ++ ys) ++ zs) ≡ (xs ++ (ys ++ zs))


++-comm : {A : Set} (xs ys : List A) → xs ++ ys ≈ ys ++ xs
++-comm xs ys z = z ∈ (xs ++ ys)      ↔⟨ Any-++ (z ≡_ )  xs ys ⟩
                  z ∈ xs ⊕ z ∈ ys     ↔⟨ ⊕-comm ⟩
                  z ∈ ys ⊕ z ∈ xs     ↔⟨ ↔sym (Any-++ (z ≡_ ) ys xs ) ⟩
                  z ∈ (ys ++ xs)      □↔


Any-concat : {A : Set} (P : A → Set) → (xss : List (List A)) → Any P (concat xss) ↔ Any (Any P) xss
Any-concat P []         = ⊥ □↔
Any-concat P (xs ∷ xss) = Any P (xs ++ concat xss)         ↔⟨ Any-++ P xs (concat xss) ⟩
                          Any P xs ⊕ Any P (concat xss)    ↔⟨ ⊕-cong (Any P xs □↔) (Any-concat P xss) ⟩
                          Any P xs ⊕ Any (Any P) xss       □↔

Any-map : {A B : Set} (P : B → Set) → (f : A → B) → (xs : List A) → Any P (map f xs) ↔ Any (P ∘ f) xs
Any-map P f []       = ⊥ □↔
Any-map P f (x ∷ xs) = P (f x) ⊕ Any P (map f xs) ↔⟨ ⊕-cong (P (f x) □↔) (Any-map P f xs) ⟩
                      (P ∘ f) x ⊕ Any (P ∘ f) xs □↔


Any->>= : {A B : Set} (P : B → Set) → (xs : List A) → (f : A → List B) → Any P (xs >>= f) ↔ Any (Any P ∘ f) xs
Any->>= P xs f = Any P (concat (map f xs))  ↔⟨ Any-concat P (map f xs) ⟩
                 Any (Any P) (map f xs)     ↔⟨ Any-map (Any P) f xs ⟩
                 Any (Any P ∘ f) xs         □↔




Any-∈ : {A : Set} {P : A → Set} {xs : List A} → Any P xs ↔ (∃ λ z → P z × z ∈ xs)
Any-∈ {A} {P} {[]}     = ⊥ ↔⟨ (↔sym ∘ uninhabited) (⊥-elim ∘ proj₂ ∘ proj₂) ⟩
                         (∃ λ z → P z × z ∈ []) □↔
Any-∈ {A} {P} {x ∷ xs} = record {to      = to'      ;
                                   from    = from'    ;
                                   from-to = from-to' ;
                                   to-from = to-from' } where
                                    to' : P x ⊕ Any P xs → ∃ (λ z → P z × z ∈ (x ∷ xs))
                                    to' (inj₁ px)  = x , (px , (inj₁ refl))
                                    to' (inj₂ any) = (proj₁ recEx) , ( (proj₁ ∘ proj₂) recEx , (inj₂ (proj₂ (proj₂ recEx))) ) where
                                           recEx = _↔_.to Any-∈ any
                                    from' : ∃ (λ z → P z × z ∈ (x ∷ xs)) → P x ⊕ Any P xs
                                    from' ex = from'' (proj₁ ex) (proj₁ (proj₂ ex)) (proj₂ (proj₂ ex)) where
                                           from'' : (z : A) → P z → z ∈ (x ∷ xs) → P x ⊕ Any P xs
                                           from'' .x px (inj₁ refl) = inj₁ px
                                           from''  z pz (inj₂ z∈xs) = inj₂ recAny where
                                                recAny = _↔_.from (Any-∈ {P = P}) (z , (pz , z∈xs))
                                    from-to' : (pf : P x ⊕ Any P xs) → from' (to' pf) ≡ pf
                                    from-to' (inj₁ px)  = refl
                                    from-to' (inj₂ any) = _↔_.from-to Any-∈ any under inj₂
                                    to-from' : (ex : ∃ (λ z → P z × z ∈ (x ∷ xs))) → to' (from' ex) ≡ ex
                                    to-from' ex = to-from'' (proj₁ ex) (proj₁ (proj₂ ex)) (proj₂ (proj₂ ex)) where
                                              to-from'' : (z : A) → (pz : P z) → (z∈xxs : z ∈ (x ∷ xs)) →
                                                             to' (from' ( z , ( pz , z∈xxs ))) ≡ ( z , ( pz , z∈xxs ))
                                              to-from'' .x px (inj₁ refl) = refl
                                              to-from''  z pz (inj₂ z∈xs) = _↔_.to-from (Any-∈ {P = P}) (z , ( pz , z∈xs ) )
                                                   under (λ ex → ((proj₁ ex) , ( (proj₁ ∘ proj₂) ex , (inj₂ (proj₂ (proj₂ ex))))))



∃-cong : {A : Set} {P Q : A → Set} → (∀ x → P x ↔ Q x) → (∃ λ x → P x) ↔ (∃ λ x → Q x)
∃-cong p = record {to     = λ ex → proj₁ ex ,  _↔_.to (p (proj₁ ex)) (proj₂ ex);
                   from    = λ ex → proj₁ ex ,  _↔_.from (p (proj₁ ex)) (proj₂ ex);
                   from-to = λ ex → _↔_.from-to (p (proj₁ ex)) (proj₂ ex) under λ pf → (proj₁ ex) , pf;
                   to-from = λ ex → _↔_.to-from (p (proj₁ ex)) (proj₂ ex) under λ pf → (proj₁ ex) , pf }




Any-cong : {A : Set} (P Q : A → Set) → (xs ys : List A) → (∀ x → P x ↔ Q x) → xs ≈ ys → Any P xs ↔ Any Q ys
Any-cong P Q xs ys p eq = Any P xs                   ↔⟨ Any-∈ ⟩
                          (∃ λ z → P z × z ∈ xs)  ↔⟨ ∃-cong (λ x → ×-cong (p x) (eq x)) ⟩
                          (∃ λ z → Q z × z ∈ ys)  ↔⟨ ↔sym Any-∈ ⟩
                          Any Q ys                  □↔



All-cong : {A : Set} {P Q : A → Set} → {xs ys : List A} → (∀ x → P x ↔ Q x) → xs ≈ ys →
                                                   (∀ x → x ∈ xs → P x) ⇔ (∀ y → y ∈ ys → Q y)
All-cong {P} {Q} {xs} {ys} p eq = record {to = λ P∀x y y∈ys → _↔_.to (p y) (P∀x y (_↔_.from (eq y) y∈ys));
                                          from = λ Q∀y x x∈xs → _↔_.from (p x) (Q∀y x (_↔_.to (eq x) x∈xs))}
                                 
