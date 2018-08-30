
{-# OPTIONS --no-universe-polymorphism #-}
open import Induction.WellFounded as WF
open import Data.Product 
open import Relation.Binary.Core
open import Relation.Unary as U using (Decidable)
open import Relation.Nullary
import Level as L using (zero)


module DivideEtImpera where
{-- This module implements a quite general version of Divide and Conquer as desribed by Douglas R. Smith in his paper 
   "The Design of Divide and Conquer Algorithms" 1984. the function makeD&C requires a well founded relation, a decidable proposition 
   of whether a given input is primitive, a composition and a decomposition function, a special function g and a function dirSolve.
   All of these functions have to fullfill certain conditions and lastly you also need an "induction principle" that describes that these
   functions work well together. After putting in all this work, you can finally reap your reward: an algorithm that does what you want:
   takes inputs that satisfy the input condition and returns results that satisfy the output condition.  
 --}


{-- these 2 functions should be somewhere in the agda standard libraries but i couln't find them so i just wrote them again --}


foldAcc : {A : Set} → {_<_ : Rel A L.zero} → {R : A → Set} →
          (step : (x : A) → ((y : A) → _<_ y x → R y) → R x) →
          (z : A) → Acc _<_ z → R z
foldAcc step z (acc a) = step z (λ y y<z → foldAcc step y (a y y<z))



wfInd : {A : Set} {_<_ : Rel A _} → (WellFounded _<_) →
        {R : A → Set} →
        (step : (x : A) → ((y : A) → _<_ y x → R y) → R x) →
        (z : A) → R z
wfInd wf step z = foldAcc step z (wf z)


{- the algorithm itself as one huge function:
 instead of requiring all the functions and then five axioms describing their behaiviour, i use
 dependent types to embedd four of the axions in therespective function they describe and
 only the last one (called "lemma" here) as an extra. See the paper for details -}


makeD&C1 : {D₁ R₁ D₂ R₂ : Set} {I₁ : D₁ → Set} {O₁ : D₁ → R₁ → Set} {I₂ : D₂ → Set}
           {O₂ : D₂ → R₂ → Set} {O₃ : D₁ → (D₂ × D₁) → Set} {O₄ : (R₂ × R₁) → R₁ → Set}
           {_<_ : Rel D₁ _} → (wf : Well-founded _<_) → {Prim : D₁ → Set} → (pDec : U.Decidable Prim) →                          
           (decomp : (x : D₁) → I₁ x → ¬ Prim x → Σ (D₂ × D₁)
                   λ y → I₂ (proj₁ y) × (I₁ (proj₂ y)) × (_<_ (proj₂ y) x) × (O₃ x y) ) →  
           (comp : (u : (R₂ × R₁)) → Σ R₁ (O₄ u)) →                                                                            
           (g : (x : D₂) → I₂ x → Σ R₂ (O₂ x)) →                                                                                
           (dirSolve : (x : D₁) → I₁ x → Prim x → Σ R₁ (O₁ x)) →                                                                
           (lemma : ∀{x₀ x₁ x₂ z₀ z₁ z₂} → O₃ x₀ (x₁ , x₂) → O₂ x₁ z₁ → O₁ x₂ z₂ → O₄ (z₁ , z₂) z₀ → O₁ x₀ z₀) →               
           (x : D₁) → I₁ x → Σ R₁ (O₁ x)                                                                                 

makeD&C1 {D₁ = D₁} {R₁ = R₁} {I₁ = I₁} {O₁ = O₁} {_<_ = _<_} wf {Prim} pDec decomp comp g dirSolve lemma x = wfInd wf step x where 
                                                step : (x : D₁) → ((y : D₁) → _<_ y x → I₁ y → Σ R₁ (O₁ y)) → I₁ x → Σ R₁ (O₁ x) 
                                                step x rec ix with (pDec x)                                                
                                                step x rec ix | (yes pfY) = dirSolve x ix pfY                        
                                                step x rec ix | (no  pfN) = let dec = decomp x ix pfN
                                                                                decV  = proj₁ dec                   
                                                                                decV1 = proj₁ decV                   
                                                                                decV2 = proj₂ decV
                                                                                decP  = proj₂ dec
                                                                                decP1 = proj₁ decP                  
                                                                                decP2 = proj₁ (proj₂ decP)
                                                                                decP3 = proj₁ (proj₂ (proj₂ decP))
                                                                                decP4 = proj₂ (proj₂ (proj₂ decP))
                                                                                gRes  = g decV1 decP1               
                                                                                gV    = proj₁ gRes                  
                                                                                gP    = proj₂ gRes
                                                                                fRes  = rec decV2 decP3 decP2
                                                                                fV    = proj₁ fRes
                                                                                fP    = proj₂ fRes
                                                                                com   = comp (gV , fV)               
                                                                                comV  = proj₁ com
                                                                                comP  = proj₂ com
                                                                                proof = lemma decP4 gP fP comP      
                                                                             in (comV , proof)                      


{- it occurred to me, that a proper Divide and conquer algorithm should make (at least) two recursive calls,
   the algorithm describen inthe pape, however, only makes one! So slightly modified it to fit in that extra
   recursive calls but left the basic principle exactly the same in this second version -}


makeD&C2 : {D₁ R₁ D₂ R₂ : Set} {I₁ : D₁ → Set} {O₁ : D₁ → R₁ → Set} {I₂ : D₂ → Set}
                 {O₂ : D₂ → R₂ → Set} {O₃ : D₁ → (D₂ × (D₁ × D₁)) → Set} {O₄ : (R₂ × (R₁ × R₁)) → R₁ → Set}      
                 {_<_ : Rel D₁ _} → (wf : Well-founded _<_) → {Prim : D₁ → Set} → (pDec : U.Decidable Prim) →                         
                 (decomp : (x : D₁) → I₁ x → ¬ Prim x → Σ (D₂ × (D₁ × D₁))
                           λ y → (I₂ (proj₁ y)) × (I₁ (proj₁ (proj₂ y))) × (I₁ (proj₂ (proj₂ y))) ×
                                 (_<_ (proj₁ (proj₂ y)) x) × (_<_ (proj₂ (proj₂ y)) x) × (O₃ x y) ) →  
                 (comp : (u : (R₂ × (R₁ × R₁)) ) → Σ R₁ (O₄ u)) →                                        
                 (g : (x : D₂) → I₂ x → Σ R₂ (O₂ x)) →                                                                                
                 (dirSolve : (x : D₁) → I₁ x → Prim x → Σ R₁ (O₁ x)) →                                                                
                 (lemma : ∀{x₀ x₁ x₂ x₃ z₀ z₁ z₂ z₃} → O₃ x₀ (x₁ , (x₂ , x₃ )) → O₂ x₁ z₁ → O₁ x₂ z₂
                             → O₁ x₃ z₃ → O₄ (z₁ , (z₂ , z₃)) z₀ → O₁ x₀ z₀) →               
                 (x : D₁) → I₁ x → Σ R₁ (O₁ x)                                                                                 

makeD&C2 {D₁ = D₁} {R₁ = R₁} {I₁ = I₁} {O₁ = O₁} {_<_ = _<_} wf {Prim} pDec decomp comp g dirSolve lemma x = wfInd wf step x where 
                                                step : (x : D₁) → ((y : D₁) → _<_ y x → I₁ y → Σ R₁ (O₁ y)) → I₁ x → Σ R₁ (O₁ x) 
                                                step x rec ix with (pDec x)                                                            
                                                step x rec ix | (yes pfY) = dirSolve x ix pfY                        
                                                step x rec ix | (no  pfN) = let dec = decomp x ix pfN
                                                                                decV = proj₁ dec
                                                                                decV1 = proj₁ decV                   
                                                                                decV2 = proj₁ (proj₂ decV)
                                                                                decV3 = proj₂ (proj₂ decV)
                                                                                decP  = proj₂ dec
                                                                                decP1 = proj₁ decP                  
                                                                                decP2 = proj₁ (proj₂ decP)
                                                                                decP3 = proj₁ (proj₂ (proj₂ decP))
                                                                                decP4 = proj₁ (proj₂ (proj₂ (proj₂ decP)))
                                                                                decP5 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ decP)))) 
                                                                                decP6 = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ decP))))
                                                                                gRes  = g decV1 decP1               
                                                                                gV    = proj₁ gRes                  
                                                                                gP    = proj₂ gRes
                                                                                f1Res = rec decV2 decP4 decP2
                                                                                f1V   = proj₁ f1Res
                                                                                f1P   = proj₂ f1Res
                                                                                f2Res = rec decV3 decP5 decP3
                                                                                f2V   = proj₁ f2Res
                                                                                f2P   = proj₂ f2Res
                                                                                com   = comp (gV , (f1V , f2V))               
                                                                                comV  = proj₁ com
                                                                                comP  = proj₂ com
                                                                                proof = lemma decP6 gP f1P f2P comP
                                                                            in (comV , proof)



