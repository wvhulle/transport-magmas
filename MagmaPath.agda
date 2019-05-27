{-# OPTIONS --cubical --safe #-}
module MagmaPath  where

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Properties
open import Function
open import Cubical.Core.Everything
open import Cubical.Foundations.Isomorphism -- isotoequiv
open import Cubical.Foundations.Prelude -- ≡ 
open import Algebra.FunctionProperties.Core -- Op₂
open import Cubical.Foundations.Univalence as Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Agda.Primitive.Cubical
open import AlgebraExamples
zeroPath : (i : I) → (fEq i) ≡ ℕ
zeroPath i = λ j → fEq (i ∧ (~ j))

op₁' : Op₂ ℕ
op₁' x y = x + transport refl y 

op₂' : Op₂ ℕ₀
op₂' x y = transport fEq (op₁ (transport (sym fEq) x) (transport (sym fEq) y))

opᵢ' : PathP (λ i → Op₂ (fEq i))  op₁  op₂'
opᵢ' i x y = transport (sym (zeroPath i))
    (op₁ (transport (zeroPath i) x) (transport (zeroPath i) y))

startLemma : op₁ ≡ op₁'
startLemma i x y = x + (transportRefl y) i

transpR : (z : ℕ) → transport fEq z ≡ f z
transpR z = Univalence.uaβ fEquiv z

baseIndLemma : (A : Type ℓ-zero) → (λ i → ua (idEquiv A) (~ i)) ≡ ua (invEquiv (idEquiv A))
baseIndLemma A = 
  sym ( ua (idEquiv A) ) ≡⟨ uaIdEquiv ⟩
  sym refl ≡⟨ refl ⟩
  refl ≡⟨ sym uaIdEquiv ⟩
  ua (idEquiv A) ≡⟨ cong ua (equivEq (idEquiv A) (invEquiv (idEquiv A)) refl) ⟩
  ua (invEquiv (idEquiv A)) ∎

transpLLemma₁ : sym (ua fEquiv) ≡ (ua (invEquiv fEquiv))
transpLLemma₁ = EquivJ
  (λ _ _ e → sym (ua e) ≡ ua (invEquiv e)) (λ A → baseIndLemma A) ℕ₀ ℕ fEquiv 

transpL : (z : ℕ₀) → transport (sym fEq) z ≡ g z
transpL z =
  transport (sym fEq) z ≡⟨ (cong (λ p → transport p z) transpLLemma₁) ⟩
  transport (ua (invEquiv fEquiv)) z ≡⟨ refl ⟩
  transport (ua gEquiv) z ≡⟨ (Univalence.uaβ gEquiv z) ⟩
  g z ∎

-- could be generalized to other structure-preserving maps
gIsMorphism : (x y : ℕ₀) → f (op₁  (g x) (g y)) ≡ (op₂ x y)
gIsMorphism (suc x , _) (suc y , _) = refl

endLemma : op₂' ≡ op₂
endLemma i x y =
  (op₂' x y
       ≡⟨ refl ⟩
   transport fEq (op₁ (transport (sym fEq) x) (transport (sym fEq) y))
       ≡⟨ transpR (op₁  (transport (sym fEq) x) (transport (sym fEq) y)) ⟩
   f (op₁  (transport (sym fEq) x) (transport (sym fEq) y))
       ≡⟨ cong₂ (λ x y → f (op₁ x y)) (transpL x) (transpL y) ⟩
   f (op₁  (g x) (g  y))
       ≡⟨ gIsMorphism x y ⟩
   op₂ x y ∎) i 

pathLemma : (PathP (λ i → Op₂ (fEq i)) op₁' op₂')  ≡  PathP ((λ i → Op₂ (fEq i))) op₁ op₂
pathLemma = cong₂ (PathP (λ i → Op₂ (fEq i))) startLemma endLemma

opᵢ : PathP (λ i → Op₂ (fEq i)) op₁ op₂
opᵢ = transport pathLemma opᵢ'

algPath : s₁ ≡ s₂
algPath = λ i → record {
   Carrier = fEq i ;
   _✧_ = opᵢ i
   }
