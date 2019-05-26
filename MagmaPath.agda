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

open import Agda.Primitive.Cubical
open import AlgebraExamples
zeroPath : (i : I) → (fEq i) ≡ ℕ
zeroPath i = λ j → fEq (i ∧ (~ j))

op₁' : Op₂ ℕ
op₁' x y = x + transport refl y 

op₂' : Op₂ ℕ₀
op₂' x y = transport fEq (op₁ (transport (sym fEq) x) (transport (sym fEq) y))
--op₂' x y = transport fEq (op₁ (transport gEq x) (transport gEq y))



opᵢ' : PathP (λ i → Op₂ (fEq i))  op₁  op₂'
opᵢ' i x y = transport (sym (zeroPath i))
    (op₁ (transport (zeroPath i) x) (transport (zeroPath i) y))

--opᵢ' i x y = transport (sym (zeroPath i))
--    (op₁ (transport (zeroPath i) x) (transport (zeroPath i) y))


startLemma : op₁ ≡ op₁'
startLemma i x y = x + (transportRefl y) i

transpR : (z : ℕ) → transport fEq z ≡ f z
transpR z = Univalence.uaβ fEquiv z

-- ua e i = Glue B (λ { (i = i0) → (A , e)
--                    ; (i = i1) → (B , idEquiv B) })

transpLLemma₁ : sym (ua (isoToEquiv fIso)) ≡ ua (isoToEquiv (invIso fIso))
transpLLemma₁ = {!!}

-- maybe with isomorphism induction?
--elimIso : {B : Type ℓ} → (Q : {A : Type ℓ} → (A → B) → (B → A) → Type ℓ') →
--          (h : Q (idfun B) (idfun B)) → {A : Type ℓ} →
--          (f : A → B) → (g : B → A) → section f g → retract f g → Q f g

--elimIso (λ f g → )

transpLLemma₂ : (z : ℕ₀) → transport (sym fEq) z ≡ transport (ua gEquiv) z
transpLLemma₂ z = cong (λ p → transport p z) transpLLemma₁ 

transpL : (z : ℕ₀) → transport (sym fEq) z ≡ g z
transpL z = (transpLLemma₂ z) ∙  (Univalence.uaβ gEquiv z) -- Univalence.uaβ gEquiv z
--transport (ua e) x ≡ e .fst x
--g (suc x , _) = x 


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
--       ≡⟨  cong f (refl) ⟩
--   ((suc (g x + g y))  , true)
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
