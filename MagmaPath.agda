{-# OPTIONS --cubical --safe #-}
module MagmaPath  where

open import Cubical.Data.Nat


--open import Relation.Binary
--open import Algebra.Structures
--open import Algebra.Morphism
open import Cubical.Core.Everything
open import Cubical.Foundations.Isomorphism -- isotoequiv
open import Cubical.Foundations.Prelude -- ≡ 
open import Cubical.Foundations.Isomorphism -- isotoequiv
open import Algebra.FunctionProperties.Core -- Op₂
--open import Agda.Primitive

--open import Cubical.Data.Nat.Properties
--

open import Cubical.Foundations.Univalence as Univalence
open import Cubical.Foundations.Equiv

open import Agda.Primitive.Cubical


open import AlgebraExamples


f : ℕ → ℕ₀ 
f n = (suc n , ( n , refl ) )

g : ℕ₀ → ℕ 
g (n , (n⁻ , p)) = n⁻ 

l' : (b : ℕ₀) → f (g b) ≡ b
l' (n , (n⁻ , p)) =  λ i → ( (sym p) i , (n⁻  , λ j → p  (~ i ∨ j)))

r' : (a : ℕ) → g (f a) ≡ a
r' zero = refl
r' (suc a) = refl

fEquiv : ℕ ≃ ℕ₀ 
fEquiv = (f ,  isoToIsEquiv (iso f g l' r'))

fEq : ℕ ≡ ℕ₀ 
fEq = ua fEquiv

-- This definition of the intermediate operator is done by transporting the arguments along zeroPath back to fEq i0, applying op₁. The result is then translated back forward to fEq i.

zeroPath : (i : I) → (fEq i) ≡ ℕ
zeroPath i = λ j → fEq (i ∧ (~ j))

op₁' : Op₂ ℕ
op₁' x y = x + transport refl y 

op₂' : Op₂ ℕ₀
--op₂' x y = transport fEq
--    (op₁ (transport (sym fEq) x) (transport (sym fEq) y))

op₂'  x y  = transp (λ i → ℕ₀) i0
  (prim^unglue {{!!}} {{!!}} {{!!}} {{!!}} {{!!}} {{!!}}
  (op₁ (transport (sym fEq) x) (transport (sym fEq) y)))


transOp : PathP (λ i → Op₂ (fEq i))  op₁'  op₂'
transOp i x y = transport (sym (zeroPath i))
    (op₁ (transport (zeroPath i) x) (transport (zeroPath i) y))

-- This code shows two lemma of the fact that the endpoints of the original intermediate operator are definitionally equal to op₁ and op₂. Using this proofs and transport, a new intermediate operator transOp' is defined that does satisfy the requirements for the intermediate operator of the intermediate magma.

startLemma : op₁ ≡ op₁'
startLemma i x y = x + (transportRefl y) i


-- uaβ : {A B : Set ℓ} (e : A ≃ B) (x : A) → transport (ua e) x ≡ e .fst x
-- (e x) = op₁, transport (ua e) x = op₂'

endLemma :  op₂'  ≡ op₂
--endLemma i x y  =(Univalence.uaβ {!fEquiv!} (op₁ (transport (sym fEq) x) (transport (sym fEq) y))) i 

endLemma j x y = op₂ x y
  -- (Univalence.uaβ {{!!}} {{!!}} {{!!}}  fEquiv ((op₁ (transport (sym fEq) x) (transport (sym fEq) y)))) i

pathLemma : (PathP (λ i → Op₂ (fEq i)) op₁' op₂')  ≡  PathP ((λ i → Op₂ (fEq i))) op₁ op₂
--pathLemma = doubleCong (PathP (λ i → Op₂ (fEq i))) startLemma endLemma
pathLemma = doubleCong (PathP (λ i → Op₂ (fEq i))) startLemma (sym endLemma)

-- PathP : ∀ {ℓ} (A : I → Set ℓ) → A i0 → A i1 → Set ℓ
transOp' : PathP (λ i → Op₂ (fEq i)) op₁ op₂
transOp' = transport pathLemma transOp
-- the endpoints should be precisely op₁ and op₂


algPath : s₁ ≡ s₂
algPath = λ i → record {
   Carrier = (fEq i) ;
   _≈_ =  _≡_;
   _∙_ = transOp' i ;
   isMagma = record {
    isEquivalence = ≡equiv  ;
     ∙-cong   = {! doubleCong (transOp' i)!} --
     }
   }

