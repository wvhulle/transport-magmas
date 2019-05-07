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
op₂' x y = transport fEq
    (op₁ (transport (sym fEq) x) (transport (sym fEq) y))

-- op₂'  x y  = transp (λ i → ℕ₀) i0
--  (prim^unglue {ℓ-zero} {ℓ-zero} {Σ ℕ notZero} {i1} {λ x → ℕ} {\ p → (λ z → {!!} , {!!} , {!!}) , {!!}}
--  (op₁ (transport (sym fEq) x) (transport (sym fEq) y)))


opᵢ' : PathP (λ i → Op₂ (fEq i))  op₁'  op₂'
opᵢ' i x y = transport (sym (zeroPath i))
    (op₁ (transport (zeroPath i) x) (transport (zeroPath i) y))

-- This code shows two lemma of the fact that the endpoints of the original intermediate operator are definitionally equal to op₁ and op₂. Using this proofs and transport, a new intermediate operator transOp' is defined that does satisfy the requirements for the intermediate operator of the intermediate magma.

startLemma : op₁ ≡ op₁'
startLemma i = λ x y → x + (transportRefl y) i

-- uaβ : (e : A ≃ B) (x : A) → transport (ua e) x ≡ (fst e) x
-- here                                  (ua e) = sym (zeroPath i)
-- so e = au (sym (zeroPath i))

endLemma : op₂ ≡ op₂'
endLemma i x y = {!!}

-- endLemma = sym {ℓ-zero} {ℕ₀ → ℕ₀ → ℕ₀} {transport (ua (idEquiv (ℕ₀ → ℕ₀ → ℕ₀))) op₂} {idEquiv (ℕ₀ → ℕ₀ → ℕ₀) .fst op₂} ( Univalence.uaβ {ℓ-zero} {ℕ₀ → ℕ₀ → ℕ₀} {ℕ₀ → ℕ₀ → ℕ₀} ((idEquiv (ℕ₀ → ℕ₀ → ℕ₀))) op₂)

pathLemma : (PathP (λ i → Op₂ (fEq i)) op₁' op₂')  ≡  PathP ((λ i → Op₂ (fEq i))) op₁ op₂
pathLemma = doubleCong (PathP (λ i → Op₂ (fEq i))) startLemma endLemma
-- PathP : ∀ {ℓ} (A : I → Set ℓ) → A i0 → A i1 → Set ℓ
opᵢ : PathP (λ i → Op₂ (fEq i)) op₁ op₂
opᵢ = transport pathLemma opᵢ'
-- the endpoints should be precisely op₁ and op₂
algPath : s₁ ≡ s₂
algPath = λ i → record {
   Carrier = (fEq i) ;
   _≈_ =  _≡_;
   _∙_ = opᵢ i ;
   isMagma = record {
    isEquivalence = ≡equiv  ;
     ∙-cong   = {! doubleCong (transOp' i)!}
     }
   }
