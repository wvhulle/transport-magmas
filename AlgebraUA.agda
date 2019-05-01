{-# OPTIONS --cubical --safe #-}
module AlgebraUA   where

open import Algebra
open import Algebra.FunctionProperties.Core
open import Algebra.Structures
open import Algebra.Morphism

open import Function
open import Relation.Binary
open import Agda.Primitive

open import Cubical.Data.Nat.Properties
open import Cubical.Data.Nat
open import Cubical.Foundations.Isomorphism
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence as Univalence
open import Cubical.Foundations.Equiv

≡equiv : ∀ {a} {A : Set a} → IsEquivalence {a} {a} {A} _≡_
≡equiv = record {refl = refl ; sym = sym ; trans = _∙_ }

cong1 : { x y u v : ℕ} → x ≡ y → u ≡ v → (x + u) ≡ (y + v)
cong1 p1 p2 =   (cong (λ x → (x + (p2 i0))) p1) ∙ ( cong (λ u → (p1 i1) + u) p2)

op₁ : Op₂ ℕ
op₁ = _+_

{-
record myMagma  c ℓ : Set (lsuc  (c ⊔ ℓ)) where
  infixl 7 _ ✧ _
  field
    Carrier : Set c
    _✧_     : Op₂ Carrier
    s       : isSet Carrier
 -}   


s₁ : Algebra.Magma  _ _
s₁ = record {
   Carrier = ℕ ;
   _≈_ = _≡_ ;
   _∙_ = op₁ ;
   isMagma = record {
    isEquivalence = ≡equiv ;
     ∙-cong   = cong1
     }
   }

notZero :  ℕ → Set _
notZero n = Σ ℕ (λ m → (n ≡ (suc m)))

ℕ₀ : Set _
ℕ₀ = Σ ℕ (λ n → notZero n)

toℕ : ℕ₀ → ℕ
toℕ (n , p) = n

sucPredLemma : (n : ℕ) → notZero n → n ≡ suc (predℕ n)
sucPredLemma n (n⁻ , p) = p ∙ (cong suc (refl ∙ (cong predℕ (sym p))))

doubleCong : ∀ {a b} {X Y : Set a} {Z : Set b} {x₁ x₂ : X} {y₁ y₂ : Y}
              (f : X → Y → Z) → x₁ ≡ x₂ → y₁ ≡ y₂ → f x₁ y₁ ≡ f x₂ y₂    
--doubleCong f p q = λ i →  ((cong f p) i) (q i)
doubleCong f p q i = cong₂ f p q i

sumLem : (x y :  ℕ) → notZero x → notZero y → predℕ (x + y) ≡ suc (predℕ (predℕ (x + y)))
sumLem x y (x⁻ , snd₁) (y⁻ , snd₂) = sucPredLemma (predℕ (x + y)) ((x⁻ + y⁻) , (cong predℕ (doubleCong (_+_) snd₁ snd₂)) ∙ (+-suc x⁻ y⁻))

--The implementation of the definition of $M_2$ in agda works by giving a term for the record type magmas. Such a term, called a record, takes all the components of a magma such as the carrier set, operator and equivalence relation on the carrier set and groups them in one object.

op₂ : Op₂ ℕ₀
op₂ (x , p)  (y , q) = ( predℕ ( x + y ) , ( predℕ (predℕ (x + y)) , sumLem x  y p q) )

s₂ : Algebra.Magma _ _
s₂ = record {
  Carrier = ℕ₀ ;
  _≈_ = (_≡_) ;
  _∙_ = op₂ ;
  isMagma = record {
    isEquivalence = ≡equiv ;
     ∙-cong   =  doubleCong op₂ --cong2
     }
  }


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

zeroPath : (i : I) → (fEq i) ≡ (fEq i0)
zeroPath i = λ j → fEq (i ∧ (~ j))

op₁' : Op₂ (fEq i0)
op₁' = (λ x y → x + transport refl y)

op₂' : Op₂ (fEq i1)
--op₂'  x y = transp (λ i → ℕ₀) i0 (prim^unglue {ℓ-zero} {ℓ-zero} {Σ ℕ notZero} {i1} {{!!}} {λ p → {!fEquiv!}} (op₁ (transport {ℓ-zero} {ℕ₀} {ℕ} (sym {ℓ-suc ℓ-zero} {{!!}} fEq) x) (transport {ℓ-zero} {Σ ℕ (λ z → Σ ℕ (λ z₁ → z ≡ suc z₁))} {ℕ} (sym {ℓ-suc ℓ-zero} {{!!}} fEq) y)))

op₂' x y = transport fEq (op₁ (transport (sym fEq) x) (transport (sym fEq) y))

transOp : PathP (λ i → Op₂ (fEq i))  op₁'  op₂'
transOp i x y = transport (sym (zeroPath i)) (op₁ (transport (zeroPath i) x) (transport (zeroPath i) y))

-- This code shows two lemma of the fact that the endpoints of the original intermediate operator are definitionally equal to op₁ and op₂. Using this proofs and transport, a new intermediate operator transOp' is defined that does satisfy the requirements for the intermediate operator of the intermediate magma.

startLemma : op₁ ≡ op₁'
startLemma i = λ x y → x + (transportRefl y) i

-- uaβ : {A B : Set ℓ} (e : A ≃ B) (x : A) → transport (ua e) x ≡ e .fst x
-- (e x) = op₁, transport (ua e) x = op₂'


tEq : (ℕ ≃ ℕ₀) ≡ (ℕ ≃ Σ ℕ notZero)
tEq = cong (λ t → ℕ ≃ t) refl

endLemma : op₂ ≡ op₂'
-- endLemma i x y = (sym (Univalence.uaβ ((λ n → ({!suc n!} , ({!n!} , {!refl!}))) , {!!}) ((op₁ (transport (sym fEq) x) (transport (sym fEq) y))))) i
endLemma i x y = (sym (Univalence.uaβ (transport tEq {!fEquiv!}) ((op₁ (transport (sym fEq) x) (transport (sym fEq) y))))) i

pathLemma : (PathP (λ i → Op₂ (fEq i)) op₁' op₂')  ≡  PathP ((λ i → Op₂ (fEq i))) op₁ op₂
--pathLemma = doubleCong (PathP (λ i → Op₂ (fEq i))) startLemma endLemma
pathLemma = doubleCong {!!} startLemma endLemma

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

open Algebra.Magma

--test1 : (Algebra.Magma._∙_ s₂) ≡ (Algebra.Magma._∙_ (algPath i1))
--test1 = {!!}

isCommutative : ∀  {a l} → (Algebra.Magma a l) → Set a
isCommutative m = (x y : (Carrier m)) →  ((Algebra.Magma._∙_  m) x y) ≡ ((Algebra.Magma._∙_  m) y x)

com₁ : isCommutative s₁
com₁ = +-comm

com₂ : isCommutative s₂
com₂ = transport (λ i → isCommutative (algPath i)) com₁
