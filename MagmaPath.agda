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

gEquiv : ℕ₀ ≃ ℕ
gEquiv = (g , isoToIsEquiv (iso g f r' l'))

fEq : ℕ ≡ ℕ₀ 
fEq = ua fEquiv

-- This definition of the intermediate operator is done by transporting the arguments along zeroPath back to fEq i0, applying op₁. The result is then translated back forward to fEq i.

zeroPath : (i : I) → (fEq i) ≡ ℕ
zeroPath i = λ j → fEq (i ∧ (~ j))

op₁' : Op₂ ℕ
op₁' x y = x + transport refl y 

op₂' : Op₂ ℕ₀
op₂' x y = transport fEq (op₁ (transport (sym fEq) x) (transport (sym fEq) y))


--op₂'  x y  = transp (λ i → ℕ₀) i0
--  (prim^unglue {ℓ-zero} {ℓ-zero} {Σ ℕ notZero} {i1} {λ x → ℕ} {\ p → (λ z → {!!} , {!!} ,-- {!!}) , {!!}}
--  (op₁ (transport (sym fEq) x) (transport (sym fEq) y)))

opᵢ' : PathP (λ i → Op₂ (fEq i))  op₁  op₂'
opᵢ' i x y = transport (sym (zeroPath i))
    (op₁ (transport (zeroPath i) x) (transport (zeroPath i) y))

startLemma : op₁ ≡ op₁'
startLemma i x y = x + (transportRefl y) i
--startLemma i x y = x + y

-- uaβ : (e : A ≃ B) (x : A) → transport (ua e) x ≡ (fst e) x
-- here                                  (ua e) = sym (zeroPath i)
-- so e = au (sym (zeroPath i))
 

transpR : (z : ℕ) → transport fEq z ≡ f z
transpR z = Univalence.uaβ fEquiv z

transpL : (z : ℕ₀) → transport (sym fEq) z ≡ g z
transpL z = Univalence.uaβ gEquiv z

-- op₂ x y ≡ x + y - 1 (refl)
-- x + y - 1 ≡ op₂ (transport (sym fEq) x) (transport (sym fEq) y)

-- x + y - 1 ≡  (op₁ (transport (sym fEq) x) (transport (sym fEq) y)) - 1
--     = doubleCong op₂ (sym (transpL x)) (sym (transpR y)) 
-- (op₁ (transport (sym fEq) x) (transport (sym fEq) y)) - 1 ≡ transport fEq (op₁ (transport (sym fEq) x) (transport (sym fEq) y))
--     = sym (transpR (op₁ (transport (sym fEq) x) (transport (sym fEq) y)) )

l₁ : (x y : ℕ₀) → transport fEq (op₁ (transport (sym fEq) x) (transport (sym fEq) y)) ≡ f (op₁  (transport (sym fEq) x) (transport (sym fEq) y)) 
l₁ x y  = transpR (op₁  (transport (sym fEq) x) (transport (sym fEq) y)) 

l₂ : (x y : ℕ₀) → f (op₁  (transport (sym fEq) x) (transport (sym fEq) y))  ≡  f (op₁  (g x) (g  y))
l₂ x y = doubleCong (λ x y → f (op₁ x y)) (transpL x) (transpL y)

l₂' : ( x y : ℕ₀) →  g x + g y ≡ predℕ (predℕ (fst x + fst y) )
l₂'  x y = {!refl!} 

l₃ : (x y : ℕ₀) → f (op₁  (g x) (g  y)) ≡ f (predℕ ( predℕ ((fst x) + (fst y))))
l₃ (x , (x⁻ , p)) (y , (y⁻ , q)) = cong f {!l₂'  (f x⁻) (f y⁻)!}

l₄ : (x y : ℕ₀) → f (predℕ ( predℕ (fst x + fst y))) ≡ ( predℕ ( fst x + fst y ) , ( predℕ (predℕ (fst x + fst y)) , sumLem (fst x)  (fst y) (snd x) (snd y)) )
l₄ (x , (x⁻ , p)) (y , (y⁻ , q)) = {!refl!}

-- op₂ (x , p)  (y , q) = ( predℕ ( x + y ) , ( predℕ (predℕ (x + y)) , sumLem x  y p q) )


endLemma : op₂' ≡ op₂
endLemma i x y =
  ((((l₁ x y) ∙ l₂ x y) ∙ (l₃ x y)) ∙ (l₄ x y)) i -- predℕ (((fst x) + (fst y)) ≡⟨ ? ⟩ ? ∎
--sym (Univalence.uaβ {!fEquiv!} {!(op₁ (transport (zeroPath i) x) (transport (zeroPath i) y))!}) i


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
     ∙-cong   = λ p q → {! doubleCong (opᵢ i) p q!}
     }
   }
