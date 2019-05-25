{-# OPTIONS --cubical --safe #-}

module AlgebraExamples where

open import Relation.Binary.Core
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Properties
open import Agda.Primitive
open import Algebra
open import Algebra.FunctionProperties.Core -- Op₂

open import Cubical.Core.Everything
open import Cubical.Foundations.Isomorphism -- isotoequiv
open import Cubical.Foundations.Prelude -- ≡ 
open import Cubical.Foundations.Isomorphism -- isotoequiv
open import Algebra.FunctionProperties.Core 
open import Cubical.Foundations.Univalence as Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

--open import Algebra.BooleanAlgebra.⊥

≡equiv : ∀ {a} {A : Set a} → IsEquivalence {a} {a} {A} _≡_
≡equiv = record {refl = refl ; sym = sym ; trans = _∙_ }

cong1 : { x y u v : ℕ} → x ≡ y → u ≡ v → (x + u) ≡ (y + v)
cong1 p1 p2 =   (cong (λ x → (x + (p2 i0))) p1) ∙ ( cong (λ u → (p1 i1) + u) p2)

op₁ : Op₂ ℕ
op₁ = _+_

record myMagma c ℓ :  Set (lsuc (c ⊔ ℓ)) where
  infixl 7 _✧_
  field
    Carrier : Set c
    _✧_     : Op₂ Carrier
--    s       : isSet Carrier


s₁ : myMagma _ lzero 
s₁ = record {
  Carrier = ℕ ;
  _✧_ = op₁
  }

data ⊥ : Set where

data ⊤ : Set where
  true : ⊤

notZero :  ℕ → Set
--notZero n = Σ ℕ (λ m → (n ≡ (suc m)))
notZero zero = ⊥
notZero (suc n) = ⊤

ℕ₀ : Set
ℕ₀ = Σ ℕ (λ n → notZero n)

f : ℕ → ℕ₀ 
f n = (suc n , true )

g : ℕ₀ → ℕ 
g (suc x , _) = x 



-- toℕ : ℕ₀ → ℕ
-- toℕ (n , p) = n

-- sucPredLemma : (n : ℕ) → notZero n → n ≡ suc (predℕ n)
-- sucPredLemma n p = ? -- p ∙ (cong suc (refl ∙ (cong predℕ (sym p))))

-- doubleCong : ∀ {a b} {X Y : Set a} {Z : Set b} {x₁ x₂ : X} {y₁ y₂ : Y}
--               (f : X → Y → Z) → x₁ ≡ x₂ → y₁ ≡ y₂ → f x₁ y₁ ≡ f x₂ y₂    
-- --doubleCong f p q = λ i →  ((cong f p) i) (q i)
-- doubleCong f p q i = cong₂ f p q i



-- sumLem : (x y :  ℕ) → notZero x → notZero y → predℕ (x + y) ≡ suc (predℕ (predℕ (x + y)))
-- sumLem x y p q = ? -- sucPredLemma (predℕ (x + y)) ((x⁻ + y⁻) , (cong predℕ (cong₂ (_+_) snd₁ snd₂)) ∙ (+-suc x⁻ y⁻))



leftInv : (b : ℕ₀) → f (g b) ≡ b
leftInv (suc x , true) = λ i → (suc x , true) 

-- l' (n , (n⁻ , p)) =  λ i → ( (sym p) i , (n⁻  , λ j → p  (~ i ∨ j)))

rightInv : (a : ℕ) → g (f a) ≡ a
rightInv a = refl

-- r' zero = refl
-- r' (suc a) = refl

fEquiv : ℕ ≃ ℕ₀ 
fEquiv = (f ,  isoToIsEquiv (iso f g leftInv rightInv))

gEquiv : ℕ₀ ≃ ℕ
gEquiv = (g , isoToIsEquiv (iso g f rightInv leftInv))

fEq : ℕ ≡ ℕ₀ 
fEq = ua fEquiv

op₂ : Op₂ ℕ₀
op₂ (suc x , _) (suc y , _) = ((suc (x + y))  , true)


s₂ : myMagma _ lzero
s₂ = record {
  Carrier = ℕ₀ ;
  _✧_ = op₂ --;
--  s = transport (λ i → isSet (fEq i)) isSetℕ
  }


-- {-
-- my-s₂ : myMagma _ _
-- my-s₂ = record {
--   Carrier = ℕ₀ ;
--   _✧_ = op₂ ;
--   s = {!!}
--  
-- -}
