{-# OPTIONS --cubical --safe #-}

module AlgebraExamples where

open import Relation.Binary.Core
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat


open import Algebra
open import Algebra.FunctionProperties.Core -- Op₂



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


s₁ : Magma  _ _
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
