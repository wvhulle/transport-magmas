{-# OPTIONS --cubical --safe #-}
module MagmaPath  where

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Properties

open import Function

open import Cubical.Core.Everything
open import Cubical.Foundations.Isomorphism -- isotoequiv
open import Cubical.Foundations.Prelude -- ≡ 
open import Cubical.Foundations.Isomorphism -- isotoequiv
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

opᵢ' : PathP (λ i → Op₂ (fEq i))  op₁  op₂'
opᵢ' i x y = transport (sym (zeroPath i))
    (op₁ (transport (zeroPath i) x) (transport (zeroPath i) y))

startLemma : op₁ ≡ op₁'
startLemma i x y = x + (transportRefl y) i

transpR : (z : ℕ) → transport fEq z ≡ f z
transpR z = Univalence.uaβ fEquiv z

transpL : (z : ℕ₀) → transport (sym fEq) z ≡ g z
transpL z = Univalence.uaβ gEquiv z

l₂' : ( x y : ℕ₀) →  op₁ (g x) (g y) ≡ predℕ (predℕ ((fst x) + (fst y)) )
l₂' (x , (x⁻ , p)) (y , (y⁻ , q)) = 
  g (x , x⁻ , p) + g (y , y⁻ , q) ≡⟨ refl ⟩
  x⁻ + y⁻ ≡⟨ refl ⟩
  predℕ (predℕ (suc (suc (x⁻ + y⁻))))  ≡⟨ cong (predℕ ∘ predℕ) ( cong suc (sym (+-suc x⁻  y⁻))) ⟩
  -- predℕ (suc x⁻) + predℕ (suc y⁻) ≡⟨ l₂'' x⁻ y⁻ ⟩
  predℕ (predℕ ((suc x⁻) + (suc y⁻))) ≡⟨ cong (λ z → predℕ (predℕ z)) (cong₂ (_+_) (sym p) (sym q)) ⟩
  predℕ (predℕ (x + y)) ∎


suc-predℕ : (x : ℕ) → suc (predℕ (suc x)) ≡ suc x
suc-predℕ x =
  suc (predℕ (suc x))  ≡⟨ refl ⟩
  (suc x) ∎

predℕ-suc : (x : ℕ) → predℕ (suc x) ≡ x
predℕ-suc x = refl

l₂ : (x⁻ y⁻ : ℕ) → suc (predℕ (predℕ (suc x⁻ + suc y⁻))) ≡ predℕ (suc x⁻ + suc y⁻)
l₂ zero zero = refl
l₂ zero (suc y⁻) = refl
l₂ (suc x⁻) zero = refl
l₂ (suc x⁻) (suc y⁻) = refl

l₃ : (x y : ℕ) → (i : I) → l₂ x y i ≡ suc (predℕ (x + suc y))
l₃ x y i = 
  l₂ x y i
    ≡⟨ (λ j → l₂ x y (i ∧ ~ j)) ⟩
  suc (predℕ (x + suc y)) ∎

l₄ : (x y : ℕ) → x + suc y ≡ suc (predℕ (x + suc y))
l₄ zero zero = refl
l₄ zero (suc y) = refl
l₄ (suc x) zero = refl
l₄ (suc x) (suc y) = refl

l₅ : (x y x⁻ y⁻ : ℕ) → (p : x ≡ suc x⁻) → (q : y ≡ suc y⁻) → (i : I) →
  cong₂ (λ u v → predℕ (u + v)) (λ i₁ → p (~ i₁)) (λ i₁ → q (~ i₁)) i
    ≡
  suc (cong₂ (λ u v → predℕ (predℕ (u + v))) (λ i₁ → p (~ i₁))
      (λ i₁ → q (~ i₁)) i)
l₅ x y x⁻ y⁻ p q i = {!!}


lₑ : (x y : ℕ₀) →
  (ℕ₀ ∋ (suc (predℕ ( predℕ (fst x + fst y))) ,
    ( (predℕ ( predℕ ((fst x) + (fst y)))) , refl {ℓ-zero} {ℕ} {(suc (predℕ ( predℕ (fst x + fst y))))} )))
  ≡
  ( predℕ ( fst x + fst y ) ,
    (predℕ (predℕ (fst x + fst y)) , sumLem (fst x)  (fst y) (snd x) (snd y)) )
lₑ (x , (x⁻ , p)) (y , (y⁻ , q)) = 
  (ℕ₀ ∋ (suc (predℕ (predℕ (x + y))) ,
         predℕ (predℕ (x + y)) ,
         refl {ℓ-zero} {ℕ} {(suc (predℕ ( predℕ (x + y))))}))
    ≡⟨ (λ i → (cong₂ (λ u v → (suc (predℕ (predℕ (u + v))))) p q i ,
               cong₂ (λ u v → predℕ (predℕ (u + v))) p q i ,
               refl {ℓ-zero} {ℕ} {cong₂ (λ u v → (suc (predℕ (predℕ (u + v))))) p q i})) ⟩
  (suc (predℕ (predℕ ((suc x⁻) + (suc y⁻)))) ,
   predℕ (predℕ ((suc x⁻) + (suc y⁻))) ,
   refl)
    ≡⟨ (λ i → (l₂ x⁻ y⁻ i ,
              predℕ (predℕ (suc x⁻ + suc y⁻)) ,
              {!l₃ x⁻ y⁻ i!} )) ⟩
  (predℕ (suc x⁻ + suc y⁻) ,
   predℕ (predℕ (suc x⁻ + suc y⁻)) ,
   l₄ x⁻ y⁻)
    ≡⟨ (λ i → ((cong₂ (λ u v → (predℕ (u + v))) (sym p) (sym q)) i  ,
               (cong₂ (λ u v →  predℕ (predℕ (u + v))) (sym p) (sym q)) i ,
                l₅ x y x⁻ y⁻ p q i )) ⟩
  (predℕ (x + y) ,
   predℕ ( predℕ (x + y)) ,
   sumLem  x y (x⁻ , p) (y⁻ , q) ) ∎

endLemma : op₂' ≡ op₂
endLemma i x y =
  (op₂' x y
       ≡⟨ refl ⟩
   transport fEq (op₁ (transport (sym fEq) x) (transport (sym fEq) y))
       ≡⟨ transpR (op₁  (transport (sym fEq) x) (transport (sym fEq) y)) ⟩
   f (op₁  (transport (sym fEq) x) (transport (sym fEq) y))
       ≡⟨ cong₂ (λ x y → f (op₁ x y)) (transpL x) (transpL y) ⟩
   f (op₁  (g x) (g  y))
       ≡⟨  cong f (l₂' x y) ⟩
   f (predℕ ( predℕ ((fst x) + (fst y))))
       ≡⟨ refl ⟩
   (suc (predℕ ( predℕ ((fst x) + (fst y)))) , (predℕ ( predℕ ((fst x) + (fst y)))) , refl )
       ≡⟨ lₑ x y ⟩
   (predℕ ( fst x + fst y ) , (predℕ (predℕ (fst x + fst y)) , sumLem (fst x)  (fst y) (snd x) (snd y)))
       ≡⟨ refl ⟩
   op₂ x y ∎) i 

pathLemma : (PathP (λ i → Op₂ (fEq i)) op₁' op₂')  ≡  PathP ((λ i → Op₂ (fEq i))) op₁ op₂
pathLemma = cong₂ (PathP (λ i → Op₂ (fEq i))) startLemma endLemma
opᵢ : PathP (λ i → Op₂ (fEq i)) op₁ op₂
opᵢ = transport pathLemma opᵢ'

isSetᵢ : (i : I) → isSet (fEq i)
isSetᵢ i = {!transport  (λ j → isSet (fEq (i ∧ j))) isSetℕ!}

algPath : s₁ ≡ s₂
algPath = λ i → record {
   Carrier = (fEq i) ;
   _✧_ = opᵢ i ;
   s = isSetᵢ i
   }
