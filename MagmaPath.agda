{-# OPTIONS --cubical --safe #-}
module MagmaPath  where

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Properties

open import Function

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

--open import Data.Nat.Solver

open import AlgebraExamples
--open import Cubical.Foundations.HoTT-UF




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

--+-suc : ∀ m n → m + suc n ≡ suc (m + n)


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

-- +-suc : ∀ m n → m + suc n ≡ suc (m + n)
lᵣ : (x⁻ y⁻ : ℕ) → suc (predℕ (predℕ (suc x⁻ + suc y⁻))) ≡ predℕ (suc x⁻ + suc y⁻)
lᵣ zero zero = refl
lᵣ zero (suc y⁻) = refl
lᵣ (suc x⁻) zero = refl
lᵣ (suc x⁻) (suc y⁻) = refl
--   suc (predℕ (predℕ (suc x⁻ + suc y⁻))) ≡⟨ {!!} ⟩
--   predℕ (suc x⁻ + suc y⁻) ∎

lₑ : (x y : ℕ₀) →
  (suc (predℕ ( predℕ (fst x + fst y))) ,
    ( (predℕ ( predℕ ((fst x) + (fst y)))) , refl ))
  ≡
  ( predℕ ( fst x + fst y ) ,
    (predℕ (predℕ (fst x + fst y)) , sumLem (fst x)  (fst y) (snd x) (snd y)) )
lₑ (x , (x⁻ , p)) (y , (y⁻ , q)) = 
  (suc (predℕ (predℕ (x + y))) , predℕ (predℕ (x + y)) , refl)
    ≡⟨ (λ i → (doubleCong (λ u v → (suc (predℕ (predℕ (u + v))))) p q i  , cong₂ (λ u v → predℕ (predℕ (u + v))) p q i , refl)) ⟩
  (suc (predℕ (predℕ ((suc x⁻) + (suc y⁻)))) , predℕ (predℕ (x + y)) , refl)
    ≡⟨ (λ i → (lᵣ x⁻ y⁻ i  , (cong predℕ (lᵣ x⁻ y⁻)) i , refl)) ⟩
  (predℕ (suc x⁻ + suc y⁻) , predℕ ( predℕ (x +  y)) , refl )
    ≡⟨ (λ i → ((doubleCong (λ u v → (predℕ (u + v))) (sym p) (sym q)) i  ,  (cong₂ (λ u v →  predℕ (predℕ (u + v))) (sym p) (sym q)) i , refl)) ⟩
  (predℕ (x + y) , predℕ ( predℕ (x + y)) , sumLem  x y (x⁻ , p) (y⁻ , q) ) ∎

endLemma : op₂' ≡ op₂
endLemma i x y =
  (op₂' x y
       ≡⟨ refl ⟩
   transport fEq (op₁ (transport (sym fEq) x) (transport (sym fEq) y))
       ≡⟨ transpR (op₁  (transport (sym fEq) x) (transport (sym fEq) y)) ⟩
   f (op₁  (transport (sym fEq) x) (transport (sym fEq) y))
       ≡⟨ doubleCong (λ x y → f (op₁ x y)) (transpL x) (transpL y) ⟩
   f (op₁  (g x) (g  y))
       ≡⟨  cong f (l₂' x y) ⟩
   f (predℕ ( predℕ ((fst x) + (fst y))))
       ≡⟨ refl ⟩
   (suc (predℕ ( predℕ ((fst x) + (fst y)))) , (predℕ ( predℕ ((fst x) + (fst y)))) , refl )
       ≡⟨ lₑ x y ⟩
   (predℕ ( fst x + fst y ) , (predℕ (predℕ (fst x + fst y)) , sumLem (fst x)  (fst y) (snd x) (snd y)))
       ≡⟨ refl ⟩
   op₂ x y ∎) i      -- ? ≡⟨ ? ⟩
--  ((((l₁ x y) ∙ l₂ x y) ∙ (l₃ x y)) ∙ (l₄ x y)) i



  --op₂' x y  ≡[ i ]  refl 
    --transport fEq (op₁ (transport (sym fEq) x) (transport (sym fEq) y)) ≡[ i ]  l₁ x y i
    --f (op₁  (transport (sym fEq) x) (transport (sym fEq) y))  ∎


pathLemma : (PathP (λ i → Op₂ (fEq i)) op₁' op₂')  ≡  PathP ((λ i → Op₂ (fEq i))) op₁ op₂
pathLemma = cong₂ (PathP (λ i → Op₂ (fEq i))) startLemma endLemma
-- PathP : ∀ {ℓ} (A : I → Set ℓ) → A i0 → A i1 → Set ℓ

opᵢ : PathP (λ i → Op₂ (fEq i)) op₁ op₂
opᵢ = transport pathLemma opᵢ'
-- the endpoints should be precisely op₁ and op₂

isSetᵢ : (i : I) → isSet (fEq i)
isSetᵢ i = {!transport  (λ j → isSet (fEq (i ∧ j))) isSetℕ!}

algPath : s₁ ≡ s₂
algPath = λ i → record {
   Carrier = (fEq i) ;
   _✧_ = opᵢ i ;
   s = isSetᵢ i
   }
