{-# OPTIONS --cubical --safe #-}

module PropertyTransports where

open import AlgebraExamples
open import MagmaPath

open import Cubical.Core.Everything
open import Cubical.Data.Nat.Properties
open import Cubical.Foundations.Prelude

--test1 : (Algebra.Magma._∙_ s₂) ≡ (Algebra.Magma._∙_ (algPath i1))
--test1 = {!!}

isCommutative : ∀  {a l} → (myMagma a l) → Set a
isCommutative m = (x y : (myMagma.Carrier m)) →  ((myMagma._✧_  m) x y) ≡ ((myMagma._✧_  m) y x)

com₁ : isCommutative s₁
com₁ = +-comm

com₂ : isCommutative s₂
com₂ = transport (λ i → isCommutative (algPath i)) com₁
