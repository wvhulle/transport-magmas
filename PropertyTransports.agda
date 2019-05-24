{-# OPTIONS --cubical --safe #-}

module PropertyTransports where


open import MagmaPath

--test1 : (Algebra.Magma._∙_ s₂) ≡ (Algebra.Magma._∙_ (algPath i1))
--test1 = {!!}

isCommutative : ∀  {a l} → (Algebra.Magma a l) → Set a
isCommutative m = (x y : (Carrier m)) →  ((Algebra.Magma._∙_  m) x y) ≡ ((Algebra.Magma._∙_  m) y x)

com₁ : isCommutative s₁
com₁ = +-comm

com₂ : isCommutative s₂
com₂ = transport (λ i → isCommutative (algPath i)) com₁
