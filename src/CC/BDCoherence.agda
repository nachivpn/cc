module CC.BDCoherence (Node : Set) where

-- Reference: I Beylin and P Dybjer (1995)

open import Function
  using ()
  renaming (id to idf ; _∘_ to _∘f_ ; const to constf)

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; subst ; trans ; subst₂ ; sym)

data Ty : Set where
  𝕘    : Node → Ty
  𝕀    : Ty
  _⊗_ : Ty → Ty → Ty

private
  variable
    p q : Node
    a b c d e : Ty

infixr 4 _∙_

data Tm : (a b : Ty) → Set where
  id    : Tm a a
  _∙_   : Tm b c → Tm a b → Tm a c
  fmap  : Tm a b → Tm c d → Tm (a ⊗ c) (b ⊗ d)
  `λ    : Tm (𝕀 ⊗ a) a
  `λ̿   : Tm a (𝕀 ⊗ a)
  ρ     : Tm (a ⊗ 𝕀) a
  ρ̿    : Tm a (a ⊗ 𝕀)
  α     : Tm (a ⊗ (b ⊗ c)) ((a ⊗ b) ⊗ c)
  α̿    : Tm ((a ⊗ b) ⊗ c) (a ⊗ (b ⊗ c))

-- Normal types
data NTy : Set where
  𝕀       : NTy
  𝕘⟨_⟩⊗_  : Node → NTy → NTy

embNTy : NTy → Ty
embNTy 𝕀           = 𝕀
embNTy (𝕘⟨ p ⟩⊗ y) = (𝕘 p) ⊗ (embNTy y)

-- Type denotations
Ty' : Set
Ty' = NTy → NTy

-- Evaluation for types
⟦_⟧ : Ty → Ty'
⟦ 𝕘 p ⟧   = 𝕘⟨ p ⟩⊗_
⟦ 𝕀 ⟧      = idf
⟦ a ⊗ b ⟧ = ⟦ a ⟧ ∘f ⟦ b ⟧

evalTy = ⟦_⟧

reifyTy : Ty' → NTy
reifyTy f = f 𝕀

-- Quote a semantic type
quoteTy : Ty' → Ty
quoteTy f = embNTy (reifyTy f)

-- Normalization for types
normTy : Ty → Ty
normTy a = quoteTy (evalTy a)

private
  variable
    a' b' c' d' e' : NTy

-- Morphisms in category of normal types
𝒩 : NTy → NTy → Set
𝒩 a b = a ≡ b

-- Term denotations
Tm' : Ty → Ty → Set
Tm' a b = {a' : NTy} → 𝒩 (⟦ a ⟧ a') (⟦ b ⟧ a')

-- Evaluate terms
eval : Tm a b → Tm' a b
eval id                 = refl
eval (t ∙ u)            = trans (eval u) (eval t)
eval (fmap {a = a} t u) = subst (λ z → ⟦ a ⟧ z ≡ _) (sym (eval u)) (eval t)
eval `λ                 = refl
eval `λ̿                = refl
eval ρ                  = refl
eval ρ̿                 = refl
eval α                  = refl
eval α̿                 = refl

-- Normal terms (could've just been `id : Nf a a`, sure)
data Nf : Ty → Ty → Set where
  id        : Nf 𝕀 𝕀
  fmap⟨id,_⟩ : Nf a b → Nf (𝕘 p ⊗ a) (𝕘 p ⊗ b)

embNf : Nf a b → Tm a b
embNf id            = id
embNf (fmap⟨id, n ⟩) = fmap id (embNf n)

reify′ : 𝒩 a' b' → Nf (embNTy a') (embNTy b')
reify′ {𝕀}          refl = id
reify′ {𝕘⟨ x ⟩⊗ a'} refl = fmap⟨id, reify′ {a'} refl ⟩

quot′ : Tm' a b → Tm (normTy a) (normTy b)
quot′ f = embNf (reify′ (f {𝕀}))

norm′ : Tm a b → Tm (normTy a) (normTy b)
norm′ {a} {b} t = quot′ {a = a} {b = b} (eval t)
