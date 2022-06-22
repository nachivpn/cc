module CC.CCStar (Node : Set) (Edge : Node → Node → Set) where

open import Relation.Binary.Construct.Closure.Equivalence
  using (EqClosure ; symmetric)
  renaming (isEquivalence to EqClosureIsEquivalence)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; <_,_>)
open import Function
  using ()
  renaming (id to idf ; _∘_ to _∘f_)

data Ty : Set where
  𝕘   : Node → Ty
  _*_ : Ty → Ty → Ty

private
  variable
    p q : Node
    a b c d : Ty

infixr 4 _∙_

data Tm : (a b : Ty) → Set where
  var   : Edge p q → Tm (𝕘 p) (𝕘 q)
  id    : Tm a a
  _∙_   : Tm b c → Tm a b → Tm a c
  fst   : Tm (a * b) a
  snd   : Tm (a * b) b
  pair  : Tm a b → Tm a c → Tm a (b * c)

infix 3 _≈_ _∼_

private
  variable
    f g h : Tm a b

data _∼_ : Tm a b → Tm a b → Set where
  idl-∼         : id ∙ f ∼ f
  idr-∼         : f ∼ f ∙ id
  assoc-∼       : (f ∙ g) ∙ h ∼ f ∙ (g ∙ h)
  fst-pair-∼    : fst ∙ pair f g ∼ f
  snd-pair-∼    : snd ∙ pair f g ∼ f
  pair-fst-snd∼ : f ∼ pair (fst ∙ f) (snd ∙ f)

_≈_  : Tm a b → Tm a b → Set
_≈_ = EqClosure _∼_

data 𝒩 : (a b : Ty) → Set where
  id       : 𝒩 a a
  fst∙     : 𝒩 a (b * c) → 𝒩 a b
  snd∙     : 𝒩 a (b * c) → 𝒩 a c
  var⟨_⟩∙_ : Edge p q → 𝒩 a (𝕘 p) → 𝒩 a (𝕘 q)

data ℳ : (a b : Ty) → Set where
  up   : 𝒩 a (𝕘 p) → ℳ a (𝕘 p)
  pair : ℳ a b → ℳ a c → ℳ a (b * c)

Tm' : Ty → Ty → Set
Tm' a (𝕘 p)   = 𝒩 a (𝕘 p)
Tm' a (b * c) = Tm' a b × Tm' a c

⟦_⟧→̇⟦_⟧ : Ty → Ty → Set
⟦ a ⟧→̇⟦ b ⟧ = {c : Ty} → (Tm' c a → Tm' c b)

eval : Tm a b → ⟦ a ⟧→̇⟦ b ⟧
eval (var x)    = var⟨ x ⟩∙_
eval id         = idf
eval (t ∙ u)    = (eval t) ∘f (eval u)
eval fst        = proj₁
eval snd        = proj₂
eval (pair t u) = < eval t , eval u >

reflect : 𝒩 a b → Tm' a b
reflect {b = 𝕘 x}    n = n
reflect {b = b * c}  n = reflect (fst∙ n) , reflect (snd∙ n)

reify : Tm' a b → ℳ a b
reify {b = 𝕘 x}   z = up z
reify {b = b * c} z = pair (reify (proj₁ z)) (reify (proj₂ z))

emb𝒩 : 𝒩 a b → Tm a b
emb𝒩 id           = id
emb𝒩 (fst∙ n)     = fst ∙ emb𝒩 n
emb𝒩 (snd∙ n)     = snd ∙ emb𝒩 n
emb𝒩 (var⟨ x ⟩∙ m) = var x ∙ emb𝒩 m

embℳ : ℳ a b → Tm a b
embℳ (up n)      = emb𝒩 n
embℳ (pair m m') = pair (embℳ m) (embℳ m')

quot : ⟦ a ⟧→̇⟦ b ⟧ → Tm a b
quot f = embℳ (reify (f (reflect id)))

norm : Tm a b → Tm a b
norm t = quot (eval t)
