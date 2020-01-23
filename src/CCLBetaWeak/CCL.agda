module CCLBetaWeak.CCL where

open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star)
  renaming (_◅◅_ to trans)

open Star renaming (ε to refl)

infixr 5 _⇒_

data Ty : Set where
  𝕓        : Ty
  𝟙        : Ty
  _⇒_  _*_ : (a b : Ty) → Ty

variable
  a b c d e : Ty

infixr 4 _∙_

data Tm : (a b : Ty) → Set where
  id    : Tm a a
  _∙_   : Tm b c → Tm a b → Tm a c
  fst   : Tm (a * b) a
  snd   : Tm (a * b) b
  pair  : Tm a b → Tm a c → Tm a (b * c)
  unit  : Tm a 𝟙
  curry : Tm (c * a) b → Tm c (a ⇒ b)
  apply : Tm ((a ⇒ b) * a) b

_⊗_ : Tm a c → Tm b d → Tm (a * b) (c * d)
t ⊗ u = pair (t ∙ fst) (u ∙ snd)

infix 3 _⟶_
infix 3 _⟶*_

-- single-step reduction
data _⟶_ : Tm a b → Tm a b → Set where

  -- reduction rules
  red-idl  : {f : Tm a b}
    → id ∙ f ⟶ f
  red-idr  : {f : Tm a b}
    → f ∙ id ⟶ f
  red-fst  : {f : Tm a b} {g : Tm a c}
    → fst ∙ (pair f g) ⟶ f
  red-snd  : {f : Tm a b} {g : Tm a c}
    → snd ∙ (pair f g) ⟶ g
  red-apply : {f : Tm (a * b) c} {g : Tm a b}
    → apply ∙ pair (curry f) g ⟶ (f ∙ pair id g)
  red-unit : {f : Tm a b}
    → (unit ∙ f) ⟶ unit

  -- composition rules
  assoc : {f : Tm c d} {g : Tm b c} {h : Tm a b}
    → (f ∙ g) ∙ h ⟶ f ∙ (g ∙ h)
  comp-pair : {f : Tm b c} {g : Tm b d} {h : Tm a b}
    → pair f g ∙ h ⟶ pair (f ∙ h) (g ∙ h)
  comp-curry : {h : Tm d c} {f : Tm (c * a) b}
    → curry f ∙ h ⟶ curry (f ∙ pair (h ∙ fst) snd)

  -- "surjective pairing" restricted to application site
  exp-apply :
    apply {a} {b} ⟶ apply ∙ pair fst snd

  -- congruence rules
  cong-pair1 : {f f' : Tm a b} {g : Tm a c}
    → f ⟶ f'
    → (pair f g) ⟶ (pair f' g)
  cong-pair2 : {f : Tm a b} {g g' : Tm a c}
    → g ⟶ g'
    → (pair f g) ⟶ (pair f g')

  cong-∙1 : {f f' : Tm b c} {g : Tm a b}
    → f ⟶ f'
    → f ∙ g ⟶ f' ∙ g

  cong-∙2 : {f : Tm b c} {g g' : Tm a b}
    → g ⟶ g'
    → f ∙ g ⟶ f ∙ g'

  -- NOTE: there is no congruence rule for curry
  -- since we want weak-head normal forms for functions

-- multi-step reduction
_⟶*_ : Tm a b → Tm a b → Set
_⟶*_ = Star (_⟶_)

-- embed ⟶ to ⟶*
lift : {t t' : Tm a b}
  → t ⟶ t'
  → t ⟶* t'
lift p = p ◅ refl

cong-pair : {f f' : Tm a b} {g g' : Tm a c}
    → f ⟶* f'
    → g ⟶* g'
    → (pair f g) ⟶* (pair f' g')
cong-pair refl refl = refl
cong-pair refl (x ◅ q) = cong-pair2 x ◅ cong-pair refl q
cong-pair (x ◅ p) q = cong-pair1 x ◅ cong-pair p q

cong-∙ : {f f' : Tm b c} {g g' : Tm a b}
  → f ⟶* f'
  → g ⟶* g'
  → f ∙ g ⟶* f' ∙ g'
cong-∙ refl refl = refl
cong-∙ refl (x ◅ q) = cong-∙2 x ◅ cong-∙ refl q
cong-∙ (x ◅ p) q = cong-∙1 x ◅ cong-∙ p q

-- reflectable terms
data Ne : Ty → Ty → Set

-- reifiable terms
data Nf : Ty → Ty → Set

embNe : Ne a b → Tm a b
embNf : Nf a b → Tm a b

data Ne where

  -- fst , snd
  fst      : Ne (a * b) a
  snd      : Ne (a * b) b

  -- fst ∙ n
  fst∙     : Ne a (b * c) → Ne a b

  -- snd ∙ n
  snd∙     : Ne a (b * c) → Ne a c

  -- contract of `curry (apply)`
  id⇒      : Ne (a ⇒ b) (a ⇒ b)

  -- apply ∙ pair n m
  app∙pair : Ne a (b ⇒ c) → Nf a b → Ne a c

data Nf where

  -- embed neutrals to normals
  up    : Ne a b → Nf a b

  -- canonical identity for 𝕓
  id𝕓   : Nf 𝕓 𝕓

  -- contract of unit
  id𝟙   : Nf 𝟙 𝟙

  -- contract of (pair id id)
  id*   : Nf (a * b) (a * b)

  -- value constructors
  unit  : Nf a 𝟙
  pair  : Nf a b → Nf a c → Nf a (b * c)
  curry : Tm (a * b) c → Nf a (b ⇒ c)

embNe fst            = fst
embNe snd            = snd
embNe (fst∙ t)       = fst ∙ embNe t
embNe (snd∙ t)       = snd ∙ embNe t
embNe id⇒            = id
embNe (app∙pair t u) = apply ∙ pair (embNe t) (embNf u)

embNf (up x)     = embNe x
embNf id𝕓        = id
embNf id𝟙        = id
embNf id*        = id
embNf unit       = unit
embNf (pair m n) = pair (embNf m) (embNf n)
embNf (curry t)  = curry t
