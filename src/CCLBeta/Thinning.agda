module CCLBeta.Thinning where

open import CCLBeta.CCL
  using (Ty ; Tm ; Ne ; Nf)

open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl)

open Ty ; open Tm
open Ne ; open Nf

private
  variable
    a b c d e : Ty

-- projections
data Prj : Ty → Ty → Set where
  fst  : Prj (a * b) a
  snd  : Prj (a * b) b
  ∙fst : Prj a b → Prj (a * c) b
  ∙snd : Prj c b → Prj (a * c) b

-- embed projections to terms
embPrjToTm : Prj a b → Tm a b
embPrjToTm fst = fst
embPrjToTm snd = snd
embPrjToTm (∙fst pc) = embPrjToTm pc ∙ fst
embPrjToTm (∙snd pc) = embPrjToTm pc ∙ snd

-- reverse-composition of projections
-- (alt. projections are transitive)
Prj-trans : Prj a b → Prj b c → Prj a c
Prj-trans fst pc' = ∙fst pc'
Prj-trans snd pc' = ∙snd pc'
Prj-trans (∙fst pc) pc' = ∙fst (Prj-trans pc pc')
Prj-trans (∙snd pc) pc' = ∙snd (Prj-trans pc pc')

-- `Entry a b c` represents single constructor (Ne a b → Ne a c)
data Entry (i : Ty) : Ty → Ty → Set where
  fst∙□    : Entry i (a * b) a
  snd∙□    : Entry i (b * c) c
  app∙⟨□,⟩ : Nf i a → Entry i (a ⇒ b) b

-- transforms an Entry into a constructor of Ne
neConstr : Entry a b c → (Ne a b → Ne a c)
neConstr fst∙□        n = fst∙ n
neConstr snd∙□        n = snd∙ n
neConstr (app∙⟨□,⟩ e) n = app∙pair n e

-- `Spine a b c` represents a constructor chain (Ne a b → Ne a c)
data Spine (i : Ty) : Ty → Ty → Set where
  []  : Spine i a a
  _∷_ : Entry i a b → Spine i b c → Spine i a c

-- add an entry to the end of the spine
snoc : Spine a b c → Entry a c d → Spine a b d
snoc []      e = e ∷ []
snoc (d ∷ s) e = d ∷ snoc s e

-- transforms a spine into a constructor of Ne
plugNe : Spine a b c → (Ne a b → Ne a c)
plugNe []      n = n
plugNe (x ∷ s) n = plugNe s (neConstr x n)

-- generate a spine for projections
genSpine : Prj b c → Spine a b c
genSpine fst       = fst∙□ ∷ []
genSpine snd       = snd∙□ ∷ []
genSpine (∙fst pc) = fst∙□ ∷ genSpine pc
genSpine (∙snd pc) = snd∙□ ∷ genSpine pc

-- embed projections into neutral elements
embPrjToNe : Prj a b → Ne a b
embPrjToNe fst      = fst
embPrjToNe snd      = snd
embPrjToNe (∙fst pc) = plugNe (genSpine pc) fst
embPrjToNe (∙snd pc) = plugNe (genSpine pc) snd

-- "substitution" of projections
-- analogous to a substituion made up of only variables
data PSub : Ty → Ty → Set where
  up≤  : Prj a b → PSub a b
  pair : PSub d a → PSub d b → PSub d (a * b)

-- embed substitution into terms
embPSubToTm : PSub a b → Tm a b
embPSubToTm (up≤ x) = embPrjToTm x
embPSubToTm (pair s s') = pair (embPSubToTm s) (embPSubToTm s')

-- substitutions admit "drop"
drop : PSub a b → PSub (a * c) b
drop (up≤ pc)    = up≤ (∙fst pc)
drop (pair s s') = pair (drop s) (drop s')

-- substitutions admit "keep"
keep : PSub a b → PSub (a * c) (b * c)
keep (up≤ pc)      = pair (up≤ (∙fst pc)) (up≤ snd)
keep (pair s s') = pair (pair (drop s) (drop s')) (up≤ snd)

-- "neutral pairs" are normal forms that result
-- from applying a substitution to a neutral
data Np : Ty → Ty → Set where
  up    : Ne a b → Np a b
  pair  : Np a b → Np a c → Np a (b * c)

-- neutral pairs are in normal form
embNpToNf : Np a b → Nf a b
embNpToNf (up x)      = up x
embNpToNf (pair s s') = pair (embNpToNf s) (embNpToNf s')

-- translate substitutions into neutral pairs
subToNp : PSub a b → Np a b
subToNp (up≤ x)     = up (embPrjToNe x)
subToNp (pair s s') = pair (subToNp s) (subToNp s')

-- translate substitutions into normal forms
embSubToNf : PSub a b → Nf a b
embSubToNf s = embNpToNf (subToNp s)

-- transforms an Entry into a constructor of Np
-- (note that it triggers some reductions!)
npConstr : Entry a b c → Np a b → Np a c
npConstr e     (up x)     = up (neConstr e x)
npConstr fst∙□ (pair m n) = m
npConstr snd∙□ (pair m n) = n

-- transforms a spine into a constructor of Np
plugNp : Spine a b c → (Np a b → Np a c)
plugNp [] n = n
plugNp (x ∷ s) n = plugNp s (npConstr x n)

-- substitution lemma for normal forms
subNf : PSub a b → Nf b c → Nf a c
subNf s id*        = embSubToNf s
subNf s id𝕓        = embSubToNf s
subNf s id𝟙        = embSubToNf s
subNf s unit       = unit
subNf s (pair m n) = pair (subNf s m) (subNf s n)
subNf s (curry n)  = curry (subNf (keep s) n)
subNf s (up x)     = subNe s x
  where

  -- generate a spine for the given neutral
  -- (given substitution is applied to normal forms in the neutral)
  genSubSpine : PSub a b → Ne b c → Spine a b c
  genSubSpine s id⇒ = []
  genSubSpine s fst = fst∙□ ∷ []
  genSubSpine s snd = snd∙□ ∷ []
  genSubSpine s (fst∙ n) = snoc (genSubSpine s n) fst∙□
  genSubSpine s (snd∙ n) = snoc (genSubSpine s n) snd∙□
  genSubSpine s (app∙pair n x) = snoc (genSubSpine s n) (app∙⟨□,⟩ (subNf s x))

  -- apply substitution to Ne to generate an Nf
  subNe  : PSub a b → Ne b c → Nf a c
  subNe s n = embNpToNf (plugNp (genSubSpine s n) (subToNp s))

-- pre-compose a projection to normal form
-- i.e., weaken a normal form (strictly)
wkNfPrj : Prj a b → Nf b c → Nf a c
wkNfPrj pc n = subNf (up≤ pc) n

-- pre-compose a projection to neutral elements
-- i.e., weaken a neutral element (strictly)
wkNePrj : Prj a b → Ne b c → Ne a c
wkNePrj pc id⇒      = embPrjToNe pc
wkNePrj pc fst      = fst∙ (embPrjToNe pc)
wkNePrj pc snd      = snd∙ (embPrjToNe pc)
wkNePrj pc (fst∙ n) = fst∙ (wkNePrj pc n)
wkNePrj pc (snd∙ n) = snd∙ (wkNePrj pc n)
wkNePrj pc (app∙pair n x) = app∙pair (wkNePrj pc n) (subNf (up≤ pc) x)

-- weakening relation (or "thinnings")
_⊆_ : Ty → Ty → Set
a ⊆ b = a ≡ b ⊎ (Prj a b)

-- weakening relation is reflexive
⊆-refl : a ⊆ a
⊆-refl = inj₁ refl

-- weakening relation is transitive
⊆-trans : e ⊆ a → a ⊆ b → e ⊆ b
⊆-trans (inj₁ refl) (inj₁ refl) = inj₁ refl
⊆-trans (inj₁ refl) (inj₂ pc)   = inj₂ pc
⊆-trans (inj₂ pc)   (inj₁ refl) = inj₂ pc
⊆-trans (inj₂ pc)   (inj₂ pc')  = inj₂ (Prj-trans pc pc')

-- weaken neutral elements
wkNe : e ⊆ a → Ne a b → Ne e b
wkNe (inj₁ refl) x = x
wkNe (inj₂ pc)   x = wkNePrj pc x

-- weaken normal forms
wkNf : e ⊆ a → Nf a b → Nf e b
wkNf (inj₁ refl) n = n
wkNf (inj₂ pc)   n = wkNfPrj pc n
