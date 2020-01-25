module CCLBeta.Thinning where

open import CCLBeta.CCL
  using (Ty ; Tm ; Ne ; Np ; Nf)

open Ty
open Tm
open Ne
open Np
open Nf

variable
  a b c d e Γ : Ty

-- "projection chains"
data _≤₀_ : Ty → Ty → Set where
  fst  : (a * b) ≤₀ a
  snd  : (a * b) ≤₀ b
  ∙fst : a ≤₀ b → (a * c) ≤₀ b
  ∙snd : c ≤₀ b → (a * c) ≤₀ b

-- "thinnings"
data _≤_ : Ty → Ty → Set where
  up≤  : a ≤₀ b → a ≤ b
  pair : d ≤ a → d ≤ b → d ≤ (a * b)

emb≤₀ : a ≤₀ b → Tm a b
emb≤₀ fst = fst
emb≤₀ snd = snd
emb≤₀ (∙fst pc) = emb≤₀ pc ∙ fst
emb≤₀ (∙snd pc) = emb≤₀ pc ∙ snd

emb≤ : a ≤ b → Tm a b
emb≤ (up≤ x) = emb≤₀ x
emb≤ (pair th th') = pair (emb≤ th) (emb≤ th')

-- `Entry Γ a b` represents single constructor (Ne Γ a → Ne Γ b)
data Entry (Γ : Ty) : Ty → Ty → Set where
  fst∙□    : Entry Γ (a * b) a
  snd∙□    : Entry Γ (b * c) c
  app∙⟨□,⟩ : Nf Γ a → Entry Γ (a ⇒ b) b

-- transforms an Entry into a constructor of Ne
neConstr : Entry Γ a b → (Ne Γ a → Ne Γ b)
neConstr fst∙□        n = fst∙ n
neConstr snd∙□        n = snd∙ n
neConstr (app∙⟨□,⟩ e) n = app∙pair n e

-- `Spine Γ a b` represents a constructor chain (Ne Γ a → Ne Γ b)
data Spine (Γ : Ty) : Ty → Ty → Set where
  []  : Spine Γ a a
  _∷_ : Entry Γ a b → Spine Γ b c → Spine Γ a c

-- add an entry to the end of the spine
snoc : Spine Γ a b → Entry Γ b c → Spine Γ a c
snoc []      e = e ∷ []
snoc (d ∷ s) e = d ∷ snoc s e

-- transforms a Spine into a constructor chain of Ne
plugNe : Spine Γ b c → Ne Γ b → Ne Γ c
plugNe []      n = n
plugNe (x ∷ s) n = plugNe s (neConstr x n)

-- generate a spine for projection chains
genSpine : a ≤₀ b → Spine Γ a b
genSpine fst      = fst∙□ ∷ []
genSpine snd      = snd∙□ ∷ []
genSpine (∙fst pc) = fst∙□ ∷ genSpine pc
genSpine (∙snd pc) = snd∙□ ∷ genSpine pc

-- embed projection chains into neutral elements
emb≤₀ToNe : a ≤₀ b → Ne a b
emb≤₀ToNe fst      = fst
emb≤₀ToNe snd      = snd
emb≤₀ToNe (∙fst pc) = plugNe (genSpine pc) fst
emb≤₀ToNe (∙snd pc) = plugNe (genSpine pc) snd

-- thinnings admit "drop"
drop : a ≤ b → (a * c) ≤ b
drop (up≤ pc)      = up≤ (∙fst pc)
drop (pair th th') = pair (drop th) (drop th')

-- thinnings admit "keep"
keep : a ≤ b → (a * c) ≤ (b * c)
keep (up≤ pc)      = pair (up≤ (∙fst pc)) (up≤ snd)
keep (pair th th') = pair (pair (drop th) (drop th')) (up≤ snd)

-- embed thinnings into neutral pairs
emb≤ToNp : a ≤ b → Np a b
emb≤ToNp (up≤ x)       = up (emb≤₀ToNe x)
emb≤ToNp (pair th th') = pair (emb≤ToNp th) (emb≤ToNp th')

-- transforms an Entry into a constructor of Np
-- (note that it triggers some reductions!)
npConstr : Entry Γ b c → Np Γ b → Np Γ c
npConstr e     (up x)     = up (neConstr e x)
npConstr fst∙□ (pair m n) = m
npConstr snd∙□ (pair m n) = n

-- transforms a Spine into a constructor chain of Np
plugNp : Spine Γ b c → Np Γ b → Np Γ c
plugNp [] n = n
plugNp (x ∷ s) n = plugNp s (npConstr x n)

-- Weaken neutrals and normal forms using thinnings

wkNe₀ : Γ ≤₀ a → Ne a b → Ne Γ b
wkNe  : Γ ≤ a  → Ne a b → Np Γ b -- Note the resulting type!
wkNp  : Γ ≤ a  → Np a b → Np Γ b
wkNf  : Γ ≤ a  → Nf a b → Nf Γ b

wkNe₀ pc id⇒      = emb≤₀ToNe pc
wkNe₀ pc (fst∙ n) = fst∙ (wkNe₀ pc n)
wkNe₀ pc (snd∙ n) = snd∙ (wkNe₀ pc n)
wkNe₀ pc fst      = fst∙ (emb≤₀ToNe pc)
wkNe₀ pc snd      = snd∙ (emb≤₀ToNe pc)
wkNe₀ pc (app∙pair n x) = app∙pair (wkNe₀ pc n) (wkNf (up≤ pc) x)

module _ where

  -- transforms a neutral to a spine for weaker inputs ("a thin spine")
  genThnSpine : Ne a b → Γ ≤ a → Spine Γ a b
  genThnSpine id⇒      th = []
  genThnSpine fst      th = fst∙□ ∷ []
  genThnSpine snd      th = snd∙□ ∷ []
  genThnSpine (fst∙ n) th = snoc (genThnSpine n th) fst∙□
  genThnSpine (snd∙ n) th = snoc (genThnSpine n th) snd∙□
  genThnSpine (app∙pair n x) th = snoc (genThnSpine n th) (app∙⟨□,⟩ (wkNf th x))

-- weakens a neutral by first generating a thin spine
-- and then transforming it into a neutral pair
wkNe th n = plugNp (genThnSpine n th) (emb≤ToNp th)

-- weaken a neutral pair by induction
wkNp th (up n)     = wkNe th n
wkNp th (pair m n) = pair (wkNp th m) (wkNp th n)

-- weaken a normal form by induction
wkNf th id𝕓        = up (emb≤ToNp th)
wkNf th id𝟙        = up (emb≤ToNp th)
wkNf th id*        = up (emb≤ToNp th)
wkNf th unit       = unit
wkNf th (up x)     = up (wkNp th x)
wkNf th (pair m n) = pair (wkNf th m) (wkNf th n)
wkNf th (curry n)  = curry (wkNf (keep th) n)
