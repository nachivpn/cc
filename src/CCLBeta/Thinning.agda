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
    a b c d e Γ : Ty

-- "projection chains"
data _⊂_ : Ty → Ty → Set where
  fst  : (a * b) ⊂ a
  snd  : (a * b) ⊂ b
  ∙fst : a ⊂ b → (a * c) ⊂ b
  ∙snd : c ⊂ b → (a * c) ⊂ b

-- embed projection chains to terms
emb⊂ToTm : a ⊂ b → Tm a b
emb⊂ToTm fst = fst
emb⊂ToTm snd = snd
emb⊂ToTm (∙fst pc) = emb⊂ToTm pc ∙ fst
emb⊂ToTm (∙snd pc) = emb⊂ToTm pc ∙ snd

⊂-trans : a ⊂ b → b ⊂ c → a ⊂ c
⊂-trans fst pc' = ∙fst pc'
⊂-trans snd pc' = ∙snd pc'
⊂-trans (∙fst pc) pc' = ∙fst (⊂-trans pc pc')
⊂-trans (∙snd pc) pc' = ∙snd (⊂-trans pc pc')

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
genSpine : a ⊂ b → Spine Γ a b
genSpine fst       = fst∙□ ∷ []
genSpine snd       = snd∙□ ∷ []
genSpine (∙fst pc) = fst∙□ ∷ genSpine pc
genSpine (∙snd pc) = snd∙□ ∷ genSpine pc

-- embed projection chains into neutral elements
emb⊂ToNe : a ⊂ b → Ne a b
emb⊂ToNe fst      = fst
emb⊂ToNe snd      = snd
emb⊂ToNe (∙fst pc) = plugNe (genSpine pc) fst
emb⊂ToNe (∙snd pc) = plugNe (genSpine pc) snd

-- "thinnings"
data Th : Ty → Ty → Set where
  up≤  : a ⊂ b → Th a b
  pair : Th d a → Th d b → Th d (a * b)

-- embed thinnings into terms
embThToTm : Th a b → Tm a b
embThToTm (up≤ x) = emb⊂ToTm x
embThToTm (pair th th') = pair (embThToTm th) (embThToTm th')

-- thinnings admit "drop"
drop : Th a b → Th (a * c) b
drop (up≤ pc)      = up≤ (∙fst pc)
drop (pair th th') = pair (drop th) (drop th')

-- thinnings admit "keep"
keep : Th a b → Th (a * c) (b * c)
keep (up≤ pc)      = pair (up≤ (∙fst pc)) (up≤ snd)
keep (pair th th') = pair (pair (drop th) (drop th')) (up≤ snd)

-- Intermediate data type to collect residual
-- pairs from thinning a neutral
data Np : Ty → Ty → Set where
  up    : Ne a b → Np a b
  pair  : Np a b → Np a c → Np a (b * c)

-- neutral pairs are in normal forms
embNpToNf : Np a b → Nf a b
embNpToNf (up x)        = up x
embNpToNf (pair th th') = pair (embNpToNf th) (embNpToNf th')

-- translate thinnings into neutral pairs
thToNp : Th a b → Np a b
thToNp (up≤ x)       = up (emb⊂ToNe x)
thToNp (pair th th') = pair (thToNp th) (thToNp th')

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

-- thinning lemma for normal forms
thNf   : Th Γ a → Nf a b → Nf Γ b
thNf th id*        = embNpToNf (thToNp th)
thNf th id𝕓        = embNpToNf (thToNp th)
thNf th id𝟙        = embNpToNf (thToNp th)
thNf th unit       = unit
thNf th (pair m n) = pair (thNf th m) (thNf th n)
thNf th (curry n)  = curry (thNf (keep th) n)
thNf th (up x)     = embNpToNf (thNe th x)
  where

  -- transforms a neutral to a spine for weaker inputs ("a thin spine")
  genThnSpine : Ne a b → Th Γ a → Spine Γ a b
  genThnSpine id⇒      th = []
  genThnSpine fst      th = fst∙□ ∷ []
  genThnSpine snd      th = snd∙□ ∷ []
  genThnSpine (fst∙ n) th = snoc (genThnSpine n th) fst∙□
  genThnSpine (snd∙ n) th = snoc (genThnSpine n th) snd∙□
  genThnSpine (app∙pair n x) th = snoc (genThnSpine n th) (app∙⟨□,⟩ (thNf th x))

  -- thinning lemma for neutrals
  -- implemented by first generating a thin spine
  -- and then evaluating it to a neutral *pair* (Np)
  thNe  : Th Γ a → Ne a b → Np Γ b
  thNe th n = plugNp (genThnSpine n th) (thToNp th)

-- weaken normal forms (strictly)
wkNf⊂ : Γ ⊂ a → Nf a b → Nf Γ b
wkNf⊂ pc n = thNf (up≤ pc) n

-- weaken neutral elements (strictly)
wkNe⊂ : Γ ⊂ a → Ne a b → Ne Γ b
wkNe⊂ pc id⇒      = emb⊂ToNe pc
wkNe⊂ pc fst      = fst∙ (emb⊂ToNe pc)
wkNe⊂ pc snd      = snd∙ (emb⊂ToNe pc)
wkNe⊂ pc (fst∙ n) = fst∙ (wkNe⊂ pc n)
wkNe⊂ pc (snd∙ n) = snd∙ (wkNe⊂ pc n)
wkNe⊂ pc (app∙pair n x) = app∙pair (wkNe⊂ pc n) (thNf (up≤ pc) x)

-- weakening relation
_⊆_ : Ty → Ty → Set
a ⊆ b = a ≡ b ⊎ (a ⊂ b)

-- weakening relation is reflexive
⊆-refl : a ⊆ a
⊆-refl = inj₁ refl

-- weakening relation is transitive
⊆-trans : e ⊆ a → a ⊆ b → e ⊆ b
⊆-trans (inj₁ refl) (inj₁ refl) = inj₁ refl
⊆-trans (inj₁ refl) (inj₂ pc)   = inj₂ pc
⊆-trans (inj₂ pc)   (inj₁ refl) = inj₂ pc
⊆-trans (inj₂ pc)   (inj₂ pc')  = inj₂ (⊂-trans pc pc')

-- weaken neutral elements
wkNe : e ⊆ a → Ne a b → Ne e b
wkNe (inj₁ refl) x = x
wkNe (inj₂ pc)   x = wkNe⊂ pc x

-- weaken normal forms
wkNf : e ⊆ a → Nf a b → Nf e b
wkNf (inj₁ refl) n = n
wkNf (inj₂ pc)   n = wkNf⊂ pc n
