module CCLBeta.Consistency where

open import CCLBeta.CCL
open import CCLBeta.Norm
open import CCLBeta.Thinning

open import Data.Unit
  using (⊤ ; tt)
open import Data.Empty
  using (⊥)
open import Data.Product
  using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  renaming (ε to refl ; _◅◅_ to trans)

open import Function
  using () renaming (_∘_ to _∘f_) -- function composition

open SetoidUtil

variable
  a b c d e : Ty

-- weakening preserves conversion
wkTm-pres-≈ : {t t' : Tm a b}
  → (w : e ⊆ a)
  → t ≈ t'
  → wkTm w t ≈ wkTm w t'
wkTm-pres-≈ refl    r = r
wkTm-pres-≈ (up pc) r = cong-∙ r refl

-- "Builder" object for building conversion proofs
R : Tm a b → Val a b → Set
R {a} {𝕓}      t x = t ≈ quot x
R {a} {𝟙}      t x = t ≈ quot x
R {a} {b ⇒ c}  t f = t ≈ quot f
  × ({e : Ty} {u : Tm e b} {u' : Val e b}
  → (w : e ⊆ a)
  → R u u'
  → R (apply ∙ pair (wkTm w t) u) (app f w u'))
R {a} {b * c} t x = t ≈ quot x
  × R (fst ∙ t) (fst∙' x)
  × R (snd ∙ t) (snd∙' x)

-- run the builder to extract proof of conversion
R-build : {t : Tm a b} {x : Val a b}
  → R t x
  → t ≈ quot x
R-build {b = 𝕓}     p = p
R-build {b = 𝟙}     p = p
R-build {b = b ⇒ c} p = proj₁ p
R-build {b = b * c} p = proj₁ p

-- chain a proof of conversion with the builder to get a new builder
-- i.e., extend the conversion proof
R-chain : {f g : Tm a b} {x : Val a b}
  → g ≈ f
  → R f x
  → R g x
R-chain {b = 𝕓} g≈f f≈x
  = trans g≈f f≈x
R-chain {b = 𝟙} g≈f f≈x
  = trans g≈f f≈x
R-chain {b = b ⇒ c} g≈f (f≈x , ss)
  = trans g≈f f≈x
  , λ {u} {y} w uRy → R-chain
      (cong-∙ refl (cong-pair (wkTm-pres-≈ w g≈f) refl))
      (ss w uRy)
R-chain {b = b * c} g≈f (f≈x , sc1 , sc2)
  = trans g≈f f≈x
  , R-chain (cong-∙ refl g≈f) sc1
  , R-chain (cong-∙ refl g≈f) sc2


wkTm-pres-id : {t : Tm a b}
    → t ≈ wkTm refl t
wkTm-pres-id = refl

-- Note on terminology: "squashes" is the reverse of "preserves",
-- i.e.,
-- preserves : F (x ⊗ y) ≈ F x ⊗ F y
-- squashes  : F x ⊗ F y ≈  F (x ⊗ y)

embPrjToTm-squashes-∙ : {e' : Ty}
  → (x : Prj e' e) (y : Prj e a)
  → embPrjToTm y ∙ embPrjToTm x  ≈ embPrjToTm (y ∘p x)
embPrjToTm-squashes-∙ fst      y = refl
embPrjToTm-squashes-∙ snd      y = refl
embPrjToTm-squashes-∙ (∙fst x) y = trans
  (sym (reduces assoc)) -- sym ALERT!
  (cong-∙ (embPrjToTm-squashes-∙ x y) refl)
embPrjToTm-squashes-∙ (∙snd x) y = trans
  (sym (reduces assoc)) -- sym ALERT!
  (cong-∙ (embPrjToTm-squashes-∙ x y) refl)

wkTmPrj-squashes-∘f : {e' : Ty} {t : Tm a b}
  → (x : Prj e' e) (y : Prj e a)
 → (wkTmPrj x ∘f wkTmPrj y) t ≈ wkTmPrj (y ∘p x) t
wkTmPrj-squashes-∘f fst y = reduces assoc
wkTmPrj-squashes-∘f snd y = reduces assoc
wkTmPrj-squashes-∘f {t = t} (∙fst x) y = begin⟨ Tms ⟩
  wkTmPrj (∙fst x) (wkTmPrj y t)            ≈⟨ refl ⟩ -- i.e., by definition of wkTmPrj
  (t ∙ embPrjToTm y) ∙ embPrjToTm x ∙ fst   ≈⟨ reduces assoc ⟩
  t ∙ (embPrjToTm y ∙ embPrjToTm x ∙ fst)   ≈⟨ cong-∙ refl (sym (reduces assoc)) ⟩ -- sym ALERT!
  t ∙ ((embPrjToTm y ∙ embPrjToTm x) ∙ fst) ≈⟨ cong-∙ refl (cong-∙ (embPrjToTm-squashes-∙ x y) refl) ⟩
  t ∙ embPrjToTm (y ∘p x) ∙ fst             ≈⟨ refl ⟩  -- i.e., by definition of wkTmPrj
  wkTmPrj (y ∘p ∙fst x) t                    ∎
wkTmPrj-squashes-∘f {t = t}  (∙snd x) y = begin⟨ Tms ⟩ -- same as above, omitting details
  wkTmPrj (∙snd x) (wkTmPrj y t)  ≈⟨ reduces assoc ⟩
  _                               ≈⟨ cong-∙ refl (sym (reduces assoc)) ⟩ -- sym ALERT!
  _                               ≈⟨ cong-∙ refl (cong-∙ (embPrjToTm-squashes-∙ x y) refl) ⟩
  wkTmPrj (y ∘p ∙snd x) t          ∎

wkTm-squashes-∘f : {e' : Ty} {t : Tm a b}
    → (w : e' ⊆ e) (w' : e ⊆ a)
    → (wkTm w ∘f wkTm w') t ≈ wkTm (w' ∘w w) t
wkTm-squashes-∘f refl   refl = refl
wkTm-squashes-∘f (up x) refl = refl
wkTm-squashes-∘f refl   (up x) = refl
wkTm-squashes-∘f (up x) (up y) = wkTmPrj-squashes-∘f x y

postulate

  natEmbNf : (w : e ⊆ a) (n : Nf a b)
    → wkTm w (embNf n) ≈ embNf (wkNf w n)

  natEmbNe : (w : e ⊆ a) (n : Ne a b)
    → wkTm w (embNe n) ≈ embNe (wkNe w n)

-- Lemma : weakening a term (with a projection) is equivalent
-- to applying a substitution (of the projection) to its normal form
wkBySubLem : (pc : Prj e a) (t : Tm a b) (n : Nf a b)
  → t ≈ embNf n
  → wkTm (up pc) t ≈ embNf (subNf (up pc) n)
wkBySubLem pc t n t≈n = begin⟨ Tms ⟩
     wkTmPrj pc t
       ≈⟨ wkTm-pres-≈ (up pc) t≈n ⟩
     wkTmPrj pc (embNf n)
       ≈⟨ natEmbNf (up pc) n ⟩
     embNf (wkNf (up pc) n)
     ∎

-- weaken a builder object with a projection
wkRPrj : (pc : Prj e a) (t : Tm a b) (v : Val a b)
  → R t v
  → R (wkTmPrj pc t) (wkValPrj pc v)
wkRPrj {b = 𝕓} pc t n t≈n
  = wkBySubLem pc t n t≈n
wkRPrj {b = 𝟙} pc t n t≈n
  = wkBySubLem pc t n t≈n
wkRPrj {b = b ⇒ c} pc t (n , _ ) (t≈n , ss)
  = wkBySubLem pc t n t≈n
  , λ {_} {u} {y} w uRy → R-chain
      (cong-∙ refl (cong-pair (wkTm-squashes-∘f w (up pc)) refl))
      (ss (⊆-trans w (up pc)) uRy)
wkRPrj {b = b * c} pc t (n , x , y) (t≈n , fsttRx , sndtRy)
  = wkBySubLem pc t n t≈n
  , R-chain (sym (reduces assoc)) (wkRPrj pc (fst ∙ t) x fsttRx) -- sym ALERT!
  , R-chain (sym (reduces assoc)) (wkRPrj pc (snd ∙ t) y sndtRy) -- sym ALERT!

-- weaken a builder object
wkR : (w : e ⊆ a) (t : Tm a b) (v : Val a b)
  → R t v
  → R (wkTm w t) (wkVal w v)
wkR refl    t v tRv = tRv
wkR (up pc) t v tRv = wkRPrj pc t v tRv
