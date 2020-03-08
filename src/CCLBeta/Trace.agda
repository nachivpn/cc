module CCLBeta.Trace where

open import CCLBeta.CCL
open import CCLBeta.Thinning hiding (⊆-refl)
open import CCLBeta.Norm

open import Data.Unit
  using (⊤ ; tt)
open import Data.Empty
  using (⊥)
open import Data.Product
  using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl; cong ; cong₂; sym)
  renaming (trans to ≡-trans)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  renaming (ε to refl)

private
  variable
    a b c d e a' : Ty

--------------------------
-- Logging reduction trace
--------------------------

pattern ⊆-refl  = inj₁ refl
pattern up-⊆ pc = inj₂ pc

-- deep compose
-- e.g., deep-∙ (f ∙ (g ∙ h)) m ≡ (f ∙ (g ∙ (h ∙ m)))
deep-∙ : Tm b c → Tm a b → Tm a c
deep-∙ id u = u
deep-∙ (t ∙ t') u = t ∙ deep-∙ t' u
deep-∙ fst u = fst ∙ u
deep-∙ snd u = snd ∙ u
deep-∙ (pair t t') u = pair t t' ∙ u
deep-∙ unit u = unit
deep-∙ (curry t) u = curry t ∙ u
deep-∙ apply u = apply ∙ u

wkTmPrj : Prj e a → Tm a b → Tm e b
wkTmPrj fst t       = deep-∙ t fst
wkTmPrj snd t       = deep-∙ t snd
wkTmPrj (∙fst pc) t = deep-∙ t (embPrjToTm (∙fst pc))
wkTmPrj (∙snd pc) t = deep-∙ t (embPrjToTm (∙snd pc))

wkTm : e ⊆ a → Tm a b → Tm e b
wkTm ⊆-refl    t = t
wkTm (up-⊆ pc) t = wkTmPrj pc t

-- a req. for implementing wk-pres-R (see below)
wk-is-deep-∙ : (pc : Prj e a) (t : Tm a b) {u : Tm b c}
  → wkTmPrj pc (u ∙ t) ≡ (u ∙ wkTmPrj pc t)
wk-is-deep-∙ fst t = refl
wk-is-deep-∙ snd t = refl
wk-is-deep-∙ (∙fst pc) t = refl
wk-is-deep-∙ (∙snd pc) t = refl

-- functor laws of wkTm

wkTm-pres-id : {t : Tm a b}
  → wkTm ⊆-refl t ≡ t
wkTm-pres-id = refl

wkTmPrj-pres-∘ : {t : Tm a b} (pc : Prj e a') (pc' : Prj a' a)
  → wkTmPrj (Prj-trans pc pc') t ≡ wkTmPrj pc (wkTmPrj pc' t)
-- TODO

wkTm-pres-∘  : {t : Tm a b} (w1 : e ⊆ a') (w2 : a' ⊆ a)
  → wkTm (w2 ∘ w1) t ≡ wkTm w1 (wkTm w2 t)
wkTm-pres-∘ ⊆-refl    ⊆-refl     = refl
wkTm-pres-∘ ⊆-refl    (up-⊆ pc)  = refl
wkTm-pres-∘ (up-⊆ pc) ⊆-refl     = refl
wkTm-pres-∘ (up-⊆ pc) (up-⊆ pc') = wkTmPrj-pres-∘ pc pc'

wkTmPrj-pres-⟶* : {t t' : Tm a b}
  → (pc : Prj e a)
  → t ⟶* t'
  → wkTmPrj pc t ⟶* wkTmPrj pc t'
-- TODO

-- trace the weakening of terms
wkTm-pres-⟶* : {t t' : Tm a b}
  → (w : e ⊆ a)
  → t ⟶* t'
  → wkTm w t ⟶* wkTm w t'
wkTm-pres-⟶* ⊆-refl    r = r
wkTm-pres-⟶* (up-⊆ pc) r = wkTmPrj-pres-⟶* pc r

-- should really just be equal (≡) ?
tracePrjToNe : (pc : Prj a b)
  → (embPrjToTm pc) ⟶* (embNe (embPrjToNe pc))
tracePrjToNe fst = refl
tracePrjToNe snd = refl
tracePrjToNe (∙fst pc) = {!!} -- TODO
tracePrjToNe (∙snd pc) = {!!} -- TODO


natEmbNf' : (pc : Prj e a)
  → (n : Nf a b)
  → wkTmPrj pc (embNf n) ≡ embNf (wkNfPrj pc n)

-- naturality of embNf?
natEmbNf : (w : e ⊆ a)
  → (n : Nf a b)
  → wkTm w (embNf n) ≡ embNf (wkNf w n)
-- TODO

-- naturality of embNe?
natEmbNe : (w : e ⊆ a)
  → (n : Ne a b)
  → wkTm w (embNe n) ≡ embNe (wkNe w n)
-- TODO

-----------------
-- Trace builder
-----------------

R : Tm a b → Val a b → Set
R {a} {𝕓}      t x = t ⟶* quot x
R {a} {𝟙}      t x = t ⟶* quot x
R {a} {b ⇒ c}  t f = t ⟶* quot f
  × ({e : Ty} {u : Tm e b} {u' : Val e b}
  → (w : e ⊆ a)
  → R u u'
  → R (apply ∙ pair (wkTm w t) u) (app f w u'))
R {a} {b * c} t x = t ⟶* quot x
  × R (fst ∙ t) (fst∙' x)
  × R (snd ∙ t) (snd∙' x)

-- extract trace
R-trace : {t : Tm a b} {x : Val a b}
  → R t x
  → t ⟶* quot x
R-trace {b = 𝕓}     p = p
R-trace {b = 𝟙}     p = p
R-trace {b = b ⇒ c} p = proj₁ p
R-trace {b = b * c} p = proj₁ p

-- chain trace with a builder
R-chain : {f g : Tm a b} {x : Val a b}
  → g ⟶* f
  → R f x
  → R g x
R-chain {b = 𝕓} g⟶*f f⟶*x
  = multi g⟶*f f⟶*x
R-chain {b = 𝟙} g⟶*f f⟶*x
  = multi g⟶*f f⟶*x
R-chain {b = b ⇒ c} g⟶*f (f⟶*x , ss)
  = multi g⟶*f f⟶*x
  , λ {u} {y} w uRy
    → R-chain (cong-∙ refl (cong-pair (wkTm-pres-⟶* w g⟶*f) refl)) (ss w uRy)
R-chain {b = b * c} g⟶*f (f⟶*x , sc1 , sc2)
  = multi g⟶*f f⟶*x
  , R-chain (cong-∙ refl g⟶*f) sc1
  , R-chain (cong-∙ refl g⟶*f) sc2

exp-apply∙ : {u : Tm a ((b ⇒ c) * b)}
    → apply ∙ u ⟶* apply ∙ pair (fst ∙ u) (snd ∙ u)
exp-apply∙ = multi (cong-∙ (one exp-apply) refl)
  (multi (one assoc) (cong-∙ refl (one comp-pair)))

-- trace builder for reflection
R-reflect : (n : Ne a b)
  → R (embNe n) (reflect n)
R-reflect {b = 𝕓} n = refl
R-reflect {b = 𝟙} n = refl
R-reflect {b = b ⇒ c} n = refl , λ {_} {u} {v} w uRv
  → R-chain (cong-∙ refl (cong-pair (zero (natEmbNe w n)) (R-trace uRv))) (R-reflect _)
R-reflect {b = b * c} n = refl , (R-reflect (fst∙ n) , R-reflect (snd∙ n))

-- trace builder for identity
R-id : R {a} id id'
R-id {𝕓} = refl
R-id {𝟙} = refl
R-id {a * b}
  = refl
  , R-chain (one red-idr) (R-reflect fst)
  , R-chain (one red-idr) (R-reflect snd)
R-id {a ⇒ b}
  = refl
  , λ {_} {u} {v} w uRv
    → R-chain (cong-∙ refl (cong-pair (R-w-id⇒ w) (R-trace uRv))) (R-reflect _)
  where
    -- trace the reduction of weakening an identity of arrow type
    R-w-id⇒ : (w : e ⊆ (a ⇒ b))
      → wkTm w id ⟶* embNe (⊆ToNe⇒ w)
    R-w-id⇒ ⊆-refl    = refl
    R-w-id⇒ (up-⊆ pc) = {!pc!} -- TODO

-- trace builder for application
R-apply∙ : {u : Tm e ((a ⇒ b) * a)} {v : Val e ((a ⇒ b) * a)}
  → R u v
  → R (apply ∙ u) (apply∙' v)
R-apply∙ {e} {u = u} {v} (p , (_ , ss) , r)
  = R-chain exp-apply∙ (ss ⊆-refl r)

-- trace builder for pairing
R-pair : {t : Tm a b} {x : Val a b}
  {u : Tm a c} {y : Val a c}
  → R t x
  → R u y
  → R (pair t u) (pair' x y)
R-pair tRx uRy
  = (cong-pair (R-trace tRx) (R-trace uRy))
  , (R-chain (one red-fst) tRx)
  , (R-chain (one red-snd) uRy)

-- weakening preserves R (weaken trace builder)
wkPrj-pres-R : (pc : Prj e a)
  → (t : Tm a b) (x : Val a b)
  → R t x
  → R (wkTmPrj pc t) (wkValPrj pc x)
wkPrj-pres-R {b = 𝕓} pc t n tRx
  = multi (wkTmPrj-pres-⟶* pc tRx) (zero (natEmbNf' pc n))
wkPrj-pres-R {b = 𝟙} pc t n tRx
  = multi (wkTmPrj-pres-⟶* pc tRx) (zero (natEmbNf' pc n))
wkPrj-pres-R {b = b ⇒ c} pc t (n , f) (t⟶*x , ss)
  = multi (wkTmPrj-pres-⟶* pc t⟶*x) (zero (natEmbNf' pc n))
  , λ {_} {u} {v} w uRv → R-chain
    (cong-∙ refl
      (cong-pair
        (zero (sym (wkTm-pres-∘ w (up-⊆ pc))))
        refl))
    (ss (up-⊆ pc ∘ w) uRv)
wkPrj-pres-R {b = b * c} pc t (n , x , y) (t⟶*x , p , q)
  = multi (wkTmPrj-pres-⟶* pc t⟶*x) (zero (natEmbNf' pc n))
  , R-chain (zero (sym (wk-is-deep-∙ pc t))) (wkPrj-pres-R _ _ _ p)
  , R-chain (zero (sym (wk-is-deep-∙ pc t))) (wkPrj-pres-R _ _ _ q)

wk-pres-R : (w : e ⊆ a)
  → (t : Tm a b) (x : Val a b)
  → R t x
  → R (wkTm w t) (wkVal w x)
wk-pres-R ⊆-refl t x tRx   = tRx
wk-pres-R (up-⊆ y) t x tRx = wkPrj-pres-R y t x tRx
