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
  using (_≡_ ; refl; cong ; cong₂)
  renaming (trans to ≡-trans)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star)
  renaming (_◅◅_ to trans)

open Star renaming (ε to refl)

private
  variable
    a b c d e a' : Ty

--------------------------
-- Logging reduction trace
--------------------------

pattern ⊆-refl  = inj₁ refl
pattern up-⊆ pc = inj₂ pc

wkTm : e ⊆ a → Tm a b → Tm e b
wkTm ⊆-refl t    = t
wkTm (up-⊆ pc) t = t ∙ embPrjToTm pc

-- trace builder
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

-- trace the weakening of terms
traceWkTm : {t t' : Tm a b}
  → (w : e ⊆ a)
  → t ⟶* t'
  → wkTm w t ⟶* wkTm w t'
traceWkTm ⊆-refl   r = r
traceWkTm (up-⊆ pc) r = cong-∙ r refl

-- chain trace with a builder
R-chain : {f g : Tm a b} {x : Val a b}
  → g ⟶* f
  → R f x
  → R g x
R-chain {b = 𝕓} g⟶*f f⟶*x
  = trans g⟶*f f⟶*x
R-chain {b = 𝟙} g⟶*f f⟶*x
  = trans g⟶*f f⟶*x
R-chain {b = b ⇒ c} g⟶*f (f⟶*x , ss)
  = trans g⟶*f f⟶*x
  , λ {u} {y} w uRy
    → R-chain (cong-∙ refl (cong-pair (traceWkTm w g⟶*f) refl)) (ss w uRy)
R-chain {b = b * c} g⟶*f (f⟶*x , sc1 , sc2)
  = trans g⟶*f f⟶*x
  , R-chain (cong-∙ refl g⟶*f) sc1
  , R-chain (cong-∙ refl g⟶*f) sc2

exp-apply∙ : {u : Tm a ((b ⇒ c) * b)}
    → apply ∙ u ⟶* apply ∙ pair (fst ∙ u) (snd ∙ u)
exp-apply∙ = trans (cong-∙ (lift exp-apply) refl)
  (trans (lift assoc) (cong-∙ refl (lift comp-pair)))


-- should really just be equal (≡) ?
tracePrjToNe : (pc : Prj a b)
  → (embPrjToTm pc) ⟶* (embNe (embPrjToNe pc))
tracePrjToNe fst = refl
tracePrjToNe snd = refl
tracePrjToNe (∙fst pc) = {!!} -- TODO
tracePrjToNe (∙snd pc) = {!!} -- TODO


-- TODO
traceWkNfPrj : (n : Nf a b) (pc : Prj e a)
  → (embNf n ∙ embPrjToTm pc) ⟶* embNf (wkNfPrj pc n)

--
traceWkNePrj : (n : Ne a b) (pc : Prj e a)
  → (embNe n ∙ embPrjToTm pc) ⟶* (embNe (wkNePrj pc n))
traceWkNePrj id⇒ pc = trans (lift red-idl) (tracePrjToNe pc)
traceWkNePrj fst pc = cong-∙ refl (tracePrjToNe pc)
traceWkNePrj snd pc = cong-∙ refl (tracePrjToNe pc)
traceWkNePrj (fst∙ n) pc = trans (lift assoc) (cong-∙ refl (traceWkNePrj n pc))
traceWkNePrj (snd∙ n) pc = trans (lift assoc) (cong-∙ refl (traceWkNePrj n pc))
traceWkNePrj (app∙pair n x) pc =
  trans (lift assoc)
    (cong-∙ refl (trans (lift comp-pair)
    (cong-pair (traceWkNePrj n pc) (traceWkNfPrj x pc))))

-- naturality of embNe
natEmbNe : (w : e ⊆ a)
  → (n : Ne a b)
  → wkTm w (embNe n) ⟶* embNe (wkNe w n)
natEmbNe ⊆-refl    n = refl
natEmbNe (up-⊆ pc) n = traceWkNePrj n pc

-- trace builder for reflection
R-reflect : (n : Ne a b)
  → R (embNe n) (reflect n)
R-reflect {b = 𝕓} n = refl
R-reflect {b = 𝟙} n = refl
R-reflect {b = b ⇒ c} n = refl , λ {_} {u} {v} w uRv
  → R-chain (cong-∙ refl (cong-pair (natEmbNe w n) (R-trace uRv))) (R-reflect _)
R-reflect {b = b * c} n = refl , (R-reflect (fst∙ n) , R-reflect (snd∙ n))

-- trace builder for identity
R-id : R {a} id id'
R-id {𝕓} = refl
R-id {𝟙} = refl
R-id {a * b}
  = refl
  , R-chain (lift red-idr) (R-reflect fst)
  , R-chain (lift red-idr) (R-reflect snd)
R-id {a ⇒ b}
  = refl
  , λ {_} {u} {v} w uRv
    → R-chain (cong-∙ refl (cong-pair (R-w-id⇒ w) (R-trace uRv))) (R-reflect _)
  where
    -- trace the reduction of weakening an identity of arrow type
    R-w-id⇒ : (w : e ⊆ (a ⇒ b))
      → wkTm w id ⟶* embNe (⊆ToNe⇒ w)
    R-w-id⇒ ⊆-refl    = refl
    R-w-id⇒ (up-⊆ pc) = trans (lift red-idl) (tracePrjToNe pc)

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
  , (R-chain (lift red-fst) tRx)
  , (R-chain (lift red-snd) uRy)
