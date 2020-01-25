module CCLBeta.Analysis where

open import Data.Unit
  using (⊤ ; tt)
open import Data.Empty
  using (⊥)
open import Relation.Nullary
  using (¬_)
open import Data.Product
  using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)

open import CCLBeta.CCL

-- defn.: "beta rules" (all but the expansive exp-apply∙ rule)
BetaRule : {t t' : Tm a b} → t ⟶ t' → Set
BetaRule red-idl        = ⊤
BetaRule red-idr        = ⊤
BetaRule red-fst        = ⊤
BetaRule red-snd        = ⊤
BetaRule red-apply      = ⊤
BetaRule red-unit       = ⊤
BetaRule assoc          = ⊤
BetaRule comp-pair      = ⊤
BetaRule comp-curry     = ⊤
BetaRule exp-apply      = ⊥ -- not a beta rule!
BetaRule (cong-pair1 p) = BetaRule p
BetaRule (cong-pair2 p) = BetaRule p
BetaRule (cong-∙1 p)    = BetaRule p
BetaRule (cong-∙2 p)    = BetaRule p
BetaRule (cong-curry p) = BetaRule p

-- defn.: beta-normal form
BetaNormal : Tm a b → Set
BetaNormal {a} {b} t = {t' : Tm a b} → ¬ Σ (t ⟶ t') BetaRule

-- lemmas needed for proving that neutrals are
-- in beta-normal form (proof below)

fst∙Lemma : (n : Ne a (b * c))
  → BetaNormal (embNe n)
  → BetaNormal (fst ∙ embNe n)

snd∙Lemma : (n : Ne a (b * c))
  → BetaNormal (embNe n)
  → BetaNormal (snd ∙ embNe n)

app∙pairLemma : (n : Ne a (b ⇒ c)) (m : Nf a b)
  → BetaNormal (embNe (app∙pair n m))

------------------------------------
-- Ne and Nf are in beta-normal form
------------------------------------

neBetaNormal : (n : Ne a b) → BetaNormal (embNe n)
neBetaNormal (fst∙ n) redp {-reduction pair-}
  = fst∙Lemma n (neBetaNormal n) redp
neBetaNormal (snd∙ n) redp
  = snd∙Lemma n (neBetaNormal n) redp
neBetaNormal (app∙pair n x) redp
  = app∙pairLemma n x redp

npBetaNormal : (n : Np a b) → BetaNormal (embNp n)
npBetaNormal (up x) redp
  = neBetaNormal x redp
npBetaNormal (pair m n) (cong-pair1 r , rBeta)
  = npBetaNormal m (r , rBeta)
npBetaNormal (pair m n) (cong-pair2 r , rBeta)
  = npBetaNormal n (r , rBeta)

nfBetaNormal : (n : Nf a b) → BetaNormal (embNf n)
nfBetaNormal (up x) redp
  = npBetaNormal x redp
nfBetaNormal (pair n m) (cong-pair1 r , rBeta)
  = nfBetaNormal n (r , rBeta)
nfBetaNormal (pair n m) (cong-pair2 r , rBeta)
  = nfBetaNormal m (r , rBeta)
nfBetaNormal (curry n) (cong-curry r , rBeta)
  = nfBetaNormal n (r , rBeta)

-- proof of the above lemmas

fst∙Lemma fst f (cong-∙2 r , rBeta) = f (r , rBeta)
fst∙Lemma snd f (cong-∙2 r , rBeta) = f (r , rBeta)
fst∙Lemma (fst∙ n) f (cong-∙2 r , rBeta) = f (r , rBeta)
fst∙Lemma (snd∙ n) f (cong-∙2 r , rBeta) = f (r , rBeta)
fst∙Lemma (app∙pair n x) f (cong-∙2 r , rBeta) = f (r , rBeta)

snd∙Lemma fst f (cong-∙2 r , rBeta) = f (r , rBeta)
snd∙Lemma snd f (cong-∙2 r , rBeta) = f (r , rBeta)
snd∙Lemma (fst∙ n) f (cong-∙2 r , rBeta) = f (r , rBeta)
snd∙Lemma (snd∙ n) f (cong-∙2 r , rBeta) = f (r , rBeta)
snd∙Lemma (app∙pair n x) f (cong-∙2 r , rBeta) = f (r , rBeta)

app∙pairLemma fst m (cong-∙2 (cong-pair2 r) , rBeta)
  = nfBetaNormal m (r , rBeta)
app∙pairLemma fst m (cong-∙1 exp-apply , ())
app∙pairLemma fst m (cong-∙2 (cong-pair1 ()) , rBeta)
app∙pairLemma snd m (cong-∙2 (cong-pair2 r) , rBeta)
  = nfBetaNormal m (r , rBeta)
app∙pairLemma snd m (cong-∙1 exp-apply , ())
app∙pairLemma snd m (cong-∙2 (cong-pair1 ()) , rBeta)
app∙pairLemma (fst∙ n) m (cong-∙2 (cong-pair1 r) , rBeta)
  = fst∙Lemma n (neBetaNormal n) (r , rBeta)
app∙pairLemma (fst∙ n) m (cong-∙2 (cong-pair2 r) , rBeta)
  = nfBetaNormal m (r , rBeta)
app∙pairLemma (fst∙ n) m (cong-∙1 exp-apply , ())
app∙pairLemma (snd∙ n) m (cong-∙2 (cong-pair1 r) , rBeta)
  = snd∙Lemma n (neBetaNormal n) (r , rBeta)
app∙pairLemma (snd∙ n) m (cong-∙2 (cong-pair2 r) , rBeta)
  = nfBetaNormal m (r , rBeta)
app∙pairLemma (snd∙ n) m (cong-∙1 exp-apply , ())
app∙pairLemma id⇒ m (cong-∙2 (cong-pair2 r) , rBeta)
  = nfBetaNormal m (r , rBeta)
app∙pairLemma id⇒ m (cong-∙1 exp-apply , ())
app∙pairLemma id⇒ m (cong-∙2 (cong-pair1 ()) , rBeta)
app∙pairLemma (app∙pair n x) m (cong-∙2 (cong-pair1 r) , rBeta)
  = app∙pairLemma n x (r , rBeta)
app∙pairLemma (app∙pair n x) m (cong-∙2 (cong-pair2 r) , rBeta)
  = nfBetaNormal m (r , rBeta)
app∙pairLemma (app∙pair n x) m (cong-∙1 exp-apply , ())
