module CCLBetaWeak.Confluence where

open import CCLBetaWeak.CCL
open import CCLBetaWeak.Norm

open import Data.Product
  using (_×_ ; ∃ ; _,_)
open import Relation.Nullary using (¬_)

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_)

-- Defn. of convergence (lower half of "the diamond")
Converge : (t t' : Tm a b) → Set
Converge t t' =  ∃ λ v → (t ⟶* v) × (t' ⟶* v)

-- Defn. of confluence ("the diamond property")
Confluence : (t : Tm a b) → Set
Confluence {a} {b} t = {u u' : Tm a b}
  → t ⟶* u
  → t ⟶* u'
  → Converge u u'

-- CCLBetaWeak is confluent if confluence holds for all terms
Confluent : Set
Confluent = {a b : Ty} (t : Tm a b) → Confluence t

-- Example of terms that don't converge
dontConvergeEx : ¬ (Converge
  (curry (id {𝕓 * 𝕓}))
  (curry (id ∙ pair (id ∙ fst) snd)))
dontConvergeEx (.(curry id) , refl , () ◅ redr)

-- CCLBetaWeak is not confluent
notConfluent : ¬ (Confluent)
notConfluent confluent = dontConvergeEx (confluent (curry id ∙ id)
  (lift red-idr)     -- curry id ∙ id ⟶ curry id
  (lift comp-curry)) -- curry id ∙ id ⟶ curry (id ∙ pair (id ∙ fst) snd)

-- Q: Can we show `notConfluent` using the following (`notSound`)?
--    Are they even related? Feels a bit similar..

-- Def. of soundness of interpretation (eval)
Soundness : Set
Soundness = {a b : Ty} (t t' : Tm a b)
  → t ⟶ t' → eval t ≡ eval t'

-- Example of terms that are interpreted differently
diffInterp : eval (curry (id {𝕓 * 𝕓}) ∙ id) ≢ eval (curry id)
diffInterp ()

-- Interpretation of CCLBetaWeak is not sound
notSound : ¬ Soundness
notSound sound = diffInterp ((sound
  (curry id ∙ id) (curry id) red-idr))
