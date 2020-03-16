module CCLBeta.Confluence where

open import CCLBeta.CCL
open import CCLBeta.Norm

open import Data.Product
  using (_×_ ; ∃ ; _,_)
open import Relation.Nullary using (¬_)

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star)
  renaming (_◅◅_ to trans)

open Star renaming (ε to refl)

private
  variable
    a b c d e : Ty

-- Defn. of convergence (lower half of "the diamond")
Converge : (t t' : Tm a b) → Set
Converge t t' = ∃ λ v → (t ⟶* v) × (t' ⟶* v)

-- Defn. of confluence ("the diamond property")
Confluence : (t : Tm a b) → Set
Confluence {a} {b} t = {u u' : Tm a b}
  → t ⟶* u
  → t ⟶* u'
  → Converge u u'

-- CCLBeta is confluent if confluence holds for all terms
Confluent : Set
Confluent = {a b : Ty} (t : Tm a b) → Confluence t

-- Example of terms that don't converge
dontConvergeEx : ¬ (Converge
  (curry (id {𝕓 * 𝕓}))
  (curry (id ∙ pair (id ∙ fst) snd)))
dontConvergeEx (.(curry id) , refl
  , cong-curry (cong-∙2 (cong-pair1 red-idl))
    ◅ cong-curry red-idl
    ◅ cong-curry (cong-pair1 ()) ◅ _)
dontConvergeEx (.(curry id) , refl
  , cong-curry (cong-∙2 (cong-pair1 red-idl))
    ◅ cong-curry red-idl
    ◅ cong-curry (cong-pair2 ()) ◅ _)
dontConvergeEx (.(curry id) , refl
  , cong-curry (cong-∙2 (cong-pair1 red-idl))
    ◅ cong-curry (cong-∙2 (cong-pair1 ())) ◅ _)
dontConvergeEx (.(curry id) , refl
  , cong-curry (cong-∙2 (cong-pair1 red-idl))
    ◅ cong-curry (cong-∙2 (cong-pair2 ())) ◅ _)
dontConvergeEx (.(curry id) , refl
  , cong-curry red-idl
    ◅ cong-curry (cong-pair1 red-idl)
    ◅ cong-curry (cong-pair1 ()) ◅ _)
dontConvergeEx (.(curry id) , refl
  , cong-curry red-idl
    ◅ cong-curry (cong-pair1 red-idl)
    ◅ cong-curry (cong-pair2 ()) ◅ _)
dontConvergeEx (t , cong-curry () ◅ r1 , r2)

-- CCLBeta is not confluent
notConfluent : ¬ Confluent
notConfluent confluent = dontConvergeEx (confluent (curry id ∙ id)
  (one red-idr)     -- curry id ∙ id ⟶ curry id
  (one comp-curry)) -- curry id ∙ id ⟶ curry (id ∙ pair (id ∙ fst) snd)
