module CCLBeta.Norm where

open import CCLBeta.CCL
open import CCLBeta.Thinning

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

-- normal identity
idn : Nf a a
idn {𝕓}     = id𝕓
idn {𝟙}     = id𝟙
idn {a ⇒ b} = up id⇒
idn {a * b} = id*

-- interpretation of types
Val : Ty → Ty → Set
Val a 𝕓       = Nf a 𝕓
Val a 𝟙       = Nf a 𝟙
Val a (b ⇒ c) = Nf a (b ⇒ c) × ({e : Ty} → e ⊆ a → Val e b → Val e c)
Val a (b * c) = Nf a (b * c) × (Val a b × Val a c)

-- weaken a value (strictly)
wkValPrj : Prj a b → Val b c → Val a c
wkValPrj {c = 𝕓} w v
  = wkNfPrj w v
wkValPrj {c = 𝟙} w v
  = wkNfPrj w v
wkValPrj {c = c ⇒ d} w (n , f)
  = wkNfPrj w n , λ w' x → f (⊆-trans w' (inj₂ w)) x
wkValPrj {c = c * d} w (n , x , y)
  = wkNfPrj w n  , wkValPrj w x , wkValPrj w y

-- weaken a value
wkVal : a' ⊆ a → Val a b → Val a' b
wkVal (inj₁ refl) x = x
wkVal (inj₂ w)   x = wkValPrj w x

-- embed thinning to Ne (only possible for arrow type)
⊆ToNe⇒ : e ⊆ (a ⇒ b) → Ne e (a ⇒ b)
⊆ToNe⇒ (inj₁ refl) = id⇒
⊆ToNe⇒ (inj₂ y)    = embPrjToNe y

-- from semantics to normal forms
reify : Val e a → Nf e a
reify {a = 𝕓}     x       = x
reify {a = 𝟙}     x       = x
reify {a = a ⇒ b} (n , _) = n
reify {a = a * b} (n , _) = n

-- from semantics to terms
quot : Val a b → Tm a b
quot x = embNf (reify x)

-- from neutrals to semantics (via types)
reflect : Ne a b → Val a b
reflect {b = 𝕓}     t = up t
reflect {b = 𝟙}     t = up t
reflect {b = b ⇒ c} t = up t , λ w x → reflect (app∙pair (wkNe w t) (reify x))
reflect {b = b * c} t = up t , reflect (fst∙ t) , reflect (snd∙ t)

-- semantic identity
id' : Val a a
id' {𝕓}     = id𝕓
id' {𝟙}     = id𝟙
id' {a ⇒ b} = up id⇒ , (λ w x → reflect (app∙pair (⊆ToNe⇒ w) (reify x)))
id' {a * b} = id* , reflect fst , reflect snd

-- projections are values (since they can be reflected)
⊆ToVal : e ⊆ a → Val e a
⊆ToVal (inj₁ refl) = id'
⊆ToVal (inj₂ pc)   = reflect (embPrjToNe pc)

app : Val a (b ⇒ c) → ({e : Ty} → e ⊆ a → Val e b → Val e c)
app x = proj₂ x

-- semantic projection fst composition
fst∙' : Val a (b * c) → Val a b
fst∙' (_ , x , _) = x

-- semantic projection snd composition
snd∙' : Val a (b * c) → Val a c
snd∙' (_ , _ , x) = x

-- semantic application composition
apply∙' : Val a ((b ⇒ c) * b) → Val a c
apply∙' (_ , f , x) = app f ⊆-refl x

-- semantic pairing
pair' : Val a b → Val a c → Val a (b * c)
pair' x y = pair (reify x) (reify y) , x , y

-- semantic term composition
eval∙ : Tm a b → Val e a → Val e b
eval∙ id      x = x
eval∙ (t ∙ u) x = eval∙ t (eval∙ u x)
eval∙ unit    x = unit
eval∙ fst     x = fst∙' x
eval∙ snd     x = snd∙' x
eval∙ apply   x = apply∙' x
eval∙ (pair t u) x
  = pair (reify (eval∙ t x)) (reify (eval∙ u x))
  , (eval∙ t x)
  , (eval∙ u x)
eval∙ (curry t) x
  = curry (reify (eval∙ t (pair' (wkVal (inj₂ fst) x) (reflect snd))))
  , λ w y → eval∙ t (pair' (wkVal w x) y)

-- interpretation of terms
eval : Tm a b → Val a b
eval id         = id'
eval (t ∙ u)    = eval∙ t (eval u)
eval fst        = reflect fst
eval snd        = reflect snd
eval unit       = unit
eval apply      = reflect (app∙pair fst (up snd))
eval (pair t u) = pair' (eval t) (eval u)
eval (curry t)  = curry (reify (eval t)) , λ w x → eval∙ t (pair' (⊆ToVal w) x)

-- normalization function
norm : Tm a b → Nf a b
norm t = reify (eval t)
