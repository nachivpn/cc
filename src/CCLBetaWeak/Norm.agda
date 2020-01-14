module CCLBetaWeak.Norm where

open import CCLBetaWeak.CCL

open import Data.Unit
  using (⊤ ; tt)
open import Data.Empty
  using (⊥)
open import Data.Product
  using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star)
  renaming (_◅◅_ to trans)

open Star renaming (ε to refl)

-- normal identity
idn : Nf a a
idn {𝕓}     = id𝕓
idn {𝟙}     = id𝟙
idn {a ⇒ b} = up id⇒
idn {a * b} = id*

-- interpretation of types
Val : Ty → Ty → Set
Val a 𝕓       = Nf a 𝕓 -- see Note 1
Val a 𝟙       = Nf a 𝟙 -- see Note 2
Val a (b ⇒ c) = Nf a (b ⇒ c) × (Val a b → Val a c) -- see Notes 3 and 4
Val a (b * c) = Nf a (b * c) × (Val a b × Val a c)

----
-- Notes on interpretation:
--
-- 1. (𝕓) We interpret 𝕓 as `Nf a 𝕓` instead of `Ne a b` to preserve `id {𝕓}`
--
-- 2. (𝟙) For the same reason as 1, we interpret 𝟙 as `Nf a 𝟙` instead of ⊤
--
-- 3. (⇒) Changing the first component of interpretation to Tm (a * b) c
-- would force all functions to be constructed by `curry`.
-- A notable consequence of this is that it would require
-- identities to be expanded to `curry apply`---which requires
-- an additional (eta-)rule: `id {_⇒_} ⟶ curry (apply)`
--
-- 4. (⇒) Changing the normal form constructor `curry` to accept
-- a normal form argument (instead of a term) would force
-- full-beta reduction. This also demands a richer interpretation:
-- the second component of interpretation must support weakening (I think)
--
----

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
reflect {b = b ⇒ c} t = up t , λ x → reflect {_} {c} (app∙pair t (reify x))
reflect {b = b * c} t = up t , reflect (fst∙ t) , reflect (snd∙ t)

-- semantic identity
id' : Val a a
id' {𝕓}     = id𝕓
id' {𝟙}     = id𝟙
id' {a ⇒ b} = up id⇒ , (λ x → reflect (app∙pair id⇒ (reify x)))
id' {a * b} = id* , reflect fst , reflect snd

infixr 4 _∘_

-- semantic application
_∘_ : Val a (b ⇒ c) → Val a b → Val a c
(_ , f) ∘ x = f x

-- semantic projection fst composition
fst∙' : Val a (b * c) → Val a b
fst∙' (_ , x , _) = x

-- semantic projection snd composition
snd∙' : Val a (b * c) → Val a c
snd∙' (_ , _ , x) = x

-- semantic application composition
apply∙' : Val a ((b ⇒ c) * b) → Val a c
apply∙' (_ , f , x) = f ∘ x

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
  = curry (t ∙ quot x ⊗ id)
  , λ y → eval∙ t (pair (reify x) (reify y) , x , y)

-- interpretation of terms
eval : Tm a b → Val a b
eval id         = id'
eval (t ∙ u)    = eval∙ t (eval u)
eval fst        = reflect fst
eval snd        = reflect snd
eval unit       = unit
eval apply      = reflect apply
eval (pair t u) = pair' (eval t) (eval u)
eval (curry t)  = (curry t) , λ x → eval∙ t (pair idn (reify x) , id' , x)

-- normalization function
norm : Tm a b → Tm a b
norm t = quot (eval t)

--------------------------
-- Logging reduction trace
--------------------------

-- trace builder
R : Tm a b → Val a b → Set
R {a} {𝕓}      t x = t ⟶* quot x
R {a} {𝟙}      t x = t ⟶* quot x
R {a} {b ⇒ c}  t f = t ⟶* quot f
  × ({u : Tm a b} {u' : Val a b}
  → R u u'
  → R (apply ∙ pair t u) (apply∙' (pair' f u')))
R {a} {b * c} t x = t ⟶* quot x
  × R (fst ∙ t) (fst∙' x)
  × R (snd ∙ t) (snd∙' x)

-- extract trace
R-reduces : {t : Tm a b} {x : Val a b}
  → R t x
  → t ⟶* quot x
R-reduces {b = 𝕓}     p = p
R-reduces {b = 𝟙}     p = p
R-reduces {b = b ⇒ c} p = proj₁ p
R-reduces {b = b * c} p = proj₁ p

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
  , λ {u} {y} uRy
    → R-chain
      (cong-∙ refl (cong-pair g⟶*f refl))
      (ss uRy)
R-chain {b = b * c} g⟶*f (f⟶*x , sc1 , sc2)
  = trans g⟶*f f⟶*x
  , R-chain (cong-∙ refl g⟶*f) sc1
  , R-chain (cong-∙ refl g⟶*f) sc2

-- trace application composition
R-apply∙ : {u : Tm e ((a ⇒ b) * a)} {v : Val e ((a ⇒ b) * a)}
  → R u v
  → R (apply ∙ u) (apply∙' v)
R-apply∙ (p , (q , ss) , r)
  = R-chain (lift exp-apply∙) (ss r)

-- lemma for reducing function application
beta-lemma :
 {t : Tm (b * c) d} {u1 : Tm a b} {u2 : Tm a c }
 → (apply ∙ pair (curry (t ∙ (u1 ⊗ id))) u2)
   ⟶* t ∙ pair u1 u2
beta-lemma = trans
  (lift red-apply)
  (trans
    (lift assoc)
     (cong-∙
       refl
       (trans
         (lift comp-pair)
         (cong-pair
           (trans (lift assoc) (trans (cong-∙ refl (lift red-fst)) (lift red-idr)))
           (trans (lift assoc) (trans (cong-∙ refl (lift red-snd)) (lift red-idl)))))))

-- trace builder for composition
Fund∙ : {a b : Ty} (t : Tm a b) → Set
Fund∙ {a} {b} t = ∀ {e} {u : Tm e a} {v : Val e a}
  → R u v
  → R (t ∙ u) (eval∙ t v)

-- trace composition
fund∙ : (t : Tm a b) → Fund∙ t
fund∙ id         uRv
  = R-chain (lift red-idl) uRv
fund∙ (t ∙ u)    uRv
  = R-chain (lift assoc) (fund∙ t (fund∙ u uRv))
fund∙ fst        (_ , p , _) = p
fund∙ snd        (_ , _ , p) = p
fund∙ (pair t t') uRv
  = trans
      (lift comp-pair)
      (cong-pair
        (R-reduces (fund∙ t uRv))
        (R-reduces (fund∙ t' uRv)))
  , R-chain
      (trans (cong-∙ refl (lift comp-pair)) (lift red-fst))
      (fund∙ t uRv)
  , R-chain
      (trans (cong-∙ refl (lift comp-pair)) (lift red-snd))
      (fund∙ t' uRv)
fund∙ unit       uRv = lift red-unit
fund∙ (curry t)  uRv
  = trans
      (cong-∙ refl (R-reduces uRv))
      (lift comp-curry)
  , λ {u = s} {x} sRx → R-chain
        (trans
          (cong-∙ refl (cong-pair (lift comp-curry) refl))
          beta-lemma)
        (fund∙ t
          ((cong-pair (R-reduces uRv) (R-reduces sRx))
          , ((R-chain (lift red-fst) uRv)
          , (R-chain (lift red-snd) sRx))))
fund∙ apply {u = u} {v = v} uRv
  = R-apply∙ {u = u} {v = v} uRv

-- trace reflection
R-reflect : (n : Ne a b)
  → R (embNf (up n)) (reflect n)
R-reflect {b = 𝕓} n = refl
R-reflect {b = 𝟙} n = refl
R-reflect {b = b ⇒ b₁} n = refl , λ {u = u} {v} uRv
  → R-chain
      (cong-∙ refl (cong-pair refl (R-reduces uRv)))
      (R-reflect (app∙pair n (reify v)))
R-reflect {b = b * b₁} n = refl , (R-reflect (fst∙ n) , R-reflect (snd∙ n))

-- trace identity
R-id : R {a} id id'
R-id {𝕓} = refl
R-id {𝟙} = refl
R-id {a ⇒ b}
  = refl
  , λ {u = u} {v} uRv
    → R-chain
        (cong-∙ refl (cong-pair refl (R-reduces uRv)))
        (R-reflect (app∙pair id⇒ (reify v)))
R-id {a * b}
  = refl
  , R-chain (lift red-idr) (R-reflect fst)
  , R-chain (lift red-idr) (R-reflect snd)

-- identity reduces to normal identity
id⟶*idn : id ⟶* embNf {a} idn
id⟶*idn {𝕓} = refl
id⟶*idn {𝟙} = refl
id⟶*idn {a ⇒ b} = refl
id⟶*idn {a * b} = refl

-- trace pairing
R-pair : {t : Tm a b} {x : Val a b}
  {u : Tm a c} {y : Val a c}
  → R t x
  → R u y
  → R (pair t u) (pair' x y)
R-pair tRx uRy
  = (cong-pair (R-reduces tRx) (R-reduces uRy))
  , (R-chain (lift red-fst) tRx)
  , (R-chain (lift red-snd) uRy)

-- trace interpretation
fund : (t : Tm a b) → R t (eval t)
fund id = R-id
fund (t ∙ u) = fund∙ t (fund u)
fund fst = R-reflect fst
fund snd = R-reflect snd
fund (pair t u) = R-pair (fund t) (fund u)
fund unit = refl
fund (curry t) = refl , (λ {u = u} {v} uRv
  → R-chain
      (lift red-apply)
      (fund∙ t (cong-pair id⟶*idn (R-reduces uRv)
      , R-chain (lift red-fst) R-id
      , R-chain (lift red-snd) uRv)))
fund apply = R-reflect apply

-- trace normalization
trace : (t : Tm a b) → t ⟶* norm t
trace t = R-reduces (fund t)
