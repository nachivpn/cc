module ExpElim.Norm where

open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂) public
open import Data.Sum
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star)
  renaming (_◅◅_ to trans)

open Star renaming (ε to refl)
open _≡_ renaming (refl to ≡-refl)

infixr 5 _⇒_

data Ty : Set where
  𝕓        : Ty
  𝟙        : Ty
  _⇒_  _*_ : (a b : Ty) → Ty

variable
  a b c d e : Ty

infixr 4 _∘_
infixr 4 _∙_

data Tm : (a b : Ty) → Set where
  id    : Tm a a
  _∙_   : Tm b c → Tm a b → Tm a c
  fst   : Tm (a * b) a
  snd   : Tm (a * b) b
  pair  : Tm a b → Tm a c → Tm a (b * c)
  unit  : Tm a 𝟙
  curry : Tm (c * a) b → Tm c (a ⇒ b)
  apply : Tm ((a ⇒ b) * a) b

_⊗_ : Tm a c → Tm b d → Tm (a * b) (c * d)
t ⊗ u = pair (t ∙ fst) (u ∙ snd)

infix 3 _⟶_
infix 3 _⟶*_

-- single-step reduction
data _⟶_ : Tm a b → Tm a b → Set where

  -- reduction rules
  red-idl  : {f : Tm a b}
    → id ∙ f ⟶ f
  red-idr  : {f : Tm a b}
    → f ∙ id ⟶ f
  red-fst  : {f : Tm a b} {g : Tm a c}
    → fst ∙ (pair f g) ⟶ f
  red-snd  : {f : Tm a b} {g : Tm a c}
    → snd ∙ (pair f g) ⟶ g
  red-apply : {f : Tm (a * b) c} {g : Tm a b}
    → apply ∙ pair (curry f) g ⟶ (f ∙ pair id g)
  red-unit : {f : Tm a b}
    → (unit ∙ f) ⟶ unit

  -- composition rules
  assoc : {f : Tm c d} {g : Tm b c} {h : Tm a b}
    → (f ∙ g) ∙ h ⟶ f ∙ (g ∙ h)
  comp-pair : {f : Tm b c} {g : Tm b d} {h : Tm a b}
    → pair f g ∙ h ⟶ pair (f ∙ h) (g ∙ h)
  comp-curry : {h : Tm d c} {f : Tm (c * a) b}
    → curry f ∙ h ⟶ curry (f ∙ (h ⊗ id))

  -- "surjective pairing" restricted to application site
  exp-apply :
      apply {a} {b} ⟶ apply ∙ pair fst snd

  -- congruence rules
  cong-pair1 : {f f' : Tm a b} {g : Tm a c}
    → f ⟶ f'
    → (pair f g) ⟶ (pair f' g)
  cong-pair2 : {f : Tm a b} {g g' : Tm a c}
    → g ⟶ g'
    → (pair f g) ⟶ (pair f g')
  cong-∙1 : {f f' : Tm b c} {g : Tm a b}
    → f ⟶ f'
    → f ∙ g ⟶ f' ∙ g
  cong-∙2 : {f : Tm b c} {g g' : Tm a b}
    → g ⟶ g'
    → f ∙ g ⟶ f ∙ g'

-- multi-step reduction
_⟶*_ : Tm a b → Tm a b → Set
_⟶*_ = Star (_⟶_)

-- embed ⟶ to ⟶*
lift : {t t' : Tm a b}
  → t ⟶ t'
  → t ⟶* t'
lift p = p ◅ refl

cong-pair : {f f' : Tm a b} {g g' : Tm a c}
    → f ⟶* f'
    → g ⟶* g'
    → (pair f g) ⟶* (pair f' g')
cong-pair refl refl = refl
cong-pair refl (x ◅ q) = cong-pair2 x ◅ cong-pair refl q
cong-pair (x ◅ p) q = cong-pair1 x ◅ cong-pair p q

cong-∙ : {f f' : Tm b c} {g g' : Tm a b}
  → f ⟶* f'
  → g ⟶* g'
  → f ∙ g ⟶* f' ∙ g'
cong-∙ refl refl = refl
cong-∙ refl (x ◅ q) = cong-∙2 x ◅ cong-∙ refl q
cong-∙ (x ◅ p) q = cong-∙1 x ◅ cong-∙ p q

-- reflectable terms
data Ne : Ty → Ty → Set

-- reifiable terms
data Nf : Ty → Ty → Set

embNe : Ne a b → Tm a b
embNf : Nf a b → Tm a b

data Ne where

  -- projections
  fst      : Ne (a * b) a
  snd      : Ne (a * b) b

  -- fst ∙ n
  fst∙     : Ne a (b * c) → Ne a b

  -- snd ∙ n
  snd∙     : Ne a (b * c) → Ne a c

  -- contract of `curry (apply)`
  id⇒      : Ne (a ⇒ b) (a ⇒ b)

  -- ≡ apply ∙ pair n m
  app∙pair : Ne a (b ⇒ c) → Nf a b → Ne a c

embNe (fst∙ t)   = fst ∙ embNe t
embNe (snd∙ t)   = snd ∙ embNe t
embNe (app∙pair t u) = apply ∙ pair (embNe t) (embNf u)
embNe fst        = fst
embNe snd        = snd
embNe id⇒        = id

data Nf where

  -- embed neutrals to normals
  up    : Ne a b → Nf a b

  -- canonical identity for 𝕓
  id𝕓   : Nf 𝕓 𝕓

  -- contract of unit
  id𝟙   : Nf 𝟙 𝟙

  -- contract of (pair id id)
  id*   : Nf (a * b) (a * b)

  -- value constructors
  unit  : Nf a 𝟙
  pair  : Nf a b → Nf a c → Nf a (b * c)
  curry : Tm (a * b) c → Nf a (b ⇒ c)

embNf (up x)   = embNe x
embNf unit       = unit
embNf (pair m n) = pair (embNf m) (embNf n)
embNf (curry t)  = curry t
embNf id𝕓 = id
embNf id𝟙 = id
embNf id* = id

-- interpretation of types
Sem : Ty → Ty → Set
Sem a 𝕓       = Nf a 𝕓
Sem a 𝟙       = Nf a 𝟙
Sem a (b ⇒ c) = Nf a (b ⇒ c) × (Sem a b → Sem a c)
Sem a (b * c) = Nf a (b * c) × (Sem a b × Sem a c)

reify : Sem e a → Nf e a
reify {a = 𝕓}     x       = x
reify {a = 𝟙}     x       = x
reify {a = a ⇒ b} (n , _) = n
reify {a = a * b} (n , _) = n

quot : Sem a b → Tm a b
quot x = embNf (reify x)

reflect : Ne a b → Sem a b
reflect {b = 𝕓}     t = up t
reflect {b = 𝟙}     t = up t
reflect {b = b ⇒ c} t = up t , λ x → reflect {_} {c} (app∙pair t (reify x))
reflect {b = b * c} t = up t , reflect (fst∙ t) , reflect (snd∙ t)

-- semantic identity
id' : Sem a a
id' {𝕓}     = id𝕓
id' {𝟙}     = id𝟙
id' {a ⇒ b} = up id⇒ , (λ x → reflect (app∙pair id⇒ (reify x)))
id' {a * b} = id* , reflect fst , reflect snd

-- semantic application
_∘_ : Sem a (b ⇒ c) → Sem a b → Sem a c
(_ , f) ∘ x = f x

-- semantic projection fst composition
fst∙' : Sem a (b * c) → Sem a b
fst∙' (_ , x , _) = x

-- semantic projection snd composition
snd∙' : Sem a (b * c) → Sem a c
snd∙' (_ , _ , x) = x

-- semantic application composition
apply∙' : Sem a ((b ⇒ c) * b) → Sem a c
apply∙' (_ , f , x) = f ∘ x

-- semantic term composition
eval∙ : Tm a b → Sem e a → Sem e b
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

-- semantic projection fst
fst' : Sem (a * b) a
fst' = reflect fst

-- semantic projection snd
snd' : Sem (a * b) b
snd' = reflect snd

-- semantic pairing
pair' : Sem a b → Sem a c → Sem a (b * c)
pair' x y = (pair (reify x) (reify y)) , x , y

-- semantic application
apply' : Sem ((a ⇒ b) * a) b
apply' = reflect (app∙pair fst (up snd))

-- normal identity
idn : Nf a a
idn {𝕓} = id𝕓
idn {𝟙} = id𝟙
idn {a ⇒ b} = up id⇒
idn {a * b} = id*

-- interpretation of terms

eval : Tm a b → Sem a b
eval id      = id'
eval (t ∙ u) = eval∙ t (eval u)
eval fst     = fst'
eval snd     = snd'
eval unit    = unit
eval apply   = apply'
eval (pair t u) = pair' (eval t) (eval u)
eval (curry t) = (curry t) , λ x → eval∙ t (pair idn (reify x) , id' , x)

-- normalization function
norm : Tm a b → Tm a b
norm t = quot (eval t)

--------------------------
-- Logging reduction trace
--------------------------

-- trace builder
R : Tm a b → Sem a b → Set
R {a} {𝕓}      t x = t ⟶* quot x
R {a} {𝟙}      t x = t ⟶* quot x
R {a} {b ⇒ c}  t f = t ⟶* quot f
  × ({u : Tm a b} {u' : Sem a b}
  → R u u'
  → R (apply ∙ pair t u) (apply∙' (pair (reify f) (reify u') , (f , u'))))
R {a} {b * c} t x = t ⟶* quot x
  × R (fst ∙ t) (fst∙' x)
  × R (snd ∙ t) (snd∙' x)

-- extract trace
R-reduces : {t : Tm a b} {x : Sem a b}
  → R t x
  → t ⟶* quot x
R-reduces {b = 𝕓}     p = p
R-reduces {b = 𝟙}     p = p
R-reduces {b = b ⇒ c} p = proj₁ p
R-reduces {b = b * c} p = proj₁ p

-- chain trace with a builder
R-chain : {f g : Tm a b} {x : Sem a b}
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

-- expand term which produces application pair
exp-app∙ : {u : Tm a ((b ⇒ c) * b)}
  → apply ∙ u ⟶* apply ∙ pair (fst ∙ u) (snd ∙ u)
exp-app∙ = trans
  (cong-∙ (lift exp-apply) refl)
  (trans (lift assoc) (lift (cong-∙2 comp-pair)))

-- trace application composition
R-apply∙ : {u : Tm e ((a ⇒ b) * a)} {v : Sem e ((a ⇒ b) * a)}
  → R u v
  → R (apply ∙ u) (apply∙' v)
R-apply∙ (p , (q , ss) , r) =
  R-chain exp-app∙ (ss r)

-- lemma for (a kind of) beta-reduction
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
Fund∙ {a} {b} t = ∀ {e} {u : Tm e a} {v : Sem e a}
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

-- trace projection fst
R-fst : R {a * b} fst fst'
R-fst {𝕓} = refl
R-fst {𝟙} = refl
R-fst {a ⇒ b} = refl , λ {u = u} {v} uRv
  → R-chain
      (cong-∙ refl (cong-pair refl (R-reduces uRv)))
      (R-reflect (app∙pair fst (reify v)))
R-fst {a * b}
  = refl
  , R-reflect (fst∙ fst)
  , R-reflect (snd∙ fst)

-- trace projection snd
R-snd : R {a * b} snd snd'
R-snd {b = 𝕓} = refl
R-snd {b = 𝟙} = refl
R-snd {b = a ⇒ b} = refl , λ {u = u} {v} uRv
  → R-chain
      (cong-∙ refl (cong-pair refl (R-reduces uRv)))
      (R-reflect (app∙pair snd (reify v)))
R-snd {b = a * b}
  = refl
  , R-reflect (fst∙ snd)
  , R-reflect (snd∙ snd)

-- trace pairing
R-pair : {t : Tm a b} {x : Sem a b}
  {u : Tm a c} {y : Sem a c}
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
fund fst = R-fst
fund snd = R-snd
fund (pair t u) = R-pair (fund t) (fund u)
fund unit = refl
fund (curry t) = refl , (λ {u = u} {v} uRv
  → R-chain
      (lift red-apply)
      (fund∙ t (cong-pair id⟶*idn (R-reduces uRv)
      , R-chain (lift red-fst) R-id
      , R-chain (lift red-snd) uRv)))
fund apply = R-chain (lift exp-apply) (R-reflect (app∙pair fst (up snd)))

-- trace normalization
trace : (t : Tm a b) → t ⟶* norm t
trace t = R-reduces (fund t)
