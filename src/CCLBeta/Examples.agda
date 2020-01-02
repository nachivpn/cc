module CCLBeta.Examples where

open import CCLBeta.Norm
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star)
  renaming (_◅◅_ to trans)
open Star

open import Relation.Binary.PropositionalEquality


--
-- reduction (required!)
--

idf : Tm a (b ⇒ b)
idf = curry snd

silly-fst : Tm (a * b) a
silly-fst = apply ∙ pair idf fst

_ : norm {𝕓 * a} silly-fst ≡ fst
_ = refl

SNat : Ty → Set
SNat a = Tm (a ⇒ a) (a ⇒ a)

zero : SNat a
zero = curry snd

one : SNat a
one = curry apply

two : SNat a
two = curry (apply ∙ pair fst apply)

three : SNat a
three = curry (apply ∙ pair fst (apply ∙ pair fst apply))

toLam : Tm a b → Tm e (a ⇒ b)
toLam t = curry (t ∙ snd)

succ : SNat a → SNat a
succ n = curry (apply ∙ pair (apply ∙ pair (toLam n) fst) (apply ∙ pair fst snd))

-- recursion combinator
rec : Tm e a → Tm e (a ⇒ a) → SNat a → Tm e a
rec b t n = apply ∙ pair (apply ∙ pair (toLam n) t) b

applys : SNat b → Tm ((b ⇒ b) * b) b
applys n = rec snd fst n

_ : norm (applys {𝕓} (succ two)) ≡ norm (applys {𝕓} three)
_ = refl

-- loop combinator
loop : Tm a a → SNat a → Tm a a
loop t n = rec id (toLam t) n

swap : Tm (𝕓 * 𝕓) (𝕓 * 𝕓)
swap = pair snd fst

_ : norm (loop swap zero) ≡ id
_ = refl

_ : norm (loop swap one) ≡ swap
_ = refl

_ : norm (loop swap two) ≡ pair fst snd
_ = refl

_ : norm (loop swap three) ≡ swap
_ = refl

_ : norm (loop swap (succ three)) ≡ norm (loop swap two)
_ = refl

--
-- no contraction (good to have)
--

curry-apply : Tm (a ⇒ b) (a ⇒ b)
curry-apply = curry apply

_ : norm {a ⇒ b} curry-apply ≡ curry-apply
_ = refl

pairfs : Tm (a * b) (a * b)
pairfs = pair fst snd

_ : norm {𝕓 * 𝕓} pairfs ≡ pairfs
_ = refl

--
-- no expansion (good to have)
--

_ : norm {a ⇒ b} id ≡ id
_ = refl

_ : norm {a * b} id ≡ id
_ = refl

_ : norm {𝕓} id ≡ id
_ = refl

_ : norm {𝟙} id ≡ id
_ = refl

_ : norm {𝕓 * 𝕓} fst ≡ fst
_ = refl

_ : norm {(𝕓 ⇒ 𝕓) * 𝕓} apply ≡ apply
_ = refl

--
-- some expansion at application site
--

_ : norm {(𝕓 ⇒ 𝕓) * 𝕓}
         (apply ∙ id) ≡ (apply ∙ pair fst snd)
_ = refl


_ : norm {((𝕓 ⇒ 𝕓) * 𝕓) * a}
         (apply ∙ fst) ≡ (apply ∙ pair (fst ∙ fst) (snd ∙ fst))
_ = refl
