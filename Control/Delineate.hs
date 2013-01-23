{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
module Control.Delineate where

import Data.Void

import Control.Delineate.Category

import Prelude hiding ((.), id, curry, uncurry, fst, snd)
import qualified Prelude as P

infix 0 ⊢
infixr 1 ⊸
infixr 4 ⊕
infixr 5 &
infixr 6 ⅋
infixr 7 ⊗



newtype Lin f g = Lin { getLin :: forall r. Not g r -> Not f r }
type (⊢) = Lin

instance Category Lin where
    id = Lin id
    Lin g . Lin f = Lin (f . g)


-- | The negation of @A@ is represented by a function taking an argument of 
--   type @A@ and returning the ambient "result" type, which stands in for ⊥.
newtype Not f r = Not { getNot :: f r -> r }


-- | A wrapper is required for plain values, since everything is kind @* -> *@
--   because of the ambient "result" type, which is simply ignored in this case.
newtype Var x r = Var { getVar :: x }

type instance Dualizer Lin = Bot
type instance Neg Lin = Not
instance StarAut Lin where
    fromNeg = unitR
    toNeg = ununitR
    dneg = dnegLin
    undneg = undnegLin

-- | Double negation all across the sky! :D
dnegLin :: x ⊢ Not (Not x)
dnegLin = Lin (\(Not k) -> Not $ \x -> k . Not $ \(Not kx) -> kx x)

undnegLin :: Not (Not x) ⊢ x
undnegLin = Lin (\x -> Not $ \(Not kx) -> kx x)


-- | Everything on the left is in a sense implicitly negated, so negation lets us
--   move things from one side to the other.
negL :: (x ⊗ y ⊢ z) -> (y ⊢ Not x ⅋ z)
negL (Lin f) = Lin (\(Not k) -> Not $ 
    \y -> k . Par . Not $ 
        \(Mult (Not nnx, z)) -> nnx . Not $ 
            \x -> getNot (f z) . Mult $ (x, y))

unnegL :: (Not x ⊗ y ⊢ z) -> (y ⊢ x ⅋ z)
unnegL f = (undneg `par` id) . negL f

negR :: (y ⊢ x ⅋ z) -> (Not x ⊗ y ⊢ z)
negR (Lin f) = Lin (\kz -> Not $ 
    \(Mult (kx,y)) -> getNot (f . Not $ \(Par (Not kxz)) -> kxz . Mult $ (kx, kz)) y)

unnegR :: (y ⊢ Not x ⅋ z) -> (x ⊗ y ⊢ z)
unnegR f = negR f . (dneg `tensor` id)

neg :: (x ⊢ y) -> (Not y ⊢ Not x)
neg (Lin f) = Lin (\(Not k) -> Not $ k . f)

unneg :: (Not y ⊢ Not x) -> (x ⊢ y)
unneg f = undneg . neg f . dneg


-- --------------------------------------------------------------------------
-- | &, pronounced "with", is the additive conjunction.
--   Given "A & B" both A and B can be true, but not at the same time.
--   Note that this is *not* the same as the usual product type, but it is
--   the categorical product in this setting.
newtype With f g r = With { getWith :: Not (Plus (Not f) (Not g)) r }
type (&) = With

fstWith :: x & y ⊢ x
fstWith = Lin (\k -> Not $ \(With (Not xy)) -> xy . Plus $ Left k )

sndWith :: x & y ⊢ y
sndWith = Lin (\k -> Not $ \(With (Not xy)) -> xy . Plus $ Right k )

pairWith :: (x ⊢ y) -> (x ⊢ z) -> (x ⊢ y & z)
pairWith (Lin f) (Lin g) = Lin (\(Not k) -> Not $ 
    \x -> k . With . Not $ 
        either (flip getNot x . f)  (flip getNot x . g) . getPlus)

type instance Prod Lin = With
instance Product Lin where
    fst = fstWith
    snd = sndWith
    pair = pairWith

-- --------------------------------------------------------------------------
-- | ⊤ is the identity for & and represents a sort of "vacuous truth". 
--   It's defined here as the negation of 0 for the sake of tidy duality, but 
--   using "exists a. a" would probably get the idea across better: you can
--   always produce a value of type ⊤, but given one you can't actually do 
--   anything with it.
newtype Top r = Top (Not Zero r)

-- introduction rules for ⊤. no special elimination rules, just use the product projections
ltop :: x ⊢ Top & x
ltop = Lin (\(Not k) -> Not $ 
    \x -> k . With . Not $ 
        \(Plus kx) -> either (\(Not kt) -> kt . Top . Not $ absurd . getZero) (($ x) . getNot) kx)

rtop :: x ⊢ x & Top
rtop = swap . ltop

assocWithL :: x & (y & z) ⊢ (x & y) & z
assocWithL = Lin $ \(Not k) -> Not $ 
        \(With (Not xyz)) ->  k . With . Not $ either 
            (\(Not kxy) -> kxy . With . Not $ either
                (xyz . Plus . Left)
                (\ky -> xyz . Plus . Right . Not $ \(With (Not yz)) -> yz . Plus $ Left ky)
                . getPlus)
            (\kz -> xyz . Plus . Right . Not $ \(With (Not yz)) -> yz . Plus $ Right kz)
            . getPlus


wswap = sndWith `pairWith` fstWith

type instance Id With = Top
instance Monoidal Lin With where
    (***) f g = pairWith (f . fstWith) (g . sndWith)
    unitL = ltop
    unitR = rtop
    ununitL = sndWith
    ununitR = fstWith
    assocL = assocWithL

instance Symmetric Lin With where
    swap = wswap


-- | Additive truth annihilates multiplicative disjunction
--   Note that @⊢ ⊤@ is a special case of this, @1 ⊢ ⊤ & ⊥@
pltop :: x ⊢ Top ⅋ y
pltop = Lin (\(Not k) -> Not $ 
    \x -> k . Par . Not $ 
        \(Mult (Not kt, Not ky)) -> kt . Top . Not $ \z -> ky $ absurd (getZero z) x)

prtop :: x ⊢ y ⅋ Top
prtop = swap . pltop

-- | ¬⊤ ≡ 0
negtop :: Not Top ⊢ Zero
negtop = Lin (\k -> Not $ \kt -> getNot kt $ Top k)


-- De Morgan's laws for &
dmwith :: Not (x & y) ⊢ Not x ⊕ Not y
dmwith = Lin (\k -> Not $ \(Not xy) -> xy $ With k)

undmwith :: Not x & Not y ⊢ Not (x ⊕ y)
undmwith = Lin (\(Not k) -> Not $ \(With (Not xy)) -> k . Not $ either 
    (\x -> xy . Plus . Left . Not $ ($ x) . getNot)
    (\y -> xy . Plus . Right . Not $ ($ y) . getNot)
    . getPlus)



-- --------------------------------------------------------------------------
-- | ⊕, read "plus", is the additive disjunction.
--   Given "A ⊕ B" either A or B is true, but you don't know which.
--   This pretty much behaves like the usual sum type, and it is the
--   categorical coproduct as well.
newtype Plus f g r = Plus { getPlus :: Either (f r) (g r) }
type (⊕) = Plus

inlPlus :: x ⊢ x ⊕ y
inlPlus = Lin (\(Not k) -> Not $ k . Plus . Left)

inrPlus :: y ⊢ x ⊕ y
inrPlus = Lin (\(Not k) -> Not $ k . Plus . Right)

copairPlus :: (y ⊢ x) -> (z ⊢ x) -> (y ⊕ z ⊢ x)
copairPlus (Lin f) (Lin g) = Lin (\k -> Not $ either (getNot $ f k) (getNot $ g k) . getPlus)


type instance Sum Lin = Plus
instance Coproduct Lin where
    inl = inlPlus
    inr = inrPlus
    copair = copairPlus

-- --------------------------------------------------------------------------
-- | 0 is the identity for ⊕ and is false in the same useless way that ⊤ is true.
--   You can never produce a value of type 0, but if *given* such a value you can
--   do anything at all (much like zombo.com). Defined here as Void to make it 
--   clear that it's uninhabited, but "forall a. a" would be more to the point.
newtype Zero r = Zero { getZero :: Void }

type instance Id Plus = Zero
instance Monoidal Lin Plus where
    (***) = plus
    unitL = inrPlus
    unitR = inlPlus
    ununitL = lzero
    ununitR = rzero
    assocL = assocPlusL

instance Symmetric Lin Plus where
    swap = cswap


-- elimination rules for 0. no special introduction rules, just use the coproduct injections
lzero :: Zero ⊕ x ⊢ x
lzero = Lin (\(Not k) -> Not $ either (absurd . getZero) k . getPlus)

rzero :: x ⊕ Zero ⊢ x
rzero = Lin (\(Not k) -> Not $ either k (absurd . getZero) . getPlus)

assocPlusL :: x ⊕ (y ⊕ z) ⊢ (x ⊕ y) ⊕ z
assocPlusL = Lin $ \(Not k) -> Not $ either 
    (k . Plus . Left . Plus . Left) 
    (either (k . Plus . Left . Plus . Right) (k . Plus . Right) . getPlus) 
    . getPlus

plus :: (w ⊢ x) -> (y ⊢ z) -> (w ⊕ y ⊢ x ⊕ z)
plus f g = copairPlus (inlPlus . f) (inrPlus . g)

-- commutativity
-- | The "c" here stands for "coproduct" because "p" was used for ⅋.
--   ...yeah. Sorry about the terrible names.
cswap :: x ⊕ y ⊢ y ⊕ x
cswap = inrPlus `copairPlus` inlPlus


-- | ¬0 ≡ ⊤
negzero :: Not Zero ⊢ Top
negzero = Lin (\k -> Not $ getNot k . Top)

-- De Morgan's laws for ⊕
dmplus :: Not (x ⊕ y) ⊢ Not x & Not y
dmplus = Lin (\(Not k) -> Not $ 
    \(Not f) -> k . With . Not $ 
        either (\(Not x) -> x . Not $ f . Plus . Left) 
               (\(Not y) -> y . Not $ f . Plus . Right) . getPlus )

undmplus :: Not x ⊕ Not y ⊢ Not (x & y)
undmplus = Lin (\(Not k) -> Not $ \xy' -> k . Not $ \(With (Not xy)) -> xy xy' )


-- --------------------------------------------------------------------------
-- | ⊗, read "times" or "tensor", is the multiplicative conjunction.
--   Given "A ⊗ B" both A and B are true and you're stuck with them.
--   This basically behaves like the usual tuples, and fills the same role
--   in regards to currying &c. It isn't a categorical product, however.
newtype Mult f g r = Mult { getMult :: (f r, g r) }
type (⊗) = Mult


-- bifunctor map
tensor :: (w ⊢ x) -> (y ⊢ z) -> (w ⊗ y ⊢ x ⊗ z)
tensor (Lin f) (Lin g) = Lin (
    \(Not k) -> Not $ 
        \(Mult (kx,ky)) -> flip (getNot . f) kx . Not $ 
            \x -> flip (getNot . g) ky . Not $ \y -> k . Mult $ (x, y) )

-- commutativity
tswap :: x ⊗ y ⊢ y ⊗ x
tswap = Lin (\(Not k) -> Not $ \(Mult (y,x)) -> k $ Mult (x, y))

-- associativity
tassocl :: x ⊗ (y ⊗ z) ⊢ (x ⊗ y) ⊗ z
tassocl = Lin (\(Not k) -> Not $ \(Mult (x, Mult (y, z))) -> k $ Mult (Mult (x, y), z))

tassocr :: (x ⊗ y) ⊗ z ⊢ x ⊗ (y ⊗ z)
tassocr = Lin (\(Not k) -> Not $ \(Mult (Mult (x, y), z)) -> k $ Mult (x, Mult (y, z)))

-- | 1 is the identity for ⊗ and a sort of "trivial truth", representing an empty 
--   antecedent or uninteresting consequent. For the most part it behaves like ().
data Unit r = Unit

-- left and right introduction/elimination rules for 1
unitMultL :: x ⊢ Unit ⊗ x
unitMultL = Lin (\(Not k) -> Not $ \x -> k $ Mult (Unit, x))

unitMultR :: x ⊢ x ⊗ Unit
unitMultR = tswap . unitMultL

cancelUnitL :: Unit ⊗ x ⊢ x
cancelUnitL = Lin (\(Not k) -> Not $ \(Mult (Unit, x)) -> k x)

cancelUnitR :: x ⊗ Unit ⊢ x
cancelUnitR = cancelUnitL . swap

type instance Id Mult = Unit
instance Monoidal Lin Mult where
    (***) = tensor
    unitL = unitMultL
    unitR = unitMultR
    ununitL = cancelUnitL
    ununitR = cancelUnitR
    assocL = tassocl
    assocR = tassocr

instance Symmetric Lin Mult where
    swap = tswap


-- | ¬1 ≡ ⊥
negunit :: Not Unit ⊢ Bot
negunit = Lin (\(Not k) -> Not $ k . Bot)

-- | Turn a multiplicative contradiction into multiplicative falsehood. Note 
--   that this is a perfectly reasonable and useful operation (specifically, 
--   it's function application).
tcancel :: x ⊗ Not x ⊢ Bot
tcancel = Lin (\(Not k) -> Not $ 
    \(Mult (x, Not kx)) -> k . Bot . Not $ 
        \Unit -> kx x)

-- De Morgan's laws for ⊗
-- man, these names are terrible.
dmtensor :: Not (x ⊗ y) ⊢ Not x ⅋ Not y
dmtensor = Lin (\(Not k) -> Not $ 
    \(Not kxy) -> k . Par . Not $ 
        \(Mult (Not x', Not y')) -> x' . Not $ 
            \x -> y' . Not $ 
                \y -> kxy $ Mult (x, y) )

undmtensor :: Not x ⊗ Not y ⊢ Not (x ⅋ y)
undmtensor = Lin (\(Not k) -> Not $ \xy -> k . Not $ \(Par (Not xy')) -> xy' xy)

-- --------------------------------------------------------------------------
-- | ⅋, read "par", is the multiplicative disjunction.
--   Given "A ⅋ B" either A or B is true, but you get to "decide" which is true
--   by providing a counterexample for the other, where the counterexample may
--   be (and often is) used in the computation that produces the final result.
--   It's probably not as confusing as it sounds. Possibly.
newtype Par f g r = Par { getPar :: Not (Mult (Not f) (Not g)) r }
type (⅋) = Par

-- bifunctor map
par :: (w ⊢ x) -> (y ⊢ z) -> (w ⅋ y ⊢ x ⅋ z)
par (Lin f) (Lin g) = Lin (\(Not k) -> Not $
    \(Par (Not kxy)) -> k . Par . Not $ kxy . Mult . (f *** g) . getMult)

-- commutativity
pswap :: x ⅋ y ⊢ y ⅋ x
pswap = Lin (\(Not k) -> Not $ 
    \(Par (Not xy)) -> k . Par . Not $ xy . Mult . swap . getMult )

-- associativity
passocl :: x ⅋ (y ⅋ z) ⊢ (x ⅋ y) ⅋ z
passocl = Lin (\(Not k) -> Not $ 
    \(Par (Not xyz)) -> k . Par . Not $ 
        \(Mult (Not xy', z')) -> xy' . Par . Not $ 
            \(Mult (x', y')) -> xyz (Mult (x', Not $ \(Par (Not yz)) -> yz $ Mult (y', z'))) )

passocr :: (x ⅋ y) ⅋ z ⊢ x ⅋ (y ⅋ z)
passocr = (id `par` swap) . swap . passocl . swap . (swap `par` id)

-- | ⊥ is the identity for ⅋ and a sort of "trivial falsehood", representing an 
--   empty consequent or uninteresting antecedent. The behavior of ⊥ is 
--   inextricably linked with ⅋, implication, and negation, all of which are what
--   allows linear logic to have constructive versions of the law of the 
--   excluded middle, double negation elimination, &c.
newtype Bot r = Bot (Not Unit r)

-- left and right introduction and elimination rules for ⊥
botL :: x ⊢ Bot ⅋ x
botL = Lin (\(Not k) -> Not $ 
    \x -> k . Par . Not $ 
        \(Mult (Not ku, Not kx)) -> ku . Bot . Not $ \Unit -> kx x)

unbotL :: Bot ⅋ x ⊢ x
unbotL = Lin (\kx -> Not $ 
    \(Par (Not k)) -> k $ Mult (Not $ \(Bot (Not ku)) -> ku Unit, kx))

botR :: x ⊢ x ⅋ Bot
botR = swap . botL

unbotR :: x ⅋ Bot ⊢ x
unbotR = unbotL . swap

type instance Id Par = Bot
instance Monoidal Lin Par where
    (***) = par
    unitL = botL
    unitR = botR
    ununitL = unbotL
    ununitR = unbotR
    assocL = passocl
    assocR = passocr

instance Symmetric Lin Par where
    swap = pswap



-- | De Morgan dual to 'tcancel' above; turns multiplicative truth into a tautology.
--   It's also the identity function.
lem :: Unit ⊢ Not x ⅋ x
lem = Lin (\(Not k) -> Not $ 
    \Unit -> k . Par . Not $ 
        \(Mult (Not kx, x)) -> kx x)

-- De Morgan's laws for ⅋
dmpar :: Not (x ⅋ y) ⊢ Not x ⊗ Not y
dmpar = Lin (\k -> Not $ \(Not f) -> f $ Par k)

undmpar :: Not x ⅋ Not y ⊢ Not (x ⊗ y)
undmpar = Lin (\(Not k) -> Not $ 
    \(Par (Not xy')) -> k . Not $ 
        \(Mult (x,y)) -> xy' $ Mult (Not $ \(Not x') -> x' x, Not $ \(Not y') -> y' y))

-- --------------------------------------------------------------------------

-- | So-called "linear" or "weak" distribution. 
--   cf. http://ncatlab.org/nlab/show/linearly+distributive+category
weakdist :: x ⊗ (y ⅋ z) ⊢ (x ⊗ y) ⅋ z
--  weakdist = swap . unnegR (passocr . (swap `par` id) . passocl . (id `par` negL id)) . (id `tensor` swap)
weakdist = Lin (\(Not k) -> Not $ 
    \(Mult (x, (Par (Not yz)))) -> k . Par . Not $ 
        \(Mult (Not xy, z)) -> yz $ Mult (Not $ xy . Mult . (,) x, z)  )


-- positive distributive law, in both directions
distPos :: x ⊗ (y ⊕ z) ⊢ (x ⊗ y) ⊕ (x ⊗ z)
--  distPos = unnegR $ copairPlus (negL inlPlus) (negL inrPlus)
distPos = Lin $ \(Not k) -> Not $ 
    \(Mult (x, Plus yz)) -> k . Plus $ either (Left . Mult . (,) x) (Right . Mult . (,) x) yz

factorc :: (x ⊗ y) ⊕ (x ⊗ z) ⊢ x ⊗ (y ⊕ z)
factorc = Lin $ \(Not k) -> Not $ 
    either (\(Mult (x, y)) -> k . Mult $ (x, Plus $ Left y) ) 
           (\(Mult (x, z)) -> k . Mult $ (x, Plus $ Right z) ) 
           . getPlus

-- negative distributive law, in both directions
distNeg :: x ⅋ (y & z) ⊢ (x ⅋ y) & (x ⅋ z)
distNeg = Lin $ \(Not k) -> Not $ 
    \(Par (Not xyz)) -> k . With . Not $ 
        either (\(Not kxy) -> kxy . Par . Not $ 
                   \(Mult (kx, ky)) -> xyz . Mult $ (kx, Not $ \(With (Not yz)) -> yz (Plus $ Left ky)))
               (\(Not kxz) -> kxz . Par . Not $
                   \(Mult (kx, kz)) -> xyz . Mult $ (kx, Not $ \(With (Not xz)) -> xz (Plus $ Right kz) ))
               . getPlus

factord :: (x ⅋ y) & (x ⅋ z) ⊢ x ⅋ (y & z)
--  factord = unnegR $ copairPlus (negL inlPlus) (negL inrPlus)
factord = Lin $ \(Not k) -> Not $ 
    \(With (Not xyxz)) -> k . Par . Not $ 
        \(Mult (kx, Not yz)) -> yz . With . Not $ 
            either (\ky -> xyxz . Plus . Left . Not $ \(Par (Not xy)) -> xy $ Mult (kx, ky)) 
                   (\kz -> xyxz . Plus . Right . Not $ \(Par (Not xz)) -> xz $ Mult (kx, kz))
                   . getPlus

-- --------------------------------------------------------------------------
-- | ⊸, sometimes read as "lollipop", is linear implication. It can be defined 
--   in terms of ⅋ and negation, and since I already had both I've done that.
type x ⊸ y = Not x ⅋ y

loli :: (x ⊢ y) -> (Unit ⊢ x ⊸ y)
loli l = negL $ l . ununitR

unloli :: (Unit ⊢ x ⊸ y) -> (x ⊢ y)
unloli l = unnegR l . unitR

negloli :: x ⊸ y ⊢ Not y ⊸ Not x
negloli = (dneg `par` id) . swap

unnegloli :: Not y ⊸ Not x ⊢ x ⊸ y
unnegloli = swap . (undneg `par` id)


curryLin :: (x ⊗ y ⊸ z) ⊢ (x ⊸ y ⊸ z)
curryLin = passocr . (dmtensor `par` id) 

uncurryLin :: (x ⊸ y ⊸ z) ⊢ (x ⊗ y ⊸ z)
uncurryLin = (undmpar `par` id) . passocl

evalLin :: (x ⊸ y) ⊗ x ⊢ y
evalLin = unbotL . (tcancel `par` id) . weakdist . swap

type instance Tup Lin = Mult
type instance Hom Lin x y = x ⊸ y

instance Closed Lin where
    curry = curryLin
    uncurry = uncurryLin
    curried l = unloli $ curryLin . loli l
    uncurried l = unloli $ uncurryLin . loli l
    eval = evalLin


