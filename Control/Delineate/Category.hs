{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
--  {-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
module Control.Delineate.Category where

import Data.Void
import Control.Arrow ((|||))
import qualified Control.Arrow as Arr
import qualified Data.Tuple as T
import Prelude hiding ((.), id, curry, uncurry, fst, snd)
import qualified Prelude as P

class Category (cat :: k -> k -> *) where
    id  :: cat a a
    (.) :: cat b c -> cat a b -> cat a c

type family Id (p :: k -> k -> k) :: k

class (Category cat) => Monoidal cat p where
    (***) :: cat a b -> cat a' b' -> cat (p a a') (p b b')
    
    right :: cat a b -> cat (p c a) (p c b)
    right = (id ***)
    
    left :: cat a b -> cat (p a c) (p b c)
    left = (*** id)
    
    unitR :: cat a (p a (Id p))
    unitL :: cat a (p (Id p) a)
    ununitR :: cat (p a (Id p)) a
    ununitL :: cat (p (Id p) a) a
    assocR :: cat (p (p a b) c) (p a (p b c))
    assocL :: cat (p a (p b c)) (p (p a b) c)
    
    default unitR :: (Symmetric cat p) => cat a (p a (Id p))
    unitR = swap . unitL

    default unitL :: (Symmetric cat p) => cat a (p (Id p) a)
    unitL = swap . unitR
    
    default ununitR :: (Symmetric cat p) => cat (p a (Id p)) a
    ununitR = ununitL . swap
    
    default ununitL :: (Symmetric cat p) => cat (p (Id p) a) a
    ununitL = ununitR . swap
    
    default assocR :: (Symmetric cat p) => cat (p (p a b) c) (p a (p b c))
    assocR = right swap . swap . assocL . swap . left swap
    
    default assocL :: (Symmetric cat p) => cat (p a (p b c)) (p (p a b) c)
    assocL = left swap . swap . assocR . swap . right swap
    

class (Monoidal cat p) => Symmetric cat p where
    swap :: cat (p a b) (p b a)

type family Hom (cat :: k -> k -> *) (x::k) (y::k) :: k
type family Tup (cat :: k -> k -> *) :: k -> k -> k
class (Symmetric cat (Tup cat)) => Closed cat where
    curry :: cat (Hom cat (Tup cat a b) c) (Hom cat a (Hom cat b c))
    uncurry :: cat (Hom cat a (Hom cat b c)) (Hom cat (Tup cat a b) c)
    curried :: cat (Tup cat a b) c -> cat a (Hom cat b c)
    uncurried :: cat a (Hom cat b c) -> cat (Tup cat a b) c
    eval :: cat (Tup cat (Hom cat a b) a) b


type family Dualizer (cat :: k -> k -> *) :: k
type family Neg (cat :: k -> k -> *) :: k -> k
class (Symmetric cat (Tup cat)) => StarAut cat where
    fromNeg :: cat (Neg cat a) (Hom cat a (Dualizer cat))
    toNeg :: cat (Hom cat a (Dualizer cat)) (Neg cat a)
    dneg :: cat a (Neg cat (Neg cat a))
    undneg :: cat (Neg cat (Neg cat a)) a


type family Prod (cat :: k -> k -> *) :: k -> k -> k
class (Monoidal cat (Prod cat)) => Product cat where
    fst :: cat (Prod cat a b) a
    snd :: cat (Prod cat a b) b
    pair :: cat a b -> cat a c -> cat a (Prod cat b c)


type family Initial (cat :: k -> k -> *) :: k
type family Sum (cat :: k -> k -> *) :: k -> k -> k
class (Monoidal cat (Sum cat)) => Coproduct cat where
    inl :: cat a (Sum cat a b)
    inr :: cat b (Sum cat a b)
    copair :: cat b a -> cat c a -> cat (Sum cat b c) a




instance Category (->) where
    id = P.id
    (.) = (P..)

type instance Id (,) = ()
instance Monoidal (->) (,) where
    (***) = (Arr.***)
    unitR x = (x, ())
    unitL x = ((), x)
    ununitR (x, ()) = x
    ununitL ((), x) = x
    assocR ((x, y), z) = (x, (y, z))
    assocL (x, (y, z)) = ((x, y), z)

instance Symmetric (->) (,) where
    swap = T.swap

type instance Id Either = Void
instance Monoidal (->) Either where
    (***) = (Arr.+++)
    unitR = Left
    unitL = Right
    ununitR = id ||| absurd
    ununitL = absurd ||| id
    assocL = Left . Left ||| (Left . Right ||| Right)
    assocR = (Left ||| Right . Left) ||| Right . Right

instance Symmetric (->) Either where
    swap = Right ||| Left

type instance Hom (->) a b = a -> b
type instance Tup (->) = (,)
instance Closed (->) where
    curry = P.curry
    uncurry = P.uncurry
    curried = P.curry
    uncurried = P.uncurry
    eval = uncurried ($)

type instance Prod (->) = (,)
instance Product (->) where
    fst = P.fst
    snd = P.snd
    pair = (Arr.&&&)

type instance Sum (->) = Either
instance Coproduct (->) where
    inl = Left
    inr = Right
    copair = either



