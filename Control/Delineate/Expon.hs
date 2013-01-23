{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
module Control.Delineate.Expon where

import Control.Delineate
import Control.Delineate.Category

import Prelude hiding ((.), id, curry, uncurry, fst, snd)
import qualified Prelude as P



newtype Bang f r = Bang { getBang :: (Unit & f & Bang f ⊗ Bang f) r }

weakenBang :: Bang x ⊢ Unit
weakenBang = Lin $ \u -> Not $ 
    \(Bang (With (Not bx))) -> bx . Plus . Left $ u

derelictBang :: Bang x ⊢ x
derelictBang = Lin $ \x -> Not $
    \(Bang (With (Not bx))) -> bx . Plus . Right . Not $ 
        \(With (Not xs)) -> xs . Plus . Left $ x

contractBang :: Bang x ⊢ Bang x ⊗ Bang x
contractBang = Lin $ \k -> Not $ 
    \(Bang (With (Not xs))) -> xs . Plus . Right . Not $ 
        \(With (Not xs')) -> xs' . Plus . Right $ k

unBang :: Bang x ⊢ Unit & x & Bang x ⊗ Bang x
unBang = Lin $ \(Not k) -> Not $ \(Bang xs) -> k xs

bang :: Unit & x & Bang x ⊗ Bang x ⊢ Bang x 
bang = Lin $ \(Not k) -> Not $ \xs -> k $ Bang xs


mkBang :: a -> Bang (Var a) r
mkBang x = Bang . With . Not $ either
    (\(Not weak) -> weak Unit)
    (\(Not kdc) -> kdc . With . Not $ either
        (\(Not der) -> der $ Var x)
        (\(Not con) -> con $ Mult (mkBang x, mkBang x))
        . getPlus) . getPlus
    

ofCourse :: a -> (Unit ⊢ Bang (Var a))
ofCourse x = Lin $ \(Not k) -> Not $ \Unit -> k $ mkBang x



newtype Wut f r = Wut { getWut :: (Bot ⊕ f ⊕ Wut f ⅋ Wut f) r }

weakenWut :: Bot ⊢ Wut x
weakenWut = Lin $ \(Not k) -> Not $ \b -> k . Wut . Plus . Left $ b

derelictWut :: x ⊢ Wut x
derelictWut = Lin $ \(Not k) -> Not $ \b -> k . Wut . Plus . Right . Plus . Left $ b

contractWut :: Wut x ⅋ Wut x ⊢ Wut x
contractWut = Lin $ \(Not k) -> Not $ \b -> k . Wut . Plus . Right . Plus . Right $ b

unWut :: Wut x ⊢ Bot ⊕ x ⊕ Wut x ⅋ Wut x
unWut = Lin $ \(Not k) -> Not $ \(Wut xs) -> k xs

wut :: Bot ⊕ x ⊕ Wut x ⅋ Wut x ⊢ Wut x 
wut = Lin $ \(Not k) -> Not $ \xs -> k $ Wut xs

