{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RankNTypes #-}

{- Delimited Continuation Indexed Monad -}
module CM where

import Prelude hiding (Functor(..), Monad(..))

class Functor f where
  fmap :: (a -> b) -> f i1 i2 a -> f i1 i2 b

class Functor f => Applicative f where
  unit :: f i i ()
  (<&>) :: f i1 i2 a -> f i2 i3 b -> f i1 i3 (a, b)
  
  return :: a -> f i i a
  (<*>)  :: f i1 i2 (a -> b) -> f i2 i3 a -> f i1 i3 b
  (>>)   :: f i1 i2 a -> f i2 i3 b -> f i1 i3 b

  unit = return ()
  x1 <&> x2 = fmap (,) x1 <*> x2

  return x = fmap (const x) unit
  f <*> x  = fmap (uncurry ($)) $ f <&> x
  x1 >> x2 = fmap snd $ x1 <&> x2

class Applicative m => Monad m where
  join :: m i1 i2 (m i2 i3 a) -> m i1 i3 a
  (>>=) :: m i1 i2 a -> (a -> m i2 i3 b) -> m i1 i3 b

  m >>= k = join $ fmap k m
  join mm = mm >>= id


fail :: a
fail = error "fail is bs"

newtype CM f i a = CM { unCPS :: (a -> i) -> f }
runCM :: CM f a a -> f
runCM (CM k) = k id

instance Functor CM where
  fmap f (CM kx) = CM $ \bk ->
                     kx $ \x ->
                       bk (f x)

instance Applicative CM where
  unit = CM $ \k -> k ()
  (CM kx) <&> (CM ky) =
    CM $ \kxy ->
      kx $ \x ->
        ky $ \y ->
          kxy (x, y)

instance Monad CM where
  join (CM k13) =
    CM $ \k3 ->
      k13 $ \(CM k23) ->
        k23 $ \x ->
          k3 x

i :: Int -> CM i i Int
i = return

(+#) :: CM i1 i2 Int -> CM i2 i3 Int -> CM i1 i3 Int
(+#) kx ky = return (+) <*> kx <*> ky

if0 :: CM i1 i2 Int
       -> CM i2 i3 a
       -> CM i2 i3 a
       -> CM i1 i3 a
if0 kbool k1 k2 = do
  b <- kbool
  case b == 0 of
   True -> k1
   False -> k2

(@@) :: CM i1 i2 (a -> CM i3 i4 b)
        -> CM i2 i3 a
        -> CM i1 i4 b
kf @@ kx = do
  f <- kf
  x <- kx
  f x
  
reset :: CM r a a -> CM i i r
reset (CM k) =
  CM $ \f ->
    f (k $ \x -> x)

shift :: ((forall r. a -> CM r r b) -> CM f i i) -> CM f b a
shift ke =
  CM $ \kx ->
    (\kf -> kf (\x -> x))
    (unCPS (ke $ \x ->
              (CM $ \kb ->
                kb (kx x))))
