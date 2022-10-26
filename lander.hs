{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Parallel where

import Prelude hiding (traverse)
import Control.Monad (ap, liftM)
import qualified Data.Foldable as Fold
import Data.Semigroup
import Data.Either

data Comp op sc a where
  Pure     :: a -> Comp op sc a
  Perform  :: op b -> (b -> Comp op sc a) -> Comp op sc a  
  Scope    :: sc c -> (c -> Comp op sc b) -> (b -> Comp op sc a) -> Comp op sc a

instance Functor (Comp op sc) where
   fmap = liftM

instance Applicative (Comp op sc) where
   pure  = Pure
   (<*>) = ap

instance Monad (Comp op sc) where
   (Pure  x)      >>= f = f x
   (Perform x k)  >>= f = Perform x ((>>= f) . k)
   (Scope x p k)  >>= f = Scope x p ((>>= f) . k)

data AlgPar op sc f g m l = AlgPar {
    gen      :: forall a.      a -> m (f a),
    hPerform :: forall a b.    op b -> (b -> m (f a)) -> m (f a),
    hScope   :: forall a b c.  sc c -> (c -> m (f b)) -> (f b -> m (f a)) -> m (f a),
    lift     :: forall a b.    f b -> (b -> l (a)) ->  m (f a)}

fold :: AlgPar op sc f g (Comp ops scs) (Comp (op :+: ops) (sc :+: scs)) -> Comp (op :+: ops) (sc :+: scs) a -> Comp ops scs (f a)
fold alg (Pure x)             = gen alg x
fold alg (Perform op k)       = (per # fwd) op where
  per o                       = hPerform alg o (fold alg . k)
  fwd o                       = Perform o (fold alg . k)
fold alg (Scope sc p k)       = (sco # fwd) sc p where
  sco s                       = \p -> hScope alg s (fold alg . p) (\x -> lift alg x k)
  fwd s                       = \p -> Scope s (fold alg . p) (\x -> lift alg x k)

perform :: (op :<: ops) => op a -> Comp ops sc a
perform e = Perform (liftEff e) Pure

scoped :: (sc :<: scs) => sc a -> Comp op scs a 
scoped e = Scope (liftEff e) Pure Pure  

data ForSc m r where
  ForS :: m -> ForSc m m

for :: (ForSc Int :<: sc) => Int -> (Int -> Comp op sc [b]) -> ([b] -> Comp op sc a)-> Comp op sc a
for l f g = Scope (liftEff (ForS l)) f g

(#) :: (f a -> b) -> (g a -> b) -> (f :+: g) a -> b
(alg # fwd) (Inl x) = alg x
(alg # fwd) (Inr x) = fwd x


-- Pure computations

data Empty a = Empty a deriving (Functor)

hVoid :: Comp Empty sc r -> r
hVoid c = case c of
  Pure r -> r
  Perform e _ -> case e of {} -- impossible

-- Accumulator

data Accum m r where
  Acc :: m -> Accum m ()

swap :: (a, b) -> (b, a)
swap (x, y) = (y, x)

hAccum :: Monoid m => Comp (Accum m :+: c) (ForSc Int :+: scs) a -> Comp c scs (m, a)
hAccum = fold AlgPar{ 
      gen = \r -> return (mempty, r), 
      hPerform = \ (Acc m) k -> do
        (m', v) <- k ()
        return (m <> m', v), 
      hScope = \(ForS i) p k -> do 
        (m1, x) <- p i
        _
        (m', b) <- k (m1,x)
        return (m1 <> m', b),
      lift = \(m, x) k -> hAccum (k x)
    }


sumEx :: forall a. (Num a) => [a] -> a
sumEx xs = let
  (Sum total, _) = hVoid $ hAccum @(Sum a) $ do
    for (length xs) (\x  -> sequence [perform $ Acc (Sum $ xs !! i) | i <- [0..(x-1)]]) (Pure . Fold.fold)
  in total


testSum :: Int
testSum = sumEx [1,2,3,12]

-- Weak Exceptions

data Except e a = Throw e deriving (Functor)

hWeak :: (Monoid e) => Comp (Except e :+: c) (ForSc Int :+: scs) a -> Comp c scs (Either e a)
hWeak = fold AlgPar{
    gen = \x -> return (Right x),
    hPerform = \(Throw err) _ -> return (Left err),
    -- hFor = \iters k -> do
    --    res <- Pure iters
    --    case firstFailure res of
    --      Left err -> return (Left err)
    --      Right t  -> k t,
    hScope = \(ForS i) p k -> do
       iters <- p i
       _
       case iters of 
        Left err -> return (Left err)
        Right t -> k (Right t),
    lift = \(Right a) k -> hWeak (k a)
}

firstFailure :: Monoid err => [Either err a] -> Either err [a]
firstFailure lst = case Fold.fold (fmap firstError lst) of
    Just e  -> Left e
    Nothing -> Right $ fmap (\(Right x) -> x) lst 
  where firstError x = case x of Left e  -> Just e
                                 Right _ -> Nothing

prog :: Comp (Except String :+: (Accum String :+: Empty)) (ForSc Int :+: sc) String
prog = do    
    perform $ Acc "start "
    for 5 (\x -> sequence $ [if i == 2
      then do
        perform $ Acc "!"
        perform $ Throw "error"
        perform $ Acc "unreachable"
      else perform $ Acc (show i) | i <- [1..x] ]) (\x -> Pure (Fold.fold x))
    perform $ Acc " end"
    return "success"

testExcept :: ([Char], Either String String)
testExcept = hVoid $ hAccum @String $ hWeak @String prog

-- Nondeterminism with once

data Choose m r where
  Choice :: m -> Choose m Bool
data Once m r where
  One :: m -> Once m ()

data Fail e a = Fail e deriving (Functor)

hOnce :: (Monoid e) => Comp ((Choose e) :+: c) ((Once e) :+: scs) a -> Comp c scs [a]
hOnce = fold (AlgPar ret onc scop lift) where
  ret :: a -> Comp c scs [a]
  ret x = return [x]
  onc :: Choose e b -> (b -> Comp c scs [a]) -> Comp c scs [a]
  onc (Choice m) k = do
    a <- k True
    b <- k False
    return (a ++ b)
  scop :: Once e d -> (d -> 
    Comp c scs [b]) -> ([b] -> 
    Comp c scs [a]) -> Comp c scs [a]
  scop (One m) p k = do
    a <- p ()
    _
    b <- k ([head a])
    return b
  lift  :: (Monoid e) => [b] -> (b -> Comp (Choose e :+: c) (Once e :+: scs) a) -> Comp c scs [a]
  lift x k = concMap x k hOnce

concMap :: (Monad m) => [c] -> (c -> b) -> (b -> m [a]) -> m [a]
concMap [] k f = return []
concMap (b:bs) k f = do
  as  <- f (k b)
  as' <- concMap bs k f
  return (as ++ as')

testOnce :: Comp ((Choose ()) :+: Empty)  ((Once ()) :+: Empty ) String
testOnce = do 
  Scope (liftEff (One ())) (\_ -> perform (Choice ())) (\b -> if b then return "heads" else return "tails")

tOnce = hVoid $ hOnce testOnce

-- dtc
data  (f :+: g) r = Inl (f r) | Inr (g r)
infixr 5 :+:

instance (Functor f, Functor g) => Functor (f :+: g) where
   fmap f (Inl x) = Inl (fmap f x)
   fmap f (Inr y) = Inr (fmap f y)

-- If we don't know the order, we can just impose restrictions with typeclasses.
-- The :<: constraint ensures we can lift an operation into the ops type,
-- no matter what the ops type ends up being.
class op :<: ops where
  liftEff :: op r -> ops r

-- Some unfortunate type family shenanigans here to get around restrictions
-- of Haskell's instance solver.
type family HasEffAtTop op ops :: Bool where
  HasEffAtTop op (op :+: rest) = 'True
  HasEffAtTop _ _ = 'False

class HasEff_ op ops (atTop :: Bool) where
  liftEff_ :: op r -> ops r

instance HasEff_ op ops (HasEffAtTop op ops) => op :<: ops where
  liftEff = liftEff_ @op @ops @(HasEffAtTop op ops)

instance HasEff_ op (op :+: rest) 'True where
  liftEff_ op = Inl op

instance op :<: rest => HasEff_ op (other :+: rest) 'False where
  liftEff_ op = Inr (liftEff op)
