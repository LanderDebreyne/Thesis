{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}  
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Prelude hiding (traverse)
import Control.Monad (ap, liftM)
import qualified Data.Foldable as Fold
import Data.Semigroup
import Data.Either
import System.Random
import Data.Functor.Identity

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

data AlgPar op sc scs f g m l = AlgPar {
    gen      :: forall a.      a -> m (f a),
    hPerform :: forall a b.    op b -> (b -> m (f a)) -> m (f a),
    hScope   :: forall a b c.  sc c -> (c -> m (f b)) -> (b -> m (f a)) -> m (f a),
    forward  :: forall a b c.  scs c -> (c -> l b) -> (b -> l a) ->  m (f a)}

fold :: AlgPar op sc scs f g (Comp ops scs) (Comp (op :+: ops) (sc :+: scs)) -> Comp (op :+: ops) (sc :+: scs) a -> Comp ops scs (f a)
fold alg (Pure x)             = gen alg x
fold alg (Perform op k)       = (per # fwd) op where
  per o                       = hPerform alg o (fold alg . k)
  fwd o                       = Perform o (fold alg . k)
fold alg (Scope sc p k)       = (sco # fwd) sc p where
  sco s                       = \p -> hScope alg s (fold alg . p) (fold alg . k)
  fwd s                       = \p -> forward alg s p k

perform :: (op :<: ops) => op a -> Comp ops sc a
perform e = Perform (liftEff e) Pure

scoped :: sc a -> Comp op (sc :+: scs) a 
scoped e = Scope (liftEff e) Pure Pure  

data ForSc m r where
  ForS :: m -> ForSc m m

for :: Int -> (Int -> Comp op (ForSc Int :+: sc) a) -> Comp op (ForSc Int :+: sc) a
for l f = Scope (Inl (ForS l)) f Pure-- (liftEff (ForS l)) f Pure

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
hAccum = fold (AlgPar ret per scop forward) where
  ret ::(Monoid m) => a -> Comp c scs (m, a)
  ret x = return (mempty, x)
  per :: (Monoid m) => Accum m b -> (b -> Comp c scs (m, a)) -> Comp c scs (m, a)
  per (Acc m) k = do
    (m', v) <- k ()    
    return (m <> m', v) 
  scop :: (Monoid m) => ForSc Int c' -> (c' -> Comp c scs (m, b)) -> (b -> Comp c scs (m, a)) -> Comp c scs (m, a)
  scop (ForS i) p k = do
    l <- sequence [p j|j <- reverse [0..i-1]]
    let (m, x) = foldr (\n a -> (fst n <> fst a, snd a)) (head l) (tail l)
    (m', b) <- k x
    return (m <> m', b)
  forward :: (Monoid m) => scs c1 -> (c1 -> Comp (Accum m :+: c) (ForSc Int :+: scs) b) -> (b -> Comp (Accum m :+: c) (ForSc Int :+: scs) a) -> Comp c scs (m, a)
  forward s p k = Scope s (hAccum . p) (\(m, x) -> hAccum (k x))


sumEx :: forall a. (Num a) => [a] -> a
sumEx xs = let
  (Sum total, _) = hVoid $ hAccum $ do
    for (length xs) (\x  -> perform $ Acc (Sum $ xs !! x))
  in total


testSum :: Int
testSum = sumEx [1,2,3,12]

-- Weak Exceptions

data Except e a = Throw e deriving (Functor)

hWeak :: (Monoid e) => Comp (Except e :+: c) (ForSc Int :+: scs) a -> Comp c scs (Either e a)
hWeak = fold (AlgPar ret per scop forward) where
  ret :: (Monoid e) => a -> Comp c scs (Either e a)
  ret x = return (Right x)
  per :: (Monoid e) => (Except e b) -> (b -> Comp c scs (Either e a)) -> Comp c scs (Either e a)
  per (Throw err) _  = return (Left err)
  scop :: (Monoid e) => (ForSc Int c') -> (c' -> Comp c scs (Either e b)) -> (b -> Comp c scs (Either e a)) -> Comp c scs (Either e a)
  scop (ForS i) p k = do
    iters <- sequence [p j| j <- [1..i]]
    case firstFailure iters of 
      Left err -> return (Left err)
      Right t -> k (head t)
  forward :: (Monoid e) => scs c1 -> (c1 -> Comp (Except e :+: c) (ForSc Int :+: scs) b) -> (b -> Comp (Except e :+: c) (ForSc Int :+: scs) a) -> Comp c scs (Either e a)
  forward s p k = Scope s (hWeak . p) (\(Right x) -> hWeak (k x))


firstFailure :: Monoid err => [Either err a] -> Either err [a]
firstFailure lst = case Fold.fold (fmap firstError lst) of
    Just e  -> Left e
    Nothing -> Right $ fmap (\(Right x) -> x) lst 
  where firstError x = case x of Left e  -> Just e
                                 Right _ -> Nothing

prog :: Comp (Except String :+: (Accum String :+: Empty)) (ForSc Int :+: sc) String
prog = do    
    perform $ Acc "start "
    for 5 (\x -> if x == 2
      then do
        perform $ Acc "!"
        perform $ Throw "error"
        perform $ Acc "unreachable"
      else perform $ Acc (show x))
    perform $ Acc " end"
    return "success"

prog2 :: Comp (Except String :+: (Accum String :+: Empty)) (ForSc Int :+: sc) String
prog2 = do
  for 5 (\x -> if x == 2
    then perform $ Throw "error"
    else perform $ Acc (show x))
  return "succes"

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
    Comp c scs [b]) -> (b -> 
    Comp c scs [a]) -> Comp c scs [a]
  scop (One m) p k = do
    a <- p ()
    k (head a)
  lift  :: (Monoid e) => scs c1 -> (c1 -> Comp (Choose e :+: c) (Once e :+: scs) b) -> (b -> Comp (Choose e :+: c) (Once e :+: scs) a) -> Comp c scs [a]
  lift s p k = Scope s (hOnce . p) (\x -> concMap x k hOnce)

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

-- -- PRNG

-- data AlgParState op sc scs s f g m l = AlgParState {
--     genS      :: forall a.      s -> a -> m (f a),
--     hPerformS :: forall a b.    s -> op b -> (s -> b -> m (f a)) -> m (f a),
--     hScopeS   :: forall a b c.  s -> sc c -> (c -> m (f b)) -> (s -> b -> m (f a)) -> m (f a),
--     forwardS  :: forall a b c.  s -> scs c -> (c -> l b) -> (b -> l a) ->  m (f a)}

-- foldS :: AlgParState op sc scs s f g (Comp ops scs) (Comp (op :+: ops) (sc :+: scs)) -> s -> Comp (op :+: ops) (sc :+: scs) a -> Comp ops scs (f a)
-- foldS alg s (Pure x)             = genS alg s x
-- foldS alg s (Perform op k)       = (per # fwd) op where
--   per o                          = hPerformS alg s o (\s x -> foldS alg s (k x))
--   fwd o                          = Perform o (foldS alg s . k)
-- foldS alg s (Scope sc p k)       = (sco # fwd) sc p where
--   sco sc'                        = \p -> hScopeS alg s sc' (\x -> foldS alg s (p x)) (\s x -> foldS alg s (k x))
--   fwd sc'                        = \p -> forwardS alg s sc' p k

-- data Rand r where
--   SampleUniform :: Rand Float

-- -- RandomGen can only split pairwise, so we recursively unfold it to a table
-- -- of the right length. (This is a serial implementation, but we note that
-- -- n-ary split can be implemented in parallel. See for instance
-- -- https://github.com/google/jax/blob/main/design_notes/prng.md)
-- splitKey :: (RandomGen g) => g -> Int -> [g]
-- splitKey g n = splitTo g n where
--   splitTo g 0 = []
--   splitTo g 1 = [g]
--   splitTo g n = g1:(splitTo g2 (n-1)) where (g1, g2) = splitKeyPair g


-- splitKeyPair :: System.Random.RandomGen g => g -> (g, g)
-- splitKeyPair = System.Random.split

-- hRandomS :: (RandomGen g) => g -> Comp (Rand :+: c) (ForSc Int :+: scs) b -> Comp c scs (Identity b)
-- hRandomS g comp = foldS AlgParState{ 
--     genS = \_ x -> return (Identity x), 
--     hPerformS = \key SampleUniform k -> let
--         (val, key') = System.Random.randomR (0.0, 1.0) key
--         in k key' val,
--     hScopeS = \key (ForS i) p k -> do
--         let (key1, key2) = splitKeyPair key
--             key1s = splitKey key1 i
--         results <- sequence [p (key1s!!j) | j <- [0..i-1]]
--         Pure (Identity (fmap runIdentity results)),
--     forwardS = \s scs p k -> Scope scs (hRandomS s . p) (\(Identity x) -> hRandomS s (k x))
--     } g comp

-- Amb

data Amb m r where
  Ambl :: [m] -> Amb [m] m

hAmb :: Comp (Amb [b] :+: c) (ForSc Int :+: scs) a -> Comp c scs [a]
hAmb = fold AlgPar{
  gen = \x -> return [x],
  hPerform = \(Ambl l) k -> do
    allRes <- sequence [k (l!!i) | i <- [0..(length l - 1)]]
    return $ concat allRes,
  hScope = \(ForS i) p k -> do
    iterResults <- sequence [p j| j <- [1..i]]
    let   
      cartProd here rest = [x:y | x <- here, y <- rest]
      allOptions = foldr cartProd [[]] iterResults
    allRes <- sequence $ map k $ concat [(allOptions!!i) | i <- [0..(length (allOptions) - 1)]]
    return $ concat allRes,
  forward = \s p k -> Scope s (hAmb . p) (\x -> concMap x k hAmb)
}

ambCoinFlips :: Comp ((Amb [String]) :+: Empty)  ((ForSc Int) :+: Empty ) String
ambCoinFlips = do
  chars <- for 3 (\_ -> perform $ Ambl ["H", "T"])
  return $ chars 

tAmb :: [String]
tAmb = hVoid $ hAmb $ ambCoinFlips

ambDigitPairs :: Comp
                  (Amb [Int] :+: (Accum [(Int, Int)] :+: Empty))
                  (ForSc Int :+: (ForSc Int :+: Empty))
                  ()
ambDigitPairs = do
  d1 <- perform $ Ambl ([0,1,2,3,4,5,6,7,8,9] :: [Int]);
  d2 <- perform $ Ambl ([0,1,2,3,4,5,6,7,8,9] :: [Int]);
  if d1 + d2 == 13
    then perform $ Acc [(d1, d2)]
    else return ()

tDigitPairs = let
  (pairs, _) = hVoid $ hAccum @[(Int, Int)] $ hAmb $ ambDigitPairs
  in pairs

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

main :: IO ()
main = putStrLn ""
