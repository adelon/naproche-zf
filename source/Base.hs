{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE BangPatterns #-}

-- | A basic prelude intended to reduce the amount of repetitive imports.
-- Mainly consists of re-exports from @base@ modules.
-- Intended to be imported explicitly (but with @NoImplicitPrelude@ enabled)
-- so that it is obvious that this module is used. Commonly used data types
-- or helper functions from outside of @base@ are also included.
--
module Base (module Base, module Export) where

-- Some definitions from @base@ need to be hidden to avoid clashes.
--
import Prelude as Export hiding
    ( Word
    , head, last, init, tail, lines, lookup
    , filter -- Replaced by generalized form from "Data.Filtrable".
    , words, pi, all
    )

import Control.Applicative as Export hiding (some)
import Control.Applicative qualified as Applicative
import Control.Monad
import Control.Monad.IO.Class as Export
import Control.Monad.State
import Data.Containers.ListUtils as Export (nubOrd) -- Faster than `nub`.
import Data.DList as Export (DList)
import Data.Foldable as Export
import Data.Function as Export (on)
import Data.Functor as Export (void)
import Data.Hashable as Export (Hashable(..))
import Data.HashMap.Strict as Export (HashMap)
import Data.HashSet as Export (HashSet)
import Data.IntMap.Strict as Export (IntMap)
import Data.List.NonEmpty as Export (NonEmpty(..))
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map as Export (Map)
import Data.Maybe as Export hiding (mapMaybe, catMaybes)  -- Replaced by generalized form from "Data.Filtrable".
import Data.Monoid (First(..))
import Data.Sequence as Export (Seq(..), replicateA)
import Data.Set as Export (Set)
import Data.Set.Internal qualified as Set
import Data.String as Export (IsString(..))
import Data.Text as Export (Text)
import Data.Traversable as Export
import Data.Void as Export
import Data.Word as Export (Word64)
import Debug.Trace as Export
import GHC.Generics as Export (Generic(..), Generic1(..))
import Prettyprinter as Export (pretty)
import UnliftIO as Export (throwIO)

-- | Signal to the developer that a branch is unreachable or represent
-- an impossible state. Using @impossible@ instead of @error@ allows
-- for easily finding leftover @error@s while ignoring impossible branches.
impossible :: String -> a
impossible msg = error ("IMPOSSIBLE: " <> msg)

-- | Signal to the developer that some part of the program is unfinished.
_TODO :: String -> a
_TODO msg = error ("TODO: " <> msg)

-- | Eliminate a @Maybe a@ value with default value as fallback.
(??) :: Maybe a -> a -> a
ma ?? a = fromMaybe a ma

-- | Convert a ternary uncurried function to a curried function.
curry3 :: ((a, b, c) -> d) -> a -> b -> c -> d
curry3 f a b c = f (a,b,c)

-- | Convert a ternary curried function to an uncurried function.
uncurry3 :: (a -> b -> c -> d) -> ((a, b, c) -> d)
uncurry3 f ~(a, b, c) = f a b c

-- | Convert a ternary curried function to an uncurried function.
uncurry4 :: (a -> b -> c -> d -> e) -> ((a, b, c, d) -> e)
uncurry4 f ~(a, b, c, d) = f a b c d

-- | Fold of composition of endomorphisms:
-- like @sum@ but for @(.)@ instead of @(+)@.
compose :: Foldable t => t (a -> a) -> (a -> a)
compose = foldl' (.) id

-- | Safe list lookup. Replaces @(!!)@.
nth :: Int -> [a] -> Maybe a
nth _ [] = Nothing
nth 0 (a : _) = Just a
nth n (_ : as) = nth (n - 1) as

-- Same as 'find', but with a 'Maybe'-valued predicate that also transforms the resulting value.
firstJust :: Foldable t => (a -> Maybe b) -> t a -> Maybe b
firstJust p = getFirst . foldMap (\ x -> First (p x))

-- | Do nothing and return @()@.
skip :: Applicative f => f ()
skip = pure ()

-- | One or more. Equivalent to @some@ from @Control.Applicative@, but
-- keeps the information that the result is @NonEmpty@.
many1 :: Alternative f => f a -> f (NonEmpty a)
many1 a = NonEmpty.fromList <$> Applicative.some a

-- | Same as 'many1', but discards the type information that the result is @NonEmpty@.
many1_ :: Alternative f => f a -> f [a]
many1_ = Applicative.some

count :: Applicative f => Int -> f a -> f [a]
count n fa
    | n <= 0    = pure []
    | otherwise = replicateM n fa

-- | Same as 'count', but requires at least one occurrence.
count1 :: Applicative f => Int -> f a -> f (NonEmpty a)
count1 n fa
    | n <= 1    = (:| []) <$> fa
    | otherwise = NonEmpty.fromList <$> replicateM n fa

-- | Apply a functor of functions to a plain value.
flap :: Functor f => f (a -> b) -> a -> f b
flap ff x = (\f -> f x) <$> ff
{-# INLINE flap #-}

-- | Like 'when' but for functions that carry a witness with them:
-- execute a monadic action depending on a 'Left' value.
-- Does nothing on 'Right' values.
--
-- > whenLeft eitherErrorOrResult throwError
--
whenLeft :: Applicative f => Either a b -> (a -> f ()) -> f ()
whenLeft mab action = case mab of
    Left err -> action err
    Right _  -> skip

-- | Like 'when', but the guard is monadic.
whenM :: Monad m => m Bool -> m () -> m ()
whenM mb ma = ifM mb ma skip

-- | Like 'unless', but the guard is monadic.
unlessM :: Monad m => m Bool -> m () -> m ()
unlessM mb ma = ifM mb skip ma

-- | Like 'guard', but the guard is monadic.
guardM :: MonadPlus m => m Bool -> m ()
guardM f = guard =<< f

-- | @if [...] then [...] else [...]@ lifted to a monad.
ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM mb ma1 ma2 = do
    b <- mb
    if b then ma1 else ma2

-- | Similar to @Reader@'s @local@, but for @MonadState@. Resets the state after a computation.
locally :: MonadState s m => m a -> m a
locally ma = do
    s <- get
    a <- ma
    put s
    return a


{-| Decompose two sets into their /exclusive/ parts.

@
    symmetricDifferenceDecompose t1 t2 = (t1 \\\\ t2, t2 \\\\ t1)
@

This is essentially a structural version of symmetric difference that
preserves the balance of the underlying tree representation.

@
    let t1 = Set.fromList [1,2,3,4]
    let t2 = Set.fromList [3,4,5,6]
    symmetricDifferenceDecompose t1 t2 == (fromList [1,2],fromList [5,6])
@
-}
symmetricDifferenceDecompose :: Ord a => Set a -> Set a -> (Set a, Set a)
symmetricDifferenceDecompose Set.Tip t2 = (Set.Tip, t2)
symmetricDifferenceDecompose t1 Set.Tip = (t1, Set.Tip)
symmetricDifferenceDecompose (Set.Bin _ x l1 r1) t2 =
    let !(l2, found, r2) = Set.splitMember x t2
        !(l1', l2') = symmetricDifferenceDecompose l1 l2
        !(r1', r2') = symmetricDifferenceDecompose r1 r2
    in  if found
            then (Set.merge l1' r1', Set.merge l2' r2')
            else (Set.link x l1' r1', Set.merge l2' r2')
