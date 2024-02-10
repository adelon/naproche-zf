{-# LANGUAGE TupleSections #-}

{-
    Simple "mostly-insert-only" insert-ordered maps.

    There's also OMap from ordered-containers which uses two regular Maps,
    but this isn't really more efficient for our use case.

    There's also InsOrdHashMap from insert-ordered-containers which tries
    its best to preserve the insertion order. Alas, this isn't quite enough to have
    stable ATP proofs. At scale and with some other features helping with proof stability,
    (i.e. prover guidance, premise selection, etc), it may be worth revisiting InsOrdHashMap.
-}

module Data.InsOrdMap where

import Data.Either
import Data.Functor
import Data.Hashable
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HM
import Data.Int
import Data.List qualified as List
import Data.List.NonEmpty (NonEmpty(..))
import Data.List.NonEmpty qualified as NonEmpty
import Data.Maybe (Maybe, maybe)
import Data.Maybe qualified as Maybe
import Data.Monoid
import Data.Semigroup
import Prelude (error)
import Data.Traversable
import Data.Foldable hiding (toList)

data InsOrdMap k v = InsOrdMap {toList :: [(k, v)], toHashMap :: (HashMap k v)}

instance Hashable k => Semigroup (InsOrdMap k a) where
    InsOrdMap a b <> InsOrdMap c d = InsOrdMap (a <> c) (b <> d)

instance Hashable k => Monoid (InsOrdMap k a) where
    mempty = InsOrdMap mempty mempty

instance Functor (InsOrdMap k) where
    fmap f (InsOrdMap asList asHashMap) = InsOrdMap (fmap (\(k,v) -> (k, f v)) asList) (fmap f asHashMap)

instance Foldable (InsOrdMap k) where
    foldr f b (InsOrdMap _asList asHashMap) = foldr f b asHashMap

instance Traversable (InsOrdMap k) where
    traverse f (InsOrdMap _asList asHashMap) = fromHashMap <$> (traverse f asHashMap)

size :: InsOrdMap k v -> Int
size omap = HM.size (toHashMap omap)

fromList :: Hashable k => [(k, v)] -> InsOrdMap k v
fromList kvs = InsOrdMap kvs (HM.fromList kvs)

fromHashMap :: HashMap k v -> InsOrdMap k v
fromHashMap kvs =  InsOrdMap (HM.toList kvs) kvs

insert :: Hashable k => k -> v -> InsOrdMap k v -> InsOrdMap k v
insert k v (InsOrdMap kvs kvs') = InsOrdMap ((k, v) : kvs) (HM.insert k v kvs')

mapMaybe :: (v1 -> Maybe v) -> InsOrdMap k v1 -> InsOrdMap k v
mapMaybe f (InsOrdMap kvs kvs') = InsOrdMap (Maybe.mapMaybe (\(k, v) -> (k,) <$> f v) kvs) (HM.mapMaybe f kvs')

lookup :: Hashable k => k -> InsOrdMap k a -> Maybe a
lookup a (InsOrdMap _ kvs) = HM.lookup a kvs

lookups :: Hashable k => NonEmpty k -> InsOrdMap k v -> Either k (NonEmpty v)
lookups ks kvs =
    let lookups' = (\a kvs' -> maybe (Left a) Right (lookup a kvs')) <$> ks
        flap ff x = (\f -> f x) <$> ff
    in case partitionEithers (NonEmpty.toList (flap lookups' kvs)) of
        (missingKey : _, _) -> Left missingKey
        ([], v : vs) -> Right (v :| vs)
        ([], []) -> error "IMPOSSIBLE (Data.InsOrdMap.lookups): one of the two result lists must be nonempty as they partition a nonempty list"

-- | Only intended for very small nonempty lists of keys!
lookupsMap :: Hashable k => NonEmpty k -> InsOrdMap k v -> Either k (InsOrdMap k v)
lookupsMap ks kvs =
    let lookups' = (\a kvs' -> maybe (Left a) Right (lookup a kvs')) <$> ks
        flap ff x = (\f -> f x) <$> ff
    in case partitionEithers (NonEmpty.toList (flap lookups' kvs)) of
        (missingKey : _, _) -> Left missingKey
        ([], vs) -> Right (fromList (List.zip (NonEmpty.toList ks) vs))

-- | Split an InsOrdMap into an InsOrdMap specified by given "relevant" keys and non-given "irrelevant" keys.
pickOutMap :: Hashable k => NonEmpty k -> InsOrdMap k v -> (InsOrdMap k v, InsOrdMap k v)
pickOutMap ks kvs =
    let (relevants, irrelevants) = List.partition (\(k,_) -> k `List.elem` NonEmpty.toList ks) (toList kvs)
    in (fromList relevants, fromList irrelevants)
