{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}


module TheoryGraph where


import Base


import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set


-- | A directed simple graph labelled by the 'FilePath' of each theory.
newtype TheoryGraph
    = TheoryGraph {unTheoryGraph :: Digraph_ FilePath}
    deriving (Show, Eq)


-- | Raw 'TheoryGraph': a map from each theory @t@ to theories that import @t@.
type Digraph_ a = Map a (Set a)


instance Semigroup TheoryGraph where
    (<>) = union


instance Monoid TheoryGraph where
    mempty = TheoryGraph Map.empty


data Precedes a = !a `Precedes` !a  deriving (Show, Eq, Ord, Generic)


union :: TheoryGraph -> TheoryGraph -> TheoryGraph
union (TheoryGraph g) (TheoryGraph g') = TheoryGraph (Map.unionWith Set.union g g')


unions :: [TheoryGraph] -> TheoryGraph
unions graphs = TheoryGraph (Map.unionsWith Set.union (fmap unTheoryGraph graphs))


-- | The set of filepaths of the theory graph.
filepaths :: TheoryGraph -> Set FilePath
filepaths (TheoryGraph g) = Map.keysSet g


-- | Return the 'Context' of a node if it is in the graph,
-- or 'Nothing' if it is not.
importers :: FilePath -> TheoryGraph -> Maybe (Set FilePath)
importers n (TheoryGraph g) = Map.lookup n g
{-# INLINE importers #-}


-- |  Return a list of the immediate successors of the given node.
succs :: FilePath -> TheoryGraph -> Maybe [FilePath]
succs n g = fmap (Set.foldl' (\ts t -> t : ts) []) (importers n g)


-- | Return 'True' if the given node is in the TheoryGraph, and 'False' otherwise.
member :: FilePath -> TheoryGraph -> Bool
member n (TheoryGraph g) = Map.member n g


-- | Add a node to the TheoryGraph.
addNode :: FilePath -> TheoryGraph -> TheoryGraph
addNode a (TheoryGraph g) = TheoryGraph (Map.insertWith Set.union a Set.empty g)


-- | Add an edge to the TheoryGraph. This is a loop if the edge is already present in the graph.
addPrecedes :: Precedes FilePath -> TheoryGraph -> TheoryGraph
addPrecedes e@(Precedes _ a') (TheoryGraph g) = addNode a' (TheoryGraph (insertTail e g))
    where
    insertTail :: forall a. Ord a => Precedes a -> Digraph_ a -> Digraph_ a
    insertTail (Precedes p s) = Map.adjust (Set.insert s) p
    {-# INLINABLE insertTail #-}


-- | Construct a graph with a single node.
singleton :: FilePath -> TheoryGraph
singleton a = TheoryGraph (Map.singleton a Set.empty)

-- | Construct a graph, from a list of nodes and edges. 
-- It takes all nodes a and add the pair (a, emptyset) to the Theorygraph,
-- afterwards it add all edges between the nodes.
makeTheoryGraph :: [Precedes FilePath] -> [FilePath] -> TheoryGraph
makeTheoryGraph es as = List.foldl' (flip addPrecedes) (TheoryGraph trivial) es
    where
    trivial :: forall empty. Map FilePath (Set empty)
    trivial = Map.fromList (fmap (, Set.empty) as)
{-# INLINE makeTheoryGraph #-}


-- | Construct a graph, from a list @x:xs@,
-- where @x@ is a pair of theorys @(a,b)@ with @a@ gets imported in @b@.
fromList :: [Precedes FilePath] -> TheoryGraph
fromList es = TheoryGraph (Map.fromListWith Set.union es')
    where
    es' :: [(FilePath, Set FilePath)]
    es' = fmap tailPart es <> fmap headPart es

    tailPart, headPart :: Precedes FilePath -> (FilePath, Set FilePath)
    tailPart (Precedes a a') = (a, Set.singleton a')
    headPart (Precedes _ a') = (a', mempty)


-- | Return a topological sort, if it exists.
topSort :: TheoryGraph -> Maybe [FilePath]
topSort g = go (filepaths g)
    where
    -- While there are unmarked nodes, visit them
    go :: Set FilePath -> Maybe [FilePath]
    go o = snd $ Set.foldl' (\(unmarked, list) n -> visit n unmarked Set.empty list) (o, Just []) o

    -- Check for marks, then visit children, mark n, and add to list
    visit :: FilePath -> Set FilePath -> Set FilePath -> Maybe [FilePath] -> (Set FilePath, Maybe [FilePath])
    visit _ opens _ Nothing = (opens, Nothing)
    visit n o t l
        | not (Set.member n o) = (o, l)
        | Set.member n t = (o, Nothing)
        | otherwise = (Set.delete n newO, fmap (n :) newL)
        where
        -- visit all children
        (newO, newL) = foldl' (\(o',l') node -> visit node o' (Set.insert n t) l') (o,l) (fromJust $ succs n g)


-- | Return a 'Right' topological sort, if it exists, or a 'Left' cycle otherwise.
topSortSeq :: TheoryGraph -> Either (Seq FilePath) (Seq FilePath)
topSortSeq g = go (filepaths g)
    where
    -- While there are unmarked nodes, visit them
    go :: Set FilePath -> Either (Seq FilePath) (Seq FilePath)
    go o = snd $ Set.foldl' (\(unmarked, list) n -> visit n unmarked Set.empty list) (o, Right mempty) o

    -- Check for marks, then visit children, mark n, and add to list
    visit :: FilePath -> Set FilePath -> Set FilePath -> Either (Seq FilePath) (Seq FilePath) -> (Set FilePath, Either (Seq FilePath) (Seq FilePath))
    visit _ opens _ (Left cyc) = (opens, Left cyc)
    visit n o t l@(Right r)
        | not (Set.member n o) = (o, l)
        | Set.member n t = (o, Left r)
        | otherwise = (Set.delete n newO, fmap (n :<|) newL)
        where
        -- visit all children
        (newO, newL) = foldl' (\(o',l') node -> visit node o' (Set.insert n t) l') (o,l) (fromJust $ succs n g)
