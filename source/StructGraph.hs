{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}


module StructGraph where


import Base
import Syntax.Internal

import Data.Map.Strict qualified as Map
import Data.Set qualified as Set


data Struct = Struct
    { structNoun :: StructPhrase
    , structAncestors :: Set StructPhrase -- ^ All ancestors, including transitive ancestors.
    , structInternalSymbols :: Set StructSymbol -- ^ Signature.
    } deriving (Show, Eq, Ord)

newtype StructGraph
    = StructGraph {unStructGraph :: Map StructPhrase Struct}
    deriving (Show, Eq, Semigroup, Monoid)


-- | Lookup a struct by its name.
lookup :: StructPhrase -> StructGraph -> Maybe Struct
lookup str graph = Map.lookup str (unStructGraph graph)

-- | Unsafe variant of 'lookup'.
unsafeLookup :: StructPhrase -> StructGraph -> Struct
unsafeLookup str graph = lookup str graph ?? error ("not in scope: " <> show str)

-- | Returns the ancestors of the given StructPhrase in the graph.
-- This function fails quietly by returning the empty set if the struct is not present in the graph.
lookupAncestors :: StructPhrase -> StructGraph -> Set StructPhrase
lookupAncestors str graph = case lookup str graph of
    Just struct -> structAncestors struct
    Nothing -> mempty

-- | Unsafe lookup of internal symbols by struct name.
lookupInternalSymbols :: StructPhrase -> StructGraph -> Set StructSymbol
lookupInternalSymbols phrase graph = case lookup phrase graph of
    Nothing -> error ("structure not in scope: " <> show phrase)
    Just struct -> structInternalSymbols struct

-- | Unsafe lookup of symbols of a structure, including those inherited from ancestors.
lookupSymbols :: StructPhrase -> StructGraph -> Set StructSymbol
lookupSymbols phrase graph = case lookup phrase graph of
    Nothing -> error ("structure not in scope: " <> show phrase)
    Just struct ->
        let ancestors = Set.map (`unsafeLookup` graph) (structAncestors struct)
            ancestorSymbols = Set.unions (Set.map structInternalSymbols ancestors)
        in ancestorSymbols <> structInternalSymbols struct

structSymbols :: Struct -> StructGraph -> Set StructSymbol
structSymbols struct graph =
    let ancestors = Set.map (`unsafeLookup` graph) (structAncestors struct)
        ancestorSymbols = Set.unions (Set.map structInternalSymbols ancestors)
    in structInternalSymbols struct <> ancestorSymbols

isInternalSymbolIn :: StructSymbol -> Struct -> Bool
isInternalSymbolIn tok struct = Set.member tok (structInternalSymbols struct)

isSymbolIn :: StructSymbol -> Struct -> StructGraph -> Bool
isSymbolIn tok struct graph =  Set.member tok (structSymbols struct graph)

-- | Insert a new struct into the graph.
insert
    :: StructPhrase
    -> Set StructPhrase
    -> Set StructSymbol
    -> StructGraph
    -> StructGraph
insert structNoun ancestors structInternalSymbols graph =
    let
        transitiveAncestors anc = lookupAncestors anc graph
        structAncestors = ancestors `Set.union` Set.unions (Set.map transitiveAncestors ancestors)
    in  StructGraph (Map.insert structNoun Struct{..} (unStructGraph graph))
