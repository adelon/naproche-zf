{-# LANGUAGE NoImplicitPrelude #-}

module Report.Region where


import Base


-- | 'Loc' wraps a value with location information specified by a 'Region'.
-- If the 'Region' of @la :: Loc a@ is 'Nowhere', we call @la@ pure, since
-- @la = pure a@ for some @a :: a@.
data Loc a = At {unLoc :: a, locRegion :: Region} deriving (Show)

-- | Equality tests ignore the location information, so that we can match
-- located values from the token stream against pure values with functions
-- such as 'Text.Earley.Derived.token'.
instance Eq a => Eq (Loc a) where
    (==) = (==) `on` unLoc

-- | As with 'Eq', comparison ignores the location information.
instance Ord a => Ord (Loc a) where
    compare = compare `on` unLoc

instance Functor Loc where
    fmap :: (a -> b) -> Loc a -> Loc b
    fmap f (a `At` loc) = f a `At` loc

instance Applicative Loc where
    pure :: a -> Loc a
    pure a = a `At` mempty

    (<*>) :: Loc (a -> b) -> Loc a -> Loc b
    f `At` r1 <*> a `At` r2 = f a `At` (r1 <> r2)


data Position = Position
    { positionLine :: Int   -- ^ Line of the position, starting at 1.
    , positionColumn :: Int -- ^ Column of the position, starting at 1.
    , positionOffset :: Int -- ^ Index of the position, starting at 0.
    } deriving (Show, Eq, Ord)

compareLine :: Position -> Position -> Ordering
compareLine = compare `on` positionLine


data Region
--
--          Start    End      Hint for pretty-printing the region
--          vvvvvvvv vvvvvvvv vvvvvvvvvvvv
    = Region Position Position PrintingHint -- ^
--
-- Source regions are indicated by start and end position.
-- The start is inclusive, the end is exclusive. Thus below
--
-- >         1   5    10   15   20   25   30   35
-- >         |   |    |    |    |    |    |    |
-- >       ┌───────────────────────────────────────
-- >   1 ─ │     #####
-- >   2 ─ │                   %%%%%%%%%%%%%%%%%%%
-- >   3 ─ │ %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- >   4 ─ │ %%%%
--
-- the hash signs (@#@) fill the region @1:5-1:10@ (a 'SingleLine') and the
-- percent signs (@%@) fill the region @2:19-4:5@ (a 'MultiLine'). Note that
-- that the length of the region is equal to the difference of the columns
-- if the region is a single line. The start position must be strictly
-- less than the end position of the region.
--
    | Nowhere -- ^
--
-- Intended for errors without source regions or
-- for lifting pure values into a located value.
--
    deriving (Show, Eq, Ord)

regionOffset :: Region -> Maybe Int
regionOffset (Region s _e _i) = Just (positionOffset s)
regionOffset Nowhere = Nothing

-- | 'Region's form a commutative monoid under taking the convex hull of
-- their unions. The empty region 'Nowhere' is the neutral element.
convexUnion :: Region -> Region -> Region
convexUnion r1 r2 = case (r1, r2) of
    (Region s1 e1 i1, Region s2 e2 i2) -> Region s e i
        where
            s = min s1 s2
            e = max e1 e2
            i = case (i1, i2) of
                (_, MultiLine)                         -> MultiLine
                (MultiLine, _)                         -> MultiLine
                _ | positionLine s1 == positionLine e2 -> SingleLine (positionColumn e - positionColumn s)
                _                                      -> MultiLine
    (_, Nowhere)                       -> r1
    (Nowhere, _)                       -> r2

instance Semigroup Region where
    (<>) :: Region -> Region -> Region
    (<>) = convexUnion

instance Monoid Region where
    mempty :: Region
    mempty = Nowhere



data PrintingHint
    = MultiLine
    | SingleLine Int -- ^ Describes the length of the single-line region.
    deriving (Show, Eq, Ord)
