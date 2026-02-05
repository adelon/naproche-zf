{-# LANGUAGE RecursiveDo #-}

module Syntax.Mixfix where

{-
Original code Copyright (c) 2014-2019, Olle Fredriksson

All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.

    * Redistributions in binary form must reproduce the above
      copyright notice, this list of conditions and the following
      disclaimer in the documentation and/or other materials provided
      with the distribution.

    * Neither the name of Olle Fredriksson nor the names of other
      contributors may be used to endorse or promote products derived
      from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
-}


import Base
import Text.Earley
import Data.Either
import Syntax.Abstract


replicateA :: Applicative f => Int -> f a -> f [a]
replicateA n = sequenceA . replicate n

consA :: Applicative f => f a -> f [a] -> f [a]
consA p q = (:) <$> p <*> q


-- | An identifier with identifier parts ('Just's), and holes ('Nothing's)
-- representing the positions of its arguments.
--
-- Example (commonly written "if_then_else_"):
-- @['Just' "if", 'Nothing', 'Just' "then", 'Nothing', 'Just' "else", 'Nothing'] :: 'Holey' 'String'@
type Holey a = [Maybe a]


-- | Create a grammar for parsing mixfix expressions.
mixfixExpression
  :: [[(Holey (Prod r e t ident), Associativity)]]
  -- ^ A table of holey identifier parsers, with associativity information.
  -- The identifiers should be in groups of precedence levels listed from
  -- binding the least to the most tightly.
  --
  -- The associativity is taken into account when an identifier starts or ends
  -- with holes, or both. Internal holes (e.g. after "if" in "if_then_else_")
  -- start from the beginning of the table.
  --
  -- Note that this rule also applies to identifiers with multiple consecutive
  -- holes, e.g. "if__" --- the associativity then applies to both holes.
  -> Prod r e t expr
  -- ^ An atom, i.e. what is parsed at the lowest level. This will
  -- commonly be a (non-mixfix) identifier or a parenthesised expression.
  -> (Holey ident -> [expr] -> expr)
  -- ^ How to combine the successful application of a holey identifier to its
  -- arguments into an expression.
  -> Grammar r (Prod r e t expr)
mixfixExpression table atom app = mixfixExpressionSeparate table' atom
  where
    table' = [[(holey, assoc, app) | (holey, assoc) <- row] | row <- table]

-- | A version of 'mixfixExpression' with a separate semantic action for each
-- individual 'Holey' identifier.
mixfixExpressionSeparate
  :: [[(Holey (Prod r e t ident), Associativity, Holey ident -> [expr] -> expr)]]
  -- ^ A table of holey identifier parsers, with associativity information and
  -- semantic actions.  The identifiers should be in groups of precedence
  -- levels listed from binding the least to the most tightly.
  --
  -- The associativity is taken into account when an identifier starts or ends
  -- with holes, or both. Internal holes (e.g. after "if" in "if_then_else_")
  -- start from the beginning of the table.
  --
  -- Note that this rule also applies to identifiers with multiple consecutive
  -- holes, e.g. "if__" --- the associativity then applies to both holes.
  -> Prod r e t expr
  -- ^ An atom, i.e. what is parsed at the lowest level. This will
  -- commonly be a (non-mixfix) identifier or a parenthesised expression.
  -> Grammar r (Prod r e t expr)
mixfixExpressionSeparate table atom = mdo
  expr <- foldrM ($) atom $ map (level expr) table
  return expr
  where
    level expr idents next = mdo
      same <- rule $ asum $ next : map (mixfixIdent same) idents
      return same
      where
        -- Group consecutive holes and ident parts.
        grp [] = []
        grp (Nothing:ps) = case grp ps of
          Left n:rest -> (Left $! (n + 1)) : rest
          rest        -> Left 1            : rest
        grp (Just p:ps) = case grp ps of
          Right ps':rest -> Right (consA p ps')       : rest
          rest           -> Right (consA p $ pure []) : rest

        mixfixIdent same (ps, a, f) = f' <$> go (grp ps)
          where
            f' xs = f (concatMap (either (map $ const Nothing) $ map Just) xs)
                   $ concat $ lefts xs
            go ps' = case ps' of
              [] -> pure []
              [Right p] -> pure . Right <$> p
              Left n:rest -> consA
                (Left <$> replicateA n (if a == RightAssoc then next
                                                           else same))
                $ go rest
              [Right p, Left n] -> consA
                (Right <$> p)
                $ pure . Left <$> replicateA n (if a == LeftAssoc then next
                                                                  else same)
              Right p:Left n:rest -> consA (Right <$> p)
                $ consA (Left <$> replicateA n expr)
                $ go rest
              Right _:Right _:_ -> error
                $  "Earley.mixfixExpression: The impossible happened. "
                ++ "Please report this as a bug."
