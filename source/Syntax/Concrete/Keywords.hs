{-# LANGUAGE NoImplicitPrelude #-}
{-|
This module defines lots of keywords and various filler
phrases. The prefix underscore indicates that we do not
care about the parse result (analogous to  discarding
like @...; _ <- action; ...@ in do-notation). Moreover,
this convention allows the use of short names that would
otherwise be Haskell keywords or clash with other definitions.
Care should be taken with introducing too many variants of
a keyword, lest the grammar becomes needlessly ambiguous!

The names are chosen using the following criteria:

   * As short as possible (e.g.: @_since@ over @_because@).

   * Sound like a keyword (e.g.: @_show@).

This module also defines symbols that have special uses
(such as @_colon@ for its use in type signatures).
-}
module Syntax.Concrete.Keywords where


import Base
import Syntax.Token
import Report.Location

import Text.Earley (Prod, (<?>), terminal)

infixr 0 ?
-- | Variant of '<?>' for annotating literal tokens.
(?) :: Prod r Text t a -> Text -> Prod r Text t a
p ? e = p <?> ("\"" <> e <> "\"")

word :: Text -> Prod r Text (Located Token) Location
word w = terminal maybeToken
   where
      maybeToken ltok = case unLocated ltok of
         Word w' | w == w' -> Just (startPos ltok)
         _ -> Nothing

symbol :: Text -> Prod r Text (Located Token) Location
symbol s = terminal maybeToken
   where
      maybeToken ltok = case unLocated ltok of
         Symbol s' | s == s' -> Just (startPos ltok)
         _ -> Nothing

command :: Text -> Prod r Text (Located Token) Location
command cmd = terminal maybeToken
   where
      maybeToken ltok = case unLocated ltok of
         Command cmd' | cmd == cmd' -> Just (startPos ltok)
         _ -> Nothing

_arity :: Prod r Text (Located Token) Int
_arity = asum
   [ 1  <$ word "unary"
   , 2  <$ word "binary"
   , 3  <$ word "ternary"
   , 4  <$ word "quaternary"
   , 5  <$ word "quinary"
   , 6  <$ word "senary"
   , 7  <$ word "septenary"
   , 8  <$ word "octonary"
   , 9  <$ word "nonary"
   , 10 <$ word "denary"
   ] <?> "\"unary\", \"binary\', ..."

-- * Keywords

_an :: Prod r Text (Located Token) Location
_an = word "a" <|> word "an" <?> "indefinite article"
_and :: Prod r Text (Located Token) Location
_and = word "and" ? "and"
_are :: Prod r Text (Located Token) Location
_are = word "are" ? "are"
_asFollows :: Prod r Text (Located Token) Location
_asFollows = word "as" <* word "follows" ? "as follows"
_assumption :: Prod r Text (Located Token) Location
_assumption = word "assumption" ? "assumption"
_be :: Prod r Text (Located Token) Location
_be = word "be" ? "be"
_by :: Prod r Text (Located Token) Location
_by = word "by" ? "by"
_bySetExt :: Prod r Text (Located Token) Location
_bySetExt = word "by" <* ((word "set" ? "set") <* word "extensionality") ? "by set extensionality"
_can :: Prod r Text (Located Token) Location
_can = word "can" ? "can"
_consistsOf :: Prod r Text (Located Token) Location
_consistsOf = word "consists" <* word "of" ? "consists of"
_contradiction :: Prod r Text (Located Token) Location
_contradiction = optional (word "a") *> word "contradiction" ? "a contradiction"
_define :: Prod r Text (Located Token) Location
_define = word "define" ? "define"
_definition :: Prod r Text (Located Token) Location
_definition = word "definition" ? "definition"
_denote :: Prod r Text (Located Token) Location
_denote = word "denote" <|> (word "stand" <* word "for") ? "denote"
_denotes :: Prod r Text (Located Token) Location
_denotes = word "denotes" ? "denotes"
_do :: Prod r Text (Located Token) Location
_do = word "do" ? "do"
_does :: Prod r Text (Located Token) Location
_does = word "does" ? "does"
_either :: Prod r Text (Located Token) Location
_either = word "either" ? "either"
_equipped :: Prod r Text (Located Token) Location
_equipped = (word "equipped" <|> word "together") <* word "with" ? "equipped with"
_every :: Prod r Text (Located Token) Location
_every = word "every" ? "every"
_exist :: Prod r Text (Located Token) Location
_exist = word "there" <* word "exist" ? "there exist"
_exists :: Prod r Text (Located Token) Location
_exists = word "there" <* word "exists" ? "there exists"
_extends :: Prod r Text (Located Token) Location
_extends = (_is) <|> (word "consists" <* word "of") ? "consists of"
_fix :: Prod r Text (Located Token) Location
_fix = word "fix" ? "fix"
_follows :: Prod r Text (Located Token) Location
_follows = word "follows" ? "follows"
_for :: Prod r Text (Located Token) Location
_for = word "for" ? "for"
_forAll :: Prod r Text (Located Token) Location
_forAll = (word "for" <* word "all") <|> word "all" ? "all"
_forEvery :: Prod r Text (Located Token) Location
_forEvery = (word "for" <* word "every") <|> word "every" ? "for every"
_have :: Prod r Text (Located Token) Location
_have = word "we" <* word "have" <* optional (word "that") ? "we have"
_if :: Prod r Text (Located Token) Location
_if = word "if" ? "if"
_iff :: Prod r Text (Located Token) Location
_iff = word "iff" <|> (word "if" <* word "and" <* word "only" <* word "if") ? "iff"
_inductively :: Prod r Text (Located Token) Location
_inductively = word "inductively" ? "inductively"
_is :: Prod r Text (Located Token) Location
_is = word "is" ? "is"
_itIsWrong :: Prod r Text (Located Token) Location
_itIsWrong = word "it" <* word "is" <* (word "not" <* word "the" <* word "case" <|> word "wrong") <* word "that" ? "it is wrong that"
_let :: Prod r Text (Located Token) Location
_let = word "let" ? "let"
_neither :: Prod r Text (Located Token) Location
_neither = word "neither" ? "neither"
_no :: Prod r Text (Located Token) Location
_no = word "no" ? "no"
_nor :: Prod r Text (Located Token) Location
_nor = word "nor" ? "nor"
_not :: Prod r Text (Located Token) Location
_not = word "not" ? "not"
_omitted :: Prod r Text (Located Token) Location
_omitted = word "omitted" ? "omitted"
_on :: Prod r Text (Located Token) Location
_on = word "on" ? "on"
_oneOf :: Prod r Text (Located Token) Location
_oneOf = word "one" <* word "of" ? "one of"
_or :: Prod r Text (Located Token) Location
_or = word "or" ? "or"
_particularly :: Prod r Text (Located Token) Location
_particularly = (word "particularly" <|> (word "in" *> word "particular")) <* _comma ? "particularly"
_relation :: Prod r Text (Located Token) Location
_relation = word "relation" ? "relation"
_satisfying :: Prod r Text (Located Token) Location
_satisfying = _suchThat <|> word "satisfying" ? "satisfying"
_setOf :: Prod r Text (Located Token) Location
_setOf = word "set" <* word "of" ? "set of"
_now :: Prod r Text (Located Token) Location
_now = (word "then" <|> word "next" <|> word "now" <|> word "first" <|> word "finally" <|> word "subsequently" <|> word "ultimately")
_show :: Prod r Text (Located Token) Location
_show = optional _now *> optional (word "we") *> word "show" <* optional (word "that")
_since :: Prod r Text (Located Token) Location
_since = word "since" <|> word "because" ? "since"
_some :: Prod r Text (Located Token) Location
_some = word "some" ? "some"
_suchThat :: Prod r Text (Located Token) Location
_suchThat = ((word "such" <* word "that") <|> (word "s" <* _dot <* word "t" <* _dot)) ? "such that"
_sufficesThat :: Prod r Text (Located Token) Location
_sufficesThat = word "it" <* word "suffices" <* word "to" <* word "show" <* word "that" ? "it suffices to show"
_suppose :: Prod r Text (Located Token) Location
_suppose = (word "suppose" <|> word "assume") <* optional (word "that") ? "assume"
_take :: Prod r Text (Located Token) Location
_take = optional _now *> (word "take" <|> word "consider") ? "take"
_that :: Prod r Text (Located Token) Location
_that = word "that" ? "that"
_the :: Prod r Text (Located Token) Location
_the = word "the" ? "the"
_then :: Prod r Text (Located Token) Location
_then = word "then" ? "then"
_thus :: Prod r Text (Located Token) Location
_thus = word "thus" <|> word "hence" <|> _now <|> word "therefore" ? "thus"
_trivial :: Prod r Text (Located Token) Location
_trivial = word "straightforward" <|> word "trivial" ? "trivial"
_unique :: Prod r Text (Located Token) Location
_unique = word "unique" ? "unique"
_write :: Prod r Text (Located Token) Location
_write = (optional (word "we") *> word "say" <* optional (word "that")) <|> (optional (word "we") *> word "write") ? "write"

-- | Introducing plain claims in proofs.
_haveIntro :: Prod r Text (Located Token) Location
_haveIntro = _thus <|> _particularly <|> _have

-- * Symbols

_colon :: Prod r Text (Located Token) Location
_colon = symbol ":" ? ":"
_pipe :: Prod r Text (Located Token) Location
_pipe = (optional (command "middle") *> symbol "|") <|> command "mid" ? "\\mid"
_comma :: Prod r Text (Located Token) Location
_comma = symbol "," ? ","
_commaAnd :: Prod r Text (Located Token) Location
_commaAnd = symbol "," <* optional (word "and") ? ", and"
_commaOr :: Prod r Text (Located Token) Location
_commaOr = symbol "," <* optional (word "or") ? ", or"
_defeq :: Prod r Text (Located Token) Location
_defeq = symbol ":=" ? ":=" -- Should use `\coloneq` from unicode-math as display.
_dot :: Prod r Text (Located Token) Location
_dot = symbol "." ? "."
_eq :: Prod r Text (Located Token) Location
_eq = symbol "=" ? "="
_in :: Prod r Text (Located Token) Location
_in = command "in" ? "\\in"
_subseteq :: Prod r Text (Located Token) Location
_subseteq = command "subseteq" ? "\\subseteq"
_to :: Prod r Text (Located Token) Location
_to = command "to" ? "\\to"
_mapsto :: Prod r Text (Located Token) Location
_mapsto = command "mapsto" ? "\\mapsto"
_ampersand :: Prod r Text (Located Token) Location
_ampersand = symbol "&" ? "&"
