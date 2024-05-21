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

import Text.Earley (Prod, (<?>), terminal)
import Text.Megaparsec (SourcePos)

infixr 0 ?
-- | Variant of '<?>' for annotating literal tokens.
(?) :: Prod r Text t a -> Text -> Prod r Text t a
p ? e = p <?> ("\"" <> e <> "\"")

word :: Text -> Prod r Text (Located Token) SourcePos
word w = terminal maybeToken
   where
      maybeToken ltok = case unLocated ltok of
         Word w' | w == w' -> Just (startPos ltok)
         _ -> Nothing

symbol :: Text -> Prod r Text (Located Token) SourcePos
symbol s = terminal maybeToken
   where
      maybeToken ltok = case unLocated ltok of
         Symbol s' | s == s' -> Just (startPos ltok)
         _ -> Nothing

command :: Text -> Prod r Text (Located Token) SourcePos
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

_an :: Prod r Text (Located Token) SourcePos
_an = word "a" <|> word "an" <?> "indefinite article"
_and :: Prod r Text (Located Token) SourcePos
_and = word "and" ? "and"
_are :: Prod r Text (Located Token) SourcePos
_are = word "are" ? "are"
_asFollows :: Prod r Text (Located Token) SourcePos
_asFollows = word "as" <* word "follows" ? "as follows"
_assumption :: Prod r Text (Located Token) SourcePos
_assumption = word "assumption" ? "assumption"
_be :: Prod r Text (Located Token) SourcePos
_be = word "be" ? "be"
_by :: Prod r Text (Located Token) SourcePos
_by = word "by" ? "by"
_bySetExt :: Prod r Text (Located Token) SourcePos
_bySetExt = word "by" <* ((word "set" ? "set") <* word "extensionality") ? "by set extensionality"
_can :: Prod r Text (Located Token) SourcePos
_can = word "can" ? "can"
_consistsOf :: Prod r Text (Located Token) SourcePos
_consistsOf = word "consists" <* word "of" ? "consists of"
_contradiction :: Prod r Text (Located Token) SourcePos
_contradiction = optional (word "a") *> word "contradiction" ? "a contradiction"
_define :: Prod r Text (Located Token) SourcePos
_define = word "define" ? "define"
_definition :: Prod r Text (Located Token) SourcePos
_definition = word "definition" ? "definition"
_denote :: Prod r Text (Located Token) SourcePos
_denote = word "denote" <|> (word "stand" <* word "for") ? "denote"
_denotes :: Prod r Text (Located Token) SourcePos
_denotes = word "denotes" ? "denotes"
_do :: Prod r Text (Located Token) SourcePos
_do = word "do" ? "do"
_does :: Prod r Text (Located Token) SourcePos
_does = word "does" ? "does"
_either :: Prod r Text (Located Token) SourcePos
_either = word "either" ? "either"
_equipped :: Prod r Text (Located Token) SourcePos
_equipped = (word "equipped" <|> word "together") <* word "with" ? "equipped with"
_every :: Prod r Text (Located Token) SourcePos
_every = (word "every") ? "every"
_exist :: Prod r Text (Located Token) SourcePos
_exist = word "there" <* word "exist" ? "there exist"
_exists :: Prod r Text (Located Token) SourcePos
_exists = word "there" <* word "exists" ? "there exists"
_extends :: Prod r Text (Located Token) SourcePos
_extends = (_is) <|> (word "consists" <* word "of") ? "consists of"
_fix :: Prod r Text (Located Token) SourcePos
_fix = word "fix" ? "fix"
_follows :: Prod r Text (Located Token) SourcePos
_follows = word "follows" ? "follows"
_for :: Prod r Text (Located Token) SourcePos
_for = word "for" ? "for"
_forAll :: Prod r Text (Located Token) SourcePos
_forAll = (word "for" <* word "all") <|> word "all" ? "all"
_forEvery :: Prod r Text (Located Token) SourcePos
_forEvery = (word "for" <* word "every") <|> (word "every") ? "for every"
_have :: Prod r Text (Located Token) SourcePos
_have = word "we" <* word "have" <* optional (word "that") ? "we have"
_if :: Prod r Text (Located Token) SourcePos
_if = word "if" ? "if"
_iff :: Prod r Text (Located Token) SourcePos
_iff = word "iff" <|> (word "if" <* word "and" <* word "only" <* word "if") ? "iff"
_inductively :: Prod r Text (Located Token) SourcePos
_inductively = word "inductively" ? "inductively"
_is :: Prod r Text (Located Token) SourcePos
_is = word "is" ? "is"
_itIsWrong :: Prod r Text (Located Token) SourcePos
_itIsWrong = word "it" <* word "is" <* (word "not" <* word "the" <* word "case" <|> word "wrong") <* word "that" ? "it is wrong that"
_let :: Prod r Text (Located Token) SourcePos
_let = word "let" ? "let"
_neither :: Prod r Text (Located Token) SourcePos
_neither = word "neither" ? "neither"
_no :: Prod r Text (Located Token) SourcePos
_no = word "no" ? "no"
_nor :: Prod r Text (Located Token) SourcePos
_nor = word "nor" ? "nor"
_not :: Prod r Text (Located Token) SourcePos
_not = word "not" ? "not"
_omitted :: Prod r Text (Located Token) SourcePos
_omitted = word "omitted" ? "omitted"
_on :: Prod r Text (Located Token) SourcePos
_on = word "on" ? "on"
_oneOf :: Prod r Text (Located Token) SourcePos
_oneOf = word "one" <* word "of" ? "one of"
_or :: Prod r Text (Located Token) SourcePos
_or = word "or" ? "or"
_particularly :: Prod r Text (Located Token) SourcePos
_particularly = (word "particularly" <|> (word "in" *> word "particular")) <* _comma ? "particularly"
_relation :: Prod r Text (Located Token) SourcePos
_relation = word "relation" ? "relation"
_satisfying :: Prod r Text (Located Token) SourcePos
_satisfying = _suchThat <|> word "satisfying" ? "satisfying"
_setOf :: Prod r Text (Located Token) SourcePos
_setOf = word "set" <* word "of" ? "set of"
_show :: Prod r Text (Located Token) SourcePos
_show = optional (word "first" <|> word "finally" <|> word "next" <|> word "now") *> optional (word "we") *> word "show" <* optional (word "that")
_since :: Prod r Text (Located Token) SourcePos
_since = word "since" <|> word "because" ? "since"
_some :: Prod r Text (Located Token) SourcePos
_some = word "some" ? "some"
_suchThat :: Prod r Text (Located Token) SourcePos
_suchThat = ((word "such" <* word "that") <|> (word "s" <* _dot <* word "t" <* _dot)) ? "such that"
_sufficesThat :: Prod r Text (Located Token) SourcePos
_sufficesThat = word "it" <* word "suffices" <* word "to" <* word "show" <* word "that" ? "it suffices to show"
_suppose :: Prod r Text (Located Token) SourcePos
_suppose = (word "suppose" <|> word "assume") <* optional (word "that") ? "assume"
_take :: Prod r Text (Located Token) SourcePos
_take = word "take" <|> word "consider" ? "take"
_that :: Prod r Text (Located Token) SourcePos
_that = word "that" ? "that"
_the :: Prod r Text (Located Token) SourcePos
_the = word "the" ? "the"
_then :: Prod r Text (Located Token) SourcePos
_then = word "then" ? "then"
_throughout :: Prod r Text (Located Token) SourcePos
_throughout = word "throughout" <* optional (word "this" <* word "section") <* optional _comma <|> (word "in" <* word "the" <* word "sequel") ? "throughout"
_thus :: Prod r Text (Located Token) SourcePos
_thus = word "thus" <|> word "then" <|> word "hence" <|> word "now" <|> word "finally" <|> word "therefore" ? "thus"
_trivial :: Prod r Text (Located Token) SourcePos
_trivial = word "straightforward" <|> word "trivial" ? "trivial"
_unique :: Prod r Text (Located Token) SourcePos
_unique = word "unique" ? "unique"
_write :: Prod r Text (Located Token) SourcePos
_write = (optional (word "we") *> word "say" <* optional (word "that")) <|> (optional (word "we") *> word "write") ? "write"

-- | Introducing plain claims in proofs.
_haveIntro :: Prod r Text (Located Token) SourcePos
_haveIntro = _thus <|> _particularly <|> _have

-- * Symbols

_colon :: Prod r Text (Located Token) SourcePos
_colon = symbol ":" ? ":"
_pipe :: Prod r Text (Located Token) SourcePos
_pipe = (optional (command "middle") *> symbol "|") <|> command "mid" ? "\\mid"
_comma :: Prod r Text (Located Token) SourcePos
_comma = symbol "," ? ","
_commaAnd :: Prod r Text (Located Token) SourcePos
_commaAnd = symbol "," <* optional (word "and") ? ", and"
_commaOr :: Prod r Text (Located Token) SourcePos
_commaOr = symbol "," <* optional (word "or") ? ", or"
_defeq :: Prod r Text (Located Token) SourcePos
_defeq = symbol ":=" ? ":=" -- Should use `\coloneq` from unicode-math as display.
_dot :: Prod r Text (Located Token) SourcePos
_dot = symbol "." ? "."
_eq :: Prod r Text (Located Token) SourcePos
_eq = symbol "=" ? "="
_in :: Prod r Text (Located Token) SourcePos
_in = symbol "∈" <|> command "in" ? "\\in"
_subseteq :: Prod r Text (Located Token) SourcePos
_subseteq = command "subseteq" ? "\\subseteq"
