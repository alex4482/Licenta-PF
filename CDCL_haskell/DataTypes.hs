module CDCL_haskell.DataTypes where

--a literal has a string name and can be negated
data Literal = Var String | NotVar String deriving (Eq, Show)

--a clause can be a literal, or a disjunction between 2 clauses
data Clause = Disj Clause Clause | Lit Literal  deriving (Eq, Show)

type Mem = [(String, Bool, Integer )] --variable name, value, level of guess
type Formula = [Clause] --all clauses
type GuessLevel = Integer -- current level of guesses/implications

emptyMem :: Mem
emptyMem = [] --will hold all literals at the end

emptyFormula :: Formula
emptyFormula = []