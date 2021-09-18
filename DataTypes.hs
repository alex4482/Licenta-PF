module DataTypes where

data Literal = Var String | NotVar String deriving (Eq, Show)

data Clause = Disj Clause Clause | Lit Literal  deriving (Eq, Show)

type Mem = [(String,Bool, Integer )] --variable name, value, level of guess
type Formula = [Clause]
type GuessLevel = Integer -- current level of guesses/implications

emptyMem :: Mem
emptyMem = [] --holds all literals