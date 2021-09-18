module DPLLPropagation where

import DataTypes
import OtherFunctions

--function that does propagating before a guess/other step
propagate :: Formula -> Mem -> GuessLevel -> Mem
propagate [] mem currentLevel = mem
propagate formula mem currentLevel =
  --let (newMem, didPropagate) = unitClausePropagation (pureLiteralPropagation formula mem)
  let (newFormula, newMem, didPropagate) = pureLiteralPropagation formula mem currentLevel
   in if didPropagate
        then propagate newFormula newMem currentLevel
        else
          let (newMem', didPropagate') = unitClausePropagation formula newMem currentLevel
           in if didPropagate'
                then propagate formula newMem' currentLevel
                else newMem

--1111111111--functions for propagation of unit clauses case
unitClausePropagation :: Formula -> Mem -> GuessLevel -> (Mem, Bool)
unitClausePropagation [] mem currentLevel = (mem, False)
unitClausePropagation (clause : remainingFormula) mem currentLevel =
  let (newMem, didPropagate) = propagateUnitClause clause mem currentLevel
   in if didPropagate
        then (newMem, True)
        else unitClausePropagation remainingFormula mem currentLevel

propagateUnitClause :: Clause -> Mem -> GuessLevel -> (Mem, Bool)
propagateUnitClause clause mem currentLevel =
  let literals = getUnassignedLiteralsFromClause clause mem
   in if count literals == 1 || not (isClauseTrueYet clause mem)
        then (assignLiteral (head literals) mem currentLevel, True)
        else (mem, False)

--1111111111

--222222222--functions for propagation of pure literals case

pureLiteralPropagation :: Formula -> Mem -> GuessLevel -> (Formula, Mem, Bool)
pureLiteralPropagation formula mem currentLevel =
  let literalsFound = findOnePolarityLiteral formula
   in if not (null literalsFound)
        then
          let (newFormula, newMem) = pureLiteralPropagation' (eliminateClausesWithLiteral formula literalsFound) (assignAllLiteralsTrueInMem mem literalsFound currentLevel) currentLevel
           in (newFormula, newMem, True)
        else (formula, mem, False)

pureLiteralPropagation' :: Formula -> Mem -> GuessLevel -> (Formula, Mem)
pureLiteralPropagation' formula mem currentLevel =
  let literalsFound = findOnePolarityLiteral formula
   in if not (null literalsFound)
        then pureLiteralPropagation' (eliminateClausesWithLiteral formula literalsFound) (assignAllLiteralsTrueInMem mem literalsFound currentLevel) currentLevel
        else (formula, mem)

assignAllLiteralsTrueInMem :: Mem -> [Literal] -> GuessLevel -> Mem
assignAllLiteralsTrueInMem mem [] _ = mem
assignAllLiteralsTrueInMem mem ( literal : otherLiterals) currentLevel =
    let (appearsLiteralInMem, _) = getLitValueFromMem literal mem in
        if not appearsLiteralInMem
            then assignAllLiteralsTrueInMem (assignLiteral literal mem currentLevel) otherLiterals currentLevel
            else assignAllLiteralsTrueInMem mem otherLiterals currentLevel


findOnePolarityLiteral :: Formula -> [Literal]
findOnePolarityLiteral formula = findOnePolarityLiteral' formula []

findOnePolarityLiteral' :: Formula -> [Literal] -> [Literal]
findOnePolarityLiteral' clauses literals
  = foldl addOrRemoveLiteralsToArray literals clauses

addOrRemoveLiteralsToArray :: [Literal] -> Clause -> [Literal] --the literals at the end will be the ones with a single polarity
addOrRemoveLiteralsToArray literals (Lit literal)
  | literal `elem` literals = literals
  | negateLit literal `elem` literals = remove (negateLit literal) literals
  | otherwise = literal : literals
addOrRemoveLiteralsToArray literals (Disj cl1 cl2) = addOrRemoveLiteralsToArray (addOrRemoveLiteralsToArray literals cl1) cl2

eliminateClausesWithLiteral :: Formula -> [Literal] -> Formula
eliminateClausesWithLiteral [] literals = []
eliminateClausesWithLiteral (clause : otherFormula) literals =
  if not (existsLiteralsInClause clause literals)
    then clause : eliminateClausesWithLiteral otherFormula literals
    else eliminateClausesWithLiteral otherFormula literals

existsLiteralsInClause :: Clause -> [Literal] -> Bool
existsLiteralsInClause (Lit lit) literals = lit `elem` literals
existsLiteralsInClause (Disj cl1 cl2) literals = existsLiteralsInClause cl1 literals || existsLiteralsInClause cl2 literals

--22222222

--test for propagate  
--propagate [ (Disj (Lit (Var "a") ) (Lit (Var "b") ) ) , (Lit (NotVar "a")), (Disj (Lit (NotVar "a") ) (Lit (NotVar "b") ) )  ] emptyMem 0
--answer: [("b",True,0),("a",False,0)]
{-
*DPLLPropagation> propagate [ (Disj (Lit (Var "a") ) (Lit (Var "b") ) ) , (Lit (NotVar "a")), (Disj (Lit (NotVar "a") ) (Lit (NotVar "b") ) )  ] emptyMem 0
[("b",True,0),("a",False,0)]
*DPLLPropagation> propagate [ (Disj (Lit (Var "a") ) (Lit (Var "b") ) ) , (Lit (NotVar "a")) ] emptyMem 0                                                  
[("a",False,0),("b",True,0)]
*DPLLPropagation> propagate [ (Disj (Lit (Var "a") ) (Lit (NotVar "b") ) ) , (Lit (NotVar "a")) ] emptyMem 0
[("a",False,0),("b",False,0)]
-}