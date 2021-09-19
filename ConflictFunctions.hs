module ConflictFunctions where

import Data.List
import DataTypes
import OtherFunctions

existsConflict :: Formula -> Mem -> (Maybe Clause, Bool)
existsConflict [] _ = (Nothing, False)
existsConflict _ [] = (Nothing, False)
existsConflict (clause : formula) mem
  | isClauseFalse clause mem = (Just clause, True)
  | otherwise = existsConflict formula mem

solveConflict :: Formula -> Mem -> GuessLevel -> Clause -> (Formula, Mem, GuessLevel)
solveConflict formula mem conflictLevel conflictClause =
  let faultyLiterals = findFaultyLiteralsInConflict conflictClause conflictLevel mem
   in let clausesForResolution = findClausesForRes formula faultyLiterals
       in if null clausesForResolution         
            then error "error at solveConflict, should not be empty"  
            else                               
              let (newClause, newLevel) = resolution clausesForResolution conflictLevel faultyLiterals mem
               in (newClause : formula, backTrackTo newLevel mem, newLevel)

findFaultyLiteralsInConflict :: Clause -> GuessLevel -> Mem -> [Literal] --faulty literals means literals in the conflict clause which have highest guess level
findFaultyLiteralsInConflict (Lit literal) guessLevel mem =
  [literal | getGuessLevelFromMem mem literal == guessLevel]
findFaultyLiteralsInConflict (Disj cl1 cl2) guessLevel mem =
  findFaultyLiteralsInConflict cl1 guessLevel mem `intersect` findFaultyLiteralsInConflict cl2 guessLevel mem

getGuessLevelFromMem :: Mem -> Literal -> GuessLevel
getGuessLevelFromMem ((name, _, level) : otherMem) literal =
  if name == getLiteralName literal
    then level
    else getGuessLevelFromMem otherMem literal
getGuessLevelFromMem [] _ = error "literal should have guess level in memory but does not have"

findClausesForRes :: Formula -> [Literal] -> [Clause]
findClausesForRes (clause : otherClauses) faultyLiterals =
  let clauseLiterals = getLiteralsFromClause clause
   in if null (map negateLit faultyLiterals `intersect` clauseLiterals)
        then findClausesForRes otherClauses faultyLiterals
        else [clause] `intersect` findClausesForRes otherClauses faultyLiterals
findClausesForRes [] _ = []

getLiteralsFromClause :: Clause -> [Literal]
getLiteralsFromClause (Lit literal) = [literal]
getLiteralsFromClause (Disj cl1 cl2) = getLiteralsFromClause cl1 `intersect` getLiteralsFromClause cl2

resolution :: [Clause] -> GuessLevel -> [Literal] -> Mem -> (Clause, GuessLevel)
resolution clauses conflictLevel faultyLiterals mem =
  let (finalClause, guessLevel) = resolution' clauses conflictLevel faultyLiterals (-1) mem
   in (head finalClause, guessLevel)

resolution' :: [Clause] -> GuessLevel -> [Literal] -> GuessLevel -> Mem -> ([Clause], GuessLevel)
resolution' clauses conflictLevel faultyLiterals backTrackLevel mem =
  if length clauses == 1
    then (clauses, backTrackLevel)
    else
      let firstClause = head clauses
       in let (secondClause, literalToRemove) = findSecondClauseForResolution firstClause (tail clauses) faultyLiterals
           in let (newClause, newGuessLevel) = resoluteTwoClauses firstClause secondClause literalToRemove conflictLevel mem
               in resolution' (remove secondClause (tail clauses)) conflictLevel faultyLiterals (max backTrackLevel newGuessLevel) mem

findSecondClauseForResolution :: Clause -> [Clause] -> [Literal] -> (Clause, Literal)
findSecondClauseForResolution firstClause otherClauses faultyLiterals =
  let firstClauseLiterals = getLiteralsFromClause firstClause
   in if null (firstClauseLiterals `intersect` faultyLiterals)
        then findSecondClauseForResolution' (map negateLit (firstClauseLiterals `intersect` map negateLit faultyLiterals)) otherClauses
        else findSecondClauseForResolution' (map negateLit (firstClauseLiterals `intersect` faultyLiterals)) otherClauses

findSecondClauseForResolution' :: [Literal] -> [Clause] -> (Clause, Literal)
findSecondClauseForResolution' [] _ = error "error when finding second clause for resolution, no faunlty literals"
findSecondClauseForResolution' _ [] = error "error when finding second clause for resolution, no other clauses given"
findSecondClauseForResolution' faultyLiterals (clause : otherClauses) =
  let clauseLiterals = getLiteralsFromClause clause
   in let foundLiterals = faultyLiterals `intersect` clauseLiterals
       in if null foundLiterals
            then findSecondClauseForResolution' faultyLiterals otherClauses
            else (clause, head foundLiterals)

resoluteTwoClauses :: Clause -> Clause -> Literal -> GuessLevel -> Mem -> (Clause, GuessLevel)
resoluteTwoClauses cl1 cl2 pivot conflictLevel mem =
  let firstLiterals = remove (negateLit pivot) (getLiteralsFromClause cl1)
   in let secondLiterals = remove pivot (getLiteralsFromClause cl2)
       in if null firstLiterals
            then
              if null secondLiterals
                then error "error at resolution of 2 clauses"
                else
                  if length secondLiterals == 1
                    then (Lit (head secondLiterals), 0)
                    else (makeClauseFromLiterals secondLiterals, highestLevelBelowConflict secondLiterals conflictLevel mem)
            else
              if null secondLiterals
                then
                  if length firstLiterals == 1
                    then (Lit (head firstLiterals), 0)
                    else (makeClauseFromLiterals firstLiterals, highestLevelBelowConflict firstLiterals conflictLevel mem)
                else (makeClauseFromLiterals (secondLiterals ++ firstLiterals), highestLevelBelowConflict (secondLiterals ++ firstLiterals) conflictLevel mem)

makeClauseFromLiterals :: [Literal] -> Clause
makeClauseFromLiterals [] = error "error at resolution when making clause from literals"
makeClauseFromLiterals [literal] = Lit literal
makeClauseFromLiterals (literal : otherLiterals) = Disj (makeClauseFromLiterals [literal]) (makeClauseFromLiterals otherLiterals)

highestLevelBelowConflict :: [Literal] -> GuessLevel -> Mem -> GuessLevel
highestLevelBelowConflict literals conflictLevel mem =
  let allLevels = map (getGuessLevelFromMem mem) literals
   in getMaxLevelFrom (removeLevelsBiggerThan allLevels conflictLevel)

getMaxLevelFrom :: [GuessLevel] -> GuessLevel
getMaxLevelFrom levels =
  if null levels
    then error "error at get max level from"
    else foldr (\x y -> if x >= y then x else y) (head levels) (tail levels)

removeLevelsBiggerThan :: [GuessLevel] -> GuessLevel -> [GuessLevel]
removeLevelsBiggerThan [] x = []
removeLevelsBiggerThan (l : others) x =
  if l >= x
    then removeLevelsBiggerThan others x
    else l : removeLevelsBiggerThan others x

backTrackTo :: GuessLevel -> Mem -> Mem
backTrackTo _ [] = []
backTrackTo currentLevel ((name, value, level) : otherMem) =
  if level > currentLevel
    then backTrackTo currentLevel otherMem
    else (name, value, level) : backTrackTo currentLevel otherMem
