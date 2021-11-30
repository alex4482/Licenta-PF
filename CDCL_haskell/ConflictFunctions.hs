module CDCL_haskell.ConflictFunctions where

import Data.List
import CDCL_haskell.DataTypes
import CDCL_haskell.OtherFunctions

--THE FUNCTIONS IN THIS FILE ARE STRICTLY USED FOR THE DISCOVERY AND SOLVING OF CONFLICTS

--returns Nothing,False if there is no conflict, or the false clause and True otherwise
existsConflict :: Formula -> Mem -> (Maybe Clause, Bool)
existsConflict [] _ = (Nothing, False)
existsConflict _ [] = (Nothing, False)
existsConflict (clause : formula) mem
  | isClauseFalse clause mem = (Just clause, True)
  | otherwise = existsConflict formula mem

--this function is called to salve a conflict and does everything up to adding new clause to formula,
--and backtracking to a certain guess level 
--if this function is called, for certain there is a conflict
solveConflict :: Formula -> Mem -> GuessLevel -> Clause -> (Formula, Mem, GuessLevel)
solveConflict formula mem conflictLevel conflictClause =
  let faultyLiterals = findFaultyLiteralsInConflict conflictClause conflictLevel mem
   in let clausesForResolution = findClausesForResolution formula faultyLiterals
       in if null clausesForResolution         
            then error "error at solveConflict, should not be empty"  
            else                               
              let (newClause, newLevel) = resolution clausesForResolution conflictLevel faultyLiterals mem
               in (newClause : formula, backTrackTo newLevel mem, newLevel)

--faulty literals means literals in the conflict clause which have the guess level of the conflict
findFaultyLiteralsInConflict :: Clause -> GuessLevel -> Mem -> [Literal] 
findFaultyLiteralsInConflict (Lit literal) guessLevel mem =
  [literal | getLiteralGuessLevelFromMem mem literal == guessLevel]
findFaultyLiteralsInConflict (Disj cl1 cl2) guessLevel mem =
  findFaultyLiteralsInConflict cl1 guessLevel mem `intersect` findFaultyLiteralsInConflict cl2 guessLevel mem

getLiteralGuessLevelFromMem :: Mem -> Literal -> GuessLevel
getLiteralGuessLevelFromMem ((name, _, level) : otherMem) literal =
  if name == getLiteralName literal
    then level
    else getLiteralGuessLevelFromMem otherMem literal
getLiteralGuessLevelFromMem [] _ = error "literal should have guess level in memory but does not have"


--it finds the clauses which contain the literals which caused the conflict
--(literals returned by findFaultyLiteralsInConflict function)
findClausesForResolution :: Formula -> [Literal] -> [Clause]
findClausesForResolution (clause : otherClauses) faultyLiterals =
  let clauseLiterals = getAllLiteralsFromClause clause
   in if null (map negateLit faultyLiterals `intersect` clauseLiterals)
        then findClausesForResolution otherClauses faultyLiterals
        else [clause] `intersect` findClausesForResolution otherClauses faultyLiterals
findClausesForResolution [] _ = []

getAllLiteralsFromClause :: Clause -> [Literal]
getAllLiteralsFromClause (Lit literal) = [literal]
getAllLiteralsFromClause (Disj cl1 cl2) = getAllLiteralsFromClause cl1 `intersect` getAllLiteralsFromClause cl2

--after resolution is applied , 1 clause will result, also the guessLevel to which to backtrack
--resolution need the clauses for the resolution, the conflict level, the literals which caused the conflict, and current memory
resolution :: [Clause] -> GuessLevel -> [Literal] -> Mem -> (Clause, GuessLevel)
resolution clauses conflictLevel faultyLiterals mem =
  let (finalClause, guessLevel) = resolution' clauses conflictLevel faultyLiterals (-1) mem
   in if length finalClause == 1 
        then (head finalClause, guessLevel)
        else error "more than 1 clause resulted in the resolution"

--same purpose as above, implements the logic, also keeps track of the level to which to back track 
resolution' :: [Clause] -> GuessLevel -> [Literal] -> GuessLevel -> Mem -> ([Clause], GuessLevel)
resolution' clauses conflictLevel faultyLiterals backTrackLevel mem =
  if length clauses == 1
    then (clauses, backTrackLevel)
    else
      let firstClause = head clauses
       in let (secondClause, literalToRemove) = findSecondClauseForResolution firstClause (tail clauses) faultyLiterals
           in let (newClause, newGuessLevel) = resoluteTwoClauses firstClause secondClause literalToRemove conflictLevel mem
               in resolution' (remove secondClause (tail clauses)) conflictLevel faultyLiterals (max backTrackLevel newGuessLevel) mem

--at every step of resolution, 2 clauses are taken to make another one
--the first one chosen is just the first one in the array, but the second one has to match the first one
findSecondClauseForResolution :: Clause -> [Clause] -> [Literal] -> (Clause, Literal)
findSecondClauseForResolution firstClause otherClauses faultyLiterals =
  let firstClauseLiterals = getAllLiteralsFromClause firstClause
   in if null (firstClauseLiterals `intersect` faultyLiterals)
        then findSecondClauseForResolution' (map negateLit (firstClauseLiterals `intersect` map negateLit faultyLiterals)) otherClauses
        else findSecondClauseForResolution' (map negateLit (firstClauseLiterals `intersect` faultyLiterals)) otherClauses

findSecondClauseForResolution' :: [Literal] -> [Clause] -> (Clause, Literal)
findSecondClauseForResolution' [] _ = error "error when finding second clause for resolution, no faulty literals"
findSecondClauseForResolution' _ [] = error "error when finding second clause for resolution, no other clauses given"
findSecondClauseForResolution' faultyLiterals (clause : otherClauses) =
  let clauseLiterals = getAllLiteralsFromClause clause
   in let foundLiterals = faultyLiterals `intersect` clauseLiterals
       in if null foundLiterals
            then findSecondClauseForResolution' faultyLiterals otherClauses
            else (clause, head foundLiterals)

--combine 2 clauses to make another one, and find a potential back track level from them
resoluteTwoClauses :: Clause -> Clause -> Literal -> GuessLevel -> Mem -> (Clause, GuessLevel)
resoluteTwoClauses cl1 cl2 pivot conflictLevel mem =
  let firstLiterals = remove (negateLit pivot) (getAllLiteralsFromClause cl1)
   in let secondLiterals = remove pivot (getAllLiteralsFromClause cl2)
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

--used to make a new clause from the literals of the 2 clauses in resolution, with exeption of the pivot literal
makeClauseFromLiterals :: [Literal] -> Clause
makeClauseFromLiterals [] = error "error at resolution when making clause from literals"
makeClauseFromLiterals [literal] = Lit literal
makeClauseFromLiterals (literal : otherLiterals) = Disj (makeClauseFromLiterals [literal]) (makeClauseFromLiterals otherLiterals)

--this function is used to find a potential level to which to back track to
--this level is the highest guess level of all literals from all clauses in the resolution
highestLevelBelowConflict :: [Literal] -> GuessLevel -> Mem -> GuessLevel
highestLevelBelowConflict literals conflictLevel mem =
  let allLevels = map (getLiteralGuessLevelFromMem mem) literals
   in getMaxLevelFrom (removeLevelsBiggerThan allLevels conflictLevel)

getMaxLevelFrom :: [GuessLevel] -> GuessLevel
getMaxLevelFrom levels =
  if null levels
    then error "error at get max level from"
    else foldr (\x y -> if x >= y then x else y) (head levels) (tail levels)

--the level to which to backtrack should not be >= to the conflict level
removeLevelsBiggerThan :: [GuessLevel] -> GuessLevel -> [GuessLevel]
removeLevelsBiggerThan [] x = []
removeLevelsBiggerThan (l : others) x =
  if l >= x
    then removeLevelsBiggerThan others x
    else l : removeLevelsBiggerThan others x

--removes all entries above given guessLevel, which is the backTrack level
backTrackTo :: GuessLevel -> Mem -> Mem
backTrackTo _ [] = []
backTrackTo currentLevel ((name, value, level) : otherMem) =
  if level > currentLevel
    then backTrackTo currentLevel otherMem
    else (name, value, level) : backTrackTo currentLevel otherMem
