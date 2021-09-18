import DataTypes
import OtherFunctions
import DPLLPropagation
import ConflictFunctions


emptyFormula :: Formula
emptyFormula = []

addClauseToFormula :: Clause -> Formula -> Formula
addClauseToFormula clause formula = formula ++ [clause]


solveFormula :: Formula -> Mem
solveFormula f = solveFormula' f emptyMem 0


solveFormula' :: Formula -> Mem -> GuessLevel -> Mem
solveFormula' f mem currentLevel = let (conflictClause, isConflict) = existsConflict f mem in 
                if isConflict
                    then if null mem || currentLevel == 0 then [] else let (newF, newMem, newLevel) = solveConflict f mem currentLevel (fromJust conflictClause) in solveFormula' newF newMem newLevel
                    else let (lit, boolean) = findUnassignedLiteral f mem in --boolean is true if there are unassigned literals
                        if boolean
                            then let newMem = propagate f (assignLiteral lit mem currentLevel) (currentLevel+1)  in solveFormula' f newMem (currentLevel+1)
                            else mem




--test for without guessing
-- [Disj (Lit (NotVar "a")) (Lit (Var "b")) , Disj (Lit (NotVar "a")) (Lit (NotVar "c")) , Lit (NotVar "b"), Disj (Lit (Var "b")) (Lit (Var "c")) ]

