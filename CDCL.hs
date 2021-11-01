import ConflictFunctions
import DPLLPropagation
import DataTypes
import OtherFunctions

--call this function with a formula and an array with information about the literals will be returned
--if the returned array is empty, the formula is unsatisfiable, otherwise, every literal will appear with a value and guess level
solveFormula :: Formula -> Mem
solveFormula f = solveFormula' f emptyMem 0

solveFormula' :: Formula -> Mem -> GuessLevel -> Mem
solveFormula' f mem currentLevel =
  let (conflictClause, isConflict) = existsConflict f mem
   in if isConflict
        then
          if null mem || currentLevel == 0
            then []
            else
              let (newF, newMem, newLevel) = solveConflict f mem currentLevel (fromJust conflictClause)
               in solveFormula' newF newMem newLevel
        else
            let newMem = propagate f mem currentLevel in
                let (lit, boolean) = findUnassignedLiteral f newMem  --boolean is true if there are unassigned literals
                    in if boolean
                        then solveFormula' f (assignLiteral (fromJust lit) newMem currentLevel) (currentLevel + 1)
                        --else newMem
                        else let (conflictClause2, isConflict2) = existsConflict f newMem
                         in if isConflict2
                              then solveFormula' f newMem currentLevel
                              else newMem
                           --

--addClauseToFormula :: Clause -> Formula -> Formula
--addClauseToFormula clause formula = formula ++ [clause]


--test for without guessing -- WORKS
-- [Disj (Lit (NotVar "a")) (Lit (Var "b")) , Disj (Lit (NotVar "a")) (Lit (NotVar "c")) , Lit (NotVar "b"), Disj (Lit (Var "b")) (Lit (Var "c")) ]

--wiki example test -OK answer
-- [ Disj (Lit (Var "x1")) (Lit (Var "x4")),Disj (Lit (Var "x1")) (Disj (Lit (NotVar "x3")) (Lit (NotVar "x8"))),Disj (Lit (Var "x1")) (Disj (Lit (Var "x8")) (Lit (Var "x12"))),Disj (Lit (Var "x2")) (Lit (Var "x11")),Disj (Lit (NotVar "x7")) (Disj (Lit (NotVar "x3")) (Lit (Var "x9"))),Disj (Lit (NotVar "x7")) (Disj (Lit (Var "x8")) (Lit (NotVar "x9"))), Disj (Lit (Var "x7")) (Disj (Lit (Var "x8")) (Lit (NotVar "x10"))),Disj (Lit (Var "x7")) (Disj (Lit (Var "x10")) (Lit (NotVar "x12")))]
--[("x10",False,1),("x7",False,0),("x8",True,0),("x9",False,0),("x12",False,0),("x1",True,0),("x4",True,0),("x3",False,0),("x2",True,0),("x11",True,0)]

{- bad example
solveFormula [Lit(Var "x1"), Lit(NotVar "x1")]
[]    
-}