module CDCL

open ../DataTypes

val solveFormula' : formula -> memory -> guessLevel -> ML memory
let rec solveFormula' f m currentLevel =
  let (conflictClause, isConflict) = existsConflict f m in
    if isConflict
        then
          if m = [] || currentLevel = 0
            then []
            else
                let (newF, newMem, newLevel) = solveConflict f m currentLevel (FStar.Option.get conflictClause) in
                    solveFormula' newF newMem newLevel
        else
            let newMem = propagate f m currentLevel in
                let lit, boolean = findUnassignedLiteral f newMem in
                    if boolean
                        then
                            let updatedMem = assignLiteral (FStar.Option.get lit) newMem currentLevel in
                                let nextLevel = currentLevel + 1 in
                                    solveFormula' f updatedMem nextLevel
                        else 
                            let (conflictClause2, isConflict2) = existsConflict f newMem in
                                if isConflict2
                                      then solveFormula' f newMem currentLevel
                                      else newMem



val solveFormula : formula -> ML memory
let solveFormula f = solveFormula' f emptyMem 0