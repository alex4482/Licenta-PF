module ConflictFunctions

open ../DataTypes
(*open FStar.List
open FStar.All
module Math = FStar.Math.Lib
module L = FStar.List.Tot*)

let intersect (#a:eqtype) (l1: list a) (l2: list a) : list a = 
    let existsInList2 = (fun (x: a) -> L.contains x l2) in
        L.filter existsInList2 l1
        
val getAllLiteralsFromClause : clause -> list literal
let rec getAllLiteralsFromClause cl = match cl with
    | Lit lit -> [lit]
    | Disj cl1 cl2 -> intersect (getAllLiteralsFromClause cl1) (getAllLiteralsFromClause cl2)


let removeFromList (#a:eqtype) (el: a) (someList: list a) = filter (fun (x: a) -> not (x = el)) someList 


val backTrackTo : guessLevel -> memory -> memory
let rec backTrackTo currentLevel m = 
    if m = [] 
        then []
        else 
            let (var :: otherMem) = m in
                let backTrackToOtherMem = backTrackTo currentLevel otherMem in
                if var.level > currentLevel
                    then backTrackToOtherMem
                    else var :: backTrackToOtherMem


val getLiteralGuessLevelFromMem : memory -> literal -> ML guessLevel
let rec getLiteralGuessLevelFromMem m l  = 
    if m = [] 
        then failwith "literal should have guess level in memory but does not have" 
        else
            let (var :: otherMem) = m in
              if var.name = (getLiteralName l)
                then var.level
                else getLiteralGuessLevelFromMem otherMem l
        
val getMaxLevelFrom : list guessLevel -> ML guessLevel
let getMaxLevelFrom levels =
  if levels = []
    then failwith "error at get max level from" 
    else
        let (level :: otherLevels) = levels in
          L.fold_left (fun (x: guessLevel) (y: guessLevel) -> if x >= y then x else y) level otherLevels


val removeLevelsBiggerThan : list guessLevel -> guessLevel -> list guessLevel
let rec removeLevelsBiggerThan levelsList x = 
    if levelsList = [] 
        then [] 
        else 
            let (level :: otherLevels) = levelsList in
                if level >= x
                    then removeLevelsBiggerThan otherLevels x
                    else level :: removeLevelsBiggerThan otherLevels x

val makeClauseFromLiterals : list literal -> ML clause
let rec makeClauseFromLiterals (literals: list literal ) = match literals with
    | [] -> failwith "error at resolution when making clause from literals"
    | (l :: []) -> Lit l
    | (l :: otherLiterals) -> Disj (Lit l) (makeClauseFromLiterals otherLiterals)


val getHighestLevelBelowConflict : list literal -> guessLevel -> memory -> ML guessLevel
let getHighestLevelBelowConflict literals conflictLevel m =
    let allLevels = map (getLiteralGuessLevelFromMem m) literals in
        getMaxLevelFrom (removeLevelsBiggerThan allLevels conflictLevel)


val resoluteTwoClauses : clause -> clause -> literal -> guessLevel -> memory -> ML ( clause & guessLevel)
let resoluteTwoClauses cl1 cl2 pivot conflictLevel m =
  let firstLiterals = removeFromList (negateLit pivot) (getAllLiteralsFromClause cl1) in
    let secondLiterals = removeFromList pivot (getAllLiteralsFromClause cl2) in
        if firstLiterals = []
            then
              if secondLiterals = []
                then failwith "error at resolution of 2 clauses"
                else
                  if (length secondLiterals) = 1
                    then (Lit (hd secondLiterals), 0)
                    else 
                        let highestLevelBelowConflict = getHighestLevelBelowConflict secondLiterals conflictLevel m in
                            let newClause = makeClauseFromLiterals secondLiterals in
                                (newClause, highestLevelBelowConflict)
            else
              if secondLiterals = []
                then
                  if (length firstLiterals) = 1
                    then (Lit (hd firstLiterals), 0)
                    else
                        let newClause = makeClauseFromLiterals firstLiterals in
                            let highestLevelBelowConflict = getHighestLevelBelowConflict firstLiterals conflictLevel m in
                                (newClause, highestLevelBelowConflict)
                else 
                    let bothClauseLiterals = append secondLiterals firstLiterals in
                        let newClause = makeClauseFromLiterals bothClauseLiterals in
                            let highestLevelBelowConflict = getHighestLevelBelowConflict bothClauseLiterals conflictLevel m in
                                (newClause, highestLevelBelowConflict)


        
val findSecondClauseForResolution' : list literal -> list clause -> ML ( clause & literal )
let rec findSecondClauseForResolution' faultyLiterals clauses =
    if faultyLiterals = [] then failwith "error when finding second clause for resolution, no faulty literals" else
        if clauses = [] then failwith "error when finding second clause for resolution, no other clauses given" else
            let (cl :: otherClauses) = clauses in
                let clauseLiterals = getAllLiteralsFromClause cl in
                    let foundLiterals = intersect faultyLiterals clauseLiterals in
                        if [] = foundLiterals
                            then findSecondClauseForResolution' faultyLiterals otherClauses
                            else (cl, hd foundLiterals)

val findSecondClauseForResolution : clause -> list clause -> list literal -> ML (clause & literal)
let findSecondClauseForResolution firstClause otherClauses faultyLiterals =
    let firstClauseLiterals = getAllLiteralsFromClause firstClause in 
        if (intersect firstClauseLiterals faultyLiterals) = []
            then 
                let negatedFaultyLiterals = L.map negateLit faultyLiterals in
                    let faultyFirstClauseLiterals = intersect firstClauseLiterals negatedFaultyLiterals in
                        let negatedFaultyFirstClauseLiterals = L.map negateLit faultyFirstClauseLiterals in
                            findSecondClauseForResolution' negatedFaultyFirstClauseLiterals otherClauses
            else 
                let faultyFirstClauseLiterals = intersect firstClauseLiterals faultyLiterals in
                    let negatedFaultyFirstClauseLiterals = L.map negateLit faultyFirstClauseLiterals in
                        findSecondClauseForResolution' negatedFaultyFirstClauseLiterals otherClauses        

        
val resolution' : list clause -> guessLevel -> list literal -> guessLevel -> memory -> ML (list clause & guessLevel)
let rec resolution' clauses conflictLevel faultyLiterals backTrackLevel m =
  if L.length clauses = 1
    then (clauses, backTrackLevel)
    else
      let firstClause = hd clauses in
       let (secondClause, literalToRemove) = findSecondClauseForResolution firstClause (tl clauses) faultyLiterals in
           let (newClause, newGuessLevel) = resoluteTwoClauses firstClause secondClause literalToRemove conflictLevel m in
            let auxClauses = removeFromList secondClause (tl clauses) in
               resolution' auxClauses conflictLevel faultyLiterals (Math.max backTrackLevel newGuessLevel) m

        
val resolution : list clause -> guessLevel -> list literal -> memory -> ML (clause & guessLevel)
let resolution clauses conflictLevel faultyLiterals m =
    let (finalClause, guessLevel) = resolution' clauses conflictLevel faultyLiterals (-1) m in 
        if L.length finalClause = 1  
            then (hd finalClause, guessLevel)
            else failwith "more than 1 clause resulted in the resolution"


val findClausesForResolution : formula -> list literal -> list clause
let rec findClausesForResolution f faultyLiterals = 
    match f with
        | [] -> []
        | (clause :: otherClauses) -> 
          let clauseLiterals = getAllLiteralsFromClause clause in 
            let literalsList = intersect (L.map negateLit faultyLiterals) clauseLiterals in
                if literalsList = []
                    then findClausesForResolution otherClauses faultyLiterals
                    else intersect [clause] (findClausesForResolution otherClauses faultyLiterals)

val findFaultyLiteralsInConflict : clause -> guessLevel -> memory -> ML (list literal)
let rec findFaultyLiteralsInConflict cl guessLevel m = match cl with
    | Lit lit -> 
        let litGuessLevel = getLiteralGuessLevelFromMem m lit in
            if litGuessLevel = guessLevel 
                then [lit]
                else []
    | Disj cl1 cl2 -> 
        let faultyLiterals1 = findFaultyLiteralsInConflict cl1 guessLevel m in
            let faultyLiterals2 = findFaultyLiteralsInConflict cl2 guessLevel m in
                intersect faultyLiterals1 faultyLiterals2

val solveConflict : formula -> memory -> guessLevel -> clause -> ML (formula & memory & guessLevel)
let solveConflict f m conflictLevel conflictClause =
  let faultyLiterals = findFaultyLiteralsInConflict conflictClause conflictLevel m in
    let clausesForResolution = findClausesForResolution f faultyLiterals in
        if clausesForResolution = []         
            then failwith "error at solveConflict, should not be empty"  
            else                               
              let (newClause, newLevel) = resolution clausesForResolution conflictLevel faultyLiterals m
               in (newClause :: f, backTrackTo newLevel m, newLevel)


val existsConflict : formula -> memory -> (option clause) & bool
let rec existsConflict f m : Tot ((option clause) & bool) (decreases (L.length f)) = 
    if f = [] 
        then (None, false)
        else if m = [] 
                then (None, false)
                else 
                    let cl :: remainingF = f in
                        if isClauseFalse cl m
                            then (Some cl, true)
                        else existsConflict remainingF m