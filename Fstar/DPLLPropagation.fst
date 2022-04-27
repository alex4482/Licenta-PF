module DPLLPropagation

open ../DataTypes

////////////functions for propagation of unit clauses case 
val propagateUnitClause : clause -> memory -> guessLevel -> memory & bool
let propagateUnitClause (cl: clause) (m: memory) (currentLevel: guessLevel) =
  let literals = getUnassignedLiteralsFromClause cl m in
    match literals with
        | [] -> m, false
        | aLiteral :: remainingLiterals -> 
            match remainingLiterals with
                | [] -> 
                    let condition = isClauseTrueYet cl m in 
                        if condition
                            then m, false
                            else let newMem = assignLiteral aLiteral m currentLevel in
                                    newMem, true
                            
                | _ -> m, false
                
val unitClausePropagation : formula -> memory -> guessLevel -> memory
let rec unitClausePropagation (f: formula) (m: memory) (currentLevel: guessLevel) =
    match f with
        | [] -> m
        | aClause :: remainingFormula -> 
            let newMem, didPropagate = propagateUnitClause aClause m currentLevel in
                if didPropagate
                    then unitClausePropagation remainingFormula newMem currentLevel 
                    else newMem



////////////functions for propagation of pure literals case

val existsLiteralsInClause : clause -> list literal -> bool
let rec existsLiteralsInClause  (cl: clause) (literals: list literal) =
    match cl with
        | Lit lit -> contains lit literals 
        | Disj cl1 cl2 -> existsLiteralsInClause cl1 literals || existsLiteralsInClause cl2 literals

val eliminateClausesWithLiterals : formula -> list literal -> formula
let rec eliminateClausesWithLiterals (f: formula) (literals: list literal) : Tot formula (decreases f) =
    match f with
        | [] -> []
        | cl :: otherFormula -> 
            let exist = existsLiteralsInClause cl literals in
                let newRemainingFormula = eliminateClausesWithLiterals otherFormula literals in
                    if not exist
                        then cl :: newRemainingFormula
                        else newRemainingFormula
           


let filter_length (#a:_) (f:a -> bool) (l:list a)
  : Lemma (L.length (L.filter f l) <= L.length l)
  = admit()       

let rec removeLiteralsWithBothPolarities literals : Tot (list literal) (decreases (L.length literals)) = 
    match literals with
        | [] -> []
        | lit :: otherLiterals -> let negatedLit = negateLit lit in
            let doesContain = L.contains negatedLit otherLiterals in
            if doesContain 
                then 
                    let myFilter = (fun (x: literal) -> not (x = negatedLit || x = lit)) in
                        filter_length myFilter otherLiterals;
                        removeLiteralsWithBothPolarities (L.filter myFilter otherLiterals)
                                
                else
                    let newOtherLiterals = removeLiteralsWithBothPolarities otherLiterals in
                       lit :: newOtherLiterals
                 
let rec levelsInClause (cl: clause) : (res: int {res >= 0}) =
    match cl with
        | Lit lit -> 0
        | Disj cl1 cl2 -> 1 + Math.max (levelsInClause cl1) (levelsInClause cl2) 
        
let clause_level_compare (cl1: clause) (cl2: clause)
  : Lemma (levelsInClause cl1 > levelsInClause cl2)
  = admit()

val addOrRemoveLiteralsToArray : (literals: list literal) -> (cl: clause) -> Tot (list literal)
let rec addOrRemoveLiteralsToArray literals cl : Tot (list literal) (decreases (levelsInClause cl))  =
    match cl with
        | Lit literal -> 
            if L.contains literal literals 
                then literals
                else literal :: literals
        | Disj cl1 cl2 -> 
            clause_level_compare cl cl1;
            let newList = addOrRemoveLiteralsToArray literals cl1 in
                clause_level_compare cl cl2;
                addOrRemoveLiteralsToArray newList cl2

val findOnePolarityLiterals' : formula -> list literal -> list literal 
let findOnePolarityLiterals' (clauses: formula) (literals: list literal) =
    let newLiterals = L.fold_left addOrRemoveLiteralsToArray literals clauses in
        removeLiteralsWithBothPolarities newLiterals
                 
val findOnePolarityLiterals : formula -> list literal
let findOnePolarityLiterals (f: formula) = findOnePolarityLiterals' f []


val assignAllLiteralsTrueInMem : memory -> list literal -> guessLevel -> memory
let rec assignAllLiteralsTrueInMem m literals currentLevel : Tot memory (decreases literals) = 
    match literals with
        | [] -> m
        | _ -> let headLit :: otherLiterals = literals in
                let (appearsLiteralInMem, _) = getLiteralValueFromMem headLit m in
                if not appearsLiteralInMem
                    then assignAllLiteralsTrueInMem (assignLiteral headLit m currentLevel) otherLiterals currentLevel
                    else assignAllLiteralsTrueInMem m otherLiterals currentLevel

let formulasLengthLemma (f1: formula) (f2: formula)
  : Lemma (L.length f1 > L.length f2)
  = admit()  

val pureLiteralPropagation : formula -> memory -> guessLevel -> formula & memory 
let pureLiteralPropagation f m currentLevel : Tot (formula & memory) (decreases (L.length f)) =
  let literalsFound = findOnePolarityLiterals f
   in if not (literalsFound = [])
        then let smallerF = eliminateClausesWithLiterals f literalsFound in
            let newMem = assignAllLiteralsTrueInMem m literalsFound currentLevel in
                (smallerF, newMem)
        else (f, m)


val propagate : formula -> memory -> guessLevel -> memory
let propagate f m currentLevel : Tot memory  = 
        match f with
        | [] -> m
        | _ -> let (newFormula, newMem) = pureLiteralPropagation f m currentLevel in
                let newMem' = unitClausePropagation f newMem currentLevel
                   in newMem'