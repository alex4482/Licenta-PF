module OtherFunctions

open ../DataTypes


val negateLit : literal -> literal
let negateLit (lit: literal)
    = match lit with
        | Var x -> NotVar x
        | NotVar x -> Var x
        

val getLiteralValueFromMem : literal -> memory -> bool & bool
let rec getLiteralValueFromMem (lit: literal) (m: memory) = 
    match m with
        | [] -> false, false
        | memHead :: memTail ->
            match lit with
                | Var myLitName -> 
                    if (String.compare myLitName memHead.name) = 0
                        then true, memHead.value
                        else getLiteralValueFromMem (Var myLitName) memTail
                | NotVar myLitName -> 
                    if (String.compare myLitName memHead.name) = 0
                        then true, not memHead.value
                        else getLiteralValueFromMem (NotVar myLitName) memTail
        


val getUnassignedLiteralsFromClause : clause -> memory -> list literal
let rec getUnassignedLiteralsFromClause (cl: clause) (m: memory) 
    : list literal
    = match cl with
        | Lit lit -> let isLitAssigned, litValue = getLiteralValueFromMem lit m in
                    if not isLitAssigned
                        then
                            [lit]
                        else
                            []
        | Disj cl1 cl2 -> let l1 = getUnassignedLiteralsFromClause cl1 m in
                            let l2 = getUnassignedLiteralsFromClause cl2 m in
                                append l1 l2


val assignLiteral : literal -> memory -> guessLevel -> memory
let assignLiteral (lit: literal) (m:memory) (guessLvl: guessLevel) = 
    match lit with
        | Var litName -> let newVarInfo = { name=litName; value=true; level=guessLvl } in newVarInfo :: m
        | NotVar litName -> let newVarInfo = { name=litName; value=false; level=guessLvl } in newVarInfo :: m


val isClauseTrueYet : clause -> memory -> bool
let rec isClauseTrueYet (cl: clause) (m:memory) = 
    match cl with
        | Lit lit -> let existsLit, litValue = getLiteralValueFromMem lit m in litValue
                        
        | Disj cl1 cl2 -> isClauseTrueYet cl1 m || isClauseTrueYet cl2 m


val isClauseFalse : clause -> memory -> bool
let rec isClauseFalse (cl: clause) (m:memory) = match m with
    | emptyMem -> false
    | _ -> match cl with
        | Lit lit -> let isLitAssigned, litValue = getLiteralValueFromMem lit m in
                            isLitAssigned && not litValue
        | Disj cl1 cl2 -> isClauseFalse cl1 m && isClauseFalse cl2 m
        
        
val getLiteralName : literal -> string
let getLiteralName (lit: literal) = match lit with
    | NotVar litName -> litName
    | Var litName -> litName

val findUnassignedLiteral : formula -> memory -> option literal & bool
let rec findUnassignedLiteral (f: formula) (m: memory) = match f with
    | [] -> None, false
    | headClause :: remainingFormula -> 
        let unasLiterals = getUnassignedLiteralsFromClause headClause m in
            match unasLiterals with 
                | [] -> findUnassignedLiteral remainingFormula m
                | headLiteral :: _ -> Some headLiteral, true