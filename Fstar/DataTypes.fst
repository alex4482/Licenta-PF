module DataTypes

type literal = 
    | Var : a:string -> literal
    | NotVar : a:string -> literal
    

type clause =
    | Lit : l: literal -> clause
    | Disj : x: clause -> y: clause -> clause

type guessLevel = int
type variableInfo = {name: string; value: bool; level: guessLevel}
    

type memory = list variableInfo
type formula = list clause


let emptyMem = []
let emptyFormula = []
