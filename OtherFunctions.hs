module OtherFunctions where

import DataTypes

negateLit :: Literal -> Literal
negateLit (Var l) = NotVar l
negateLit (NotVar l) = Var l

getUnassignedLiteralsFromClause :: Clause -> Mem -> [Literal]
getUnassignedLiteralsFromClause (Lit literal) mem = let (isLitAssigned, litValue) = getLitValueFromMem literal mem in
                                                ([literal | not isLitAssigned ]) --returns literal if it isnt in memory
getUnassignedLiteralsFromClause (Disj cl1 cl2) mem = getUnassignedLiteralsFromClause cl1 mem ++ getUnassignedLiteralsFromClause cl2 mem


getLitValueFromMem :: Literal -> Mem -> (Bool, Bool) --the first bool says if literal appears in memory, the second one is the value if it appears in memory
getLitValueFromMem _ [] = (False, False)
getLitValueFromMem (Var myLitName) ( (literalName, literalValue, _) : remainingMem) = if myLitName == literalName
                                                                                then (True, literalValue )
                                                                                else getLitValueFromMem (Var myLitName) remainingMem
getLitValueFromMem (NotVar myLitName) ( (literalName, literalValue, _) : remainingMem) = if myLitName == literalName
                                                                                then (True, not literalValue )
                                                                                else getLitValueFromMem (NotVar myLitName) remainingMem

assignLiteral :: Literal -> Mem -> GuessLevel -> Mem
assignLiteral (Var literal) mem guessLevel = (literal, True, guessLevel) : mem --can be made better (not make them automaticaly false)
assignLiteral (NotVar literal) mem guessLevel = (literal, False, guessLevel) : mem

isClauseTrueYet :: Clause -> Mem -> Bool
isClauseTrueYet (Lit literal) mem = snd (getLitValueFromMem literal mem)
isClauseTrueYet (Disj cl1 cl2) mem = isClauseTrueYet cl1 mem || isClauseTrueYet cl2 mem


isClauseFalse :: Clause -> Mem -> Bool
isClauseFalse _ [] = False
isClauseFalse (Lit literal) mem = let (isLitAssigned, litValue) = getLitValueFromMem literal mem in
                             isLitAssigned && litValue
isClauseFalse (Disj cl1 cl2) mem = isClauseFalse cl1 mem || isClauseFalse cl2 mem
--isClauseFalse (Lit (NotVar litName)) mem = let (isLitAssigned, litValue) = getLitValueFromMem litName mem in
--                             isLitAssigned && not litValue
--isClauseFalse (Lit (Var litName)) mem = let (isLitAssigned, litValue) = getLitValueFromMem litName mem in
--                             isLitAssigned && litValue

getLiteralName :: Literal -> String
getLiteralName (Var litName) = litName
getLiteralName (NotVar litName) = litName


findUnassignedLiteral :: Formula -> Mem -> (Literal, Bool)
findUnassignedLiteral [] _ = (Var "empty", False)
findUnassignedLiteral (clause : remainingFormula) mem = let unasLiterals = getUnassignedLiteralsFromClause clause mem in
                                            if count unasLiterals > 0
                                                then (head unasLiterals, True)
                                                else findUnassignedLiteral remainingFormula mem

fromJust :: Maybe a -> a
fromJust Nothing = error "fromJust"
fromJust (Just element) = element

remove :: Eq a => a -> [a] -> [a]
remove _ [] = []
remove element (headEl : array) = if element == headEl 
                                    then remove element array
                                    else headEl : remove element array

count :: Num p => [a] -> p
count [] = 0
count (elem : array) = 1 + count array
--count array = foldr (\ elem -> (+) 1) 0 array