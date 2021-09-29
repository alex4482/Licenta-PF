module OtherFunctions where

import DataTypes


--all functions in this file have very suggestive names, and may be used be different functions in different files

negateLit :: Literal -> Literal
negateLit (Var l) = NotVar l
negateLit (NotVar l) = Var l

getUnassignedLiteralsFromClause :: Clause -> Mem -> [Literal]
getUnassignedLiteralsFromClause (Lit literal) mem = let (isLitAssigned, litValue) = getLiteralValueFromMem literal mem in
                                                ([literal | not isLitAssigned ]) --returns literal if it isnt in memory
getUnassignedLiteralsFromClause (Disj cl1 cl2) mem = getUnassignedLiteralsFromClause cl1 mem ++ getUnassignedLiteralsFromClause cl2 mem


getLiteralValueFromMem :: Literal -> Mem -> (Bool, Bool) --the first bool says if literal appears in memory, the second one is the value if it appears in memory
getLiteralValueFromMem _ [] = (False, False)
getLiteralValueFromMem (Var myLitName) ( (literalName, literalValue, _) : remainingMem) = if myLitName == literalName
                                                                                then (True, literalValue )
                                                                                else getLiteralValueFromMem (Var myLitName) remainingMem
getLiteralValueFromMem (NotVar myLitName) ( (literalName, literalValue, _) : remainingMem) = if myLitName == literalName
                                                                                then (True, not literalValue )
                                                                                else getLiteralValueFromMem (NotVar myLitName) remainingMem

--TODO: may have to make assignement random, and not to always be true???
assignLiteral :: Literal -> Mem -> GuessLevel -> Mem
assignLiteral (Var literal) mem guessLevel = (literal, True, guessLevel) : mem --can be made better (not make them automaticaly false)
assignLiteral (NotVar literal) mem guessLevel = (literal, False, guessLevel) : mem

--a clause is true if it has a literal with true value, or negated literal with false value
isClauseTrueYet :: Clause -> Mem -> Bool
isClauseTrueYet (Lit literal) mem = snd (getLiteralValueFromMem literal mem)
isClauseTrueYet (Disj cl1 cl2) mem = isClauseTrueYet cl1 mem || isClauseTrueYet cl2 mem

--a clause is false only if all literals have the false value (it may also contain negated literals with true value)
isClauseFalse :: Clause -> Mem -> Bool
isClauseFalse _ [] = False
isClauseFalse (Lit literal) mem = let (isLitAssigned, litValue) = getLiteralValueFromMem literal mem in
                             isLitAssigned && not litValue
isClauseFalse (Disj cl1 cl2) mem = isClauseFalse cl1 mem && isClauseFalse cl2 mem --it was ||

getLiteralName :: Literal -> String
getLiteralName (Var litName) = litName
getLiteralName (NotVar litName) = litName

findUnassignedLiteral :: Formula -> Mem -> (Maybe Literal, Bool)
findUnassignedLiteral [] _ = (Nothing, False)
findUnassignedLiteral (clause : remainingFormula) mem = let unasLiterals = getUnassignedLiteralsFromClause clause mem in
                                            if count unasLiterals > 0
                                                then (Just (head unasLiterals), True)
                                                else findUnassignedLiteral remainingFormula mem

fromJust :: Maybe a -> a
fromJust Nothing = error "fromJust value is a Nothing"
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