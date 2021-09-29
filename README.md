# Licenta-PF

CDCL.hs
- is the main file. import that one and you import them all.


DataTypes.hs
- contains definitions and explanations of all types of data used


DPLLPropagation.hs
- is a module which individually takes care of the propagation steps from DPLL algorithm
                    (imports DataTypes.hs and OtherFunctions.hs)


ConflictFunctions.hs
- is a module which individually takes care of finding and solving the conflicts in a formula
                    (imports DataTypes.hs and OtherFunctions.hs and Data.List)
               
               
OtherFunctions.hs
- is a module containing different functions with different functionalities, 
              that can be used by all other modules if needed (all of them are used by at least 1 other module at the moment)
