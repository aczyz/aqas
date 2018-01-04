module Formulas where


data Form =   V Int
            | N Form        --negation
            | C Form Form   --conjunction
            | D Form Form   --disjunction
            | I Form Form   --implication
            deriving (Eq, Read, Show)
            
-- checking if formula is a literal
isLiteral :: Form -> Bool
isLiteral x = case x of
                V _ -> True
                N z -> case z of
                            V _ -> True
                            _ -> False
                _   -> False

-- checking if formula is an alpha
alphaForm :: Form -> Bool
alphaForm x = case x of
                    C _ _ -> True
                    N z -> case z of 
                            D _ _ -> True
                            I _ _ -> True 
                            N z -> True
                            _ -> False
                    _ -> False        

-- checking if formula is a beta
betaForm :: Form -> Bool
betaForm x = not (alphaForm x) && not (isLiteral x)
