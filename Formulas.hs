module Formulas where


data Form =   V Int
            | N Form        --negation
            | C Form Form   --conjunction
            | D Form Form   --disjunction
            | I Form Form   --implication
            deriving (Eq, Read, Show)

isLiteral :: Form -> Bool   --checks whether literal or not
isLiteral x = case x of
                V _ -> True
                N z -> case z of
                            V _ -> True
                            _   -> False
                _   -> False

alphaForm :: Form -> Bool   --check if alpha
alphaForm x = case x of 
                    C _ _ -> True
                    N z   -> case z of 
                                D _ _ -> True
                                I _ _ -> True 
                                N _   -> True
                                _     -> False
                    _     -> False        

betaForm :: Form -> Bool   -- check if beta
betaForm x = not (alphaForm x) && not (isLiteral x) -- not alpha
