module Rules where

import Sequents
import Formulas


alphaIng :: Form -> [Form]
alphaIng x = case x of
                 C z y -> [z, y]
                 N v -> case v of 
                            D z y -> [N z, N y]
                            I z y -> [z, N y]
                            N z   -> [z]

betaIng :: Form -> [Form]
betaIng x = case x of
                I a b -> [N a, b]
                D a b -> [a, b]
                N v -> case v of
                            C a b -> [N a, N b]



-- makes tuple with sorted formulas from sequent                        
sort :: Sequent -> ([Form], [Form], [Form], [Form], [Form], [Form])
sort x =  (lAlphaSeq x, rBetaSeq x, lBetaSeq x, rAlphaSeq x, lLiteral x, rLiteral x)
                                

sAnalizer :: ([Form], [Form], [Form], [Form], [Form], [Form]) -> HyperSequent
sAnalizer ([], [], [], [], [], [])          = []
sAnalizer ([], [], [], [], [], qs)          = [([], qs)]
sAnalizer ([], [], [], [], ws, qs)          = [(ws, qs)]
sAnalizer ([], [], [], r:rs, ws, qs)        = if length (alphaIng r) == 1 
                                                    then [(ws, (alphaIng r) ++ rs ++ qs)]
                                                    else [(ws, ((alphaIng r) !! 0) : rs ++ qs), (ws, ((alphaIng r) !! 1) : rs ++ qs)]
sAnalizer ([], [], z:zs, rs, ws, qs)        = [(((betaIng z) !! 0) : zs ++ ws, rs ++ qs), (((betaIng z) !! 1) : zs ++ ws, rs ++ qs)]
sAnalizer ([], y:ys, zs, rs, ws, qs)        = [(zs ++ ws, (betaIng y) ++ ys ++ rs ++ qs)]
sAnalizer (x:xs, ys, zs, rs, ws, qs)        = [((alphaIng x) ++ xs ++ zs ++ ws, ys ++ rs ++ qs)]

-- first formula from each sequent
sCreator :: HyperSequent -> HyperSequent
sCreator []     = []
sCreator (x:xs) = (sAnalizer (sort x)) ++ (sCreator xs)

-- first formula from first sequent
sCreator2 :: HyperSequent -> HyperSequent
sCreator2 []     = []
sCreator2 (x:xs) = (sAnalizer (sort x)) ++ xs

-- iterates sCreator until hypersequent is minimal
sCreatorIter :: HyperSequent -> HyperSequent
sCreatorIter []     = []
sCreatorIter (x:xs) = if isMinimal (sCreator (x:xs)) || abdProblem (sCreator (x:xs))
                        then sCreator (x:xs) 
                        else sCreatorIter (sCreator (x:xs))




{--sAnalizer :: ([Form], [Form], [Form], [Form], [Form], [Form]) -> HyperSequent
sAnalizer ([], [], [], [], [], [])          = []
sAnalizer (x:xs, y:ys, z:zs, r:rs, ws, qs)
                                            | (x:xs) /= [] = [((alphaIng x) ++ xs ++ (z:zs) ++ ws, (y:ys) ++ (r:rs) ++ qs)]
                                            | (y:ys) /= [] = [((z:zs) ++ ws, (betaIng y) ++ ys ++ (r:rs) ++ qs)]
                                            | (z:zs) /= [] = [(((betaIng z) !! 0) : zs ++ ws, (r:rs) ++ qs), (((betaIng z) !! 1) : zs ++ ws, (r:rs) ++ qs)]
                                            | (r:rs) /= [] = [(ws, ((alphaIng r) !! 0) : rs ++ qs), (ws, ((alphaIng r) !! 1) : rs ++ qs)]
                                            | otherwise    = [(ws, qs)]
--} 
