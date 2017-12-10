module Rules where

import Sequents
import Formulas

-- fst formulas's ingredients in a list (left side)   (why?)
lAlpha :: Sequent -> [Form]  
lAlpha (x:xs, ys) = alphaIng x

rAlpha :: Sequent -> [Form]  
rAlpha (xs, y:ys) = alphaIng y

lBeta :: Sequent -> [Form] -- left beta rule
lBeta (x:xs, ys) = betaIng x

rBeta :: Sequent -> [Form]
rBeta (xs, y:ys) = betaIng y

lDNeg :: Sequent -> HyperSequent -- not necessary as dbl neg is already an alpha, keeping just in case
lDNeg (x:xs, ys) = case x of 
                        N a -> case a of
                                    N b -> [(b:xs, ys)]
                                    _ -> [(x:xs, ys)]
                        _ -> lDNeg (xs ++ [x], ys)

rDNeg :: Sequent -> HyperSequent 
rDNeg (xs, y:ys) = case y of 
                        N a -> case a of
                                    N b -> [(xs, b:ys)]
                                    _ -> [(xs, y:ys)]
                        _ -> rDNeg (xs, ys ++ [y])

-- sorting list ([alpha, beta], [beta, alpha])
sort' :: Sequent -> Sequent
sort' (x, y) = (z ++ v, v' ++ z')
            where
                z = filter alphaForm x
                v = filter betaForm x
                z' = filter alphaForm y
                v' = filter betaForm y

-- another way of doing so
sort'' :: Sequent -> Sequent                
sort'' x = (lAlphaSeq x ++ lBetaSeq x, rBetaSeq x ++ rAlphaSeq x)

-- insert formula on the left side
insertL :: Form -> Sequent -> Sequent
insertL a (x, y)
                | alphaForm a = (a:x, y)
                | betaForm a = (x ++ [a], y)

-- insert formula, right side
insertR :: Form -> Sequent -> Sequent
insertR a (x, y)
                | alphaForm a = (x, a:y)
                | betaForm a = (x, y ++ [a])

-- list of alpha formula's ingredients
alphaIng :: Form -> [Form]   --[Form] (?)
alphaIng x = case x of
                C z y -> [z, y]
                N v -> case v of 
                            D z y -> [N z, N y]
                            I z y -> [z, N y]
                            N z -> [z]
                            
-- same but for beta
betaIng :: Form -> [Form]
betaIng x = case x of
                I a b -> [N a, b]
                D a b -> [a, b]
                N v -> case v of
                            C a b -> [N a, N b]

-- this one will check first formula and insert it
rule :: Sequent -> [Sequent]
rule (x:xs, y:ys)
            | alphaForm x = case (alphaIng x) of
                                [z, v] -> [(x:xs, y:ys), insertL z (insertL v (xs, y:ys))]
                                [z] -> [(x:xs, y:ys), insertL z (xs, y:ys)]
            | betaForm y = case (betaIng y) of
                                [z, v] -> [(x:xs, y:ys), insertR z (insertL v (x:xs, ys))]
                                [z] -> [(x:xs, y:ys), insertR z (x:xs, ys)]


-- examples 
ex = sort' ([D (V 1) (V 2), C (V 4) (V 5), N (V 1)], [V 1, V 2, D (V 1) (V 2)])
test = rule ex


