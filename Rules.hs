module Rules where

import Sequents
import Formulas

--lAlpha :: Sequent -> HyperSequent  --left alpha rule
lAlpha (x:xs, ys) = alphaIng x

rAlpha :: Sequent -> (Form, Form)  --right alpha rule
rAlpha (xs, y:ys) = alphaIng y

lBeta :: Sequent -> (Form, Form) -- left beta rule
lBeta (x:xs, ys) = betaIng x

rBeta :: Sequent -> (Form, Form) --right beta rule
rBeta (xs, y:ys) = betaIng y

lDNeg :: Sequent -> HyperSequent --left double negation rule
lDNeg (x:xs, ys) = case x of 
                        N a -> case a of
                                    N b -> [(b:xs, ys)]
                                    _ -> [(x:xs, ys)]
                        _ -> lDNeg (xs ++ [x], ys)

rDNeg :: Sequent -> HyperSequent --right double negation rule
rDNeg (xs, y:ys) = case y of 
                        N a -> case a of
                                    N b -> [(xs, b:ys)]
                                    _ -> [(xs, y:ys)]
                        _ -> rDNeg (xs, ys ++ [y])

sort' :: Sequent -> Sequent                        
sort' (x:xs, y:ys) = (z ++ [x] ++ v, v' ++ [y] ++ z')
            where
                z = filter alphaForm xs
                v = filter betaForm xs
                z' = filter alphaForm ys
                v' = filter betaForm ys

sort'' :: Sequent -> Sequent                
sort'' x = (lAlphaSeq x ++ lBetaSeq x, rBetaSeq x ++ rAlphaSeq x)

insert :: Form -> Sequent -> [Sequent]  --tylko sekwent i jedna formuła (plus podwójna negacja)
insert a (x, y)
                | alphaForm a = [(a:x, y)]
                | betaForm a = [(z ++ [a] ++ v, y)]
                    where
                        z = lAlphaSeq (x, y)
                        v = lBetaSeq (x, y) 

alphaIng :: Form -> (Form, Form)   --[Form] (?)
alphaIng x = case x of
                C z y -> (z, y)
                N v -> case v of 
                            D z y -> (N z, N y)
                            I z y -> (z, N y)

betaIng :: Form -> (Form, Form)
betaIng x = case x of
                I a b -> (N a, b)
                D a b -> (a, b)
                N v -> case v of
                            C a b -> (N a, N b)



                            
{-

 sort([Alpha1, Alpha2, ... Beta] [Beta1, Beta2, ... Alpha])
 alpha ingredients
 take first formula and put its products/ingredients in correct place (sorted), depending on it being alpha or beta
 and again

 alpha/beta ingredients (table) :: Formula -> [Formula]
 

mRule (xs, ys)   
            | alphaSeq (xs, ys) = (lAlpha (xs, ys)) <*> (rAlpha (xs, ys))
            -}


