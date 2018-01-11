module Sequents where

import Formulas

type Sequent = ([Form], [Form])
type HyperSequent = [Sequent]

lBetaSeq :: Sequent -> [Form]                         --creates list with betas (left side)
lBetaSeq ([], _) = []
lBetaSeq (x:xs, ys)
                    | betaForm x = x : lBetaSeq (xs, ys)
                    | otherwise  = lBetaSeq (xs, ys)

lAlphaSeq :: Sequent -> [Form]                        --creates list with alphas (left side)
lAlphaSeq ([], _) = []
lAlphaSeq (x:xs, ys)
                    | alphaForm x = x : lAlphaSeq (xs, ys)
                    | otherwise   = lAlphaSeq (xs, ys)

rBetaSeq :: Sequent -> [Form]                         --creates list with betas (right side)
rBetaSeq (_, []) = []
rBetaSeq (xs, y:ys)
                    | betaForm y = y : rBetaSeq (xs, ys)
                    | otherwise  = rBetaSeq (xs, ys)

rAlphaSeq :: Sequent -> [Form]                        --creates list with alphas (right side)
rAlphaSeq (_, []) = []
rAlphaSeq (xs, y:ys)
                    | alphaForm y = y : rAlphaSeq (xs, ys)
                    | otherwise   = rAlphaSeq (xs, ys)

isAtomic :: Sequent -> Bool                         --if sequent is atomic
isAtomic (x, y) = all isLiteral x && all isLiteral y

isMinimal :: HyperSequent -> Bool                   --if Hypersequent is minimal
isMinimal xs = all isAtomic xs 

isClosed :: Sequent -> Bool                         --if Sequent is closed
isClosed ([], [])     = False
isClosed ([], y:ys)   = case y of
                          N a -> if elem a (y:ys) then True else isClosed ([], ys)
                          _   -> if elem (N y) ys then True else isClosed ([], ys)
isClosed (x:xs, ys)   = case x of
                          N b -> if elem b xs || elem (N b) ys then True else isClosed (xs, ys)
                          _   -> if elem x ys || elem (N x) xs then True else isClosed (xs, ys)


                         
abdProblem :: HyperSequent -> Bool                  --if Hypersequent is an abductive problem
abdProblem [] = False
abdProblem xs = all isClosed xs 

atomAbdProblem :: HyperSequent -> Bool              --if Hypersequent is an atomic abductive problem
atomAbdProblem xs = if abdProblem xs && isMinimal xs then True else False




{-
isOpen :: Sequent -> Bool - potrzebne?

alpha/beta/dNeg Seq - Bool czy info która formuła?
-}
