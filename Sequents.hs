module Sequents where

import Formulas


type Sequent = ([Form], [Form])
type HyperSequent = [Sequent]

--creates list with betas (left side)
lBetaSeq :: Sequent -> [Form]
lBetaSeq ([], _) = []
lBetaSeq (x:xs, ys)
                    | betaForm x = x: lBetaSeq (xs, ys)
                    | otherwise  = lBetaSeq (xs, ys)

--creates list with alphas (left side)
lAlphaSeq :: Sequent -> [Form]
lAlphaSeq ([], _) = []
lAlphaSeq (x:xs, ys)
                    | alphaForm x = x: lAlphaSeq (xs, ys)
                    | otherwise  = lAlphaSeq (xs, ys)

--creates list with betas (right side)
rBetaSeq :: Sequent -> [Form]
rBetaSeq (_, []) = []
rBetaSeq (xs, y:ys)
                  | betaForm y = y : rBetaSeq (xs, ys)
                  | otherwise  = rBetaSeq (xs, ys)

--creates list with alphas (right side)
rAlphaSeq :: Sequent -> [Form]
rAlphaSeq (_, []) = []
rAlphaSeq (xs, y:ys)
                    | alphaForm y = y : rAlphaSeq (xs, ys)
                    | otherwise  = rAlphaSeq (xs, ys)

--creates list with right side literals
rLiteral :: Sequent -> [Form]
rLiteral (_, []) = []
rLiteral (xs, y:ys)
                    | isLiteral y = y : rLiteral (xs, ys)
                    | otherwise   = rLiteral (xs, ys)

--creates list with left side literals
lLiteral :: Sequent -> [Form]
lLiteral ([], _) = []
lLiteral (x:xs, ys)
                    | isLiteral x = x : lLiteral (xs, ys)
                    | otherwise   = lLiteral (xs, ys)


--if sequent is atomic
isAtomic :: Sequent -> Bool
isAtomic (x, y) = all isLiteral x && all isLiteral y

--if Hypersequent is minimal
isMinimal :: HyperSequent -> Bool
isMinimal xs= all isAtomic xs

--if Sequent is closed
isClosed :: Sequent -> Bool
isClosed ([], [])     = False
isClosed ([], y:ys)   = case y of
                          N a -> if elem a (y:ys) then True else isClosed ([], ys)
                          _   -> if elem (N y) ys then True else isClosed ([], ys)
isClosed (x:xs, ys) = case x of
                          N b -> if elem b xs || elem (N b) ys then True else isClosed (xs, ys)
                          _   -> if elem x ys || elem (N x) xs then True else isClosed (xs, ys)


--if Hypersequent is an abductive problem
abdProblem :: HyperSequent -> Bool
abdProblem []     = False
abdProblem xs = any isClosed xs

--if Hypersequent is an atomic abductive problem
atomAbdProblem :: HyperSequent -> Bool
atomAbdProblem xs = if abdProblem xs && isMinimal xs then True else False
