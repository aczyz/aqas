module Rules where

import Sequents
import Formulas

alphaIng :: Form -> [Form]
alphaIng x = case x of
                C z y -> [z, y]
                N v   -> case v of 
                            D z y -> [N z, N y]
                            I z y -> [z, N y]
                            N z   -> [z]

betaIng :: Form -> [Form]
betaIng x = case x of
                I a b -> [N a, b]
                D a b -> [a, b]
                N v   -> case v of
                            C a b -> [N a, N b]

lLiteral :: Sequent -> [Form]
lLiteral (x, _) = filter isLiteral x

rLiteral :: Sequent -> [Form]
rLiteral (_, y) = filter isLiteral y


seqAnalyzer :: Sequent -> HyperSequent
seqAnalyzer ([], [])   = []

seqAnalyzer (x:xs, [])   = case (lAlphaSeq (x:xs, []), rBetaSeq (x:xs, []), lBetaSeq (x:xs, []), 
                                rAlphaSeq (x:xs, []), lLiteral (x:xs, []), rLiteral (x:xs, [])) of
                            (p:_, _, _, _, _, _)     -> [(alphaIng p ++ xs, [])]
                            ([], [], r:_, _, _, _)   -> [(head (betaIng r) : xs, []), (tail (betaIng r), [])]
                            ([], [], [], [], ts, us) -> [(ts, us)]

seqAnalyzer ([], y:ys)   = case (lAlphaSeq ([], y:ys), rBetaSeq ([], y:ys), lBetaSeq ([], y:ys), 
                                rAlphaSeq ([], y:ys), lLiteral ([], y:ys), rLiteral ([], y:ys)) of
                            ([], q:_, _, _, _, _)    -> [([], betaIng q ++ ys)]
                            ([], [], [], s:_, _, _)  -> [([], head (alphaIng s) : ys), ([], tail (alphaIng s) ++ ys)]
                            ([], [], [], [], ts, us) -> [(ts, us)]

seqAnalyzer (x:xs, y:ys) = case (lAlphaSeq (x:xs, y:ys), rBetaSeq (x:xs, y:ys), lBetaSeq (x:xs, y:ys), 
                                rAlphaSeq (x:xs, y:ys), lLiteral (x:xs, y:ys), rLiteral (x:xs, y:ys)) of
                            (p:_, _, _, _, _, _)     -> [(alphaIng p ++ xs, y:ys)]
                            ([], q:_, _, _, _, _)    -> [(x:xs, betaIng q ++ ys)]
                            ([], [], r:_, _, _, _)   -> [(head (betaIng r) : xs, y:ys), (tail (betaIng r), y:ys)]
                            ([], [], [], s:_, _, _)  -> [(x:xs, head (alphaIng s) : ys), (x:xs, tail (alphaIng s) ++ ys)]
                            ([], [], [], [], ts, us) -> [(ts, us)]


seqCreator :: HyperSequent -> HyperSequent
seqCreator []     = []
seqCreator (x:xs) = seqAnalyzer x ++ seqCreator xs
-- dodać iterację, żeby rozkładały się wszystkie formuły
