module Rules where

import Sequents
import Formulas

-- list with left alpha formulas only
lAlpha :: Sequent ->[Form]
lAlpha (x, y) = filter alphaForm x

-- list with right alpha formulas only
rAlpha :: Sequent -> [Form]
rAlpha (x, y) = filter alphaForm y

-- list with left beta formulas only
lBeta :: Sequent -> [Form]
lBeta (x, y) = filter betaForm x

-- list with right beta formulas only
rBeta :: Sequent -> [Form]
rBeta (x, y) = filter betaForm y

-- list with left literals only
l_lit :: Sequent -> [Form]
l_lit (x, y) = filter isLiteral x

-- list with right literals only
r_lit :: Sequent -> [Form]
r_lit (x, y) = filter isLiteral y


-- list of alpha formula's components
-- added variables, the reason is stated below 
alphaIng :: Form -> [Form]
alphaIng x = case x of
                V _ -> [x]
                C z y -> [z, y]
                N v -> case v of
                            V _ -> [x]
                            D z y -> [N z, N y]
                            I z y -> [z, N y]
                            N z -> [z]

-- same but for beta
-- added variables as there were some problems when trying out one of the examples below (test2)
betaIng :: Form -> [Form]
betaIng x = case x of
                V _ -> [x]
                I a b -> [N a, b]
                D a b -> [a, b]
                N v -> case v of
                            V _ -> [x]
                            C a b -> [N a, N b]


-- sorting list into ([alpha, beta] [beta, alpha])
sort' :: Sequent -> Sequent
sort' (x, y) = (z ++ v, v' ++ z')
            where
                z = filter alphaForm x
                v = filter betaForm x
                z' = filter alphaForm y
                v' = filter betaForm y

-- another way of doing so
sort'' :: Sequent -> Sequent
sort'' x = (lAlpha x ++ lBeta x, rBeta x ++ rAlpha x)

-- changing sequent type into tuple
seq_analys :: Sequent -> ([Form], [Form], [Form], [Form], [Form], [Form])
seq_analys x = (lAlpha x, lBeta x, l_lit x, rBeta x, rAlpha x, r_lit x)

-- example to show that it works
test1 = seq_analys ([C (V 1) (V 2), V 4, V 6, D (V 3) (V 4)], [C (V 1) (V 3), V 4, V 8])

-- insert formula in the antecedent of a sequent
insert_ant :: Form -> ([Form], [Form], [Form], [Form], [Form], [Form]) -> ([Form], [Form], [Form], [Form], [Form], [Form])
insert_ant y (x, a, b, c, d, e)
                | alphaForm y = (y:x, a, b, c, d, e)
                | betaForm y = (x, y:a, b, c, d, e)
                | isLiteral y = (x, a, y:b, c, d, e)
                
-- insert formula in a succedent of a sequent
insert_succ :: Form -> ([Form], [Form], [Form], [Form], [Form], [Form]) -> ([Form], [Form], [Form], [Form], [Form], [Form])
insert_succ y (x, a, b, c, d, e)
                | betaForm y = (x, a, b, y:c, d, e)
                | alphaForm y = (x, a, b, c, y:d, e)
                | isLiteral y = (x, a, b, c, d, y:e)

-- inserting components of given formula (unctions below will vary in regards to formula's type and its side)
-- in the correct place, making that into a list (as in the case of alpha formula on the right side and beta
-- on the left we'll get two sequents), to make it easier to get those back into sequent form
l_ins_alpha :: ([Form], [Form], [Form], [Form], [Form], [Form]) -> [([Form], [Form], [Form], [Form], [Form], [Form])]
l_ins_alpha (x:xs, a, b, c, d, e)
                        | alphaForm x = case (alphaIng x) of
                                                           [z, v] -> [insert_ant z (insert_ant v (xs, a, b, c, d, e))]
                                                           [z] -> [insert_ant z (xs, a, b, c, d, e)]

r_ins_alpha :: ([Form], [Form], [Form], [Form], [Form], [Form]) -> [([Form], [Form], [Form], [Form], [Form], [Form])]
r_ins_alpha (x, a, b, c, d:ds, e)
                        | alphaForm d  = case (alphaIng d) of
                                                           [z, v] -> [insert_succ z (x, a, b, c, ds, e), insert_succ v (x, a, b, c, ds, e)]
                                                           [z] -> [insert_succ z (x, a, b, c, ds, e)]
                        | isLiteral d = [(x, a, b, c, ds, d:e)] -- added to check something

l_ins_beta :: ([Form], [Form], [Form], [Form], [Form], [Form]) -> [([Form], [Form], [Form], [Form], [Form], [Form])]
l_ins_beta (x, a:as, b, c, d, e)
                        | betaForm a = case (betaIng a) of
                                                           [z, v] -> [insert_ant z (x, as, b, c, d, e), insert_ant v (x, as, b, c, d, e)]
                                                           [z] -> [insert_ant z (x, as, b, c, d, e)]
                        | isLiteral a = [(x, as, a:b, c, d, e)] --same, tbh it won't be needed in future


r_ins_beta :: ([Form], [Form], [Form], [Form], [Form], [Form]) -> [([Form], [Form], [Form], [Form], [Form], [Form])]
r_ins_beta (x, a, b, c:cs, d, e)
                        | betaForm c = case (betaIng c) of
                                                           [z, v] -> [insert_succ z (insert_succ v (x, a, b, cs, d, e))]
                                                           [z] -> [insert_succ z (x, a, b, cs, d, e)]


-- applying proper rules to non-empty sets
apply_rule :: ([Form], [Form], [Form], [Form], [Form], [Form]) -> [([Form], [Form], [Form], [Form], [Form], [Form])]
apply_rule (z, c, v, a, b, d)
              | not (null z) = l_ins_alpha (z, c, v, a, b, d)
              | not (null c) = l_ins_beta (z, c, v, a, b, d)
              | not (null a) = r_ins_beta (z, c, v, a, b, d)
              | not (null b) = r_ins_alpha (z, c, v, a, b, d)


-- getting back into sequent form
seq_creator :: ([Form], [Form], [Form], [Form], [Form], [Form]) -> Sequent
seq_creator (x, y, z, a, b, c) = (x ++ y ++ z, a ++ b ++ c)


hyper_creator :: HyperSequent -> HyperSequent
hyper_creator (x:xs) = case (apply_rule (seq_analys x)) of
                            [z, y] -> [seq_creator z] ++ [seq_creator y] ++ xs
                            [z] -> [seq_creator z] ++ xs


-- creates hseqs out of non atomic sequents
create_hseq :: HyperSequent -> HyperSequent
create_hseq [] = []
create_hseq (x:xs) = case isAtomic x of
                          True -> x : create_hseq xs
                          False -> hyper_creator (x:xs)

test3 = create_hseq [([I (V 1) (I (V 2) (V 3)), C (V 2) (V 4)], [I (V 2) (V 3)])]
test31 = seq_analys (head [([V 2,V 4,I (V 2) (V 3),I (V 1) (I (V 2) (V 3))],[])])


drv :: [HyperSequent] -> [HyperSequent]
drv (x:xs) = [until (isMinimal) create_hseq x] ++ (x:xs)


test2 = drv [[([I (V 1) (I (V 2) (V 3)), C (V 2) (V 4)], [I (V 2) (V 3)])]]  --success
test4 = drv [[([C (V 1) (V 2)], [V 3])]]  --success 
test6 = drv [[([C (I (N (V 1)) (D (V 2) (V 1))) (D (V 1) (V 2))], [D (V 1) (N (V 1)), I (V 10) (V 2), C (V 5) (V 6), C (V 5) (V 7), C (V 5) (V 22), C (V 5) (V 44)])]] --success
test7 = drv [[([D (C (V 1) (V 2)) (D (V 1) (D (V 3) (V 5)))], [V 6])]] --success
test8 = drv [[([C (D (V 11) (V 22)) (V 66)], [V 77])]] --success


-- returns head of list with hseqs, so the minimal hseq
lasthseq :: [HyperSequent] -> HyperSequent
lastsheq x = head x


abd_prob :: HyperSequent -> HyperSequent
abd_prob x = filter isOpen x

test9 = abd_prob (lasthseq test7)

