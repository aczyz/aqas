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


type TupleSeq = ([Form], [Form], [Form], [Form], [Form], [Form])


-- makes tuple with sorted formulas from sequent
sort :: Sequent -> TupleSeq 
sort x =  (lAlphaSeq x, rBetaSeq x, lBetaSeq x, rAlphaSeq x, lLiteral x, rLiteral x)


sAnalizer :: TupleSeq -> HyperSequent
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
sCreator (x:xs) | isClosed x = sCreator xs
                | otherwise = sAnalizer (sort x) ++ (sCreator xs)


-- all steps in one list
drv :: [HyperSequent] -> [HyperSequent]
drv (x:xs) | isMinimal x = (x:xs)
           | otherwise = drv ((sCreator x) : (x:xs))


test2 = drv [[([I (V 1) (I (V 2) (V 3)), C (V 2) (V 4)], [I (V 2) (V 3)])]]
test6 = drv [[([C (I (N (V 1)) (D (V 2) (V 1))) (D (V 1) (V 2))], [D (V 1) (N (V 1)), I (V 10) (V 2), C (V 5) (V 6), C (V 5) (V 7), C (V 5) (V 22), C (V 5) (V 44)])]]
test8 = drv [[([C (D (V 11) (V 22)) (V 66)], [V 77])]]



type HintikkaSet = (([Form], [Form]), ([Form], [Form]), [Form])

-- no alphas that haven't had any rule applied to them yet
no_alphas :: HintikkaSet -> Bool
no_alphas (x, y, z) = case x of
                ([], r) -> True
                _ -> False

-- same as above
no_betas :: HintikkaSet -> Bool
no_betas (x, y, z) = case y of
                ([], r) -> True
                _ -> False

-- inserting formulas into adequate part of hintikka set
insert_form :: Form -> HintikkaSet -> HintikkaSet
insert_form a ((x, y), (z, r), b) 
                | alphaForm a = ((a:x, y), (z, r), b)
                | betaForm a = ((x, y), (a:z, r), b)
                | isLiteral a = ((x, y), (z, r), a:b)

-- creating list with single hintikka set 
alpha_rule :: HintikkaSet -> [HintikkaSet]
alpha_rule ((x:xs, y), z, r) = case alphaIng x of
                                    [a] -> [insert_form a ((xs, x:y), z, r)]
                                    [a, b] -> [insert_form b (insert_form a ((xs, x:y), z, r))] 
                                             
-- creating list consisting of three hintikka sets
beta_rule :: HintikkaSet -> [HintikkaSet]
beta_rule (x, (z:zs, y), r) = case betaIng z of
                                  [a, b] -> [insert_form a (x, (zs, z:y), r), 
                                             insert_form b (x, (zs, z:y), r),
                                             insert_form a (insert_form b (x, (zs, z:y), r))]   


-- creating list consisting of three hintikka sets 
alpha_rule1 :: HintikkaSet -> [HintikkaSet]
alpha_rule1 ((x:xs, y), z, r) = case alphaIng x of
                                     [a, b] -> [insert_form a ((xs, x:y), z, r),  
                                             insert_form b ((xs, x:y), z, r),
                                             insert_form a (insert_form b ((xs, x:y),z, r))]  

                                    
                                             
-- creating list consisting a single hintikka set
beta_rule1 :: HintikkaSet -> [HintikkaSet]
beta_rule1 (x, (z:zs, y), r) = case betaIng z of
                                    [a] -> [insert_form a (x, (zs, z:y), r)]
                                    [a, b] -> [insert_form b (insert_form a (x, (zs, z:y), r))] 
                                 
-- creates list of all hintikka sets
hintikka_set :: [HintikkaSet] -> [HintikkaSet]
hintikka_set [] = []
hintikka_set (x:xs) 
            | no_alphas x && no_betas x = x : hintikka_set xs
            | not (no_alphas x) =  hintikka_set (alpha_rule x ++ xs)
            | not (no_betas x) = hintikka_set (xs ++ beta_rule x)   

-- same as above, dual hintikka sets
dhintikka_set :: [HintikkaSet] -> [HintikkaSet]
dhintikka_set [] = []
dhintikka_set (x:xs) 
            | no_alphas x && no_betas x = x : dhintikka_set xs
            | not (no_alphas x) = dhintikka_set (beta_rule1 x ++ xs)
            | not (no_betas x) = dhintikka_set (xs ++ alpha_rule1 x)  


test_set = hintikka_set [(([C (V 4) (V 5)], []), ([I (V 1) (I (V 2) (V 3))], []), [])]

-- joining certain parts of hintikkaset type to create more 'user-friendly' structure
jn :: HintikkaSet -> [Form]
jn ((_, x), (_, y), z) = x ++ y ++ z

-- mapping the above function over list of hintikka sets
hs_list :: [HintikkaSet] -> [[Form]]
hs_list x = map jn x

-- checking if hintikka set is inconsistent
incnst :: [Form] -> Bool
incnst (x:xs) = case x of
                N z -> if elem z xs then True else False
                z -> if elem (N z) xs then True else False

-- getting rid of inconsistent sets using function defined above
rmv :: [[Form]] -> [[Form]]
rmv [] = []
rmv (x:xs) = case incnst x of
                    True -> rmv xs
                    _ -> x : rmv xs

test0 = rmv (hs_list test_set)
