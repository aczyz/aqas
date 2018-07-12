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


------------------------------------------------------------------
-- restriction rules and other functions

-- creating list of hintikka sets which do not
-- consist of negation of a given formula
-- (for 1st abd rule)
{-r1_abd :: [[Form]] -> Form -> [[Form]
r1_abd [] y  = []
r1_abd (x:xs) y | elem y x     = r1_abd xs ys
                | otherwise    = y : r1_abd xs y 

--foldr :: (a -> b -> b)  -> b -> [a] -> b
{-
 -
 - ([Form], [[Form]]) -> ([Form], [[Form]])
r1_abd ([], xs]    = ([], xs)
r1_abd [(y:ys),(x:xs)]  | elem y x   = r1_abd y xs
                        | otherwise  = ...

f0 :: Form -> [HSet] -> [HSet]
f0 y []  = []
f0 y (x:xs)  | elem y x = f0 y xs
             | otherwise    = x : f0 y xs 


f1 :: Form -> ([Form], [HSet]) -> ([Form], [Hset])
f1 y ([], (x:xs)] | y `elem` x = if
                  |  

f2 :: [Seq] -> [Form]
f2 [] = []
f2 x:xs = ant1 x ++ f2 xs
 
 -}

-- creating list with hintikka sets which 
-- do not consist of a given formula
-- (for 2nd abd rule, antecedent of implication)
r2_abd :: [[Form]] -> Form -> [[Form]]
r2_abd [] y = []
r2_abd (x:xs) y | elem y x  = r2_abd xs y
                | otherwise = x : r2_abd xs y


-- creating list of hintikka sets which 
-- more general, checking every formula 
-- from the derivation 
apply_r1 :: [Form] -> [[Form]] -> [[Form]]
apply_r1 [] zs     = []
apply_r1 (x:xs) zs = r1_abd zs x ++ apply_r1 xs zs 

--ap_r1 :: (a -> b -> b) -> [a] -> b -> b
--ap_r1 f x y = foldr (\z s acc -> (++) (f z s)  acc) []

-- same as above, but checking 2nd abd rule
-- on list with literals from derivation
apply_r2 :: [Form] -> [[Form]] -> [[Form]]
apply_r2 [] zs     = []
apply_r2 (x:xs) zs = r2_abd zs x ++ apply_r2 xs zs  

-- using the above function, checking the whole
-- hypersequent (succedent of it)
-- and creating list with hintikka sets 
-- which do not consists of a negation of a given formula
f3' :: HyperSequent -> [[Form]] -> [[Form]]
f3' [] zs     = []
f3' (x:xs) zs = apply_r1 (sc1 x) zs ++ f3' xs zs 


-- similar but with 2nd abd rule
f4' :: HyperSequent -> [[Form]] -> [[Form]]
f4' [] zs     = []
f4' (x:xs) zs = apply_r2 (ant1 x) zs ++ f4' xs zs

-- succedent of a sequent
sc1 :: Sequent -> [Form]
sc1 (x, y) = x

-- antecedent of a sequent
ant1 :: Sequent -> [Form]
ant1 (x, y) =  y


-- adding literals to separate list
f5' :: [Form] -> [Form] -> [Form]
f5' [] ys     = []
f5' (x:xs) ys = if elem (N x) ys then f5' xs ys else x: f5' xs ys

f51 ::[Form] -> [[Form]] -> [Form]
f51 xs [] = []
f51 xs (y:ys) = f5' xs y ++ f51 xs ys
-}
{-
adding literals not appearing in the hintikka set to separate list
f6 :: HyperSequent -> [[Form]] -> ([[Form]], [Form])
f6 (x:xs) zs = (f3 ( ...
-}

{-
f0 ::  Form -> [[Form]] -> [[Form]]   --zbiór hintikka setów,  w których formuła nie występuje 


f1 ::  Form -> ([Form], [[Form]]) -> ([Form], [[Form]])


f2 : [[Form]] -> ([Form], [[Form]]) -- [A1, A2, T, ..., An ...] T = te, których nie można zamknąć 
--generalizacja dla hipersewkentu


--jesli f2 zwraca (_, []) to 
-- decyzja czy przechodzimy do drugiego literału
f3 :: [Sequent] -> [Form] 

-}

--jeżeli literał znajduje sie w secie to zwraca True
--w przeciwnym wypadku False
fspr :: Form -> [Form] -> Bool 
fspr  y xs | elem y xs  = True
           | otherwise = False

f0 :: Form -> [[Form]] -> [[Form]]
f0 x [] = []
f0 x (y:ys) | fspr x y  = f0 x ys
            | otherwise = (y : f0 x ys)

-- dodaje do pierwszego elementu pary negacje sprawdzanego literału 
f1 :: Form -> ([Form], [[Form]]) -> ([Form], [[Form]])
f1 x (zs, (y:ys)) | fspr x y  = f1 x ([], ys)
                  | otherwise = (((N x) : zs), [y])

--f2 :: [[Form]] -> ([Form], [[Form]])


-- succedent of a sequent
sc1 :: Sequent -> [Form]
sc1 (x, y) = y

-- antecedent of a sequent
ant1 :: Sequent -> [Form]
ant1 (x, y) =  x

-- zwraca listę poprzedników hipersekwentu
f28 :: HyperSequent -> [[Form]]
f28 xs = map ant1 xs


test88 = f28 (head test2)
test9  = [([C (I (N (V 1)) (D (V 2) (V 1))) (D (V 1) (V 2))], [D (V 1) (N (V 1)), I (V 10) (V 2), C (V 5) (V 6), C (V 5) (V 7), C (V 5) (V 22), C (V 5) (V 44)]), ([C (I (N (V 1)) (D (V 2) (V 1))) (D (V 1) (V 2))], [D (V 1) (N (V 1)), I (V 10) (V 2), C (V 5) (V 6), C (V 5) (V 7), C (V 5) (V 22), C (V 5) (V 44)])]


-- to be continued
