import Data.List
import Data.Maybe
import Data.Function

get = genericIndex




data LambdaElement = Abstraction LambdaElement | Application LambdaElement LambdaElement | Variable Integer

--shows variable names in a deBruijn indexing system
show_L_with_var_names :: LambdaElement -> Integer -> [String]  -> String
show_L_with_var_names (Variable v) depth symbols = if v<=depth then symbols `get` (depth - v)
                                                               else (concat ["<", show v, ">"])

show_L_with_var_names (Abstraction body) depth symbols = (abstraction_symbol++(symbols `get` (depth+1))++separation_symbol++body_as_string)
                                                            where body_as_string = show_L_with_var_names body (depth+1) symbols
                                                                  abstraction_symbol = "λ"
                                                                  separation_symbol = "."

show_L_with_var_names (Application la lb) depth symbols = la_as_string++" "++lb_as_string
                                                            where requires_parens (Variable _) = False
                                                                  requires_parens _ = True
                                                                  in_parens_if_necessary l = let as_string = show_L_with_var_names l depth symbols
                                                                                             in  if requires_parens l then "("++as_string++")"
                                                                                                                      else  as_string
                                                                  [la_as_string, lb_as_string] = map in_parens_if_necessary [la, lb]

--the variable names that will be used: first it's just the alphabet, and then it adds pedices
alphabet = map (\c->[c]) ['a'..'z']
subscript_numbers = ["₀","₁","₂","₃","₄","₅","₆","₇","₈","₉"];
getDigits 0 = []
getDigits n = (getDigits $ div n 10)++[mod n 10]


--shows a pretty lambda expression
instance Show LambdaElement where
    show l =  show_L_with_var_names l (-1) symbols
                where alphabet_with_symbol s = map (++s) alphabet
                      showNumberAsSubscript n = concatMap (subscript_numbers!!) $ getDigits n
                      all_subscripts = map showNumberAsSubscript [0..]
                      symbols = concatMap alphabet_with_symbol all_subscripts

--from now on, a dictionary is an association list between expressions and names, this is to show expressions using their common names when possible


showCombinators :: [(String, LambdaElement)] -> LambdaElement -> String
showCombinators dict l = let lookUpDict l' = find (\(v, vl)->alphaEquivalent vl l') dict
                             requires_parens l' = case lookUpDict l' of Just _   -> False
                                                                        otherwise -> True
                             showWithParensIfNecessary l' = let as_string = showCombinators dict l' in if requires_parens l' then "("++as_string++")" else as_string
                         in  case lookUpDict l of Just (c, _) -> c
                                                  Nothing     -> case l of Application la lb -> (showWithParensIfNecessary la)++" "++(showWithParensIfNecessary lb)
                                                                           _                 -> show l



--checks for alpha equivalence
alphaEquivalent :: LambdaElement -> LambdaElement -> Bool
alphaEquivalent (Variable n) (Variable m) = n==m
alphaEquivalent (Abstraction b) (Abstraction p) = alphaEquivalent b p
alphaEquivalent (Application p q) (Application l m) = (alphaEquivalent p l) && (alphaEquivalent q m)
alphaEquivalent _ _ = False


instance Eq LambdaElement where
    (==) = alphaEquivalent
    


lambdaFmap f (Variable v) = (Variable v)
lambdaFmap f (Abstraction body) = Abstraction (f body)
lambdaFmap f (Application la lb) = Application (f la) (f lb)


modifyFreeVariables :: (Integer -> Integer) -> LambdaElement -> LambdaElement
modifyFreeVariables func l = modifyFreeVariables' (-1) l
                                where modifyFreeVariables' depth (Variable v) = if v > depth then (Variable (func v)) else (Variable v)
                                      modifyFreeVariables' depth ab@(Abstraction body) = lambdaFmap (modifyFreeVariables' (depth+1)) ab
                                      modifyFreeVariables' depth app@(Application _ _) = lambdaFmap (modifyFreeVariables' depth) app

--to chance context in the deBruijn indexing system
raiseFreeVariables :: LambdaElement -> LambdaElement
raiseFreeVariables l = modifyFreeVariables (\x-> x-1) l


sinkFreeVariables :: Integer -> LambdaElement -> LambdaElement
sinkFreeVariables s l = modifyFreeVariables (+s) l


betaReduce :: LambdaElement -> LambdaElement  -- Not sure this is correct, but it does work with ski calculus stress tests
betaReduce (Application (Abstraction la) lb) = raisedAbstraction  --not recursive because of the Y combinator
                                                where replaceBoundVariable nL depth (Variable v) = if v == depth then sinkFreeVariables depth nL else (Variable v)
                                                      replaceBoundVariable nL depth ab@(Abstraction _) = lambdaFmap (replaceBoundVariable nL (depth+1)) ab
                                                      replaceBoundVariable nL depth app@(Application _ _) = lambdaFmap (replaceBoundVariable nL depth) app
                                                      laReplaced = replaceBoundVariable lb 0 la
                                                      raisedAbstraction = (\(Abstraction body)-> body) $ raiseFreeVariables (Abstraction laReplaced)
betaReduce l = lambdaFmap betaReduce l 


betaReduceRepeat :: LambdaElement -> LambdaElement
betaReduceRepeat a = tryReducing iterations a
                        where iterations = 6
                              tryReducing 0 l = l
                              tryReducing n l = let reduced = betaReduce l
                                                in  if alphaEquivalent l reduced then l else tryReducing (n-1) reduced



etaReduce :: LambdaElement -> LambdaElement
etaReduce (Abstraction (Application l (Variable 0))) = raiseFreeVariables l
etaReduce l = lambdaFmap etaReduce l


cI = Abstraction (Variable 0)
cK = Abstraction (Abstraction (Variable 1))
cT = cK
cF = Abstraction (Abstraction (Variable 0))
cS = Abstraction (Abstraction (Abstraction (Application (Application (Variable 2) (Variable 0)) (Application (Variable 1) (Variable 0)))))
cM = Abstraction (Application (Variable 0) (Variable 0))
cB = Abstraction (Abstraction (Application (Variable 1) (Variable 0)))
cY = Abstraction (Application (Abstraction (Application (Variable 1) (Application (Variable 0) (Variable 0)))) (Abstraction (Application (Variable 1) (Application (Variable 0) (Variable 0)))))
cX = Abstraction (Application (Application (Variable 0) cS) cK)
cC = Abstraction (Abstraction (Abstraction (Application (Application (Variable 2) (Variable 0)) (Variable 1))))
cG = Abstraction (Abstraction (Application (Variable 0) (Variable 1)))



lambdaApply :: LambdaElement -> LambdaElement -> LambdaElement
lambdaApply a b = betaReduce $ Application a b



getTopLevelElems :: String -> [String]
getTopLevelElems s = foldl appendToLastIfOpen [] s
                        where isOpen :: String -> Bool
                              isOpen s' = let countElem e l = length $ filter (==e) l
                                              openParenCount = countElem '(' s'
                                              closeParenCount = countElem ')' s'
                                          in  openParenCount > closeParenCount
                              isParen c = elem c "()"
                              appendToLastIfOpen :: [String] -> Char -> [String]
                              appendToLastIfOpen [] x = [[x]] 
                              appendToLastIfOpen a  x = let lastAccList = last a
                                                            alreadyClosedStrings = init a
                                                        in  if (isOpen lastAccList)
                                                                then alreadyClosedStrings++[lastAccList++[x]]
                                                                else alreadyClosedStrings++[lastAccList]++[[x]]


                         
parseAsTree :: [(String, LambdaElement)] -> String -> LambdaElement
parseAsTree dict s = let isSingleChar s' = (length s)==1
                         lookUpDict c = find (\(v, l)->c==v) dict
                         toCombinator s' = if isSingleChar s' 
                                            then case lookUpDict s' of Just  (v, l) -> l
                                                                       Nothing      -> cK
                                            else parseAsTree dict s'
                         removeOuterParens ('(':[]) = ""
                         removeOuterParens ('(':xs) = init xs
                         removeOuterParens x        = x
                         elementsInTopLevel = map (toCombinator . removeOuterParens) $ getTopLevelElems s
                         apply la lb = Application la lb
                    in   case elementsInTopLevel of []        -> cI
                                                    (x:[])    -> x
                                                    otherwise -> foldl1 apply elementsInTopLevel


parseCombinatorString s = parseAsTree allCombinators 


--choiceCombinators:
iterateNTimes :: Integer -> (a->a) -> a -> a
iterateNTimes n func first = (`get` n) $ iterate func first

makeChooserCombinator :: Integer -> Integer -> LambdaElement
makeChooserCombinator from choice = iterateNTimes from (Abstraction) (Variable choice)

makeHolderCombinator :: Integer -> Integer -> LambdaElement
makeHolderCombinator from choice = Abstraction $ iterateNTimes from (Abstraction) $ foldl (Application) (Variable 0) $ map (Variable) $ reverse [(from - choice+1)..(from)]


allCombinators = [ ("I", cI),
                   ("K", cK),
                   ("S", cS),
                   ("F", cF),
                   ("B", cB),
                   ("C", cC),
                   ("B", cB),
                   ("Y", cY),
                   ("M", cM),
                   ("X", cX)]

showWithCommonCombinators = showCombinators allCombinators




allExpressionsOfLength :: Integer -> [LambdaElement]
allExpressionsOfLength n = expressionsWithFreeVariables (-1) n
                                where expressionsWithFreeVariables freeV 0 = map (Variable) [0..freeV]
                                      expressionsWithFreeVariables freeV depth = let deeper = depth-1
                                                                                     abstractions = map Abstraction $ expressionsWithFreeVariables (freeV+1) deeper
                                                                                     all_sums_of_depth = takeWhile ((>0) . snd) $ map (\x->(x, depth-x)) [1..]
                                                                                     all_applications_with_lengths (a, b) = let [pa, pb] = map (expressionsWithFreeVariables freeV) [a, b]
                                                                                                                            in  Application <$> pa <*> pb
                                                                                     applications = concatMap all_applications_with_lengths all_sums_of_depth
                                                                                     variables = map (Variable) [0..freeV]
                                                                                 in  abstractions++applications++variables

allDifferentCombinatorsOfLength n = nubBy alphaEquivalent $ map betaReduceRepeat $ allExpressionsOfLength n

makeAllCombinationsOfDict :: [LambdaElement] ->Integer ->  [LambdaElement]
makeAllCombinationsOfDict dict 0 = []
makeAllCombinationsOfDict dict 1 = dict
makeAllCombinationsOfDict dict n = nubBy alphaEquivalent allReducedCombinations
                                    where rec = makeAllCombinationsOfDict dict 
                                          allPartitionsOfN = map (\x->(x, n-x)) [1..(n-1)]
                                          allUnreducedApplications = concatMap (\(a, b)->Application <$> (rec a) <*> (rec b)) allPartitionsOfN
                                          allReducedCombinations = map (etaReduce . betaReduceRepeat) allUnreducedApplications






boringSet n = choosers++holders
                where allPairs = concatMap (\x->zip (repeat x) [0..(x-1)]) [1..n]
                      choosers = map (uncurry  makeChooserCombinator) allPairs
                      holders  = map (uncurry makeHolderCombinator) allPairs
                      
                      

--this is the main functionality of this program, to generate all the lambda expressions 
--n is the maximum depth of the tree representing the lambda expression
showZoo n = mapM_ (putStrLn . showWithCommonCombinators . betaReduceRepeat) $ allDifferentCombinatorsOfLength n




































