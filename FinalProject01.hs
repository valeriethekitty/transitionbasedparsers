module FinalProject01 where

import Control.Applicative(liftA, liftA2, liftA3)
import Data.List

import CFGParsing
import Distribution.Simple.Program.HcPkg (list)

bottomUp :: (Eq nt, Eq t) => CFG nt t -> [t] -> [[ParseStep nt t]]
bottomUp cfg input =
  let (nts, ts, start, rules) = cfg in
  let startingConfig = ([], input) in
  let goalConfig = ([NoBar start], []) in
  parser [shift, reduce] rules startingConfig goalConfig 
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-- IMPORTANT: Please do not change anything above here.
--            Write all your code below this line.
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

-- Warm-up 1A
-- r is the given RewriteRule
-- a is the nt portion of TRule, and b is the terminal portion
-- x is the nt portion of NTRule, y is the [nt] portion
-- for Chomsky Normal Form, NoRule is always True, TRule is always true
-- we only have to worry about NTRule which needs to have exactly two branches or elements in the list
-- so we check if length of y (the [nt] portion) is equal to 2
isRuleCNF :: RewriteRule nt t -> Bool
isRuleCNF r = case r of 
                NoRule -> True
                TRule a b -> True
                NTRule x y -> length y == 2

-- Warm-up 1B
-- c is the given CFG
-- n is set to the nonterminal symbols
-- s is set to the terminal symbols
-- i is set to the initial nonterminal symbols
-- r is set to the rules
-- x is the first rule in the list, rest is the rest of the list
-- this puts a case statement on the rules list
-- if the rules list is empty, return True so that the recursion works
-- otherwise, call the isRuleCNF function on the first rule
-- use the and operator with recursive function call on a CFG with every rule except the already checked rule
isCNF :: CFG nt t -> Bool
isCNF c = let (n, s, i, r) = c in 
  case r of 
    [] -> True
    x:rest -> isRuleCNF x && isCNF (n,s,i,rest)

-- Warm-up 2
-- l is the given list of lists
-- basically this takes a list of lists and reduces it to a single list by concatenating all the elements
concatLists :: [[a]] -> [a]
concatLists l = 
    case l of
        [] -> []
        (x:rest) -> x ++ concatLists rest

-- n is the new element to be added
-- l is the list given
-- this takes a list and goes through all the elements and adds n to the end
addToEnd :: a -> ([a] -> [a])
addToEnd n l = case l of
                       [] -> [n]
                       y:rest -> y:(addToEnd n rest)

-- if the current state is a goal config, we have succeeded, so return the history + the current state
-- otherwise, check if you can go any further from the current state using consumeFSA
-- if you cannot, return the empty list
-- if you can, x is the list of possible configurations which is the list of the new current configurations
-- recursively call the function using map to map x to nc (new current) and concatenate the resulting list of lists
pathsToGoalFSA :: (Eq st, Eq sy) => ((st,[sy]), [(st,[sy])]) -> [(st,sy,st)] -> [(st,[sy])] -> [[(st,[sy])]]
pathsToGoalFSA (current, history) rules goals = 
  case elem current goals of
    True -> [addToEnd current history]
    False -> case consumeFSA rules current of 
              [] -> []
              x -> concatLists (map(\nc -> pathsToGoalFSA (nc, addToEnd current history) rules goals) x)

-- These functions are placeholders to work with 'bottomUp' in Part 1.3. 
-- You should replace 'undefined' in these functions with your own code.

-- C
-- r represents the given list of rules
-- (n, s) represents the given configuration where n is the stack of nonterminals and s is the rest of the input string
-- if there is nothing to be parsed, shift should return the empty list
-- if there is something left, x is the next item to be parsed and rest is the rest of the list
-- check x against the rules and see if it matches any of them, if so add that
-- at the end, concatenate the lists together
shift :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
shift r (n,s) = 
    case s of 
      [] -> []
      x:rest -> concatLists(map(\rule -> 
        case rule of
          NTRule y z -> []
          NoRule -> []
          TRule y z ->
            case rhsTRule rule == x of 
              True -> [ParseStep Shift rule (addToEnd (NoBar (lhs rule)) n, rest)]
              False -> [] )r)

-- n is the integer, l is the list
-- given a list and number delete that number of items from the end of the list
-- if n == 0, return the list
-- if n >= length of the list, return empty list
-- otherwise
cutList :: Int -> [a] -> [a]
cutList n l = 
  case n >= length l of
    True -> []
    False -> case n == 0 of
      True -> l
      False -> cutList (n-1) (init l) -- built in function that gets rid of the last element

-- children is the given list of children, stack is the given stack
-- if children is empty, return True if stack is empty and False otherwise
-- otherwise, if stack is empty, return False; otherwise, check if the first elements are equal
-- x is the first element of children, rest is the rest of the children; y is the first element of stack, rest2 is the rest of the stack
-- y2 is the nt from y which is type Stack nt 
-- use the and operator with a recursive call to the function with rest and rest2
compareChildrenAndStack :: (Eq nt) => [nt] -> [Stack nt] -> Bool
compareChildrenAndStack children stack =
  case children of 
    [] -> case stack of 
            [] -> True
            x -> False
    x:rest -> case stack of
                [] -> False
                y:rest2 -> case y of 
                            Bar y2 -> False
                            NoBar y2 -> x == y2 && compareChildrenAndStack rest rest2

-- n is the integer, stack is the stack
-- x is the item popped, rest is the rest of the stack
-- given an integer and a list, pop elements from the front of the list until the length of the list is the given number
-- recursive call should terminate when n is equal to the length of the stack passed in
popStack :: Int -> [a] -> [a]
popStack n stack = 
  case stack of
    [] -> []
    x:rest -> case n >= length stack of
                True -> stack
                False -> popStack n rest

-- head is the nt of the given NTRule, children is the list of nt, stack is the given stack 
-- if the stack is not at least the size of the children, the rule is invalid
-- otherwise, cut the length of the stack to the size of the children and compare both stacks
checkValidNTRule :: (Eq nt, Eq t) => RewriteRule nt t -> [Stack nt] -> Bool
checkValidNTRule (NTRule head children) stack = 
  case length stack >= length children of 
    False -> False
    True -> 
      let newStack = popStack (length children) stack in
        compareChildrenAndStack children newStack

applyValidNTRule :: (Eq nt, Eq t) => RewriteRule nt t -> [Stack nt] -> [Stack nt]
applyValidNTRule (NTRule head children) stack = 
  addToEnd (NoBar head) (cutList (length children) stack)

-- r is the list of given rules
-- (n,s) is the given configuration where n is [Stack nt] and s is [nt]
-- if n is an empty list, there is nothing to reduce, so return the empty list
-- otherwise, x just represents that there is something there
-- map the rules to the case statement checking the validity of each rule using checkValidNTRule
-- if the rule is valid, add the ParseStep, otherwise, add the empty string
-- concatenate the list of lists and return
reduce :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
reduce r (n,s) = 
  case n of 
    [] -> []
    x -> concatLists(map(\rule ->
      case rule of
        TRule y z -> []
        NoRule -> []
        NTRule y z ->
          case checkValidNTRule rule n of 
            True -> let newStack = applyValidNTRule rule n in
              [ParseStep Reduce rule (newStack, s)]
            False -> [])r)

-- D
-- takes two parameters of type Stack nt (stack1 and stack2) and compares them
-- n and n2 are the nt parameters of the Stack data type for stack1 and stack2 respectively
-- if stack1 is Bar n, return False if stack2 is NoBar n2, otherwise return whether n == n2
-- else if stack1 is NoBar n, return False if stack2 is Bar n2, otherwise return whether n == n2
compareStackData :: (Eq nt) => Stack nt -> Stack nt -> Bool
compareStackData stack1 stack2 =
  case stack1 of
    Bar n -> case stack2 of
                Bar n2 -> n == n2 
                NoBar n2 -> False
    NoBar n -> case stack2 of  
                  Bar n2 -> False 
                  NoBar n2 -> n == n2

-- takes two stacks (aka lists of Stack nt) and compares them (stack1 and stack2)
-- if stack1 is empty, return whether stack2 is also empty
-- otherwise, if stack2 is empty return False, and otherwise, compare the data of the first elements of stack1 and stack2 (x and y respectively)
-- use the and operator with a recursive call to compare the rest of the elements 
-- rest is the rest of stack1, rest2 is the rest of stack2
compareStacks :: (Eq nt) => [Stack nt] -> [Stack nt] -> Bool
compareStacks stack1 stack2 = 
  case stack1 of
    [] -> length stack2 == 0
    x:rest -> 
      case stack2 of
        [] -> False
        y:rest2 -> compareStackData x y && compareStacks rest rest2

-- takes two lists of some type and compares them (list1 and list2)
-- literally the exact same as the above but for regular data types
compareLists :: (Eq a) => [a] -> [a] -> Bool
compareLists list1 list2 = 
  case list1 of
    [] -> length list2 == 0
    x:rest -> 
      case list2 of
        [] -> False
        y:rest2 -> x == y && compareLists rest rest2

-- compare the start configuration (startStack, startString) with the goal config (goalStack, goalString)
-- compare the startString with the goalString -> if False, return False
-- otherwise return the comparison of the startStack with the goalStack 
compareStartAndGoal :: (Eq nt, Eq t) => Config nt t -> Config nt t -> Bool
compareStartAndGoal (startStack, startString) (goalStack, goalString) = 
  case compareLists startString goalString of
    True -> compareStacks startStack goalStack 
    False -> False

parsesToGoal :: (Eq nt, Eq t)
       => [[RewriteRule nt t] -> Config nt t -> [ParseStep nt t]]
          -- ^ List of transition steps. ^
       -> [RewriteRule nt t]  -- Rules from the CFG.
       -> Config nt t         -- Starting configuration.
       -> Config nt t         -- Goal configuration.
       -> (ParseStep nt t, [ParseStep nt t])  -- Current and history
       -> [[ParseStep nt t]]  -- New list.
parsesToGoal steps rules (startStack, startString) (goalStack, goalString) (current, history) = 
  case compareStartAndGoal (startStack, startString) (goalStack, goalString) of
    True -> [addToEnd current history]
    False -> let stepList = concatLists (map(\step -> step rules (startStack, startString))steps) in
      case stepList of
        [] -> []
        parsesteps -> 
          concatLists (map(
            \nc -> parsesToGoal steps rules (getConfig nc) (goalStack, goalString) (nc, addToEnd current history)) parsesteps)

-- simple cfg to test bottom up parser
cfgSimple :: CFG Cat String
cfgSimple = ([V,NP], ["watches","spies"], 
         VP, 
         [(NTRule VP [V,NP]),
          (TRule NP "watches"), 
          (TRule V "spies")
          ]
        )

-- even simpler cfg to test bottom up parser
cfgSimpler :: CFG Cat String
cfgSimpler = ([V,VP], ["watches"], 
         VP, 
         [(TRule VP "watches"),
          (TRule V "watches")
          ]
        )

-- call the helper function parsesToGoal, similar to what we did with pathsToGoalFSA
-- the first ParseStep is the "current" and history is an empty string
-- current should be ParseStep NoTransition NoRule (startStack, startString) because that is the starting configuration
parser :: (Eq nt, Eq t)
       => [[RewriteRule nt t] -> Config nt t -> [ParseStep nt t]]
          -- ^ List of transition steps. ^
       -> [RewriteRule nt t]  -- Rules from the CFG.
       -> Config nt t         -- Starting configuration.
       -> Config nt t         -- Goal configuration.
       -> [[ParseStep nt t]]  -- List of possible parses.
parser steps rules (startStack, startString) (goalStack, goalString) = 
  parsesToGoal steps rules (startStack, startString) (goalStack, goalString) (ParseStep NoTransition NoRule (startStack, startString), [])

-- E
-- this takes a TRule and tells you if it is valid in "match"
-- head is the nt of the given TRule and the child is the t of the TRule
-- stack is the given Stack nt
-- terminal is the given t
-- basically, both items have to match
checkValidTRule :: (Eq nt, Eq t) => RewriteRule nt t -> Stack nt -> t -> Bool
checkValidTRule (TRule head child) stack terminal = compareStackData (NoBar head) stack && child == terminal

-- cfg to test top down parser
cfgTopDown :: CFG Cat String
cfgTopDown = ([V,VP,NP,D,N,S], ["the","baby","saw","boy"], S, 
         [(NTRule S [NP,VP]), (NTRule NP [D,N]), (NTRule VP [V,NP]),
         (TRule V "saw"), (TRule N "boy"), (TRule N "baby"), (TRule D "the")
          ]
        )

-- r is the list of rules, (n,s) is the starting configuration where n is [Stack nt] and s is [t]
-- if input string is empty, return empty list
-- otherwise, if the starting stack is empty, return empty list, otherwise, 
-- x is first terminal is the input string, y is first Stack nt in the starting stack
-- rest is the rest of the input string, rest2 is the rest of the stack
-- map all rules, if rule is valid, add the ParseStep associated to the rule
-- otherwise, add empty list
-- concatenate at the end to reduce it to one list
match :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
match r (n,s) = 
    case s of 
      [] -> []
      x:rest -> 
        case n of 
          [] -> []
          y:rest2 -> concatLists(map(\rule -> 
            case rule of
              NTRule w z -> []
              NoRule -> []
              TRule w z ->
                case checkValidTRule rule y x of 
                  True -> [ParseStep Match rule (rest2, rest)]
                  False -> [])r)

-- given a rule and a nonterminal,
-- if the rule is anything other than an NTRule, return False
-- otherwise, return whether nonterminal is equal to NoBar x
-- where x is the left hand side of the rule and y is the right hand side
checkValidPredictRule :: (Eq nt, Eq t) => RewriteRule nt t -> Stack nt -> Bool
checkValidPredictRule rule nonterminal = 
  case rule of
    NoRule -> False
    TRule x y -> False
    NTRule x y -> compareStackData nonterminal (NoBar x)

-- given a list of nt, turn it into a list of Stack nt
-- nonterminals is the given list
-- basically just go through and convert the first element of the list to Stack nt by adding NoBar
-- then add on the rest of the converted list with a recursive call
turnNTtoStack :: (Eq nt) => [nt] -> [Stack nt]
turnNTtoStack nonterminals = 
  case nonterminals of
    [] -> []
    x:rest -> (NoBar x):(turnNTtoStack rest)

-- r is the list of rules, (n,s) is the starting configuration where n is [Stack nt] and s is [t]
-- if starting stack is empty, return empty list
-- otherwise, for each rule, check if it is a valid rule
-- x is the first element of the starting stack, rest is the rest of the starting stack
-- if so, add the corresponding ParseStep, otherwise add the empty list
-- concatenate the lists at the end
predict :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
predict r (n,s) = 
  case n of
    [] -> []
    x:rest -> concatLists(map(\rule -> 
      case (checkValidPredictRule rule x) of 
        True -> [ParseStep Predict rule (concatLists [(turnNTtoStack (rhsNTRule rule)), rest], s)]
        False -> [])r)

-- modeled off bottomUp
-- I changed the rules to match and predict
-- I changed the starting config to be [NoBar start], input
-- I changed the goal config to be [],[]
topDown :: (Eq nt, Eq t) => CFG nt t -> [t] -> [[ParseStep nt t]]
topDown cfg input =
  let (nts, ts, start, rules) = cfg in
  let startingConfig = ([NoBar start], input) in
  let goalConfig = ([], []) in
  parser [match, predict] rules startingConfig goalConfig 

-- F
-- this takes a TRule and tells you if it is valid in "matchLC"
-- head is the nt of the given TRule and the child is the t of the TRule
-- stack is the given Stack nt
-- terminal is the given t
-- basically, both items have to match and the stack element must be a Bar element
checkValidTRuleMatchLC :: (Eq nt, Eq t) => RewriteRule nt t -> Stack nt -> t -> Bool
checkValidTRuleMatchLC (TRule head child) stack terminal = compareStackData (Bar head) stack && child == terminal

-- honestly the same as match, except you call checkValidTRuleMatchLC instead 
-- (means only works if the stack element is no bar)
-- r is the list of rules, (n,s) is the starting configuration where n is [Stack nt] and s is [t]
-- if input string is empty, return empty list
-- otherwise, if the starting stack is empty, return empty list, otherwise, 
-- x is first terminal is the input string, y is first Stack nt in the starting stack
-- rest is the rest of the input string, rest2 is the rest of the stack
-- map all rules, if rule is valid, add the ParseStep associated to the rule
-- otherwise, add empty list
-- concatenate at the end to reduce it to one list
matchLC :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
matchLC r (n,s) = 
    case s of 
      [] -> []
      x:rest -> 
        case n of 
          [] -> []
          y:rest2 -> concatLists(map(\rule -> 
            case rule of
              NTRule w z -> []
              NoRule -> []
              TRule w z ->
                case checkValidTRuleMatchLC rule y x of 
                  True -> [ParseStep Match rule (rest2, rest)]
                  False -> [])r)

-- pretty much the same as shift, but you add to the front of the list instead in ParseStep
-- r represents the given list of rules
-- (n, s) represents the given configuration where n is the stack of nonterminals and s is the rest of the input string
-- if there is nothing to be parsed, shift should return the empty list
-- if there is something left, x is the next item to be parsed and rest is the rest of the list
-- check x against the rules and see if it matches any of them, if so add that
-- at the end, concatenate the lists together
shiftLC :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
shiftLC r (n,s) = 
  case s of 
    [] -> []
    x:rest -> concatLists(map(\rule -> 
      case rule of
        NTRule y z -> []
        NoRule -> []
        TRule y z ->
          case rhsTRule rule == x of 
            True -> [ParseStep Shift rule ((NoBar (lhs rule)):n, rest)]
            False -> [] )r) 
  
-- given a rule and a nonterminal,
-- if the rule is anything other than an NTRule, return False
-- otherwise, x is the left hand side of the rule and y is the right hand side
-- if y is empty list, return false (should not happen, but just to be thorough
-- otherwise, z is the first element of y, and rest is the rest of y
-- return whether or not the given nonterminal is equal to NoBar z
checkValidPredictLCRule :: (Eq nt, Eq t) => RewriteRule nt t -> Stack nt -> Bool
checkValidPredictLCRule rule nonterminal = 
  case rule of
    NoRule -> False
    TRule x y -> False
    NTRule x y -> case y of
      [] -> False
      z:rest -> compareStackData nonterminal (NoBar z)

-- given a list of nt, turn it into a list of Stack nt
-- nonterminals is the given list
-- basically just go through and convert the first element of the list to Stack nt by adding Bar
-- then add on the rest of the converted list with a recursive call
turnNTtoBarredStack :: (Eq nt) => [nt] -> [Stack nt]
turnNTtoBarredStack nonterminals = 
  case nonterminals of
    [] -> []
    x:rest -> (Bar x):(turnNTtoBarredStack rest)

-- similar to predict except for the way it constructs the ParseStep and the function it calls to check validity
-- remove the first element from the right hand list, concatenate that with NoBar left-hand side, and the rest of the stack
-- r is the list of rules, (n,s) is the starting configuration where n is [Stack nt] and s is [t]
-- if starting stack is empty, return empty list
-- otherwise, for each rule, check if it is a valid rule
-- x is the first element of the starting stack, rest is the rest of the starting stack
-- if so, add the corresponding ParseStep, otherwise add the empty list
-- concatenate the lists at the end
predictLC :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
predictLC r (n,s) = 
  case n of
    [] -> []
    x:rest -> concatLists(map(\rule -> 
      case (checkValidPredictLCRule rule x) of 
        True -> let barred = (turnNTtoBarredStack (rhsNTRule rule)) in
          [ParseStep Predict rule (concatLists [popStack (length barred - 1) barred, [NoBar (lhs rule)], rest], s)]
        False -> [])r)

-- check if a rule is valid for connectLC
-- given a rule and two nonterminals (nonterminal1 and nonterminal2),
-- if the rule is anything other than an NTRule, return False
-- otherwise, x is the left hand side of the rule and y is the right hand side
-- compare Bar x with the second nonterminal, use the and operator with the following
-- if y is empty list, return false (should not happen, but just to be thorough
-- otherwise, z is the first element of y, and rest is the rest of y
-- return whether or not the first given nonterminal is equal to NoBar z
checkValidConnectLCRule :: (Eq nt, Eq t) => RewriteRule nt t -> Stack nt -> Stack nt -> Bool
checkValidConnectLCRule rule nonterminal1 nonterminal2 = 
  case rule of
    NoRule -> False
    TRule x y -> False
    NTRule x y -> 
      compareStackData (Bar x) nonterminal2 && case y of
        [] -> False
        z:rest -> compareStackData (NoBar z) nonterminal1 


-- r is the list of rules, (n,s) is the starting configuration where n is [Stack nt] and s is [t]
-- if starting stack is empty, return empty list
-- if starting stack has only one value, return empty list
-- otherwise, for each rule, check if it is a valid rule
-- x is the first element of the starting stack, y is the second, rest is the rest of the starting stack
-- if so, add the corresponding ParseStep, otherwise add the empty list
-- concatenate the lists at the end
connectLC :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
connectLC r (n,s) = 
  case n of
    [] -> []
    x:[] -> []
    x:y:rest -> concatLists(map(\rule -> 
      case (checkValidConnectLCRule rule x y) of 
        True -> let barred = (turnNTtoBarredStack (rhsNTRule rule)) in
          [ParseStep Connect rule (concatLists [popStack (length barred - 1) barred, rest], s)]
        False -> [])r)

-- modeled off bottomUp
-- I changed the rules to matchLC, shiftLC, predictLC, and connectLC
-- I changed the starting config to be [Bar start], input
-- I changed the goal config to be [],[]
leftCorner :: (Eq nt, Eq t) => CFG nt t -> [t] -> [[ParseStep nt t]]
leftCorner cfg input =
  let (nts, ts, start, rules) = cfg in
  let startingConfig = ([Bar start], input) in
  let goalConfig = ([], []) in
  parser [matchLC, shiftLC, predictLC, connectLC] rules startingConfig goalConfig 

cfgCat :: CFG Cat String
cfgCat = ([S, VP,NP,D,V,N], ["cat","dog","hates","the"], 
         S, 
         [(NTRule VP [V,NP]), (NTRule S [NP,VP]), (NTRule NP [D, N]),
          (NTRule VP [V]),
          (TRule N "cat"),
          (TRule V "hates"), (TRule N "dog"), (TRule D "the")
          ]
        )