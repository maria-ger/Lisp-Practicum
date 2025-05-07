{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use uncurry" #-}
{-# HLINT ignore "Use tuple-section" #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# HLINT ignore "Use foldl" #-}

module Eval (addFuncToStack, initFStack, correct,
             evalExpr, evalExprs, takeSExpr, printList,
             initLambdaList, funcParams, allAtoms, atomToString) where

import Types (SExpr(Atom, IntNum, FloatNum, Str, Nil, Pair, None),
              LambdaList (LambdaList), VarValue(Init, Val),
              Callable(BaseCall, UserCall, UserVar), FStack(Empty, Cons),
              Error(Error) )
import Data.Char (toUpper)
import GHC.Float (int2Double)
import GHC.ResponseFile (escapeArgs)

-- working with the stack of functions

initFStack::FStack
initFStack = addVars ["S1", "S2", "S3", "S4"] (foldl (\stack func -> Cons (BaseCall func) stack) Empty functions )
             where functions = [("car", car), ("cdr", cdr), ("cons", cons),
                                ("quote", quote), ("eval", eval),
                                ("cond", cond), ("atom", atom),
                                ("eq", eq), ("eql", eql), ("null", Eval.null),
                                ("numberp", numberp), ("symbolp", symbolp),
                                ("listp", listp), ("member", member),
                                ("append", append), ("list", list),
                                ("+", (Eval.+)), ("-", (Eval.-)),
                                ("*", (Eval.*)), ("/", (Eval./)),
                                ("<", (Eval.<)), (">", (Eval.>)),
                                ("<=", (Eval.<=)), (">=", (Eval.>=)),
                                ("defun", defun), ("setq", setq),
                                ("print", Eval.print)]

addVars::[String]->FStack->FStack
addVars [] stack = stack
addVars (var:s) stack = addVars s (addVarToStack var Nil stack)

addFuncToStack::String->Int->LambdaList->SExpr->(FStack->FStack)
addFuncToStack fname n params expr = Cons (UserCall (fname, n, params, expr))

addVarToStack::String->SExpr->(FStack->FStack)
addVarToStack vname expr = Cons (UserVar (vname, expr))

isBase::String->FStack->Bool
isBase _ Empty = False
isBase name (Cons func stack) | name == map toUpper (getName func) = True
                              | otherwise = isBase name stack

getBase::String->FStack->(FStack->[SExpr]->Either Error (FStack, SExpr))
getBase _ Empty = \_ _ -> Right (Empty, None)
getBase name
        (Cons (BaseCall (fname, f)) stack) | name == map toUpper fname = f
                                           | otherwise = getBase name stack
getBase name (Cons (UserCall _) stack) = getBase name stack
getBase name (Cons (UserVar _) stack) = getBase name stack

isUser::String->FStack->Bool
isUser _ Empty = False
isUser name (Cons (UserCall func) stack) | name == getName (UserCall func) = True
                                         | otherwise = isUser name stack
isUser name (Cons _ stack) = isUser name stack

getUser::String->FStack->(LambdaList, SExpr)
getUser _ Empty = (LambdaList [], None)
getUser name
        (Cons (UserCall (fname, _, lst, expr)) stack) | name == fname
                                                     = (lst, expr)
                                                      | otherwise
                                                     = getUser name stack
getUser name (Cons (UserVar _) stack) = getUser name stack
getUser _ _ = (LambdaList [], None)

isVar::String->FStack->Bool
isVar _ Empty = False
isVar name (Cons (UserVar func) stack) | name == getName (UserVar func) = True
                                       | otherwise = isVar name stack
isVar name (Cons _ stack) = isVar name stack

getVar::String->FStack->SExpr
getVar _ Empty = None
getVar name
        (Cons (UserVar (fname, expr)) stack) | name == fname = expr
                                             | otherwise = getVar name stack
getVar name (Cons (UserCall _) stack) = getVar name stack
getVar _ _ = None

getName::Callable->String
getName (BaseCall (name, _)) = name
getName (UserCall (name, _, _, _)) = name
getName (UserVar (name, _)) = name


-- main function for expression evaluation

evalExprs::FStack->[SExpr]->[SExpr]->Either Error [SExpr]
evalExprs _ results [] = Right results
evalExprs stack cur (e:es) | correct res = evalExprs (fst r) (cur ++ [snd r]) es
                           | otherwise = Left err
                             where res = evalExpr stack e
                                   r = case res of
                                    Right x -> x
                                    Left _ -> (Empty, None)
                                   err = case res of
                                    Right _ -> Error ""
                                    Left x -> x

evalExpr::FStack->SExpr->Either Error (FStack, SExpr)
evalExpr stack (IntNum x) = Right (stack, IntNum x)
evalExpr stack (FloatNum x) = Right (stack, FloatNum x)
evalExpr stack (Str x) = Right (stack, Str x)
evalExpr stack Nil = Right (stack, Nil)
evalExpr stack (Atom x) | x == "T" = Right (stack, Atom x)
                        | isVar x stack
                          = evalExpr stack user
                        | otherwise = Left (Error "No such variable!")
                        where user = getVar x stack
evalExpr stack
         (Pair (Pair (Atom "LAMBDA",
          Pair (xs, Pair (expr, Nil))), ps)) | not (correctParams params)
                                               = Left (Error "Incorrect actual parameters!")
                                             | not (correctParams names)
                                               = Left (Error "Incorrect formal parameters!")
                                             | otherwise
                                               = applyLambda stack
                                                             names
                                                             expr
                                                             params
                                             where params = funcParams ps
                                                   names = funcParams xs
evalExpr stack
         (Pair (Atom "LET",
          Pair (lst, Pair (expr, Nil)))) | not (correctParams params)
                                           = Left (Error "Incorrect parameters!")
                                         | otherwise = letLambda stack
                                                                 params
                                                                 expr
                                         where params = funcParams lst
evalExpr stack (Pair (Atom x, y)) | not (correctParams params)
                                    = Left (Error "Incorrect parameters!")
                                  | x == "QUOTE" = car stack [y]
                                  | x == "COND" = cond stack params
                                  | x == "DEFUN" = defun stack params
                                  | x == "SETQ" = setq stack params
                                  | isUser x stack = applyUser stack
                                                               (fst user)
                                                               (snd user)
                                                               params
                                  | isBase x stack = applyBase stack
                                                               (getBase x
                                                                        stack)
                                                               params
                                  | otherwise = Left (Error "No such function!")
                                  where params = funcParams y
                                        user = getUser x stack
evalExpr _  _= Left (Error "Incorrect S-expression!")


formLambdaList::LambdaList->[SExpr]->LambdaList
formLambdaList (LambdaList lst) exprs = LambdaList (zipWith (\(name, _) expr ->
                                                   (name, Val expr)) lst exprs)


-- evaluate expression via base LISP function
applyBase::FStack->(FStack->[SExpr]->Either Error (FStack, SExpr))->[SExpr]->
  Either Error (FStack, SExpr)
applyBase stack func params | correctList vals
                              = func stack (map takeSExpr vals)
                            | otherwise
                            --  = Left (Error "Function parameters are incorrect!")
                              = Left (Error (collectErrors errors))
                            where vals = map (evalExpr stack) params
                                  errors = map getError (filter (not . correct) vals)

-- evaluate expression via user (defun) function
applyUser::FStack->LambdaList->SExpr->[SExpr]->Either Error (FStack, SExpr)
applyUser stack (LambdaList lst)
          expr params | length lst == length params
                        = evalExpr stack (substVars
                                          (formLambdaList (LambdaList lst)
                                                          params)
                                          expr)
                      | otherwise = Left (Error "Number of parameters imbalance!")

substVars::LambdaList->SExpr->SExpr
substVars (LambdaList []) expr = expr
substVars (LambdaList ((name, value) : rest)) expr = substVars
                                                    (LambdaList rest)
                                                    (subst name value expr)

subst::String->VarValue->SExpr->SExpr
subst name (Val expr) (Atom x) | x == name = expr
                               | otherwise = Atom x
subst _ _ (Pair (Atom "QUOTE", y)) = Pair (Atom "QUOTE", y)
subst name (Val expr) (Pair (x, y)) = Pair (subst name (Val expr) x,
                                            subst name (Val expr) y)
subst _ _ expr = expr

-- LISP functions implementation

eval::FStack->[SExpr]->Either Error (FStack, SExpr)
eval stack [expr] = evalExpr stack expr
eval _ _ = Left (Error "EVAL takes one parameter!")


cond::FStack->[SExpr]->Either Error (FStack, SExpr)
cond _ [] = Left (Error "COND must have at least one parameter!")
cond stack params = condDo stack params

condDo::FStack->[SExpr]->Either Error (FStack, SExpr)
condDo stack [] = Right (stack, Nil)
condDo stack ((Pair (x, Nil)):rest) | correct p && predicate p = p
                                    | correct p = condDo stack rest
                                    | otherwise = Left (Error "Incorrect parameters!")
                                    where p = evalExpr stack x
condDo stack ((Pair (x, Pair (e, Nil))): rest) | correct p && predicate p
                                                 = evalExpr stack e
                                               | correct p = condDo stack rest
                                               | otherwise
                                                 = Left (Error "Incorrect parameters!")
                                               where p = evalExpr stack x
condDo _ _ = Left (Error "Incorrect parameters!")


letParams::[SExpr]->[(SExpr, SExpr)]
letParams [] = []
letParams ((Pair (x, Pair(p, Nil))): rest) = (x, p) : letParams rest
letParams _ = [(None, None)]

correctLet::[(SExpr, SExpr)]->Bool
correctLet [(None, None)] = False
correctLet _ = True

letLambda::FStack->[SExpr]->SExpr->Either Error (FStack, SExpr)
letLambda stack params expr | not (correctLet paramlist)
                              = Left (Error "Incorrect parameters!")
                            | otherwise = applyLambda stack
                                          (map fst paramlist)
                                          expr
                                          (map snd paramlist)
                            where paramlist = letParams params

applyLambda::FStack->[SExpr]->SExpr->[SExpr]->Either Error (FStack, SExpr)
applyLambda stack names expr params | allAtoms names
                                      = applyUser stack
                                                  (initLambdaList
                                                   (map atomToString names))
                                                  expr
                                                  params
                                    | otherwise
                                     = Left (Error "Formal parameters must be atoms!")

newFuncNum::FStack->Int
newFuncNum Empty = 0
newFuncNum (Cons (UserCall (_, _, _, _)) stack) = 1 Prelude.+ newFuncNum stack
newFuncNum (Cons _ stack) = newFuncNum stack

defun :: FStack->[SExpr]->Either Error (FStack, SExpr)
defun stack [Atom name, params, body] | Prelude.null lst
                                        = Right (addFuncToStack name
                                                            (newFuncNum stack)
                                                            (LambdaList [])
                                                            body
                                                            stack, Atom name)
                                      | allAtoms lst
                                        = Right
                                          (addFuncToStack name
                                                      (newFuncNum stack)
                                                      (initLambdaList
                                                       (map atomToString lst))
                                                      body
                                                      stack, Atom name)
                                      | otherwise
                                        = Left (Error "Formal parameters must be atoms!")
                                      where lst = funcParams params
defun _ _ = Left (Error "Incorrect function definition!")

setq :: FStack->[SExpr]->Either Error (FStack, SExpr)
setq stack [Atom name, body] | correct expr
                               = Right (addVarToStack name body stack, None)
                             | otherwise = Left (Error "Incorrect value of variable!")
                             where expr = evalExpr stack body
setq _ _ = Left (Error "Incorrect variable definition!")

initLambdaList::[String]->LambdaList
initLambdaList exprs = LambdaList (map (\name -> (name, Init)) exprs)

allAtoms::[SExpr]->Bool
allAtoms [] = True
allAtoms ((Atom _) : es) = allAtoms es
allAtoms _ = False


car::FStack->[SExpr]->Either Error (FStack, SExpr)
car stack [Pair (x, _)] = Right (stack, x)
car _ _ = Left (Error "CAR must be applyed to nonempty list!")


cdr::FStack->[SExpr]->Either Error (FStack, SExpr)
cdr stack [Pair (_, xs)] = Right (stack, xs)
cdr _ _ = Left (Error "CDR must be applyed to nonempty list!")


cons::FStack->[SExpr]->Either Error (FStack, SExpr)
cons stack [x, y] = Right (stack, Pair (x, y))
cons _ _ = Left (Error "CONS takes two parameters!")


atom::FStack->[SExpr]->Either Error (FStack, SExpr)
atom stack [Pair _] = Right (stack, Nil)
atom stack [_] = Right (stack, Atom "T")
atom _ _ = Left (Error "ATOM takes one parameter!")


eq::FStack->[SExpr]->Either Error (FStack, SExpr)
eq stack [Nil, Nil] = Right (stack, Atom "T")
eq stack [Atom x, Atom y] | x == y = Right (stack, Atom "T")
                    | otherwise = Right (stack, Nil)
eq stack [Atom _, _] = Right (stack, Nil)
eq stack [_, Atom _] = Right (stack, Nil)
eq stack [_, _] = Right (stack, Nil)
eq _ _ = Left (Error "EQ takes two parameters!")


eqNum::[SExpr]->SExpr
eqNum [IntNum x, IntNum y] | x == y = Atom "T"
                           | otherwise = Nil
eqNum [FloatNum x, FloatNum y] | x == y = Atom "T"
                               | otherwise = Nil
eqNum [IntNum x, FloatNum y] | int2Double x == y = Atom "T"
                             | otherwise = Nil
eqNum [FloatNum x, IntNum y] | x == int2Double y = Atom "T"
                             | otherwise =Nil
eqNum _ = None

eql::FStack->[SExpr]->Either Error (FStack, SExpr)
eql stack [x, y] | predicate (numberp stack [x]) &&
                   predicate (numberp stack [y])
                   = Right (stack, eqNum [x, y])
                 | predicate (numberp stack [x]) = Right (stack, Nil)
                 | otherwise = eq stack [x, y]
eql _ _ = Left (Error "EQL takes two parameters!")


null::FStack->[SExpr]->Either Error (FStack, SExpr)
null stack [x] = eq stack [x, Nil]
null _ _ = Left (Error "NULL takes one parameter!")


numberp::FStack->[SExpr]->Either Error (FStack, SExpr)
numberp stack [IntNum _] = Right (stack, Atom "T")
numberp stack [FloatNum _] = Right (stack, Atom "T")
numberp stack [_] = Right (stack, Nil)
numberp _ _ = Left (Error "NUMBERP takes one parameter!")


symbolp::FStack->[SExpr]->Either Error (FStack, SExpr)
symbolp stack [Str _] = Right (stack, Atom "T")
symbolp stack [Atom _] = Right (stack, Atom "T")
symbolp stack [Nil] = Right (stack, Atom "T")
symbolp stack [_] = Right (stack, Nil)
symbolp _ _ = Left (Error "SYMBOLP takes one parameter!")


listp::FStack->[SExpr]->Either Error (FStack, SExpr)
listp stack [Nil] = Right (stack, Atom "T")
listp stack [Pair _] = Right (stack, Atom "T")
listp stack [_] = Right (stack, Nil)
listp _ _ = Left (Error "LISTP takes one parameter!")


quote::FStack->[SExpr]->Either Error (FStack, SExpr)
quote stack [x] = Right (stack, x)
quote _ _ = Left (Error "QUOTE takes one parameter!")


(<)::FStack->[SExpr]->Either Error (FStack, SExpr)
(<) stack [IntNum x, IntNum y] | x Prelude.< y = Right (stack, Atom "T")
                               | otherwise = Right (stack, Nil)
(<) stack [IntNum x, FloatNum y] | int2Double x Prelude.< y = Right (stack, Atom "T")
                                 | otherwise = Right (stack, Nil)
(<) stack [FloatNum x, IntNum y] | x Prelude.< int2Double y = Right (stack, Atom "T")
                                 | otherwise = Right (stack, Nil)
(<) stack [FloatNum x, FloatNum y] | x Prelude.< y = Right (stack, Atom "T")
                                   | otherwise = Right (stack, Nil)
(<) _ _ = Left (Error "Incorrect parameters!")

(>)::FStack->[SExpr]->Either Error (FStack, SExpr)
(>) stack [IntNum x, IntNum y] | x Prelude.> y = Right (stack, Atom "T")
                               | otherwise = Right (stack, Nil)
(>) stack [IntNum x, FloatNum y] | int2Double x Prelude.> y = Right (stack, Atom "T")
                                 | otherwise = Right (stack, Nil)
(>) stack [FloatNum x, IntNum y] | x Prelude.> int2Double y = Right (stack, Atom "T")
                                 | otherwise = Right (stack, Nil)
(>) stack [FloatNum x, FloatNum y] | x Prelude.> y = Right (stack, Atom "T")
                                   | otherwise = Right (stack, Nil)
(>) _ _ = Left (Error "Incorrect parameters!")

(<=)::FStack->[SExpr]->Either Error (FStack, SExpr)
(<=) stack [IntNum x, IntNum y] | x Prelude.<= y = Right (stack, Atom "T")
                                | otherwise = Right (stack, Nil)
(<=) stack [IntNum x, FloatNum y] | int2Double x Prelude.<= y = Right (stack, Atom "T")
                                  | otherwise = Right (stack, Nil)
(<=) stack [FloatNum x, IntNum y] | x Prelude.<= int2Double y = Right (stack, Atom "T")
                                  | otherwise = Right (stack, Nil)
(<=) stack [FloatNum x, FloatNum y] | x Prelude.<= y = Right (stack, Atom "T")
                                    | otherwise = Right (stack, Nil)
(<=) _ _ = Left (Error "Incorrect parameters!")

(>=)::FStack->[SExpr]->Either Error (FStack, SExpr)
(>=) stack [IntNum x, IntNum y] | x Prelude.>= y = Right (stack, Atom "T")
                                | otherwise = Right (stack, Nil)
(>=) stack [IntNum x, FloatNum y] | int2Double x Prelude.>= y = Right (stack, Atom "T")
                                  | otherwise = Right (stack, Nil)
(>=) stack [FloatNum x, IntNum y] | x Prelude.>= int2Double y = Right (stack, Atom "T")
                                  | otherwise = Right (stack, Nil)
(>=) stack [FloatNum x, FloatNum y] | x Prelude.>= y = Right (stack, Atom "T")
                                    | otherwise = Right (stack, Nil)
(>=) _ _ = Left (Error "Incorrect parameters!")

(+)::FStack->[SExpr]->Either Error (FStack, SExpr)
(+) stack [] = Right (stack, IntNum 0)
(+) stack [IntNum x] = Right (stack, IntNum x)
(+) stack [FloatNum x] = Right (stack, FloatNum x)
(+) stack ((IntNum x) :
           (IntNum y) : xs) = (Eval.+) stack (IntNum (x Prelude.+ y) : xs)
(+) stack ((FloatNum x) :
           (FloatNum y) : xs) = (Eval.+) stack (FloatNum (x Prelude.+ y) : xs)
(+) stack ((FloatNum x) :
           (IntNum y) : xs) = (Eval.+) stack (FloatNum (x Prelude.+ dy) : xs)
                              where dy = int2Double y
(+) stack ((IntNum x) :
           (FloatNum y) : xs) = (Eval.+) stack (FloatNum (dx Prelude.+ y) : xs)
                                where dx = int2Double x
(+) _ _ = Left (Error "Incorrect parameters!")

(-)::FStack->[SExpr]->Either Error (FStack, SExpr)
(-) stack [IntNum x] = Right (stack, IntNum (negate x))
(-) stack [FloatNum x] = Right (stack, FloatNum x)
(-) stack ((IntNum x) :
           (IntNum y) : xs) | Prelude.null xs
                              = Right (stack, IntNum (x Prelude.- y))
                            | otherwise
                              = (Eval.-) stack (IntNum (x Prelude.- y) : xs)
(-) stack ((FloatNum x) :
           (FloatNum y) : xs) | Prelude.null xs
                                = Right (stack, FloatNum (x Prelude.- y))
                              | otherwise
                                = (Eval.-) stack (FloatNum (x Prelude.- y) : xs)
(-) stack ((FloatNum x) :
           (IntNum y) : xs) = (Eval.-) stack (FloatNum (x Prelude.- dy) : xs)
                              where dy = int2Double y
(-) stack ((IntNum x) :
           (FloatNum y) : xs) = (Eval.-) stack (FloatNum (dx Prelude.- y) : xs)
                                where dx = int2Double x
(-) _ _ = Left (Error "Incorrect parameters!")

(*)::FStack->[SExpr]->Either Error (FStack, SExpr)
(*) stack [] = Right (stack, IntNum 1)
(*) stack [IntNum x] = Right (stack, IntNum x)
(*) stack [FloatNum x] = Right (stack, FloatNum x)
(*) stack ((IntNum x) :
           (IntNum y) : xs) = (Eval.*) stack (IntNum (x Prelude.* y) : xs)
(*) stack ((FloatNum x) :
           (FloatNum y) : xs) = (Eval.*) stack (FloatNum (x Prelude.* y) : xs)
(*) stack ((FloatNum x) :
           (IntNum y) : xs) = (Eval.*) stack (FloatNum (x Prelude.* dy) : xs)
                              where dy = int2Double y
(*) stack ((IntNum x) :
           (FloatNum y) : xs) = (Eval.*) stack (FloatNum (dx Prelude.* y) : xs)
                                where dx = int2Double x
(*) _ _ = Left (Error "Incorrect parameters!")

(/)::FStack->[SExpr]->Either Error (FStack, SExpr)
(/) stack [IntNum x] = Right (stack, FloatNum (1 Prelude./ int2Double x))
(/) stack [FloatNum x] = Right (stack, FloatNum (1 Prelude./ x))
(/) stack ((IntNum x) :
           (IntNum y) : xs) | y == 0 = Left (Error "Division by zero!")
                            | Prelude.null xs
                              = Right (stack, FloatNum (dx Prelude./ dy))
                            | otherwise
                              = (Eval./) stack (FloatNum (dx Prelude./ dy) : xs)
                              where dx = int2Double x
                                    dy = int2Double y
(/) stack ((FloatNum x) :
           (FloatNum y) : xs) | y == 0 = Left (Error "Division by zero!")
                              | Prelude.null xs
                                = Right (stack, FloatNum (x Prelude./ y))
                              | otherwise
                                = (Eval./) stack (FloatNum (x Prelude./ y) : xs)
(/) stack ((FloatNum x) :
           (IntNum y) : xs) | y == 0 = Left (Error "Division by zero!")
                            | otherwise
                              = (Eval./) stack (FloatNum (x Prelude./ dy) : xs)
                              where dy = int2Double y
(/) stack ((IntNum x) :
           (FloatNum y) : xs) | y == 0 = Left (Error "Division by zero!")
                              | otherwise
                                = (Eval./) stack (FloatNum (dx Prelude./ y) : xs)
                                where dx = int2Double x
(/) _ _ = Left (Error "Incorrect parameters!")


member::FStack->[SExpr]->Either Error (FStack, SExpr)
member _ [Pair _, _] = Left (Error "First parameter can't be a list!")
member stack [_, Nil] = Right (stack, Nil)
member stack [a, Pair (x, y)] | predicate (eql stack [a, x])
                                = Right (stack, Atom "T")
                              | otherwise = member stack [a, y]
member _ _ = Left (Error "MEMBER takes two parameters!")


list::FStack->[SExpr]->Either Error (FStack, SExpr)
list stack [] = Right (stack, Nil)
list stack (e:es) | correct res = cons stack [e, takeSExpr res]
                  | otherwise = Left (Error "Incorrect parameter!")
                  where res = list stack es


append::FStack->[SExpr]->Either Error (FStack, SExpr)
append stack [x, y] | isProperList stack x && isProperList stack y
                      = Right (stack, doAppend stack x y)
                    | otherwise = Left (Error "Incorrect format of list!")
append _ _ = Left (Error "APPEND takes two parameters!")

doAppend::FStack->SExpr->SExpr->SExpr
doAppend _ Nil lst2 = lst2
doAppend stack lst1 lst2 = takeSExpr (cons stack [takeSExpr car1,
                                                  doAppend stack
                                                           (takeSExpr cdr1)
                                                           lst2])
                           where car1 = car stack [lst1]
                                 cdr1 = cdr stack [lst1]

isProperList::FStack->SExpr->Bool
isProperList _ Nil = True
isProperList stack
             (Pair x) = isProperList stack (takeSExpr (cdr stack [Pair x]))
isProperList _ _ = False

-- supporting functions (checking correctness)

funcParams::SExpr->[SExpr]
funcParams Nil = []
funcParams (Pair (x, xs)) = x : funcParams xs
funcParams _ = [None]

correctParams::[SExpr]->Bool
correctParams [None] = False
correctParams _ = True

correct::Either Error a->Bool
correct (Left _) = False
correct _ = True

correctList::[Either Error a]->Bool
correctList = all correct

getError::Either Error (FStack, SExpr)->Error
getError (Right _) = Error ""
getError (Left err) = err

collectErrors::[Error]->String
collectErrors [] = []
collectErrors [Error err] = err
collectErrors (Error err:rest) = err ++ '\n' : collectErrors rest

takeSExpr::Either Error (FStack, SExpr)->SExpr
takeSExpr (Left _) = None
takeSExpr (Right (_, x)) = x

predicate::Either Error (FStack, SExpr)->Bool
predicate (Right (_, Nil)) = False
predicate (Right (_, _)) = True
predicate _ = False

atomToString::SExpr->String
atomToString (Atom s) = s
atomToString _ = []

-- s-expression printable view

printList::[SExpr]->String
printList [] = []
printList ((Str s):rest) = s ++ "\n" ++ printList rest
printList (_:rest) = printList rest

fromSExpr::SExpr->String
fromSExpr Nil = "NIL"
fromSExpr (IntNum i) = show i
fromSExpr (FloatNum f) = show f
fromSExpr (Str s) = show s
fromSExpr (Atom a) = map toUpper a
fromSExpr (Pair (x, Nil)) = "(" ++ fromSExpr x ++ ")"
fromSExpr (Pair (x, Pair y)) = "(" ++ fromSExpr x ++  " "  ++
                               withoutBr (Pair y) ++ ")"
fromSExpr (Pair (x, y)) = "(" ++ fromSExpr x ++ " . " ++ fromSExpr y ++ ")"
fromSExpr _ = []

withoutBr::SExpr->String
withoutBr (Pair (x, Nil)) = fromSExpr x
withoutBr (Pair (x, Pair y)) = fromSExpr x ++  " "  ++ withoutBr (Pair y)
withoutBr (Pair (x, y)) = fromSExpr x ++  " . "  ++ fromSExpr y
withoutBr _ = []

print::FStack->[SExpr]->Either Error (FStack, SExpr)
print stack [x] = Right (stack, Str (fromSExpr x))
print _ _ = Left (Error "PRINT takes one parameter!")