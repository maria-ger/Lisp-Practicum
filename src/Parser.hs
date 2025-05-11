{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Parser (lispParser, addSpaces, parseInput, parseResult, textTags) where

import Text.Parsec.String ( Parser ) 
import Text.Parsec.Token
    ( GenLanguageDef( 
        reservedNames, caseSensitive, 
        commentStart, commentEnd, 
        identStart, identLetter
        ),
      LanguageDef, 
      GenTokenParser (whiteSpace, reserved, identifier, 
                      integer, float, stringLiteral),
      makeTokenParser )
import Text.Parsec.Language (emptyDef)
import Text.Parsec.Combinator (choice, option)
import Text.Parsec (parse, alphaNum, letter, eof, try, ParseError)
import Data.Char (toUpper)
import Data.Functor.Identity (Identity)
import Types ( SExpr(Atom, IntNum, FloatNum, Str, Nil, Pair, None), 
               FStack(Empty,Cons), LambdaList(LambdaList), 
               Callable(UserCall), Tag(Symb, Func, Var) )
import Eval (initLambdaList, funcParams, allAtoms, atomToString)

-- definition of LISP language (reserved tokens)
langDef :: LanguageDef st
langDef = emptyDef { commentStart = "",
                     commentEnd = "",
                     identStart = letter,
                     identLetter = alphaNum,
                     caseSensitive = False,
                     reservedNames = ["(", ")", " . ", "`", "T", "NIL", 
                                      "+ ", "- ", "*", "/", "%",
                                      "=", ">", "<", ">=", "<="] }

-- token parser
lexer :: GenTokenParser String u Identity
lexer = makeTokenParser langDef

parseInt::Parser SExpr
parseInt =  do
    n <- integer lexer
    return (IntNum (fromInteger n))

parseFloat::Parser SExpr
parseFloat = do
    n <- float lexer
    return (FloatNum n)

parseString::Parser SExpr
parseString = do
    s <- stringLiteral lexer
    return (Str s)

parseAtom::Parser SExpr
parseAtom = do
    i <- identifier lexer
    return (Atom (map toUpper i))

parsePlus::Parser SExpr
parsePlus = do
    reserved lexer "+"
    return (Atom "+")

parseMinus::Parser SExpr
parseMinus = do
    reserved lexer "-"
    return (Atom "-")

parseMul::Parser SExpr
parseMul = do
    reserved lexer "*"
    return (Atom "*")

parseDiv::Parser SExpr
parseDiv = do
    reserved lexer "/"
    return (Atom "/")

parseMod::Parser SExpr
parseMod = do
    reserved lexer "%"
    return (Atom "%")

parseEqual::Parser SExpr
parseEqual = do
    reserved lexer "="
    return (Atom "=")

parseLess::Parser SExpr
parseLess = do
    reserved lexer "<"
    return (Atom "<")

parseGreater::Parser SExpr
parseGreater = do
    reserved lexer ">"
    return (Atom ">")

parseLessOrEq::Parser SExpr
parseLessOrEq = do
    reserved lexer "<="
    return (Atom "<=")

parseGreaterOrEq::Parser SExpr
parseGreaterOrEq = do
    reserved lexer ">="
    return (Atom ">=")

parseNil::Parser SExpr
parseNil = do
    reserved lexer "("
    reserved lexer ")"
    return Nil

parseStrNil::Parser SExpr
parseStrNil = do
    reserved lexer "NIL"
    return Nil

parseTrue::Parser SExpr
parseTrue = do
    reserved lexer "T"
    return (Atom "T")

parseDotList::Parser SExpr
parseDotList = do
    reserved lexer "("
    carL <- parseSExpr
    reserved lexer "."
    cdrL <- parseSExpr
    reserved lexer ")"
    return (Pair (carL, cdrL))

parseList::Parser SExpr
parseList = do
    reserved lexer "("
    carL <- parseSExpr
    cdrL <- option Nil parseRest
    reserved lexer ")"
    return (Pair (carL, cdrL))

parseRest::Parser SExpr
parseRest = do
    carL <- parseSExpr
    cdrL <- option Nil parseRest
    return (Pair (carL, cdrL))

parseQuote::Parser SExpr
parseQuote = do
    reserved lexer "`"
    expr <- parseSExpr
    return (Pair (Atom "QUOTE", Pair (expr, Nil)))

parseSExpr::Parser SExpr
parseSExpr = choice [try parsePlus,
                     try parseMinus,
                     try parseMul,
                     try parseDiv,
                     try parseLessOrEq,
                     try parseGreaterOrEq,
                     try parseLess,
                     try parseGreater,
                     try parseFloat,
                     try parseInt, 
                     --parseString,
                     parseStrNil,
                     parseTrue,
                     parseAtom,
                     parseQuote,
                     try parseNil,
                     try parseDotList,
                     parseList]

lispParser::Parser [SExpr]
lispParser = do
    whiteSpace lexer
    expr <- parseSExpr
    rest<-option [] lispParser
    return (expr : rest)


addSpaces::String->String
addSpaces [] = []
addSpaces (x : xs) | x == '(' || x == ')' || x == '`' 
                        = " " ++ [x] ++ " " ++ addSpaces xs
                   | otherwise = x : addSpaces xs


-- main parser

parseInput::String->Either ParseError [SExpr]
parseInput s = parse lispParser "" (addSpaces s)

parseResult::Either ParseError [SExpr]->[Tag]
parseResult (Left _) = []
parseResult (Right exprs) = flatTags (toTagAll (loadFStack 0 Empty exprs) exprs)


-- stack

addToStack::String->Int->LambdaList->SExpr->(FStack->FStack)
addToStack fname fnum params expr = Cons (UserCall (fname, fnum, params, expr))

loadFStack::Int->FStack->[SExpr]->FStack
loadFStack _ stack [] = stack
loadFStack n stack (Pair (Atom "DEFUN", p):s) = loadFStack (n + 1) (addToStack name n lambdalst body stack) s
                                                where [Atom name, params, body] = funcParams p
                                                      lambdalst = initLambdaList (map atomToString lst)
                                                      lst = funcParams params
                                                      
loadFStack n stack (_:s) = loadFStack n stack s

onStack::FStack->String->Bool
onStack Empty _ = False
onStack (Cons (UserCall (fname, _, _, _)) stack) name | name == fname = True
                                                      | otherwise = onStack stack name
onStack (Cons _ stack) name = onStack stack name

funcNum::FStack->String->Int
funcNum Empty _ = 0
funcNum (Cons (UserCall (fname, num, _, _)) stack) name | name == fname = num
                                                        | otherwise = funcNum stack name
funcNum (Cons _ stack) name = funcNum stack name                                                        


-- SExpr to Tag

flatTags::[[Tag]]->[Tag]
flatTags = foldr1 (++)

textTags::[Tag]->String
textTags [] = []
textTags ((Symb s):rest) = s ++ textTags rest
textTags (_:rest) = textTags rest

toTagAll::FStack->[SExpr]->[[Tag]]
toTagAll stack = map (toTag stack)

toTag::FStack->SExpr->[Tag]
toTag _ Nil = [Symb "NIL"]
toTag _ (IntNum i) = [Symb (show i)]
toTag _ (FloatNum f) = [Symb (show f)]
toTag _ (Str s) = [Symb s]
toTag _ (Atom a) = [Symb (map toUpper a)]
toTag _ (Pair (Atom "QUOTE", Pair (y, Nil))) = [Symb "(", Symb "QUOTE"] 
                                                           ++ quoteToTag y ++ [Symb ")"]
toTag stack (Pair (Atom "EVAL", Pair 
                    (Pair (Atom "QUOTE", Pair (y, Nil)), Nil))) = [Symb "(", Symb "EVAL", 
                                                                  Symb "(", Symb "QUOTE"]
                                                                  ++ toTag stack y
                                                                  ++ [Symb ")", Symb ")"]
toTag stack (Pair (Atom "DEFUN", p)) = [Symb "(", Symb "DEFUN"] ++ [Func (funcNum stack name)]
                                       ++ [Symb "("] ++ varList 0 varnames ++ 
                                       replaceVars stack varnames body ++ [Symb ")"]
                                       where [Atom name, params, body] = funcParams p
                                             varnames = funcParams params
toTag stack (Pair (Atom "COND", p)) = [Symb "(", Symb "COND"] ++ condToTag [] stack params ++ [Symb ")"]
                                      where params = funcParams p
toTag stack (Pair (Atom x, Nil)) | onStack stack x = [Symb "(", Func (funcNum stack x), Symb ")"]
                                 | otherwise = [Symb "(", Symb x, Symb ")"]
toTag stack (Pair (Atom x, Pair y)) | onStack stack x = [Symb "(", Func (funcNum stack x)]
                                                        ++ toTagNoBr stack (Pair y)
                                                        ++ [Symb ")"]
                                    | otherwise = [Symb "(", Symb x] ++
                                                  toTagNoBr stack (Pair y) ++ [Symb ")"]
toTag stack (Pair (x, Nil)) = [Symb "("] ++ toTag stack x ++ [Symb ")"]
toTag stack (Pair (x, Pair y)) = [Symb "("] ++ toTag stack x ++ toTagNoBr stack (Pair y) ++ [Symb ")"]
toTag stack (Pair (x, y)) = [Symb "("] ++ toTag stack x ++ [Symb "."] ++ toTag stack y ++ [Symb ")"]
toTag _ _ = []

toTagNoBr::FStack->SExpr->[Tag]
toTagNoBr stack (Pair (x, Nil)) = toTag stack x
toTagNoBr stack (Pair (x, Pair y)) = toTag stack x ++ toTagNoBr stack (Pair y)
toTagNoBr stack (Pair (x, y)) = toTag stack x ++ [Symb "."] ++ toTag stack y
toTagNoBr _ _ = []                                         

varList::Int->[SExpr]->[Tag]
varList _ [] = [Symb ")"]
varList n (Atom _:ns) = Var n : varList (n + 1) ns
varList _ _ = []

replaceVars::FStack->[SExpr]->SExpr->[Tag]
replaceVars _ _ Nil = [Symb "NIL"]
replaceVars _ _ (IntNum i) = [Symb (show i)]
replaceVars _ _ (FloatNum f) = [Symb (show f)]
replaceVars _ _ (Str s) = [Symb s]
replaceVars _ _ (Pair (Atom "QUOTE", Pair (y, Nil))) = [Symb "(", Symb "QUOTE"] 
                                                           ++ quoteToTag y ++ [Symb ")"]
replaceVars stack names (Pair (Atom "EVAL", Pair 
                    (Pair (Atom "QUOTE", Pair (y, Nil)), Nil))) = [Symb "(", Symb "EVAL", 
                                                                  Symb "(", Symb "QUOTE"]
                                                                  ++ replaceVars stack names y
                                                                  ++ [Symb ")", Symb ")"]
replaceVars _ names (Atom x) | isVar (Atom x) names = [Var i]
                                 | otherwise = [Symb (map toUpper x)]
                                 where i = ind (Atom x) names
replaceVars stack names (Pair (Atom "COND", p)) = [Symb "(", Symb "COND"] ++ condToTag names stack params ++ [Symb ")"]
                                                  where params = funcParams p
replaceVars stack _ (Pair (Atom x, Nil)) | onStack stack x = [Symb "(", Func (funcNum stack x), Symb ")"]
                                         | otherwise = [Symb "(", Symb x, Symb ")"]
replaceVars stack names (Pair (Atom x, Pair y)) | onStack stack x = [Symb "(", Func (funcNum stack x)]
                                                                    ++ replaceNoBr stack names (Pair y)
                                                                    ++ [Symb ")"]
                                                | otherwise = [Symb "(", Symb x] ++
                                                              replaceNoBr stack names (Pair y)++[Symb ")"]
replaceVars stack names (Pair (x, Nil)) = [Symb "("] ++ replaceVars stack names x ++ [Symb ")"]
replaceVars stack names (Pair (x, Pair y)) = [Symb "("] ++ replaceVars stack names x 
                                             ++ replaceNoBr stack names (Pair y) ++ [Symb ")"]
replaceVars stack names (Pair (x, y)) = replaceVars stack names x ++ [Symb "."] ++ replaceVars stack names y
replaceVars _ _ _ = []

replaceNoBr::FStack->[SExpr]->SExpr->[Tag]
replaceNoBr stack names (Pair (x, Nil)) = replaceVars stack names x
replaceNoBr stack names (Pair (x, Pair y)) = replaceVars stack names x ++ replaceNoBr stack names (Pair y)
replaceNoBr stack names (Pair (x, y)) = replaceVars stack names x ++  [Symb "."]  ++ replaceVars stack names y
replaceNoBr _ _ _ = []

quoteToTag::SExpr->[Tag]
quoteToTag Nil = [Symb "NIL"]
quoteToTag (IntNum i) = [Symb (show i)]
quoteToTag (FloatNum f) = [Symb (show f)]
quoteToTag (Str s) = [Symb s]
quoteToTag (Atom a) = [Symb (map toUpper a)]
quoteToTag (Pair (x, Nil)) = [Symb "("] ++ quoteToTag x ++ [Symb ")"]
quoteToTag (Pair (x, Pair y)) = [Symb "("] ++ quoteToTag x ++ 
                                quoteNoBr (Pair y) ++ [Symb ")"]
quoteToTag (Pair (x, y)) = [Symb "("] ++ quoteToTag x ++ [Symb "."] 
                           ++ quoteToTag y ++ [Symb ")"]
quoteToTag _ = []

quoteNoBr::SExpr->[Tag]
quoteNoBr (Pair (x, Nil)) = quoteToTag x
quoteNoBr (Pair (x, Pair y)) = quoteToTag x ++ quoteNoBr (Pair y)
quoteNoBr (Pair (x, y)) = quoteToTag x ++  [Symb "."]  ++ quoteToTag y
quoteNoBr _ = []

condToTag::[SExpr]->FStack->[SExpr]->[Tag]
condToTag _ _ [] = []
condToTag names stack ((Pair (x, Nil)):s) | null names = [Symb "("] ++ toTag stack x ++ 
                                                         [Symb ")"] ++ condToTag names stack s
                                          | otherwise = [Symb "("] ++ replaceVars stack names x ++ 
                                                        [Symb ")"] ++ condToTag names stack s
condToTag names stack ((Pair (x, Pair (e, Nil))):s) | null names = [Symb "("] ++ toTag stack x ++ 
                                                                   toTag stack e ++ [Symb ")"] ++ 
                                                                   condToTag names stack s
                                                    | otherwise = [Symb "("] ++ replaceVars stack names x ++ 
                                                                  replaceVars stack names e ++ [Symb ")"] ++ 
                                                                  condToTag names stack s
condToTag _ _ _ = []

isVar::(Eq a)=>a->[a]->Bool
isVar _ [] = False
isVar a (x:xs) | x == a = True
               | otherwise = isVar a xs

ind::(Eq a)=>a->[a]->Int
ind _ [] = -1
ind a (x:xs) | x == a = 0
             | otherwise = 1 + ind a xs
