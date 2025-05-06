{-# OPTIONS_GHC -Wno-unused-top-binds #-}
module Lgraph (getNode, checkCurBr, addNodes, initGraph, allPaths) where

import Types(Lgraph(Lgraph), Path(Path), Node(Node), Bracket(Bracket))

initGraph::Int -> Lgraph
initGraph = Lgraph 1 []

addNode::Lgraph -> Node -> Lgraph
addNode (Lgraph s lst f) node = Lgraph s (node : lst) f

addNodes::Lgraph -> [Node] -> Lgraph
addNodes = foldl addNode

getNode::Int -> [Node] -> Node
getNode _ [] = Node 0 []
getNode from ((Node f lst) : ns) | from == f = Node f lst
                                 | otherwise = getNode from ns

checkBrackets::[Bracket] -> [Bracket] -> Bool
checkBrackets [] [] = True
checkBrackets [] _ = False
checkBrackets ((Bracket br1 i):brs1) [] = checkBrackets brs1 [Bracket br1 i]
checkBrackets ((Bracket br1 i):brs1) ((Bracket br2 j):brs2) | (br1==')' && br2=='(' || br1=='>' && br2=='<') 
                                                              && i == j = checkBrackets brs1 brs2
                                                            | otherwise = checkBrackets brs1 brs
                                                            where brs = Bracket br1 i : Bracket br2 j : brs2

checkCurBr::[Bracket]->[Bracket]->(Bool, [Bracket])
checkCurBr brs [] = (True, reverse brs)
checkCurBr [] (Bracket br i:brs) | br == '(' || br == '<' = (True, Bracket br i:brs)
                                 | otherwise = (False, [])
checkCurBr ((Bracket br1 i1):brs1) 
           ((Bracket br2 i2):brs2) | br1 == '(' && br2 == ')' && i1==i2 = checkCurBr brs1 brs2
                                   | br1 == '<' && br2 == '>' && i1==i2 = checkCurBr brs1 brs2
                                   | br2 == '(' || br2 == '<' = (True, reverse (Bracket br1 i1:brs1) ++ (Bracket br2 i2:brs2))
                                   | otherwise = (False, [])
--brs1 is reversed so we can take first elem
--Bool: true if needs both traces check ( and <, false if only the first trace (

addNext::Bool->[Path] -> Path -> Node -> [Path]
addNext _ ps _ (Node _ []) = ps
addNext flag ps (Path vs s trace1 trace2 brs1 brs2) 
        (Node from ((str, br1, br2, v):rest))
                       | flag && fst correct1 && fst correct2 
                       = addNext flag (ps ++ [Path (v:vs) (s++[str]) (trace1++br1) (trace2++br2) (snd correct1) (snd correct2)]) 
                                 (Path vs s trace1 trace2 brs1 brs2) 
                                 (Node from rest)
                       | not flag && fst correct1 = addNext flag (ps ++ [Path (v:vs) (s++[str]) (trace1++br1) (trace2++br2) (snd correct1) brs2]) 
                                 (Path vs s trace1 trace2 brs1 brs2) 
                                 (Node from rest)
                       | otherwise = addNext flag ps (Path vs s trace1 trace2 brs1 brs2) (Node from rest)
                       where correct1 = checkCurBr (reverse brs1) br1
                             correct2 = checkCurBr (reverse brs2) br2

bfs::Bool->[Path] -> [Node] -> Int -> [Path]
bfs _ [] _ _ = []
bfs flag ((Path (v:vs) str br1 br2 brs1 brs2) : ps) 
         nodes f | v == f && null brs1 && null brs2 = path : bfs flag ps nodes f
                 | v == f = bfs flag ps nodes f
                 | otherwise = bfs flag (addNext flag ps path (getNode v nodes)) nodes f
                 where path = Path (v:vs) str br1 br2 brs1 brs2
bfs _ ((Path [] _ _ _ _ _):_) _ _ = []

checkPath::Path -> Bool
checkPath (Path _ _ brs1 brs2 _ _) = checkBrackets brs1 [] && checkBrackets brs2 []

allPaths::Bool->Lgraph -> [Path]
--allPaths (Lgraph s nodes f) = filter checkPath (bfs [Path [s] [] [] [] [] []] nodes f)
allPaths flag (Lgraph s nodes f) = bfs flag [Path [s] [] [] [] [] []] nodes f

