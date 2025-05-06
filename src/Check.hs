{-# OPTIONS_GHC -Wno-unused-imports #-}
module Check (checkSolution) where

import Debug.Trace
import Types(Lgraph(Lgraph), Node(Node), Bracket, Tag(Symb))
import Lgraph(getNode, checkCurBr)

--[Bracket] - соответствие пути-условию
--Int - начало пути решения
checkSolution::Lgraph->Int->[Bracket]->[Bracket]->[Tag]->Bool
checkSolution (Lgraph _ nodes f) n = next (getNode n nodes) nodes f

next::Node->[Node]->Int->[Bracket]->[Bracket]->[Tag]->Bool
next (Node from to) nodes f br1 br2 sol | from == f && null br1 && null br2 && null sol = True
                                        | from == f = False
                                        | success && n == f = next (Node n []) nodes f newbr1 newbr2 sol2
                                        | success = next node nodes f newbr1 newbr2 sol2
                                        | otherwise = False
                                        where (success, n, newbr1, newbr2, sol2) = findNextNode to br1 br2 sol
                                              node = getNode n nodes

findNextNode::[(Tag, [Bracket], [Bracket], Int)]->[Bracket]->[Bracket]->[Tag]->(Bool, Int, [Bracket], [Bracket], [Tag])
findNextNode [] _ _ _ = (False, -1, [], [], [])
findNextNode ((graph, br1, br2, n):rest) brs1 brs2 [] | fst correct1 && fst correct2 && graph == Symb "" = (True, n, snd correct1, snd correct2, [])
                                                      | otherwise = findNextNode rest brs1 brs2 []
                                                      where correct1 = checkCurBr (reverse brs1) br1
                                                            correct2 = checkCurBr (reverse brs2) br2
findNextNode ((graph, br1, br2, n):rest) 
             brs1 brs2 (sol:tags) | fst correct1 && fst correct2 && graph == sol 
                                    = (True, n, snd correct1, snd correct2, tags)
                                  | fst correct1 && fst correct2 && graph == Symb ""
                                    = (True, n, snd correct1, snd correct2, sol:tags)
                                  | otherwise = findNextNode rest brs1 brs2 (sol:tags)
                                  where correct1 = checkCurBr (reverse brs1) br1
                                        correct2 = checkCurBr (reverse brs2) br2