{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module UI (launchUI) where

import Control.Lens
import Monomer
import TextShow
import Codec.Binary.UTF8.String (utf8Encode, encodeString, decodeString)
import Data.Text (Text, pack, tail, length, dropEnd, unpack) 
import Task
import Check
import Types
import Parser
import Eval
import Debug.Trace (trace)
import Distribution.Utils.String (encodeStringUtf8, decodeStringUtf8)
import Text.Show.Unicode


data AppModel = AppModel {
  _clickCount :: Int,
  _randomSeed :: Int,
  _newTask :: Bool,
  _typeTask :: Text,
  _taskField :: Bool,
  _task :: ([Tag], [Bracket], [Bracket]),
  _taskText :: Text,
  _solution :: Text,
  _checked :: Bool,
  _status :: Bool,
  _graph :: ([Node], Int, Int),
  _space :: Text,
  _interprete :: Bool,
  _input :: Text,
  _result :: Text,
  _manual :: Bool
} deriving (Eq, Show)

data AppEvent
  = AppInit
  | AppExit
  | AppIncrease
  | AppNewTask
  | AppChooseTask
  | AppCheck
  | AppRun
  | AppEval
  | AppManual
  deriving (Eq, Show)

makeLenses 'AppModel

buildUI
  :: WidgetEnv AppModel AppEvent
  -> AppModel
  -> WidgetNode AppModel AppEvent
buildUI _ model = widgetTree where
    widgetTree = hstack [
        vstack_ [childSpacing_ 20]
        [label "Меню" `styleBasic` [textCenter_ True],
         spacer_ [width 10],
         button "Новая задача" AppNewTask,
         button "Интерпретатор" AppRun,
         button "Справка" AppManual,
         button "Выход" AppExit] `styleBasic` [textCenter, padding 50],
         widgetIf (model & _newTask) widget1,
         widgetIf (model & _interprete) widget2,
         widgetIf (model & _manual) widget3
        ] `styleBasic` [padding 5]
    widget1 = vstack_ [childSpacing_ 10] [
              hstack_ [childSpacing_ 5] [
                dropdown typeTask ["случайная задача", "выражение", "условие", "функция", "рекурсия", "функционал"] createLabel createLabel,
                button "Получить задачу" AppChooseTask],
              widgetIf (model & _taskField) (vstack_ [childSpacing_ 10] [label "Условие:" `styleBasic` [],
                zstack [textArea_ space [readOnly_ True],
                       label_ (dropEnd 1 $ model^. taskText) [multiline]
                       `styleBasic` [textTop, paddingT 10, paddingL 10]],
                label "Решение:" `styleBasic` [],
                textArea_ solution [acceptTab],
                button "Проверить" AppCheck,
                widgetIf ((model & _checked) && (model & _status)) 
                                  (label "Верно" `styleBasic` [textColor green]),
                widgetIf ((model & _checked) && not (model & _status)) 
                                  (label "Неверно" `styleBasic` [textColor red])])
              ] `styleBasic` [padding 20]
    widget2 = vstack_ [childSpacing_ 10] [
                textArea_ input [acceptTab],
                button "Запустить" AppEval,
                label "Результат:",
                label_( model^. result) [multiline]
              ]
    widget3 = zstack [textArea_ space [readOnly_ True],
                       vscroll (label_ manText [multiline])
                       `styleBasic` [textTop, paddingT 10, paddingL 10]] 

createLabel::Text -> WidgetNode s e
createLabel t = label t `styleBasic` []

getTypeIdx::AppModel->Text->Int
getTypeIdx _ "выражение" = 0
getTypeIdx _ "условие" = 1
getTypeIdx _ "функция" = 2
getTypeIdx _ "рекурсия" = 3
getTypeIdx _ "функционал" = 4
getTypeIdx _ "" = 5
getTypeIdx model _ = chooseType (model^. randomSeed)


handleEvent
  :: WidgetEnv AppModel AppEvent
  -> WidgetNode AppModel AppEvent
  -> AppModel
  -> AppEvent
  -> [AppEventResponse AppModel AppEvent]
handleEvent _ _ model evt = case evt of
  AppInit -> []
  AppExit -> [exitApplication]
  AppIncrease -> [Model $ model & clickCount +~ 1]
  AppNewTask -> [Model $ model & newTask .~ True & randomSeed +~ 1
                               & typeTask .~ "Выберите тип задачи:"
                               & taskField .~ False & checked .~ False 
                               & interprete .~ False
                               & manual .~ False]
  AppChooseTask -> [Model $ model & taskField .~ True
                    & graph .~ g
                    & task .~ chosenT & randomSeed +~ 1
                    & taskText .~ pack (drop 1 (ushow $ textTags tags))
                    & solution .~ ""
                    & checked .~ False]
                    where t = getTypeIdx model (model^. typeTask)
                          s = chooseSubType (model^. randomSeed) t
                          g = getGraph t s
                          (nodes, end, _) = g
                          chosenT = chooseTask (getTasks (taskLgraph nodes end)) (model^. randomSeed)
                          (tags, _, _) = chosenT
  AppCheck -> [Model $ model & status .~ checkSolution (Lgraph 1 nodes f) solStart br1 br2 solTags
                             & checked .~ True]
              where (nodes, solStart, f) = model ^. graph
                    exprs = parseInput $ unpack $ model ^.solution
                    solTags = case exprs of
                                  Left _ -> []
                                  --Right res -> case evalExprs initFStack [] res of
                                                   --Left _ -> []
                                                   --Right _ -> parseResult exprs
                                  Right _ -> parseResult exprs
                    (_, br1, br2) = model ^. task
  AppRun -> [Model $ model & interprete .~ True & input .~ "" & newTask .~ False & result .~ "" & manual .~ False]
  AppEval -> [Model $ model & result .~ pack res]
             where parsed = parseInput (unpack $ model ^. input)
                   res = case parsed of
                             Left err -> show err
                             Right exprs -> case evalExprs initFStack [] exprs of
                                                 Left (Error err) -> err
                                                 Right results -> printList results
  AppManual -> [Model $ model & manual .~ True & interprete .~ False & input .~ "" & newTask .~ False & result .~ ""]
  

launchUI :: IO ()
launchUI = do
  startApp model handleEvent buildUI config
  where
    config = [
      appWindowTitle "Lisp-Practicum",
      appWindowIcon "src/assets/images/icon.png",
      appTheme lightTheme,
      appFontDef "Regular" "src/assets/fonts/Roboto-Regular.ttf",
      appInitEvent AppInit
      ]
    model = AppModel 0 1 False "Выберите тип задачи:" False ([], [], []) "" "" False False ([], 0, 0) "" False "" "" False


manText::Text
manText = pack ("Система автоматизированной генерации условий и проверки решений задач по Лиспу.\n\n" ++
                "Чтобы получить задачу, в меню нажмите на кнопку <<Новая задача>>, затем выберите ее тип и нажмите на <<Получить задачу>>.\n" ++
                "Затем введите в текстовом поле свое решение и нажмите <<Проверить>>. После проверки решение можно редактировать и проверять заново.\n" ++
                "Чтобы узнать результат работы программы на Лиспе, в меню перейдите в <<Интерпретатор>>. " ++
                "В поле ввода наберите текст и нажмите <<Запустить>>. Ниже будет вывод программы.\n" ++ 
                "Выход из системы доступен по соответсвующей кнопке в меню.\n\n\n" ++
                "Встроенные функции:\n\n" ++
                "Базовые:\n" ++
                "    car\n" ++
                "    cdr\n" ++
                "    cons\n" ++
                "    atom\n" ++
                "    eq\n" ++
                "    quote\n" ++
                "    eval\n" ++
                "    cond\n" ++
                "Другие:\n" ++
                "    defun\n" ++
                "    lambda\n" ++
                "    null\n" ++
                "    eql\n" ++
                "    =\n" ++
                "    +\n" ++
                "    -\n" ++
                "    *\n" ++
                "    /\n" ++
                "    <\n" ++
                "    >\n" ++
                "    <=\n" ++
                "    >=\n" ++
                "    %\n" ++
                "    sqrt\n" ++
                "    expt\n" ++
                "    not\n" ++
                "    and\n" ++
                "    or\n" ++
                "    numberp\n" ++
                "    symbolp\n" ++
                "    listp\n" ++
                "    member\n" ++
                "    append\n" ++
                "    list\n" ++
                "    setq\n" ++
                "    apply\n" ++
                "    funcall\n" ++
                "    mapcar\n" ++
                "    maplist\n" ++
                "    reduce\n" ++
                "    print\n")
