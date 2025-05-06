module Types (SExpr(Atom, IntNum, FloatNum, Str, Nil, Pair, None),
              Error(Error),
              VarValue(Init, Val),
              LambdaList(LambdaList),
              Callable(BaseCall, UserCall, UserVar),
              FStack(Empty, Cons),
              Tag(Symb, Func, Var),
              Lgraph(Lgraph),
              Node(Node),
              Bracket(Bracket),
              Path(Path)
             ) where

data SExpr = Atom String | IntNum Int | FloatNum Double | Str String | 
             Nil | Pair (SExpr, SExpr) | None deriving (Eq, Show)
data VarValue = Init | Val SExpr
newtype LambdaList = LambdaList [(String, VarValue)]
data Callable = BaseCall (String, FStack->[SExpr]->Either Error (FStack, SExpr)) | 
                UserCall (String, Int, LambdaList, SExpr) | -- Int - number of user function
                UserVar (String, SExpr)
data FStack = Empty | Cons Callable FStack
newtype Error = Error String deriving Show

data Bracket = Bracket Char Int deriving (Eq, Show) -- Bracket Type Index
data Node = Node Int [(Tag, [Bracket], [Bracket], Int)] deriving (Eq, Show)
data Lgraph = Lgraph Int [Node] Int -- Lgraph Start [Node] Finish
data Path = Path [Int] [Tag] [Bracket] [Bracket] [Bracket] [Bracket] deriving (Show)

data Tag = Symb String | Func Int | Var Int deriving (Show)

instance Eq Tag where
        (==) (Symb s1) (Symb s2) = s1 == s2
        (==) (Func f1) (Func f2) = f1 == f2
        (==) (Var v1) (Var v2) = v1 == v2
        (==) _ _ = False
