{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ExistentialQuantification #-}

module Language where

import CoreParser

data Expr a
  = A Atom
  | EAp (Expr a) (Expr a)   
  | ELet              --let的表达式
    IsRec             --bool类  (True 表示recursive，目的是区分递归和非递归的)
    [(a, Expr a)]     --定义
    (Expr a)          --body of let
  | ECase             --case　表达式
    (Expr a)
    [Alter a]         --可选项
  | ELam [a] (Expr a)   --lambda表达式


data Atom
  = ENum CN
  | EConstr Int Int
  | EVar Name
  | Prn CoreExpr    --包含在括号内的表达式

data CN = I Int | F Double
  deriving (Show, Eq)

instance Ord CN where
  (>) (I x) (I y) = x > y
  (>) (I x) (F y) = fromIntegral x > y
  (>) (F x) (F y) = x > y
  (>) (F x) (I y) = x > fromIntegral y

  (<) = flip (>)

  (>=) (I x) (I y) = x >= y
  (>=) (I x) (F y) = fromIntegral x >= y
  (>=) (F x) (F y) = x >= y
  (>=) (F x) (I y) = x >= fromIntegral y
  
  (<=) = flip (>=)

instance Num CN where
  (+) (I x) (I y) = I (x + y)
  (+) (I x) (F y) = F (fromIntegral x + y)
  (+) (F x) (F y) = F (x + y)
  (+) (F x) (I y) = F (fromIntegral y + x)

  (-) (I x) (I y) = I (x - y)
  (-) (I x) (F y) = F (fromIntegral x - y)
  (-) (F x) (F y) = F (x - y)
  (-) (F x) (I y) = F (x - fromIntegral y)

  (*) (I x) (I y) = I (x * y)
  (*) (I x) (F y) = F (fromIntegral x * y)
  (*) (F x) (F y) = F (x * y)
  (*) (F x) (I y) = F (x * fromIntegral y)

  abs (I x) = I $ abs x
  abs (F x) = F $ abs x
  
  negate (I x) = I $ negate x
  negate (F x) = F $ negate x

  signum (I x)
    | x > 0 = (I 1)
    | x < 0 = (I (-1))
    | otherwise = (I x)
  signum (F x)
    | x > 0 = (F 1.0)
    | x < 0 = (F (-1.0))
    | otherwise = F x

  fromInteger n = I (fromIntegral n)


type CoreExpr = Expr Name   --一般表达式
type Name = String          --变量名
type IsRec = Bool
type Alter a = (Int, [a], Expr a)
type CoreAlt = Alter Name
type Program a = [ScDefn a]
type CoreProgram = Program Name
type ScDefn a = (Name, [a], Expr a)   --supercombinator definition
type CoreScDefn = ScDefn Name
type Defn a = (a, Expr a)
type CoreDefn = Defn Name

data PartialExpr = NoOp | Op Name CoreExpr     --Op 操作符名称 表达式


instance Functor Expr where
  fmap :: (a -> b) -> Expr a -> Expr b
  fmap _ (A (EVar ne)) = A (EVar ne)
  fmap _ (A (ENum n)) = A (ENum n)
  fmap _ (A (EConstr n1 n2)) = A (EConstr n1  n2)
  fmap f (EAp e1 e2) = EAp (f <$> e1) (f <$> e2)

  fmap f (ELet b defn e) = ELet b defn' (f <$> e)
    where
      defn' = (\(a, e1) -> (f a, f <$> e1)) <$> defn

  fmap f (ECase e atrs) = ECase (f <$> e) atrs'
    where
      atrs' = (\(n, as, e) -> (n, f <$> as, f <$> e)) <$> atrs

  fmap f (ELam as e) = ELam (f <$> as) (f <$> e)

recursive, nonRecursive :: IsRec
recursive = True
nonRecursive = False

data Iseq
  = INil
  | IStr String
  | IAppend Iseq Iseq
  | IIndent Iseq
  | INewline
  deriving Eq

iNil :: Iseq
iNil = INil

iStr :: String -> Iseq
iStr str = IStr str

iAppend :: Iseq -> Iseq -> Iseq
iAppend seq1 INil = seq1
iAppend INil seq2 = seq2
iAppend seq1 seq2 = IAppend seq1 seq2

iIndent seq = IIndent seq
iNewline = INewline
iSpace n = iStr $ rSpaces n

iNum :: CN  -> Iseq
iNum (I n) = iStr $ show n
iNum (F n) = iStr $ show n


iFWNum :: Int -> Int -> Iseq
iFWNum n w = iStr $ (rSpaces (w - length digits)) ++ digits
  where
    digits = show n

iLayn :: [Iseq] -> Iseq   --列表每一行以数字开头表示行数
iLayn seqs = foldr makeIt iNil (zip [1..] seqs)
  where
    makeIt (n,seq) rs
      | rs == iNil = iConcat [iFWNum n 4, iStr ") ", iIndent seq, rs]
      | otherwise = iConcat [iFWNum n 4, iStr ") ", iIndent seq, iNewline, rs]
      
--取绑定的名称
bindersOf :: [(a, b)] -> [a]
bindersOf defns = [name | (name, _) <- defns]

--取右值
rhssOf :: [(a,b)] -> [b]
rhssOf defns = [rhs | (_, rhs) <- defns]


--判断基本表达式
isAtomicExpr :: Expr a -> Bool
isAtomicExpr (A _) = True
isAtomicExpr _ = False


preludeDefs :: CoreProgram
preludeDefs = [ ("I", ["x"], A (EVar "x")),
                ("K", ["x", "y"],A (EVar "x")),
                ("K1", ["x", "y"], A (EVar "y")),
                ("S", ["f", "g", "x"], EAp (EAp (A (EVar "f")) (A (EVar "x")))
                                           (EAp (A (EVar "g")) (A (EVar "x")))),
                ("compose", ["f","g","x"], EAp (A (EVar "f"))
                                               (EAp (A (EVar "g")) (A (EVar "x")))),
                ("twice", ["f"], EAp (EAp (A (EVar "compose")) (A (EVar "f"))) (A (EVar "f")))]


--打印表达式
pprExpr :: CoreExpr -> Iseq
pprExpr e@(A ae) = pprAExpr e
pprExpr (EAp e1 e2)
  | isBinop e1 = iConcat [pprExpr e2, (iStr " "), pprExpr e1]
  | otherwise = iConcat [pprExpr e1, (iStr " "), pprExpr e2]              --打印类似与+,-,*,/之类的中序运算符

--let或letrec的表达
pprExpr (ELet isrec defns expr)
 = iConcat [ iStr keyword, iNewline,
             (iSpace 2), iIndent (pprDefns defns), iNewline,
             iStr "in ", pprExpr expr]
   where
     keyword | isrec = "letrec"
             | otherwise = "let"
--打印case
pprExpr (ECase expr alters)
  = iConcat [iStr "case ", iIndent (pprExpr expr), iStr " of", iNewline, (chng alters)]
    where
      chng tgs = foldr (\x xs -> iConcat [iIndent (pprAlter x), iNewline, xs]) INil tgs
--lambda表达式
--lambda (x y z..) ...
pprExpr (ELam eles expr)
  = iConcat [iStr "lambda ",pprArgs eles, iStr " -> ",pprExpr expr]


--打印函数定义
--type Alter a = (Int, [a], Expr a)
--type CoreAlt = Alter Name
pprAlter :: CoreAlt -> Iseq
pprAlter (i, as, expr) = iConcat [iStr (show "<" ++ show i ++ ">: "), (chng as), iStr " -> ", iIndent(pprExpr expr)]
  where
    chng tgs = foldr (\x xs -> iConcat [iStr x, iStr " ",xs]) INil tgs

pprDefns :: [(Name, CoreExpr)] -> Iseq
pprDefns defns = foldr makeIt iNil defns
  where
    makeIt x rs = if rs == iNil
                     then iConcat [pprDefn x, rs]
                     else iConcat [pprDefn x, iNewline, rs]

pprDefn :: (Name, CoreExpr) -> Iseq
pprDefn (name, expr)
  = iConcat [iIndent (iStr name), iStr " = ", iIndent (pprExpr expr)]

pprAExpr :: CoreExpr -> Iseq
pprAExpr (A (EVar v)) = iStr v
pprAExpr (A (ENum cn)) = pprCN cn
pprAExpr (A (Prn e)) = iConcat [iStr "(", (pprExpr e), iStr ")"]
pprAExpr (A (EConstr t a)) = iConcat [iStr "Pack {", iNum (I t), iStr ",", iNum (I a), iStr "}"]

pprCN :: CN -> Iseq
pprCN (I n) = iStr $ show n
pprCN (F n) = iStr $ show n

pprArgs :: [String] -> Iseq
pprArgs args = foldr (\x rs -> iConcat [iStr x, iSpace 1, rs]) iNil args
{-
pprProgram prog = iInterleave (iAppend (iStr " ;") iNewline) (map pprSc prog)
-}

--type Program a = [ScDefn a]
--type CoreProgram = Program Name
pprProgram :: CoreProgram -> Iseq
pprProgram p = foldr process INil p
  where
    process x xs = iConcat [pprScDefn x, iStr "; ", iNewline, xs]

{-
type ScDefn a = (Name, [a], Expr a)   --supercombinator definition
type CoreScDefn = ScDefn Name
-}
pprScDefn :: CoreScDefn -> Iseq
pprScDefn (name, as, expr) = iConcat [iStr name, iSpace 1 ,pprArgs as, iStr "= ", iIndent (pprExpr expr)]
--  where
--    chng as = foldr (\x xs -> (iStr x) `iAppend` xs) INil as

mkMultiAp :: Int -> CoreExpr -> CoreExpr -> CoreExpr
mkMultiAp n e1 e2 = foldl (EAp) e1 (take n e2s_i)
  where
    e2s_i = e2 : e2s_i

iConcat :: [Iseq] -> Iseq
iConcat tgs = foldl1 iAppend tgs

iInterleave :: Iseq -> [Iseq] -> Iseq
iInterleave iseq tgs = foldl1 (\x y -> iConcat [x, iseq, y]) tgs


--转换Iseq为String
flatten :: Int -> [(Iseq, Int)] -> String
flatten _ ((INewline, indent):prs)
  = '\n' : (rSpaces indent) ++ (flatten indent prs)

flatten col ((IIndent seq, _):prs)
  = flatten col ((seq, col):prs)

flatten col ((IStr s, indent):prs)
--  | s == "\n" = flatten col ((INewline, indent):prs)
  = s ++ flatten (col + length s) prs

flatten col ((IAppend seq1 seq2, indent):prs)
  = flatten col ((seq1,indent):(seq2,indent):prs)

flatten _ _ = []
  
iDisplay :: Iseq -> String
iDisplay seq = flatten 0 [(seq, 0)]

--解析程序
pProgram :: Parser CoreProgram
pProgram = sepByc1 pSc ';'


pSc :: Parser CoreScDefn
pSc = liftA4 mk_sc oneWord (foldParser oneWord) (tok $ string1 "=") pExpr
  where
    mk_sc name args _ body = (name,args,body)

pVar :: Parser CoreExpr
pVar = do w <- oneWord
          if w `elem` keyWords1
          then unexpectedStringParser w
          else return $ A (EVar w)


pExpr :: Parser CoreExpr
pExpr = (pLet True) <|> (pLet False) <|> pCase <|> pLam <|> pExpr1

pCase :: Parser CoreExpr
pCase = liftA4 mk_case (string1 "case") pExpr (stringTok "of\n") pAlters
  where
    mk_case _ e _ as = ECase e as

    pAlters :: Parser [CoreAlt]
    pAlters = do as <- sepByc1 pAlter '\n'
                 return $ zipWith (\(_, vs, e) n -> (n, vs, e)) as [1..]

--默认tag为0，后期再修改
pAlter :: Parser CoreAlt
pAlter = do vars <- list oneWord
            string1 "->"
            expr <- pExpr
            return $ (0, vars, expr)


pLet :: Bool -> Parser CoreExpr
pLet isRec = if not isRec
                then liftA4 mk_let (string1 "let") pEq_Expr (string1 "in") pExpr
                else liftA4 mk_letrec (string1 "letrec") (sepByc1 pEq_Expr '\n') (string1 "in") pExpr
  where
    mk_let _ eqe _ e = ELet False [eqe] e
    mk_letrec _ eqes _ e = ELet True eqes e

    
pEq_Expr :: Parser CoreDefn
pEq_Expr = do v <- oneWord
              charTok '='
              e <- pExpr
              return (v, e)


pLam :: Parser CoreExpr
pLam = liftA4 mk_lambda (string1 "\\") (list oneWord) (string1 "->") pExpr
  where
    mk_lambda _ es _ e = ELam es e


pCommon :: Parser CoreExpr
pCommon = do v <- oneWord
             c <- symbol
             makeIt (pure (\e -> EAp (EAp (A (EVar [c])) (A (EVar v))) e))
  where
    makeIt mrs = do v <- list (letter <|> digit)
                    c <- symbol
                    let new_mrs = liftA (makeAp c v)mrs in
                      makeIt new_mrs
                    <|> do v <- list (letter <|> digit)
                           rs <- mrs
                           return $ rs (A (EVar v))

    makeAp c v f = \e' -> EAp (EAp (A (EVar [c])) (f $ (A (EVar v)))) e'

{-expr -> let defns in expr
        | letrec dfns in expr
        | case expr of alts
        | \ var1 ... varn . expr
        | expr1

  expr1 -> expr2 | expr1
         | expr2
  expr2 -> expr3 & expr2
         | expr3
  expr3 -> expr4 relop expr4
         | expr4
  expr4 -> expr5 + expr4
         | expr5 - expr5
         | expr5
  expr5 -> expr6 * expr5
         | expr6 / expr6
         | expr6
  expr6 -> aexpr1 ... aexprn
-}

pExpr1 :: Parser CoreExpr
pExpr1 = (liftA2 assembleOp pExpr2 pExpr1c) <|> pExpr2

pExpr1c :: Parser PartialExpr
pExpr1c = (liftA2 Op (tok $ string1 "|") pExpr1) <|> (pure NoOp)

pExpr2 :: Parser CoreExpr
pExpr2 = (liftA2 assembleOp pExpr3 pExpr2c) <|> pExpr3

pExpr2c :: Parser PartialExpr
pExpr2c = (liftA2 Op (tok $ string1 "&") pExpr1) <|> (pure NoOp)

pExpr3 :: Parser CoreExpr
pExpr3 = (liftA2 assembleOp pExpr4 pExpr3c) <|> pExpr4

pExpr3c :: Parser PartialExpr
pExpr3c = (liftA2 Op pRelop pExpr4) <|> (pure NoOp)

pRelop :: Parser String
pRelop = foldr (\x xs-> (tok $ string1 x) <|> xs) (string1 ">") ["<=", ">=", "==", "/=", "<"]

pExpr4 :: Parser CoreExpr
pExpr4 = (liftA2 assembleOp pExpr5 pExpr4c) <|> pExpr5

pExpr4c :: Parser PartialExpr
pExpr4c = (liftA2 Op (tok $ string1 "+") pExpr4) <|>
          (liftA2 Op (tok $ string1 "-") pExpr5) <|> (pure NoOp)
          

pExpr5 :: Parser CoreExpr
pExpr5 = (liftA2 assembleOp pExpr6 pExpr5c) <|> pExpr6

pExpr5c :: Parser PartialExpr
pExpr5c = (liftA2 Op (tok $ string1 "*") pExpr5) <|>
          (liftA2 Op (tok $ string1 "/") pExpr5) <|>
          (liftA2 Op (tok $ string1 "`div`") pExpr5) <|> (pure NoOp)

pExpr6 :: Parser CoreExpr
pExpr6 = do i <- pItem
            makeIt $ pure (\x -> EAp i x)
            <|> do i <- pItem
                   return i
  where
    pItem = pNum1 <|> pVar <|> pPack <|> pPrnedExpr 
    makeIt mrs = do i <- pItem
                    let new_mrs = liftA (\f -> (\x -> EAp (f i) x)) mrs in
                      makeIt new_mrs
                    <|> do i <- pItem
                           rs <- mrs
                           return $ rs i

pPrnedExpr :: Parser CoreExpr
pPrnedExpr = do e <- betweenWithc pExpr '(' ')'
                return $ A (Prn e)

assembleOp :: CoreExpr -> PartialExpr -> CoreExpr
assembleOp e1 (Op op e2) = EAp (EAp (A (EVar op)) e1) e2
assembleOp e1 _ = e1


--auxilliary function
binOperators :: [String]
binOperators = ["+","-","*","/","<","<=",">",">=","==","/=","&","|"]

isBinop :: CoreExpr -> Bool
isBinop (A (EVar op)) = op `elem` binOperators
isBinop _ = False


oneWord :: Parser String
oneWord = tok $ list1 (alpha' <|> digit')

rSpaces :: Int -> String
rSpaces n
  | n > 0 = replicate n ' '
  | otherwise = ""


pExpr2pString :: Parser CoreExpr -> Parser String
pExpr2pString pe = do e <- pe
                      return $ iDisplay $ pprExpr e

pDefn2pString :: Parser CoreDefn -> Parser String
pDefn2pString pd = pd >>= (return . iDisplay . pprDefn)

pScDefn2pString :: Parser CoreScDefn -> Parser String
pScDefn2pString pscd = pscd >>= (return . iDisplay . pprScDefn)

pProgram2pString :: Parser CoreProgram -> Parser String
pProgram2pString pp = pp >>= (return . iDisplay . pprProgram)

pNum1 :: Parser CoreExpr
pNum1 = do n <- pInt
           f <- pDouble
           let f' = fromIntegral n + 0.0 in
             return $ A (ENum (F (f' + f)))
           <|> do n <- pInt
                  return $ A (ENum (I n))


pInt :: Parser Int
pInt = do d <- tok (list1 digit')
          return $ (read d :: Int)


pFloat :: Parser Float
pFloat = do p <- is '.'
            ds <- tok (list1 digit')
            let f = (read ('0':p:ds) :: Float) in
              return f


pDouble :: Parser Double
pDouble = do p <- is '.'
             ds <- tok (list1 digit')
             let f = (read ('0':p:ds) :: Double) in
               return f

pPack :: Parser CoreExpr
pPack = do string1 "Pack"
           (tag,arity) <- betweenWithc getIt '{' '}'
           return $ A $ EConstr tag arity
  where
    getIt = do t <- pInt
               charTok ','
               a <- pInt
               return (t,a)


pUDInfix :: Parser String
pUDInfix = betweenWithc oneWord '`' '`'
              
keyWords1 :: [String]
keyWords1 = ["case","else","in","if","letrec","let","of","Pack"]


countEAp :: (Expr a) -> Int
countEAp (EAp e1 e2)
  | isAtomicExpr e1 = 1
  | otherwise = 1 + countEAp e1
