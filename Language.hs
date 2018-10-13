{-# LANGUAGE InstanceSigs #-}
{-
pCommon尚不能处理有括号的情况，并且获取运算符时，没考虑优先级
pCase存在问题
pLet的letrec存在问题

存在作用域问题
-}

{-2018/10/12问题修复，主要是，对oneWord进行修改
-oneWord = do r <- list (alpha' <|> digit')
              spaces
              return
+oneWord = tok $ list (alpha' <|> digit')
似的oneWord能获取空格间的一个字符串-}

module Language where

import CoreParser

data Expr a
  = EVar Name
  | ENum Int
  | EConstr Int Int
  | EAp (Expr a) (Expr a)   
  | ELet              --let的表达式
    IsRec             --bool类  (True 表示recursive，目的是区分递归和非递归的)
    [(a, Expr a)]     --定义
    (Expr a)          --body of let
  | ECase             --case　表达式
    (Expr a)
    [Alter a]         --可选项
  | ELam [a] (Expr a)   --lambda表达式

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
  fmap _ (EVar ne) = EVar ne
  fmap _ (ENum n) = ENum n
  fmap _ (EConstr n1 n2) = EConstr n1  n2
  fmap f (EAp e1 e2) = EAp (f <$> e1) (f <$> e2)

  fmap f (ELet b defn e) = ELet b defn' (f <$> e)
    where
      defn' = (\(a, e1) -> (f a, f <$> e1)) <$> defn

  fmap f (ECase e atrs) = ECase (f <$> e) atrs'
    where
      atrs' = (\(n, as, e) -> (n, f <$> as, f <$> e)) <$> atrs

  fmap f (ELam as e) = ELam (f <$> as) (f <$> e)

{-
instance Monad Expr where
  (>>=) :: Expr a -> (a -> Expr b) -> Expr b
  (>>=) (EVar ne) _ = EVar ne
  (>>=) (ENum n) _ = ENum n
  (>>=) (EConstr n1 n2) = EConstr n1 n2

  (>>=) (EAp e1 e2) f_e = EAp (e1 >>= f_e) (e2 >>= f_e)
  (>>=) (ELet b defn e) f_e = ELet b defn' (e >>= f_e)
    where
      defn' = (\(ne, e) -> (ne, e >>= f_e)) <$> defn
-}

recursive, nonRecursive :: IsRec
recursive = True
nonRecursive = False

data Iseq
  = INil
  | IStr String
  | IAppend Iseq Iseq
  | IIndent Iseq
  | INewline

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

iNum :: Int -> Iseq
iNum = iStr . show

iFWNum :: Int -> Int -> Iseq
iFWNum n w = iStr $ (rSpaces (w - length digits)) ++ digits
  where
    digits = show n

iLayn :: [Iseq] -> Iseq   --列表每一行以数字开头表示行数
iLayn seqs = iConcat (map lay_item (zip [1..] seqs))
  where
    lay_item (n,seq)
      = iConcat [iFWNum 4 n, iStr ") ", iIndent seq, iNewline]

infixOperators = ["+","-","*","/"]

--取绑定的名称
bindersOf :: [(a, b)] -> [a]
bindersOf defns = [name | (name, _) <- defns]

--取右值
rhssOf :: [(a,b)] -> [b]
rhssOf defns = [rhs | (_, rhs) <- defns]


--判断基本表达式
isAtomicExpr :: Expr a -> Bool
isAtomicExpr (EVar _) = True
isAtomicExpr (ENum _) = True
isAtomicExpr _ = False


preludeDefs :: CoreProgram
preludeDefs = [ ("I", ["x"], EVar "x"),
                ("K", ["x", "y"], EVar "x"),
                ("K1", ["x", "y"], EVar "y"),
                ("S", ["f", "g", "x"], EAp (EAp (EVar "f") (EVar "x"))
                                           (EAp (EVar "g") (EVar "x"))),
                ("compose", ["f","g","x"], EAp (EVar "f")
                                               (EAp (EVar "g") (EVar "x"))),
                ("twice", ["f"], EAp (EAp (EVar "compose") (EVar "f")) (EVar "f"))]


--打印表达式
pprExpr :: CoreExpr -> Iseq
pprExpr (EVar v) = iStr v
pprExpr (EAp e1 e2)
  | isInfix e1 = iConcat [pprExpr e2, (iStr " "), pprExpr e1]              --打印类似与+,-,*,/之类的中序运算符
  | otherwise = iConcat [(pprExpr e1), (iStr " "), (pprAExppr e2)]
    where
      isInfix (EVar op) = elem op infixOperators
      isInfix _ = False


--let或letrec的表达
pprExpr (ELet isrec defns expr)
 = iConcat [ iStr keyword, iNewline,
             iStr " ", (pprDefns defns), iNewline,
             iStr "in ", pprExpr expr]
   where
     keyword | isrec = "letrec"
             | otherwise = "let"
--打印case
pprExpr (ECase expr alters)
  = iConcat [iStr "case ", iIndent (pprExpr expr), iStr " of", iNewline, (chng alters)]
    where
      chng tgs = foldr (\x xs -> iConcat [pprAlter x, iNewline, xs]) INil tgs
--lambda表达式
--lambda (x y z..) ...
pprExpr (ELam eles expr)
  = iConcat [iStr "lambda ",iStr (foldl1 (++) eles), iStr "->", (pprExpr expr)]


--打印函数定义
--type Alter a = (Int, [a], Expr a)
--type CoreAlt = Alter Name
pprAlter :: CoreAlt -> Iseq
pprAlter (i, as, expr) = iConcat [(iStr $ (show i ++ ": ")), (chng as), iStr " -> ", (pprExpr expr)]
  where
    chng tgs = foldr (\x xs -> iConcat [(iStr x), xs]) INil tgs

pprDefns :: [(Name, CoreExpr)] -> Iseq
pprDefns defns = iInterleave seq (map pprDefn defns)
  where
    seq = iConcat [iStr ";", iNewline]

pprDefn :: (Name, CoreExpr) -> Iseq
pprDefn (name, expr)
  = iConcat [iIndent (iStr name), iStr "=", iIndent (pprExpr expr)]

pprAExppr :: CoreExpr -> Iseq
pprAExppr e
  | isAtomicExpr e = pprExpr e
  | otherwise = iConcat [iStr "(", pprExpr e, iStr ")"]

--type Program a = [ScDefn a]
--type CoreProgram = Program Name
pprProgram :: CoreProgram -> Iseq
pprProgram p = foldr process INil p
  where
    process x xs = (pprScDefn x) `iAppend` xs

{-
type ScDefn a = (Name, [a], Expr a)   --supercombinator definition
type CoreScDefn = ScDefn Name
-}
pprScDefn :: CoreScDefn -> Iseq
pprScDefn (name, as, expr) = iConcat [(iStr name), chng as, (pprExpr expr)]
  where
    chng as = foldr (\x xs -> (iStr x) `iAppend` xs) INil as


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
  = '\n' : (replicate indent ' ') ++ (flatten indent prs)

flatten col ((IIndent seq, _):prs)
  = flatten col ((seq, col):prs)

flatten col ((IStr s, indent):prs)
  | s == "\n" = flatten col ((INewline, indent):prs)
  | otherwise = s ++ (flatten indent prs)

flatten col ((IAppend seq1 seq2, indent):prs)
  = flatten col ((seq1,indent):(seq2,indent):prs)

flatten _ _ = []
  
iDisplay seq = flatten 0 [(seq, 0)]

--解析程序
pVar :: Parser CoreExpr
pVar = do w <- oneWord
          return $ EVar w


pExpr :: Parser CoreExpr
pExpr = pCase <|> (pLet True) <|> (pLet False) <|> pLam <|> pCommon <|> pVar

pCase :: Parser CoreExpr
pCase = liftA4 mk_case (string1 "case") getExpr (stringTok "of\n") pAlters
  where
    mk_case _ e _ as = ECase e as
    getExpr = pExpr <|> (betweenWithc pExpr '(' ')')

    pAlters :: Parser [CoreAlt]
    pAlters = do as <- sepByc1 pAlter '\n'
                 return $ zipWith (\(_, vs, e) n -> (n, vs, e)) as [1..]


--默认tag为0，后期再修改
pAlter :: Parser CoreAlt
pAlter = do var <- oneWord
            string1 "->"
            expr <- pExpr
            return $ (0, [var], expr)


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
             makeIt (pure (\e -> EAp (EAp (EVar [c]) (EVar v)) e))
  where
    makeIt mrs = do v <- list (letter <|> digit)
                    c <- symbol
                    let new_mrs = liftA (makeAp c v)mrs in
                      makeIt new_mrs
                    <|> do v <- list (letter <|> digit)
                           rs <- mrs
                           return $ rs (EVar v)

    makeAp c v f = \e' -> EAp (EAp (EVar [c]) (f $ EVar v)) e'

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
{-
pExpr1 :: Parser CoreExpr
pExpr1 = liftA2 assembleOp pExpr2 pExpr1c

pExpr1c :: Parser PartialExpr
pExpr1c = (liftA2 Op (charTok '|') pExpr1) <|> (pure NoOp)

pExpr2 :: Parser CoreExpr
pExpr2 = liftA2 assembleOp pExpr3 pExpr2c

pExpr2c :: Parser PartialExpr
pExpr2c = (liftA2 Op (charTok '&') pExpr1) <|> (pure NoOp)

pExpr3 :: Parser CoreExpr
pExpr3 = liftA2 assembleOp pExpr4 pExpr3c

pExpr3c :: Parser CoreExpr
pExpr3c = (liftA2 assembleOp pRelop pExpr4) <|> (pure NoOp)
-}
pRelop :: Parser String
pRelop = foldr (\x xs-> (string1 x) <|> xs) (string1 "") ["<=", ">=", "==","<", ">"]


assembleOp :: CoreExpr -> PartialExpr -> CoreExpr
assembleOp e1 (Op op e2) = EAp (EAp (EVar op) e1) e2
assembleOp e1 _ = e1


--auxilliary function
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

