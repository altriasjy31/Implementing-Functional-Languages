{-# LANGUAGE ExistentialQuantification #-}
--NData的问题未解决
--if没有起作用

module Template03 where

import CoreParser
import Language

import qualified Data.Map.Lazy as Mz
import qualified Data.Map.Internal.Debug as Mid


type Addr = Int
type TiStack = [Addr]

type TiDump = [TiStack]

--Heap的组成 (size, [free address], Mz.Map address Node)
--Node的的组成 NAp Addr Addr | NSupercomb Name [Name] CoreExpr | NNum a

data Node = NAp Addr Addr
          | NSupercomb Name [Name] CoreExpr
          | NInd Addr
          | NPrim Name Primitive
          | NNum CN
          | NData Int [Addr]


data Primitive =
  Neg | Abs
  | Add | Sub  | Mul | DivI | DivF
  | PrimConstr Int Int
  | If | Then | Else
  deriving Eq


--data Arith = forall a. Num a => AnyArith (a -> a -> a)

type Heap a = (Int, [Addr], Mz.Map Addr a)
type TiHeap = Heap Node

--包含了全部的函数名以及对应的地址
type TiGlobals = Mz.Map Name Addr

--统计结果
type TiStatics = Int

type TiState = (TiStack, TiDump, TiHeap, TiGlobals, TiStatics)

runProg :: String -> IO ()
runProg file = case parse pProgram file of
                 Result remind result -> putStrLn $ showResults $ eval $ compile result
                 _ -> error "There is someting error"


initialTiDump :: TiDump
initialTiDump = []

tiStatInitial :: TiStatics
tiStatInitial = 0

tiStatIncSteps :: TiStatics -> TiStatics
tiStatIncSteps s = s + 1

tiStatGetSteps :: TiStatics -> Int
tiStatGetSteps s = s


applyTostatics :: (TiStatics -> TiStatics) -> TiState -> TiState
applyTostatics stats_fun (stack, dump, heap, sc_defs, stats)
  = (stack,dump,heap,sc_defs, stats_fun stats)


compile :: CoreProgram -> TiState
compile program = (initial_stack, initialTiDump, initial_heap, globals, tiStatInitial)
  where
    initial_stack = aLookup (error "\"main\" function doesn't exist") "main" (\x -> [x]) globals

    extraPreludeDefs = []
    sc_defs = preludeDefs ++ extraPreludeDefs ++ program
    (initial_heap, globals) = buildInitialHeap sc_defs

buildInitialHeap :: [CoreScDefn] -> (TiHeap, TiGlobals)
buildInitialHeap sc_defs = (heap2, addrs)
  where
    (heap1, sc_addrs) = foldl (makeIt allocateSc) (hInitial, Mz.empty::TiGlobals) sc_defs
    (heap2, addrs) = foldl (makeIt allocatePrim) (heap1,sc_addrs) primitives

    makeIt f (h, gb) item = let (h', (name,addr)) = f h item in
                              (h', Mz.insert name addr gb)

allocateSc :: TiHeap -> CoreScDefn -> (TiHeap, (Name, Addr))
allocateSc heap (name, args, body) = (heap', (name, addr))
  where
    (heap', addr) = hAlloc (NSupercomb name args body) heap

allocatePrim :: TiHeap -> (Name, Primitive) -> (TiHeap, (Name,Addr))
allocatePrim heap (name, prim)
  = (heap', (name,addr))
    where
      (heap', addr) = hAlloc (NPrim name prim) heap

--可不可以在这里修改，改为入栈一样的操作，使得最后的结果处于栈顶
eval :: TiState -> [TiState]
eval state = state:rest_states
  where
    rest_states
      | isFinal state = []
      | otherwise = eval next_state

    next_state = doAdmin $ step state

    doAdmin :: TiState -> TiState
    doAdmin state = applyTostatics tiStatIncSteps state

{-
相比于上面，这并不是一个好的定义方式
但，尚不清楚理由
eval :: TiState -> [TiState]
eval state
  | isFinal state = [state]
  | otherwise = state : eval next_state
  where
    next_state = doAdmin $ step state

    doAdmin :: TiState -> TiState
    doAdmin state = applyTostatics tiStatIncSteps state
-}

isFinal :: TiState -> Bool
isFinal ([],_,_,_,_) = error "Empty Stack"
isFinal ([a],[],hp,_,_)
  = isDataNode (hLookup a hp)
isFinal _ = False

step :: TiState -> TiState
step state@(sk,dp,hp,gb,sic)
  = dispatch (hLookup (head sk) hp)
  where
    dispatch (NNum n) = numStep state n
    dispatch (NAp a1 a2) = apStep state a1 a2
    dispatch (NSupercomb sc args body) = scStep state sc args body
    dispatch (NInd a) = indStep state a
    dispatch (NPrim _ p) = primStep state p
    dispatch (NData t conps) = dataStep state t conps

numStep :: TiState -> CN -> TiState
numStep ([a],d:dp,hp,gb,sic) _ = (d,dp,hp,gb,sic)
numStep (sk,_,hp,_,_) _ = error ("the number of element in the stack is not one"
                                 ++ "\n"
                                 ++ (iDisplay $ showStack hp sk))

apStep :: TiState -> Addr -> Addr -> TiState
apStep (a:sk,dp,hp,gb,sic) a1 a2
  = if isIndNode node
       then (a:sk,dp,hp',gb,sic)
       else (a1:a:sk,dp,hp,gb,sic)
  where
    node = hLookup a2 hp
    node' = NAp a1 (getInd node)
    hp' = hUpdate a node' hp

scStep :: TiState -> Name -> [Name] -> CoreExpr -> TiState
scStep (sk,dp,hp,gb,sic) sc_name arg_names body
  = (new_sk,dp,new_hp,gb,sic)
    where
      new_sk = drop (length arg_names) sk
      addr_n = head new_sk
      new_hp = iUpdate body addr_n hp env
      env = foldl (\g (k,a) -> Mz.insert k a g) gb arg_bindings
      arg_bindings = maybe
                     (error ("The number of arguments have some errors\n"
                             ++ Mid.showTree gb))
                     id
                     (checkAndzip arg_names (getargs hp sk))

indStep :: TiState -> Addr -> TiState
indStep (sk,dp,hp,gb,sic) a
  = (new_sk,dp,hp,gb,sic)
  where      
    new_sk = (a:tail sk)

primStep :: TiState -> Primitive -> TiState
primStep state Neg = primOneArith state Neg
primStep state Abs = primOneArith state Abs
primStep state (PrimConstr t n) = constrStep state t n
primStep state If = primIf state  
primStep state arith = primArith state arith


dataStep :: TiState -> Int -> [Addr] -> TiState
dataStep (_,s:dp,hp,gb,sic) _ _
  = (s,dp,hp,gb,sic)

primOneArith :: TiState -> Primitive -> TiState
primOneArith ([a,a1],dp,hp,gb,sic) f
  = if isDataNode numNode
    then ([a1],dp,hp',gb,sic)
    else ([b],[a1]:dp,hp,gb,sic)
  where
    apNode = hLookup a1 hp
    b = snd $ getNAp apNode
    numNode = hLookup b hp
    numNode' = arithOneN f numNode
    hp' = hUpdate a1 numNode' hp

primNeg _ = error "the number of arguments in stack must be 2"

primArith :: TiState -> Primitive -> TiState
primArith ((a:a1:a2:sk),dp,hp,gb,sic) f
  | isDataNode arg1 && isDataNode arg2 = let nw_nd = arithNNum f arg1 arg2
                                             hp' = hUpdate a2 nw_nd hp in
                                           ([a2],dp,hp',gb,sic)
  | isDataNode arg1 = ([arg2_addr],[a1,a2]:dp,hp,gb,sic)
  | isDataNode arg2 = ([arg1_addr],[a1,a2]:dp,hp,gb,sic)
  | otherwise = ([arg1_addr,arg2_addr],[a1,a2]:dp,hp,gb,sic)
    where
      [arg1_addr,arg2_addr] = getargsNoName [a1,a2] hp
      arg1 = hLookup arg1_addr hp
      arg2 = hLookup arg2_addr hp

constrStep :: TiState -> Int -> Int -> TiState
constrStep (sk,dp,hp,gb,sic) tag arity
  = (new_sk,dp,new_hp,gb,sic)
  where
    new_sk = drop arity sk
    addr_n = head new_sk
    conps = getargs hp sk
    new_hp = hUpdate addr_n (NData tag conps) hp

primIf :: TiState -> TiState
primIf ([a,a1,a2,a3,a4,a5],dp,hp,gb,sic)
  | k1 == Then && k2 == Else = primIf_go ([a,a1,a3,a5],dp,hp,gb,sic)
  | otherwise = error "PrimIfCheck: the pattern of like if ... then ... else"
    where
      [k1_addr,k2_addr] = getargsNoName [a2,a4] hp
      [k1,k2] = map (getNPrimP . (flip hLookup) hp) [k1_addr,k2_addr]
primIf _ = error "PrimIfCheck: the pattern of like if ... then ... else"

primIf_go :: TiState -> TiState
primIf_go ((a:a1:a2:a3:sk),dp,hp,gb,sic)
  | isDataNode s = ([a3],dp,new_hp,gb,sic)
  | otherwise = ([s_addr],[a1,a2,a3]:dp,hp,gb,sic)
  where
    [s_addr,r1_addr,r2_addr] = getargsNoName [a1,a2,a3] hp
    s = hLookup s_addr hp
    new_hp = if getNDataT s == 2
             then hUpdate a3 (NInd r1_addr) hp
             else hUpdate a3 (NInd r2_addr) hp
primIf_go _ = error "The number of arguments of the stack is less then 4"

      
instantiate :: CoreExpr -> TiHeap -> TiGlobals -> (TiHeap, Addr)
instantiate (A (ENum n)) heap env = hAlloc (NNum n) heap
instantiate (EAp e1 e2) heap env = hAlloc (NAp a1 a2) heap2
  where
    (heap1, a1) = instantiate e1 heap env
    (heap2, a2) = instantiate e2 heap1 env

instantiate (A (EVar v)) heap env = (heap, aLookup
                                           (error $ "Undefined name: " ++ v ++ "\n" ++ Mid.showTree env )
                                           v
                                           id
                                           env)

instantiate (A (Prn e)) heap env = instantiate e heap env

instantiate (A (EConstr tag arity)) heap env
  = instantiateConstr tag arity heap env

instantiate (ELet isrec defs body) heap env
  | isrec = instantiateLetrec defs body heap env
  | otherwise = instantiateLet defs body heap env

instantiate (ECase e alts) heap env = error "Can't instantiate case expr"

instantiateConstr tag arity heap env
  = hAlloc (NPrim "Cons" (PrimConstr tag arity)) heap

instantiateLet defs body heap env = instantiate body heap1 env1
  where
    (m, e) = head defs
    (heap1, a1) = instantiate e heap env
    env1 = Mz.insert m a1 env

--已修改，事先确定每个def参数个数保证，最后的地址正确
instantiateLetrec defs body heap env = instantiate body heap1 env1
  where
    argsWithNum = map (\(n, e) -> (n, countEAp e)) defs
    maxAddr = hNextAddr heap
    arg_bindings = scanl (\(_,addr) (n,inc) -> (n,addr+inc)) ("",maxAddr-1) argsWithNum
    env1 = foldl (\en (m,addr) -> Mz.alter (\_ -> Just addr)  m en) env arg_bindings
    heap1 = foldl (\hp (_,e) -> fst $ instantiate e hp env1) heap defs
    

iUpdate :: CoreExpr -> Addr -> TiHeap -> TiGlobals -> TiHeap
iUpdate (A (ENum n)) upd_addr heap _ = hUpdate upd_addr (NNum n) heap
iUpdate (A (EVar v)) upd_addr heap env = hUpdate upd_addr (NInd old_addr) heap
  where
    old_addr = aLookup
               (error $ "There is no variable which is called \"" ++ v ++ "\"\n")
               v
               id
               env

iUpdate (A (Prn e)) upd_addr heap env = iUpdate e upd_addr heap env
iUpdate (A (EConstr tag arity)) upd_addr heap env
  = iConstrUpdate upd_addr tag arity heap env

iUpdate (EAp e1 e2) upd_addr heap env
  = hUpdate upd_addr (NAp a1 a2) heap2
    where
      (heap1, a1) = instantiate e1 heap env
      (heap2, a2) = instantiate e2 heap1 env

iUpdate (ELet isrec defs body) upd_addr heap env = iUpdate body upd_addr heap1 env1
  where
    alternative_env = if isrec then env1 else env
    (heap1, env1) = foldl makeIt (heap,env) defs
    makeIt (hp,en) (m,e) = let (hp',a) = instantiate e hp alternative_env 
                               en' = Mz.insert m a en in
                             (hp',en')

iUpdate (ECase e alts) upd_addr heap env = error "Can't instantiate and update case expr"

iConstrUpdate upd_addr tag arity heap env
  = hUpdate upd_addr (NPrim "Cons" (PrimConstr tag arity)) heap


showResults :: [TiState] -> String
showResults states
 = iDisplay (iConcat [iLayn (map showState states), showStatics (last states)])

showState :: TiState -> Iseq
showState (sk,dp,hp,gb,sic)
  = iConcat [showStack hp sk, iNewline, showDumpDepth dp]
    

showState' :: TiState -> Iseq
showState' (_,_,(_,_,m),_,_)
  = foldr (\(k, a) rs -> iConcat [iStr "(", showAddr k,
                                  iStr ",",
                                  showNode a, iStr ")",iNewline ,rs])
    iNil
    (Mz.assocs m)


showEnv :: Mz.Map Name Addr -> Iseq
showEnv env = Mz.foldrWithKey (\n a rs -> iConcat [iStr "(",iStr n, iStr" , ",showAddr a, iStr ")",rs]) iNil env

showDumpDepth :: TiDump -> Iseq
showDumpDepth dump = iConcat [iStr "Dump Depth: ", iNum $ I $ length dump]


showStack :: TiHeap -> TiStack -> Iseq
showStack heap stack
  = iConcat [ iStr "Stk [",
              iIndent (foldr makeIt iNil stack),
              iStr " ]"]
    where
      makeIt x rs
        | rs == iNil = iConcat [show_stack_item x,rs]
        | otherwise = iConcat [show_stack_item x,iNewline,rs]

      show_stack_item addr
        = iConcat [showFWAddr addr, iStr ": ",
                   showStkNode heap (hLookup addr heap)]

showStkNode :: TiHeap -> Node -> Iseq
showStkNode heap (NAp fun_addr arg_addr)
  = iConcat [ iStr "NAp ", showFWAddr fun_addr,
              iStr " ", showFWAddr arg_addr, iStr " (",
              showNode (hLookup arg_addr heap), iStr ") "]

showStkNode heap node = showNode node

showNode :: Node -> Iseq
showNode (NAp a1 a2) = iConcat [ iStr "NAp ", showAddr a1,
                                 iStr " ", showAddr a2]
showNode (NSupercomb name args body) = iStr ("NSupercomb " ++ name)
showNode (NNum n) = iConcat [(iStr "NNum "), (iNum n)]
showNode (NInd a) = iConcat [iStr "NInd ", showAddr a]
showNode (NPrim m _) = iConcat [iStr "NPrim ", iStr m]
showNode (NData t ay) = iConcat [iStr "Pack ", iNum (I t), iStr " ", iNum (I $ length ay)]
                            
showAddr :: Addr -> Iseq
showAddr addr = iStr (show addr)

showFWAddr :: Addr -> Iseq         --Show address in field of width 4
showFWAddr addr = iStr (rSpaces (4 - length str) ++ str)
  where
    str = show addr

showStatics :: TiState -> Iseq
showStatics (sk,dp,hp,gb,sic)
  = iConcat [iNewline,iNewline,iStr "Total number of steps = ",
             iNum (I (tiStatGetSteps sic))]



--auxiliary function
aLookup :: (Ord k) => b -> k -> (a -> b) -> Mz.Map k a -> b
aLookup err key f mka = maybe err f (Mz.lookup key mka)

hInitial :: TiHeap
hInitial = (0, [1..], Mz.empty :: Mz.Map Addr Node)

--hAlloc :: Heap a -> a -> (Heap a, Addr)
hAlloc :: a -> Heap a -> (Heap a, Addr)
hAlloc x (size, (next:free), cts) = ((size+1, free, Mz.alter (\_ -> Just x) next cts), next)

hNextAddr :: Heap a -> Addr
hNextAddr (_,(next:_),_) = next

--hLookup :: Ord k => (a,b, Mz.Map k c) -> k -> c
hLookup :: Ord k => k -> (a,b,Mz.Map k c) -> c
hLookup x (_,_, cts) = aLookup (error "can't find it") x id cts

hFindMin :: Ord k => (a,b,Mz.Map k c) -> k
hFindMin (_,_,cts) = fst $ Mz.findMin cts

--第一个(k,c)为替换原来，k处的值
hUpdate :: Ord k => k -> c -> (a,b,Mz.Map k c) -> (a,b,Mz.Map k c)
hUpdate oldK node (sz,free,cts) = let cts1 = Mz.alter (\_ -> Just node) oldK cts in
                                    (sz,free,cts1)

hCut n (sz,free,cts) = (sz+n,free1,cts)
  where
    free1 = drop n free

getargs :: TiHeap -> TiStack -> [Addr]
getargs heap (sc:sk)
  = map get_arg sk
    where
      get_arg addr = arg
        where
          (_, arg) = getNAp $ hLookup addr heap

getargsNoName :: TiStack -> TiHeap -> [Addr]
getargsNoName sk hp
  = map (snd . getNAp . (flip hLookup) hp) sk

isDataNode :: Node -> Bool
isDataNode (NNum _) = True
isDataNode (NData _ _) = True
isDataNode _ = False

isIndNode :: Node -> Bool
isIndNode (NInd _) = True
isIndNode _ = False

isApNode :: Node -> Bool
isApNode (NAp _ _) = True
isApNode _ = False 

checkAndzip :: [a] -> [b] -> Maybe [(a,b)]
checkAndzip [] _ = Just []
checkAndzip (a:as) (b:bs) = makeIt as bs (Just (\x -> ((a,b):x)))
  where
    makeIt [] _ mrs = liftA (\f -> f []) mrs
    makeIt (a':as') (b':bs') mrs = let new_mrs = liftA (\f -> (\x -> f ((a',b'):x))) mrs in
                                     makeIt as' bs' new_mrs
    makeIt _ _ _ = Nothing                                 
checkAndzip _ _ = Nothing


primitives :: [(Name, Primitive)]
primitives = [("negate", Neg),
              ("+", Add), ("-", Sub),
              ("*", Mul), ("abs", Abs),
              ("/", DivF), ("`div`", DivI),
              ("if", If), ("then", Then), ("else", Else)]

{-
arithNNum :: Arith -> Node -> Node -> Node
arithNNum (AnyArith f) (NNum n1) (NNum n2) = NNum $ f n1 n2
-}

arithNNum :: Primitive -> Node -> Node -> Node
arithNNum Add = addNNum
arithNNum Sub = subNNum
arithNNum Mul = mulNNum
arithNNum DivI = divNNum
arithNNum DivF = divNNum_f

arithOneN :: Primitive -> Node -> Node
arithOneN Abs = absNNum
arithOneN Neg = negNNum

negNNum :: Node -> Node
negNNum (NNum n) = NNum $ negate n
negNNum _ = error "not a \"NNum\" type"

addNNum :: Node -> Node -> Node
addNNum (NNum n1) (NNum n2) = NNum $ n1 + n2
addNNum _ _ = error "not a \"NNum\" type"

subNNum :: Node -> Node -> Node
subNNum (NNum n1) (NNum n2) = NNum $ n1 - n2
subNNum _ _ = error "not a \"NNum\" type"

mulNNum :: Node -> Node -> Node
mulNNum (NNum n1) (NNum n2) = NNum $ n1 * n2
mulNNum _ _ = error "not a \"NNum\" type"

divNNum :: Node -> Node -> Node
divNNum (NNum (I x1)) (NNum (I x2)) = NNum $ I (x1 `div` x2)
divNNum _ _ = error "only for two integer num"

divNNum_f :: Node -> Node -> Node
divNNum_f (NNum (F x1)) (NNum (F x2)) = NNum $ F (x1 / x2)
divNNum_f (NNum (I x1)) (NNum (F x2)) = let x1' = fromIntegral x1 + 0.0 in
                                          NNum $ F (x1' / x2)
divNNum_f (NNum (F x1)) (NNum (I x2)) = let x2' = fromIntegral x2 + 0.0 in
                                          NNum $ F (x1 / x2')
divNNum_f (NNum (I x1)) (NNum (I x2)) = let x1' = fromIntegral x1 + 0.0
                                            x2' = fromIntegral x2 + 0.0 in
                                          NNum $ F (x1' / x2')

absNNum :: Node -> Node
absNNum (NNum n) = NNum $ abs n

getInd :: Node -> Addr
getInd (NInd a) = a
getInd _ = error "not a \"NInd\" type"

getNAp :: Node -> (Addr,Addr)
getNAp (NAp a1 a2) = (a1,a2)
getNAp _ = error "not a \"NInd\" type"

getNPrimP :: Node -> Primitive
getNPrimP (NPrim _ p) = p
getNPrimP _ = error "not a \"NPrim\" type"

getNDataT :: Node -> Int
getNDataT (NData tag _) = tag
getNDataT _ = error "not a \"NData\" type"

getHdofSk :: TiState -> Node
getHdofSk ((a:_),_,hp,_,_) = hLookup a hp
getHdofSk _ = error "the stack is empty"

extraPreludeDefs :: CoreProgram
extraPreludeDefs = [("False", [], A $ EConstr 1 0),
                    ("True", [], A $ EConstr 2 0)]
