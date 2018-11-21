-- 增加了OutPut，用于对外界输出，但没处理最后结束时，不行

module Template_pointer_reversal where

import CoreParser
import Language

import qualified Data.Map.Lazy as Mz
import qualified Data.Map.Internal.Debug as Mid


type Addr = Int
type AddrRange = (Addr, Addr)
type TiStack = [Addr]

--type TiDump = [TiStack]
type TiDump = [Int]    --表示每一截堆栈的长度

--Heap的组成 (size, [free address], Mz.Map address Node)
--Node的的组成 NAp Addr Addr | NSupercomb Name [Name] CoreExpr | NNum a

data Node
  = NAp Addr Addr | NSupercomb Name [Name] CoreExpr | NInd Addr
  | NPrim Name Primitive | NNum CN | NData Int [Addr]
  | NMarked MarkState Node

data MarkState = Done             --Marking on this node finished
               | Visits Int       --Node visited n times so far


type Heap a = (Int, [Addr], Mz.Map Addr a)
type TiHeap = Heap Node
type OutPut = [Addr] -> [Addr]  --包含了，要打印对象的地址

--包含了全部的函数名以及对应的地址
type TiGlobals = Mz.Map Name Addr

--统计结果
type TiStatics = Int


type TiState = (OutPut,TiStack, TiDump, TiHeap, TiGlobals, TiStatics)

type Primitive = TiState -> TiState


runProg :: String -> IO ()
runProg file = case parse pProgram file of
                 Result remind result -> putStrLn $ showResults $ eval $ compile result
                 _ -> error "There is someting error"


tiStatInitial :: TiStatics
tiStatInitial = 0

tiStatIncSteps :: TiStatics -> TiStatics
tiStatIncSteps s = s + 1

tiStatGetSteps :: TiStatics -> Int
tiStatGetSteps s = s


applyTostatics :: (TiStatics -> TiStatics) -> TiState -> TiState
applyTostatics stats_fun (output,stack, dump, heap, sc_defs, stats)
  = (output,stack,dump,heap,sc_defs, stats_fun stats)


compile :: CoreProgram -> TiState
compile program = (tail . (-1:), initial_stack, initialTiDump, initial_heap, globals, tiStatInitial)
  where
    initial_stack = aLookup (error "\"main\" function doesn't exist") "main" (\x -> [x]) globals

    initialTiDump = [ls]
    ls = length initial_stack
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
isFinal (op,sk,[d],hp,gb,sic)
  | d == 0 = True
  | d == 1 = isDataNode $ hLookup (head sk) hp
  | otherwise = False
isFinal _ = False  

step :: TiState -> TiState
step state@(op,sk,dp,hp,gb,sic)
  = dispatch (hLookup (head sk) hp)
  where
    dispatch (NNum _) = numStep state
    dispatch (NAp a1 a2) = apStep state a1 a2
    dispatch (NSupercomb sc args body) = scStep state sc args body
    dispatch (NInd a) = indStep state a
    dispatch (NPrim _ p) = primStep state p
    dispatch (NData t conps) = dataStep t conps state

numStep :: TiState -> TiState
numStep (op,sk,(d:ds),hp,gb,sic)
  | null ds = (op, tail sk, (d-1:ds),hp,gb,sic)
  | d == 1 = (op, tail sk,ds,hp,gb,sic)
  | otherwise = error ("the number of element in the stack is not one"
                                 ++ "\n"
                                 ++ (iDisplay $ showStack hp sk))


apStep :: TiState -> Addr -> Addr -> TiState
apStep (op,(a:sk),dp@(d:ds),hp,gb,sic) a1 a2
  = if isIndNode node
       then (op, (a:sk),dp,hp',gb,sic)
       else (op, (a1:a:sk),(d+1:ds),hp,gb,sic)
  where
    node = hLookup a2 hp
    node' = NAp a1 (getInd node)
    hp' = hUpdate a node' hp

scStep :: TiState -> Name -> [Name] -> CoreExpr -> TiState
scStep (op, sk,(d:ds),hp,gb,sic) sc_name arg_names body
  = (op,new_sk,new_dp,new_hp,gb,sic)
    where
      l = length arg_names
      new_sk = drop l sk
      new_dp = (d-l:ds)
      addr_n = head new_sk
      new_hp = iUpdate body addr_n hp env
      env = foldl (\g (k,a) -> Mz.insert k a g) gb arg_bindings
      arg_bindings = maybe
                     (error ("The number of arguments have some errors\n"
                             ++ Mid.showTree gb))
                     id
                     (checkAndzip arg_names (getargs hp sk))

indStep :: TiState -> Addr -> TiState
indStep (op,sk,dp,hp,gb,sic) a
  = (op,new_sk,dp,hp,gb,sic)
  where      
    new_sk = (a:tail sk)

primStep :: TiState -> Primitive -> TiState
primStep state prim = prim state

dataStep :: Int -> [Addr] -> TiState  -> TiState
dataStep _ _ (op,sk,(d:ds),hp,gb,sic)
  = (op,new_sk,ds,hp,gb,sic)
  where
    new_sk = drop d sk

primOneArith :: (Node -> Node) -> TiState -> TiState
primOneArith f (op,[a,a1],dp@(d:ds),hp,gb,sic)
  = if isDataNode numNode
    then (op,[a1],(d-1:ds),new_hp,gb,sic)
    else (op,[b,a1],(1:(d-1):ds),hp,gb,sic)
  where
    apNode = hLookup a1 hp
    b = snd $ getNAp apNode
    numNode = hLookup b hp
    numNode' = f numNode
    new_hp = hUpdate a1 numNode' hp

primOneArith _ _ = error "the number of arguments in stack must be 2"

primDyadic :: (Node -> Node -> Node) -> TiState -> TiState
primDyadic f (op,(a:a1:a2:sk),(d:ds),hp,gb,sic)
  | not $ isDataNode arg1 = (op,(arg1_addr:a2:sk),(1:(d-2):ds),hp,gb,sic)
  | not $ isDataNode arg2 = (op,(arg2_addr:a2:sk),(1:(d-2):ds),hp,gb,sic)
  | otherwise = (op,(a2:sk),(d-2:ds),new_hp,gb,sic)
    where
      [arg1_addr, arg2_addr] = getargsNoName [a1,a2] hp
      arg1 = hLookup arg1_addr hp
      arg2 = hLookup arg2_addr hp

      rs = f arg1 arg2
      new_hp = hUpdate a2 rs hp


constrStep :: Int -> Int -> TiState -> TiState
constrStep tag arity (op,sk,(d:ds),hp,gb,sic)
  = (op,new_sk,new_dp,new_hp,gb,sic)
  where
    new_sk = drop arity sk
    new_dp = (d-arity:ds)
    addr_n = head new_sk
    conps = getargs hp $ take d sk
    new_hp = hUpdate addr_n (NData tag conps) hp



primIf :: TiState -> TiState
primIf (op,(a:a1:a2:a3:sk),(d:ds),hp,gb,sic)
  | isDataNode s = (op,(a3:sk),(d-3:ds),new_hp,gb,sic)
  | otherwise = (op,(s_addr:a1:a2:a3:sk),(1:(d-1):ds),hp,gb,sic)
  where
    [s_addr,r1_addr,r2_addr] = getargsNoName [a1,a2,a3] hp
    s = hLookup s_addr hp
    new_hp = if getNDataT s == 2
             then hUpdate a3 (NInd r1_addr) hp
             else hUpdate a3 (NInd r2_addr) hp

casePairStep :: TiState -> TiState
casePairStep (op,(a:a1:a2:sk),(d:ds),hp,gb,sic)
  | not $ isDataNode p = (op,(p_addr:a2:sk),(1:(d-2):ds),hp,gb,sic)
  | otherwise = (op,(new_f_addr:sk),(1:ds),new_hp,gb,sic)
  where
    [p_addr,f_addr] = getargsNoName [a1,a2] hp
    p = hLookup p_addr hp 
    (addr_1:args_addr) = getNDataA p

    nd = NAp f_addr addr_1
    (hp1, f1_addr) = hAlloc nd hp
    (new_hp,new_f_addr) = makeButLst (hp1,f1_addr) args_addr

    makeButLst (h,f_a) [argi] = let nd = NAp f_a argi
                                    tmp_h = hUpdate a2 nd h in
                                  (tmp_h, a2)
    makeButLst (h,f_a) (argi:args) = let (h',f_a') = hAlloc (NAp f_a argi) h in
                                       makeButLst (h',f_a') args
                                       
caseListStep :: TiState -> TiState
caseListStep (op,(a:a1:a2:a3:sk),(d:ds),hp,gb,sic)
  | not $ isDataNode p = (op,(p_addr:a3:sk),(1:(d-3):ds),hp,gb,sic)
  | otherwise = (op,(a3:sk),(d-3:ds),new_hp,gb,sic)   --"new_hp" depends on the kind of "pack tag"
  where
    [p_addr,cn_addr,cc_addr] = getargsNoName [a1,a2,a3] hp
    p = hLookup p_addr hp
    cn = hLookup cn_addr hp
    (p_tag, p_args_addr) = getNData p
    new_hp = if p_tag == 2
                then fst $ makeButLst (hp,cc_addr) p_args_addr
                else if p_tag == 1
                        then hUpdate a3 cn hp
                        else error "it is not a Cons Node or a Nil Node"

    makeButLst (h,f_a) [argi] = let ap = NAp f_a argi
                                    h' = hUpdate a3 ap h in
                                  (h',a3)
    makeButLst (h,f_a) (argi:args) = let (h',f_a') = hAlloc (NAp f_a argi) h in
                                       makeButLst (h',f_a') args
abortStep :: TiState -> TiState
abortStep _ = error "the program must be aborted"

printStep :: TiState -> TiState
printStep (op, (a:a1:a2:sk),(d:ds),hp,gb,sic)
  | not $ isDataNode b1 = (op, (b1_addr:a2:sk), (1:(d-2):ds),hp,gb,sic)
  | otherwise = ((\x -> op (b1_addr:x)),(b2_addr:sk),(1:ds),hp,gb,sic)
  where
    [b1_addr,b2_addr] = getargsNoName [a1,a2] hp
    b1 = hLookup b1_addr hp


stopStep :: TiState -> TiState
stopStep (op,_,_,hp,gb,sic) = (op,[],[0],hp,gb,sic)
    

      
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

instantiate (ECase e alts) heap env = error "can't instantiate case"
{-
  = (new_hp, lst_addr)
  where
    (hp1, r_addr) = instantiate e heap env
    r = hLookup r_addr hp1p
    
-}
instantiateConstr tag arity heap env
  = hAlloc (NPrim "Cons" $ constrStep tag arity) heap

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
               (error $ "There is no variable which is called \""
                ++ v
                ++ "\"\n"
                ++ (iDisplay $ showEnv env))
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
  = hUpdate upd_addr (NPrim "Cons" $ constrStep tag arity) heap


--garbage collection

markFrom :: (Addr, Addr, TiHeap) -> (Addr, Addr, TiHeap)
markFrom st@(f_addr, b_addr, hp)
  | isApNode f_nd = let (a1,a2) = getNAp f_nd
                        nd1 = NAp b_addr a2
                        mnd = NMarked (Visits 1) nd1
                        hp1 = hUpdate f_addr mnd hp in
                      markFrom (a1,f_addr,hp1)

  | isPrimNode f_nd = let mnd = NMarked Done f_nd
                          hp1 = hUpdate f_addr mnd hp in
                        markFrom (f_addr,b_addr,hp1)

  | isMDone f_nd = goto b_nd st

  | isIndNode f_nd = let ia = getInd f_nd in
                       markFrom (ia,b_addr,hp)

  | isDataNode f_nd = let mnd = NMarked Done f_nd
                          hp1 = hUpdate f_addr mnd hp in
                        markFrom (b_addr,f_addr,hp1)
  where
    f_nd = hLookup f_addr hp
    b_nd = hLookup b_addr hp

    isMDone (NMarked Done _) = True
    isMDone _ = False

    goto (NMarked (Visits 1) nd) st@(f_addr,b_addr,hp)
      = let (b',a2) = getNAp nd
            mnd = NMarked (Visits 2) (NAp f_addr b')
            hp1 = hUpdate b_addr mnd hp in
          markFrom (a2,b_addr,hp1)
                      
    goto (NMarked (Visits 2) nd) (f_addr,b_addr,hp)
      = let (a1,b') = getNAp nd
            mnd = NMarked Done (NAp a1 f_addr)
            hp1 = hUpdate b_addr mnd hp in
          markFrom (b_addr,b',hp1)
    goto _ st@(f_addr,0,hp) = st         --结束

markFromTiStack :: TiStack -> TiDump -> [Addr]
markFromTiStack sk dp = (fst $ foldl makeIt (tail . (0:),sk) dp) []
  where
    makeIt (frs, sk) n = let tmp_sk = drop (n - 1) sk
                             r = maybe
                                 (error "some errors in the TiDump so that the number in the dump can't mathch with the corelated in the stack")
                                 id
                                 $ mbHead tmp_sk
                             sk1 = maybe
                                   (error "some errors in the TiDump so that the number in the dump can't mathch with the corelated in the stack")
                                   id
                                   $ mbTail tmp_sk in
                           ((\x -> frs $ r:x),sk1)
    mbHead (a:_) = Just a
    mbHead _ = Nothing

    mbTail (_:a) = Just a
    mbTail _ = Nothing


scanHeap :: TiHeap -> TiHeap
scanHeap hp = foldr unmarkIt hp usedAddrs
  where
    usedAddrs = hAddrsUsed hp
    unmarkIt a hp = if isMarkedNode nd
                       then hUpdate a (getNMarkd nd) hp
                       else hFree a hp
      where
        nd = hLookup a hp



--show result functions
showResults :: [TiState] -> String
showResults states
 = iDisplay (iConcat [iLayn (map showState states), showStatics (last states)])

showState :: TiState -> Iseq
showState (op,sk,dp,hp,gb,sic)
  = iConcat [iStr "OutPut: ", iNewline, showOutPut hp op,iNewline,
             iStr "Stack: ", iNewline,showStack hp sk, iNewline, showDumpDepth dp]
--  = iConcat [iStr "Stack: ", iNewline,showStack hp sk, iNewline, showDumpDepth dp]
    

showState' :: TiState -> Iseq
showState' (_,_,_,(_,_,m),_,_)
  = foldr (\(k, a) rs -> iConcat [iStr "(", showAddr k,
                                  iStr ",",
                                  showNode a, iStr ")",iNewline ,rs])
    iNil
    (Mz.assocs m)


showEnv :: Mz.Map Name Addr -> Iseq
showEnv env = Mz.foldrWithKey (\n a rs -> iConcat [iStr "(",iStr n, iStr" , ",showAddr a, iStr ")",rs]) iNil env

showDumpDepth :: TiDump -> Iseq
showDumpDepth dump = iConcat [iNewline, iStr "Dump Depth: ", iNum $ I $ length dump]


showOutPut :: TiHeap -> OutPut -> Iseq
showOutPut hp op
  | op1 == [] = iNil
  | otherwise = iConcat [iStr "Out: ",
                         foldr makeIt iNil op1]
  where
    op1 = op []
    makeIt x rs
      | rs == iNil = iConcat [show_stack_item x, rs]
      | otherwise = iConcat [show_stack_item x, iStr ", ",rs]
      
    

    show_stack_item addr
      = iConcat [showFWAddr addr, iStr ": ",
                 showStkNode hp (hLookup addr hp)]


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
showNode (NData t ay) = iConcat [iStr "NData ", iNum (I t), iStr " ", iNum (I $ length ay)]

                            
showAddr :: Addr -> Iseq
showAddr addr = iStr (show addr)

showFWAddr :: Addr -> Iseq         --Show address in field of width 4
showFWAddr addr = iStr (rSpaces (4 - length str) ++ str)
  where
    str = show addr

showStatics :: TiState -> Iseq
showStatics (op,sk,dp,hp,gb,sic)
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

hSize :: Ord k => (Int,b,Mz.Map k c) -> Int
hSize (sz,_,_) = sz

hAddrsUsed :: Ord k => (a,[Addr],Mz.Map k c) -> [Addr]
hAddrsUsed (_,(a:_),_) = [1,2..a]

hFree :: Ord k => k -> (Int,[k],Mz.Map k a) -> (Int,[k],Mz.Map k a)
hFree a (sz,free,nds) = (sz+1,a:free,new_nds)
  where
    new_nds = Mz.delete a nds

aNull :: Addr
aNull = 0

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

isDataNode_not_nnum :: Node -> Bool
isDataNode_not_nnum (NData _ _) = True
isDataNode_not_nnum _ = False

isIndNode :: Node -> Bool
isIndNode (NInd _) = True
isIndNode _ = False

isApNode :: Node -> Bool
isApNode (NAp _ _) = True
isApNode _ = False 

isMarkedNode :: Node -> Bool
isMarkedNode (NMarked _ _) = True
isMarkedNode _ = False

isPrimNode :: Node -> Bool
isPrimNode (NPrim _ _) = True
isPrimNode _ = False

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
primitives = [("negate", primOneArith negNNum),
              ("abs", primOneArith absNNum),
              ("+", primDyadic addNNum), ("-", primDyadic subNNum),
              ("*", primDyadic mulNNum),
              ("/", primDyadic divNNum_f), ("`div`", primDyadic divNNum),
              ("if", primIf),
              ("<", primDyadic $ compareNData lessData), ("<=", primDyadic $ compareNData lesseqData),
              (">", primDyadic $ compareNData greaterData), (">=", primDyadic $ compareNData greatereqData),
              ("==", primDyadic $ compareNData eqData), ("/=", primDyadic $ compareNData noteqData),
              ("casePair", casePairStep), ("caseList", caseListStep),("abort", abortStep),
              ("print", printStep),("stop", stopStep)]


compareNData :: (Node -> Node -> Bool) -> Node -> Node -> Node
compareNData f nd1 nd2 = if f nd1 nd2
                            then NData 2 []
                            else NData 1 []

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


eqData :: Node -> Node -> Bool
eqData (NData t1 _) (NData t2 _) = t1 == t2
eqData (NNum n1) (NNum n2) = n1 == n2

noteqData :: Node -> Node -> Bool
noteqData (NData t1 _) (NData t2 _) = t1 /= t2
noteqData (NNum n1) (NNum n2) = n1 /= n2

lessData :: Node -> Node -> Bool
lessData (NData t1 _) (NData t2 _) = t1 < t2
lessData (NNum n1) (NNum n2) = n1 < n2

lesseqData :: Node -> Node -> Bool
lesseqData (NData t1 _) (NData t2 _) = t1 <= t2
lesseqData (NNum n1) (NNum n2) = n1 <= n2

greaterData :: Node -> Node -> Bool
greaterData (NData t1 _) (NData t2 _) = t1 > t2
greaterData (NNum n1) (NNum n2) = n1 > n2

greatereqData :: Node -> Node -> Bool
greatereqData (NData t1 _) (NData t2 _) = t1 >= t2
greatereqData (NNum n1) (NNum n2) = n1 >= n2

getInd :: Node -> Addr
getInd (NInd a) = a
getInd _ = error "not a \"NInd\" type"

getNAp :: Node -> (Addr,Addr)
getNAp (NAp a1 a2) = (a1,a2)
getNAp _ = error "not a \"NInd\" type"

getNPrimP :: Node -> Primitive
getNPrimP (NPrim _ p) = p
getNPrimP _ = error "not a \"NPrim\" type"

getNData :: Node -> (Int, [Addr])
getNData (NData tag args) = (tag,args)
getNData _ = error "not a \"NData\" type"

getNDataT :: Node -> Int
getNDataT (NData tag _) = tag
getNDataT _ = error "not a \"NData\" type"

getNDataA :: Node -> [Addr]
getNDataA (NData _ args) = args
getNDataA _ = error "not a \"NData\" type"

getHdofSk :: TiState -> Node
getHdofSk (op,(a:_),_,hp,_,_) = hLookup a hp
getHdofSk _ = error "the stack is empty"

getNmvap :: Node -> (Int,Addr,Addr)
getNmvap (NMarked (Visits n) (NAp a b)) = (n,a,b)
getNmvap  _ = error "not a \"NMarked (Visits n) (NAp a b)\" type"

getNMarkd :: Node -> Node
getNMarkd (NMarked _ nd) = nd
getNMarkd _ = error "not a \"NMarked\" type"

extraPreludeDefs :: CoreProgram
extraPreludeDefs = [ ("False", [], A $ EConstr 1 0),
                     ("True", [], A $ EConstr 2 0),
                     ("MkPair", ["x","y"], EAp
                                           (EAp (A $ EConstr 1 2) (A $ EVar "x"))
                                           (A $ EVar "y")),
                     ("fst", ["p"], EAp
                                    (EAp (A $ EVar "casePair") (A $ EVar "p"))
                                    (A $ EVar "K")),
                     ("snd", ["p"], EAp
                                    (EAp (A $ EVar "casePair") (A $ EVar "p"))
                                    (A $ EVar "K1")),
                     ("nil", [], A $ EConstr 1 0),
                     ("cons", ["x","xs"], EAp
                                          (EAp (A $ EConstr 2 2) (A $ EVar "x"))
                                          (A $ EVar "xs")),
                     ("head", ["xs"], EAp
                                      (EAp
                                       (EAp (A $ EVar "caseList") (A $ EVar "xs"))
                                       (A $ EVar "abort"))
                                      (A $ EVar "head'")),
                     ("head'", ["x","xs"], A $ EVar "x"),
                     ("tail", ["xs"],EAp
                                      (EAp
                                       (EAp (A $ EVar "caseList") (A $ EVar "xs"))
                                       (A $ EVar "abort"))
                                      (A $ EVar "tail'")),
                     ("tail'",["x","xs"], A $ EVar "xs"),
                     ("printList", ["xs"], EAp
                                           (EAp
                                            (EAp (A $ EVar "caseList") (A $ EVar "xs"))
                                            (A $ EVar "stop"))
                                           (A $ EVar "printCons")),
                     ("printCons", ["h", "t"], EAp
                                               (EAp (A $ EVar "print") (A $ EVar "h"))
                                               (EAp (A $ EVar "printList") (A $ EVar "t")))]
                                              
                                           

