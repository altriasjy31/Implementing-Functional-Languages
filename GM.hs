{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ExistentialQuantification #-}
module GM where

import Language
import CoreParser

--(stack, dump, heap, global)
{-
主要函数的类型
runProg :: IO String
compile :: CoreProgram -> TiState
eval :: TiState -> [TiState]
showResult :: [TiState] -> String
-}

{-
runProg :: String -> IO String
runProg file = case parse pProgram file of
                 Result remind result -> putStrLn $ showResult $ eval $ compile result
                 _ -> error "There is someting error"
-}


type Addr = Int                 
type TiStack = [Addr]

data TiDump = DummyTiDump

type Heap a = (Int, [Int], [(Int, a)])
data Node = NAp Addr Addr
          | NSupercomb Name [Name] CoreExpr
          | forall a . (Num a, Show a) => NNum a
type TiHeap = Heap Node

type ASSOC a b = [(a,b)]
type TiGlobals = ASSOC Name Addr          

type TiStats = Int

type TiState = (TiStack, TiDump, TiHeap, TiGlobals, TiStats)

initialTiDump :: TiDump
initialTiDump = DummyTiDump

tiStatInitial :: TiStats
tiStatInitial = 0

tiStatIncSteps :: TiStats -> TiStats
tiStatIncSteps s = s + 1

tiStatGetSteps :: TiStats -> Int
tiStatGetSteps s = s

--applies a given function to the statistics component of the state:
applyToStatas :: (TiStats -> TiStats) -> TiState -> TiState
applyToStatas stats_fun (stack, dump, heap, sc_defs, stats) = (stack,dump,heap,sc_defs,stats_fun stats)


compile :: CoreProgram -> TiState
compile program = (initial_stack, initialTiDump, initial_heap, globals, tiStatInitial)
  where
    initial_stack = maybe (error "main is not defined") (\x -> [x]) (lookup "main" globals)

    extraPreludeDefs = []    --暂时把这个定为空
    sc_defs = program ++ preludeDefs ++ extraPreludeDefs
    (initial_heap, globals) = buildInitialHeap sc_defs


buildInitialHeap :: [CoreScDefn] -> (TiHeap, TiGlobals)
buildInitialHeap = foldl make (hInitial, [])
  where
    make (h, gs) scf = let (h',g') = allocateSc h scf
                       in (h', g':gs)

allocateSc :: TiHeap -> CoreScDefn -> (TiHeap, (Name, Addr))
allocateSc heap (name, args, body) = (heap', (name, addr))
  where
    (heap', addr) = hAlloc heap (NSupercomb name args body)

eval :: TiState -> [TiState]
eval state = state : rest_states
  where
    rest_states
      | isFinal state = []
      | otherwise = eval next_state

    next_state = doAdmin (step state)

    doAdmin :: TiState -> TiState
    doAdmin state = applyToStatas tiStatIncSteps state

isFinal :: TiState -> Bool
isFinal ([sole_addr], dump,heap,globals,stats)    --只有一个元素
  = isDataNode (hLookup heap sole_addr)
isFinal ([],_,_,_,_) = error "Empty Stack"
isFinal _ = False

step :: TiState -> TiState
step state@(stack,dump,heap,globals,stats)
  = dispatch (hLookup heap (hd stack))
  where
    dispatch (NNum n) = numStep state n
    dispatch (NAp a1 a2) = apStep state a1 a2
    dispatch (NSupercomb sc args body) = scStep state sc args body

numStep :: (Num a, Show a) => TiState -> a -> TiState
numStep _ _ = error "Number applied as a function"

apStep :: TiState -> Addr -> Addr -> TiState
apStep (stack,dump,heap,globals,stats) a1 a2
  = (a1:stack,dump,heap,globals,stats)

scStep :: TiState -> Name -> [Name] -> CoreExpr -> TiState
scStep (stack, dump,heap,globals,stats) sc_name arg_names body
  = (new_stack,dump,new_heap,globals,stats)
  where
    new_stack = result_addr : (drop (length arg_names+1) stack)

    (new_heap, result_addr) = instantiate body heap env
    env = arg_bindings ++ globals
    arg_bindings = zip arg_names (getargs heap stack)

getargs :: TiHeap -> TiStack -> [Addr]
getargs heap (sc:stack)
  = map get_arg stack
    where
      get_arg addr = arg
        where
          (NAp fun arg) = hLookup heap addr

instantiate :: CoreExpr -> TiHeap -> ASSOC Name Addr -> (TiHeap, Addr)
instantiate (A (ENum n)) heap env = hAlloc heap (NNum n)
instantiate (EAp e1 e2) heap env = hAlloc heap2 (NAp a1 a2)
  where
    (heap1,a1) = instantiate e1 heap env
    (heap2,a2) = instantiate e2 heap1 env
instantiate (A (EVar v)) heap env = (heap, maybe (error ("Undefined name")) id (lookup v env))


--auxiliary function
type MultState = (Int, Int, Int, Int)

hd :: [a] -> a
hd (x:_) =  x
hd _ = error "empty list"


hInitial = (0,      [1..],  [])
hAlloc :: Heap a -> a -> (Heap a, Addr)
hAlloc  (size, (next:free), cts) n   = ((size+1, free,   (next,n) : cts),next)

hLookup :: Heap a -> Addr -> a
hLookup (_, _, cts) a = maybe (error "not in the heap") id (lookup a cts)

isDataNode :: Node -> Bool
isDataNode (NNum _) = True
isDataNode _ = False

transitionRules :: Int -> Int -> Int
transitionRules n m = evalMult (n, m, 0, 0)
  where
    evalMult :: MultState -> Int
    evalMult state@(n, m, d, t)
      | m == 0 && d == 0 = t
      | d == 0 = evalMult (n, m-1,n,t)
      | otherwise = evalMult (n,m,d-1,t+1)
