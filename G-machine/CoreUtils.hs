module CoreUtils (
  module Language,
  Addr,Heap,
  GmState,GmCode,GmStack,GmStatistic,
  Instruction(UnWind,Pushglobal,Pushcn,Push,Mkap,Slide),
  Node(NNum,NAp,NGlobal),
  aLookup,
  hInitial,hAlloc,hNextAddr,hLookup,hFindMin,hUpdate,
  hCut,hFree,
  getargs,getargsNoName,
  isDataNode,isApNode,isGlobalNode,
  getNAp,getHdofSk
) where

import Language
import CoreParser
import qualified Data.Map.Lazy as Mz

type Addr = Int
type GmState = (GmCode, GmStack, GmHeap, GmGlobals, GmStatistic)

type GmCode = [Instruction]
type GmStack = [Addr]
type GmHeap = Heap Node
type GmGlobals = Mz.Map Name Addr
type GmStatistic = Int

type Heap a = (Int, [Addr], Mz.Map Addr a)

data Instruction
  = UnWind
  | Pushglobal Name
  | Pushcn CN
  | Push Int
  | Mkap
  | Slide Int

data Node
  = NNum CN
  | NAp Addr Addr
  | NGlobal Int GmCode


instance Eq Instruction where
  UnWind == UnWind = True
  Pushglobal a == Pushglobal b = a == b
  Pushcn a == Pushcn b = a == b
  Push a == Push b = a == b
  Mkap == Mkap = True
  Slide a == Slide b = a == b
  _ == _ = False



getCode :: GmState -> GmCode
getCode (i, sk, hp, gb,sic) = i

putCode :: GmCode -> GmState -> GmState
putCode i' (i, sk,hp,gb,sic) = (i',sk,hp,gb,sic)

getHeap :: GmState -> GmHeap
getHeap (_,_,hp,_,_) = hp

putHeap :: GmHeap -> GmState -> GmState
putHeap hp' (i,sk,hp,gb,sic) = (i,sk,hp',gb,sic)

getGlobal :: GmState -> GmGlobals
getGlobal (_,_,_,gb,_) = gb

putGlobal :: GmGlobals -> GmState -> GmState
putGlobal gb' (i,sk,hp,gb,sic) = (i,sk,hp,gb',sic)

sicInitial :: GmStatistic
sicInitial = 0

sicIncSteps :: GmStatistic -> GmStatistic
sicIncSteps s = s + 1

sicGetSteps :: GmStatistic -> GmStatistic
sicGetSteps s = s

getStatistic :: GmState -> GmStatistic
getStatistic (_,_,_,_,sic) = sic

putStatistic :: GmStatistic -> GmState -> GmState
putStatistic sic' (i,sk,hp,gb,sic) = (i,sk,hp,gb,sic')


aLookup :: (Ord k) => b -> k -> (a -> b) -> Mz.Map k a -> b
aLookup err key f mka = maybe err f (Mz.lookup key mka)

hInitial :: GmHeap
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

getargs :: GmHeap -> GmStack -> [Addr]
getargs heap (sc:sk)
  = map get_arg sk
    where
      get_arg addr = arg
        where
          (_, arg) = getNAp $ hLookup addr heap

getargsNoName :: GmStack -> GmHeap -> [Addr]
getargsNoName sk hp
  = map (snd . getNAp . (flip hLookup) hp) sk

isDataNode :: Node -> Bool
isDataNode (NNum _) = True
isDataNode _ = False


isApNode :: Node -> Bool
isApNode (NAp _ _) = True
isApNode _ = False 

isGlobalNode :: Node -> Bool
isGlobalNode (NGlobal _ _) = True
isGlobalNode _ = False

checkAndzip :: [a] -> [b] -> Maybe [(a,b)]
checkAndzip [] _ = Just []
checkAndzip (a:as) (b:bs) = makeIt as bs (Just (\x -> ((a,b):x)))
  where
    makeIt [] _ mrs = liftA (\f -> f []) mrs
    makeIt (a':as') (b':bs') mrs = let new_mrs = liftA (\f -> (\x -> f ((a',b'):x))) mrs in
                                     makeIt as' bs' new_mrs
    makeIt _ _ _ = Nothing                                 
checkAndzip _ _ = Nothing

getNAp :: Node -> (Addr,Addr)
getNAp (NAp a1 a2) = (a1,a2)
getNAp _ = error "not a \"NInd\" type"

getHdofSk :: GmState -> Node
getHdofSk (_,(a:_),hp,_,_) = hLookup a hp
getHdofSk _ = error "the stack is empty"

