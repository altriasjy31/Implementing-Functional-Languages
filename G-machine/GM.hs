module GM where

import Language
import qualified Data.Map.Lazy as Mz

{-
runProg :: String -> IO ()
runProg inp = case parse pProgram inp of
                Result _ r -> putStrLn $ showResults $ eval $ compile r
                _ -> error "These is someting error in your program"
-}

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
  = NNum Int
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



