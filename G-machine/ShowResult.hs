module ShowResult where

import qualified Data.Map.Lazy as Mz
import Language
import CoreUtils

showResults :: [GmState] -> [Char]
showResults sts@(st@(_,_,_,gb,_):_)
  =iDisplay (iConcat [
                iStr "Supercombinator definitions", iNewline,
                Mz.foldrWithKey interIt iNil gb,
                iNewline,iNewline,iStr "State transitions",iNewline,iNewline,
                iLayn (map showState sts),iNewline,iNewline,
                showStatistic (last sts)])
   where
     interIt nm ar r
       | r == iNil = iConcat [showSc st (nm,ar), r]
       | otherwise = iConcat [showSc st (nm,ar), iNewline, r]
                
showSc :: GmState -> (Name, Addr) -> Iseq
showSc (_,_,hp,_,_) (name, addr)
  = iConcat [iStr "Code for ", iStr name, iNewline,
             showGmCode gmcode, iNewline, iNewline]
    where
      (NGlobal arity gmcode) = hLookup addr hp


showGmCode :: GmCode -> Iseq
showGmCode i
  = iConcat [iStr " Code:{",
             iIndent (foldr interIt iNil i),
             iStr "}",iNewline]
    where
      interIt c r
        | r == iNil = iConcat [showInstruction c, r]
        | otherwise = iConcat [showInstruction c, iNewline, r]

showInstruction :: Instruction -> Iseq
showInstruction UnWind = iStr "Unwind"
showInstruction (Pushglobal f) = iConcat [iStr "Pushglobal ", iStr f]
showInstruction (Push n) = iConcat [iStr "Push ", iNum $ I n]
showInstruction (Pushcn cn) = iConcat [iStr "Pushcn ", iNum cn]
showInstruction Mkap = iStr "Mkap"
showInstruction (Slide n) = iConcat [iStr "Slide ", iNum $ I n]


showState :: GmState -> Iseq
showState st@(i,_,_,_,_)
  = iConcat [showStack st, iNewline,
             showGmCode i, iNewline]

showStack :: GmState -> Iseq
showStack st@(_,sk,_,_,_)
  = iConcat [iStr " Stack:[",
             iIndent (foldr interIt iNil $ reverse sk),
             iStr "]"]
    where
      interIt a r
        | r == iNil = iConcat [showStackItem st a, r]
        | otherwise = iConcat [showStackItem st a, iNewline, r]

showStackItem :: GmState -> Addr -> Iseq
showStackItem st@(_,_,hp,_,_) addr
  = iConcat [showAddr addr, iStr ": ",
             showNode st addr (hLookup addr hp)]

showAddr :: Addr -> Iseq
showAddr addr = iStr (show addr)
                  

showNode :: GmState -> Addr -> Node -> Iseq
showNode _ _ (NNum cn) = iNum cn
showNode (_,_,_,gb,sic) addr (NGlobal n g) = iConcat [iStr "Global", iStr v]
  where
    tmp = \x -> "":x
    v = head $ (Mz.foldlWithKey makeIt (tail . tmp) gb) []
    makeIt r k a = if a == addr
                      then (\x -> r (k:x))
                      else r
showNode _ _ (NAp a1 a2) = iConcat [iStr "Ap ", showAddr a1,
                                    showAddr a2]
showStatistic :: GmState -> Iseq
showStatistic (i,sk,hp,gb,sic)
  = iConcat [iNewline,iNewline,iStr "Total number of steps = ",
             iNum (I (sicIncSteps sic))]

