module ShowResult where

import qualified Data.Map.Lazy as Mz
import Language
import CoreUtils

showResults :: [GmState] -> [Char]
showResults sts@((_,_,_,gb,_):_)
  =iDisplay (iConcat [
                iStr "Supercombinator definitions", iNewline,
                Mz.foldr interIt iNil gb,
                iNewline,iNewline,iStr "State transitions",iNewline,iNewline,
                iLayn (map showState sts),iNewline,iNewline,
                showStatistic (last sts)])
   where
     interIt sc r
       | r == iNil = iConcat [showSc sc, r]
       | otherwise = iConcat [showSc sc, iNewline, r]
                
showSc :: GmState -> (Name, Addr) -> Iseq
showSc (_,_,hp,_,_) (name, addr)
  = iConcat [iStr "Code for ", iStr name, iNewline,
             showGmCode gmcode, iNewline, iNewline]
    where
      (NGlobal arity gmcode) = hLookup hp addr


showGmCode :: GmCode -> Iseq
showGmCode i
  = iConcat [iStr " Code:{",
             iIndent (foldl interIt i),
             iStr "}",iNewline]

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
             iIndent, foldr interIt iNil $ reverse sk,
             iStr "]"]
    where
      interIt a r
        | r == iNil = iConcat [showStackItem st a, r]
        | otherwise = iConcat [showStackItem st a, iNewline, r]

showStackItem :: GmState -> Addr -> Iseq
showStackItem st@(_,_,hp,_,_) addr
  = iConcat [showAddr addr, iStr ": ",
             showNode st addr (hLookup hp addr)]

showAddr :: Addr -> Iseq
showAddr addr = iStr (show addr)
                  

showNode :: GmState -> Addr -> Node -> Iseq
showNode _ _ (NNum cn) = iNum cn
showNode (_,_,_gb,sic) addr (NGlobal n g) = iConcat [iStr "Global", iStr v]
  where
    tmp = \x -> (NNum (I 0)):x
    v = head $ (Mz.foldlWithKey makeIt (tail . tmp) gb) []
    makeIt k a r = if a == addr
                      then (\x -> r (k:x))
                      else r
showNode _ _ (NAp a1 a2) = iConcat [iStr "Ap ", showAddr a1,
                                    showAddr a2]
