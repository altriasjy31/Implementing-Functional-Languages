module GM where

import CoreUtils
import ShowResult

runProg :: String -> IO ()
runProg inp = putStrLn $ process $ prgetresult $ prparse pProgram inp
  where
    process r = showResults $ eval $ compile r

eval :: GmState -> [GmState]
eval state = state : rest
  where
    rest | gmFinal state = []
         | otherwise = eval nextState
    nextState = doAdmin $ step state

doAdmin :: GmState -> GmState
doAdmin (i,sk,hp,gb,sic) = (i,sk,hp,gb,sic+1)

gmFinal :: GmState -> Bool
gmFinal (i,_,_,_,_) = null i

step :: GmState -> GmState
step (i:is,sk,hp,gb,sic) = dispatch i (is,sk,hp,gb,sic)


dispatch :: Instruction -> GmState -> GmState
dispatch (Pushglobal f) = pushglobal f
dispatch (Pushcn n) = pushcn n
dispatch Mkap = mkap
dispatch (Push n) = push n
dispatch (Slide n) = slide n
dispatch UnWind = unwind


pushglobal :: Name -> GmState -> GmState
pushglobal f (i,sk,hp,gb,sic)
  = (i,a:sk,hp,gb,sic)
  where
    a = aLookup (error $ "Undeclared global: " ++ f) f id gb

pushcn :: CN -> GmState -> GmState
pushcn cn (i,sk,hp,gb,sic)
  = (i,a:sk,new_hp,gb,sic)
  where
    (new_hp, a) = hAlloc (NNum cn) hp

mkap :: GmState -> GmState
mkap (i,a1:a2:as,hp,gb,sic)
  = (i,a:as,new_hp,gb,sic)
  where
    (new_hp,a) = hAlloc (NAp a1 a2) hp

push :: Int -> GmState -> GmState
push n (i,sk,hp,gb,sic)
  = (i,a:sk,hp,gb,sic)
  where
    (_, a) = getNAp $ hLookup (sk !! (n+1)) hp


slide :: Int -> GmState -> GmState
slide n (i,a:as,hp,gb,sic)
  = (i,a:new_as,hp,gb,sic)
  where
    new_as = drop n as

unwind :: GmState -> GmState
unwind (i,a:as,hp,gb,sic)
  | isDataNode nd = ([],a:as,hp,gb,sic)
  | isApNode nd = let (a1,_) = getNAp nd in
                    (i,a1:a:as,hp,gb,sic)
  | isGlobalNode nd = let (NGlobal n c) = nd in
                        if length as < n
                        then error "Uwind with too few arguments"
                        else (c,a:as,hp,gb,sic)
  | otherwise = error "Must be \"NNum\" or \"NAp\""
    where
      nd = hLookup a hp
  

compile :: CoreProgram -> GmState
compile program = (initialCode,[],heap,globals,sicInitial)
  where
    (heap, globals) = foldl_compile compileSc program
    

compileSc :: CoreScDefn -> GmCompiledSC
compileSc (name, args, body) = (name, n, compileR body env)
  where
    n = length args
    (env, _) = foldl makeIt (mzempty, 0) args
    makeIt (e, addr) arg = let e1 = mzinsert arg addr e in
                             (e1, addr+1)

compileR :: CoreExpr -> GmGlobals -> GmCode
compileR body env = compileC body env ++ [Slide (d + 1), UnWind]
  where
    d = mzsize env

compileC :: CoreExpr -> GmGlobals -> GmCode
compileC (A (EVar f)) env = if isSpc
                           then [Pushglobal f]
                           else [Push f_addr]
  where
    isSpc = mzmember f env
    f_addr = aLookup (error "Not in the environment") f id env
compileC (A (ENum cn)) _ = [Pushcn cn]
compileC (EAp e1 e2) env = compileC e1 env ++ compileC e2 env1 ++ [Mkap]
  where
    env1 = argOffset 1 env

                                    
