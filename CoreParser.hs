{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ExistentialQuantification #-}

module CoreParser (
  module Control.Applicative,
  module Data.Char,
  Parser,
  constantParser,
  expectedEofParser, unexpectedEofParser,
  unexpectedCharParser, unexpectedStringParser,
  getResult,
  (|||),
  parse,
  character,
  list,
  list1,
  alpha, digit, letter,symbol,
  alpha',digit',letter',
  satisfy,
  satisfy_S,
  is,
  space,spaces,spaces1,
  oneOf,noneOf,
  tok,charTok,stringTok,
  string,string1,
  pKeyWords,
  liftA4,
  sepByc1,sepByparser1,
  betweenWithc,betweenWithparser,
  endByParser
  )where


import Control.Applicative
import Data.Char

type Tokens = String

data Feedback a =
    Result Tokens a       -- Result （剩余部分）　结果
  | ExpectedEof Tokens
  | UnexpectedEof
  | UnexpectedChar Char
  | UnexpectedString String
  deriving Eq

data Parser a = Parser (Tokens -> Feedback a)

instance Show a => Show (Feedback a) where
  show (Result t a)
    = stringConcat ["Result >", t, "< ", show a]
  show (ExpectedEof t)
    = stringConcat ["Expected end of stream, but got >", show t, "<"]
  show (UnexpectedEof) = "Unexpected end of stream"
  show (UnexpectedChar c)
    = stringConcat ["Unexpected character: ", show c]
  show (UnexpectedString s)
    = stringConcat ["Unexpected string: ", show s]

--只有处理正确的结果时，f　才会被成功应用
instance Functor Feedback where
{-
  _ <$> err@(ExpectedEof _) = err
  _ <$> err@(UnexpectedEof) = err
  _ <$> err@(UnexpectedChar _) = err
  _ <$> err@(UnexpectedString _) = err
  f <$> (Result t a) = Result t (f a)
-}

  fmap _ (ExpectedEof i) = ExpectedEof i
  fmap _ UnexpectedEof = UnexpectedEof
  fmap _ (UnexpectedChar c) = UnexpectedChar c
  fmap _ (UnexpectedString s) = UnexpectedString s
  fmap f (Result t a) = Result t (f a)


--判断是正确的结果还是产生了错误
isErrorResult :: Feedback a -> Bool
isErrorResult (Result _ _) = False
isErrorResult _ = True

onResult :: Feedback a -> (Tokens -> a -> Feedback b) -> Feedback b
onResult (ExpectedEof i) _ = ExpectedEof i
onResult UnexpectedEof _ = UnexpectedEof
onResult (UnexpectedChar c) _ = UnexpectedChar c
onResult (UnexpectedString s) _ = UnexpectedString s
onResult (Result t a) f = f t a


parse :: Parser a -> Tokens -> Feedback a
parse (Parser p) = p

expectedEofParser :: String -> Parser a
expectedEofParser s = constantParser $ ExpectedEof s

unexpectedEofParser :: Parser a
unexpectedEofParser = constantParser UnexpectedEof

unexpectedCharParser :: Char -> Parser a
unexpectedCharParser c = Parser (\_ -> UnexpectedChar c)

unexpectedStringParser :: String -> Parser a
unexpectedStringParser s = constantParser $ UnexpectedString s

getResult :: Feedback a -> a
getResult (Result _ x) = x
getResult _ = error "we need \"Result rs x\""

constantParser :: Feedback a -> Parser a
constantParser = Parser . const

instance Functor Parser where
--  fmap :: (a -> b) -> Parser a -> Parser b
--  fmap f per = Parser (\tok -> f <$> (parse per tok))
  fmap :: (a -> b) -> Parser a -> Parser b
  fmap f per = do r <- per
                  return $ f r

instance Applicative Parser where
  pure :: a -> Parser a
  pure = return


  (<*>) :: Parser (a -> b) -> Parser a -> Parser b
  (<*>) perF per = do f <- perF
                      r <- per
                      return $ f r


instance Monad Parser where
  return :: a -> Parser a
  return x = Parser (\tok -> Result tok x)

  (>>=) :: Parser a -> (a -> Parser b) -> Parser b
  (>>=) per f_per
    = Parser (\tok ->
                case parse per tok of
                  Result t a -> parse (f_per a) t
                  err -> onResult err (\x y -> parse (f_per y) x))

instance Alternative Parser where
  empty :: Parser a
  empty = Parser (\tok -> ExpectedEof tok)

  (<|>) :: Parser a -> Parser a -> Parser a
  (<|>) per1 per2 = Parser (\tok -> case parse per1 tok of
                                      (Result t a) -> Result t a
                                      _ -> parse per2 tok)

(|||) :: Parser a -> Parser a -> Parser a
(|||) per1 per2
  = Parser (\tok ->
              case parse per1 tok of
                (Result t a) -> Result t a
                _ -> parse per2 tok)
infix 3 |||
                                                      
character :: Parser Char
character = Parser check
  where
    check (h:rma) = Result rma h
    check _ = UnexpectedEof

--不会返回错误，一旦不匹配，返回[]
list :: Parser a -> Parser [a]
list per = do r <- per
              (r:) <$> (list per)
              <|> return []

--当一开始就出现不匹配时，返回错误
list1 :: Parser a -> Parser [a]
list1 per = do r <- per
               (r:) <$> (list per)

satisfy :: (Char -> Bool) -> Parser Char
satisfy f = do c <- character
               if f c
                 then return $ c
                 else unexpectedCharParser c


satisfy_S :: Int -> (String -> Bool) -> Parser String
satisfy_S n f = do s <- thisManyI n character
                   if f s
                     then return s
                     else return []

oneOf :: String -> Parser Char
oneOf cs = tok $ satisfy (\c -> c `elem` cs)

noneOf :: String -> Parser Char
noneOf cs = tok $ satisfy (\c -> not (c `elem` cs))

                  
is :: Char -> Parser Char
is c = satisfy (== c)

space :: Parser Char
space = satisfy (== ' ')

spaces :: Parser String
spaces = list space

spaces1 :: Parser String
spaces1 = list1 space


thisManyI :: Int -> Parser a -> Parser [a]
thisManyI n per = do r <- per
                     make (n-1) (pure (r:))
  where
    make c mrt
      | c == 0 = mrt >>= \rt -> return $ rt []
      | otherwise = do rt <- mrt
                       r <- per
                       make (c-1) $ pure (\x -> rt (r:x))


tok :: Parser a -> Parser a
tok per = do spaces
             r <- per
             spaces
             return r

charTok :: Char -> Parser Char
charTok c = tok (is c)
             
string1 :: String -> Parser String
string1 (h:rma) = do r <- is h
                     (r:) <$> string1 rma
string1 _ = return []                  

string :: String -> Parser String
string (h:rma) = do r <- is h
                    makeIt (pure (r:)) rma
                    <|> do c <- character
                           return [c]

  where
    makeIt mrs (h':rma') = do r <- is h'
                              makeIt (chng_rs r mrs) rma'
                              <|> do return (mrs >>= \rs -> rs [])
    makeIt mrs _ = return (mrs >>= \rs -> rs [])

    chng_rs c = liftA (\f -> (\x -> f (c:x)))

stringTok :: String -> Parser String
stringTok (h:rma) = do r <- charTok h
                       (r:) <$> stringTok rma
stringTok _ = return []


--Parser b是一个间隔符，因此，该函数的目的是针对含有间隔的对象，将间隔之间的对象放到一块儿
sepByparser1 :: Parser a -> Parser b -> Parser [a]
sepByparser1 per sep = do r <- liftA2 (\x _ -> x) per sep
                          (r:) <$> sepByparser1 per sep
                          <|> do r <- per
                                 return [r]

sepByc1 :: Parser a -> Char -> Parser [a]
sepByc1 per sep = let pSep = charTok sep
                  in sepByparser1 per pSep


betweenWithparser :: Parser a -> Parser b -> Parser b -> Parser a
betweenWithparser per pleft pright = do pleft
                                        r <- per
                                        pright
                                        return r

betweenWithc :: Parser a -> Char -> Char -> Parser a
betweenWithc per left right = let pl = charTok left
                                  pr = charTok right
                              in do pl
                                    r <- per
                                    pr
                                    return r
endByParser :: Parser a -> Parser [a] -> Parser [a]
endByParser per ped = do c <- per
                         makeIt (pure (c:))
  where
    makeIt mrs = do ed <- ped
                    rs <- mrs
                    return $ rs ed
                    <|> do c <- per
                           rs <- mrs
                           makeIt (pure (\x -> rs (c:x)))
                           <|> do rs <- mrs
                                  return $ rs []

--auxilliary function
alpha = tok $ satisfy isAlpha
digit = tok $ satisfy isDigit
letter = tok $ satisfy isLetter
symbol = tok $ satisfy (\c -> c `elem` "!$%*+-/:=?>@^_~#")

alpha' = satisfy isAlpha
digit' = satisfy isDigit
letter' = satisfy isLetter

keyWords1 :: [String]
keyWords1 = ["case","else","in","if","letrec","let","of","Pack"]

pKeyWords :: Parser String
pKeyWords = foldr make (string1 "") keyWords1
  where
    make x rs = (string x) <|> rs


stringConcat :: [String] -> String
stringConcat = foldr1 (++) 

--Parser in spj-lest-book
pLit = string1
pVar = pKeyWords >> oneVar
  where
    oneVar = list (satisfy isLetter)
pHelloOrGoodbye :: Parser String
pHelloOrGoodbye = (pLit "hello") <|> (pLit "goodbye")

pGreeting :: Parser (String, String)
pGreeting = liftA3 (\x y _-> (x,y)) pHelloOrGoodbye pVar (pLit "!")

pGreetings :: Parser [(String, String)]
pGreetings = pZeroOrMore pGreeting

pThen :: (a -> b -> c) -> Parser a -> Parser b -> Parser c
pThen = liftA2


pThen3 :: (a -> b -> c -> d) -> Parser a -> Parser b -> Parser c -> Parser d
pThen3 = liftA3

pThen4 :: (a -> b -> c -> d -> e) -> Parser a -> Parser b -> Parser c -> Parser d -> Parser e
pThen4 f p1 p2 p3 p4 = f <$> p1 <*> p2 <*> p3 <*> p4

liftA4 :: (a -> b -> c -> d -> e) -> Parser a -> Parser b -> Parser c -> Parser d -> Parser e
liftA4 f p1 p2 p3 p4 = f <$> p1 <*> p2 <*> p3 <*> p4


pZeroOrMore per = (pOneOrMore per) <|> (return [])
pOneOrMore = list

pApply :: Parser a -> (a -> b) -> Parser b
pApply = flip (<$>)


pOneOrMoreWithSep :: Parser a -> Parser b -> Parser [a]
pOneOrMoreWithSep = sepByparser1

