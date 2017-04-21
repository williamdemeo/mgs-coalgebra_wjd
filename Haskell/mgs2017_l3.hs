-- MIDLANDS GRADUATE SCHOOL 2017
-- Coalgebras and Infinite Data Structures
--    Venanzio Capretta

-- Lecture 3

{-# LANGUAGE RankNTypes #-}

import Data.Functor.Identity

-- Monadic Streams
data MStream m a = MCons (m (a, MStream m a))

-- Pure Streams
type Stream a = MStream Identity a

cons :: a -> Stream a -> Stream a
cons a s = MCons $ Identity (a,s)

infixr 5 <:

(<:) :: a -> Stream a -> Stream a
(<:) = cons

hd :: Stream a -> a
hd (MCons (Identity (a,_))) = a

tl :: Stream a -> Stream a
tl (MCons (Identity (_,alpha))) = alpha


-- Function that returns the index of the first non-decreasing element

{-
nodec :: Monad m => MStream m Int -> m Int
nodec alpha = do let (MCons m0) = alpha
                 (x0, (MCons m1)) <- m0
                 (x1, _) <- m1
                 if x0 <= x1 then return 1
                             else (+1) <$> nodec (MCons m1)
-}

ioalpha :: MStream IO Integer
ioalpha = ioalpha_n 0
  where ioalpha_n n = MCons $ do
           putStr ("Element number "++(show n)++": ")
           x <- readLn
           return (x, ioalpha_n (n+1))

nsum :: Monad m => MStream m Integer -> m Integer
nsum (MCons m) = do
  (x, alpha) <- m
  sumn x alpha
sumn :: Monad m => Integer -> MStream m Integer -> m Integer
sumn 0 _ = return 0
sumn n (MCons m) = do
  (x, alpha) <- m
  s <- sumn (n-1) alpha
  return (x+s)

nodec :: Monad m => MStream m Int -> m Int
nodec (MCons m) = do
  (x, alpha) <- m
  nodec_from x alpha
nodec_from x (MCons m) = do
  (y, alpha) <- m
  if x <= y then return 1
            else (+1) <$> nodec_from y alpha


-- Pure streams from (infinite) lists
lstream :: [a] -> Stream a
lstream (a:as) =  MCons (Identity (a,lstream as))

nats :: Stream Integer
nats = lstream [0..]

-- finitely branching trees

leaf :: MStream [] a
leaf = MCons []

tree0 :: MStream [] Integer
tree0 = MCons
          [(6, MCons [(7, leaf),
                      (3, MCons [(2, MCons [(2,leaf),(0,leaf)]),
                                 (4,leaf)
                                ])
                     ]
           ),
           (4, MCons [(5, leaf),
                      (1, MCons [(0, MCons [(10,leaf),(2,leaf)]),
                                 (3, leaf)
                                ])
                     ]
           )
          ]

tree1 :: Integer -> MStream [] Integer
tree1 n = MCons [(m, tree1 m) | m <- [n..2*n]]

-- State monad

data State s a = State (s -> (a,s))

runstate :: State s a -> s -> (a,s)
runstate (State h) a = h a

runst :: State s a -> s -> a
runst st = fst . runstate st

instance Functor (State s) where
  fmap f (State h) = State $ \s -> let (x,s') = h s in (f x, s')

instance Applicative (State s) where
  pure x = State $ \s -> (x,s)
  (State stf) <*> (State stx) =
    State $ \s -> let (f,s') = stf s in
                  let (x,s'') = stx s' in
                  (f x, s'')

instance Monad (State s) where
  (State stx) >>= stf =
    State $ \s -> let (x,s') = stx s in
                  runstate (stf x) s'

asktwice :: Monad m => MStream m a -> m a
asktwice (MCons m) = do (a0,_) <- m
                        (a1,_) <- m
                        return a1

askonce :: Monad m => MStream m a -> m a
askonce (MCons m) = do (a0,_) <- m
                       return a0

inc :: MStream (State Int) Int
inc = MCons $ State $ \s -> ((s,inc),s+1)

-- Error Monads

data Error m a = Pure a | Throw (m a)

merge :: Applicative m => Error m a -> m a
merge (Pure a) = pure a
merge (Throw m) = m

instance Functor m => Functor (Error m) where
  fmap f (Pure a) = Pure (f a)
  fmap f (Throw m) = Throw (fmap f m)

instance Applicative m => Applicative (Error m) where
  pure = Pure
  (Pure f) <*> (Pure x) = Pure (f x)
  (Pure f) <*> (Throw m) = Throw (f <$> m)
  (Throw mf) <*> ex = Throw (mf <*> (merge ex))

instance Monad m => Monad (Error m) where
  (Pure x) >>= f = f x
  (Throw m) >>= f = Throw (m >>= merge.f)

-- Writer Monad (with Integers)

data WInt a = WInt a Integer

get_index :: WInt a -> Integer
get_index (WInt _ n) = n

instance Functor WInt where
  fmap f (WInt x n) = WInt (f x) n

instance Applicative WInt where
  pure x = WInt x 0
  (WInt f n) <*> (WInt x m) = WInt (f x) (max n m)  

instance Monad WInt where
  (WInt x n) >>= f = let (WInt y m) = f x in WInt y (max n m)


indx :: Stream a -> MStream WInt a
indx s = index 0 s

index :: Integer -> Stream a -> MStream WInt a
index n s = let (a,s') = (hd s, tl s)
            in MCons $ WInt (a, index (n+1) s') n

modulus :: (forall m. Monad m => MStream m a -> m b) 
           -> Stream a -> Integer
modulus f s = get_index (f (indx s)) + 1

-- Strategy Trees

data StrTree a b = Answer b | Ask (a -> StrTree a b)

instance Functor (StrTree a) where
  fmap f (Answer x) = Answer (f x)
  fmap f (Ask h) = Ask (\a -> fmap f (h a)) 

instance Applicative (StrTree a) where
  pure = Answer
  (Answer f) <*> (Answer x) = Answer (f x)
  stf <*> (Ask hx) = Ask $ \a -> stf <*> (hx a)
  (Ask hf) <*> stx = Ask $ \a -> (hf a) <*> stx 

instance Monad (StrTree a) where
  (Answer x) >>= f = f x
  (Ask hx) >>= f = Ask $ \a -> (hx a) >>= f

meval :: Monad m => StrTree a b -> MStream m a -> m b
meval (Answer b) _ = return b
meval (Ask h) (MCons m) = m >>= \(a,alpha) -> meval (h a) alpha

iota :: MStream (StrTree a) a
iota = MCons $ Ask $ \a -> Answer (a,iota)

tabulate :: (forall m. Monad m => MStream m a -> m b) 
            -> StrTree a b
tabulate f = f iota

-- runst (asktwice inc) 0   = 1
-- runst (askonce inc) 0    = 0
-- runst (meval (tabulate asktwice) inc) 0   = 1
