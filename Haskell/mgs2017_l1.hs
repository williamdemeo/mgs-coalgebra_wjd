-- MIDLANDS GRADUATE SCHOOL 2017
-- Coalgebras and Infinite Data Structures
--    Venanzio Capretta

-- Lecture 1

-- STREAM CALCULUS 
-- from Ralf Hinze, "Concrete stream calculus"

import Control.Applicative
import Data.List

data Stream a = Cons {hd :: a, tl :: Stream a}

infixr 5 <:

(<:) :: a -> Stream a -> Stream a
(<:) = Cons

-- Pretty printing of streams, only the first 20 elements

shown :: Show a => Int -> Stream a -> String
shown 0 _ = "..."
shown n s = show (hd s) ++ " <: " ++ shown (n-1) (tl s)

instance Show a => Show (Stream a) where
  show = shown 20
  
-- Stream is an applicative functor
  
instance Functor Stream where
  fmap f s = f (hd s) <: fmap f (tl s)

instance Applicative Stream where
  pure x = x <: pure x
  fs <*> xs = ((hd fs) (hd xs)) <: ((tl fs) <*> (tl xs))
  
-- Defining a list from a stream
strList :: Stream a -> [a]
strList s = hd s : strList (tl s) 
  
-- Defining a stream from a list: use only with infinite lists
listStr :: [a] -> Stream a
listStr (x:xs) = x <: listStr xs
listStr [] = error "the list must be infinite to generate a stream"

strRepeat :: a -> Stream a
strRepeat = pure 

-- Numeric operations are done pointwise

instance Num a => Num (Stream a) where
  (+) = liftA2 (+)
  (-) = liftA2 (-)
  (*) = liftA2 (*)
  abs = fmap abs
  signum = fmap signum
  fromInteger i = pure (fromInteger i)

-- The stream of all natural numbers
nat :: Stream Int
nat = 0 <: (nat+1)

-- The most general way to define a stream
strUnfold :: (b -> a) -> (b -> b) -> b -> Stream a
strUnfold h t y = h y <: strUnfold h t (t y)

-- Alternative definition of stream of naturals
nat1 :: Stream Int
nat1 = strUnfold id (+1) 0

-- Interleaving two streams
(|><) :: Stream a -> Stream a -> Stream a
s1 |>< s2 = hd s1 <: (s2 |>< (tl s1))

-- Elements in even positions
evens :: Stream a -> Stream a
evens s = hd s <: odds (tl s)

-- Elements in odd positions
odds :: Stream a -> Stream a
odds s = evens (tl s)

-- Stream of Fibonacci numbers
fib :: Stream Int
fib = 0 <: (1 <: fib) + fib

-- Stream of prime numbers (Erathostenes' algorithm)

-- Keep only the elements satisfying a property
strFilter :: (a -> Bool) -> Stream a -> Stream a
strFilter p s = if (p (hd s)) 
                then (hd s) <: strFilter p (tl s)
                else strFilter p (tl s)                   

-- Delete all multiples of n
sieve :: Int -> Stream Int -> Stream Int
sieve n = strFilter (\x -> mod x n /= 0)

erathostenes :: Stream Int -> Stream Int
erathostenes s = hd s <: erathostenes (sieve (hd s) (tl s))

primes :: Stream Int
primes = erathostenes (tl $ tl nat)

-- Two function of doubtful productivity

f :: Stream a -> Stream a
f s = hd s <: (f $ tl $ tl $ tl $ tl s)

psi :: Stream a -> Stream a
psi s = hd s <: (evens $ psi $ f $ tl s) |>< (odds $ psi $ evens $ tl s)

isp :: Stream a -> Stream a
isp s = hd s <: (odds $ isp $ evens $ tl s) |>< (evens $ isp $ odds $ tl s)


fib_aux :: (Integer,Integer) -> Stream Integer
fib_aux = strUnfold fst (\(a,b)->(b,a+b))

fib2 = fib_aux (0,1)

from :: Integer -> Stream Integer
from = strUnfold id (+1)


-- INFINITE BINARY TREES

data BTree a = Bnode {label :: a, left :: BTree a, right :: BTree a}

-- Pretty printing of trees, to depth 5

spaces n = take n (repeat ' ')

vshowbtl :: Show a => Int -> BTree a -> [String]
vshowbtl 0 s = ["."]
vshowbtl n (Bnode x l r) = (sp1 ++ lb ++ sp2) :
                           (zipWith (\ls rs -> ls ++ sp' ++ rs) sl sr)
  where lb = show x
        sl = vshowbtl (n-1) l
        sr = vshowbtl (n-1) r
        sp1 = spaces (length (sl!!0))
        sp2 = spaces (length (sr!!0))
        sp' = spaces (length lb)

vshowbtn :: Show a => Int -> BTree a -> String
vshowbtn n = (intercalate "\n") . (vshowbtl n)

vshowbt :: Show a => BTree a -> String
vshowbt = vshowbtn 5 -- (intercalate "\n") . (vshowbtn 5)

hshowbtn :: Show a => String -> Int -> BTree a -> String
hshowbtn sp 0 _ = sp ++ "..."
hshowbtn sp n t = hshowbtn sp' (n-1) (right t) ++
                  '\n' : sp ++ lb ++ " <: " ++ 
                  '\n' : hshowbtn sp' (n-1) (left t)
                 
  where lb = show (label t) 
        sp' = sp ++ (take (length lb) (repeat ' '))
 
hshowbt :: Show a => BTree a -> String
hshowbt = hshowbtn "" 5        

instance Show a => Show (BTree a) where
  show = vshowbtn 5

-- Tree with repetition of an element in the nodes
btrepeat :: a -> BTree a
btrepeat x = Bnode x (btrepeat x) (btrepeat x)

-- Mirror image of a tree
mirror :: BTree a -> BTree a
mirror (Bnode x l r) = Bnode x (mirror r) (mirror l)

-- BTree is an applicative functor

instance Functor BTree where
  fmap f (Bnode x l r) = Bnode (f x) (fmap f l) (fmap f r)

instance Applicative BTree where
  pure x = btrepeat x
  fs <*> xs = Bnode (label fs (label xs))
                    (left fs <*> left xs)
                    (right fs <*> right xs)
    
-- The leftmost path of a tree gives a stream
lspine :: BTree a -> Stream a
lspine t = label t <: lspine (left t)

-- Numeric operations are done pointwise
instance Num a => Num (BTree a) where
  (+) = liftA2 (+)
  (-) = liftA2 (-)
  (*) = liftA2 (*)
  abs = fmap abs
  signum = fmap signum
  fromInteger i = pure (fromInteger i)

-- From stream to tree: repeat an element at a given depth
lrep :: Stream a -> BTree a
lrep s = Bnode (hd s) (lrep (tl s)) (lrep (tl s))


strtr :: Stream a -> BTree a
strtr s = Bnode (hd s) (strtr (evens $ odds s)) (strtr (odds $ odds s))

-- The most general way to define a tree
treeUnfold :: (b->a) -> (b->b) -> (b-> b) -> b -> BTree a
treeUnfold n l r x = Bnode (n x) (treeUnfold n l r (l x)) (treeUnfold n l r (r x))

str2tree :: Stream a -> BTree a
str2tree = treeUnfold hd (evens.tl) (odds.tl)

trl2str :: [BTree a] -> Stream a
trl2str = strUnfold (\(t:ts) -> label t) (\(t:ts) -> ts ++ [left t,right t])

tr2str t = trl2str [t]

-- Binary tree of all natural numbers

pow2 :: BTree Int
pow2 = Bnode 1 (2*pow2) (2*pow2)

tnat :: BTree Int
tnat = Bnode 0 (tnat+pow2) (tnat+2*pow2)

-- A different way to do it, works with any stream
-- Arranges the elements in the tree

--Drops n elements from a stream
sdrop :: Int -> Stream a -> Stream a
sdrop 0 s = s
sdrop n s = sdrop (n-1) (tl s)

stotree :: Stream a -> Int -> BTree a
stotree s n = Bnode (hd s) (stotree (sdrop n s) (2*n) ) (stotree (sdrop (n + 1) s) ((2*n) + 1) )

streamToTree ::  Stream a -> BTree a
streamToTree s = stotree s 1

-- 2015 Exercise Class
-- Flattening a tree into a stream

t2s_alpha :: (BTree a, [BTree a]) -> (a,(BTree a, [BTree a]))
t2s_alpha (Bnode a t1 t2, ts) = (a, ts')
  where ts' = case ts of
                [] -> (t1,[t2])
                (r:rs) -> (r,rs++[t1,t2])

tree2stream :: BTree a -> Stream a
tree2stream t = strUnfold (\x -> fst $ t2s_alpha x) 
                          (\x -> snd $ t2s_alpha x)
                          (t,[])

-- Mapping a stream to a tree, width-first

s2t_h :: Stream a -> a
s2t_h (Cons x xs) = x

s2t_l :: Stream a -> Stream a
s2t_l (Cons x xs) = fst (chomp xs 1)
 
s2t_r :: Stream a -> Stream a
s2t_r (Cons x xs) = snd (chomp xs 1)
 
split :: Stream a -> Int -> ([a],Stream a)
split s 0 = ([],s)
split (Cons a s) n = let (l,s') = split s (n-1) in (a:l,s')

sapp :: [a] -> Stream a -> Stream a
sapp [] s = s
sapp (x:xs) s = x <: (sapp xs s)

chomp :: Stream a -> Int -> (Stream a, Stream a)
chomp s n = let (l0,s0) = split s n
                (l1,s1) = split s0 n
                (s2,s3) = chomp s1 (2*n)
            in (sapp l0 s2, sapp l1 s3)

stream2tree :: Stream a -> BTree a
stream2tree = treeUnfold s2t_h s2t_l s2t_r

