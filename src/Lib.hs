{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-|
Module : Lib
Description : Library with enumerations of rational numbers

Based on
Gibbons, J., Lester, D., & Bird, R. (2006). Functional pearl: Enumerating the rationals. Journal of Functional Programming, 16(3), 281-291. [doi:10.1017/S0956796806005880](https://doi.org/10.1017/S0956796806005880)
-}
module Lib where

import Prelude hiding (gcd)
import Data.Ratio
import Data.List (group)

-- * Enumerating rationals by diagonals

-- | List of positive rational numbers created from diagonals. Contains infinitely many duplicates. Merely here for comparison.
ratPosDiag1 :: [Rational]
ratPosDiag1 = concat (diags [[m % n | m <- [1..]] | n <- [1..]])
  where diags = diags' []
        diags' _ [] = error "Impossible"
        diags' xss (ys : yss) = map head xss : diags' (ys : map tail xss) yss

-- | List of positive rational numbers created from diagonals. Although diaganals now constructed directly. Contains infinitely many duplicates. Merely here for comparison.
ratPosDiag2 :: [Rational]
ratPosDiag2 = concat [[m % (d-m) | m <- [1..d-1]] | d <- [2..]]

-- * Euclid's gcd algorithm

gcd :: Integer -> Integer -> Integer
gcd m n
  | m < n = gcd m (n-m)
  | m > n = gcd (m-n) n
  | m == n = m
  | otherwise = error "Not possible"

-- | Computes the gcd of two positive integers (no checks done) paired
-- with a trace of the computation. Uses subtractive Euclid algorithm.
gcdTrace' :: Integer -> Integer -> (Integer, [Bool])
gcdTrace' m n
  | m < n = step False $ gcdTrace' m (n-m)
  | m > n = step True $ gcdTrace' (m-n) n
  | m == n = (m, [])
  | otherwise = error "Not possible"
  where step b (m', bs) = (m', b:bs)

-- | Returns the trace of subtractive Euclid algorithm on two positive
-- integers.
gcdTrace :: Integer -> Integer -> [Bool]
gcdTrace m n = snd $ gcdTrace' m n

-- | Takes the gcd and a trace of subtractive Euclid algorithm to
-- reconstruct pair of integers.
gcdTraceToPair :: Integer -> [Bool] -> (Integer, Integer)
gcdTraceToPair d bs = foldr undo (d,d) bs
  where undo False (m, n) = (m, n + m)
        undo True (m, n) = (m + n, n)

-- | List of positive rational numbers without duplicates. Maps
-- 'gcdTraceToPair' on all possible Boolean sequences, i.e., all
-- possible subtractive Euclid traces. Setting the gcd to 1 gives
-- reduced fractions. This is @rat3@ in Gibbins et al. paper.
ratPosGcd :: [Rational]
ratPosGcd = map (uncurry (%) . gcdTraceToPair 1) boolseq
  where boolseq = [] : [b : bs | bs <- boolseq, b <- [False, True]]

-- * Tree data type

-- | Infinite trees over arbitrary type. There are no leaves.
data Tree a = Node (Tree a) a (Tree a)

instance Foldable Tree
  where foldMap f (Node l k r) = foldMap f l `mappend` f k `mappend` foldMap f r

instance Functor Tree
  where fmap f (Node l k r) = Node (fmap f l) (f k) (fmap f r)

treeLevels :: Tree a -> [[a]]
treeLevels (Node l k r) = [k] : zipWith (<>) (treeLevels l) (treeLevels r)

unfoldt :: (t -> (a, t, t)) -> t -> Tree a
unfoldt f x = let (a,y,z) = f x in Node (unfoldt f y) a (unfoldt f z)
        
-- * Stern-Brocot

stern_brocot :: Tree Rational
stern_brocot = fmap (uncurry (%)) (unfoldt step ((0,1),(1,0)))
  where step (l,r) = let m = adj l r
                     in (m,(l,m),(m,r))
        adj (m,n) (m',n') = (m+m',n+n')

rat4 :: [Rational]
rat4 = concat $ treeLevels stern_brocot


rat5 :: [Rational]
rat5 = concat (unfolds infill [(0,1),(1,0)])

unfolds :: (a -> (b,a)) -> a -> [b]
unfolds f a = let (b,a') = f a
              in b : unfolds f a'

infill :: [(Integer, Integer)] -> ([Ratio Integer], [(Integer, Integer)])
infill xs = (map mkRat ys,interleave xs ys)
  where ys = zipWith adj xs (tail xs)
        adj (m,n) (m',n') = (m+m',n+n')

interleave :: [a] -> [a] -> [a]
interleave (x : xs) ys = x : interleave ys xs
interleave [] [] = []
interleave _ _ = error "Should be lists of equal length"

mkRat :: (Integer, Integer) -> Ratio Integer
mkRat = uncurry (%)

-- Calkin-Wilf

calkin_wilf :: Tree Rational
calkin_wilf = fmap (uncurry (%)) (unfoldt step (1,1))
  where step (m,n) = ((m,n), (m,m+n), (m+n,n))

rat6 :: [Rational]
rat6 = concat $ treeLevels calkin_wilf

rat7 :: [Rational]
rat7 = iterate next 1

next :: Rational -> Rational
next x = recip $ fromInteger n + 1 - y
  where (n,y) = properFraction x

rat8 :: [Rational]
rat8 = iterate next0 0
  where next0 0 = 1
        next0 x
          | x > 0     = negate x
          | otherwise = next (negate x)

negatecf :: (Num a, Eq a) => [a] -> [a]
negatecf [] = error "Should be non-empty"
negatecf [n0] = [negate n0]
negatecf [n0, 2] = [negate n0 - 1, 2]
negatecf (n0 : 1 : n2 : ns) = (negate n0 - 1) : (n2 + 1) : ns
negatecf (n0 : n1 : ns) = (negate n0 - 1) : 1 : (n1 - 1) : ns

type CF = [Integer]

rat9 :: [CF]
rat9 = iterate (recipcf . nextcf ) [1]
  where nextcf [] = error "Should be non-empty"
        nextcf [n0] = [n0 + 1]
        nextcf [n0, 2] = [n0 , 2]
        nextcf (n0 : 1 : n2 : ns) = n0 : (n2 + 1) : ns
        nextcf (n0 : n1 : ns) = n0 : 1 : (n1 - 1) : ns
        recipcf (0 : ns) = ns
        recipcf ns = 0 : ns

cf2rat :: CF -> Rational
cf2rat = mkRat . foldr op (1, 0)
  where op m (n, d) = (m * n + d, n)

runlengths :: Integer -> [Integer]
runlengths n =
  let ls = map (fromIntegral . length) . group $ bits n []
  in if odd (length ls) then ls else 0:ls
  where
    bits :: Integer -> [Integer] -> [Integer]
    bits 0 bs = bs
    bits m bs =
      let (q,r) = divMod m 2
      in r:bits q bs

toEnumerate :: Integer -> Rational
toEnumerate = cf2rat . runlengths

dgcd :: Integer -> Integer -> CF
dgcd _ 0 = []
dgcd 0 _ = []
dgcd m n
  | m < n = 0:dgcd n m
  | n < m = let (q,r) = divMod m n
            in q:dgcd n r
  | m == n = []
  | otherwise = error "Impossible"

fromEnumerate :: Rational -> Integer
fromEnumerate i =
  let n = numerator i
      d = denominator i
      cf = dgcd n d
      cf' = if odd (length cf)
            then cf
            else let (_fs, (f:[])) = splitAt (length cf - 1) cf
                 in init cf <> [f-1,1]
      bits = concatMap (uncurry replicate) $ zip (map fromIntegral cf') (cycle [1,0])
      g [] = 0
      g (b:bs) = b + 2 * g bs
  in g bits

{-
instance Enum CF where
  toEnum = undefined
  fromEnum = undefined
-}
