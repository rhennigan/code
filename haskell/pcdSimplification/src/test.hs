import Data.List
import Data.Ord (comparing)
import Numeric.LinearAlgebra.Algorithms

length' [] = 0
length' (xh:xt) = length' xt + 1

join' [] y = y
join' (xh:xt) y = xh:(join' xt y)

head' (xh:xt) = xh

tail' (xh:xt) = xt

last' (xh:[]) = xh
last' (xh:xt) = last' xt

map' _ [] = []
map' f (xh:xt) = f xh : (map' f xt)

zip' f (xh:xt) (yh:yt) = (f xh yh) : (zip' f xt yt)
zip' _ _ _ = []

sum' [] = 0
sum' (xh:xt) = xh + (sum xt)

mean' x = (sum' x) / (fromIntegral $ length' x)

acc' x [] = x
acc' [] (yh:yt) = acc' [yh] yt
acc' x (yh:yt) = acc' (x ++ [last' x + yh]) yt

accumulate' = acc' []

transpose' :: [[a]]->[[a]]
transpose' ([]:_) = []
transpose' x = map head' x : transpose' (map tail' x)

dot' [] _ = 0
dot' _ [] = 0
dot' (uh:ut) (vh:vt) = uh*vh + (dot' ut vt)

rev' [] a = a
rev' (xh:xt) a = rev' xt (xh:a)

reverse' x = rev' x []

-- |Numerically stable mean
mean :: Floating a => [a] -> a
mean x = fst $ foldl' (\(!m, !n) x -> (m+(x-m)/(n+1),n+1)) (0,0) x

-- |Sample Covariance
cov :: (Floating a) => [a] -> [a] -> a
cov xs ys = sum (zipWith (*) (map f1 xs) (map f2 ys)) / (n-1)
    where
      n = fromIntegral $ length $ xs
      m1 = mean xs
      m2 = mean ys
      f1 = \x -> (x - m1)
      f2 = \x -> (x - m2)
      
covMatrix m = map (\x -> (map (cov x) (transpose m))) (transpose m)