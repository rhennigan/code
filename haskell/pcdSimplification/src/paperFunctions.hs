import Data.List
import Data.Ord (comparing)
import qualified Data.Vector as Vec
import qualified Data.Packed.Matrix as Mat
import qualified Numeric.LinearAlgebra.Algorithms as Lapack

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

acc' :: Num t => [t] -> [t] -> [t]
acc' x [] = x
acc' [] (yh:yt) = acc' [yh] yt
acc' x (yh:yt) = acc' (x ++ [last' x + yh]) yt

accumulate' :: Num t => [t] -> [t]
accumulate' = acc' []

tr' :: [[a]]->[[a]]
tr' ([]:_) = []
tr' x = map head' x : tr' (map tail' x)

dot' [] _ = 0
dot' _ [] = 0
dot' (uh:ut) (vh:vt) = uh*vh + (dot' ut vt)

dotm' [] _ = []
dotm' _ [] = []
dotm' m1 m2 = map (\p -> (map (dot' p) (tr' m2))) (m1)

rev' [] a = a
rev' (xh:xt) a = rev' xt (xh:a)

reverse' x = rev' x []

--cov' x y = (sum' (zip' (*)  f1 f2))/(fromIntegral $ length' x - 1)
--        where 
--                f1 = (map' (\p -> (p - mean' x)) x)
--                f2 = (map' (\q -> (q - mean' y)) y)

cov' x y = (dot' f1 f2)/(fromIntegral $ length' x - 1)
        where 
                f1 = (map' (\p -> (p - mean' x)) x)
                f2 = (map' (\q -> (q - mean' y)) y)
                
covm' m = map (\p -> (map (cov' p) (tr' m))) (tr' m)

shift' m = map' (\p -> (zip' (-) p s)) m
        where
                s = map' mean' (tr' m)

svd' m = Lapack.svd (Mat.fromLists m)

usvd'' (u, s, v) = Mat.toLists u

usvd' m = usvd'' (svd' m)

pc' m = dotm' (shift' m) (usvd' . covm' $ m)


--- Codimension reduction error section

var' x = sum' (map' (\p -> (p - mean' x)^2) x) / (fromIntegral $ length' x - 1)
variance' m = map var' (tr' m)

err' m = map' (\p -> p/(sum' v)) (accumulate' . reverse' $ v)
        where v = variance' . pc' $ m

--var' m = map' (\c -> sum' (map' (\r -> (r - mean' c)^2 ) c)) (tr' m)
                
--pc' m = dotm' (shift' m) (svd' . covm' . shift' $ m)

dist' :: Floating a => [a] -> [a] -> a
dist' a b = sqrt (sum'( Vec.toList (Vec.zipWith (\x->(\y->(x-y)^2)) a' b')))
        where   a' = Vec.fromList a
                b' = Vec.fromList b

cl' [] c1 c2 _ = [c1,c2]
cl' (xh:xt) c1 c2 [k1,k2]
        | (dist' xh k1) < (dist' xh k2) = cl' xt (xh:c1) c2 [k1,k2]
        | otherwise                     = cl' xt c1 (xh:c2) [k1,k2]
        
nextk' [c1,c2] = [(map' mean' (tr' c1)), (map' mean' (tr' c2))]

kstep' p oldk newk
        | oldk == newk  = cl' p [] [] newk
        | otherwise             = kstep' p newk (nextk' (cl' p [] [] newk))

kmeans' p = kstep' p [] [(head p), (last p)]