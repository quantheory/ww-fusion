module FusionTests where
import WWFusion
import Prelude hiding ((++), concat, dropWhile, filter, foldl, foldr, map, reverse, scanl)

foldrMap c n f xs = foldr c n $ map f xs

foldrFilter c n p xs = foldr c n $ filter p xs

mapFilter f p xs = map f $ filter p xs

filterMap p f xs = filter p $ map f xs

mapEft f start stop = map f $ eft start stop

mapReverse f xs = map f $ reverse xs

reverseMap f xs = reverse $ map f xs
