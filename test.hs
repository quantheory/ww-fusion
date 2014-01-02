{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module F where
--import qualified Data.IntMap as IM
import AFusion as A

f :: [[Int]] -> Int
f x = foldl' (+) 0 $ A.concat x

g :: [Int] -> [Int] -> Int
g x y = foldl' (+) 0 $ x A.++ y

h :: Tree -> Int
h t = foldl' (+) 0 $ toList t

data Tree
  = Bin !Tree !Tree
  | Tip {-# UNPACK #-} !Int

toList :: Tree -> [Int]
toList = \tree -> buildW (toListFB tree)
{-# INLINE toList #-}

toListFB
  :: forall r f
  .  Tree
  -> (forall e. Iso (f e) (e -> r -> r))
  -> (Int -> r -> r) -> r -> r
toListFB root (Iso wrap unwrap) c n = wrap go root n
  where
    go :: f Tree
    go = unwrap $ \t z -> case t of
      Bin l r -> wrap go l (wrap go r z)
      Tip x -> c x z
{-# INLINE [0] toListFB #-}
