{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
module WWFusion
  ( (++)
  , buildW
  , concat
  , dropWhile
  , eft
  , filter
  , foldl
  , foldl'
  , foldr
  , foldrW
  , foldM
  , map
  , reverse
  , scanl
  , Wrap(..)
  ) where

import Prelude hiding ((++), concat, dropWhile, filter, foldl, foldr, map, reverse, scanl)
data Wrap f b = Wrap (forall e. f e -> e -> b -> b) (forall e. (e -> b -> b) -> f e)

foldrW
  :: Wrap f b
  -> (a -> b -> b)
  -> b
  -> [a]
  -> b
foldrW (Wrap wrap unwrap) f z0 list0 = wrap go list0 z0
  where
    go = unwrap $ \list z' -> case list of
      [] -> z'
      x:xs -> f x $ wrap go xs z'
{-# NOINLINE[0] foldrW #-}

newtype Simple b e = Simple { runSimple :: e -> b -> b }

isoSimple :: Wrap (Simple b) b
isoSimple = Wrap runSimple Simple

static :: b -> Wrap (Simple b) (b -> b -> b)
static z0 = Wrap
 (\(Simple f) e k z b -> k (f e b) z)
 (\u -> Simple $ \e i -> u e const z0 i)

staticCons :: (a -> r -> r) -> a -> (r -> r -> r) -> (r -> r -> r)
staticCons c = \x k l r -> c x (k l r)
{-# INLINE staticCons #-}

-- foldr :: (a -> b -> b) -> b -> [a] -> b
-- foldr f z = foldrW isoSimple f z
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr f z = \xs -> foldrW (static z) (staticCons f) const xs z z
{-# INLINE foldr #-}

buildW
  :: (forall b f . (Wrap f b)
    -> (a -> b -> b)
    -> b
    -> b)
  -> [a]
buildW g = g isoSimple (:) []
{-# INLINE[0] buildW #-}

buildWStatic
  :: (forall b f . (Wrap f b)
    -> (a -> b -> b)
    -> b
    -> b)
  -> [a]
buildWStatic g = g (static []) (staticCons (:)) const [] []
{-# INLINE[0] buildWStatic #-}

augmentW
  :: (forall b f . (Wrap f b)
    -> (a -> b -> b)
    -> b
    -> b)
  -> [a]
  -> [a]
augmentW g xs = g isoSimple (:) xs
{-# INLINE[0] augmentW #-}

augmentWStatic
  :: (forall b f . (Wrap f b)
    -> (a -> b -> b)
    -> b
    -> b)
  -> [a]
  -> [a]
augmentWStatic g xs = g (static xs) (staticCons (:)) const xs xs
{-# INLINE[0] augmentWStatic #-}

(++) :: [a] -> [a] -> [a]
a ++ b = augmentW (\i c n -> foldrW i c n a) b
{-# INLINE (++) #-}

concat :: [[a]] -> [a]
concat xs = buildWStatic (\i c n -> foldrW i (\x y -> foldrW i c y x) n xs)
{-# INLINE concat #-}

foldl' :: (b -> a -> b) -> b -> [a] -> b
foldl' f initial = \xs -> foldrW (Wrap wrap unwrap) g id xs initial
  where
    wrap (Simple s) e k a = k $ s e a
    unwrap u = Simple $ \e a -> u e id a
    g x next acc = next $! f acc x
{-# INLINE foldl' #-}

foldl :: (b -> a -> b) -> b -> [a] -> b
foldl f initial = \xs -> foldrW wrapFoldl g id xs initial
  where
    g x next acc = next $ f acc x
{-# INLINE foldl #-}

wrapFoldl :: Wrap (Simple b) (b -> b)
wrapFoldl = Wrap (\(Simple s) e k a -> k $ s e a)
                 (\u -> Simple $ \e a -> u e id a)

map :: (a -> b) -> [a] -> [b]
map f = \ xs -> buildWStatic (\ww c n -> foldrW ww (mapFB c f) n xs)
{-# INLINE map #-}

mapFB ::  (elt -> lst -> lst) -> (a -> elt) -> a -> lst -> lst
mapFB c f = \x ys -> c (f x) ys
{-# INLINE [0] mapFB #-}

{-# RULES
"mapFB"     forall c f g.       mapFB (mapFB c f) g     = mapFB c (f.g)
 #-}

filter :: (a -> Bool) -> [a] -> [a]
filter p = \xs -> buildWStatic (\ww c n -> foldrW ww (filterFB c p) n xs) 
{-# INLINE filter #-}

filterFB :: (a -> b -> b) -> (a -> Bool) -> a -> b -> b
filterFB c p x r | p x       = x `c` r
                 | otherwise = r

{-# INLINE[0] filterFB #-}

{-# RULES
"filterFB"        forall c p q. filterFB (filterFB c p) q = filterFB c (\x -> q x && p x)
 #-}

eft :: Int -> Int -> [Int]
eft = \from to -> buildWStatic (eftFB from to)
{-# INLINE eft #-}

eftFB
  :: Int
  -> Int
  -> (Wrap f r)
  -> (Int -> r -> r)
  -> r
  -> r
eftFB from to (Wrap wrap unwrap) cons nil = wrap go from nil
  where
    go = unwrap $ \i rest -> if i <= to
      then cons i $ wrap go (i + 1) rest
      else rest
{-# INLINE[0] eftFB #-}

dropWhile :: (a -> Bool) -> [a] -> [a]
dropWhile p xs = buildW $ dwFB p xs
{-# INLINE dropWhile #-}

dwFB :: (a -> Bool) -> [a] -> Wrap f r -> (a -> r -> r) -> r -> r
dwFB p xs = \w cons nil -> foldrW (dwWrap w) (dwCons p cons) (dwNil nil) xs True
{-# INLINE dwFB #-}

newtype Arg s f e = Arg { runArg :: f (e, s) }

dwWrap :: Wrap f r -> Wrap (Arg s f) (s -> r)
dwWrap (Wrap wrap unwrap) = Wrap
  (\(Arg h) e k s -> wrap h (e,s) (k s))
  (\h -> Arg . unwrap $ \(e,s) r -> h e (\_ -> r) s)
{-# INLINE[0] dwWrap #-}

dwNil :: r -> Bool -> r
dwNil r _ = r
{-# INLINE[0] dwNil #-}

dwCons :: (a -> Bool) -> (a -> r -> r) -> a -> (Bool -> r) -> (Bool -> r)
dwCons p c = \e k b -> let b' = b && p e in if b' then k b' else e `c` k b'
{-# INLINE[0] dwCons #-}

reverse :: [a] -> [a]
reverse xs = buildW $ \w cons nil -> foldrW (revWrap w) (revFB cons) id xs nil
{-# INLINE reverse #-}

revFB c = \v fn z -> fn (c v z)
{-# INLINE[0] revFB #-}

revWrap :: Wrap f r -> Wrap f (r -> r)
revWrap (Wrap wrap unwrap) = Wrap
  (\h e k s -> k $ wrap h e s)
  (\h -> unwrap $ \e r -> h e id r)
{-# INLINE[0] revWrap #-}

revCons :: (a -> r -> r) -> a -> (r -> r) -> r -> r
revCons c e k z = k (c e z)
{-# INLINE[0] revCons #-}

scanl :: (b -> a -> b) -> b -> [a] -> [b]
scanl f z xs = buildW (scanlFB f z xs)
{-# INLINE scanl #-}

scanlFB :: (b -> a -> b) -> b -> [a] -> Wrap f r -> (b -> r -> r) -> r -> r
scanlFB f z xs = \w c n -> z `c` foldrW (scanlWrap w) (scanlCons c f) (const n) xs z
{-# INLINE scanlFB #-}

scanlWrap :: Wrap f r -> Wrap (Env b f) (b -> r)
scanlWrap (Wrap wrap unwrap) = Wrap
  (\(Env s) e k b -> wrap (s b) e (k b))
  (\u -> Env $ \b -> unwrap $ \e r -> u e (\b' -> r) b)
{-# INLINE[0] scanlWrap #-}

newtype Env r f e = Env { runEnv :: r -> f e }

scanlCons :: (b -> r -> r) -> (b -> a -> b) -> a -> (b -> r) -> b -> r
scanlCons c f = \e k acc -> let acc' = f acc e in c acc' $ k acc'
{-# INLINE[0] scanlCons #-}

foldM             :: forall m elT accT . (Monad m) => (accT -> elT -> m accT) -> accT -> [elT] -> m accT
foldM f initial = \xs -> foldrW wrapFoldM g return xs initial
  where
    g x next acc = f acc x >>= \val -> next val
    wrapFoldM :: Wrap (SimpleM m accT) (accT -> m accT)
    wrapFoldM = Wrap (\(SimpleM s) e k a -> s e a `bindFoldM` k)
                     (\u -> SimpleM $ \e a -> u e returnFoldM a)
{-# INLINE foldM #-}

newtype SimpleM m b e = SimpleM { runSimpleM :: e -> b -> m b }

bindFoldM :: Monad m => m a -> (a -> m b) -> m b
bindFoldM = (>>=)
{-# INLINE [0] bindFoldM #-}

returnFoldM :: Monad m => a -> m a
returnFoldM = return
{-# INLINE [0] returnFoldM #-}

{-# RULES
"MonadRightId" forall m . bindFoldM m return = m
 #-}

{-# RULES
"foldrW/buildW" forall
    f z
    (i :: Wrap f b)
    (g :: forall c g .
      (Wrap g c)
      -> (a -> c -> c)
      -> c
      -> c)
    .
  foldrW i f z (buildW g) = g i f z
"foldrW/buildWStatic" forall
    f z
    (i :: Wrap f b)
    (g :: forall c g .
      (Wrap g c)
      -> (a -> c -> c)
      -> c
      -> c)
    .
  foldrW i f z (buildWStatic g) = g i f z
"foldrW/augmentW" forall
    f z
    (i :: forall e. Wrap (f e) (e -> b -> b))
    (g :: forall c g .
      (Wrap g c)
      -> (a -> c -> c)
      -> c
      -> c)
    xs
    .
  foldrW i f z (augmentW g xs) = g i f (foldrW i f z xs)
"foldrW/augmentWStatic" forall
    f z
    (i :: forall e. Wrap (f e) (e -> b -> b))
    (g :: forall c g .
      (Wrap g c)
      -> (a -> c -> c)
      -> c
      -> c)
    xs
    .
  foldrW i f z (augmentWStatic g xs) = g i f (foldrW i f z xs)
"augmentW/buildW" forall
    (f :: forall c g.
      (Wrap g c)
      -> (a -> c -> c)
      -> c
      -> c)
    (g :: forall c g .
      (Wrap g c)
      -> (a -> c -> c)
      -> c
      -> c)
    .
  augmentW g (buildW f) = buildW (\i c n -> g i c (f i c n))
"augmentWStatic/buildW" forall
    (f :: forall c g.
      (Wrap g c)
      -> (a -> c -> c)
      -> c
      -> c)
    (g :: forall c g .
      (Wrap g c)
      -> (a -> c -> c)
      -> c
      -> c)
    .
  augmentWStatic g (buildW f) = buildW (\i c n -> g i c (f i c n))
"augmentW/buildWStatic" forall
    (f :: forall c g.
      (Wrap g c)
      -> (a -> c -> c)
      -> c
      -> c)
    (g :: forall c g .
      (Wrap g c)
      -> (a -> c -> c)
      -> c
      -> c)
    .
  augmentW g (buildWStatic f) = buildW (\i c n -> g i c (f i c n))
"augmentWStatic/buildWStatic" forall
    (f :: forall c g.
      (Wrap g c)
      -> (a -> c -> c)
      -> c
      -> c)
    (g :: forall c g .
      (Wrap g c)
      -> (a -> c -> c)
      -> c
      -> c)
    .
  augmentWStatic g (buildWStatic f) = buildWStatic (\i c n -> g i c (f i c n))
  #-}
