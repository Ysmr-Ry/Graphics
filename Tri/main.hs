{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
import Prelude hiding ((<*>))
import Haste
import Haste.DOM
import Haste.Events
import Haste.Graphics.Canvas
import Control.Monad
import "mtl" Control.Monad.State
import Data.List
import Data.IORef
import Lens.Micro
import Lens.Micro.Mtl
import Text.Printf

type LoopState = ((Double, Double), IORef [Point], IORef Bool)

newtype World a = World { runWorld :: StateT LoopState IO a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadState LoopState)

instance MonadEvent World where
  mkHandler h = World $ do
    s <- get
    lift $ mkHandler $ \v -> let
        World h' = h v
      in void $ execStateT h' s

data Tri = Tri Point Point Point | None
  deriving Show

mkTri :: Point -> Point -> Point -> Tri
mkTri p1 p2 p3
  | abs (b-c) < a+eps && a < b+c+eps = Tri p1 p2 p3
  | otherwise                        = None
  where
    [a,b,c] = edges (Tri p1 p2 p3)

gray :: Color
gray = RGB 40 40 40

eps :: Double
eps = 1e-9

infPt :: Point
infPt = (fi (maxBound :: Int), fi (maxBound :: Int))

main :: IO ()
main = do
  elemById "canvas" >>= \case
    Just cid -> do
      w <- read <$> getProp cid "width"
      h <- read <$> getProp cid "height"
      ptsRef <- newIORef []
      flRef <- newIORef False

      documentBody `onEvent` MouseDown $ \(MouseData (x,y) _ _) -> do
        pts <- readIORef ptsRef

        when (length pts == 3) $ writeIORef ptsRef []
        modifyIORef ptsRef ((fi x, fi y):)

      documentBody `onEvent` KeyDown $ \(KeyData code _ _ _ _) -> do
        when (code == 13) $ modifyIORef flRef not

      fromElem cid >>= \case
        Just cvs -> evalStateT (runWorld $ loop cvs) ((w,h), ptsRef, flRef)
        Nothing  -> error "Canvas could not be found!"
    Nothing  -> error "Canvas ID could not be found!"

loop :: Canvas -> World ()
loop cvs = do
  ((w,h), ptsRef, flRef) <- get
  pts <- liftIO $ readIORef ptsRef
  fl <- liftIO $ readIORef flRef

  render cvs $ do
    forM_ pts $ \p -> do
      color gray $ fill $ circle p 5

    when (length pts >= 2) $ forM_ (zip pts (tail $ pts ++ [head pts])) $ \(p1,p2) -> do
      color gray $ stroke $ line p1 p2

    when (length pts == 3) $ do
      let p1 = pts!!0
          p2 = pts!!1
          p3 = pts!!2
          tri = mkTri p1 p2 p3
          as = angs tri
          [a,b,c] = edges tri
          [s1,s2,s3] = map (sin . (*2)) as
          [t1,t2,t3] = map tan as
          gcs =  [(1,1,1), (s1,s2,s3), (a,b,c), (t1,t2,t3), (-a,b,c), (a,-b,c), (a,b,-c)]
          cs = map (getC tri) gcs
          cols = [gray, RGB 0 255 50, RGB 255 50 0, RGB 0 50 255, RGB 255 200 0, RGB 255 200 0, RGB 255 200 0]
          names = ["G", "O", "I", "H", "I[A]", "I[B]", "I[C]"]

      forM_ (zip cs cols) $ \(ct,c) -> do
        color c $ fill $ circle ct 5

      opacity 1.0 $ lineWidth 2 $ do
        -- outC
        color (cols!!1) $ do
          stroke $ circle (cs!!1) (getR tri)
          when fl $ opacity 0.5 $ stroke $ do
            line (cs!!1) $ (1/2).>(p1+p2)
            line (cs!!1) $ (1/2).>(p2+p3)
            line (cs!!1) $ (1/2).>(p3+p1)

        -- inC
        color (cols!!2) $ do
          stroke $ circle (cs!!2) (getr tri)
          when fl $ opacity 0.5 $ stroke $ do
            line (cs!!2) p1
            line (cs!!2) p2
            line (cs!!2) p3          

        -- exC
        forM_ [4..6] $ \i -> do
          color (cols!!i) $ do
            stroke $ circle (cs!!i) (getr' tri (gcs!!i))

            when fl $ opacity 0.5 $ stroke $ forM_ ((cs!!2): delete (pts!!(i-4)) pts) $ \p -> do
              line (cs!!i) p

        -- Euler Line
        color (RGB 200 0 255) $ stroke $ uncurry line (clippedLine ((0,0),(w,h)) ((cs!!0), (cs!!1)))

        forM_ (zip pts (tail $ pts ++ [head pts])) $ \(p1,p2) -> do
          color gray $ stroke $ uncurry line (clippedLine ((0,0),(w,h)) (p1,p2))

      -- info
      opacity 0.7 $ color gray $ font "20px Ricty Diminished" $ do
        text (5,25) $ show tri
        let infos = [("a,b,c", showD [a,b,c]),
                     ("S", showD (area tri)),
                     ("R", showD (getR tri)), 
                     ("r", showD (getr tri)), 
                     ("r'", showD (map (\i -> getr' tri (gcs!!i)) [4..6])),
                     ("line", show fl)]
            ma = maximum $ map (length . fst) infos ++ map length names
        forM_ (zip [0..] infos) $ \(i,(name,str)) -> do
          text (5,50+fi i*25) $ name ++ ":" ++ replicate (ma+1-length name) ' ' ++ str

        forM_ [0..length cs-1] $ \i -> do
          color (cols!!i) $ text (5,50+fi (length infos)*25+fi i*25) $ names!!i ++ ":" ++ replicate (ma+1-length (names!!i)) ' ' ++ showD (cs!!i)

  setTimer (Once 10) (loop cvs)
  return ()

fi :: (Integral a, Num b) => a -> b
fi = fromIntegral

instance Num (Double, Double) where
  (+) (x1,y1) (x2,y2) = (x1+x2, y1+y2)
  (-) (x1,y1) (x2,y2) = (x1-x2, y1-y2)
  (*) (x1,y1) (x2,y2) = (x1*x2, y1*y2)
  negate (x,y) = (-x,-y)
  abs (x,y) = (sqrt (x*x+y*y), 0)
  signum (x,y) = (x/norm, y/norm)
    where
      norm = sqrt $ x*x+y*y
  fromInteger n = (fi n,0)

infixl 7 <.>
(<.>) :: Point -> Point -> Double
(<.>) (x1,y1) (x2,y2) = x1*x2+y1*y2

infixl 7 <*>
(<*>) :: Point -> Point -> Double
(<*>) (x1,y1) (x2,y2) = x1*y2-y1*x2

infixl 7 .>
(.>) :: Double -> Point -> Point
(.>) a v = (a,a)*v

norm :: Point -> Double
norm = fst . abs

edges :: Tri -> [Double]
edges None           = []
edges (Tri p1 p2 p3) = map norm [p3-p2, p1-p3, p2-p1]

angs :: Tri -> [Double]
angs None           = []
angs (Tri p1 p2 p3) = map acos cs
  where
    getCos p q = p<.>q/(norm p*norm q)
    cs = [getCos (p2-p1) (p3-p1), getCos (p1-p2) (p3-p2), getCos (p1-p3) (p2-p3)]

area :: Tri -> Double
area None           = 0
area (Tri p1 p2 p3) = (p2-p1)<*>(p3-p1)/2

getR :: Tri -> Double
getR tri
  | null as         = 0
  | otherwise       = abs $ head (edges tri)/(2*s)
  where
    as = angs tri
    s = sin $ head as

getr :: Tri -> Double
getr tri = case edges tri of
  []      -> 0
  [a,b,c] -> getr' tri (a,b,c)

getr' :: Tri -> (Double, Double, Double) -> Double
getr' tri (a,b,c) = abs $ 2*area tri/(a+b+c)

getC :: Tri -> (Double, Double, Double) -> Point
getC None _                     = infPt
getC tri@(Tri p1 p2 p3) (a,b,c) = (recip (a+b+c)).>(a.>p1+b.>p2+c.>p3)

clippedLine :: (Point, Point) -> (Point, Point) -> (Point, Point)
clippedLine ((x,y),(w,h)) ((x1,y1),(x2,y2))
  | abs (x1-x2) < eps  = ((x1,y), (x2,h))
  | otherwise          = ((x, f x), (w, f w))
  where
    f x = (y2-y1)/(x2-x1)*(x-x1)+y1

class ShowD a where
  showD :: a -> String

instance ShowD Double where
  showD d = printf "%.2f" d

instance ShowD (Double, Double) where
  showD (d1,d2) = "(" ++ showD d1 ++ "," ++ showD d2 ++ ")"

instance ShowD [Double] where
  showD ds = "[" ++ intercalate "," (map showD ds) ++ "]"