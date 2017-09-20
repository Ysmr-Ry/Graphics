{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
import Haste
import Haste.DOM
import Haste.Events
import Haste.Graphics.Canvas
import Haste.Foreign (ffi)
import Control.Applicative
import Control.Monad
import "mtl" Control.Monad.State
import Data.Complex
import Data.IORef
import Lens.Micro
import Lens.Micro.Mtl
import Numeric.FFT
import System.Random

type LoopState = ((Double, Double), ([Complex Double], [Complex Double]), (Int, [Bool]), (IORef Bool, Bool))

newtype World a = World { runWorld :: StateT LoopState IO a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadState LoopState)

instance MonadEvent World where
  mkHandler h = World $ do
    s <- get
    lift $ mkHandler $ \v -> let
        World h' = h v
      in void $ execStateT h' s

fftSize :: Int
fftSize = 256

scaleR :: Double
scaleR = 200

main :: IO ()
main = do
  elemById "canvas" >>= \case
    Just cid -> do
      w <- read <$> getProp cid "width"
      h <- read <$> getProp cid "height"
      rands <- replicateM (fftSize`div`2) randomIO
      enterF <- newIORef False

      document `onEvent` KeyDown $ \(KeyData code _ _ _ _) -> do
        when (code==13) $ modifyIORef enterF not

      let sqWavd = map (sqWav . (:+0) . fi) [0..fftSize-1]

      fromElem cid >>= \case
        Just cvs -> evalStateT (runWorld $ loop cvs) ((w,h), (sqWavd, take (fftSize`div`2) $ fft sqWavd), (0, rands), (enterF, True))
        Nothing  -> error "Canvas could not be found!"
    Nothing  -> error "Canvas ID could not be found!"

loop :: Canvas -> World ()
loop cvs = do
  ((w,h),(fd,ffd),(p,rands),(enterF,micF)) <- get
  let org = (w/2,h/2)
      fdL = _2._1
      ffdL = _2._2
      pL = _3._1
      micFL = _4._2
  
  when (not micF) $ do
    mics <- liftIO $ map (:+0) <$> getMic
    fdL .= take fftSize mics
    
  (_,(fd,_),_,_) <- get
      
  render cvs $ translate org $ do
    forM_ (zip [0..] (zip fd (tail fd))) $ \(i,(pf:+_,f:+_)) -> do
      color (RGB 0 255 128) $ lineWidth 3 $ stroke $ line (w/2*i/fi fftSize,scaleR*pf) (w/2*(i+1)/fi fftSize,scaleR*f)
    resP <- (\f -> foldM f (-w/4,0) (zip [0..] ffd)) $ \pt@(x,y) (i,c) -> do
      let r = magnitude c
          ang = phase c
          dr = r/fi fftSize*scaleR*2

      when (dr >= 2) $ color (RGB 40 40 40) $ do
        lineWidth 2 $ stroke $ circle pt dr
      return $ (x+(if rands!!i then 1 else -1)*dr*cos (2*pi*fi i*fi p/fi fftSize+ang+pi/2), y+dr*sin (2*pi*fi i*fi p/fi fftSize+ang+pi/2))

    opacity 0.5 $ color (RGB 0 255 128) $ lineWidth 3 $ stroke $ line resP (0,scaleR*realPart (head fd))
    color (RGB 0 255 128) $ fill $ circle resP 3
    color (RGB 0 255 128) $ fill $ circle (0,scaleR*realPart (head fd)) 3

    font "30px ヒラギノ角ゴ" $ text (-w/2+20,-h/2+50) $ "Microphone: " ++ if micF then "Off" else "On"

  when (not micF) $ do
    pL .= 0
    ffdL .= take (fftSize`div`2) (fft fd)

  enter <- liftIO $ readIORef enterF
  when enter $ do
    micFL .= not micF
    liftIO $ writeIORef enterF False

  when micF $ do
    fdL .= rot 1 fd
    (_,_,(p,_),_) <- get
    pL .= (p+1) `mod` fftSize

  setTimer (Once 10) (loop cvs)
  return ()

sqWav :: Floating a => a -> a
sqWav x = sum $ take 32 $ map (\i -> sin (2*pi*fi i*x/fi fftSize)/fi i) [1,3..]

rot :: Int -> [a] -> [a]
rot n xs = drop n xs ++ take n xs

getMic :: IO [Double]
getMic = ffi $ toJSString "(function(){ return dat; })"

fi :: (Integral a, Num b) => a -> b
fi = fromIntegral