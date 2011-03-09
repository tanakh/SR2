module Codec.SR2.Enumerator (
  test
  ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Data.Bits
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import Data.Enumerator as E
import qualified Data.Enumerator.Binary as EB
import qualified Data.Enumerator.List as EL
import Data.IORef
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Vector.Unboxed.Mutable as MV
import Data.Word
import System.IO

data StateMap =
  StateMap
  { t :: M.Map Int Word32
  , dt :: M.Map Int Word32
  }

newStateMap :: Int -> StateMap
newStateMap n =
  StateMap (M.fromList [ (i, 1`shiftL`31) | i<-[0..n-1]])
           (M.fromList [ (i, 512 `div` (fromIntegral i+2)) | i<-[0..127]])

predict :: StateMap -> Word32 -> Word32
predict sm cxt =
  ((t sm) M.! (fromIntegral cxt)) `shiftR` 20

update :: StateMap -> Word32 -> Bool -> StateMap
update sm cxt y = sm { t = rt }
  where
    n = (t sm M.! fromIntegral cxt) .&. 127
    p = (t sm M.! fromIntegral cxt) `shiftR` 9
    nt | n < 127 = M.update (\i -> Just $ i+1) (fromIntegral cxt) (t sm)
       | otherwise = t sm
    rt = M.update (\i -> Just $ i + (((((if y then 1 else 0) `shiftL` 23) - p) * (dt sm M.! fromIntegral n)) .&. 0xffffff80)) (fromIntegral cxt) nt
                                                             
encoder :: MonadIO m => Int -> E.Enumeratee (Word32, Bool) B.ByteString m a
encoder n = go (newStateMap n) (0 :: Word32) (0xffffffff :: Word32) where
  go sm x1 x2 (E.Continue k) = do
    mnext <- EL.head
    case mnext of
      Nothing -> do
        newStep <- lift $ E.runIteratee $ k $ E.Chunks [B.singleton $ fromIntegral $ x1 `shiftR` 24]
        return newStep
      Just (wcxt, y) -> do
        let cxt = fromIntegral wcxt
        let p = predict sm cxt
        let xmid = x1 + ((x2-x1)`shiftR`12) * p
        (x1, x2) <- return $ if y then (x1, xmid) else (xmid+1, x2)
        let nsm = update sm cxt y
        let loop x1 x2
              | ((x1 `xor` x2) .&. 0xff000000) == 0 =
                  let c = (fromIntegral $ x2 `shiftR` 24) in
                  let (cs, r) = loop (x1 `shiftL` 8) ((x2 `shiftL` 8) + 255) in
                  (c:cs, r)
              | otherwise =
                  ([], (x1, x2))
        (cs, (x1, x2)) <- return $ loop x1 x2
        newStep <- lift $ E.runIteratee $ k $ E.Chunks [B.pack cs]
        go nsm x1 x2 newStep

  go sm x1 x2 step =
    return step

data Decoder =
  Decoder
  { d_x1, d_x2, d_x :: Word32
  , d_sm :: StateMap
  }

newDecoder :: MonadIO m => Int -> E.Iteratee B.ByteString m (Word32 -> E.Iteratee B.ByteString m Bool)
newDecoder n = do
  cs <- EB.take 4
  let x = BL.foldl (\acc c -> (acc `shiftL` 8) + fromIntegral c) (0 :: Word32) cs
  r <- liftIO $ newIORef (Decoder 0 0xffffffff (fromIntegral x) (newStateMap n))
  return $ f r
  where
    f r cxt = do
      -- liftIO $ print ("cxt", cxt)
      e <- liftIO $ readIORef r
      let p = predict (d_sm e) cxt
      let x1 = d_x1 e
      let x2 = d_x2 e
      let x = d_x e
      let xmid = x1 + ((x2-x1)`shiftR`12)*fromIntegral p
      let y = x<=xmid
      (x1, x2) <- return $ if y then (x1, xmid) else (xmid+1, x2)
      let nsm = update (d_sm e) cxt y
      -- liftIO $ print (x1, x2)
      let loop x1 x2 x
            | (x1`xor`x2).&.0xff000000 /= 0 = return (x1, x2, x)
            | otherwise = do
              mc <- EB.head
              let c = fromMaybe 255 mc
              loop (x1`shiftL`8) ((x2`shiftL`8)+255) ((x`shiftL`8)+fromIntegral c)
      (x1, x2, x) <- loop x1 x2 x
      liftIO $ writeIORef r $ Decoder x1 x2 x nsm
      return y

compress :: MonadIO m => E.Enumeratee B.ByteString (Word32, Bool) m a
compress step = do
  t4 <- liftIO $ MV.replicate 0x100000 (0 :: Word32)
  go (0 :: Word32) (0 :: Word32) t4 step
    
  where
    go c1 h t4 (E.Continue k) = do
      r <- liftIO $ MV.read t4 (fromIntegral (h :: Word32))
      let cxt = if r>=0x4000000 then 1024+(r`shiftR`24) else c1 .|. ((r`shiftR`16) .&. 0x3f00)
      cxt <- return $ cxt * 258
      
      mc <- EB.head
      case mc of
        Nothing -> do
          newStep <- lift $ E.runIteratee $ k $ E.Chunks $ [(cxt, True), (cxt+1, False)] ++ encode (cxt+2) (r .&. 0xff)
          return newStep
        Just c -> do
          let comp3 = (fromIntegral c * 0x10101) `xor` r
          newStep <- case comp3 of
            _ | (comp3 .&. 0xff) == 0 -> do
              newStep <- lift $ E.runIteratee $ k $ E.Chunks [(cxt, False)]
              when (r<0x3f000000) $ liftIO $ do
                a <- liftIO $ MV.read t4 (fromIntegral h)
                liftIO $ MV.write t4 (fromIntegral h) $ a+0x1000000
              return newStep
            _ | (comp3 .&. 0xff00) == 0 -> do
              newStep <- lift $ E.runIteratee $ k $ E.Chunks [(cxt, True), (cxt+1, True), (cxt+2, False)]
              liftIO $ MV.write t4 (fromIntegral h) $ (r.&.0xff0000).|.((r`shiftL`8).&.0xff00).|.fromIntegral c.|.0x1000000
              return newStep
            _ | (comp3 .&. 0xff0000) == 0 -> do
              newStep <- lift $ E.runIteratee $ k $ E.Chunks [(cxt, True), (cxt+1, True), (cxt+2, True)]
              liftIO $ MV.write t4 (fromIntegral h) $ ((r`shiftL`8).&.0xffff00).|.fromIntegral c.|.0x1000000
              return newStep
            _ -> do
              newStep <- lift $ E.runIteratee $ k $ E.Chunks $ [(cxt, True), (cxt+1, False)] ++ encode (cxt+2) (fromIntegral c)
              liftIO $ MV.write t4 (fromIntegral h) $ ((r`shiftL`8).&.0xffff00).|.fromIntegral c
              return newStep
          go (fromIntegral c) ((h*(5`shiftL`5)+fromIntegral c+1).&.0xfffff) t4 newStep
    go _ _ _ step =
      return step
    
    encode :: Word32 -> Word32 -> [(Word32, Bool)]
    encode cxt c = h ++ l where
      b = (c `shiftR` 4) + 16
      h = [ (cxt+1,            ifb $ b`shiftR`3)
          , (cxt+(b`shiftR`3), ifb $ b`shiftR`2)
          , (cxt+(b`shiftR`2), ifb $ b`shiftR`1)
          , (cxt+(b`shiftR`1), ifb $ b )]
      
      ncxt = cxt + 15*(b-15)
      nb = (c .&. 15) .|. 16
      l = [ (ncxt+1,             ifb $ nb`shiftR`3)
          , (ncxt+(nb`shiftR`3), ifb $ nb`shiftR`2)
          , (ncxt+(nb`shiftR`2), ifb $ nb`shiftR`1)
          , (ncxt+(nb`shiftR`1), ifb $ nb )]
          
    ifb n = n.&. 1 == 1

c2w :: Word8 -> Word32
c2w = fromIntegral

decode e cxt = do
  let hi=1
      lo=1
  
  hi <- (hi+) . (hi+) . b2i <$> e (cxt+hi)
  hi <- (hi+) . (hi+) . b2i <$> e (cxt+hi)
  hi <- (hi+) . (hi+) . b2i <$> e (cxt+hi)
  hi <- (hi+) . (hi+) . b2i <$> e (cxt+hi)
  
  cxt <- return $ cxt + 15*(hi-15)
  lo <- (lo+) . (lo+) . b2i <$> e (cxt+lo)
  lo <- (lo+) . (lo+) . b2i <$> e (cxt+lo)
  lo <- (lo+) . (lo+) . b2i <$> e (cxt+lo)
  lo <- (lo+) . (lo+) . b2i <$> e (cxt+lo)
  
  return $ ((hi-16)`shiftL`4).|.(lo-16)

b2i True = 1
b2i False = 0

decompress :: MonadIO m => Int -> E.Enumeratee B.ByteString B.ByteString m a
decompress n step = do
  e <- newDecoder n
  t4 <- liftIO $ MV.replicate 0x100000 (0 :: Word32)
  go e (0 :: Word32) (0 :: Word32) t4 step
  where
    go e c1 h t4 (E.Continue k) = do
      r <- liftIO $ MV.read t4 (fromIntegral h)
      let cxt = if r>=0x4000000 then 1024+(r`shiftR`24) else c1 .|. ((r`shiftR`16).&.0x3f00)
      cxt <- return $ cxt * 258
      -- liftIO $ print ("go", cxt, r, c1)
      
      b1 <- e cxt
      mc1 <- if b1
        then do
        b2 <- e (cxt+1)
        if b2
          then do
          b3 <- e (cxt+2)
          if b3
            then do
            let c1 = (r`shiftR`16).&.0xff
            liftIO $ MV.write t4 (fromIntegral (h :: Word32)) ((r`shiftL`8).&.0xffff00.|.c1.|.0x1000000)
            return $ Just c1
            else do
            let c1 = (r`shiftR`8).&.0xff
            liftIO $ MV.write t4 (fromIntegral h) (r.&.0xff0000.|.(r`shiftL`8).&.0xff00.|.c1.|.0x1000000)
            return $ Just c1
          else do
          c1 <- decode e (cxt+2)
          if c1==r.&.0xff
            then return Nothing
            else do
            liftIO $ MV.write t4 (fromIntegral h) ((r`shiftL`8).&.0xffff00.|.c1)
            return $ Just c1
        else do
        let c1 = r.&.0xff
        when (r<0x3f000000) $ do
          liftIO $ do
            a <- MV.read t4 (fromIntegral h)
            MV.write t4 (fromIntegral h) $ a + 0x1000000
        return $ Just c1
      
      -- liftIO $ print mc1
      
      case mc1 of
        Nothing ->
          return $ E.Continue k
        Just c1 -> do
          nextStep <- lift $ E.runIteratee $ k $ E.Chunks [B.pack [toEnum $ fromIntegral c1]]
          h <- return $ (h*(5`shiftL`5)+c1+1).&.0xfffff
          go e c1 h t4 nextStep

    go _ _ _ _ step =
      return step

test :: FilePath -> IO ()
test fp = do
  -- h <- openFile "output" WriteMode
  -- E.run_ $ EB.enumFile fp $$ joinI $ compress $$ joinI $ encoder ((1024+64)*258) $$ EB.iterHandle h
  -- hClose h
  
  -- E.run_ $ EB.enumFile "input" $$ joinI $ compress $$ joinI $ encoder ((1024+64)*258) $$ E.printChunks True

  -- E.run_ $ EB.enumFile fp $$ joinI $ compress $$ E.printChunks False
  
  -- E.run_ $ EB.enumFile "output" $$ joinI $ decompress ((1024+64)*258) $$ E.printChunks True
  
  h <- openFile "decoded" WriteMode
  E.run_ $ EB.enumFile "output" $$ joinI $ decompress ((1024+64)*258) $$ EB.iterHandle h
  hClose h

