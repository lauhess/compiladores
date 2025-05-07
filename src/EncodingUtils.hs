module EncodingUtils(Byte, int2bs, bs2int, skipBs) where
import Data.Binary
import Data.Bits

{-
  Módulo que provee funciones para la codificación y decodificación de enteros
  en el formato LEB128 para unsigned integers de 32 bits.
  Usaremos esto para poder representar los enteros de 32 bits con el bytecode de 8 bits.
  Esta codificación consiste en representar los enteros mediante una secuencia de bytes
  donde cada byte usa los 7 bits menos significativos para representar un fragmento del entero
  y el bit más significativo para indicar si hay más bytes en la secuencia.
  Por ejemplo, el entero 265 se representa con los bytes:
    [0x81, 0x02] = [0b1000 0001, 0b0000 0010]
                      ⮝           ⮝
-}

type Byte = Word8

-- Constantes comunes
mask :: Int
mask = 0x7F  -- 0111 1111

cont :: Word8
cont = 0x80  -- 1000 0000

-- Codificación: Convierte un entero en una secuencia de bytes LEB128.
int2bs :: Int -> [Byte]
int2bs x 
  | x < 0x80  = [fromIntegral x]
  | otherwise = (fromIntegral (x .&. mask) .|. cont) : int2bs (x `shiftR` 7)

-- Decodificación: Convierte una secuencia de bytes LEB128 en un entero de 32 bits 
-- y devolviendo el resto de la cadena de bytes
bs2int :: [Byte] -> (Int, [Byte])
bs2int = decodeBs 0 0
  where
    -- Aplica la máscara y desplaza el valor a la posición indicada.
    applyMask :: Byte -> Int -> Int
    applyMask x = shiftL (fromIntegral x .&. mask)
    -- applyMask = flip shiftL . ((.&.) mask . fromIntegral)

    -- Combina el acumulador con el valor procesado del byte actual.
    combine :: Int -> Byte -> Int -> Int
    combine acc x shift' = acc .|. applyMask x shift'

    decodeBs :: Int -> Int -> [Byte] -> (Int, [Byte])
    decodeBs acc _ [] = (acc, [])
    decodeBs acc shift' (x:xs) =
      if x .&. cont == 0
        then ( combine acc x shift', xs )
        else decodeBs ( combine acc x shift' ) (shift' + 7) xs



skipBs :: [Byte] -> ([Byte], [Byte])
skipBs [] = ([], [])
skipBs (y:ys) = 
  if y .&. cont == 0 
  then ([y], ys)
  else let (skipped, rest) = skipBs ys in (y:skipped, rest)