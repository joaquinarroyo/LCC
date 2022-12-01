import Control.Monad (liftM, ap)
import Control.Applicative (Applicative(..))

newtype Writer w a = Writer { runWriter :: (a, [w]) }

instance Functor (Writer w) where
    fmap = liftM

instance Applicative (Writer w) where
    pure  = return
    (<*>) = ap

instance Monad (Writer w) where
    return x = Writer (x, [])
    (Writer (a, w)) >>= k  = let (a', w') = runWriter (k a)
                             in Writer (a', w ++ w')

--- Examen Parcial 3 2018
-- 1 b)
newtype WriterMaybe w a = WM { runWM :: (Maybe a,  [w]) }

instance Functor (WriterMaybe w) where
    fmap = liftM

instance Applicative (WriterMaybe w) where
    pure  = return
    (<*>) = ap

instance Monad (WriterMaybe w) where
    return x = WM (Just x, [])
    m >>= k  = case runWM m of
                (Nothing, w) -> WM (Nothing, w)
                (Just x, w)  -> let (y, w') = runWM (k x)
                                in WM (y, w ++ w')
-- 1 c)
fail :: WriterMaybe e a
fail = WM (Nothing, [])

tell :: [w] -> WriterMaybe w ()
tell xs = WM (Just (), xs)


-- 1 d)
type Rule = String
type Packet = String

data Result = Accepted | Rejected deriving (Show, Eq)

-- aca da igual la condicion para el matcheo, es solo para probar
match :: [Rule] -> Packet -> [(Rule, Result)]
match [] p = []
match (r:rs) p = case r of
    "ACCEPT" -> (r, Accepted) : match rs p
    "REJECT" -> (r, Rejected) : match rs p
    _        -> match rs p

rules = ["ACCEPT", "ACCEPT"]
rules2 = ["ASddas", "Dsadsa"]
packet = "paquete 1"

filterPacket :: [Rule] -> Packet -> WriterMaybe Char Packet
filterPacket rules packet = case match rules packet of
    [] -> do tell ("No rules matched with " ++ packet)
             Main.fail -- en hoja pones fail y listo
    xs -> do mapM (f packet) xs
             return packet
    where f p (r, Accepted) = tell ("Rule " ++ r ++ " accepted packet " ++ p ++ "||")
          f p (r, Rejected) = do tell ("Rule " ++ r ++ " rejected packet " ++ p)
                                 Main.fail

filterPacket' :: [Rule] -> Packet -> (Maybe Packet, [Char])
filterPacket' rules packet = runWM (filterPacket rules packet)

-- 2)

data T a = Uno a | Dos (a, a) | More (a, a) (T a) deriving Show

instance Functor T where
    fmap f (Uno a) = (Uno (f a))
    fmap f (Dos (a, b)) = (Dos (f a, f b))
    fmap f (More (a, b) c) = (More (f a, f b) (fmap f c))


{- 

fmap id (Uno x) =
= (Uno (id x)) =
= Uno x =
= id (Uno x)

fmap id (Dos (x, y)) =
= (Dos (id x, id y)) =
= (Dos (x, y)) =
= id (Dos (x, y))

fmap id (More (x, y) c) =
= More (id x, id y) (fmap f c) = {H.I}
= More (x, y) c =
= id (More (x, y) c)

((fmap f) . (fmap g)) (Uno x) =
= fmap f (fmap g (Uno x)) =
= fmap f (Uno (g x)) =
= Uno (f (g x)) =
= Uno ((f . g) x) =
= fmap (f. g) (Uno x)

((fmap f) . (fmap g)) (Dos (x, y)) =
= fmap f (fmap g (Dos (x, y))) =
= fmap f (Dos (g x, g y)) =
= Dos (f (g x), f (g y)) =
= Dos ((f. g) x, (f. g) y) =
= fmap (f. g) (Dos (x, y))

((fmap f) . (fmap g)) (More (x, y) c) =
= fmap f (fmap g (More (x, y) c)) =
= fmap f (More (g x, g y) (fmap g c)) =
= More (f (g x), f (g y), (fmap f (fmap g c))) =
= More (f (g x), f (g y), (fmap f . fmap g) c) = {H.I}
= More (f (g x), f (g y), (fmap (f. g) c)) =
= More ((f. g) x, (f. g) (fmap (f. g) c)) =
= fmap (f. g) (More (x, y) c)

-}

