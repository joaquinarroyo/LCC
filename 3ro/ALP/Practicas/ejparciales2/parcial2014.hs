import Control.Monad (liftM, ap)
import Control.Applicative (Applicative(..))

data Type v = TVar v | TInt | Func (Type v) (Type v)

instance Functor Type where
    fmap f (TVar x) = TVar (f x)
    fmap f TInt = TInt
    fmap f (Func x y) = Func (fmap f x) (fmap f y)

instance Applicative Type where
    pure  = return
    (<*>) = ap

instance Monad Type where
    return x = TVar x
    TVar x >>= f = f x
    TInt >>=f = TInt
    Func x y >>= f = Func (x >>= f) (y >>= f)

apply :: (a -> Type b) -> Type a -> Type b
apply f t = t >>= f

comp :: (a -> Type b) -> (c -> Type a) -> (c -> Type b)
comp f g = \y -> g y >>= \x -> f x

(>>>) :: Eq v => v -> Type v -> (v -> Type v)
v >>> t = \x -> if x == v then t else return x

esta :: Eq v => v -> Type v -> Bool
esta v (TVar x) = v == x
esta v (Func x y) = esta v x || esta v y
esta v TInt = False

varBind :: Eq v => v -> Type v -> Maybe (v -> Type v)
varBind v t = if esta v t then Just (v >>> t) else Nothing

unify :: Type v -> Type v -> Maybe (v -> Type v)
unify t1 t2 = case (t1, t2) of
                (TVar x, TVar y) -> if x == y then Just id else Just (x >>> t2)
                (TVar x, _) -> varBind x t2
                (_, TVar x) -> varBind x t1
                (Func x y, Func x' y') -> do f <- unify x x'
                                             g <- unify (apply f y) (apply f y')
                                             return (f . g)
                (_, _) -> if t1 == t2 then Just id else Nothing


