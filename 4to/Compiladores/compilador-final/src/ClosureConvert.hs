module ClosureConvert (
  runCC,
  ccWrite
)
where

import IR
import Control.Monad.State
import Control.Monad.Writer
import Subst
import Lang

-- |
runCC :: [Decl TTerm] -> IrDecls
runCC decls = let ((ir, _), irs) = runWriter $ runStateT (mapM ccDecl decls) 0
              in IrDecls (irs ++ ir)

-- |
ccDecl :: Decl TTerm -> StateT Int (Writer [IrDecl]) IrDecl
ccDecl (Decl _ name ty t) = IrVal name (getIrTy ty) <$> closureConvert t

-- |
ccWrite :: String -> FilePath -> IO ()
ccWrite p filename = writeFile filename p

-- |
getVarName :: Name -> StateT Int (Writer [IrDecl]) Name
getVarName n = do
  i <- get
  put (i+1)
  return $ n ++ "_" ++ show i

-- |
var2ir :: Var -> Ir
var2ir (Free name) = IrVar name
var2ir (Global name)  = IrGlobal name
var2ir (Bound _) = undefined

-- |
getIrTy :: Ty -> IrTy
getIrTy (NatTy _) = IrInt
getIrTy (FunTy _ _ _) = IrFunTy
getIrTy (SynTy _) = undefined

-- |
replaceFreeVars :: [(Name, Ty)] -> Name -> Ir -> Ir
replaceFreeVars = replaceFreeVars' 1
  where
    replaceFreeVars' :: Int -> [(Name, Ty)] -> Name -> Ir -> Ir
    replaceFreeVars' _ [] _ t' = t'
    replaceFreeVars' i ((x, ty):xs) clo t' = IrLet x (getIrTy ty) (IrAccess (IrVar clo) (getIrTy ty) i) (replaceFreeVars' (i + 1) xs clo t')

-- | Conversion de clausura
closureConvert :: TTerm -> StateT Int (Writer [IrDecl]) Ir
closureConvert (V i v) = return $ var2ir v
closureConvert (Const i c) = return $ IrConst c
closureConvert (BinaryOp i op t1 t2) = do
  t1' <- closureConvert t1
  t2' <- closureConvert t2
  return $ IrBinaryOp op t1' t2'
closureConvert (IfZ i t1 t2 t3) = do
  t1' <- closureConvert t1
  t2' <- closureConvert t2
  t3' <- closureConvert t3
  return $ IrIfZ t1' t2' t3'
closureConvert (Let i n ty t1 scope@(Sc1 t)) = do
  var <- getVarName n
  t1' <- closureConvert t1
  t' <- closureConvert (open var scope)
  return $ IrLet var (getIrTy ty) t1' t'
closureConvert (Print i s t) =  do
  t' <- closureConvert t
  var <- getVarName "print"
  return $ IrLet var IrInt t' (IrPrint s (IrVar var))
closureConvert (App i t1 t2) = do
  clos <- closureConvert t1
  t2' <- closureConvert t2
  fun <- getVarName "fun"
  return $ IrLet fun IrClo clos $ IrCall (IrAccess (IrVar fun) IrClo 0) [IrVar fun, t2'] IrInt
closureConvert (Lam (_, fty) n ty scope@(Sc1 t)) = do
  var <- getVarName ("f" ++ n)
  clos <- getVarName "clos"
  let freeVs = freeVarsWithTy t
  body <- closureConvert (open var scope)
  tell [IrFun var (getIrTy fty) [(clos, IrClo), (var, getIrTy ty)] (replaceFreeVars freeVs clos body)]
  return $ MkClosure var (map (IrVar . fst) freeVs)
closureConvert (Fix i n1 ty1 n2 ty2 scope@(Sc2 t)) = do
  var <- getVarName ("fix_" ++ n1 ++ "_" ++ n2)
  clos <- getVarName "fixClos"
  let freeVs = freeVarsWithTy t
  body <- closureConvert (open2 n1 n2 scope)
  tell [IrFun var (getIrTy ty1) [(clos, IrClo), (n2, getIrTy ty2)] (IrLet n1 (getIrTy ty1) (IrVar clos) (replaceFreeVars freeVs clos body))]
  return $ MkClosure var (map (IrVar . fst) freeVs)