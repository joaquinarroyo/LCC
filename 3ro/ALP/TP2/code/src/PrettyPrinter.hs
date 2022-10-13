module PrettyPrinter
  ( printTerm
  , printTermUN
  , render
  , ppLamTerm
  )
where

import           Common
import           Text.PrettyPrint.ANSI.Leijen
import           Prelude                 hiding ( (<>) )

-- lista de posibles nombres para variables
vars :: [String]
vars =
  [ c : n | n <- "" : map show [1 ..], c <- ['x', 'y', 'z'] ++ ['a' .. 'w'] ]

parensIf :: Bool -> Doc -> Doc
parensIf True  = parens
parensIf False = id

-- pp used fresh term
pp :: [String] -> [String] -> Term -> Doc
pp used _  (Bound k         ) = text (used !! k)
pp _    _  (Free  (Global s)) = text s
pp used vs (i :@: c         ) = sep
  [ parensIf (isLam i) (pp used vs i)
  , nest 1 (parensIf (isLam c || isApp c) (pp used vs c))
  ]
                                  -- el chequeo por isLam no es necesario pero queda bien
pp used vs (Lam c) =
  let x = head vs in text "λ" <> text x <> plambda (x : used) (tail vs) c

plambda :: [String] -> [String] -> Term -> Doc
plambda used vs (Lam c) =
  let x = head vs in text " " <> text x <> plambda (x : used) (tail vs) c
plambda used vs c = text ". " <> pp used vs c

isLam :: Term -> Bool
isLam (Lam _) = True
isLam _       = False

isApp :: Term -> Bool
isApp (_ :@: _) = True
isApp _         = False

fv :: Term -> [String]
fv (Bound _         ) = []
fv (Free  (Global n)) = [n]
fv (t :@: u         ) = fv t ++ fv u
fv (Lam c           ) = fv c

--
printTerm :: Term -> Doc
printTerm t = pp [] (filter (\v -> v `notElem` fv t) vars) t


-- Robado de GLambda https://github.com/goldfirere/glambda/

-- | A function that changes a 'Doc's color
type ApplyColor = Doc -> Doc

-- | Information about coloring in de Bruijn indexes and binders
data Coloring = Coloring [ApplyColor] [ApplyColor]
 -- ^ a stream of the colors used for bound variables,
 -- and the remaining colors to use.

-- | A 'Coloring' for an empty context
defaultColoring :: Coloring
defaultColoring = Coloring [] all_colors
  where all_colors = red : green : yellow : blue : magenta : cyan : all_colors

ppUN :: Coloring -> Term -> Doc
ppUN (Coloring used _) (Bound k) = used !! k $ (text "#" <> int k)
ppUN ((Coloring _ _)) (Free (Global s)) = text s
ppUN col (i :@: c) = sep
  [ parensIf (isLam i) (ppUN col i)
  , nest 1 (parensIf (isLam c || isApp c) (ppUN col c))
  ]
                                  -- el chequeo por isLam no es necesario pero queda bien
ppUN (Coloring used fresh) (Lam c) =
  let col = head fresh
  in  col (text "λ") <+> ppUN (Coloring (col : used) (tail fresh)) c

printTermUN :: Term -> Doc
printTermUN = ppUN defaultColoring

render :: Doc -> String
render = flip displayS "" . renderPretty 0.5 80