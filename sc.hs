import Data.Maybe
import Data.List
import Data.Either
import Debug.Trace
import Control.Applicative

type Id = String

data Expr = Var Id
          | Lam Id Expr
          | App Expr Expr
          | Cons Id [Expr]
          | Let Expr Id Expr
          | Fun Id
          | Case Expr [(Pattern, Expr)]
            deriving Eq

data Pattern = Pattern Id [Id]
               deriving (Eq)

type Program = (Expr, [(Id, Expr)])

data Tree = Node Expr [Edge]
            deriving (Show, Eq)

data Edge = Simple Tree
          | Fold Expr [(Id, Id)]
          | CaseBranch Tree Pattern
            deriving (Show, Eq)

instance Show Expr where
  show (Var x) = x
  show (Lam x e) = "λ" ++ x ++ " " ++ (show e)
  show (App e1 e2) = (show e1) ++ " @ " ++ (show e2)
  show (Cons t es) = t ++ "(" ++ (intercalate ", " (map show es)) ++ ")"
  show (Let e1 x e2) = "let " ++ x ++ " = " ++ (show e1) ++ " in " ++ (show e2)
  show (Fun f) = f
  show (Case e ps) = "case " ++ (show e) ++ " of\n\t" ++ (intercalate "\n\t" (map show ps))

instance Show Pattern where
  show (Pattern t ids) = t ++  "(" ++ (intercalate ", " ids) ++ ")"

subst :: Expr -> Id -> Expr -> Expr
subst (Var y) x e
  | x == y = e
  | otherwise = Var y
subst (Lam y e1) x e
  | x == y = (Lam y e1)
  | otherwise = Lam y (subst e1 x e)
subst (App e1 e2) x e = App (subst e1 x e) (subst e2 x e)
subst (Cons t gs) x e = Cons t (map (\g -> subst g x e) gs)
subst (Let e1 y e2) x e = Let (subst e1 x e) y (subst e2 x e)
subst (Fun f) _ _ = Fun f
subst (Case e1 pats) x e = Case (subst e1 x e) (map (\p -> subst_pat p x e) pats)

subst_pat :: (Pattern, Expr) -> Id -> Expr -> (Pattern, Expr)
subst_pat (p@(Pattern t ps), e1) x e
 | any (== x) ps = (p, e1)
 | otherwise = (p, subst e1 x e)

subst_list :: Expr -> [(Id, Expr)] -> Expr
subst_list e ss = foldl (\e1 (x, e2) -> subst e1 x e2) e ss

is_value :: Expr -> Bool
is_value (Var _) = True
is_value (Lam _ _) = True
is_value (Cons _ es) = all is_value es
is_value (App (Lam _ _) _) = False
is_value (App e _) = is_value e
is_value _ = False

free_var_pat :: (Pattern, Expr) -> [Id]
free_var_pat ((Pattern _ ids), e) = (free_var e) \\ ids

free_var :: Expr -> [Id]
free_var (Fun _) = []
free_var (Var x) = [x]
free_var (Cons _ es) = foldr union [] (map free_var es)
free_var (Lam x e) = (free_var e) \\ [x]
free_var (App e1 e2) = union (free_var e1) (free_var e2)
free_var (Let e1 x e2) = union ((free_var e2) \\ [x]) (free_var e1)
free_var (Case e ps) = union (free_var e) (foldr union [] (map free_var_pat ps))

all_var_pat :: (Pattern, Expr) -> [Id]
all_var_pat ((Pattern _ ids), e) = (all_var e) ++ ids

all_var :: Expr -> [Id]
all_var (Fun _) = []
all_var (Var x) = [x]
all_var (Cons _ es) = foldr union [] (map all_var es)
all_var (Lam x e) = (x:(all_var e))
all_var (App e1 e2) = union (all_var e1) (all_var e2)
all_var (Let e1 x e2) = union ((all_var e2) ++ [x]) (all_var e1)
all_var (Case e ps) = union (all_var e) (foldr union [] (map all_var_pat ps))

fix_id :: [Id] -> Id -> Id
fix_id bs id = if elem id bs then fix_id bs (id ++ "'") else id

rename_pat :: [Id] -> (Pattern, Expr) -> (Pattern, Expr)
rename_pat bs ((Pattern t ids), e) = let fixed_ids = map (fix_id bs) ids in
                                     ((Pattern t fixed_ids), (subst_list e (zip ids (map Var fixed_ids))))

rename :: [Id] -> Expr -> Expr
rename _ e@(Fun _) = e
rename _ e@(Var _) = e
rename bs (Cons t es) = Cons t (map (rename bs) es)
rename bs (Lam x e) = Lam x (rename bs e)
rename bs (App e1 e2) = App (rename bs e1) (rename bs e2)
rename bs (Let e1 x e2) = Let (rename bs e1) x (rename bs e2)
rename bs (Case e ps) = Case (rename bs e) (map (rename_pat bs) ps)

closure :: Expr -> Expr
closure e = let free = free_var e in foldl (\ e1 x -> Lam x e1) e free

match :: Id -> Int -> (Pattern, Expr) -> Bool
match t1 n (Pattern t2 xs, _) = t1 == t2 && n == (length xs)

equal_pats :: (Pattern, Expr) -> (Pattern, Expr) -> Bool
equal_pats (Pattern t1 xs1, _) (Pattern t2 xs2, _) = t1 == t2 && length xs1 == length xs2 &&
                                                         all (\(a,b) -> a == b) (zip xs1 xs2)

eval_step_cons :: [(Id, Expr)]  -> [Expr] -> [Expr]
eval_step_cons defs [] = []
eval_step_cons defs (x:xs) = if (is_value x) then x:(eval_step_cons defs xs) else (eval_step defs x):xs

eval_step :: [(Id, Expr)] -> Expr -> Expr
eval_step defs (Fun f) = fromJust (lookup f defs)
eval_step defs (App (Lam x e1) e2) = subst e1 x e2
eval_step defs (App e1 e2) = App (eval_step defs e1) e2
eval_step defs (Let e1 x e2) = subst e2 x (eval (e1, defs))
eval_step defs (Cons t es) = Cons t (eval_step_cons defs es)
eval_step defs (Case (Cons t1 es) pats) = let pat = find (match t1 (length es)) pats in case pat of
  Just (Pattern _ xs, e) -> subst_list e (zip xs es)
eval_step defs (Case e pats) = Case (eval_step defs e) pats

eval :: Program -> Expr
eval (e, defs) = if is_value e then e else eval ((eval_step defs e), defs)

decompose :: Expr -> Maybe (Expr -> Expr, Expr)
decompose (Fun f) = if f == ">" then Nothing else Just (id, Fun f)
decompose (Case e1 ps) = ((\(f, e2) -> ((flip Case ps) . f, e2)) <$> decompose e1) <|> Just (id, Case e1 ps)
decompose (Lam x e) = (\(f, e2) -> ((Lam x) . f, e2)) <$> decompose e
decompose (App e1 e2) = (\(f, e3) -> ((flip App e2) . f, e3)) <$> decompose e1
decompose e = Nothing

homeo_embed_d :: Expr -> Expr -> Bool
homeo_embed_d e (Cons _ es) = any (homeo_embed e) es
homeo_embed_d e (Lam _ e1) = (homeo_embed e e1)
homeo_embed_d e (App f x) = (homeo_embed e x) || (homeo_embed e f)
homeo_embed_d e (Case e1 pats) = (homeo_embed e e1) || any (\(_,e2) -> homeo_embed e1 e2) pats
homeo_embed_d e1 e2 = e1 == e2

coupling_pat :: ((Pattern, Expr), (Pattern, Expr)) -> Bool
coupling_pat ((Pattern t1 _, e1), (Pattern t2 _, e2)) = t1 == t2 && (homeo_embed e1 e2)

homeo_embed_c :: Expr -> Expr -> Bool
homeo_embed_c (Var _) (Var _) = True
homeo_embed_c (Cons a es1) (Cons b es2) = (a == b) && (length es1 == length es2) && (all (\(x,y) -> homeo_embed x y) (zip es1 es2))
homeo_embed_c (Lam _ e1) (Lam _ e2) = homeo_embed e1 e2
homeo_embed_c (App f1 x1) (App f2 x2) = (homeo_embed f1 f2) && (homeo_embed x1 x2)
homeo_embed_c (Case e1 ps1) (Case e2 ps2) = (length ps1 == length ps2) && (homeo_embed e1 e2) && all coupling_pat (zip ps1 ps2)
homeo_embed_c e1 e2 = e1 == e2

homeo_embed :: Expr -> Expr -> Bool
homeo_embed e1 e2 = (homeo_embed_c e1 e2) || (homeo_embed_d e1 e2)

generalization_functor_list :: Int -> [(Expr, Expr)] -> (Int, [(Expr, [(Id, Expr)], [(Id, Expr)])])
generalization_functor_list cnt [] = (cnt, [])
generalization_functor_list cnt ((e1, e2):es) = let (cnt1, res) = generalization_functor_list cnt es in
                                                let (cnt2, x) = generalization_functor cnt1 e1 e2 in
                                                (cnt2, x:res)

generalization_functor :: Int -> Expr -> Expr -> (Int, (Expr, [(Id, Expr)], [(Id, Expr)]))
generalization_functor cnt (Var x) (Var y)
  | x == y = (cnt, ((Var x), [], []))
generalization_functor cnt (Fun f1) (Fun f2)
  | f1 == f2 = (cnt, ((Fun f1), [], []))
generalization_functor cnt (Cons a es1) (Cons b es2)
  | (a == b) && (length es1 == length es2) = (cnt1, ((Cons a es3), (concat sub1), (concat sub2))) where
           (cnt1, gs) = generalization_functor_list cnt (zip es1 es2)
           (es3, sub1, sub2) = unzip3 gs
generalization_functor cnt (App f1 e1) (App f2 e2) = (cnt2, ((App f3 e3), subf1 ++ sube1, subf2 ++ sube2)) where
           (cnt1, (f3, subf1, subf2)) = generalization_functor cnt f1 f2
           (cnt2, (e3, sube1, sube2)) = generalization_functor cnt1 e1 e2
generalization_functor cnt e1 e2 = (cnt + 1, ((Var v), [(v, e1)], [(v, e2)])) where v = "v" ++ (show cnt)

generalization_subexpr :: (Expr, [(Id, Expr)], [(Id, Expr)]) -> (Expr, [(Id, Expr)], [(Id, Expr)])
generalization_subexpr (e, [], []) = (e, [], [])
generalization_subexpr (e', ((v1, e1):es1'), ((_, e2):es2')) = let (e, es1, es2) = generalization_subexpr (e', es1', es2') in
                                                               let v2' = find ((== e1) . snd) es1 in let v2'' = find ((== e2) . snd) es2 in
                                                               if isJust v2' && isJust v2'' && (fst . fromJust) v2' == (fst . fromJust) v2'' then
                                                               let (v2, _) = fromJust v2' in (subst e v1 (Var v2), es1, es2) else (e, ((v1, e1):es1), ((v1, e2):es2))


generalization :: Int -> Expr -> Expr -> (Int, (Expr, [(Id, Expr)], [(Id, Expr)]))
generalization cnt e1 e2 = let (n, g) = generalization_functor cnt e1 e2 in (n, generalization_subexpr g)

is_trivial :: Expr -> Bool
is_trivial (Var _) = True
is_trivial _ = False

renaming_constraints :: Expr -> Expr -> [Maybe (String, String)]
renaming_constraints (Var x) (Var y) = [Just (x, y)]
renaming_constraints (Lam x e1) (Lam y e2) = renaming_constraints e1 (subst e2 y (Var x))
renaming_constraints (App e1 e2) (App e3 e4) = renaming_constraints e1 e3 ++ renaming_constraints e2 e4
renaming_constraints (Cons t1 es1) (Cons t2 es2)
  | t1 == t2 && length es1 == length es2 = concat (map (\(a,b) -> renaming_constraints a b) (zip es1 es2))
renaming_constraints (Fun f1) (Fun f2)
  | f1 == f2 = []
renaming_constraints (Case e1 ps1) (Case e2 ps2)
  | all (\(a,b) -> equal_pats a b) (zip ps1 ps2) = renaming_constraints e1 e2 ++
                                                 concat (map (\((_,a),(_,b)) -> renaming_constraints a b) (zip ps1 ps2))
renaming_constraints _ _ = [Nothing]

renaming :: Expr -> Expr -> Maybe [(String, String)]
renaming e1 e2 = let constraints' = renaming_constraints e1 e2 in
                 if any isNothing constraints' then Nothing else let constraints = nub $ map fromJust constraints' in
                 let (f, s) = unzip constraints in if (length f == length (nub f) && length s == length (nub s)) then
                 Just (filter (\(x, y) -> not (x == y)) constraints) else Nothing

find_renaming :: [Expr] -> Expr -> Maybe (Expr, [(String, String)])
find_renaming path e = foldl (\a p -> if isJust a then a else let r = renaming e p in
                                      if isJust r then Just (p, fromJust r) else Nothing) Nothing path

concatenate_renamings :: [(String, String)] -> [(String, String)] -> [(String, String)]
concatenate_renamings r1 r2 = unionBy (\(_, s1) (_, s2) -> s1 == s2) r1 r2

find_homeo :: [Expr] -> Expr -> Maybe Expr
find_homeo path e = find (\e' -> homeo_embed_c e' e) path

all_edges :: Tree -> [(Expr, Expr)]
all_edges (Node t []) = []
all_edges (Node t ((CaseBranch c@(Node e _) _):cs)) = (t, e):(all_edges c ++ all_edges (Node t cs))
all_edges (Node t ((Simple c@(Node e _)):cs)) = (t, e):(all_edges c ++ all_edges (Node t cs))
all_edges (Node t ((Fold e r):cs)) = all_edges (Node t cs)

create_let :: Expr -> [(Id, Expr)] -> Expr
create_let e [] = e
create_let e (s:ss) = Let (snd s) (fst s) (create_let e ss)

bottom_gen :: Int -> [(Id, Expr)] -> [Expr] -> Expr -> Either (Int, (Expr, Expr)) Tree
bottom_gen cnt defs path (Let e1 x e2) = fmap (\t -> Node (Let e1 x e2) [Simple (Node e1 []), Simple t]) (bottom_gen cnt defs path e2)
bottom_gen cnt defs path e = build_tree cnt defs path e

try_build_tree :: Int -> [(Id, Expr)] -> [Expr] -> Expr -> Either (Int, (Expr, Expr)) Tree
try_build_tree cnt defs path e
  | Just (par_e, r) <- find_renaming path e = Right (Node e [Fold par_e (concatenate_renamings r (map (\x -> (x, x)) (free_var par_e)))])
  | Just par_e <- find_homeo path e = let (new_cnt, (gen_e, s1, s2)) = generalization cnt e par_e in if is_trivial gen_e
                                      then drive cnt defs path e
                                      else if all (is_trivial . snd) s2 then bottom_gen new_cnt defs path (create_let gen_e s1)
                                      else Left (new_cnt, (par_e, create_let gen_e s2))
  | otherwise = drive cnt defs (e:path) e

build_tree :: Int -> [(Id, Expr)] -> [Expr] -> Expr -> Either (Int, (Expr, Expr)) Tree
build_tree cnt defs path e = case (try_build_tree cnt defs path e) of
  Right tree -> Right tree
  Left (new_cnt, (par_e, gen_e)) -> if (par_e == e) then bottom_gen new_cnt defs path gen_e else Left (new_cnt, (par_e, gen_e))

simplify_step_cons :: [(Id, Expr)] -> [Expr] -> Maybe [Expr]
simplify_step_cons _ [] = Nothing
simplify_step_cons defs (e:es)
  | is_value e = (\es1 -> e:es1) <$> simplify_step_cons defs es
  | otherwise = (\e1 -> e1:es) <$> simplify_step defs e

simplify_step :: [(Id, Expr)] -> Expr -> Maybe Expr
simplify_step defs e@(App (Lam _ _) _) = Just (eval_step defs e)
simplify_step defs (App e1 e2) = (\e3 -> App e3 e2) <$> simplify_step defs e1
simplify_step defs (Cons t es) = (\es1 -> Cons t es1) <$> simplify_step_cons defs es
simplify_step defs e@(Case (Cons _ _) _) = Just (eval_step defs e)
simplify_step defs (Case e pats) = (\e1 -> Case e1 pats) <$> simplify_step defs e
simplify_step defs e = Nothing

simplify :: Program -> Expr
simplify (e, defs) = maybe e (\e1 -> simplify (e1, defs)) (simplify_step defs e)

try_subst :: Pattern -> Expr -> Expr -> Expr
try_subst (Pattern t ids) (Var x) be = subst be x (Cons t (map Var ids))
try_subst _ v e = e

drive :: Int -> [(Id, Expr)] -> [Expr] -> Expr -> Either (Int, (Expr, Expr)) Tree
drive cnt defs path e = case (decompose e) of
  Just (_, Fun _) -> (\e2 -> Node e [Simple e2]) <$> build_tree cnt defs path (simplify (rename (all_var e) (eval_step defs e), defs))
  Just (f, Case e1 ps) -> let e3 = (simplify (e1, defs)) in
                          let cs = map (\(p, be) -> build_tree cnt defs path (simplify ((try_subst p e3 (f be)), defs))) ps in
                          let (cs_left, cs_right) = partitionEithers cs in if not (null cs_left) then Left $ head cs_left else
                          (\e2 -> Node e ((Simple e2):(map (\(c, (p, _)) -> CaseBranch c p) (zip cs_right ps)))) <$>
                          build_tree cnt defs path e3
  Nothing -> Right $ Node e []

super_compile :: Program -> Tree
super_compile (e, defs) = fromRight (error "up-generalization failed") (build_tree 1 defs [] e)

node_to_expr :: [(Expr, (Id, [(Id, Id)]))] -> Tree -> Program
node_to_expr folds (Node e []) = (e, [])
node_to_expr folds (Node ee@(Case _ ps) ((Simple c1):cs))
  | not (null cs) = let (es, defs) = unzip (map (\(CaseBranch c p) -> node_to_expr_or_def folds c) cs) in
                    let (e1, defs1) = node_to_expr_or_def folds c1 in (Case e1 (zip (map (\(CaseBranch _ p) -> p) cs) es), concat defs ++ defs1)
node_to_expr folds (Node (Let e1 x e2) (c1:(Simple c2):[])) = let (e, defs) = node_to_expr_or_def folds c2 in (Let e1 x e, defs)
node_to_expr folds (Node e1 [Fold e2 r]) = let (f, r) = fromJust (lookup e2 folds) in (create_fun_call f (map fst r) (Fun f), [])
node_to_expr folds (Node e [Simple c]) = node_to_expr_or_def folds c

create_body :: Expr -> [Id] -> Expr
create_body e [] = e
create_body e (x:xs) = Lam x (create_body e xs)

create_fun_call :: Id -> [Id] -> Expr -> Expr
create_fun_call f [] e = e
create_fun_call f (x:xs) e = create_fun_call f xs (App e (Var x))

node_to_expr_or_def :: [(Expr, (Id, [(Id, Id)]))] -> Tree -> Program
node_to_expr_or_def folds (Node e cs)
  | Just (f, r) <- lookup e folds = let (e1, defs) = node_to_expr folds (Node e cs) in
                                    let call = create_fun_call f (map snd r) (Fun f) in
                                    (call, ((f, (create_body e1 (map snd r))):(filter (not . (== f) . fst) defs)))
  | otherwise = node_to_expr folds (Node e cs)

find_folds :: Tree -> Int -> (Int, [(Expr, (Id, [(Id, Id)]))])
find_folds (Node _ []) cnt = (cnt, [])
find_folds (Node _ [Fold e r]) cnt = (cnt + 1, [(e, ("f" ++ show cnt, r))])
find_folds (Node e ((CaseBranch t _):cs)) cnt = find_folds (Node e ((Simple t):cs)) cnt
find_folds (Node e ((Simple t):cs)) cnt = let (cnt1, folds1) = find_folds t cnt in
                                        let (cnt2, folds2) = find_folds (Node e cs) cnt1 in
                                        (cnt2, unionBy (\(e1, _) (e2, _) -> e1 == e2) folds1 folds2)

extract_code :: Tree -> Program
extract_code t = let (e, defs) = node_to_expr_or_def (snd (find_folds t 1)) t in (closure e, nub defs)

int_to_expr :: Int -> Expr
int_to_expr 0 = Cons "Z" []
int_to_expr n = Cons "S" [int_to_expr (n - 1)]

expr_to_int :: Expr -> Int
expr_to_int (Cons "Z" []) = 0
expr_to_int (Cons "S" [x]) = 1 + expr_to_int x

str_to_expr :: String -> Expr
str_to_expr [] = Cons "Nil" []
str_to_expr (s:ss) = Cons "Cons" [Cons [s] [], str_to_expr ss]

expr_to_str :: Expr -> String
expr_to_str (Cons "Nil" []) = ""
expr_to_str (Cons "Cons" [Cons s [], ss]) = s ++ (expr_to_str ss)

expr_to_bool :: Expr -> Bool
expr_to_bool (Cons "True" []) = True
expr_to_bool (Cons "False" []) = False

sample_sum :: Expr
sample_sum = App (App (Fun "sum")
                        (App (Fun "squares")
                            (App (App (Fun "upto") (int_to_expr 1)) (Var "n"))
                        )
                  ) (int_to_expr 0)

sum' :: Expr
sum' = Lam "xs" $ Lam "a" $ Case (Var "xs") [
  (Pattern "Nil" [], Var "a"),
  (Pattern "Cons" ["y", "ys"], App (App (Fun "sum") (Var "ys")) (App (App (Fun "+") (Var "y")) (Var "a")))]

plus :: Expr
plus = Lam "a" $ Lam "b" $ Case (Var "a") [
  (Pattern "Z" [], Var "b"),
  (Pattern "S" ["x"], Cons "S" [App (App (Fun "+") (Var "x")) (Var "b")])]

upto :: Expr
upto = Lam "m" $ Lam "n" $ Case (App (App (Fun ">") (Var "m")) (Var "n")) [
  (Pattern "True" [], Cons "Nil" []),
  (Pattern "False" [], Cons "Cons" [Var "m", App (App (Fun "upto") (App (App (Fun "+") (int_to_expr 1)) (Var "m"))) (Var "n")])]

gt :: Expr
gt = Lam "m" $ Lam "n" $ Case (Var "m") [
  (Pattern "Z" [], Cons "False" []),
  (Pattern "S" ["x"], Case (Var "n") [
    (Pattern "Z" [], Cons "True" []),
    (Pattern "S" ["y"], App (App (Fun ">") (Var "x")) (Var "y"))
  ])]

squares :: Expr
squares = Lam "xs" $ Case (Var "xs") [
  (Pattern "Nil" [], Cons "Nil" []),
  (Pattern "Cons" ["y", "ys"], Cons "Cons" [App (App (Fun "*") (Var "y")) (Var "y"), App (Fun "squares") (Var "ys")])]

mult :: Expr
mult = Lam "m" $ Lam "n" $ Case (Var "m") [
  (Pattern "Z" [], Cons "Z" []),
  (Pattern "S" ["x"], App (App (Fun "+") (Var "n")) (App (App (Fun "*") (Var "x")) (Var "n")))]

sample_match :: Expr
sample_match = Lam "p" $ App (App (App (App (Fun "m1") (Var "p")) (Var "str")) (Var "p")) (Var "str")

m1 :: Expr
m1 = Lam "p'" $ Lam "s" $ Lam "op" $ Lam "os" $ Case (Var "p'") [
  (Pattern "Nil" [], Cons "True" []),
  (Pattern "Cons" ["p", "pp"], App (App (App (App (App (Fun "m2") (Var "s")) (Var "p")) (Var "pp")) (Var "op")) (Var "os"))]

m2 :: Expr
m2 = Lam "s'" $ Lam "p" $ Lam "pp" $ Lam "op" $ Lam "os" $ Case (Var "s'") [
  (Pattern "Nil" [], Cons "False" []),
  (Pattern "Cons" ["s", "ss"], Case (App (App (Fun "==") (Var "s")) (Var "p")) [
    (Pattern "True" [], App (App (App (App (Fun "m1") (Var "pp")) (Var "ss")) (Var "op")) (Var "os")),
    (Pattern "False" [], App (App (Fun "next") (Var "os")) (Var "op"))])]

next :: Expr
next = Lam "os" $ Lam "p" $ Case (Var "os") [
  (Pattern "Nil" [], Cons "False" []),
  (Pattern "Cons" ["s", "ss"], App (App (App (App (Fun "m1") (Var "p")) (Var "ss")) (Var "p")) (Var "ss"))]

str_compare :: Expr
str_compare = Lam "s" $ Lam "p" $ Case (Var "p") [
  (Pattern "a" [], Case (Var "s") [
    (Pattern "a" [], Cons "True" []),
    (Pattern "b" [], Cons "False" [])]),
  (Pattern "b" [], Case (Var "s") [
    (Pattern "a" [], Cons "False" []),
    (Pattern "b" [], Cons "True" [])])]

lib :: [(String, Expr)]
lib = [("sum", sum'), ("squares", squares), ("upto", upto), ("+", plus), ("*", mult), (">", gt),
       ("m1", m1), ("m2", m2), ("==", str_compare), ("next", next)]

(e_sum, defs_sum) = extract_code $ super_compile (sample_sum, lib)
(e_match, defs_match) = extract_code $ super_compile (App sample_match (str_to_expr "bba"), lib)

launch_sum :: Int -> Int
launch_sum n = expr_to_int $ eval ((App e_sum (int_to_expr n)), defs_sum ++ lib)

launch_match :: String -> Bool
launch_match str = expr_to_bool $ eval ((App e_match (str_to_expr str)), defs_match ++ lib)