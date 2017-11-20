import Prelude hiding (const, concat, or)


data RHS = And [RHS] | Neg RHS | Conc [RHS] | T Char | NT Char deriving (Show, Eq)

type Grammar = [(RHS, RHS)]
type Interp = RHS -> String -> Double


--f :: [a] -> Int -> [[[a]]]
f lst n = ans where 
    f1 lst = [(take k lst, drop k lst) | k <- [0 .. length lst]]

    f2 lst 1 = lst 
    f2 lst n = ans where
        n2 = map (\(x1,x2) -> (x1, f1 x2)) lst
        n3 = concatMap  (\(x1,x2) -> map (\(x3,x4) -> (x1 ++ [x3],x4)) x2) n2
        ans = f2 n3 (n-1)

    n1 = map (\(x1, x2) -> ([x1],x2)) $ f1 lst    
    res = f2 n1 n
    ans = map fst $ filter (\(x1,x2) -> x2 == []) res


concat langs = \string -> 
    maximum 
    $ map minimum 
    $ map (map (\(x,y) -> x y)) 
    $ map (zip langs) 
    $ f string (length langs)


botIntT nonterm = \string -> 0.0
botIntI nonterm = \string -> 0.5


ww :: Grammar
ww = [
    (NT 'S', And [Neg (Conc [NT 'A', NT 'B']), Neg (Conc [NT 'B', NT 'A']), Neg (NT 'A'), Neg (NT 'B')] ),
    (NT 'A', And [T 'a']),
    (NT 'A', And [Conc [NT 'C', NT 'A', NT 'C']]),
    (NT 'B', And [T 'b']),  
    (NT 'B', And [Conc [NT 'C', NT 'B', NT 'C']]),
    (NT 'C', And [T 'a']),
    (NT 'C', And [T 'b'])
    ]

astar :: Grammar
astar = [
    (NT 'S', And [Neg (NT 'S'), (NT 'A')]),
    (NT 'A', And [Conc [T 'a', NT 'A']]),
    (NT 'A', And [T 'a'])
    ]

snegs :: Grammar
snegs = [
    (NT 'S', And [Neg (NT 'S')])
    ]


interpretationExt :: Interp -> Interp
interpretationExt interpretation rhs = interpretationExtHelp rhs where
    interpretationExtHelp  (And []) = \string -> if string == "" then 1 else 0
    interpretationExtHelp (Conc []) = \string -> if string == "" then 1 else 0
    interpretationExtHelp     (T a) = \string -> if string == [a] then 1 else 0
    interpretationExtHelp    (NT a) = \string -> interpretation (NT a) string
    interpretationExtHelp (Conc rs) = \string -> concat (map interpretationExtHelp rs) string
    interpretationExtHelp   (Neg r) = \string -> 1 - interpretationExtHelp r string
    interpretationExtHelp  (And rs) = \string -> minimum $ map (\r -> interpretationExtHelp r string) rs



isNegative (Neg _) = True
isNegative _ = False
isPositive rhs = not $ isNegative rhs

theta :: Grammar -> Interp -> Interp -> Interp
theta grammar intJ = \intI nonterm string ->
    let extIntI = interpretationExt intI in 
    let extIntJ = interpretationExt intJ in 

    let rhss = map snd $ filter (\(lhs,rhs) -> nonterm == lhs) grammar in
    
    let res1 = any (\rhs -> 
            case rhs of 
                And rhs1 -> 
                    let posAts = filter isPositive rhs1 in 
                    let negAts = filter isNegative rhs1 in 
                    all (\li -> extIntI li string == 1.0) posAts && all (\li -> extIntJ li string == 1.0) negAts
            ) rhss in 

    let res2 = all (\rhs -> 
            case rhs of 
                And rhs1 -> 
                    let posAts = filter isPositive rhs1 in 
                    let negAts = filter isNegative rhs1 in 
                    any (\li -> extIntI li string == 0.0) posAts || any (\li -> extIntJ li string == 0.0) negAts
            ) rhss in     

    if res1 then 1.0 else if res2 then 0.0 else 0.5


omega ::  Grammar -> Interp -> Int -> Interp
omega g int 0 = botIntT
omega g int n = theta g int (omega g int (n-1))  


m :: Grammar -> Int -> Int -> Interp
m g 0 k = botIntI
m g n k = omega g (m g (n-1) k) k

res1 = (m ww 2 2) (NT 'S') "aaa"
res2 = (m ww 2 2) (NT 'S') "aabaab" 
