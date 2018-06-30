> module Test where
>
> import Data.List
> import Test.QuickCheck

 import E1S

 test edit

> type Proposition = Integer
> data Form = P Proposition | Neg Form | Conj Form Form | Disj Form Form | Top | Bottom | Knows Agent Form deriving (Eq,Ord)
> instance Show Form where
>   showsPrec _ (P name) = showString $ show name
>   showsPrec p (Neg formula) = showParen (p > 3) $
>     showString "not " . showsPrec 3 formula
>   showsPrec p (Conj lhs rhs) = showParen (p > 2) $
>     showsPrec 3 lhs . showString " and " . showsPrec 2 rhs
>   showsPrec p (Disj lhs rhs) = showParen (p > 1) $
>     showsPrec 2 lhs . showString " or " . showsPrec 1 rhs
>   showsPrec p Top = showString "T"
>   showsPrec p Bottom = showString "B"
>   showsPrec p (Knows _ _) = showString "K"


> type Assignment = [Integer]
> type Agent = Integer

> satisfies :: Assignment -> Form -> Bool
> satisfies v (P k)      = k `elem` v
> satisfies v (Neg f)    = not (satisfies v f)
> satisfies v (Conj f g) = satisfies v f && satisfies v g
> satisfies v (Disj f g) = satisfies v f || satisfies v g
> satisfies _ Top        = True
> satisfies _ Bottom     = False

> make_beta :: [Proposition] -> [Proposition] -> [(World, Valuation)] -> Form
> make_beta ap_M ap_W valuations = make_beta2 ap_M ap_W ap_W valuations
>
> make_beta2 :: [Proposition] -> [Proposition] -> [Proposition] -> [(World, Valuation)] -> Form
> make_beta2 _ [] ap_W _ = uExists ap_W
> make_beta2 ap_M (prop_w:restProps) ap_W (val:valuations) = Conj (Disj (Neg (P prop_w)) (desc ap_M (snd val))) (make_beta2 ap_M restProps ap_W valuations)

> uExists :: [Proposition] -> Form
> uExists ap = uExists2 [(x, remove x ap) | x <- ap]
>
> uExists2 :: [(Proposition, [Proposition])] -> Form
> uExists2 [] = Bottom
> uExists2 ((active_prop, inactive_props):rest) = Disj (possibleWorld active_prop inactive_props) (uExists2 rest)
>
> possibleWorld :: Proposition -> [Proposition] -> Form
> possibleWorld active_prop [] = P active_prop
> possibleWorld active_prop (inactive_prop:rest) = Conj (Neg (P inactive_prop)) (possibleWorld active_prop rest)

> desc :: [Proposition] -> [Proposition] -> Form
> desc ap props = desc2 ((nub ap) \\ props) props
>
> desc2 :: [Proposition] -> [Proposition] -> Form
> desc2 out_props (in_prop:in_props) = Conj (P in_prop) (desc2 out_props in_props)
> desc2 (out_prop:out_props) []      = Conj (Neg (P out_prop)) (desc2 out_props [])
> desc2 [] []                        = Top

> varsIn :: Form -> [Integer]
> varsIn (P k)      = [k]
> varsIn (Neg f)    = varsIn f
> varsIn (Conj f g) = nub (varsIn f ++ varsIn g)

> modelCheck :: SuccEpistM -> Assignment -> Form -> Bool
> modelCheck model world (P k)            = k `elem` world
> modelCheck model world (Neg f)          = not (modelCheck model world f)
> modelCheck model world (Conj f g)       = (modelCheck model world f) && (modelCheck model world g)
> modelCheck model world (Disj f g)       = (modelCheck model world f) || (modelCheck model world g)
> modelCheck (Mo ap beta programs) world (Knows agent f)  
>                                         = case (lookup agent programs) of
>                                              Just program_a -> all (\x -> (not (runProgram beta ap program_a world  x)) 
>                                                       || (modelCheck (Mo ap beta programs) x f) ) [ assignment | assignment <- (allAssignmentsFor ap), satisfies assignment beta]
>                                              Nothing -> False


---

\small

> allAssignmentsFor :: [Integer] -> [Assignment]
> allAssignmentsFor []     = [ [] ]
> allAssignmentsFor (p:ps) =
>   [ p:rest | rest <- allAssignmentsFor ps ]
>   ++ allAssignmentsFor ps

> isValid :: Form -> Bool
> isValid f =
>   and [ v `satisfies` f  | v <- allAssignmentsFor (varsIn f) ]



 data Prp = P Int | Q Int | R Int | S Int deriving (Eq,Ord)
 instance Show Prp where 
  show (P 0) = "p"; show (P i) = "p" ++ show i 
  show (Q 0) = "q"; show (Q i) = "q" ++ show i 
  show (R 0) = "r"; show (R i) = "r" ++ show i
  show (S 0) = "s"; show (S i) = "s" ++ show i

> data Program = AssignTo Proposition Form
>               | Question Form
>               | Semicolon Program Program
>               | Cap Program Program
>               | Cup Program Program
>               | IdleProgram
>               | UniversalProgram
>               deriving (Eq,Show)

> remove element list = filter (\e -> e/=element) list

> runProgram :: Form -> [Proposition] -> Program -> Assignment -> Assignment -> Bool
> runProgram beta _ (AssignTo prop formula) a_1 a_2        | satisfies a_1 formula = (sort $ nub $ prop:a_1) == (sort $ nub a_2)
>                                                          | otherwise             = (sort $ nub (remove prop a_1)) == (sort $ nub a_2)
> runProgram beta _ (Question formula) a_1 a_2         = ((sort $ nub a_1) == (sort $ nub a_2)) && satisfies a_1 formula
> runProgram beta ap (Semicolon pi_1 pi_2) a_1 a_2     = 
>            not (all (\x -> not ((runProgram beta ap pi_1 a_1 x) && (runProgram beta ap pi_2 x a_2))) [ assignment | assignment <- (allAssignmentsFor ap), satisfies assignment beta] )
> runProgram beta ap (Cap pi_1 pi_2) a_1 a_2           = (runProgram beta ap pi_1 a_1 a_2) && (runProgram beta ap pi_2 a_1 a_2)
> runProgram beta ap (Cup pi_1 pi_2) a_1 a_2           = (runProgram beta ap pi_1 a_1 a_2) || (runProgram beta ap pi_2 a_1 a_2)
> runProgram beta _ IdleProgram _ _                    = False
> runProgram beta _ UniversalProgram _ _               = True



> programSet :: [Proposition] -> Program
> programSet [] = IdleProgram
> programSet (current_prop:rest) = 
>    Semicolon (Cup (AssignTo current_prop Top) (AssignTo current_prop Bottom)) (programSet rest)

> data SuccEpistM = Mo
> 			 [Proposition]
> 			 Form
>        [(Agent, Program)]
>        deriving (Eq,Show)

> type World = Integer
> type Valuation = [Proposition]
> type Relation = [(World, [World])]


> data KripkeM = KMo 
>        [(Agent, Relation)]
>        [(World, Valuation)]
>        deriving (Eq,Show)

> kripkeToSuccint :: KripkeM -> SuccEpistM
> kripkeToSuccint (KMo relations valuations) = Mo ap beta programs
>                                              where ap = sort (ap_M ++ ap_W)
>                                                    beta = make_beta ap_M ap_W valuations
>                                                    programs = [(agent, relationToProgram relation ap beta) | (agent, relation) <- relations]
>                                                    ap_M = nub $ concat [snd x | x <- valuations]
>                                                    ap_W = [-(fst x) | x <- valuations]
 

> relationToProgram :: Relation -> [Proposition] -> Form -> Program
> relationToProgram relation ap beta = relationToProgram1 relation ap
>
> relationToProgram1 :: Relation -> [Proposition] -> Program
> relationToProgram1 [] _ = IdleProgram
> relationToProgram1 ((world, neighbors):rest) ap = Cup (relationToProgram2 world neighbors ap) (relationToProgram1 rest ap)
>
> relationToProgram2 :: World -> [World] -> [Proposition] -> Program
> relationToProgram2 _ [] _ = IdleProgram
> relationToProgram2 w_1 (w_2:rest) ap = Cup ( Semicolon (Semicolon (Question (P (-w_1)) ) UniversalProgram) (Question (P (-w_2))) ) (relationToProgram2 w_1 rest ap)

> modelCheckKrpk :: KripkeM -> World -> Form -> Bool
> modelCheckKrpk (KMo relations valuations) world (P k) = case (lookup world valuations) of
>                                               Just valuation -> k `elem` valuation
>                                               Nothing -> False
> modelCheckKrpk model world (Neg f)          = not (modelCheckKrpk model world f)
> modelCheckKrpk model world (Conj f g)       = (modelCheckKrpk model world f) && (modelCheckKrpk model world g)
> modelCheckKrpk model world (Disj f g)       = (modelCheckKrpk model world f) || (modelCheckKrpk model world g)
> modelCheckKrpk (KMo relations valuations) world (Knows agent f)  
>                                         = case (lookup agent relations) of
>                                              Just relation_a -> case (lookup world relation_a) of
>                                                 Just neighbors -> all (\x -> modelCheckKrpk (KMo relations valuations) x (f) ) neighbors
>                                                 Nothing -> True
>                                              Nothing -> True





 			 [state]

 			 [(Agent, [(state, state, Prp)] )]

> my_kmodel = KMo 
>              [(1, [(1,[2,3])]),
>                 (2, [(2,[4,5]), (3,[6])])]
>              [(4, [1,2]), (5,[1]), (6,[1,2]), (1,[]), (2,[]), (3,[])]

> phi = Knows 1 (Knows 2 (P 2))

initM :: (Num state, Enum state) => 
        [Agent] -> [Prp] -> EpistM state
initM ags props = (Mo states ags val accs points) 
 where 
  states  = [0..(2^k-1)]
   k       = length props

 			 [(Agent, [(state, state, Prp)] )]

> my_kmodel = KMo 
>              [(1, [(1,[2,3])]),
>                 (2, [(2,[4,5]), (3,[6])])]
>              [(4, [1,2]), (5,[1]), (6,[1,2]), (1,[]), (2,[]), (3,[])]

> phi = (Knows 2 (P 2))

initM :: (Num state, Enum state) => 
        [Agent] -> [Prp] -> EpistM state
initM ags props = (Mo states ags val accs points) 
 where 
  states  = [0..(2^k-1)]
   k       = length props
                                                    

> modelCheckKrpk :: KripkeM -> World -> Form -> Bool
> modelCheckKrpk (KMo relations valuations) world (P k) = case (lookup world valuations) of
>                                               Just valuation -> k `elem` valuation
>                                               Nothing -> False
> modelCheckKrpk model world (Neg f)          = not (modelCheckKrpk model world f)
> modelCheckKrpk model world (Conj f g)       = (modelCheckKrpk model world f) && (modelCheckKrpk model world g)
> modelCheckKrpk model world (Disj f g)       = (modelCheckKrpk model world f) || (modelCheckKrpk model world g)
> modelCheckKrpk (KMo relations valuations) world (Knows agent f)  
>                                         = case (lookup agent relations) of
>                                              Just relation_a -> case (lookup world relation_a) of
>                                                 Just neighbors -> all (\x -> modelCheckKrpk (KMo relations valuations) x (f) ) neighbors
>                                                 Nothing -> True
>                                              Nothing -> True





 			 [state]

 			 [(Agent, [(state, state, Prp)] )]

> my_kmodel = KMo 
>              [(1, [(1,[2,3])]),
>                 (2, [(2,[4,5]), (3,[6])])]
>              [(4, [1,2]), (5,[1]), (6,[1,2])]

> phi = Knows 1 (Knows 2 (P 1))

initM :: (Num state, Enum state) => 
        [Agent] -> [Prp] -> EpistM state
initM ags props = (Mo states ags val accs points) 
 where 
  states  = [0..(2^k-1)]
   k       = length props