% default total
interface SubFormula a where
    getArrayVars : a -> List String
mutual

    data Formula = And         Formula Formula 
                | Not          Formula
                | ForAll       String  Formula
                | AtomFormula  Atom
                | Length       String Int
                | FormTrue 
                | FormFalse
    

    data Atom    = TermEquals    Term  Term
                | TermLessThan  Term  Term
                   
    data Array   = ArrayVar String
                | Store     Array Term Term
        
    data Term    = IntVar  String
                | IntTerm  Int
                | Times    Int   Term
                | Plus     Term  Term
                | Access   Array Term

 
    SubFormula Term where
        getArrayVars (Access a t) = union (getArrayVars a) (getArrayVars t)
        getArrayVars (Plus t1 t2) = union (getArrayVars t1) (getArrayVars t2)
        getArrayVars (Times n t) = getArrayVars t
        getArrayVars _ = []

    SubFormula Array where 
        getArrayVars (ArrayVar s) = [s]
        getArrayVars (Store a t1 t2) =  foldl union [] [(getArrayVars a),(getArrayVars t1),(getArrayVars t2)]

    SubFormula Atom where
        getArrayVars (TermEquals t1 t2) = union (getArrayVars t1) (getArrayVars t2)
        getArrayVars (TermLessThan t1 t2) = union (getArrayVars t1) (getArrayVars t2)
            
    SubFormula Formula where 
        getArrayVars f =
            case f of (And x y) => union (getArrayVars x) (getArrayVars y)
                      (Not x) => getArrayVars x
                      (ForAll x y) => getArrayVars y
                      (AtomFormula x) => getArrayVars x   
                      (Length x y) => []
                      FormTrue => []
                      FormFalse => []  

lengthFree : Formula -> Bool
lengthFree f =
    case f of (And g h)       => lengthFree g && lengthFree h
              (Not g)         => lengthFree g
              (ForAll _ _ )   => True
              (AtomFormula _) => True
              (Length _ _)    => False
              f               => True  --FormTrue, FormFalse

--  Determines if a formula has its length constraints in the correct form for
--   an array property.
isLengthPrefixedForm : Formula -> Bool
isLengthPrefixedForm f =
    if (lengthFree f)
        then True
        else case f of
            (And (Length a n) g) => isLengthPrefixedForm g
            f                    => False

-- | Removes the lengths and makes them into an envorinment.
stripLength : Formula -> List (String, Int)
stripLength f =
    if (isLengthPrefixedForm f)
        then
            if (lengthFree f)
                then  []
                else 
                    case f of
                        (And (Length a n) g) => ((a, n)::stripLength g)
                        _   => []
        else []

arraysWithLen : Formula -> List String
arraysWithLen f = map fst (stripLength f)


data FormulaWL : Type where
    verify : (f:Formula) ->  sort (getArrayVars f) = sort (arraysWithLen f) -> FormulaWL

f : Formula
f = And (Length "a" 3) (AtomFormula (TermEquals (Access (ArrayVar "a") (IntTerm 3)) (IntTerm 1)))

f' : FormulaWL
f' = verify f Refl

g : Formula
g = (AtomFormula (TermEquals (Access (ArrayVar "a") (IntTerm 3)) (IntTerm 1)))
g' : FormulaWL 
--g' = verify g Refl


h : Formula
h = And (Length "a" 3) (AtomFormula (TermEquals (Access (ArrayVar "a") (IntTerm 3)) (Access (ArrayVar "b") (IntTerm 3))))

foo : FormulaWL -> Formula
foo (verify f prf) = f 