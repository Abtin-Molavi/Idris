% default total
||| An interface for declaring a type to be a group 
interface Group g where
    -- A group has an assocative binary operation
    (*) : g -> g -> g
    timesIsAssoc : (a, b, c : g) -> a*(b*c) = (a*b)*c 

    -- and an identity element e such that for all g in G,
    --  e*g = g*e = g
    e : g
    idIsLId : (a:g) -> (e*a) = a 
    idIsRId : (a:g) -> (a*e) = a

   -- and every element g has an inverse g^{-1} such that
   -- g*g^{-1} = g^{-1}*g = e
    inverse : g -> g
    inverseIsLInverse : (a : g) -> (inverse a) * a  = e
    inverseIsRInverse : (a : g) -> a * (inverse a) = e


interface Group g => Boolean g where
    idempotent : (a : g ) -> a*a = Main.e
    
booleanImpliesAbelianPartial : Boolean g => (a, b : g) -> a*b = b*a 
booleanImpliesAbelianPartial a b = rewrite sym (idIsRId a) in                    -- aeb = b(ae)
                            rewrite timesIsAssoc b a e in                        -- aeb = bae
                            rewrite idIsRId (b*a) in                             -- aeb = ba
                            rewrite sym (idempotent (a*b)) in                    -- a(ab(ab))b = ba 
                            ?goal



booleanImpliesAbelian : Boolean g => (a, b : g) -> a*b = b*a 
booleanImpliesAbelian a b = rewrite sym (idIsRId a) in                           -- aeb = b(ae)
                            rewrite timesIsAssoc b a e in                        -- aeb = bae
                            rewrite idIsRId (b*a) in                             -- aeb = ba
                            rewrite sym (idempotent (a*b)) in                    -- a(ab(ab))b = ba 
                            rewrite sym (timesIsAssoc a (a * b * (a * b)) b ) in -- a(ab(ab)b) = ba
                            rewrite sym (timesIsAssoc a b (a*b)) in              -- a(a(b(ab)b) = ba
                            rewrite sym (timesIsAssoc a (b * (a * b)) b ) in     -- a(a(b(ab)b)) = ba
                            rewrite sym (timesIsAssoc b (a * b) b ) in           -- a(a(b((ab)b))) = ba
                            rewrite sym (timesIsAssoc a b b ) in                 -- a(a(b((a(bb))) = ba
                            rewrite idempotent b in                              -- a(a(b(ae))) = ba
                            rewrite idIsRId a in                                 -- a(a(ba)) = ba
                            rewrite timesIsAssoc a a (b*a) in                    -- aa(ba) = ba
                            rewrite idempotent a in                              -- e(ba)) = ba
                            rewrite idIsLId (b*a) in                             -- ba = ba
                            Refl 

--    An elementary proof about groups that might appear on the first day of a group
--    theory course. It requires assuming only the group axioms and the properties of equivalence relations. 
--    Namely, this is the cancellation law, stating that for any group elements a, b and c:
--    if ab=ac, then b=c. 
--    These steps for a proof correspond to the helper functions
--    of the same number.
--    Step 1.  b = (a^{-1} * a )* b, c = (a^{-1}*a)*c
--    Step 2. If ab=ac, then a^{-1} * (ab) = a^{-1}*(ac)
--    Step 3. If  (a^{-1}*a)*b = (a^{-1}*a)*c, then b = c
--    Step 4. If a^{-1}*(ab) = a^{-1}*(ac), then b = c

lclHelper1 : Group g => (a,b : g) -> (inverse a) * a * b = b
lclHelper1 a b = rewrite inverseIsLInverse a in (rewrite idIsLId b in Refl)

lclHelper2 : Group g => (a,b, c : g) -> a*b = a*c -> (inverse a) * (a * b) = (inverse a) * (a * c)
lclHelper2 a b c prop = rewrite (sym prop) in Refl

lclHelper3 : Group g => (a,b,c : g) -> (inverse a) * a * b = (inverse a) * a * c -> b = c
lclHelper3 a b c prop  = rewrite (sym (lclHelper1 a b)) in (rewrite sym (lclHelper1 a c) in prop)

lclHelper4 : Group g => (a,b,c : g) -> inverse a * (a * b) = inverse a * (a * c) -> b = c
lclHelper4 a b c prop = let applyAssoc1 = (timesIsAssoc (inverse a) a b) in 
                        let prop' = trans (sym applyAssoc1) prop in 
                        let applyAssoc2 = (timesIsAssoc (inverse a) a c) in 
                        let prop'' = trans prop' applyAssoc2 in lclHelper3 a b c prop''
                        
leftCancellationLaw : Group g => (a, b, c : g) -> a*b = a*c -> b = c
leftCancellationLaw a b c prop  =  let prop' = lclHelper2 a b c prop in rewrite (lclHelper4 a b c prop') in Refl

