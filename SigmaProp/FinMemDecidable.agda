{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- FinMemDecidable.agda
--
-- Decidability of Comp, Coherent, and FinMem on finite elements.
--
-- PaperSemanticsSigma.agda already exposes decidability of the order
-- relation via `leFinEl` + `leFinEl-sound` + `leFinEl-complete`.
-- This file adds the analogous decidability for the "typing relation"
-- FinMem, together with all the auxiliary predicates it mentions
-- (Comp / CompFun / CompStepFun / CompStepStep, Coherent / CoherentFun /
-- CoherentFunTail / CoherentWith, FinMemFun / FinMemAllU / FinMemAllProp).
--
-- Style: instead of mirroring leFinEl's Nat-valued interface we use a
-- direct `Dec A = Or A (A -> Empty)` since it gives proof objects
-- immediately and composes cleanly through the many nested Pair cases.
--
-- The mutual block below is marked {-# TERMINATING #-} for the same
-- reason PaperSemanticsSigma's is: FinMem's `FinMem Bot a = FinMem a
-- UCode` clause swaps arguments, and FinMemFun recurses through
-- EvalFun.  The recursion pattern is exactly the one PaperSemanticsSigma
-- already uses, so Agda's accept-with-pragma matches.
--
-- 0 postulates.
------------------------------------------------------------------------

module SigmaProp.FinMemDecidable where

open import SigmaProp.BasicSigma
  using ( Top ; tt ; Empty
        ; Sigma ; mkSigma ; fst ; snd ; Pair
        ; List ; nil ; cons
        ; FinEl ; Bot ; UCode ; PropCode ; FunEl ; PiCode ; SigmaCode ; PairCode
        ; FinFun
        )
open import SigmaProp.PaperSemanticsSigma
  using ( Or ; inl ; inr
        ; Comp ; CompFun ; CompStepFun ; CompStepStep
        ; Coherent ; CoherentFun ; CoherentFunTail ; CoherentWith
        ; CFTcons ; mkCFT
        ; NotBot
        ; FinMem ; FinMemFun ; FinMemAllU ; FinMemAllProp
        ; EvalFun
        )

------------------------------------------------------------------------
-- Dec type and generic combinators
------------------------------------------------------------------------

Dec : Set -> Set
Dec A = Or A (A -> Empty)

yes : {A : Set} -> A -> Dec A
yes a = inl a

no : {A : Set} -> (A -> Empty) -> Dec A
no na = inr na

dec-Pair : {A B : Set} -> Dec A -> Dec B -> Dec (Pair A B)
dec-Pair (inl a) (inl b) = inl (mkSigma a b)
dec-Pair (inl a) (inr nb) = inr (\ p -> nb (snd p))
dec-Pair (inr na) _       = inr (\ p -> na (fst p))

dec-Or : {A B : Set} -> Dec A -> Dec B -> Dec (Or A B)
dec-Or (inl a) _         = inl (inl a)
dec-Or (inr na) (inl b)  = inl (inr b)
dec-Or (inr na) (inr nb) = inr (\ { (inl a) -> na a ; (inr b) -> nb b })

-- Decidable implication: if we can decide both A and B we can decide A -> B.
dec-impl : {A B : Set} -> Dec A -> Dec B -> Dec (A -> B)
dec-impl (inl a) (inl b)  = inl (\ _ -> b)
dec-impl (inl a) (inr nb) = inr (\ f -> nb (f a))
dec-impl (inr na) _       = inl (\ a -> Empty-elim (na a))
  where
    Empty-elim : {X : Set} -> Empty -> X
    Empty-elim ()

------------------------------------------------------------------------
-- NotBot is trivially decidable
------------------------------------------------------------------------

decNotBot : (u : FinEl) -> Dec (NotBot u)
decNotBot Bot             = no (\ ())
decNotBot UCode           = yes tt
decNotBot PropCode        = yes tt
decNotBot (FunEl g)       = yes tt
decNotBot (PiCode a f)    = yes tt
decNotBot (SigmaCode a f) = yes tt
decNotBot (PairCode u v)  = yes tt

------------------------------------------------------------------------
-- Decidability of Comp and its helpers
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual
  decComp : (u v : FinEl) -> Dec (Comp u v)
  decComp Bot             v               = yes tt
  -- UCode
  decComp UCode           Bot             = yes tt
  decComp UCode           UCode           = yes tt
  decComp UCode           PropCode        = no (\ ())
  decComp UCode           (FunEl g)       = no (\ ())
  decComp UCode           (PiCode b g)    = no (\ ())
  decComp UCode           (SigmaCode b g) = no (\ ())
  decComp UCode           (PairCode u v)  = no (\ ())
  -- PropCode
  decComp PropCode        Bot             = yes tt
  decComp PropCode        UCode           = no (\ ())
  decComp PropCode        PropCode        = yes tt
  decComp PropCode        (FunEl g)       = no (\ ())
  decComp PropCode        (PiCode b g)    = no (\ ())
  decComp PropCode        (SigmaCode b g) = no (\ ())
  decComp PropCode        (PairCode u v)  = no (\ ())
  -- FunEl
  decComp (FunEl g)       Bot             = yes tt
  decComp (FunEl g)       UCode           = no (\ ())
  decComp (FunEl g)       PropCode        = no (\ ())
  decComp (FunEl g)       (FunEl h)       = decCompFun g h
  decComp (FunEl g)       (PiCode b h)    = no (\ ())
  decComp (FunEl g)       (SigmaCode b h) = no (\ ())
  decComp (FunEl g)       (PairCode u v)  = no (\ ())
  -- PiCode
  decComp (PiCode a f)    Bot             = yes tt
  decComp (PiCode a f)    UCode           = no (\ ())
  decComp (PiCode a f)    PropCode        = no (\ ())
  decComp (PiCode a f)    (FunEl h)       = no (\ ())
  decComp (PiCode a f)    (PiCode b g)    =
    dec-Pair (decComp a b) (decCompFun f g)
  decComp (PiCode a f)    (SigmaCode b g) = no (\ ())
  decComp (PiCode a f)    (PairCode u v)  = no (\ ())
  -- SigmaCode
  decComp (SigmaCode a f) Bot             = yes tt
  decComp (SigmaCode a f) UCode           = no (\ ())
  decComp (SigmaCode a f) PropCode        = no (\ ())
  decComp (SigmaCode a f) (FunEl h)       = no (\ ())
  decComp (SigmaCode a f) (PiCode b g)    = no (\ ())
  decComp (SigmaCode a f) (SigmaCode b g) =
    dec-Pair (decComp a b) (decCompFun f g)
  decComp (SigmaCode a f) (PairCode u v)  = no (\ ())
  -- PairCode
  decComp (PairCode u v)  Bot              = yes tt
  decComp (PairCode u v)  UCode            = no (\ ())
  decComp (PairCode u v)  PropCode         = no (\ ())
  decComp (PairCode u v)  (FunEl h)        = no (\ ())
  decComp (PairCode u v)  (PiCode b g)     = no (\ ())
  decComp (PairCode u v)  (SigmaCode b g)  = no (\ ())
  decComp (PairCode u1 v1) (PairCode u2 v2) =
    dec-Pair (decComp u1 u2) (decComp v1 v2)

  decCompFun : (f g : FinFun) -> Dec (CompFun f g)
  decCompFun nil         g = yes tt
  decCompFun (cons s f)  g =
    dec-Pair (decCompStepFun s g) (decCompFun f g)

  decCompStepFun : (s : Pair FinEl FinEl) (g : FinFun) -> Dec (CompStepFun s g)
  decCompStepFun s nil         = yes tt
  decCompStepFun s (cons t g)  =
    dec-Pair (decCompStepStep s t) (decCompStepFun s g)

  decCompStepStep : (s t : Pair FinEl FinEl) -> Dec (CompStepStep s t)
  decCompStepStep s t =
    dec-impl (decComp (fst s) (fst t)) (decComp (snd s) (snd t))

  ----------------------------------------------------------------------
  -- Coherent family
  ----------------------------------------------------------------------

  decCoherent : (u : FinEl) -> Dec (Coherent u)
  decCoherent Bot             = yes tt
  decCoherent UCode           = yes tt
  decCoherent PropCode        = yes tt
  decCoherent (FunEl g)       = decCoherentFun g
  decCoherent (PiCode a f)    =
    dec-Pair (decCoherent a) (decCoherentFunTail f)
  decCoherent (SigmaCode a f) =
    dec-Pair (decCoherent a) (decCoherentFunTail f)
  decCoherent (PairCode u v)  =
    dec-Pair (dec-Pair (decCoherent u) (decCoherent v))
             (dec-Or (decNotBot u) (decNotBot v))

  decCoherentFun : (f : FinFun) -> Dec (CoherentFun f)
  decCoherentFun nil         = no (\ ())
  decCoherentFun (cons p ps) = decCoherentFunTail (cons p ps)

  decCoherentFunTail : (f : FinFun) -> Dec (CoherentFunTail f)
  decCoherentFunTail nil         = yes tt
  decCoherentFunTail (cons p ps) = decCFTcons p ps

  -- CFTcons is a record with five fields; we decide each, then pack.
  decCFTcons : (p : Pair FinEl FinEl) (ps : FinFun) -> Dec (CFTcons p ps)
  decCFTcons p ps
    with decCoherent (fst p)
       | decCoherent (snd p)
       | decNotBot   (snd p)
       | decCoherentWith p ps
       | decCoherentFunTail ps
  ... | inl kc | inl vc | inl vn | inl cp | inl tc =
          yes (mkCFT kc vc vn cp tc)
  ... | inr nkc | _ | _ | _ | _ =
          no (\ r -> nkc (CFTcons.key-coh r))
  ... | inl _  | inr nvc | _ | _ | _ =
          no (\ r -> nvc (CFTcons.val-coh r))
  ... | inl _  | inl _  | inr nvn | _ | _ =
          no (\ r -> nvn (CFTcons.val-nbot r))
  ... | inl _  | inl _  | inl _  | inr ncp | _ =
          no (\ r -> ncp (CFTcons.compat r))
  ... | inl _  | inl _  | inl _  | inl _  | inr ntc =
          no (\ r -> ntc (CFTcons.tail-coh r))

  decCoherentWith : (p : Pair FinEl FinEl) (qs : FinFun) -> Dec (CoherentWith p qs)
  decCoherentWith p nil         = yes tt
  decCoherentWith p (cons q qs) =
    dec-Pair
      (dec-impl (decComp (fst p) (fst q)) (decComp (snd p) (snd q)))
      (decCoherentWith p qs)

  ----------------------------------------------------------------------
  -- FinMem family
  ----------------------------------------------------------------------

  decFinMem : (u a : FinEl) -> Dec (FinMem u a)
  -- Bot is in a iff a : U
  decFinMem Bot             a               = decFinMem a UCode
  -- UCode
  decFinMem UCode           Bot             = no (\ ())
  decFinMem UCode           UCode           = yes tt
  decFinMem UCode           PropCode        = no (\ ())
  decFinMem UCode           (FunEl g)       = no (\ ())
  decFinMem UCode           (PiCode a f)    = no (\ ())
  decFinMem UCode           (SigmaCode a f) = no (\ ())
  decFinMem UCode           (PairCode u v)  = no (\ ())
  -- PropCode
  decFinMem PropCode        Bot             = no (\ ())
  decFinMem PropCode        UCode           = yes tt
  decFinMem PropCode        PropCode        = no (\ ())
  decFinMem PropCode        (FunEl g)       = no (\ ())
  decFinMem PropCode        (PiCode a f)    = no (\ ())
  decFinMem PropCode        (SigmaCode a f) = no (\ ())
  decFinMem PropCode        (PairCode u v)  = no (\ ())
  -- FunEl: only belongs to a Pi type
  decFinMem (FunEl g)       Bot             = no (\ ())
  decFinMem (FunEl g)       UCode           = no (\ ())
  decFinMem (FunEl g)       PropCode        = no (\ ())
  decFinMem (FunEl g)       (FunEl h)       = no (\ ())
  decFinMem (FunEl g)       (PiCode a f)    =
    dec-Pair (decFinMemFun g a f)
             (dec-Pair (decCoherentFun g)
                       (decFinMem (PiCode a f) UCode))
  decFinMem (FunEl g)       (SigmaCode a f) = no (\ ())
  decFinMem (FunEl g)       (PairCode u v)  = no (\ ())
  -- PiCode
  decFinMem (PiCode a f)    Bot             = no (\ ())
  decFinMem (PiCode a f)    UCode           =
    dec-Pair (decFinMem a UCode)
             (dec-Pair (decFinMemAllU f a)
                       (decCoherentFunTail f))
  decFinMem (PiCode a f)    PropCode        =
    dec-Pair (decFinMem a UCode)
             (dec-Pair (decFinMemAllProp f a)
                       (decCoherentFunTail f))
  decFinMem (PiCode a f)    (FunEl g)       = no (\ ())
  decFinMem (PiCode a f)    (PiCode b g)    = no (\ ())
  decFinMem (PiCode a f)    (SigmaCode b g) = no (\ ())
  decFinMem (PiCode a f)    (PairCode u v)  = no (\ ())
  -- SigmaCode
  decFinMem (SigmaCode a f) Bot             = no (\ ())
  decFinMem (SigmaCode a f) UCode           =
    dec-Pair (decFinMem a UCode)
             (dec-Pair (decFinMemAllU f a)
                       (decCoherentFunTail f))
  decFinMem (SigmaCode a f) PropCode        = no (\ ())
  decFinMem (SigmaCode a f) (FunEl g)       = no (\ ())
  decFinMem (SigmaCode a f) (PiCode b g)    = no (\ ())
  decFinMem (SigmaCode a f) (SigmaCode b g) = no (\ ())
  decFinMem (SigmaCode a f) (PairCode u v)  = no (\ ())
  -- PairCode: only belongs to a Sigma type
  decFinMem (PairCode u v)  Bot              = no (\ ())
  decFinMem (PairCode u v)  UCode            = no (\ ())
  decFinMem (PairCode u v)  PropCode         = no (\ ())
  decFinMem (PairCode u v)  (FunEl g)        = no (\ ())
  decFinMem (PairCode u v)  (PiCode b g)     = no (\ ())
  decFinMem (PairCode u v)  (SigmaCode a f)  =
    dec-Pair (dec-Pair (decFinMem u a)
                       (decFinMem v (EvalFun f u)))
             (dec-Pair (decCoherent (PairCode u v))
                       (decFinMem (SigmaCode a f) UCode))
  decFinMem (PairCode u v)  (PairCode u2 v2) = no (\ ())

  decFinMemFun : (g : FinFun) (a : FinEl) (f : FinFun) -> Dec (FinMemFun g a f)
  decFinMemFun nil         a f = yes tt
  decFinMemFun (cons p ps) a f =
    dec-Pair
      (dec-Pair (decFinMem (fst p) a)
                (decFinMem (snd p) (EvalFun f (fst p))))
      (decFinMemFun ps a f)

  decFinMemAllU : (f : FinFun) (a : FinEl) -> Dec (FinMemAllU f a)
  decFinMemAllU nil         a = yes tt
  decFinMemAllU (cons p ps) a =
    dec-Pair
      (dec-Pair (decFinMem (fst p) a) (decFinMem (snd p) UCode))
      (decFinMemAllU ps a)

  decFinMemAllProp : (f : FinFun) (a : FinEl) -> Dec (FinMemAllProp f a)
  decFinMemAllProp nil         a = yes tt
  decFinMemAllProp (cons p ps) a =
    dec-Pair
      (dec-Pair (decFinMem (fst p) a) (decFinMem (snd p) PropCode))
      (decFinMemAllProp ps a)
