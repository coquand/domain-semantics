{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Valid/Props.agda
--
-- The properties of the stage-k relations (paper1 Sec. 2.7), proved
-- for EVERY stage k by induction on k: at stage 0 everything is
-- trivial, and the proofs at stage k+1 use the properties at stage k
-- for the components (smaller codes) and, for the term relation at a
-- universe, the type-level properties at the same stage.
-- No rank side conditions are needed at this level.
------------------------------------------------------------------------

module MAHLOINJ.Valid.Props where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLO.Syntax
open import MAHLO.Typing
import MAHLOINJ.Domain.Basic as D
open D using (Top ; tt ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl ; PairEl ; SigmaCode
             ; FinFun ; nil ; cons ; mkSigma) renaming (fst to dfst ; snd to dsnd)
open D using () renaming (suc to nsuc ; zero to nzero ; Nat to Lev)
open import MAHLOINJ.Domain.Kernel
  using (EvalFun ; LeCode ; FinMem ; Comp ; Sup ; Coherent ; CoherentFunTail ; LeFunCode ; FinMemAllU
        ; LeCode-trans ; Coherent-EvalFun ; EvalFun-mon ; EvalFun-in-UCode ; coh-from-aU ; FinMem-a-in-U
        ; FinMem-coh-u ; finMem-piU-dom ; finMem-piU-allU ; finMem-piU-cft
        ; finMem-sigU-dom ; finMem-sigU-allU ; finMem-sigU-cft ; comp-EvalFun ; EvalFun-append-eq
        ; LeFunCode-refl ; append ; CompFun ; LeCode-Sup-left ; LeCode-Sup-right ; FinMemFun ; EvalFun-mon-arg
        ; LeCode-Sup-lub ; LeCode-refl ; FinMem-Sup-element)
open import MAHLOINJ.Model.Selection
  using (Selection ; selectionBelow ; FinMemAllU-Selection ; FinMem-Selection-UCode ; Selection-le-EvalFun
        ; Coherent-Selection ; Coherent-Selection-val ; FinMem-Selection ; FinMem-Selection-codomain)
open import MAHLOINJ.Syntax.Presup using (pCv ; pTE)
open import MAHLOINJ.Syntax.CtxConv using (ccTE ; ccTy)
open import MAHLOINJ.Syntax.Wf using (wfTy)
open import MAHLOINJ.Syntax.Funct using (s1fTy)
open import MAHLOINJ.Valid.HeadRed
open import MAHLOINJ.Valid.Stage
open import MAHLOINJ.Valid.Aux

------------------------------------------------------------------------
-- shapes
------------------------------------------------------------------------

record ShapeOK (S : Shape) : Set where
  field
    inj   : {n : Num} {A A' : Expr n} {B B' : Expr (suc n)} -> Eq (S A B) (S A' B') -> Eq A A' * Eq B B'
    nored : {n : Num} {A : Expr n} {B : Expr (suc n)} -> NoRed (S A B)

PiOK : ShapeOK PiB
PiOK = record { inj = PiB-inj ; nored = nored-Pi }

SigOK : ShapeOK SigmaB
SigOK = record { inj = SigmaB-inj ; nored = nored-Sigma }

-- code parts
record CodeU (b : FinEl) (f : FinFun) : Set where
  constructor mkCodeU
  field
    bU   : FinMem b UCode
    allU : FinMemAllU f b
    cft  : CoherentFunTail f

piU : (b : FinEl) (f : FinFun) -> FinMem (PiCode b f) UCode -> CodeU b f
piU b f m = mkCodeU (finMem-piU-dom b f m) (finMem-piU-allU b f m) (finMem-piU-cft b f m)

sigU : (b : FinEl) (f : FinFun) -> FinMem (SigmaCode b f) UCode -> CodeU b f
sigU b f m = mkCodeU (finMem-sigU-dom b f m) (finMem-sigU-allU b f m) (finMem-sigU-cft b f m)

------------------------------------------------------------------------
-- the property pack at a stage
------------------------------------------------------------------------

record Props (k : Lev) : Set where
  RT = St.RT k
  RM = St.RM k
  field
    natV  : {n : Num} {G : Ctx n} -> IsType G Nat -> RT G Nat Nat NatCode
    symT  : {n : Num} {G : Ctx n} {T T' : Expr n} (a : FinEl) -> FinMem a UCode -> RT G T T' a -> RT G T' T a
    transT : {n : Num} {G : Ctx n} {T1 T2 T3 : Expr n} (a : FinEl) -> FinMem a UCode ->
             RT G T1 T2 a -> RT G T2 T3 a -> RT G T1 T3 a
    downT : {n : Num} {G : Ctx n} {T T' : Expr n} (a0 a1 : FinEl) -> LeCode a0 a1 ->
            FinMem a0 UCode -> FinMem a1 UCode -> RT G T T' a1 -> RT G T T' a0
    joinT : {n : Num} {G : Ctx n} {T T' : Expr n} (a1 a2 : FinEl) -> Comp a1 a2 ->
            FinMem a1 UCode -> FinMem a2 UCode -> RT G T T' a1 -> RT G T T' a2 -> RT G T T' (Sup a1 a2)
    expT  : {n : Num} {G : Ctx n} {T T1 T' : Expr n} (a : FinEl) -> HRs T T1 -> TyEq G T T1 ->
            RT G T1 T' a -> RT G T T' a
    expT' : {n : Num} {G : Ctx n} {T T' T1' : Expr n} (a : FinEl) -> HRs T' T1' -> TyEq G T' T1' ->
            RT G T T1' a -> RT G T T' a
    symM  : {n : Num} {G : Ctx n} {M M' T : Expr n} (u a : FinEl) -> FinMem u a -> FinMem a UCode -> RT G T T a ->
            RM G M M' T u a -> RM G M' M T u a
    transM : {n : Num} {G : Ctx n} {M1 M2 M3 T : Expr n} (u a : FinEl) -> FinMem u a -> FinMem a UCode -> RT G T T a ->
             RM G M1 M2 T u a -> RM G M2 M3 T u a -> RM G M1 M3 T u a
    convM : {n : Num} {G : Ctx n} {M M' T T' : Expr n} (u a : FinEl) -> FinMem u a -> FinMem a UCode -> RT G T T' a ->
            RM G M M' T u a -> RM G M M' T' u a
    restrM : {n : Num} {G : Ctx n} {M M' T : Expr n} (u u' a : FinEl) -> LeCode u' u ->
             FinMem u' a -> FinMem u a -> FinMem a UCode -> RT G T T a -> RM G M M' T u a -> RM G M M' T u' a
    downM : {n : Num} {G : Ctx n} {M M' T : Expr n} (u a0 a1 : FinEl) -> LeCode a0 a1 ->
            FinMem u a0 -> FinMem a0 UCode -> FinMem a1 UCode -> RT G T T a1 ->
            RM G M M' T u a1 -> RM G M M' T u a0
    upM   : {n : Num} {G : Ctx n} {M M' T : Expr n} (u a0 a1 : FinEl) -> LeCode a0 a1 ->
            FinMem u a0 -> FinMem a0 UCode -> FinMem a1 UCode -> RT G T T a1 ->
            RM G M M' T u a0 -> RM G M M' T u a1
    joinM : {n : Num} {G : Ctx n} {M M' T : Expr n} (u1 u2 a : FinEl) -> Comp u1 u2 ->
            FinMem u1 a -> FinMem u2 a -> FinMem a UCode -> RT G T T a ->
            RM G M M' T u1 a -> RM G M M' T u2 a -> RM G M M' T (Sup u1 u2) a
    expM  : {n : Num} {G : Ctx n} {M M1 M' T : Expr n} (u a : FinEl) -> FinMem u a -> FinMem a UCode ->
            HRs M M1 -> ConvTm G M M1 T ->
            RT G T T a -> RM G M1 M' T u a -> RM G M M' T u a
    expM' : {n : Num} {G : Ctx n} {M M' M1' T : Expr n} (u a : FinEl) -> FinMem u a -> FinMem a UCode ->
            HRs M' M1' -> ConvTm G M' M1' T ->
            RT G T T a -> RM G M M1' T u a -> RM G M M' T u a

props0 : Props nzero
props0 = record
  { natV = \ _ -> tt ; symT = \ _ _ _ -> tt ; transT = \ _ _ _ _ -> tt ; downT = \ _ _ _ _ _ _ -> tt
  ; joinT = \ _ _ _ _ _ _ _ -> tt ; expT = \ _ _ _ _ -> tt ; expT' = \ _ _ _ _ -> tt
  ; symM = \ _ _ _ _ _ _ -> tt ; transM = \ _ _ _ _ _ _ _ -> tt ; convM = \ _ _ _ _ _ _ -> tt
  ; restrM = \ _ _ _ _ _ _ _ _ _ -> tt ; downM = \ _ _ _ _ _ _ _ _ _ -> tt ; upM = \ _ _ _ _ _ _ _ _ _ -> tt
  ; joinM = \ _ _ _ _ _ _ _ _ _ _ -> tt ; expM = \ _ _ _ _ _ _ _ _ -> tt ; expM' = \ _ _ _ _ _ _ _ _ -> tt }

------------------------------------------------------------------------
-- type-level properties at stage (suc k), generic over the code shape
------------------------------------------------------------------------

module CodeT (k : Lev) (ih : Props k) (S : Shape) (sok : ShapeOK S) where

  open Props ih
  CT = CodeTy S (St.RT k) (St.RM k)

  -- PER consequences at stage k
  reflL : {n : Num} {G : Ctx n} {T T' : Expr n} (a : FinEl) -> FinMem a UCode -> St.RT k G T T' a -> St.RT k G T T a
  reflL a aU r = transT a aU r (symT a aU r)

  reflR : {n : Num} {G : Ctx n} {T T' : Expr n} (a : FinEl) -> FinMem a UCode -> St.RT k G T T' a -> St.RT k G T' T' a
  reflR a aU r = transT a aU (symT a aU r) r

  reflML : {n : Num} {G : Ctx n} {M M' T : Expr n} (u a : FinEl) -> FinMem u a -> FinMem a UCode ->
    St.RT k G T T a -> St.RM k G M M' T u a -> St.RM k G M M T u a
  reflML u a m aU v r = transM u a m aU v r (symM u a m aU v r)

  reflMR : {n : Num} {G : Ctx n} {M M' T : Expr n} (u a : FinEl) -> FinMem u a -> FinMem a UCode ->
    St.RT k G T T a -> St.RM k G M M' T u a -> St.RM k G M' M' T u a
  reflMR u a m aU v r = transM u a m aU v (symM u a m aU v r) r

  keyMem : {w c : FinEl} (b : FinEl) (f : FinFun) -> CodeU b f -> Selection f w c -> FinMem w b
  keyMem b f cu sel = FinMemAllU-Selection b sel (CodeU.allU cu) (CodeU.cft cu) (coh-from-aU b (CodeU.bU cu)) (CodeU.bU cu)

  symC : {n : Num} {G : Ctx n} {T T' : Expr n} (b : FinEl) (f : FinFun) -> CodeU b f -> CT G T T' b f -> CT G T' T b f
  symC b f cu r = record
    { A = A' ; A' = A ; B = B' ; B' = B ; rT = rT' ; rT' = rT ; tT = tT' ; tT' = tT
    ; iA = iA' ; iB = iB' ; iA' = iA ; iB' = iB
    ; eA = tyeq-sym eA
    ; eB = tyeq-sym (ccTE iA' (tyeq-sym eA) eB)
    ; dom = symT b (CodeU.bU cu) dom
    ; cod = \ w c sel N N' cv rm ->
        symT c (FinMem-Selection-UCode b sel (CodeU.allU cu) (CodeU.cft cu))
          (cod w c sel N' N (conv-sym (conv-conv cv (tyeq-sym eA)))
                  (convM w b (keyMem b f cu sel) (CodeU.bU cu) (symT b (CodeU.bU cu) dom)
                     (symM w b (keyMem b f cu sel) (CodeU.bU cu) (reflR b (CodeU.bU cu) dom) rm))) }
    where open CodeTy r

  transC : {n : Num} {G : Ctx n} {T1 T2 T3 : Expr n} (b : FinEl) (f : FinFun) -> CodeU b f ->
    CT G T1 T2 b f -> CT G T2 T3 b f -> CT G T1 T3 b f
  transC {G = G} {T2 = T2} b f cu r1 r2 = go (ShapeOK.inj sok (HRs-det (CodeTy.rT' r1) (CodeTy.rT r2) (ShapeOK.nored sok) (ShapeOK.nored sok)))
    where
      module R1 = CodeTy r1
      module R2 = CodeTy r2
      go : Eq R1.A' R2.A * Eq R1.B' R2.B -> CT G _ _ b f
      go (eqA , eqB) = record
        { A = R1.A ; A' = R2.A' ; B = R1.B ; B' = R2.B' ; rT = R1.rT ; rT' = R2.rT' ; tT = R1.tT ; tT' = R2.tT'
        ; iA = R1.iA ; iB = R1.iB ; iA' = R2.iA' ; iB' = R2.iB'
        ; eA = tyeq-trans R1.eA (transport (\ X -> TyEq G X R2.A') (Eq-sym eqA) R2.eA)
        ; eB = tyeq-trans R1.eB (ccTE R1.iA R1.eA
                 (transport2 (\ X Y -> TyEq (extend G X) Y R2.B') (Eq-sym eqA) (Eq-sym eqB) R2.eB))
        ; dom = transT b (CodeU.bU cu) R1.dom (transport (\ X -> St.RT k G X R2.A' b) (Eq-sym eqA) R2.dom)
        ; cod = \ w c sel N N' cv rm ->
            let cvA2 = conv-conv cv R1.eA
                hN'  = snd (pCv cvA2)
                wb = keyMem b f cu sel
                rmA1 = reflMR w b wb (CodeU.bU cu) (reflL b (CodeU.bU cu) R1.dom) rm
                rmA2 = convM w b wb (CodeU.bU cu) R1.dom rmA1
                cod2 = transport2 (\ X Y -> (N0 N0' : Expr _) -> ConvTm G N0 N0' X -> St.RM k G N0 N0' X w b ->
                                    St.RT k G (subst1 Y N0) (subst1 R2.B' N0') c)
                         (Eq-sym eqA) (Eq-sym eqB) (R2.cod w c sel)
            in transT c (FinMem-Selection-UCode b sel (CodeU.allU cu) (CodeU.cft cu))
                 (R1.cod w c sel N N' cv rm) (cod2 N' N' (conv-refl hN') rmA2) }

  -- the codomain relation at an arbitrary argument of the domain
  codAt : {n : Num} {G : Ctx n} {T T' : Expr n} {b : FinEl} {f : FinFun} (r : CT G T T' b f) -> CodeU b f ->
    (w : FinEl) -> FinMem w b -> (N N' : Expr n) -> ConvTm G N N' (CodeTy.A r) ->
    St.RM k G N N' (CodeTy.A r) w b ->
    St.RT k G (subst1 (CodeTy.B r) N) (subst1 (CodeTy.B' r) N') (EvalFun f w)
  codAt {b = b} {f} r cu w wb N N' cv rm =
    let cw = FinMem-coh-u w b wb
        sb = selectionBelow f w (CodeU.cft cu) cw
        w0 = dfst sb ; c0 = dfst (dsnd sb) ; sel0 = dfst (dsnd (dsnd sb))
        lw0 = dfst (dsnd (dsnd (dsnd sb))) ; eq0 = dsnd (dsnd (dsnd (dsnd sb)))
        w0b = keyMem b f cu sel0
        rm0 = restrM w w0 b lw0 w0b wb (CodeU.bU cu) (reflL b (CodeU.bU cu) (CodeTy.dom r)) rm
    in transport (St.RT k _ _ _) (Eq-sym eq0) (CodeTy.cod r w0 c0 sel0 N N' cv rm0)

  -- diagonal version: for a validity record of T against itself, B' = B
  diagB : {n : Num} {G : Ctx n} {T : Expr n} {b : FinEl} {f : FinFun} (r : CT G T T b f) ->
    Eq (CodeTy.B' r) (CodeTy.B r)
  diagB r = Eq-sym (snd (ShapeOK.inj sok (HRs-det (CodeTy.rT r) (CodeTy.rT' r) (ShapeOK.nored sok) (ShapeOK.nored sok))))

  codAtD : {n : Num} {G : Ctx n} {T : Expr n} {b : FinEl} {f : FinFun} (r : CT G T T b f) -> CodeU b f ->
    (w : FinEl) -> FinMem w b -> (N N' : Expr n) -> ConvTm G N N' (CodeTy.A r) ->
    St.RM k G N N' (CodeTy.A r) w b ->
    St.RT k G (subst1 (CodeTy.B r) N) (subst1 (CodeTy.B r) N') (EvalFun f w)
  codAtD {G = G} {f = f} r cu w wb N N' cv rm =
    transport (\ Y -> St.RT k G (subst1 (CodeTy.B r) N) (subst1 Y N') (EvalFun f w)) (diagB r)
      (codAt r cu w wb N N' cv rm)

  downC : {n : Num} {G : Ctx n} {T T' : Expr n} (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) ->
    LeCode b0 b1 -> LeFunCode f0 f1 -> CodeU b0 f0 -> CodeU b1 f1 -> CT G T T' b1 f1 -> CT G T T' b0 f0
  downC b0 f0 b1 f1 lb lf c0 c1 r = record
    { A = A ; A' = A' ; B = B ; B' = B' ; rT = rT ; rT' = rT' ; tT = tT ; tT' = tT'
    ; iA = iA ; iB = iB ; iA' = iA' ; iB' = iB' ; eA = eA ; eB = eB
    ; dom = downT b0 b1 lb (CodeU.bU c0) (CodeU.bU c1) dom
    ; cod = \ w c sel N N' cv rm ->
        let cb0 = coh-from-aU b0 (CodeU.bU c0) ; cb1 = coh-from-aU b1 (CodeU.bU c1)
            wb0 = FinMemAllU-Selection b0 sel (CodeU.allU c0) (CodeU.cft c0) cb0 (CodeU.bU c0)
            cw  = FinMem-coh-u w b0 wb0
            wb1 = mem-up w b0 b1 lb wb0 (CodeU.bU c1)
            sb  = selectionBelow f1 w (CodeU.cft c1) cw
            w1 = dfst sb ; c1' = dfst (dsnd sb) ; sel1 = dfst (dsnd (dsnd sb))
            lw1 = dfst (dsnd (dsnd (dsnd sb))) ; eqc1 = dsnd (dsnd (dsnd (dsnd sb)))
            w1b1 = FinMemAllU-Selection b1 sel1 (CodeU.allU c1) (CodeU.cft c1) cb1 (CodeU.bU c1)
            vA = reflL b1 (CodeU.bU c1) dom
            rm1 = restrM w w1 b1 lw1 w1b1 wb1 (CodeU.bU c1) vA (upM w b0 b1 lb wb0 (CodeU.bU c0) (CodeU.bU c1) vA rm)
            rt1 = cod w1 c1' sel1 N N' cv rm1
            cU  = FinMem-Selection-UCode b0 sel (CodeU.allU c0) (CodeU.cft c0)
            ef1U = EvalFun-in-UCode f1 w b1 (CodeU.cft c1) cw (CodeU.allU c1)
            c1U = transport (\ x -> FinMem x UCode) eqc1 ef1U
            ccU = coh-from-aU c cU
            le0 = Selection-le-EvalFun f0 sel (LeFunCode-refl f0 (CodeU.cft c0)) (CodeU.cft c0) (CodeU.cft c0)
                    (Coherent-Selection sel (CodeU.cft c0))
            -- c <= EvalFun f0 w' <= EvalFun f0 w <= EvalFun f1 w = c1'
            le1 = EvalFun-mon f0 f1 w (CodeU.cft c0) (CodeU.cft c1) cw lf
            ce0 = Coherent-EvalFun f0 w (CodeU.cft c0) cw
            ce1 = Coherent-EvalFun f1 w (CodeU.cft c1) cw
            lec = LeCode-trans c (EvalFun f0 w) (EvalFun f1 w) ccU ce0 ce1 (le-sel-arg c0 sel) le1
        in downT c c1' (transport (LeCode c) eqc1 lec) cU c1U rt1 }
    where
      open CodeTy r
      le-sel-arg : {w c : FinEl} -> CodeU b0 f0 -> Selection f0 w c -> LeCode c (EvalFun f0 w)
      le-sel-arg cu s = Selection-le-EvalFun f0 s (LeFunCode-refl f0 (CodeU.cft cu)) (CodeU.cft cu) (CodeU.cft cu)
                          (Coherent-Selection s (CodeU.cft cu))

  joinC : {n : Num} {G : Ctx n} {T T' : Expr n} (b1 : FinEl) (f1 : FinFun) (b2 : FinEl) (f2 : FinFun) ->
    Comp b1 b2 -> CompFun f1 f2 -> CodeU b1 f1 -> CodeU b2 f2 -> CodeU (Sup b1 b2) (append f1 f2) ->
    CT G T T' b1 f1 -> CT G T T' b2 f2 -> CT G T T' (Sup b1 b2) (append f1 f2)
  joinC {G = G} {T} {T'} b1 f1 b2 f2 cb cf c1 c2 c12 r1 r2 =
    go (ShapeOK.inj sok (HRs-det (CodeTy.rT r1) (CodeTy.rT r2) (ShapeOK.nored sok) (ShapeOK.nored sok)))
       (ShapeOK.inj sok (HRs-det (CodeTy.rT' r1) (CodeTy.rT' r2) (ShapeOK.nored sok) (ShapeOK.nored sok)))
    where
      module R1 = CodeTy r1
      module R2 = CodeTy r2
      b12 = Sup b1 b2
      cb1 = coh-from-aU b1 (CodeU.bU c1) ; cb2 = coh-from-aU b2 (CodeU.bU c2)
      go : Eq R1.A R2.A * Eq R1.B R2.B -> Eq R1.A' R2.A' * Eq R1.B' R2.B' -> CT G T T' b12 (append f1 f2)
      go (eA1 , eB1) (eA2 , eB2) = record
        { A = R1.A ; A' = R1.A' ; B = R1.B ; B' = R1.B' ; rT = R1.rT ; rT' = R1.rT' ; tT = R1.tT ; tT' = R1.tT'
        ; iA = R1.iA ; iB = R1.iB ; iA' = R1.iA' ; iB' = R1.iB' ; eA = R1.eA ; eB = R1.eB
        ; dom = domJ
        ; cod = \ w c sel N N' cv rm ->
            let cb12 = coh-from-aU b12 (CodeU.bU c12)
                wb  = FinMemAllU-Selection b12 sel (CodeU.allU c12) (CodeU.cft c12) cb12 (CodeU.bU c12)
                cw  = FinMem-coh-u w b12 wb
                vA  = reflL b12 (CodeU.bU c12) domJ
                lb1 = LeCode-Sup-left b1 b2 cb cb1 cb2
                lb2 = LeCode-Sup-right b1 b2 cb cb1 cb2
                -- part 1
                s1  = selectionBelow f1 w (CodeU.cft c1) cw
                w1 = dfst s1 ; e1c = dfst (dsnd s1) ; sel1 = dfst (dsnd (dsnd s1))
                lw1 = dfst (dsnd (dsnd (dsnd s1))) ; eq1 = dsnd (dsnd (dsnd (dsnd s1)))
                w1b = FinMemAllU-Selection b1 sel1 (CodeU.allU c1) (CodeU.cft c1) cb1 (CodeU.bU c1)
                rm1 = downM w1 b1 b12 lb1 w1b (CodeU.bU c1) (CodeU.bU c12) vA
                        (restrM w w1 b12 lw1 (mem-up w1 b1 b12 lb1 w1b (CodeU.bU c12)) wb (CodeU.bU c12) vA rm)
                rt1 = R1.cod w1 e1c sel1 N N' cv rm1
                -- part 2 (transported to R1's A, B)
                s2  = selectionBelow f2 w (CodeU.cft c2) cw
                w2 = dfst s2 ; e2c = dfst (dsnd s2) ; sel2 = dfst (dsnd (dsnd s2))
                lw2 = dfst (dsnd (dsnd (dsnd s2))) ; eq2 = dsnd (dsnd (dsnd (dsnd s2)))
                w2b = FinMemAllU-Selection b2 sel2 (CodeU.allU c2) (CodeU.cft c2) cb2 (CodeU.bU c2)
                rm2 = downM w2 b2 b12 lb2 w2b (CodeU.bU c2) (CodeU.bU c12) vA
                        (restrM w w2 b12 lw2 (mem-up w2 b2 b12 lb2 w2b (CodeU.bU c12)) wb (CodeU.bU c12) vA rm)
                cod2 = transport2 (\ X Y -> (N0 N0' : Expr _) -> ConvTm G N0 N0' X -> St.RM k G N0 N0' X w2 b2 ->
                                     St.RT k G (subst1 Y N0) (subst1 R1.B' N0') e2c)
                         (Eq-sym eA1) (Eq-sym eB1)
                         (transport (\ Y -> (N0 N0' : Expr _) -> ConvTm G N0 N0' R2.A -> St.RM k G N0 N0' R2.A w2 b2 ->
                                     St.RT k G (subst1 R2.B N0) (subst1 Y N0') e2c) (Eq-sym eB2) (R2.cod w2 e2c sel2))
                rt2 = cod2 N N' cv rm2
                ef1 = EvalFun f1 w ; ef2 = EvalFun f2 w
                cmp = comp-EvalFun f1 f2 w cf (CodeU.cft c1) cw
                cmp' = transport2 Comp eq1 eq2 cmp
                c1U = transport (\ x -> FinMem x UCode) eq1 (EvalFun-in-UCode f1 w b1 (CodeU.cft c1) cw (CodeU.allU c1))
                c2U = transport (\ x -> FinMem x UCode) eq2 (EvalFun-in-UCode f2 w b2 (CodeU.cft c2) cw (CodeU.allU c2))
                rtj = joinT e1c e2c cmp' c1U c2U rt1 rt2
                cU  = FinMem-Selection-UCode b12 sel (CodeU.allU c12) (CodeU.cft c12)
                lec = Selection-le-EvalFun (append f1 f2) sel (LeFunCode-refl (append f1 f2) (CodeU.cft c12))
                        (CodeU.cft c12) (CodeU.cft c12) (Coherent-Selection sel (CodeU.cft c12))
                eqa = EvalFun-append-eq f1 f2 w cf (CodeU.cft c1) cw
                lec' = transport (LeCode c) (Eq-trans eqa (transport2 (\ x y -> Eq (Sup ef1 ef2) (Sup x y)) eq1 eq2 refl)) lec
                cjU = transport (\ x -> FinMem x UCode) (Eq-trans eqa (transport2 (\ x y -> Eq (Sup ef1 ef2) (Sup x y)) eq1 eq2 refl))
                        (EvalFun-in-UCode (append f1 f2) w b12 (CodeU.cft c12) cw (CodeU.allU c12))
            in downT c (Sup e1c e2c) lec' cU cjU rtj }
        where
          domJ = joinT b1 b2 cb (CodeU.bU c1) (CodeU.bU c2) R1.dom
                   (transport2 (\ X Y -> St.RT k G X Y b2) (Eq-sym eA1) (Eq-sym eA2) R2.dom)

  expC : {n : Num} {G : Ctx n} {T T1 T' : Expr n} (b : FinEl) (f : FinFun) -> HRs T T1 -> TyEq G T T1 ->
    CT G T1 T' b f -> CT G T T' b f
  expC b f hr q r = record
    { A = A ; A' = A' ; B = B ; B' = B' ; rT = HRs-trans hr rT ; rT' = rT' ; tT = tyeq-trans q tT ; tT' = tT'
    ; iA = iA ; iB = iB ; iA' = iA' ; iB' = iB' ; eA = eA ; eB = eB ; dom = dom ; cod = cod }
    where open CodeTy r

  expC' : {n : Num} {G : Ctx n} {T T' T1' : Expr n} (b : FinEl) (f : FinFun) -> HRs T' T1' -> TyEq G T' T1' ->
    CT G T T1' b f -> CT G T T' b f
  expC' b f hr q r = record
    { A = A ; A' = A' ; B = B ; B' = B' ; rT = rT ; rT' = HRs-trans hr rT' ; tT = tT ; tT' = tyeq-trans q tT'
    ; iA = iA ; iB = iB ; iA' = iA' ; iB' = iB' ; eA = eA ; eB = eB ; dom = dom ; cod = cod }
    where open CodeTy r

------------------------------------------------------------------------
-- term level, Pi clause, at stage (suc k)
------------------------------------------------------------------------

module PiM (k : Lev) (ih : Props k) where

  open Props ih
  open CodeT k ih PiB PiOK
  PT = PiTm (St.RM k)

  -- align a Pi-term record with a validity record of its type
  align : {n : Num} {G : Ctx n} {M M' T T' : Expr n} {g : FinFun} {b : FinEl} {f : FinFun} ->
    (r : CT G T T' b f) -> PT G M M' T g b f ->
    Sg (PT G M M' T g b f) (\ p -> Eq (PiTm.A p) (CodeTy.A r) * Eq (PiTm.B p) (CodeTy.B r))
  align {G = G} {M} {M'} {T} {g = g} {b} {f} r p = go (PiB-inj (HRs-det (PiTm.rT p) (CodeTy.rT r) nored-Pi nored-Pi))
    where
      go : Eq (PiTm.A p) (CodeTy.A r) * Eq (PiTm.B p) (CodeTy.B r) ->
           Sg (PT G M M' T g b f) (\ p' -> Eq (PiTm.A p') (CodeTy.A r) * Eq (PiTm.B p') (CodeTy.B r))
      go (eA , eB) =
        record { A = CodeTy.A r ; B = CodeTy.B r ; rT = CodeTy.rT r ; tT = CodeTy.tT r ; iA = CodeTy.iA r ; iB = CodeTy.iB r
               ; app = transport2 (\ X Y -> (w v : FinEl) -> Selection g w v -> (N N' : Expr _) -> ConvTm G N N' X ->
                                     St.RM k G N N' X w b -> St.RM k G (App M N) (App M' N') (subst1 Y N) v (EvalFun f w))
                         eA eB (PiTm.app p) }
        , (refl , refl)

  record FunU (g : FinFun) (b : FinEl) (f : FinFun) : Set where
    constructor mkFunU
    field
      fm  : FinMemFun g b f
      cfg : CoherentFunTail g

  selKey : {w v : FinEl} {g : FinFun} {b : FinEl} {f : FinFun} -> CodeU b f -> FunU g b f -> Selection g w v -> FinMem w b
  selKey {b = b} {f} cu fu sel =
    FinMem-Selection b f sel (FunU.fm fu) (FunU.cfg fu) (coh-from-aU b (CodeU.bU cu)) (CodeU.bU cu)

  selVal : {w v : FinEl} {g : FinFun} {b : FinEl} {f : FinFun} -> CodeU b f -> FunU g b f -> Selection g w v ->
    FinMem v (EvalFun f w)
  selVal {b = b} {f} cu fu sel =
    FinMem-Selection-codomain b f sel (FunU.fm fu) (FunU.cfg fu) (CodeU.cft cu) (CodeU.allU cu)

  efU : {w : FinEl} (b : FinEl) (f : FinFun) -> CodeU b f -> FinMem w b -> FinMem (EvalFun f w) UCode
  efU {w} b f cu wb = EvalFun-in-UCode f w b (CodeU.cft cu) (FinMem-coh-u w b wb) (CodeU.allU cu)

  symPi : {n : Num} {G : Ctx n} {M M' T : Expr n} {g : FinFun} {b : FinEl} {f : FinFun} ->
    CodeU b f -> FunU g b f -> CT G T T b f -> PT G M M' T g b f -> PT G M' M T g b f
  symPi {b = b} {f} cu fu r p0 = record
    { A = A ; B = B ; rT = rT ; tT = tT ; iA = iA ; iB = iB
    ; app = \ w v sel N N' cv rm ->
        let wb = selKey cu fu sel ; vm = selVal cu fu sel ; eU = efU b f cu wb
            vA = reflL b (CodeU.bU cu) (CodeTy.dom r)
            hN' = snd (pCv cv)
            rmS = symM w b wb (CodeU.bU cu) vA rm
            x = app w v sel N' N (conv-sym cv) (transport (\ X -> St.RM k _ _ _ X w b) (Eq-sym eqA) rmS)
            vN' = codAtD r cu w wb N' N' (conv-refl (transport (HasType _ N') (Eq-sym eqA) hN'))
                    (transport (\ X -> St.RM k _ _ _ X w b) (Eq-sym eqA) (reflMR w b wb (CodeU.bU cu) vA rm))
            vN'N = codAtD r cu w wb N' N (conv-sym cv) (transport (\ X -> St.RM k _ _ _ X w b) (Eq-sym eqA) rmS)
            x' = transport (\ Y -> St.RM k _ _ _ (subst1 Y N') v (EvalFun f w)) eqB x
            y = symM v (EvalFun f w) vm eU vN' x'
        in transport (\ Y -> St.RM k _ _ _ (subst1 Y N) v (EvalFun f w)) (Eq-sym eqB) (convM v (EvalFun f w) vm eU vN'N y) }
    where
      p = fst (align r p0) ; eqA = fst (snd (align r p0)) ; eqB = snd (snd (align r p0))
      open PiTm p

  -- after alignment, A and B are those of the validity record
  alignA : {n : Num} {G : Ctx n} {M M' T T' : Expr n} {g : FinFun} {b : FinEl} {f : FinFun} ->
    (r : CT G T T' b f) -> PT G M M' T g b f ->
    (w v : FinEl) -> Selection g w v -> (N N' : Expr n) -> ConvTm G N N' (CodeTy.A r) ->
    St.RM k G N N' (CodeTy.A r) w b -> St.RM k G (App M N) (App M' N') (subst1 (CodeTy.B r) N) v (EvalFun f w)
  alignA r p0 = PiTm.app (fst (align r p0))

  mkPi : {n : Num} {G : Ctx n} {M M' T T' : Expr n} {g : FinFun} {b : FinEl} {f : FinFun} {b' : FinEl} {f' : FinFun} ->
    (r : CT G T T' b' f') ->
    ((w v : FinEl) -> Selection g w v -> (N N' : Expr n) -> ConvTm G N N' (CodeTy.A r) ->
      St.RM k G N N' (CodeTy.A r) w b -> St.RM k G (App M N) (App M' N') (subst1 (CodeTy.B r) N) v (EvalFun f w)) ->
    PT G M M' T g b f
  mkPi r h = record { A = CodeTy.A r ; B = CodeTy.B r ; rT = CodeTy.rT r ; tT = CodeTy.tT r
                    ; iA = CodeTy.iA r ; iB = CodeTy.iB r ; app = h }

  mkPi' : {n : Num} {G : Ctx n} {M M' T T' : Expr n} {g : FinFun} {b : FinEl} {f : FinFun} ->
    (r : CT G T T' b f) ->
    ((w v : FinEl) -> Selection g w v -> (N N' : Expr n) -> ConvTm G N N' (CodeTy.A' r) ->
      St.RM k G N N' (CodeTy.A' r) w b -> St.RM k G (App M N) (App M' N') (subst1 (CodeTy.B' r) N) v (EvalFun f w)) ->
    PT G M M' T' g b f
  mkPi' r h = record { A = CodeTy.A' r ; B = CodeTy.B' r ; rT = CodeTy.rT' r ; tT = CodeTy.tT' r
                     ; iA = CodeTy.iA' r ; iB = CodeTy.iB' r ; app = h }

  transPi : {n : Num} {G : Ctx n} {M1 M2 M3 T : Expr n} {g : FinFun} {b : FinEl} {f : FinFun} ->
    CodeU b f -> FunU g b f -> CT G T T b f -> PT G M1 M2 T g b f -> PT G M2 M3 T g b f -> PT G M1 M3 T g b f
  transPi {b = b} {f} cu fu r p1 p2 = mkPi r (\ w v sel N N' cv rm ->
    let wb = selKey cu fu sel ; vm = selVal cu fu sel ; eU = efU b f cu wb
        vA = reflL b (CodeU.bU cu) (CodeTy.dom r)
        hN' = snd (pCv cv)
        rmR = reflMR w b wb (CodeU.bU cu) vA rm
        x1 = alignA r p1 w v sel N N' cv rm
        x2 = alignA r p2 w v sel N' N' (conv-refl hN') rmR
        x2' = convM v (EvalFun f w) vm eU (codAtD r cu w wb N' N (conv-sym cv) (symM w b wb (CodeU.bU cu) vA rm)) x2
    in transM v (EvalFun f w) vm eU (codAtD r cu w wb N N (conv-refl (fst (pCv cv))) (reflML w b wb (CodeU.bU cu) vA rm))
         x1 x2')

  convPi : {n : Num} {G : Ctx n} {M M' T T' : Expr n} {g : FinFun} {b : FinEl} {f : FinFun} ->
    CodeU b f -> FunU g b f -> CT G T T' b f -> PT G M M' T g b f -> PT G M M' T' g b f
  convPi {b = b} {f} cu fu r p = mkPi' r (\ w v sel N N' cv' rm' ->
    let wb = selKey cu fu sel ; vm = selVal cu fu sel ; eU = efU b f cu wb
        cv = conv-conv cv' (tyeq-sym (CodeTy.eA r))
        rm = convM w b wb (CodeU.bU cu) (symT b (CodeU.bU cu) (CodeTy.dom r)) rm'
        vA = reflL b (CodeU.bU cu) (CodeTy.dom r)
        x = alignA r p w v sel N N' cv rm
    in convM v (EvalFun f w) vm eU (codAt r cu w wb N N (conv-refl (fst (pCv cv))) (reflML w b wb (CodeU.bU cu) vA rm)) x)

  expPi : {n : Num} {G : Ctx n} {M M1 M' T : Expr n} {g : FinFun} {b : FinEl} {f : FinFun} ->
    CodeU b f -> FunU g b f -> CT G T T b f -> HRs M M1 -> ConvTm G M M1 T -> PT G M1 M' T g b f -> PT G M M' T g b f
  expPi {b = b} {f} cu fu r hr q p = mkPi r (\ w v sel N N' cv rm ->
    let wb = selKey cu fu sel ; vm = selVal cu fu sel ; eU = efU b f cu wb
        vA = reflL b (CodeU.bU cu) (CodeTy.dom r)
        hN = fst (pCv cv)
        qA = conv-App (CodeTy.iA r) (CodeTy.iB r) (conv-conv q (CodeTy.tT r)) (conv-refl hN)
    in expM v (EvalFun f w) vm eU (HRs-app hr) qA
         (codAtD r cu w wb N N (conv-refl hN) (reflML w b wb (CodeU.bU cu) vA rm))
         (alignA r p w v sel N N' cv rm))

  expPi' : {n : Num} {G : Ctx n} {M M' M1' T : Expr n} {g : FinFun} {b : FinEl} {f : FinFun} ->
    CodeU b f -> FunU g b f -> CT G T T b f -> HRs M' M1' -> ConvTm G M' M1' T -> PT G M M1' T g b f -> PT G M M' T g b f
  expPi' {G = G} {b = b} {f} cu fu r hr q p = mkPi r (\ w v sel N N' cv rm ->
    let wb = selKey cu fu sel ; vm = selVal cu fu sel ; eU = efU b f cu wb
        vA = reflL b (CodeU.bU cu) (CodeTy.dom r)
        hN = fst (pCv cv) ; hN' = snd (pCv cv)
        wG = wfTy (CodeTy.iA r)
        qA = conv-conv (conv-App (CodeTy.iA r) (CodeTy.iB r) (conv-conv q (CodeTy.tT r)) (conv-refl hN'))
               (s1fTy wG (CodeTy.iA r) hN' hN (conv-sym cv) (CodeTy.iB r))
    in expM' v (EvalFun f w) vm eU (HRs-app hr) qA
         (codAtD r cu w wb N N (conv-refl hN) (reflML w b wb (CodeU.bU cu) vA rm))
         (alignA r p w v sel N N' cv rm))

  restrPi : {n : Num} {G : Ctx n} {M M' T : Expr n} {g g' : FinFun} {b : FinEl} {f : FinFun} ->
    LeFunCode g' g -> CodeU b f -> FunU g b f -> FunU g' b f -> CT G T T b f -> PT G M M' T g b f -> PT G M M' T g' b f
  restrPi {g = g} {g'} {b} {f} lf cu fu fu' r p = mkPi r (\ w v sel N N' cv rm ->
    let wb = selKey cu fu' sel ; cw = FinMem-coh-u w b wb ; eU = efU b f cu wb
        vA = reflL b (CodeU.bU cu) (CodeTy.dom r)
        sb = selectionBelow g w (FunU.cfg fu) cw
        w0 = dfst sb ; v0 = dfst (dsnd sb) ; sel0 = dfst (dsnd (dsnd sb))
        lw0 = dfst (dsnd (dsnd (dsnd sb))) ; eqv0 = dsnd (dsnd (dsnd (dsnd sb)))
        w0b = selKey cu fu sel0 ; cw0 = FinMem-coh-u w0 b w0b
        rm0 = restrM w w0 b lw0 w0b wb (CodeU.bU cu) vA rm
        x = alignA r p w0 v0 sel0 N N' cv rm0
        v0m0 = selVal cu fu sel0
        lef = EvalFun-mon-arg f w0 w lw0 (CodeU.cft cu) cw0 cw
        v0m = mem-up v0 (EvalFun f w0) (EvalFun f w) lef v0m0 eU
        valN = codAtD r cu w wb N N (conv-refl (fst (pCv cv))) (reflML w b wb (CodeU.bU cu) vA rm)
        x1 = upM v0 (EvalFun f w0) (EvalFun f w) lef v0m0 (efU b f cu w0b) eU valN x
        cv' = Coherent-Selection-val sel (FunU.cfg fu')
        lev1 = Selection-le-EvalFun g' sel (LeFunCode-refl g' (FunU.cfg fu')) (FunU.cfg fu') (FunU.cfg fu') cw
        lev2 = EvalFun-mon g' g w (FunU.cfg fu') (FunU.cfg fu) cw lf
        ce' = Coherent-EvalFun g' w (FunU.cfg fu') cw ; ce = Coherent-EvalFun g w (FunU.cfg fu) cw
        lev = transport (LeCode v) eqv0 (LeCode-trans v (EvalFun g' w) (EvalFun g w) cv' ce' ce lev1 lev2)
    in restrM v0 v (EvalFun f w) lev (selVal cu fu' sel) v0m eU valN x1)

  downPi : {n : Num} {G : Ctx n} {M M' T : Expr n} {g : FinFun} {b0 b1 : FinEl} {f0 f1 : FinFun} ->
    LeCode b0 b1 -> LeFunCode f0 f1 -> CodeU b0 f0 -> CodeU b1 f1 -> FunU g b0 f0 ->
    CT G T T b1 f1 -> PT G M M' T g b1 f1 -> PT G M M' T g b0 f0
  downPi {b0 = b0} {b1} {f0} {f1} lb lf cu0 cu1 fu0 r1 p = mkPi r1 (\ w v sel N N' cv rm ->
    let wb0 = selKey cu0 fu0 sel ; cw = FinMem-coh-u w b0 wb0
        wb1 = mem-up w b0 b1 lb wb0 (CodeU.bU cu1)
        vA1 = reflL b1 (CodeU.bU cu1) (CodeTy.dom r1)
        rm1 = upM w b0 b1 lb wb0 (CodeU.bU cu0) (CodeU.bU cu1) vA1 rm
        x = alignA r1 p w v sel N N' cv rm1
        lef = EvalFun-mon f0 f1 w (CodeU.cft cu0) (CodeU.cft cu1) cw lf
        valN = codAtD r1 cu1 w wb1 N N (conv-refl (fst (pCv cv))) (reflML w b1 wb1 (CodeU.bU cu1) vA1 rm1)
    in downM v (EvalFun f0 w) (EvalFun f1 w) lef (selVal cu0 fu0 sel) (efU b0 f0 cu0 wb0) (efU b1 f1 cu1 wb1) valN x)

  upPi : {n : Num} {G : Ctx n} {M M' T : Expr n} {g : FinFun} {b0 b1 : FinEl} {f0 f1 : FinFun} ->
    LeCode b0 b1 -> LeFunCode f0 f1 -> CodeU b0 f0 -> CodeU b1 f1 -> FunU g b0 f0 ->
    CT G T T b1 f1 -> PT G M M' T g b0 f0 -> PT G M M' T g b1 f1
  upPi {b0 = b0} {b1} {f0} {f1} lb lf cu0 cu1 fu0 r1 p = mkPi r1 (\ w v sel N N' cv rm ->
    let wb0 = selKey cu0 fu0 sel ; cw = FinMem-coh-u w b0 wb0
        wb1 = mem-up w b0 b1 lb wb0 (CodeU.bU cu1)
        vA1 = reflL b1 (CodeU.bU cu1) (CodeTy.dom r1)
        rm0 = downM w b0 b1 lb wb0 (CodeU.bU cu0) (CodeU.bU cu1) vA1 rm
        r0 = downC b0 f0 b1 f1 lb lf cu0 cu1 r1
        x = alignA r0 p w v sel N N' cv rm0
        lef = EvalFun-mon f0 f1 w (CodeU.cft cu0) (CodeU.cft cu1) cw lf
        valN = codAtD r1 cu1 w wb1 N N (conv-refl (fst (pCv cv))) (reflML w b1 wb1 (CodeU.bU cu1) vA1 rm)
    in upM v (EvalFun f0 w) (EvalFun f1 w) lef (selVal cu0 fu0 sel) (efU b0 f0 cu0 wb0) (efU b1 f1 cu1 wb1) valN x)

  joinPi : {n : Num} {G : Ctx n} {M M' T : Expr n} {g1 g2 : FinFun} {b : FinEl} {f : FinFun} ->
    CompFun g1 g2 -> CodeU b f -> FunU g1 b f -> FunU g2 b f -> FunU (append g1 g2) b f ->
    CT G T T b f -> PT G M M' T g1 b f -> PT G M M' T g2 b f -> PT G M M' T (append g1 g2) b f
  joinPi {g1 = g1} {g2} {b} {f} cg cu fu1 fu2 fu12 r p1 p2 = mkPi r (\ w v sel N N' cv rm ->
    let wb = selKey cu fu12 sel ; cw = FinMem-coh-u w b wb ; eU = efU b f cu wb
        vA = reflL b (CodeU.bU cu) (CodeTy.dom r)
        valN = codAtD r cu w wb N N (conv-refl (fst (pCv cv))) (reflML w b wb (CodeU.bU cu) vA rm)
        s1 = selectionBelow g1 w (FunU.cfg fu1) cw
        w1 = dfst s1 ; v1 = dfst (dsnd s1) ; sel1 = dfst (dsnd (dsnd s1))
        lw1 = dfst (dsnd (dsnd (dsnd s1))) ; eq1 = dsnd (dsnd (dsnd (dsnd s1)))
        w1b = selKey cu fu1 sel1 ; cw1 = FinMem-coh-u w1 b w1b
        lef1 = EvalFun-mon-arg f w1 w lw1 (CodeU.cft cu) cw1 cw
        y1 = upM v1 (EvalFun f w1) (EvalFun f w) lef1 (selVal cu fu1 sel1) (efU b f cu w1b) eU valN
               (alignA r p1 w1 v1 sel1 N N' cv (restrM w w1 b lw1 w1b wb (CodeU.bU cu) vA rm))
        v1m = mem-up v1 (EvalFun f w1) (EvalFun f w) lef1 (selVal cu fu1 sel1) eU
        s2 = selectionBelow g2 w (FunU.cfg fu2) cw
        w2 = dfst s2 ; v2 = dfst (dsnd s2) ; sel2 = dfst (dsnd (dsnd s2))
        lw2 = dfst (dsnd (dsnd (dsnd s2))) ; eq2 = dsnd (dsnd (dsnd (dsnd s2)))
        w2b = selKey cu fu2 sel2 ; cw2 = FinMem-coh-u w2 b w2b
        lef2 = EvalFun-mon-arg f w2 w lw2 (CodeU.cft cu) cw2 cw
        y2 = upM v2 (EvalFun f w2) (EvalFun f w) lef2 (selVal cu fu2 sel2) (efU b f cu w2b) eU valN
               (alignA r p2 w2 v2 sel2 N N' cv (restrM w w2 b lw2 w2b wb (CodeU.bU cu) vA rm))
        v2m = mem-up v2 (EvalFun f w2) (EvalFun f w) lef2 (selVal cu fu2 sel2) eU
        cmp = transport2 Comp eq1 eq2 (comp-EvalFun g1 g2 w cg (FunU.cfg fu1) cw)
        j = joinM v1 v2 (EvalFun f w) cmp v1m v2m eU valN y1 y2
        eqa = Eq-trans (EvalFun-append-eq g1 g2 w cg (FunU.cfg fu1) cw)
                (transport2 (\ x y -> Eq (Sup (EvalFun g1 w) (EvalFun g2 w)) (Sup x y)) eq1 eq2 refl)
        lev = transport (LeCode v) eqa
                (Selection-le-EvalFun (append g1 g2) sel (LeFunCode-refl (append g1 g2) (FunU.cfg fu12))
                   (FunU.cfg fu12) (FunU.cfg fu12) cw)
        ceU = coh-from-aU (EvalFun f w) eU
        supm = FinMem-Sup-element v1 v2 (EvalFun f w) cmp ceU v1m v2m
    in restrM (Sup v1 v2) v (EvalFun f w) lev (selVal cu fu12 sel) supm eU valN j)

------------------------------------------------------------------------
-- term level, Sigma clause, at stage (suc k)
------------------------------------------------------------------------

module SigM (k : Lev) (ih : Props k) where

  open Props ih
  open CodeT k ih SigmaB SigOK
  ST = SigTm (St.RM k)

  record PairU (u1 u2 b : FinEl) (f : FinFun) : Set where
    constructor mkPairU
    field
      m1 : FinMem u1 b
      m2 : FinMem u2 (EvalFun f u1)

  efU : (u1 b : FinEl) (f : FinFun) -> CodeU b f -> FinMem u1 b -> FinMem (EvalFun f u1) UCode
  efU u1 b f cu m = EvalFun-in-UCode f u1 b (CodeU.cft cu) (FinMem-coh-u u1 b m) (CodeU.allU cu)

  align : {n : Num} {G : Ctx n} {M M' T T' : Expr n} {u1 u2 b : FinEl} {f : FinFun} ->
    (r : CT G T T' b f) -> ST G M M' T u1 u2 b f ->
    Sg (ST G M M' T u1 u2 b f) (\ p -> Eq (SigTm.A p) (CodeTy.A r) * Eq (SigTm.B p) (CodeTy.B r))
  align {G = G} {M} {M'} {T} {u1 = u1} {u2} {b} {f} r p =
    go (SigmaB-inj (HRs-det (SigTm.rT p) (CodeTy.rT r) nored-Sigma nored-Sigma))
    where
      go : Eq (SigTm.A p) (CodeTy.A r) * Eq (SigTm.B p) (CodeTy.B r) ->
           Sg (ST G M M' T u1 u2 b f) (\ p' -> Eq (SigTm.A p') (CodeTy.A r) * Eq (SigTm.B p') (CodeTy.B r))
      go (eA , eB) =
        record { A = CodeTy.A r ; B = CodeTy.B r ; rT = CodeTy.rT r ; tT = CodeTy.tT r ; iA = CodeTy.iA r ; iB = CodeTy.iB r
               ; cF = transport (ConvTm G (Fst M) (Fst M')) eA (SigTm.cF p)
               ; fstR = transport (\ X -> St.RM k G (Fst M) (Fst M') X u1 b) eA (SigTm.fstR p)
               ; sndR = transport (\ Y -> St.RM k G (Snd M) (Snd M') (subst1 Y (Fst M)) u2 (EvalFun f u1)) eB (SigTm.sndR p) }
        , (refl , refl)

  -- aligned components
  cFA : {n : Num} {G : Ctx n} {M M' T T' : Expr n} {u1 u2 b : FinEl} {f : FinFun} ->
    (r : CT G T T' b f) -> ST G M M' T u1 u2 b f -> ConvTm G (Fst M) (Fst M') (CodeTy.A r)
  cFA r p = SigTm.cF (fst (align r p))
  fstA : {n : Num} {G : Ctx n} {M M' T T' : Expr n} {u1 u2 b : FinEl} {f : FinFun} ->
    (r : CT G T T' b f) -> ST G M M' T u1 u2 b f -> St.RM k G (Fst M) (Fst M') (CodeTy.A r) u1 b
  fstA r p = SigTm.fstR (fst (align r p))
  sndA : {n : Num} {G : Ctx n} {M M' T T' : Expr n} {u1 u2 b : FinEl} {f : FinFun} ->
    (r : CT G T T' b f) -> ST G M M' T u1 u2 b f ->
    St.RM k G (Snd M) (Snd M') (subst1 (CodeTy.B r) (Fst M)) u2 (EvalFun f u1)
  sndA r p = SigTm.sndR (fst (align r p))

  mkSig : {n : Num} {G : Ctx n} {M M' T T' : Expr n} {u1 u2 b b' : FinEl} {f f' : FinFun} ->
    (r : CT G T T' b' f') -> ConvTm G (Fst M) (Fst M') (CodeTy.A r) ->
    St.RM k G (Fst M) (Fst M') (CodeTy.A r) u1 b ->
    St.RM k G (Snd M) (Snd M') (subst1 (CodeTy.B r) (Fst M)) u2 (EvalFun f u1) -> ST G M M' T u1 u2 b f
  mkSig r c x y = record { A = CodeTy.A r ; B = CodeTy.B r ; rT = CodeTy.rT r ; tT = CodeTy.tT r
                         ; iA = CodeTy.iA r ; iB = CodeTy.iB r ; cF = c ; fstR = x ; sndR = y }

  mkSig' : {n : Num} {G : Ctx n} {M M' T T' : Expr n} {u1 u2 b b' : FinEl} {f f' : FinFun} ->
    (r : CT G T T' b' f') -> ConvTm G (Fst M) (Fst M') (CodeTy.A' r) ->
    St.RM k G (Fst M) (Fst M') (CodeTy.A' r) u1 b ->
    St.RM k G (Snd M) (Snd M') (subst1 (CodeTy.B' r) (Fst M)) u2 (EvalFun f u1) -> ST G M M' T' u1 u2 b f
  mkSig' r c x y = record { A = CodeTy.A' r ; B = CodeTy.B' r ; rT = CodeTy.rT' r ; tT = CodeTy.tT' r
                          ; iA = CodeTy.iA' r ; iB = CodeTy.iB' r ; cF = c ; fstR = x ; sndR = y }

  -- validity of the second component's type
  vSnd : {n : Num} {G : Ctx n} {M M' T : Expr n} {u1 u2 b : FinEl} {f : FinFun} -> CodeU b f -> PairU u1 u2 b f ->
    (r : CT G T T b f) -> ST G M M' T u1 u2 b f ->
    St.RT k G (subst1 (CodeTy.B r) (Fst M)) (subst1 (CodeTy.B r) (Fst M)) (EvalFun f u1)
  vSnd {u1 = u1} {b = b} cu pu r p =
    codAtD r cu u1 (PairU.m1 pu) _ _ (conv-refl (fst (pCv (cFA r p))))
      (reflML u1 b (PairU.m1 pu) (CodeU.bU cu) (reflL b (CodeU.bU cu) (CodeTy.dom r)) (fstA r p))

  symSig : {n : Num} {G : Ctx n} {M M' T : Expr n} {u1 u2 b : FinEl} {f : FinFun} -> CodeU b f -> PairU u1 u2 b f ->
    CT G T T b f -> ST G M M' T u1 u2 b f -> ST G M' M T u1 u2 b f
  symSig {u1 = u1} {u2} {b} {f} cu pu r p =
    mkSig r (conv-sym (cFA r p)) (symM u1 b m1 (CodeU.bU cu) vA (fstA r p))
      (convM u2 (EvalFun f u1) m2 eU (codAtD r cu u1 m1 _ _ (cFA r p) (fstA r p))
        (symM u2 (EvalFun f u1) m2 eU (vSnd cu pu r p) (sndA r p)))
    where
      m1 = PairU.m1 pu ; m2 = PairU.m2 pu ; vA = reflL b (CodeU.bU cu) (CodeTy.dom r) ; eU = efU u1 b f cu m1

  transSig : {n : Num} {G : Ctx n} {M1 M2 M3 T : Expr n} {u1 u2 b : FinEl} {f : FinFun} -> CodeU b f -> PairU u1 u2 b f ->
    CT G T T b f -> ST G M1 M2 T u1 u2 b f -> ST G M2 M3 T u1 u2 b f -> ST G M1 M3 T u1 u2 b f
  transSig {u1 = u1} {u2} {b} {f} cu pu r p1 p2 =
    mkSig r (conv-trans (cFA r p1) (cFA r p2)) (transM u1 b m1 (CodeU.bU cu) vA (fstA r p1) (fstA r p2))
      (transM u2 (EvalFun f u1) m2 eU (vSnd cu pu r p1) (sndA r p1)
        (convM u2 (EvalFun f u1) m2 eU
           (codAtD r cu u1 m1 _ _ (conv-sym (cFA r p1)) (symM u1 b m1 (CodeU.bU cu) vA (fstA r p1)))
           (sndA r p2)))
    where
      m1 = PairU.m1 pu ; m2 = PairU.m2 pu ; vA = reflL b (CodeU.bU cu) (CodeTy.dom r) ; eU = efU u1 b f cu m1

  convSig : {n : Num} {G : Ctx n} {M M' T T' : Expr n} {u1 u2 b : FinEl} {f : FinFun} -> CodeU b f -> PairU u1 u2 b f ->
    CT G T T' b f -> ST G M M' T u1 u2 b f -> ST G M M' T' u1 u2 b f
  convSig {u1 = u1} {u2} {b} {f} cu pu r p =
    mkSig' r (conv-conv (cFA r p) (CodeTy.eA r)) (convM u1 b m1 (CodeU.bU cu) (CodeTy.dom r) (fstA r p))
      (convM u2 (EvalFun f u1) m2 eU
         (codAt r cu u1 m1 _ _ (conv-refl (fst (pCv (cFA r p))))
            (reflML u1 b m1 (CodeU.bU cu) (reflL b (CodeU.bU cu) (CodeTy.dom r)) (fstA r p)))
         (sndA r p))
    where m1 = PairU.m1 pu ; m2 = PairU.m2 pu ; eU = efU u1 b f cu m1

  restrSig : {n : Num} {G : Ctx n} {M M' T : Expr n} {u1 u2 u1' u2' b : FinEl} {f : FinFun} ->
    LeCode u1' u1 -> LeCode u2' u2 -> CodeU b f -> PairU u1 u2 b f -> PairU u1' u2' b f ->
    CT G T T b f -> ST G M M' T u1 u2 b f -> ST G M M' T u1' u2' b f
  restrSig {u1 = u1} {u2} {u1'} {u2'} {b} {f} l1 l2 cu pu pu' r p =
    mkSig r (cFA r p) (restrM u1 u1' b l1 m1' m1 (CodeU.bU cu) vA (fstA r p))
      (downM u2' (EvalFun f u1') (EvalFun f u1) lef m2' eU' eU vS
         (restrM u2 u2' (EvalFun f u1) l2 (mem-up u2' (EvalFun f u1') (EvalFun f u1) lef m2' eU) m2 eU vS (sndA r p)))
    where
      m1 = PairU.m1 pu ; m2 = PairU.m2 pu ; m1' = PairU.m1 pu' ; m2' = PairU.m2 pu'
      vA = reflL b (CodeU.bU cu) (CodeTy.dom r) ; eU = efU u1 b f cu m1 ; eU' = efU u1' b f cu m1'
      lef = EvalFun-mon-arg f u1' u1 l1 (CodeU.cft cu) (FinMem-coh-u u1' b m1') (FinMem-coh-u u1 b m1)
      vS = vSnd cu pu r p

  downSig : {n : Num} {G : Ctx n} {M M' T : Expr n} {u1 u2 b0 b1 : FinEl} {f0 f1 : FinFun} ->
    LeCode b0 b1 -> LeFunCode f0 f1 -> CodeU b0 f0 -> CodeU b1 f1 -> PairU u1 u2 b0 f0 ->
    CT G T T b1 f1 -> ST G M M' T u1 u2 b1 f1 -> ST G M M' T u1 u2 b0 f0
  downSig {u1 = u1} {u2} {b0} {b1} {f0} {f1} lb lf cu0 cu1 pu r1 p =
    mkSig r1 (cFA r1 p) (downM u1 b0 b1 lb m1 (CodeU.bU cu0) (CodeU.bU cu1) vA1 (fstA r1 p))
      (downM u2 (EvalFun f0 u1) (EvalFun f1 u1) lef m2 (efU u1 b0 f0 cu0 m1) (efU u1 b1 f1 cu1 m1b1)
         (vSnd cu1 (mkPairU m1b1 (mem-up u2 (EvalFun f0 u1) (EvalFun f1 u1) lef m2 (efU u1 b1 f1 cu1 m1b1))) r1 p)
         (sndA r1 p))
    where
      m1 = PairU.m1 pu ; m2 = PairU.m2 pu
      m1b1 = mem-up u1 b0 b1 lb m1 (CodeU.bU cu1)
      vA1 = reflL b1 (CodeU.bU cu1) (CodeTy.dom r1)
      lef = EvalFun-mon f0 f1 u1 (CodeU.cft cu0) (CodeU.cft cu1) (FinMem-coh-u u1 b0 m1) lf

  upSig : {n : Num} {G : Ctx n} {M M' T : Expr n} {u1 u2 b0 b1 : FinEl} {f0 f1 : FinFun} ->
    LeCode b0 b1 -> LeFunCode f0 f1 -> CodeU b0 f0 -> CodeU b1 f1 -> PairU u1 u2 b0 f0 ->
    CT G T T b1 f1 -> ST G M M' T u1 u2 b0 f0 -> ST G M M' T u1 u2 b1 f1
  upSig {u1 = u1} {u2} {b0} {b1} {f0} {f1} lb lf cu0 cu1 pu r1 p =
    mkSig r1 (cFA r0 p) fst1
      (upM u2 (EvalFun f0 u1) (EvalFun f1 u1) lef m2 (efU u1 b0 f0 cu0 m1) (efU u1 b1 f1 cu1 m1b1)
         (codAtD r1 cu1 u1 m1b1 _ _ (conv-refl (fst (pCv (cFA r0 p))))
            (reflML u1 b1 m1b1 (CodeU.bU cu1) vA1 fst1))
         (sndA r0 p))
    where
      m1 = PairU.m1 pu ; m2 = PairU.m2 pu
      m1b1 = mem-up u1 b0 b1 lb m1 (CodeU.bU cu1)
      vA1 = reflL b1 (CodeU.bU cu1) (CodeTy.dom r1)
      r0 = downC b0 f0 b1 f1 lb lf cu0 cu1 r1
      fst1 = upM u1 b0 b1 lb m1 (CodeU.bU cu0) (CodeU.bU cu1) vA1 (fstA r0 p)
      lef = EvalFun-mon f0 f1 u1 (CodeU.cft cu0) (CodeU.cft cu1) (FinMem-coh-u u1 b0 m1) lf

  joinSig : {n : Num} {G : Ctx n} {M M' T : Expr n} {u1 u2 u1' u2' b : FinEl} {f : FinFun} ->
    Comp u1 u1' -> Comp u2 u2' -> CodeU b f -> PairU u1 u2 b f -> PairU u1' u2' b f ->
    PairU (Sup u1 u1') (Sup u2 u2') b f ->
    CT G T T b f -> ST G M M' T u1 u2 b f -> ST G M M' T u1' u2' b f -> ST G M M' T (Sup u1 u1') (Sup u2 u2') b f
  joinSig {u1 = u1} {u2} {u1'} {u2'} {b} {f} c1 c2 cu pu pu' ps r p p' =
    mkSig r (cFA r p) (joinM u1 u1' b c1 m1 m1' (CodeU.bU cu) vA (fstA r p) (fstA r p'))
      (joinM u2 u2' (EvalFun f s1) c2 (mem-up u2 (EvalFun f u1) (EvalFun f s1) le1 m2 eS)
         (mem-up u2' (EvalFun f u1') (EvalFun f s1) le1' m2' eS) eS vS
         (upM u2 (EvalFun f u1) (EvalFun f s1) le1 m2 (efU u1 b f cu m1) eS vS (sndA r p))
         (upM u2' (EvalFun f u1') (EvalFun f s1) le1' m2' (efU u1' b f cu m1') eS vS (sndA r p')))
    where
      m1 = PairU.m1 pu ; m2 = PairU.m2 pu ; m1' = PairU.m1 pu' ; m2' = PairU.m2 pu'
      s1 = Sup u1 u1'
      vA = reflL b (CodeU.bU cu) (CodeTy.dom r)
      cb = coh-from-aU b (CodeU.bU cu)
      ms = PairU.m1 ps
      cs = FinMem-coh-u s1 b ms
      cu1 = FinMem-coh-u u1 b m1 ; cu1' = FinMem-coh-u u1' b m1'
      le1 = EvalFun-mon-arg f u1 s1 (LeCode-Sup-left u1 u1' c1 cu1 cu1') (CodeU.cft cu) cu1 cs
      le1' = EvalFun-mon-arg f u1' s1 (LeCode-Sup-right u1 u1' c1 cu1 cu1') (CodeU.cft cu) cu1' cs
      eS = efU s1 b f cu ms
      vS = codAtD r cu s1 ms _ _ (conv-refl (fst (pCv (cFA r p))))
             (upFst (joinM u1 u1' b c1 m1 m1' (CodeU.bU cu) vA (fstA r p) (fstA r p')))
        where
          upFst : St.RM k _ _ _ _ s1 b -> St.RM k _ _ _ _ s1 b
          upFst x = reflML s1 b ms (CodeU.bU cu) vA x

  expSig : {n : Num} {G : Ctx n} {M M1 M' T : Expr n} {u1 u2 b : FinEl} {f : FinFun} -> CodeU b f -> PairU u1 u2 b f ->
    CT G T T b f -> HRs M M1 -> ConvTm G M M1 T -> ST G M1 M' T u1 u2 b f -> ST G M M' T u1 u2 b f
  expSig {M = M} {M1} {u1 = u1} {u2} {b} {f} cu pu r hr q p =
    mkSig r (conv-trans qF (cFA r p)) (expM u1 b m1 (CodeU.bU cu) (HRs-fst hr) qF vA (fstA r p))
      (expM u2 (EvalFun f u1) m2 eU (HRs-snd hr) qS vSM
         (convM u2 (EvalFun f u1) m2 eU (codAtD r cu u1 m1 _ _ (conv-sym qF) rmF) (sndA r p)))
    where
      m1 = PairU.m1 pu ; m2 = PairU.m2 pu ; vA = reflL b (CodeU.bU cu) (CodeTy.dom r) ; eU = efU u1 b f cu m1
      qS' = conv-conv q (CodeTy.tT r)
      qF = conv-Fst (CodeTy.iA r) (CodeTy.iB r) qS'
      qS = conv-Snd (CodeTy.iA r) (CodeTy.iB r) qS'
      rm11 = reflML u1 b m1 (CodeU.bU cu) vA (fstA r p)
      rmF = expM' u1 b m1 (CodeU.bU cu) (HRs-fst hr) qF vA rm11
      rmFF = expM' u1 b m1 (CodeU.bU cu) (HRs-fst hr) qF vA (symM u1 b m1 (CodeU.bU cu) vA rmF)
      vSM = codAtD r cu u1 m1 _ _ (conv-refl (fst (pCv qF))) rmFF

  expSig' : {n : Num} {G : Ctx n} {M M' M1' T : Expr n} {u1 u2 b : FinEl} {f : FinFun} -> CodeU b f -> PairU u1 u2 b f ->
    CT G T T b f -> HRs M' M1' -> ConvTm G M' M1' T -> ST G M M1' T u1 u2 b f -> ST G M M' T u1 u2 b f
  expSig' {G = G} {M = M} {M'} {M1'} {u1 = u1} {u2} {b} {f} cu pu r hr q p =
    mkSig r (conv-trans (cFA r p) (conv-sym qF)) (expM' u1 b m1 (CodeU.bU cu) (HRs-fst hr) qF vA (fstA r p))
      (expM' u2 (EvalFun f u1) m2 eU (HRs-snd hr) qS (vSnd cu pu r p) (sndA r p))
    where
      m1 = PairU.m1 pu ; m2 = PairU.m2 pu ; vA = reflL b (CodeU.bU cu) (CodeTy.dom r) ; eU = efU u1 b f cu m1
      qS' = conv-conv q (CodeTy.tT r)
      qF = conv-Fst (CodeTy.iA r) (CodeTy.iB r) qS'
      wG = wfTy (CodeTy.iA r)
      cMM' = conv-trans (cFA r p) (conv-sym qF)
      qS = conv-conv (conv-Snd (CodeTy.iA r) (CodeTy.iB r) qS')
             (s1fTy wG (CodeTy.iA r) (snd (pCv cMM')) (fst (pCv cMM')) (conv-sym cMM') (CodeTy.iB r))

------------------------------------------------------------------------
-- term level, Nat clause, at stage (suc k)
------------------------------------------------------------------------

module NatM (k : Lev) (ih : Props k) where

  open Props ih
  SN = SucTm (St.RM k)


  symS : {n : Num} {G : Ctx n} {M M' : Expr n} {v : FinEl} -> FinMem v NatCode -> IsType G Nat ->
    SN G M M' v -> SN G M' M v
  symS {v = v} vm iN p = mkSucTm P' P rM' rM cM' cM (conv-sym cP) (symM v NatCode vm tt (natV iN) pred)
    where open SucTm p

  transS : {n : Num} {G : Ctx n} {M1 M2 M3 : Expr n} {v : FinEl} -> FinMem v NatCode -> IsType G Nat ->
    SN G M1 M2 v -> SN G M2 M3 v -> SN G M1 M3 v
  transS {G = G} {v = v} vm iN p1 p2 = go (Suc-inj (HRs-det (SucTm.rM' p1) (SucTm.rM p2) nored-Suc nored-Suc))
    where
      go : Eq (SucTm.P' p1) (SucTm.P p2) -> SN G _ _ v
      go e = mkSucTm (SucTm.P p1) (SucTm.P' p2) (SucTm.rM p1) (SucTm.rM' p2) (SucTm.cM p1) (SucTm.cM' p2)
               (conv-trans (SucTm.cP p1) (transport (\ X -> ConvTm G X (SucTm.P' p2) Nat) (Eq-sym e) (SucTm.cP p2)))
               (transM v NatCode vm tt (natV iN) (SucTm.pred p1)
                  (transport (\ X -> St.RM k G X (SucTm.P' p2) Nat v NatCode) (Eq-sym e) (SucTm.pred p2)))

  restrS : {n : Num} {G : Ctx n} {M M' : Expr n} {v v' : FinEl} -> LeCode v' v -> FinMem v' NatCode -> FinMem v NatCode ->
    IsType G Nat -> SN G M M' v -> SN G M M' v'
  restrS {v = v} {v'} le vm' vm iN p = mkSucTm P P' rM rM' cM cM' cP (restrM v v' NatCode le vm' vm tt (natV iN) pred)
    where open SucTm p

  joinS : {n : Num} {G : Ctx n} {M M' : Expr n} {v v' : FinEl} -> Comp v v' -> FinMem v NatCode -> FinMem v' NatCode ->
    IsType G Nat -> SN G M M' v -> SN G M M' v' -> SN G M M' (Sup v v')
  joinS {G = G} {M} {M'} {v} {v'} c vm vm' iN p p' =
    go (Suc-inj (HRs-det (SucTm.rM p') (SucTm.rM p) nored-Suc nored-Suc))
       (Suc-inj (HRs-det (SucTm.rM' p') (SucTm.rM' p) nored-Suc nored-Suc))
    where
      go : Eq (SucTm.P p') (SucTm.P p) -> Eq (SucTm.P' p') (SucTm.P' p) -> SN G M M' (Sup v v')
      go e1 e2 = mkSucTm (SucTm.P p) (SucTm.P' p) (SucTm.rM p) (SucTm.rM' p) (SucTm.cM p) (SucTm.cM' p) (SucTm.cP p)
                   (joinM v v' NatCode c vm vm' tt (natV iN) (SucTm.pred p)
                      (transport2 (\ X Y -> St.RM k G X Y Nat v' NatCode) e1 e2 (SucTm.pred p')))

  expS : {n : Num} {G : Ctx n} {M M1 M' : Expr n} {v : FinEl} -> HRs M M1 -> ConvTm G M M1 Nat ->
    SN G M1 M' v -> SN G M M' v
  expS hr q p = mkSucTm P P' (HRs-trans hr rM) rM' (conv-trans q cM) cM' cP pred
    where open SucTm p

  expS' : {n : Num} {G : Ctx n} {M M' M1' : Expr n} {v : FinEl} -> HRs M' M1' -> ConvTm G M' M1' Nat ->
    SN G M M1' v -> SN G M M' v
  expS' hr q p = mkSucTm P P' rM (HRs-trans hr rM') cM (conv-trans q cM') cP pred
    where open SucTm p
