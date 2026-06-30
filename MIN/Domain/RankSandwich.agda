{-# OPTIONS --without-K --exact-split #-}
------------------------------------------------------------------------
-- RankSandwich.agda  (MIN/ -- Pi + U fragment)
--
-- Lemma S (the "sandwiched" coupled rank-reduction): goodS.
-- Type-code cases (T1, T2) are wired to the verified `typeShrink`
-- (via the interval-reducer `reducePiIn`).  The function-element couple
-- (C: z = PiCode, x = FunEl) is the remaining construction.
------------------------------------------------------------------------
module MIN.Domain.RankSandwich where

open import MIN.Domain.Basic
  using ( Nat ; zero ; suc ; max ; Le ; Le-trans ; Le-max-l ; Le-max-r
        ; Top ; tt ; Empty ; Pair ; mkSigma ; fst ; snd ; Sigma
        ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ; nil ; cons )
open import MIN.Domain.Order
  using ( RANK ; RANKFun ; Coherent ; CoherentFunTail ; LeCode ; LeFunCode
        ; LeCode-Bot )
open import MIN.Domain.MemStage using ( finMemC )
open import MIN.Domain.MemUnfold using ( finMemC-bot-to ; finMemC-bot-from ; FinMem-coh-u )
open import MIN.Domain.Membership
  using ( finMem-piU-dom ; finMem-piU-allU ; finMem-piU-cft
        ; finMem-funel-fun ; finMem-funel-wf )
open import MIN.Domain.RankSandwichCore using ( SStmt ; SOut )
open import MIN.Domain.RankSandwichFam using ( typeShrink )
open import MIN.Domain.RankSandwichFunBuild using ( funShrink )

exFalso : {A : Set} -> Empty -> A
exFalso ()

funElAbsurd : (w : FinEl) (g : FinFun) -> finMemC w (FunEl g) -> Empty
funElAbsurd Bot          g ()
funElAbsurd UCode        g ()
funElAbsurd (FunEl h)    g ()
funElAbsurd (PiCode a f) g ()

------------------------------------------------------------------------
-- Reduce a type code  PiCode p0 pf : U  inside an interval [lo, hi]
-- (lo, hi rank <= suc m) to a rank-<= suc m type code p' : U in [lo, hi].
------------------------------------------------------------------------
reducePiIn : (m : Nat) (ih : SStmt m) (lo hi p0 : FinEl) (pf : FinFun) ->
  Le (RANK lo) (suc m) -> Le (RANK hi) (suc m) -> Coherent lo -> Coherent hi ->
  Le (max (RANK p0) (RANKFun pf)) (suc m) ->
  LeCode lo (PiCode p0 pf) -> LeCode (PiCode p0 pf) hi ->
  finMemC (PiCode p0 pf) UCode ->
  Sigma FinEl (\ p' ->
    Pair (finMemC p' UCode)
    (Pair (Le (RANK p') (suc m)) (Pair (LeCode lo p') (LeCode p' hi))))
reducePiIn m ih (PiCode lo0 lof) (PiCode hi0 hif) p0 pf
  rlo rhi clo chi rp lp lh pU =
  typeShrink m ih p0 lo0 hi0 pf hif lof
    cp0 p0U rp0 (fst clo) rlo0 (fst lp) (fst chi) rhi0 (fst lh)
    cpf allUpf rpf (snd chi) rhif (snd lh) (snd clo) rlof (snd lp)
  where
    p0U  = finMem-piU-dom p0 pf pU
    cp0  = FinMem-coh-u p0 UCode p0U
    cpf  = finMem-piU-cft p0 pf pU
    allUpf = finMem-piU-allU p0 pf pU
    rp0  = Le-trans (RANK p0) (max (RANK p0) (RANKFun pf)) (suc m) (Le-max-l (RANK p0) (RANKFun pf)) rp
    rpf  = Le-trans (RANKFun pf) (max (RANK p0) (RANKFun pf)) (suc m) (Le-max-r (RANK p0) (RANKFun pf)) rp
    rlo0 = Le-trans (RANK lo0) (max (RANK lo0) (RANKFun lof)) m (Le-max-l (RANK lo0) (RANKFun lof)) rlo
    rlof = Le-trans (RANKFun lof) (max (RANK lo0) (RANKFun lof)) m (Le-max-r (RANK lo0) (RANKFun lof)) rlo
    rhi0 = Le-trans (RANK hi0) (max (RANK hi0) (RANKFun hif)) m (Le-max-l (RANK hi0) (RANKFun hif)) rhi
    rhif = Le-trans (RANKFun hif) (max (RANK hi0) (RANKFun hif)) m (Le-max-r (RANK hi0) (RANKFun hif)) rhi
reducePiIn m ih Bot (PiCode hi0 hif) p0 pf
  rlo rhi clo chi rp lp lh pU =
  mkSigma p' (mkSigma p'U (mkSigma rkp' (mkSigma tt p'-hi)))
  where
    p0U  = finMem-piU-dom p0 pf pU
    cp0  = FinMem-coh-u p0 UCode p0U
    cpf  = finMem-piU-cft p0 pf pU
    allUpf = finMem-piU-allU p0 pf pU
    rp0  = Le-trans (RANK p0) (max (RANK p0) (RANKFun pf)) (suc m) (Le-max-l (RANK p0) (RANKFun pf)) rp
    rpf  = Le-trans (RANKFun pf) (max (RANK p0) (RANKFun pf)) (suc m) (Le-max-r (RANK p0) (RANKFun pf)) rp
    rhi0 = Le-trans (RANK hi0) (max (RANK hi0) (RANKFun hif)) m (Le-max-l (RANK hi0) (RANKFun hif)) rhi
    rhif = Le-trans (RANKFun hif) (max (RANK hi0) (RANKFun hif)) m (Le-max-r (RANK hi0) (RANKFun hif)) rhi
    ts = typeShrink m ih p0 Bot hi0 pf hif nil
           cp0 p0U rp0 tt tt (LeCode-Bot p0) (fst chi) rhi0 (fst lh)
           cpf allUpf rpf (snd chi) rhif (snd lh) tt tt tt
    p'   = fst ts
    p'U  = fst (snd ts)
    rkp' = fst (snd (snd ts))
    p'-hi = snd (snd (snd (snd ts)))
reducePiIn m ih UCode     (PiCode hi0 hif) p0 pf rlo rhi clo chi rp lp lh pU = exFalso lp
reducePiIn m ih (FunEl g) (PiCode hi0 hif) p0 pf rlo rhi clo chi rp lp lh pU = exFalso lp
reducePiIn m ih lo Bot       p0 pf rlo rhi clo chi rp lp lh pU = exFalso lh
reducePiIn m ih lo UCode     p0 pf rlo rhi clo chi rp lp lh pU = exFalso lh
reducePiIn m ih lo (FunEl g) p0 pf rlo rhi clo chi rp lp lh pU = exFalso lh

------------------------------------------------------------------------
-- Lemma S, by induction on n.
------------------------------------------------------------------------
goodS : (n : Nat) -> SStmt n

-- z = Bot : x = Bot.
goodS n a b c d Bot Bot ra rb rc rd rx rz ca cb cc cd cx cz la lxb lcz lzd xz =
  mkSigma Bot (mkSigma Bot (mkSigma tt (mkSigma tt
    (mkSigma la (mkSigma tt (mkSigma lcz (mkSigma tt xz)))))))
goodS n a b c d UCode        Bot ra rb rc rd rx rz ca cb cc cd cx cz la lxb lcz lzd ()
goodS n a b c d (FunEl g)    Bot ra rb rc rd rx rz ca cb cc cd cx cz la lxb lcz lzd ()
goodS n a b c d (PiCode p f) Bot ra rb rc rd rx rz ca cb cc cd cx cz la lxb lcz lzd ()

-- z = UCode : x a type code.
goodS n a b c d Bot   UCode ra rb rc rd rx rz ca cb cc cd cx cz la lxb lcz lzd xz =
  mkSigma Bot (mkSigma UCode (mkSigma tt (mkSigma tt
    (mkSigma la (mkSigma tt (mkSigma lcz (mkSigma lzd xz)))))))
goodS n a b c d UCode UCode ra rb rc rd rx rz ca cb cc cd cx cz la lxb lcz lzd xz =
  mkSigma UCode (mkSigma UCode (mkSigma tt (mkSigma tt
    (mkSigma la (mkSigma lxb (mkSigma lcz (mkSigma lzd xz)))))))
goodS n a b c d (FunEl g) UCode ra rb rc rd rx rz ca cb cc cd cx cz la lxb lcz lzd ()
-- T1 (x = PiCode): reduce x in [a,b] via reducePiIn; z' = UCode.
goodS (suc m) a b c d (PiCode x0 xf) UCode ra rb rc rd rx rz ca cb cc cd cx cz la lxb lcz lzd xz =
  let r = reducePiIn m (goodS m) a b x0 xf ra rb ca cb rx la lxb xz
      x'   = fst r ; x'U = fst (snd r) ; rkx' = fst (snd (snd r))
      a-x' = fst (snd (snd (snd r))) ; x'-b = snd (snd (snd (snd r)))
  in mkSigma x' (mkSigma UCode (mkSigma rkx' (mkSigma tt
       (mkSigma a-x' (mkSigma x'-b (mkSigma lcz (mkSigma lzd x'U)))))))
goodS zero a b c d (PiCode x0 xf) UCode ra rb rc rd rx rz ca cb cc cd cx cz la lxb lcz lzd xz =
  exFalso (pi-rank1-no-ub b lxb rb)
  where
    pi-rank1-no-ub : (b : FinEl) -> LeCode (PiCode x0 xf) b -> Le (RANK b) zero -> Empty
    pi-rank1-no-ub Bot          () rb
    pi-rank1-no-ub UCode        () rb
    pi-rank1-no-ub (FunEl g)    () rb
    pi-rank1-no-ub (PiCode q g) lq ()

-- z = FunEl : impossible.
goodS n a b c d x (FunEl g) ra rb rc rd rx rz ca cb cc cd cx cz la lxb lcz lzd xz =
  exFalso (funElAbsurd x g xz)

-- z = PiCode : x = Bot (T2) or x = FunEl (C).
goodS (suc m) a b c d Bot (PiCode z0 zf) ra rb rc rd rx rz ca cb cc cd cx cz la lxb lcz lzd xz =
  let zU = finMemC-bot-to (PiCode z0 zf) xz
      r  = reducePiIn m (goodS m) c d z0 zf rc rd cc cd rz lcz lzd zU
      z'   = fst r ; z'U = fst (snd r) ; rkz' = fst (snd (snd r))
      c-z' = fst (snd (snd (snd r))) ; z'-d = snd (snd (snd (snd r)))
  in mkSigma Bot (mkSigma z' (mkSigma tt (mkSigma rkz'
       (mkSigma la (mkSigma tt (mkSigma c-z' (mkSigma z'-d (finMemC-bot-from z' z'U))))))))
goodS zero a b c d Bot (PiCode z0 zf) ra rb rc rd rx rz ca cb cc cd cx cz la lxb lcz lzd xz =
  exFalso (pi-rank1-no-ub d lzd rd)
  where
    pi-rank1-no-ub : (d : FinEl) -> LeCode (PiCode z0 zf) d -> Le (RANK d) zero -> Empty
    pi-rank1-no-ub Bot          () rd
    pi-rank1-no-ub UCode        () rd
    pi-rank1-no-ub (FunEl g)    () rd
    pi-rank1-no-ub (PiCode q g) lq ()
goodS n a b c d UCode      (PiCode z0 zf) ra rb rc rd rx rz ca cb cc cd cx cz la lxb lcz lzd ()
goodS n a b c d (PiCode p f) (PiCode z0 zf) ra rb rc rd rx rz ca cb cc cd cx cz la lxb lcz lzd ()
-- C : function-element couple.
goodS (suc m) a b c d (FunEl g) (PiCode z0 zf)
  ra rb rc rd rx rz ca cb cc cd cx cz la lxb lcz lzd xz =
  funShrink m (goodS m) a b c d z0 zf g ra rb rc rd rz rx ca cb cc cd cx
    (fst cz) (snd cz)
    (finMem-piU-dom z0 zf (finMem-funel-wf g z0 zf xz))
    (finMem-piU-allU z0 zf (finMem-funel-wf g z0 zf xz))
    (finMem-funel-fun g z0 zf xz)
    la lxb lcz lzd
goodS zero a b c d (FunEl g) (PiCode z0 zf)
  ra rb rc rd rx rz ca cb cc cd cx cz la lxb lcz lzd xz =
  exFalso (pi-rank1-no-ub b lxb rb)
  where
    pi-rank1-no-ub : (b : FinEl) -> LeCode (FunEl g) b -> Le (RANK b) zero -> Empty
    pi-rank1-no-ub Bot          () rb
    pi-rank1-no-ub UCode        () rb
    pi-rank1-no-ub (FunEl h)    lq ()
    pi-rank1-no-ub (PiCode q h) () rb
