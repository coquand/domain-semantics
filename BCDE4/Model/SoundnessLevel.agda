{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.Model.SoundnessLevel
--
-- Soundness of the level-product rules:
--
--   * InvTyp-LPi, InvTyp-LLam, InvTyp-LApp   (formation, abstraction,
--                                             application);
--   * InvConv-LPi, InvConv-LLam               (congruences);
--   * InvConv-LApp-fun, InvConv-LApp-lvl      (congruences of t l);
--   * InvConv-LApp-beta, InvConv-LApp-eta     (β and η).
--
-- Level functions are strict: every non-⊥ edge of a level graph lives
-- at ONE canonical level token, so typed upper bounds are built edge by
-- edge from the induction hypothesis at that level (`lgraph`).
--
-- 0 postulates.
------------------------------------------------------------------------

open import BCDE4.Levels using (LDecAll)

module BCDE4.Model.SoundnessLevel (D : LDecAll) where

open import BCDE4.Dom.Basic using (U0 ; EqL ; EqL-refl ; EqL-Eq)
import BCDE4.Dom.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ; fst ; snd ;
              Pair ; List ; nil ; cons ; Eq ; refl ; Eq-transport ; Eq-sym ;
              FinEl ; Bot ; UCode ; LevTy ; LevEl ; FunEl ; PiCode ; LPiCode ; FinFun)
open import BCDE4.Dom.Kernel using (LeCode ; LeCode-refl ; LeCode-trans ;
  Coherent ; CoherentFun ; CoherentFunTail ; CFTcons ; mkCFT ; cft-from-cf ; CoherentWith ;
  NotBot ; FinMem ; FinMemFun ; FinMemAllU ; FinMem-coh-u ; FinMem-a-in-U ; coh-from-aU ;
  finMem-U-lvl ; finMem-upward ; finMem-LevTy-inv ;
  finMem-LpiU-mk ; finMem-LpiU-allU ; finMem-LpiU-cft ;
  finMem-Lfunel-fun ; finMem-Lfunel-coh ; finMem-Lfunel-wf ; finMem-Lfunel-mk ;
  Comp ; EvalFun ; EvalFun-mon-arg ; Coherent-EvalFun ; EvalFun-in-UCode ;
  LeFunCode)
open CFTcons
open import BCDE4.Model.Selection using (Selection ; Edge ; EdgeIn ; here ; there ;
  Coherent-Selection ; CoherentFun-edge-key ; selectionBelow ; FinMem-Selection-codomain)
open import BCDE4.Model.Core using (Expr ; U ; LPi ; LLam ; LApp ; lsub1 ; lshiftE ; Ctx)
open import BCDE4.Levels using (LCtx ; LSub ; LExpr ; LDec ; Valid ; lsubL ; lvar)
open import BCDE4.Basic using (Either ; inl ; inr)
open import BCDE4.Model.Guard
open import BCDE4.Model.Eval D
open import BCDE4.Model.EvalLevel D using (EvalRel-lsub1-fwd ; EvalRel-lsub1-bwd ;
  EvalRel-ldec-fwd ; EvalRel-ldec-bwd ; EvalRel-lshift-fwd ; EvalRel-lshift-bwd)
open import BCDE4.Model.SoundnessLemmas D using (Fits ; Fits-CoherentEnv ; Typed ; InvTyp ; InvConv ;
  mapEdges ; mapEdges-corr ; EvalFun-edge-le ; NotBot-from-Le ; NotBot-from-FinMem ; finMem-Bot-eq)
open import BCDE4.Model.SoundnessExtra D using (InvTyp-equiv)

private variable
  TL : LCtx
  θ : LSub

------------------------------------------------------------------------
-- Small facts
------------------------------------------------------------------------

private
  Eq-cong : {A B : Set} (f : A -> B) {x y : A} -> Eq x y -> Eq (f x) (f y)
  Eq-cong f refl = refl

edgeVal : (e : Edge) (h : FinFun) -> CoherentFunTail h -> EdgeIn e h ->
  Pair (Coherent (snd e)) (NotBot (snd e))
edgeVal e (cons q qs) cft here = mkSigma (val-coh cft) (val-nbot cft)
edgeVal e (cons q qs) cft (there ein) = edgeVal e qs (tail-coh cft) ein

-- a member of a (level-0) universe code is in U0
finMem-in-U : {n : Nat} (l : LExpr) (rho : EnvApprox TL θ n) (x : FinEl) ->
  EvalRel (U l) rho x -> (y : FinEl) -> FinMem y x -> FinMem y U0
finMem-in-U l rho Bot evU y fm =
  Eq-transport (\ z -> FinMem z U0) (Eq-sym (finMem-Bot-eq y fm)) tt
finMem-in-U l rho (UCode lu) evU y fm = finMem-U-lvl y lu 0 fm
finMem-in-U l rho LevTy (mkSigma _ ()) y fm
finMem-in-U l rho (LevEl _) (mkSigma _ ()) y fm
finMem-in-U l rho (FunEl _) (mkSigma _ ()) y fm
finMem-in-U l rho (PiCode _ _) (mkSigma _ ()) y fm
finMem-in-U l rho (LPiCode _) (mkSigma _ ()) y fm

-- the code of a level is canonical
lcode-canon : (T : LCtx) (m : LExpr) -> Eq (lcodeT T (ldecT T (lcodeT T m))) (lcodeT T m)
lcode-canon T m = LDec.lcode-sound (D T) (LDec.ldec-code (D T) m)

-- two tokens: LevEl k <= LevEl c gives k = c
levEq : (k c : Nat) -> LeCode (LevEl k) (LevEl c) -> Eq k c
levEq k c le = EqL-Eq k c le

-- joining singleton graphs of an evaluation
build-graph : {n : Nat} (F : Expr n) (rho : EnvApprox TL θ n) -> CoherentEnv rho ->
  (g : FinFun) -> CoherentFun g ->
  ((p : Edge) -> EdgeIn p g -> EvalRel F rho (FunEl (cons p nil))) ->
  EvalRel F rho (FunEl g)
build-graph F rho crho nil () f
build-graph F rho crho (cons p nil) _ f = f p here
build-graph F rho crho (cons p (cons q qs)) cfg f =
  let evSing = f p here
      evRest = build-graph F rho crho (cons q qs) (tail-coh cfg) (\ r rin -> f r (there rin))
      sgl  = FunEl (cons p nil)
      rest = FunEl (cons q qs)
      csing = EvalRel-coh F rho sgl evSing
      crest = EvalRel-coh F rho rest evRest
      comp  = EvalRel-Comp F rho crho sgl rest evSing evRest
  in EvalRel-Sup F rho sgl rest crho csing crest comp evSing evRest

------------------------------------------------------------------------
-- Level graphs: every edge moved to its level token
------------------------------------------------------------------------

LNew : FinFun -> Set
LNew f = (p : Edge) -> EdgeIn p f -> Pair Nat FinEl

lgraph : (f : FinFun) -> LNew f -> FinFun
lgraph f ne = mapEdges f (\ p ein -> mkSigma (LevEl (fst (ne p ein))) (snd (ne p ein)))

lgraph-corr : (f : FinFun) (ne : LNew f) (p : Edge) (ein : EdgeIn p f) ->
  EdgeIn (mkSigma (LevEl (fst (ne p ein))) (snd (ne p ein))) (lgraph f ne)
lgraph-corr f ne p ein = mapEdges-corr f (\ p ein -> mkSigma (LevEl (fst (ne p ein))) (snd (ne p ein))) p ein

lgraph-member : (f : FinFun) (ne : LNew f) (e : Edge) -> EdgeIn e (lgraph f ne) ->
  Sigma Edge (\ p -> Sigma (EdgeIn p f) (\ ein ->
    Eq e (mkSigma (LevEl (fst (ne p ein))) (snd (ne p ein)))))
lgraph-member (cons p ps) ne .(mkSigma (LevEl (fst (ne p here))) (snd (ne p here))) here =
  mkSigma p (mkSigma here refl)
lgraph-member (cons p ps) ne e (there ein) =
  let r = lgraph-member ps (\ q qin -> ne q (there qin)) e ein
  in mkSigma (fst r) (mkSigma (there (fst (snd r))) (snd (snd r)))

lgraph-cft : (f : FinFun) (ne : LNew f) ->
  ((p : Edge) (ein : EdgeIn p f) -> Pair (Coherent (snd (ne p ein))) (NotBot (snd (ne p ein)))) ->
  ((p : Edge) (ein : EdgeIn p f) (q : Edge) (qin : EdgeIn q f) ->
     Eq (fst (ne p ein)) (fst (ne q qin)) -> Comp (snd (ne p ein)) (snd (ne q qin))) ->
  CoherentFunTail (lgraph f ne)
lgraph-cft nil ne ch cm = tt
lgraph-cft (cons p ps) ne ch cm =
  mkCFT tt (fst (ch p here)) (snd (ch p here))
    (cw ps (\ q qin -> ne q (there qin)) (\ q qin -> cm p here q (there qin)))
    (lgraph-cft ps (\ q qin -> ne q (there qin)) (\ q qin -> ch q (there qin))
       (\ q qin r rin -> cm q (there qin) r (there rin)))
  where
    cw : (qs : FinFun) (ne' : LNew qs) ->
      ((q : Edge) (qin : EdgeIn q qs) -> Eq (fst (ne p here)) (fst (ne' q qin)) ->
         Comp (snd (ne p here)) (snd (ne' q qin))) ->
      CoherentWith (mkSigma (LevEl (fst (ne p here))) (snd (ne p here))) (lgraph qs ne')
    cw nil ne' h = tt
    cw (cons q qs) ne' h =
      mkSigma (\ c -> h q here (EqL-Eq _ _ c))
              (cw qs (\ r rin -> ne' r (there rin)) (\ r rin -> h r (there rin)))

lgraph-lf : (f : FinFun) (ne : LNew f) -> CoherentFunTail f -> CoherentFunTail (lgraph f ne) ->
  ((p : Edge) (ein : EdgeIn p f) ->
     Pair (LeCode (LevEl (fst (ne p ein))) (fst p)) (LeCode (snd p) (snd (ne p ein)))) ->
  ((p : Edge) (ein : EdgeIn p f) -> Coherent (snd (ne p ein))) ->
  LeFunCode f (lgraph f ne)
lgraph-lf f ne cf cft' le cw = go f (\ q qin -> qin)
  where
    go : (ps : FinFun) -> ((q : Edge) -> EdgeIn q ps -> EdgeIn q f) -> LeFunCode ps (lgraph f ne)
    go nil sh = tt
    go (cons q qs) sh =
      let ein  = sh q here
          k    = fst (ne q ein)
          w    = snd (ne q ein)
          cq   = CoherentFun-edge-key q f cf ein
          cvq  = fst (edgeVal q f cf ein)
          le1  = EvalFun-edge-le (mkSigma (LevEl k) w) (lgraph f ne) (fst q) cft'
                   (lgraph-corr f ne q ein) cq (fst (le q ein))
          cef  = Coherent-EvalFun (lgraph f ne) (fst q) cft' cq
          head = LeCode-trans (snd q) w (EvalFun (lgraph f ne) (fst q)) cvq (cw q ein) cef
                   (snd (le q ein)) le1
      in mkSigma head (go qs (\ r rin -> sh r (there rin)))

lgraph-ledges : {n : Nat} (X : Expr n) (rho : EnvApprox TL θ n) (f : FinFun) (ne : LNew f) ->
  ((p : Edge) (ein : EdgeIn p f) ->
     Pair (Eq (lcodeT TL (ldecT TL (fst (ne p ein)))) (fst (ne p ein)))
          (EvalRel X (extL rho (ldecT TL (fst (ne p ein)))) (snd (ne p ein)))) ->
  LEdges X rho (lgraph f ne)
lgraph-ledges X rho f ne h e ein =
  let r  = lgraph-member f ne e ein
      p  = fst r
      pi = fst (snd r)
      eq = snd (snd r)
      k  = fst (ne p pi)
  in Eq-transport (\ e' -> LBody X rho (fst e') (snd e')) (Eq-sym eq)
       (inr (mkSigma k (mkSigma (fst (h p pi)) (mkSigma (EqL-refl k) (snd (h p pi))))))

allU-from-edges : (g : FinFun) (a : FinEl) ->
  ((e : Edge) -> EdgeIn e g -> Pair (FinMem (fst e) a) (FinMem (snd e) U0)) -> FinMemAllU g a
allU-from-edges nil a h = tt
allU-from-edges (cons p ps) a h = mkSigma (h p here) (allU-from-edges ps a (\ e ein -> h e (there ein)))

lgraph-allU : (f : FinFun) (ne : LNew f) ->
  ((p : Edge) (ein : EdgeIn p f) -> FinMem (snd (ne p ein)) U0) -> FinMemAllU (lgraph f ne) LevTy
lgraph-allU f ne h = allU-from-edges (lgraph f ne) LevTy (\ e ein ->
  let r = lgraph-member f ne e ein
  in Eq-transport (\ e' -> Pair (FinMem (fst e') LevTy) (FinMem (snd e') U0)) (Eq-sym (snd (snd r)))
       (mkSigma tt (h (fst r) (fst (snd r)))))

------------------------------------------------------------------------
-- Strictness of the level products of [[LPi A]]
------------------------------------------------------------------------

-- a non-⊥ value of f at x sits above a canonical level token
lpi-nb : {n : Nat} (A : Expr n) (rho : EnvApprox TL θ n) (f : FinFun) ->
  EvalRel (LPi A) rho (LPiCode f) -> (x : FinEl) -> Coherent x -> NotBot (EvalFun f x) ->
  Sigma Nat (\ k -> Pair (Eq (lcodeT TL (ldecT TL k)) k) (LeCode (LevEl k) x))
lpi-nb {TL = TL} A rho f ev x cx nb =
  let cf  = fst ev
      sb  = selectionBelow f x cf cx
      x0  = fst sb
      v0  = fst (snd sb)
      sel = fst (snd (snd sb))
      le0 = fst (snd (snd (snd sb)))
      eq0 = snd (snd (snd (snd sb)))
      cx0 = Coherent-Selection sel cf
      cv0 = Coherent-EvalFun f x cf cx
  in cases x0 v0 cx0 le0 eq0 (snd ev x0 v0 sel)
  where
    cases : (x0 v0 : FinEl) -> Coherent x0 -> LeCode x0 x -> Eq (EvalFun f x) v0 -> LBody A rho x0 v0 ->
      Sigma Nat (\ k -> Pair (Eq (lcodeT TL (ldecT TL k)) k) (LeCode (LevEl k) x))
    cases x0 v0 cx0 le0 eq0 (inl l) =
      absurd (Coherent-val-LeBot-absurd (EvalFun f x)
        (mkSigma (Coherent-EvalFun f x (fst ev) cx) nb) (Eq-transport (\ z -> LeCode z Bot) (Eq-sym eq0) l))
    cases x0 v0 cx0 le0 eq0 (inr (mkSigma k (mkSigma ck (mkSigma lk e)))) =
      mkSigma k (mkSigma ck (LeCode-trans (LevEl k) x0 x tt cx0 cx lk le0))

-- a key of a typed level function carrying a non-⊥ value is a canonical token
lpi-key : {n : Nat} (A : Expr n) (rho : EnvApprox TL θ n) (f : FinFun) ->
  EvalRel (LPi A) rho (LPiCode f) -> (key y : FinEl) -> NotBot y ->
  FinMem key LevTy -> FinMem y (EvalFun f key) ->
  Sigma Nat (\ k -> Pair (Eq (lcodeT TL (ldecT TL k)) k) (Eq key (LevEl k)))
lpi-key {TL = TL} A rho f ev key y nby mk my = cases key (finMem-LevTy-inv key mk) my
  where
    cases : (key : FinEl) -> Either (Eq key Bot) (Sigma Nat (\ k -> Eq key (LevEl k))) ->
      FinMem y (EvalFun f key) ->
      Sigma Nat (\ k -> Pair (Eq (lcodeT TL (ldecT TL k)) k) (Eq key (LevEl k)))
    cases .Bot (inl refl) my =
      let r = lpi-nb A rho f ev Bot tt (NotBot-from-FinMem y (EvalFun f Bot) nby my)
      in absurd (noLev (fst r) (snd (snd r)))
      where
        noLev : (k : Nat) -> LeCode (LevEl k) Bot -> Empty
        noLev k ()
    cases .(LevEl m) (inr (mkSigma m refl)) my =
      let r  = lpi-nb A rho f ev (LevEl m) tt (NotBot-from-FinMem y (EvalFun f (LevEl m)) nby my)
          eq = levEq (fst r) m (snd (snd r))
      in mkSigma m (mkSigma (Eq-transport (\ k -> Eq (lcodeT TL (ldecT TL k)) k) eq (fst (snd r))) refl)

-- the value of a level product at a level instantiates its body
lpi-app-cases : {n : Nat} (A : Expr n) (l : LExpr) (rho : EnvApprox TL θ n) (x w : FinEl) ->
  Coherent x -> LeCode x (LevEl (lcodeT TL (lsubL θ l))) -> LBody A rho x w ->
  EvalRel (lsub1 A l) rho w
lpi-app-cases A l rho x w cx lex (inl l0) =
  Eq-transport (EvalRel (lsub1 A l) rho) (Eq-sym (leBot-eq w l0)) (EvalRel-Bot (lsub1 A l) rho)
lpi-app-cases {TL = TL} {θ = θ} A l rho x w cx lex (inr (mkSigma k (mkSigma ck (mkSigma lk e)))) =
  let c  = lcodeT TL (lsubL θ l)
      eq = levEq k c (LeCode-trans (LevEl k) x (LevEl c) tt cx tt lk lex)
      e' = Eq-transport (\ k' -> EvalRel A (extL rho (ldecT TL k')) w) eq e
  in EvalRel-lsub1-bwd A l rho w (EvalRel-ldec-fwd A rho (lsubL θ l) w e')

LPi-app-type : {n : Nat} (A : Expr n) (l : LExpr) (rho : EnvApprox TL θ n) (f : FinFun) ->
  EvalRel (LPi A) rho (LPiCode f) ->
  EvalRel (lsub1 A l) rho (EvalFun f (LevEl (lcodeT TL (lsubL θ l))))
LPi-app-type {TL = TL} {θ = θ} A l rho f ev =
  let c   = lcodeT TL (lsubL θ l)
      cf  = fst ev
      sb  = selectionBelow f (LevEl c) cf tt
      x   = fst sb
      w   = fst (snd sb)
      sel = fst (snd (snd sb))
      lex = fst (snd (snd (snd sb)))
      eqw = snd (snd (snd (snd sb)))
  in Eq-transport (EvalRel (lsub1 A l) rho) (Eq-sym eqw)
       (lpi-app-cases A l rho x w (Coherent-Selection sel cf) lex (snd ev x w sel))

------------------------------------------------------------------------
-- Formation of level products
------------------------------------------------------------------------

record LPiEd {TL : LCtx} {θ : LSub} {n : Nat} (A : Expr n) (rho : EnvApprox TL θ n) (p : Edge) : Set where
  constructor mkLPiEd
  field
    ek   : Nat
    eck  : Eq (lcodeT TL (ldecT TL ek)) ek
    elk  : LeCode (LevEl ek) (fst p)
    eb   : FinEl
    eble : LeCode (snd p) eb
    ebev : EvalRel A (extL rho (ldecT TL ek)) eb
    ebU  : FinMem eb U0

InvTyp-LPi : {n : Nat} {G : Ctx n} {l : LExpr} (A : Expr n) (rho : EnvApprox TL θ n) -> Fits G rho ->
  ((k : Nat) -> InvTyp G A (U l) (extL rho (ldecT TL k))) ->
  InvTyp G (LPi A) (U l) rho
InvTyp-LPi {TL = TL} {θ = θ} {l = l} A rho fits ih Bot ev =
  mkSigma Bot (mkSigma (UCode (lcodeT TL (lsubL θ l))) (mkSigma tt (mkSigma tt (mkSigma tt (mkSigma tt (EqL-refl (lcodeT TL (lsubL θ l))))))))
InvTyp-LPi A rho fits ih (UCode _) ()
InvTyp-LPi A rho fits ih LevTy ()
InvTyp-LPi A rho fits ih (LevEl _) ()
InvTyp-LPi A rho fits ih (FunEl _) ()
InvTyp-LPi A rho fits ih (PiCode _ _) ()
InvTyp-LPi {TL = TL} {θ = θ} {l = l} A rho fits ih (LPiCode f) ev =
  mkSigma (LPiCode f') (mkSigma (UCode (lcodeT TL (lsubL θ l))) (mkSigma lf (mkSigma ev' (mkSigma fmU (mkSigma tt (EqL-refl (lcodeT TL (lsubL θ l))))))))
  where
    crho = Fits-CoherentEnv rho fits
    cf : CoherentFunTail f
    cf = fst ev
    edges = LPi-edgewise A rho f ev

    ed : (p : Edge) -> EdgeIn p f -> LPiEd A rho p
    ed p ein =
      let cvp = edgeVal p f cf ein
          r   = LBody-nb A rho (fst p) (snd p) (fst cvp) (snd cvp) (edges p ein)
          k   = fst r
          ck  = fst (snd r)
          lk  = fst (snd (snd r))
          e   = snd (snd (snd r))
          ty  = ih k (snd p) e
          b'  = fst ty
          a'' = fst (snd ty)
          le  = fst (snd (snd ty))
          e'  = fst (snd (snd (snd ty)))
          fm  = fst (snd (snd (snd (snd ty))))
          evU = snd (snd (snd (snd (snd ty))))
      in mkLPiEd k ck lk b' le e' (finMem-in-U l (extL rho (ldecT TL k)) a'' evU b' fm)

    ne : LNew f
    ne p ein = mkSigma (LPiEd.ek (ed p ein)) (LPiEd.eb (ed p ein))

    f' : FinFun
    f' = lgraph f ne

    ch : (p : Edge) (ein : EdgeIn p f) -> Pair (Coherent (snd (ne p ein))) (NotBot (snd (ne p ein)))
    ch p ein =
      let d = ed p ein ; cvp = edgeVal p f cf ein
      in mkSigma (coh-from-aU (LPiEd.eb d) (LPiEd.ebU d))
                 (NotBot-from-Le (snd p) (LPiEd.eb d) (fst cvp) (snd cvp) (LPiEd.eble d))

    cm : (p : Edge) (ein : EdgeIn p f) (q : Edge) (qin : EdgeIn q f) ->
      Eq (fst (ne p ein)) (fst (ne q qin)) -> Comp (snd (ne p ein)) (snd (ne q qin))
    cm p ein q qin eq =
      let d1 = ed p ein ; d2 = ed q qin
      in EvalRel-Comp A (extL rho (ldecT TL (LPiEd.ek d1))) (CoherentEnv-reidx rho crho) _ _ (LPiEd.ebev d1)
           (Eq-transport (\ k -> EvalRel A (extL rho (ldecT TL k)) (LPiEd.eb d2)) (Eq-sym eq) (LPiEd.ebev d2))

    cft' : CoherentFunTail f'
    cft' = lgraph-cft f ne ch cm

    lf : LeFunCode f f'
    lf = lgraph-lf f ne cf cft' (\ p ein -> mkSigma (LPiEd.elk (ed p ein)) (LPiEd.eble (ed p ein)))
           (\ p ein -> fst (ch p ein))

    ev' : EvalRel (LPi A) rho (LPiCode f')
    ev' = mkSigma cft' (LBody-from-edges A rho crho f' cft'
            (lgraph-ledges A rho f ne (\ p ein -> mkSigma (LPiEd.eck (ed p ein)) (LPiEd.ebev (ed p ein)))))

    fmU : FinMem (LPiCode f') (UCode (lcodeT TL (lsubL θ l)))
    fmU = finMem-U-lvl (LPiCode f') 0 (lcodeT TL (lsubL θ l))
            (finMem-LpiU-mk f' (lgraph-allU f ne (\ p ein -> LPiEd.ebU (ed p ein))) cft')

------------------------------------------------------------------------
-- Level abstraction
------------------------------------------------------------------------

record LLamEd {TL : LCtx} {θ : LSub} {n : Nat} (A M : Expr n) (rho : EnvApprox TL θ n) (p : Edge) : Set where
  constructor mkLLamEd
  field
    ek   : Nat
    eck  : Eq (lcodeT TL (ldecT TL ek)) ek
    elk  : LeCode (LevEl ek) (fst p)
    ey   : FinEl
    eyle : LeCode (snd p) ey
    eyev : EvalRel M (extL rho (ldecT TL ek)) ey
    eb   : FinEl
    eyb  : FinMem ey eb
    ebev : EvalRel A (extL rho (ldecT TL ek)) eb

InvTyp-LLam : {n : Nat} {G : Ctx n} (A M : Expr n) (rho : EnvApprox TL θ n) -> Fits G rho ->
  ((k : Nat) -> InvTyp G M A (extL rho (ldecT TL k))) ->
  InvTyp G (LLam M) (LPi A) rho
InvTyp-LLam A M rho fits ih Bot ev =
  mkSigma Bot (mkSigma Bot (mkSigma tt (mkSigma tt (mkSigma tt tt))))
InvTyp-LLam A M rho fits ih (UCode _) ()
InvTyp-LLam A M rho fits ih LevTy ()
InvTyp-LLam A M rho fits ih (LevEl _) ()
InvTyp-LLam A M rho fits ih (PiCode _ _) ()
InvTyp-LLam A M rho fits ih (LPiCode _) ()
InvTyp-LLam A M rho fits ih (FunEl nil) ev = absurd (fst ev)
InvTyp-LLam {TL = TL} A M rho fits ih (FunEl (cons p0 ps0)) ev =
  mkSigma (FunEl h) (mkSigma (LPiCode ft) (mkSigma lf (mkSigma evH (mkSigma fmH evF))))
  where
    g : FinFun
    g = cons p0 ps0
    crho = Fits-CoherentEnv rho fits
    cg : CoherentFunTail g
    cg = fst ev
    edges = LLam-edgewise M rho g ev

    ed : (p : Edge) -> EdgeIn p g -> LLamEd A M rho p
    ed p ein =
      let cvp = edgeVal p g cg ein
          r   = LBody-nb M rho (fst p) (snd p) (fst cvp) (snd cvp) (edges p ein)
          k   = fst r
          ty  = ih k (snd p) (snd (snd (snd r)))
      in mkLLamEd k (fst (snd r)) (fst (snd (snd r)))
           (fst ty) (fst (snd (snd ty))) (fst (snd (snd (snd ty))))
           (fst (snd ty)) (fst (snd (snd (snd (snd ty))))) (snd (snd (snd (snd (snd ty)))))

    neH : LNew g
    neH p ein = mkSigma (LLamEd.ek (ed p ein)) (LLamEd.ey (ed p ein))
    neF : LNew g
    neF p ein = mkSigma (LLamEd.ek (ed p ein)) (LLamEd.eb (ed p ein))

    h : FinFun
    h = lgraph g neH
    ft : FinFun
    ft = lgraph g neF

    chH : (p : Edge) (ein : EdgeIn p g) -> Pair (Coherent (snd (neH p ein))) (NotBot (snd (neH p ein)))
    chH p ein =
      let d = ed p ein ; cvp = edgeVal p g cg ein
      in mkSigma (FinMem-coh-u (LLamEd.ey d) (LLamEd.eb d) (LLamEd.eyb d))
                 (NotBot-from-Le (snd p) (LLamEd.ey d) (fst cvp) (snd cvp) (LLamEd.eyle d))

    chF : (p : Edge) (ein : EdgeIn p g) -> Pair (Coherent (snd (neF p ein))) (NotBot (snd (neF p ein)))
    chF p ein =
      let d = ed p ein
      in mkSigma (coh-from-aU (LLamEd.eb d) (FinMem-a-in-U (LLamEd.ey d) (LLamEd.eb d) (LLamEd.eyb d)))
                 (NotBot-from-FinMem (LLamEd.ey d) (LLamEd.eb d) (snd (chH p ein)) (LLamEd.eyb d))

    cmH : (p : Edge) (ein : EdgeIn p g) (q : Edge) (qin : EdgeIn q g) ->
      Eq (fst (neH p ein)) (fst (neH q qin)) -> Comp (snd (neH p ein)) (snd (neH q qin))
    cmH p ein q qin eq =
      let d1 = ed p ein ; d2 = ed q qin
      in EvalRel-Comp M (extL rho (ldecT TL (LLamEd.ek d1))) (CoherentEnv-reidx rho crho) _ _ (LLamEd.eyev d1)
           (Eq-transport (\ k -> EvalRel M (extL rho (ldecT TL k)) (LLamEd.ey d2)) (Eq-sym eq) (LLamEd.eyev d2))

    cmF : (p : Edge) (ein : EdgeIn p g) (q : Edge) (qin : EdgeIn q g) ->
      Eq (fst (neF p ein)) (fst (neF q qin)) -> Comp (snd (neF p ein)) (snd (neF q qin))
    cmF p ein q qin eq =
      let d1 = ed p ein ; d2 = ed q qin
      in EvalRel-Comp A (extL rho (ldecT TL (LLamEd.ek d1))) (CoherentEnv-reidx rho crho) _ _ (LLamEd.ebev d1)
           (Eq-transport (\ k -> EvalRel A (extL rho (ldecT TL k)) (LLamEd.eb d2)) (Eq-sym eq) (LLamEd.ebev d2))

    cftH : CoherentFunTail h
    cftH = lgraph-cft g neH chH cmH
    cftF : CoherentFunTail ft
    cftF = lgraph-cft g neF chF cmF

    lf : LeFunCode g h
    lf = lgraph-lf g neH cg cftH (\ p ein -> mkSigma (LLamEd.elk (ed p ein)) (LLamEd.eyle (ed p ein)))
           (\ p ein -> fst (chH p ein))

    evH : EvalRel (LLam M) rho (FunEl h)
    evH = mkSigma cftH (LBody-from-edges M rho crho h cftH
            (lgraph-ledges M rho g neH (\ p ein -> mkSigma (LLamEd.eck (ed p ein)) (LLamEd.eyev (ed p ein)))))

    evF : EvalRel (LPi A) rho (LPiCode ft)
    evF = mkSigma cftF (LBody-from-edges A rho crho ft cftF
            (lgraph-ledges A rho g neF (\ p ein -> mkSigma (LLamEd.eck (ed p ein)) (LLamEd.ebev (ed p ein)))))

    allUF : FinMemAllU ft LevTy
    allUF = lgraph-allU g neF (\ p ein -> FinMem-a-in-U (LLamEd.ey (ed p ein)) (LLamEd.eb (ed p ein)) (LLamEd.eyb (ed p ein)))

    go : (ps : FinFun) (sh : (q : Edge) -> EdgeIn q ps -> EdgeIn q g) ->
      FinMemFun (lgraph ps (\ q qin -> neH q (sh q qin))) LevTy ft
    go nil sh = tt
    go (cons q qs) sh =
      let qin = sh q here
          d   = ed q qin
          k   = LLamEd.ek d
          b   = LLamEd.eb d
          cb  = fst (chF q qin)
          le-b = EvalFun-edge-le (mkSigma (LevEl k) b) ft (LevEl k) cftF (lgraph-corr g neF q qin) tt (EqL-refl k)
          fmy = finMem-upward (LLamEd.ey d) b (EvalFun ft (LevEl k)) le-b cb
                  (Coherent-EvalFun ft (LevEl k) cftF tt) (LLamEd.eyb d)
                  (EvalFun-in-UCode ft (LevEl k) LevTy cftF tt allUF)
      in mkSigma (mkSigma tt fmy) (go qs (\ r rin -> sh r (there rin)))

    fmH : FinMem (FunEl h) (LPiCode ft)
    fmH = finMem-Lfunel-mk h ft (go g (\ q qin -> qin)) cftH (finMem-LpiU-mk ft allUF cftF)

------------------------------------------------------------------------
-- Level application
------------------------------------------------------------------------

InvTyp-LApp : {n : Nat} {G : Ctx n} (A t : Expr n) (l : LExpr) (rho : EnvApprox TL θ n) -> Fits G rho ->
  InvTyp G t (LPi A) rho -> InvTyp G (LApp t l) (lsub1 A l) rho
InvTyp-LApp {TL = TL} {θ = θ} A t l rho fits invT u ev =
  nb-elim (\ b -> EvalRel (LApp t l) rho b -> Typed (LApp t l) (lsub1 A l) rho b)
    (\ _ -> mkSigma Bot (mkSigma Bot (mkSigma tt (mkSigma tt (mkSigma tt (EvalRel-Bot (lsub1 A l) rho))))))
    main u ev
  where
    c : Nat
    c = lcodeT TL (lsubL θ l)
    crho = Fits-CoherentEnv rho fits

    hcase : (b : FinEl) -> NotBot b -> Coherent b -> (w a' : FinEl) ->
      LeCode (FunEl (cons (mkSigma (LevEl c) b) nil)) w -> EvalRel t rho w -> FinMem w a' ->
      EvalRel (LPi A) rho a' -> Typed (LApp t l) (lsub1 A l) rho b
    hcase b nb cb Bot a' () ew fm evPi
    hcase b nb cb (UCode _) a' () ew fm evPi
    hcase b nb cb LevTy a' () ew fm evPi
    hcase b nb cb (LevEl _) a' () ew fm evPi
    hcase b nb cb (PiCode _ _) a' () ew fm evPi
    hcase b nb cb (LPiCode _) a' () ew fm evPi
    hcase b nb cb (FunEl g') Bot le ew () evPi
    hcase b nb cb (FunEl g') (UCode _) le ew fm ()
    hcase b nb cb (FunEl g') LevTy le ew fm ()
    hcase b nb cb (FunEl g') (LevEl _) le ew fm ()
    hcase b nb cb (FunEl g') (FunEl _) le ew fm ()
    hcase b nb cb (FunEl g') (PiCode _ _) le ew fm ()
    hcase b nb cb (FunEl g') (LPiCode f) le ew fm evPi =
      let le-u   = fst le
          cg'    = finMem-Lfunel-coh g' f fm
          ctg'   = cft-from-cf g' cg'
          fmfun  = finMem-Lfunel-fun g' f fm
          wf     = finMem-Lfunel-wf g' f fm
          allU   = finMem-LpiU-allU f wf
          cff    = finMem-LpiU-cft f wf
          y      = EvalFun g' (LevEl c)
          cy     = Coherent-EvalFun g' (LevEl c) ctg' tt
          nby    = NotBot-from-Le b y cb nb le-u
          sb     = selectionBelow g' (LevEl c) ctg' tt
          u0     = fst sb
          v0     = fst (snd sb)
          sel    = fst (snd (snd sb))
          le-u0  = fst (snd (snd (snd sb)))
          eq-v0  = snd (snd (snd (snd sb)))
          cu0    = Coherent-Selection sel ctg'
          fm-v0  = FinMem-Selection-codomain LevTy f sel fmfun ctg' cff allU
          Tt     = EvalFun f (LevEl c)
          mon    = EvalFun-mon-arg f u0 (LevEl c) le-u0 cff cu0 tt
          fm-y0  = finMem-upward v0 (EvalFun f u0) Tt mon (Coherent-EvalFun f u0 cff cu0)
                     (Coherent-EvalFun f (LevEl c) cff tt) fm-v0 (EvalFun-in-UCode f (LevEl c) LevTy cff tt allU)
          fm-y   = Eq-transport (\ z -> FinMem z Tt) (Eq-sym eq-v0) fm-y0
          ev-sing = EvalRel-down t rho (FunEl g') (FunEl (cons (mkSigma (LevEl c) y) nil)) crho
                      (mkCFT tt cy nby tt tt) ew (mkSigma (LeCode-refl y cy) tt)
      in mkSigma y (mkSigma Tt (mkSigma le-u (mkSigma (nbody-in y nby ev-sing)
           (mkSigma fm-y (LPi-app-type A l rho f evPi)))))

    main : (b : FinEl) -> NotBot b -> EvalRel (LApp t l) rho b -> Typed (LApp t l) (lsub1 A l) rho b
    main b nb e0 =
      let e  = nbody-out b nb e0
          ty = invT _ e
      in hcase b nb (EvalRel-coh (LApp t l) rho b e0) (fst ty) (fst (snd ty)) (fst (snd (snd ty)))
           (fst (snd (snd (snd ty)))) (fst (snd (snd (snd (snd ty))))) (snd (snd (snd (snd (snd ty)))))

------------------------------------------------------------------------
-- Congruences
------------------------------------------------------------------------

LPi-map : {n : Nat} (A A' : Expr n) (rho : EnvApprox TL θ n) ->
  ((k : Nat) (v : FinEl) -> EvalRel A (extL rho (ldecT TL k)) v -> EvalRel A' (extL rho (ldecT TL k)) v) ->
  (u : FinEl) -> EvalRel (LPi A) rho u -> EvalRel (LPi A') rho u
LPi-map A A' rho h Bot ev = tt
LPi-map A A' rho h (LPiCode f) ev =
  mkSigma (fst ev) (\ u v sel -> lbody-map A A' rho rho u v (\ k e -> h k v e) (snd ev u v sel))
LPi-map A A' rho h (UCode _) ()
LPi-map A A' rho h LevTy ()
LPi-map A A' rho h (LevEl _) ()
LPi-map A A' rho h (FunEl _) ()
LPi-map A A' rho h (PiCode _ _) ()

LLam-map : {n : Nat} (M M' : Expr n) (rho : EnvApprox TL θ n) ->
  ((k : Nat) (v : FinEl) -> EvalRel M (extL rho (ldecT TL k)) v -> EvalRel M' (extL rho (ldecT TL k)) v) ->
  (u : FinEl) -> EvalRel (LLam M) rho u -> EvalRel (LLam M') rho u
LLam-map M M' rho h Bot ev = tt
LLam-map M M' rho h (FunEl g) ev =
  mkSigma (fst ev) (\ u v sel -> lbody-map M M' rho rho u v (\ k e -> h k v e) (snd ev u v sel))
LLam-map M M' rho h (UCode _) ()
LLam-map M M' rho h LevTy ()
LLam-map M M' rho h (LevEl _) ()
LLam-map M M' rho h (PiCode _ _) ()
LLam-map M M' rho h (LPiCode _) ()

InvConv-LPi : {n : Nat} {G : Ctx n} {l : LExpr} (A A' : Expr n) (rho : EnvApprox TL θ n) -> Fits G rho ->
  ((k : Nat) -> InvConv G A A' (U l) (extL rho (ldecT TL k))) ->
  InvConv G (LPi A) (LPi A') (U l) rho
InvConv-LPi {l = l} A A' rho fits h =
  mkSigma (InvTyp-LPi {l = l} A rho fits (\ k -> fst (h k)))
    (mkSigma (InvTyp-LPi {l = l} A' rho fits (\ k -> fst (snd (h k))))
      (mkSigma (LPi-map A A' rho (\ k v e -> fst (snd (snd (h k))) v e))
               (LPi-map A' A rho (\ k v e -> snd (snd (snd (h k))) v e))))

InvConv-LLam : {n : Nat} {G : Ctx n} (A M M' : Expr n) (rho : EnvApprox TL θ n) -> Fits G rho ->
  ((k : Nat) -> InvConv G M M' A (extL rho (ldecT TL k))) ->
  InvConv G (LLam M) (LLam M') (LPi A) rho
InvConv-LLam A M M' rho fits h =
  mkSigma (InvTyp-LLam A M rho fits (\ k -> fst (h k)))
    (mkSigma (InvTyp-LLam A M' rho fits (\ k -> fst (snd (h k))))
      (mkSigma (LLam-map M M' rho (\ k v e -> fst (snd (snd (h k))) v e))
               (LLam-map M' M rho (\ k v e -> snd (snd (snd (h k))) v e))))

InvConv-LApp-fun : {n : Nat} {G : Ctx n} (A t t' : Expr n) (l : LExpr) (rho : EnvApprox TL θ n) ->
  Fits G rho -> InvConv G t t' (LPi A) rho -> InvConv G (LApp t l) (LApp t' l) (lsub1 A l) rho
InvConv-LApp-fun A t t' l rho fits h =
  mkSigma (InvTyp-LApp A t l rho fits (fst h))
    (mkSigma (InvTyp-LApp A t' l rho fits (fst (snd h)))
      (mkSigma (mp t t' (fst (snd (snd h)))) (mp t' t (snd (snd (snd h))))))
  where
    mp : (F F' : Expr _) -> ((w : FinEl) -> EvalRel F rho w -> EvalRel F' rho w) ->
      (u : FinEl) -> EvalRel (LApp F l) rho u -> EvalRel (LApp F' l) rho u
    mp F F' k u ev = nbody-map {X = LAppX F l rho u} {Y = LAppX F' l rho u} u (k _) ev

InvConv-LApp-lvl : {n : Nat} {G : Ctx n} (A t : Expr n) (l l' : LExpr) (rho : EnvApprox TL θ n) ->
  Fits G rho -> InvTyp G t (LPi A) rho -> Valid TL (lsubL θ l) (lsubL θ l') ->
  InvConv G (LApp t l) (LApp t l') (lsub1 A l) rho
InvConv-LApp-lvl {TL = TL} {θ = θ} {G = G} A t l l' rho fits invT v =
  mkSigma invL (mkSigma (InvTyp-equiv {G = G} {M = LApp t l} {N = LApp t l'} {T = lsub1 A l} {rho = rho} invL bwd fwd)
    (mkSigma fwd bwd))
  where
    eq : Eq (lcodeT TL (lsubL θ l)) (lcodeT TL (lsubL θ l'))
    eq = LDec.lcode-sound (D TL) v
    invL = InvTyp-LApp A t l rho fits invT
    fwd : (u : FinEl) -> EvalRel (LApp t l) rho u -> EvalRel (LApp t l') rho u
    fwd u ev = nbody-map {X = LAppX t l rho u} {Y = LAppX t l' rho u} u
      (Eq-transport (\ c -> EvalRel t rho (FunEl (cons (mkSigma (LevEl c) u) nil))) eq) ev
    bwd : (u : FinEl) -> EvalRel (LApp t l') rho u -> EvalRel (LApp t l) rho u
    bwd u ev = nbody-map {X = LAppX t l' rho u} {Y = LAppX t l rho u} u
      (Eq-transport (\ c -> EvalRel t rho (FunEl (cons (mkSigma (LevEl c) u) nil))) (Eq-sym eq)) ev

------------------------------------------------------------------------
-- β:  (⟨α⟩M) l = M(l/α)
------------------------------------------------------------------------

InvConv-LApp-beta : {n : Nat} {G : Ctx n} (A M : Expr n) (l : LExpr) (rho : EnvApprox TL θ n) ->
  Fits G rho -> ((k : Nat) -> InvTyp G M A (extL rho (ldecT TL k))) ->
  InvConv G (LApp (LLam M) l) (lsub1 M l) (lsub1 A l) rho
InvConv-LApp-beta {TL = TL} {θ = θ} {G = G} A M l rho fits ih =
  mkSigma invL (mkSigma (InvTyp-equiv {G = G} {M = LApp (LLam M) l} {N = lsub1 M l} {T = lsub1 A l} {rho = rho} invL bwd fwd)
    (mkSigma fwd bwd))
  where
    c : Nat
    c = lcodeT TL (lsubL θ l)
    crho = Fits-CoherentEnv rho fits
    invL = InvTyp-LApp A (LLam M) l rho fits (InvTyp-LLam A M rho fits ih)

    fwdN : (b : FinEl) -> NotBot b -> EvalRel (LLam M) rho (FunEl (cons (mkSigma (LevEl c) b) nil)) ->
      EvalRel (lsub1 M l) rho b
    fwdN b nb e =
      let lb  = LLam-edgewise M rho _ e (mkSigma (LevEl c) b) here
          r   = LBody-nb M rho (LevEl c) b (val-coh (fst e)) nb lb
          k   = fst r
          eq  = levEq k c (fst (snd (snd r)))
          ev' = Eq-transport (\ k' -> EvalRel M (extL rho (ldecT TL k')) b) eq (snd (snd (snd r)))
      in EvalRel-lsub1-bwd M l rho b (EvalRel-ldec-fwd M rho (lsubL θ l) b ev')

    fwd : (u : FinEl) -> EvalRel (LApp (LLam M) l) rho u -> EvalRel (lsub1 M l) rho u
    fwd = nb-elim (\ b -> EvalRel (LApp (LLam M) l) rho b -> EvalRel (lsub1 M l) rho b)
            (\ _ -> EvalRel-Bot (lsub1 M l) rho) (\ b nb e0 -> fwdN b nb (nbody-out b nb e0))

    bwdN : (b : FinEl) -> NotBot b -> EvalRel (lsub1 M l) rho b ->
      EvalRel (LLam M) rho (FunEl (cons (mkSigma (LevEl c) b) nil))
    bwdN b nb ev =
      let e2 = EvalRel-ldec-bwd M rho (lsubL θ l) b (EvalRel-lsub1-fwd M l rho b ev)
          cb = EvalRel-coh (lsub1 M l) rho b ev
          cg : CoherentFunTail (cons (mkSigma (LevEl c) b) nil)
          cg = mkCFT tt cb nb tt tt
          eds = LEdges-cons M rho (mkSigma (LevEl c) b) nil
                  (inr (mkSigma c (mkSigma (lcode-canon TL (lsubL θ l)) (mkSigma (EqL-refl c) e2))))
                  (\ q ())
      in mkSigma cg (LBody-from-edges M rho crho _ cg eds)

    bwd : (u : FinEl) -> EvalRel (lsub1 M l) rho u -> EvalRel (LApp (LLam M) l) rho u
    bwd u ev = nbody-inN u (\ nb -> bwdN u nb ev)

------------------------------------------------------------------------
-- η:  t = ⟨α⟩(t α)   at a level product
------------------------------------------------------------------------

NotFun : FinEl -> Set
NotFun (FunEl _)    = Empty
NotFun Bot          = Empty
NotFun (UCode _)    = Top
NotFun LevTy        = Top
NotFun (LevEl _)    = Top
NotFun (PiCode _ _) = Top
NotFun (LPiCode _)  = Top

fmf-at : (h : FinFun) (a : FinEl) (f : FinFun) -> FinMemFun h a f ->
  (e : Edge) -> EdgeIn e h -> Pair (FinMem (fst e) a) (FinMem (snd e) (EvalFun f (fst e)))
fmf-at (cons q qs) a f fmf .q here = fst fmf
fmf-at (cons q qs) a f fmf e (there ein) = fmf-at qs a f (snd fmf) e ein

InvConv-LApp-eta : {n : Nat} {G : Ctx n} (A t : Expr n) (rho : EnvApprox TL θ n) ->
  Fits G rho -> InvTyp G t (LPi A) rho ->
  InvConv G t (LLam (LApp (lshiftE t) (lvar zero))) (LPi A) rho
InvConv-LApp-eta {TL = TL} {θ = θ} {G = G} A t rho fits invT =
  mkSigma invT (mkSigma (InvTyp-equiv {G = G} {M = t} {N = etaT} {T = LPi A} {rho = rho} invT bwd fwd)
    (mkSigma fwd bwd))
  where
    etaT : Expr _
    etaT = LLam (LApp (lshiftE t) (lvar zero))
    Body : Expr _
    Body = LApp (lshiftE t) (lvar zero)
    crho = Fits-CoherentEnv rho fits

    mkEdge : (k : Nat) -> Eq (lcodeT TL (ldecT TL k)) k -> (y : FinEl) -> NotBot y ->
      EvalRel t rho (FunEl (cons (mkSigma (LevEl k) y) nil)) -> EvalRel Body (extL rho (ldecT TL k)) y
    mkEdge k ck y nb e =
      nbody-in y nb
        (Eq-transport (\ c' -> EvalRel (lshiftE t) (extL rho (ldecT TL k)) (FunEl (cons (mkSigma (LevEl c') y) nil)))
          (Eq-sym ck) (EvalRel-lshift-bwd t rho (ldecT TL k) _ e))

    decEdge : (k : Nat) -> Eq (lcodeT TL (ldecT TL k)) k -> (y : FinEl) -> NotBot y ->
      EvalRel Body (extL rho (ldecT TL k)) y -> EvalRel t rho (FunEl (cons (mkSigma (LevEl k) y) nil))
    decEdge k ck y nb e =
      EvalRel-lshift-fwd t rho (ldecT TL k) _
        (Eq-transport (\ c' -> EvalRel (lshiftE t) (extL rho (ldecT TL k)) (FunEl (cons (mkSigma (LevEl c') y) nil)))
          ck (nbody-out y nb e))

    noLPi : (pa x : FinEl) -> NotFun x -> FinMem x pa -> EvalRel (LPi A) rho pa -> Empty
    noLPi Bot x nf m e = nbBot x nf (finMem-Bot-eq x m)
      where
        nbBot : (x : FinEl) -> NotFun x -> Eq x Bot -> Empty
        nbBot .Bot () refl
    noLPi (UCode _) x nf m ()
    noLPi LevTy x nf m ()
    noLPi (LevEl _) x nf m ()
    noLPi (FunEl _) x nf m ()
    noLPi (PiCode _ _) x nf m ()
    noLPi (LPiCode f) (UCode _) nf () e
    noLPi (LPiCode f) LevTy nf () e
    noLPi (LPiCode f) (LevEl _) nf () e
    noLPi (LPiCode f) (PiCode _ _) nf () e
    noLPi (LPiCode f) (LPiCode _) nf () e
    noLPi (LPiCode f) Bot () m e
    noLPi (LPiCode f) (FunEl _) () m e

    lamG : (g' f : FinFun) -> FinMem (FunEl g') (LPiCode f) -> EvalRel (LPi A) rho (LPiCode f) ->
      EvalRel t rho (FunEl g') -> EvalRel etaT rho (FunEl g')
    lamG g' f fm evPi evt = mkSigma cg' (LBody-from-edges Body rho crho g' ctg' edges)
      where
        cg' = finMem-Lfunel-coh g' f fm
        ctg' = cft-from-cf g' cg'
        fmfun = finMem-Lfunel-fun g' f fm
        edges : LEdges Body rho g'
        edges p ein =
          let cv   = edgeVal p g' ctg' ein
              fk   = fmf-at g' LevTy f fmfun p ein
              r    = lpi-key A rho f evPi (fst p) (snd p) (snd cv) (fst fk) (snd fk)
              k    = fst r
              ck   = fst (snd r)
              eqk  = snd (snd r)
              ckey = CoherentFun-edge-key p g' ctg' ein
              evs  = EvalRel-down t rho (FunEl g') (FunEl (cons p nil)) crho (mkCFT ckey (fst cv) (snd cv) tt tt) evt
                       (mkSigma (EvalFun-edge-le p g' (fst p) ctg' ein ckey (LeCode-refl (fst p) ckey)) tt)
              evs' = Eq-transport (\ z -> EvalRel t rho (FunEl (cons (mkSigma z (snd p)) nil))) eqk evs
          in inr (mkSigma k (mkSigma ck
               (mkSigma (Eq-transport (\ z -> LeCode (LevEl k) z) (Eq-sym eqk) (EqL-refl k))
                        (mkEdge k ck (snd p) (snd cv) evs'))))

    fwd-main : (w w' pa : FinEl) -> Coherent w -> LeCode w w' -> EvalRel t rho w' -> FinMem w' pa ->
      EvalRel (LPi A) rho pa -> EvalRel etaT rho w
    fwd-main w Bot pa cw le evt fm evPi =
      Eq-transport (EvalRel etaT rho) (Eq-sym (leBot-eq w le)) (EvalRel-Bot etaT rho)
    fwd-main w (FunEl g') (LPiCode f) cw le evt fm evPi =
      EvalRel-down etaT rho (FunEl g') w crho cw (lamG g' f fm evPi evt) le
    fwd-main w (FunEl g') Bot cw le evt () evPi
    fwd-main w (FunEl g') (UCode _) cw le evt fm ()
    fwd-main w (FunEl g') LevTy cw le evt fm ()
    fwd-main w (FunEl g') (LevEl _) cw le evt fm ()
    fwd-main w (FunEl g') (FunEl _) cw le evt fm ()
    fwd-main w (FunEl g') (PiCode _ _) cw le evt fm ()
    fwd-main w (UCode k) pa cw le evt fm evPi = absurd (noLPi pa (UCode k) tt fm evPi)
    fwd-main w LevTy pa cw le evt fm evPi = absurd (noLPi pa LevTy tt fm evPi)
    fwd-main w (LevEl k) pa cw le evt fm evPi = absurd (noLPi pa (LevEl k) tt fm evPi)
    fwd-main w (PiCode a0 f0) pa cw le evt fm evPi = absurd (noLPi pa (PiCode a0 f0) tt fm evPi)
    fwd-main w (LPiCode f0) pa cw le evt fm evPi = absurd (noLPi pa (LPiCode f0) tt fm evPi)

    fwd : (w : FinEl) -> EvalRel t rho w -> EvalRel etaT rho w
    fwd w ev =
      let ty = invT w ev
      in fwd-main w (fst ty) (fst (snd ty)) (EvalRel-coh t rho w ev) (fst (snd (snd ty)))
           (fst (snd (snd (snd ty)))) (fst (snd (snd (snd (snd ty))))) (snd (snd (snd (snd (snd ty)))))

    bwd : (w : FinEl) -> EvalRel etaT rho w -> EvalRel t rho w
    bwd Bot ev = EvalRel-Bot t rho
    bwd (UCode _) ()
    bwd LevTy ()
    bwd (LevEl _) ()
    bwd (PiCode _ _) ()
    bwd (LPiCode _) ()
    bwd (FunEl g) ev = build-graph t rho crho g (fst ev) edgeB
      where
        ctg = cft-from-cf g (fst ev)
        edgeB : (p : Edge) -> EdgeIn p g -> EvalRel t rho (FunEl (cons p nil))
        edgeB p ein =
          let cv  = edgeVal p g ctg ein
              r   = LBody-nb Body rho (fst p) (snd p) (fst cv) (snd cv) (LLam-edgewise Body rho g ev p ein)
              k   = fst r
              e1  = decEdge k (fst (snd r)) (snd p) (snd cv) (snd (snd (snd r)))
              eqk = levLe-eq k (fst p) (fst (snd (snd r)))
          in Eq-transport (\ z -> EvalRel t rho (FunEl (cons (mkSigma z (snd p)) nil))) (Eq-sym eqk) e1
