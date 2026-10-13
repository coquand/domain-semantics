{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Adq/Base.agda  (Tarski port of MAHLOINJ/Adq/Base)
--
-- Infrastructure of the fundamental lemma: related (convertible)
-- substitutions over an environment, their symmetry / reflexivity /
-- extension, and the code-adjustment helper.
------------------------------------------------------------------------

module MAHLORT.Adq.Base where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
import MAHLOINJ.Domain.Basic as D
open D using (Top ; tt ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl ; PairEl ; SigmaCode
             ; FinFun ; nil ; cons ; mkSigma) renaming (fst to dfst ; snd to dsnd)
open import MAHLOINJ.Domain.Kernel
  using (EvalFun ; LeCode ; FinMem ; Comp ; Sup ; Coherent ; coh-from-aU ; FinMem-coh-u ; FinMem-a-in-U
        ; LeCode-Sup-left ; LeCode-Sup-right ; LeCode-trans ; Coherent-Sup ; finMem-upward ; FinMem-Sup-element
        ; EvalFun-in-UCode ; finMem-funel-fun ; finMem-funel-coh ; finMem-funel-wf ; finMemC-pair-fst ; finMemC-pair-snd
        ; CoherentFunTail ; cft-from-cf)
open import MAHLOINJ.Model.Selection
  using (Selection ; FinMem-Selection ; FinMem-Selection-codomain ; FinMemAllU-Selection ; FinMem-Selection-UCode)
open import MAHLORT.Valid.Props using (CodeU ; piU ; sigU)
open import MAHLOINJ.Model.Comb using (Ideal)
open import MAHLORT.Model
open import MAHLORT.Model using (EvalRel-wk ; EvalRel-unwk)
open import MAHLORT.Model using (Fits ; Fits-coh ; Fits-ext ; Fits-var)
open import MAHLORT.Syntax.Lemmas
open import MAHLORT.Syntax.Subst
open import MAHLORT.Syntax.Funct
open import MAHLORT.Syntax.Presup using (pCv ; pTE ; pTm)
open import MAHLORT.Valid.HeadRed
open import MAHLORT.Valid.Stage
open import MAHLOINJ.Valid.Aux using (mem-up)
open import MAHLORT.Valid.Public

transport3 : {A B C : Set} (P : A -> B -> C -> Set) {a a' : A} {b b' : B} {c c' : C} ->
  Eq a a' -> Eq b b' -> Eq c c' -> P a b c -> P a' b' c'
transport3 P refl refl refl x = x

------------------------------------------------------------------------
-- related substitutions
------------------------------------------------------------------------

record SR {h g : Num} (H : Ctx h) (G : Ctx g) (s s' : Sub h g) (rho : EnvApprox g) : Set where
  constructor mkSR
  field
    cs : CSub H G s s'
    ty : (i : Fin g) (a : FinEl) -> EvalRel (lookup G i) rho a -> FinMem a UCode ->
         RTy H (substExpr s (lookup G i)) (substExpr s' (lookup G i)) a
    tm : (i : Fin g) (a : FinEl) -> EvalRel (lookup G i) rho a -> FinMem a UCode -> FinMem (lookupEnv i rho) a ->
         RTm H (s i) (s' i) (substExpr s (lookup G i)) (lookupEnv i rho) a

symCS : {h g : Num} {H : Ctx h} {G : Ctx g} {s s' : Sub h g} -> CSub H G s s' -> CSub H G s' s
symCS c = csub (CSub.w2 c) (CSub.w1 c) (\ i -> conv-conv (conv-sym (CSub.cv c i)) (CSub.te c i)) (\ i -> tyeq-sym (CSub.te c i))

-- validity on the diagonals of a two-sided type relation
diagL : {n : Num} {G : Ctx n} {T T' : Expr n} (a : FinEl) -> FinMem a UCode -> RTy G T T' a -> RTy G T T a
diagL a aU r = pTransT a aU r (pSymT a aU r)

diagR : {n : Num} {G : Ctx n} {T T' : Expr n} (a : FinEl) -> FinMem a UCode -> RTy G T T' a -> RTy G T' T' a
diagR a aU r = pTransT a aU (pSymT a aU r) r

-- symmetric term relation, transported to the other side's type
symTm : {n : Num} {G : Ctx n} {M M' T T' : Expr n} (u a : FinEl) -> FinMem u a -> FinMem a UCode ->
  RTy G T T' a -> RTm G M M' T u a -> RTm G M' M T' u a
symTm u a um aU v r = pConvM u a um aU v (pSymM u a um aU (diagL a aU v) r)

symSR : {h g : Num} {H : Ctx h} {G : Ctx g} {s s' : Sub h g} {rho : EnvApprox g} -> SR H G s s' rho -> SR H G s' s rho
symSR {H = H} {G} {s} {s'} {rho} sr = mkSR (symCS (SR.cs sr))
  (\ i a e aU -> pSymT a aU (SR.ty sr i a e aU))
  (\ i a e aU m -> symTm {G = H} {M = s i} {M' = s' i} {T = substExpr s (lookup G i)} {T' = substExpr s' (lookup G i)}
                     (lookupEnv i rho) a m aU (SR.ty sr i a e aU) (SR.tm sr i a e aU m))

-- left diagonal of a related pair of substitutions
leftSR : {h g : Num} {H : Ctx h} {G : Ctx g} {s s' : Sub h g} {rho : EnvApprox g} ->
  WfCtx H -> WfCtx G -> SR H G s s' rho -> SR H G s s rho
leftSR {H = H} {G} {s} {s'} {rho} wH wG sr = mkSR (reflC wG (CSub.w1 (SR.cs sr)) wH)
  (\ i a e aU -> diagL a aU (SR.ty sr i a e aU))
  (\ i a e aU m -> pTransM {G = H} {M1 = s i} {M2 = s' i} {M3 = s i} {T = substExpr s (lookup G i)}
                     (lookupEnv i rho) a m aU (diagL a aU (SR.ty sr i a e aU)) (SR.tm sr i a e aU m)
                     (pSymM {G = H} {M = s i} {M' = s' i} {T = substExpr s (lookup G i)}
                        (lookupEnv i rho) a m aU (diagL a aU (SR.ty sr i a e aU)) (SR.tm sr i a e aU m)))

------------------------------------------------------------------------
-- code adjustment inside an ideal of type codes
------------------------------------------------------------------------

adj : {n : Num} {G : Ctx n} {M M' T : Expr n} (PT : FinEl -> Set) -> Ideal PT ->
  ((c : FinEl) -> PT c -> FinMem c UCode -> RTy G T T c) ->
  (x c1 : FinEl) -> PT c1 -> FinMem c1 UCode -> FinMem x c1 -> RTm G M M' T x c1 ->
  (u c2 : FinEl) -> PT c2 -> FinMem c2 UCode -> LeCode u x -> FinMem u c2 -> RTm G M M' T u c2
adj PT iT VT x c1 e1 c1U xm r u c2 e2 c2U lux um =
  let cp = Ideal.comp iT c1 c2 e1 e2
      c3 = Sup c1 c2
      e3 = Ideal.sup iT c1 c2 e1 e2
      cc1 = coh-from-aU c1 c1U ; cc2 = coh-from-aU c2 c2U
      cc3 = Coherent-Sup c1 c2 cp cc1 cc2
      c3U = FinMem-Sup-element c1 c2 UCode cp tt c1U c2U
      le13 = LeCode-Sup-left c1 c2 cp cc1 cc2
      le23 = LeCode-Sup-right c1 c2 cp cc1 cc2
      v3 = VT c3 e3 c3U
      xm3 = finMem-upward x c1 c3 le13 cc1 cc3 xm c3U
      um3 = finMem-upward u c2 c3 le23 cc2 cc3 um c3U
      r3 = pUpM x c1 c3 le13 xm c1U c3U v3 r
      r4 = pRestrM x u c3 lux um3 xm3 c3U v3 r3
  in pDownM u c2 c3 le23 um c2U c3U v3 r4

------------------------------------------------------------------------
-- membership facts at Pi / Sigma codes
------------------------------------------------------------------------

module _ {g : FinFun} {b : FinEl} {f : FinFun} (gm : FinMem (FunEl g) (PiCode b f)) (pU : FinMem (PiCode b f) UCode) where

  private
    cu = piU b f pU
    cfg = cft-from-cf g (finMem-funel-coh g b f gm)

  selKey : {w v : FinEl} -> Selection g w v -> FinMem w b
  selKey sel = FinMem-Selection b f sel (finMem-funel-fun g b f gm) cfg (coh-from-aU b (CodeU.bU cu)) (CodeU.bU cu)

  selVal : {w v : FinEl} -> Selection g w v -> FinMem v (EvalFun f w)
  selVal sel = FinMem-Selection-codomain b f sel (finMem-funel-fun g b f gm) cfg (CodeU.cft cu) (CodeU.allU cu)

efU : {w : FinEl} (b : FinEl) (f : FinFun) -> CodeU b f -> FinMem w b -> FinMem (EvalFun f w) UCode
efU {w} b f cu wb = EvalFun-in-UCode f w b (CodeU.cft cu) (FinMem-coh-u w b wb) (CodeU.allU cu)

------------------------------------------------------------------------
-- extending related substitutions
------------------------------------------------------------------------

extSR : {h g : Num} {H : Ctx h} {G : Ctx g} {s s' : Sub h g} {rho : EnvApprox g} -> SR H G s s' rho ->
  {A : Expr g} -> TyEq H (substExpr s A) (substExpr s' A) ->
  ((a : FinEl) -> EvalRel A rho a -> FinMem a UCode -> RTy H (substExpr s A) (substExpr s' A) a) ->
  {N N' : Expr h} -> HasType H N (substExpr s A) -> HasType H N' (substExpr s' A) -> ConvTm H N N' (substExpr s A) ->
  (w : FinEl) ->
  ((a : FinEl) -> EvalRel A rho a -> FinMem a UCode -> FinMem w a -> RTm H N N' (substExpr s A) w a) ->
  SR H (extend G A) (consSub s N) (consSub s' N') (extendEnv rho w)
extSR {H = H} {G} {s} {s'} {rho} sr {A} qA VA {N} {N'} hN hN' cN w RN = mkSR (consC (SR.cs sr) hN hN' cN qA) ty tm
  where
    ty : (i : Fin _) (a : FinEl) -> EvalRel (lookup (extend G A) i) (extendEnv rho w) a -> FinMem a UCode ->
         RTy H (substExpr (consSub s N) (lookup (extend G A) i)) (substExpr (consSub s' N') (lookup (extend G A) i)) a
    ty fzero a e aU = transport2 (\ X Y -> RTy H X Y a) (Eq-sym (consSub-wk s N A)) (Eq-sym (consSub-wk s' N' A))
                        (VA a (EvalRel-unwk A rho w a e) aU)
    ty (fsuc i) a e aU = transport2 (\ X Y -> RTy H X Y a) (Eq-sym (consSub-wk s N (lookup G i))) (Eq-sym (consSub-wk s' N' (lookup G i)))
                        (SR.ty sr i a (EvalRel-unwk (lookup G i) rho w a e) aU)
    tm : (i : Fin _) (a : FinEl) -> EvalRel (lookup (extend G A) i) (extendEnv rho w) a -> FinMem a UCode ->
         FinMem (lookupEnv i (extendEnv rho w)) a ->
         RTm H (consSub s N i) (consSub s' N' i) (substExpr (consSub s N) (lookup (extend G A) i)) (lookupEnv i (extendEnv rho w)) a
    tm fzero a e aU m = transport (\ X -> RTm H N N' X w a) (Eq-sym (consSub-wk s N A)) (RN a (EvalRel-unwk A rho w a e) aU m)
    tm (fsuc i) a e aU m = transport (\ X -> RTm H (s i) (s' i) X (lookupEnv i rho) a) (Eq-sym (consSub-wk s N (lookup G i)))
                        (SR.tm sr i a (EvalRel-unwk (lookup G i) rho w a e) aU m)
