{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLO/ValU.agda
--
-- Validity of the universe rules (mahlo-plan.tex Sec. 6.4):
--   * Pi, Sigma, Nat in V and in U_{f,g}; subsumption and (R');
--   * U_{f,g} : V and its congruence: the interpretations of the types
--     OpF and OpG f unfold to Op(V*)  (decodeF / decodeG), and Lemma 15
--     (mahlo-code) applies;
--   * fhat, ghat and the delta-equations.
--
-- The KEY OBSERVATION: a valid code U_{f rho, g rho} = U_{f rho', g rho'}
-- in V* already carries Indep(f rho, g rho) and the operator equality on
-- pre(f rho, g rho, V*)  (invU, from the U-clause of Gamma).  So the
-- closure rules of U_{f,g} need no hypothesis on f, g; only the
-- congruence rules for fhat/ghat use decodeF/decodeG, to relate
-- f rho with f' rho'.
------------------------------------------------------------------------

open import MAHLO.Basic
open import MAHLO.TermModel
import MAHLO.Model
import MAHLO.Fixpoint

module MAHLO.ValU (TM : TermModel) (M : MAHLO.Model.Model TM)
                  (Fx : MAHLO.Fixpoint.Fixpoint TM) where

open TermModel TM
open MAHLO.Model TM using (Env ; cons)
open MAHLO.Model.Model M
open import MAHLO.Candidate TM
open import MAHLO.Pre TM
open import MAHLO.Gamma TM
open import MAHLO.EndExt TM
open import MAHLO.Congruence TM
open MAHLO.Fixpoint TM
open Fixpoint Fx
open Mahlo Fx using (mahlo-code)
open Cand V
open import MAHLO.Validity TM M Fx
open import MAHLO.Syntax
  renaming (Pi to tPi ; Sigma to tSigma ; Nat to tNat ; V to tV)
open import MAHLO.Typing

private
  module RV = IsPER R-per

------------------------------------------------------------------------
-- Inversion for codes: the key observation
------------------------------------------------------------------------

record UInv (f g f' g' : D) (X : Rel) : Set where
  constructor uinv
  field
    rU  : R (U f g) (U f' g')
    ind : Indep V f g
    op  : Op V (Pre V f g) f g f' g'
    eX  : X ~ Res V (Pre V f g)

private
  indopTr : {f0 g0 f0' g0' f g f' g' : D} ->
            f0 ~~ f -> g0 ~~ g -> f0' ~~ f' -> g0' ~~ g' ->
            Indep V f0 g0 * Op V (Pre V f0 g0) f0 g0 f0' g0' ->
            Indep V f g * Op V (Pre V f g) f g f' g'
  indopTr e1 e2 e3 e4 (ind , op) =
    Indep-cong V e1 e2 ind ,
    Op-cong V e1 e2 e3 e4 (Op-pred V (\ a p -> Pre-cong V (~~-sym e1) (~~-sym e2) p) op)

invU : {u u' f g f' g' : D} {X : Rel} -> TyR u u' X ->
       u ~~ U f g -> u' ~~ U f' g' -> UInv f g f' g' X
invU (tyV ea _ _) e e' = Empty-elim (V-U (~~-trans (~~-sym ea) e))
invU (tyPi _ _ _ _ _ _ ea _ _ _ _) e e' = Empty-elim (Pi-U (~~-trans (~~-sym ea) e))
invU (tySig _ _ _ _ _ _ ea _ _ _ _) e e' = Empty-elim (Sig-U (~~-trans (~~-sym ea) e))
invU {u} {u'} {f} {g} {f'} {g'} {X} (tySm r eX) e e' = h (_<<_.inc unfold r)
  where
    intU : I u ~ Res V (Pre V f g)
    intU = ~-trans (_<<_.int unfold u (RV.rl r)) (GI-U V u f g e)
    rU : R (U f g) (U f' g')
    rU = CandCl.R-cl2 V e e' r
    ne-u : {a f0 g0 : D} -> N a a -> a ~~ U f0 g0 -> Empty
    ne-u n e0 = ne-U (N-self e0 n)
    h : GR V u u' -> UInv f g f' g' X
    h (gne n) = Empty-elim (ne-u (IsPER.rl N-per n) e)
    h (gnat e1 _) = Empty-elim (Nat-U (~~-trans (~~-sym e1) e))
    h (gpi p) = Empty-elim (Pi-U (~~-trans (~~-sym (PiRel.ea p)) e))
    h (gsig p) = Empty-elim (Sig-U (~~-trans (~~-sym (SigRel.ea p)) e))
    h (gU (mkU f0 g0 f0' g0' ea eb ind ind' op)) =
      let i1 = U-inj (~~-trans (~~-sym ea) e)
          i2 = U-inj (~~-trans (~~-sym eb) e')
          io = indopTr (fst i1) (snd i1) (fst i2) (snd i2) (ind , op)
      in uinv rU (fst io) (snd io) (~-trans eX intU)

------------------------------------------------------------------------
-- Small helpers
------------------------------------------------------------------------

-- elements of V
Rof : {m : Num} {r r' : Env m} {a a' : D} -> TmV (den tV r) (den tV r') a a' -> R a a'
Rof p = elAt (tmvTr den-V den-V ~~-refl ~~-refl p) tyVV

inV : {m : Num} {r r' : Env m} {a a' : D} -> R a a' -> TmV (den tV r) (den tV r') a a'
inV x = tmvTr (~~-sym den-V) (~~-sym den-V) ~~-refl ~~-refl (tmv _ tyVV x)

-- elements of a code
uI : {m : Num} (f g : Expr m) {r r' : Env m} {X : Rel} ->
     TyR (den (Ucode f g) r) (den (Ucode f g) r') X ->
     UInv (den f r) (den g r) (den f r') (den g r') X
uI f g d = invU d (den-Ucode f g) (den-Ucode f g)

uEl : {m : Num} (f g : Expr m) {r r' : Env m} {a a' : D} ->
      TmV (den (Ucode f g) r) (den (Ucode f g) r') a a' ->
      R a a' * (Pre V (den f r) (den g r) a * Pre V (den f r) (den g r) a')
uEl f g p = fst (UInv.eX (uI f g (TmV.ty p))) (TmV.el p)

-- the weakened code at an extended environment
wkU : {m : Num} (f g : Expr m) {r r' : Env m} {v v' a a' : D} ->
      TmV (den (wkExpr (Ucode f g)) (cons r v)) (den (wkExpr (Ucode f g)) (cons r' v')) a a' ->
      TmV (den (Ucode f g) r) (den (Ucode f g) r') a a'
wkU f g {r} {r'} {v} {v'} =
  tmvTr (den-wk-cons r v (Ucode f g)) (den-wk-cons r' v' (Ucode f g)) ~~-refl ~~-refl

vLamE : {m : Num} (r : Env m) (X : Expr m) (w : D) -> app (den (Lam X tV) r) w ~~ Vd
vLamE r X w = ~~-trans (den-Lam X tV w) den-V

module _ {n : Num} {G : Ctx n} where

  ----------------------------------------------------------------------
  -- subsumption and (R')
  ----------------------------------------------------------------------

  v-conv-sub : {A B f g : Expr n} -> ValConv G A B (Ucode f g) -> ValConv G A B tV
  v-conv-sub {f = f} {g} h e = inV (fst (uEl f g (h e)))

  v-conv-R' : {A B f g : Expr n} -> ValTm G A (Ucode f g) -> ValTm G B (Ucode f g) ->
              ValConv G A B tV -> ValConv G A B (Ucode f g)
  v-conv-R' {f = f} {g} hA hB hAB e =
    tmv _ (TmV.ty (hA e))
      (snd (UInv.eX (uI f g (TmV.ty (hA e))))
        (Rof (hAB e) , (fst (snd (uEl f g (hA e))) , snd (snd (uEl f g (hB e))))))

  v-ty-Nat-U : {f g : Expr n} -> ValTm G (Ucode f g) tV -> ValTm G tNat (Ucode f g)
  v-ty-Nat-U {f} {g} h e =
    tmv _ d (snd (UInv.eX (uI f g d))
      (CandCl.R-cl2 V (~~-sym den-Nat) (~~-sym den-Nat) seed-nat ,
       (pre-nat _ den-Nat , pre-nat _ den-Nat)))
    where d = tySm (Rof (h e)) ~-refl

  ----------------------------------------------------------------------
  -- Pi and Sigma in V
  ----------------------------------------------------------------------

  private
    lamR : {m : Num} {r r' : Env m} {A A' : Expr m} {B B' : Expr (suc m)} {v v' : D} ->
           R (den B (cons r v)) (den B' (cons r' v')) ->
           R (app (den (Lam A B) r) v) (app (den (Lam A' B') r') v')
    lamR {A = A} {A'} {B} {B'} {v} {v'} =
      CandCl.R-cl2 V (~~-sym (den-Lam A B v)) (~~-sym (den-Lam A' B' v'))

    lamP : {m : Num} {r : Env m} {A : Expr m} {B : Expr (suc m)} {v : D} {f g : D} ->
           Pre V f g (den B (cons r v)) -> Pre V f g (app (den (Lam A B) r) v)
    lamP {A = A} {B} {v} = Pre-cl V (~~-sym (den-Lam A B v))

  module _ {A A' : Expr n} {B B' : Expr (suc n)}
           (hAA : ValConv G A A' tV) (hBB : ValConv (extend G A) B B' tV)
           {rho rho' : Env n} (e : EnvR G rho rho') where
    private
      rA = Rof (hAA e)
      rAA = Rof (vconv-l {G = G} hAA e)
      fe : FamEq V (den A rho) (den (Lam A B) rho) (den (Lam A' B') rho')
      fe v v' i = lamR {A = A} {A'} (Rof (hBB (envCons e (tmSm rAA i))))

    piV : TmV (den tV rho) (den tV rho') (den (PiB A B) rho) (den (PiB A' B') rho')
    piV = tmvTr ~~-refl ~~-refl (~~-sym (den-Pi A (Lam A B))) (~~-sym (den-Pi A' (Lam A' B')))
            (inV (piIn rA fe))

    sigV : TmV (den tV rho) (den tV rho') (den (SigmaB A B) rho) (den (SigmaB A' B') rho')
    sigV = tmvTr ~~-refl ~~-refl (~~-sym (den-Sigma A (Lam A B))) (~~-sym (den-Sigma A' (Lam A' B')))
             (inV (sigIn rA fe))

  v-conv-Pi-V : {A A' : Expr n} {B B' : Expr (suc n)} ->
                ValConv G A A' tV -> ValConv (extend G A) B B' tV ->
                ValConv G (PiB A B) (PiB A' B') tV
  v-conv-Pi-V hAA hBB e = piV hAA hBB e

  v-conv-Sigma-V : {A A' : Expr n} {B B' : Expr (suc n)} ->
                   ValConv G A A' tV -> ValConv (extend G A) B B' tV ->
                   ValConv G (SigmaB A B) (SigmaB A' B') tV
  v-conv-Sigma-V hAA hBB e = sigV hAA hBB e

  ----------------------------------------------------------------------
  -- families in a code
  ----------------------------------------------------------------------

  module Fam {f g A A' : Expr n} {B B' : Expr (suc n)}
             (hAA : ValConv G A A' (Ucode f g))
             (hBB : ValConv (extend G A) B B' (wkExpr (Ucode f g)))
             {rho rho' : Env n} (e : EnvR G rho rho') where

    fr = den f rho
    gr = den g rho
    Ar = den A rho
    Ar' = den A' rho'
    Fr = den (Lam A B) rho
    Fr' = den (Lam A' B') rho'

    pA = hAA e
    u = uI f g (TmV.ty pA)
    open UInv u public

    rA : R Ar Ar'
    rA = fst (uEl f g pA)
    preA : Pre V fr gr Ar
    preA = fst (snd (uEl f g pA))
    preA' : Pre V fr gr Ar'
    preA' = snd (snd (uEl f g pA))

    private
      rAA = fst (uEl f g (vconv-l {G = G} hAA e))
      e0 = EnvR-rl G e
      hB = vconv-l {G = extend G A} hBB
      atL : {v v' : D} -> I Ar v v' -> R (app Fr v) (app Fr v') *
              (Pre V fr gr (app Fr v) * Pre V fr gr (app Fr v'))
      atL {v} {v'} i =
        let q = uEl f g (wkU f g (hB (envCons e0 (tmSm (RV.rl rA) i)))) in
        lamR {A = A} {A} (fst q) ,
        (lamP {A = A} {B}  (fst (snd q)) ,
         lamP {A = A} {B}  (snd (snd q)))
      atLR : {v v' : D} -> I Ar v v' -> R (app Fr v) (app Fr' v') *
               (Pre V fr gr (app Fr v) * Pre V fr gr (app Fr' v'))
      atLR {v} {v'} i =
        let q = uEl f g (wkU f g (hBB (envCons e (tmSm rAA i)))) in
        lamR {A = A} {A'} (fst q) ,
        (lamP {A = A} {B}  (fst (snd q)) ,
         lamP {A = A'} {B'}  (snd (snd q)))

    fe : FamEq V Ar Fr Fr'
    fe v v' i = fst (atLR i)

    rF : FamResp V Ar Fr
    rF v v' i = fst (atL i)

    hF : FamIn V (Pre V fr gr) Ar Fr
    hF v i = fst (snd (atL i))

    hF' : FamIn V (Pre V fr gr) Ar' Fr'
    hF' v i = snd (snd (atLR (snd (I-resp rA) i)))

    ix = ind Ar Fr preA rF hF

  ----------------------------------------------------------------------
  -- Pi and Sigma in a code (Pre needs no Indep for these)
  ----------------------------------------------------------------------

  v-conv-Pi-U : {f g A A' : Expr n} {B B' : Expr (suc n)} ->
                ValConv G A A' (Ucode f g) ->
                ValConv (extend G A) B B' (wkExpr (Ucode f g)) ->
                ValConv G (PiB A B) (PiB A' B') (Ucode f g)
  v-conv-Pi-U {f} {g} {A} {A'} {B} {B'} hAA hBB e =
    tmvTr ~~-refl ~~-refl (~~-sym (den-Pi A (Lam A B))) (~~-sym (den-Pi A' (Lam A' B')))
      (tmv _ (TmV.ty pA) (snd eX (rPi , (preL , pre-sat _ _ preL rPi))))
    where
      open Fam hAA hBB e
      rPi = piIn rA fe
      preL = pre-pi _ Ar Fr ~~-refl preA rF hF (piIn (RV.rl rA) rF)

  v-conv-Sigma-U : {f g A A' : Expr n} {B B' : Expr (suc n)} ->
                   ValConv G A A' (Ucode f g) ->
                   ValConv (extend G A) B B' (wkExpr (Ucode f g)) ->
                   ValConv G (SigmaB A B) (SigmaB A' B') (Ucode f g)
  v-conv-Sigma-U {f} {g} {A} {A'} {B} {B'} hAA hBB e =
    tmvTr ~~-refl ~~-refl (~~-sym (den-Sigma A (Lam A B))) (~~-sym (den-Sigma A' (Lam A' B')))
      (tmv _ (TmV.ty pA) (snd eX (rSig , (preL , pre-sat _ _ preL rSig))))
    where
      open Fam hAA hBB e
      rSig = sigIn rA fe
      preL = pre-sig _ Ar Fr ~~-refl preA rF hF (sigIn (RV.rl rA) rF)

------------------------------------------------------------------------
-- Decoding the operator types:  [OpF] and [OpG f] unfold to Op(V*)
------------------------------------------------------------------------

module _ {n : Num} where

  private
    -- Pi A:V. B  at r
    topE : (r : Env n) (Bd : Expr (suc n)) ->
           den (PiB tV Bd) r ~~ Pi Vd (den (Lam tV Bd) r)
    topE r Bd = ~~-trans (den-Pi tV (Lam tV Bd)) ((\ e -> Pi-cong e ~~-refl) den-V)

    -- (x0 -> V)  at (r, A)  is  Pi A (\_. V)
    domE : (r : Env (suc n)) ->
           den (Arr x0 tV) r ~~ Pi (r fzero) (den (Lam x0 tV) r)
    domE r = ~~-trans (den-Pi x0 (Lam x0 tV))
               ((\ e -> Pi-cong e ~~-refl) (den-Var fzero))

    -- the type of families  A -> V,  for A small
    domTy : (r r' : Env (suc n)) -> R (r fzero) (r' fzero) ->
            TyV (den (Arr x0 tV) r) (den (Arr x0 tV) r')
    domTy r r' rA =
      piTy (domE r) (domE r') (tySm rA ~-refl)
        (\ v v' i -> tyvTr (~~-sym (vLamE r x0 v)) (~~-sym (vLamE r' x0 v')) (tyv _ tyVV))

    domEl : (r r' : Env (suc n)) (rA : R (r fzero) (r' fzero)) {F F' : D} ->
            FamEq V (r fzero) F F' -> TyV.X (domTy r r' rA) F F'
    domEl r r' rA fe =
      piIntro (TyV.ty (domTy r r' rA)) (domE r) (domE r')
        (\ v v' dY y ->
           tmvTr (~~-sym (vLamE r x0 v)) (~~-sym (vLamE r' x0 v')) ~~-refl ~~-refl
             (tmv _ tyVV (fe v v' (elAt (tmv _ dY y) (tySm rA ~-refl)))))

    bodyF : Expr (suc n)
    bodyF = Arr (Arr x0 tV) tV

    fE : (r : Env n) (A : D) ->
         app (den (Lam tV bodyF) r) A ~~
            Pi (den (Arr x0 tV) (cons r A)) (den (Lam (Arr x0 tV) tV) (cons r A))
    fE r A = ~~-trans (den-Lam tV bodyF A) (den-Pi (Arr x0 tV) (Lam (Arr x0 tV) tV))

  decodeF : {rho rho' : Env n} {a1 a2 : D} ->
            TmV (den OpF rho) (den OpF rho') a1 a2 ->
            (A A' F F' : D) -> R A A' -> FamEq V A F F' -> R (FA a1 A F) (FA a2 A' F')
  decodeF {rho} {rho'} tf A A' F F' rA fe =
    elAt (tmvTr (vLamE (cons rho A) (Arr x0 tV) F) (vLamE (cons rho' A') (Arr x0 tV) F')
                ~~-refl ~~-refl t2) tyVV
    where
      t1 = piElim (TmV.ty tf) (topE rho bodyF) (topE rho' bodyF) (TmV.el tf) tyVV rA
      dt = domTy (cons rho A) (cons rho' A') rA
      t2 = piElim (TmV.ty t1) (fE rho A) (fE rho' A') (TmV.el t1)
                  (TyV.ty dt) (domEl (cons rho A) (cons rho' A') rA fe)

  module _ (f : Expr n) where
    private
      ff : Expr (suc (suc n))
      ff = wkExpr (wkExpr f)
      fa : Expr (suc (suc n))
      fa = App (App ff x1) x0
      bodyG2 : Expr (suc (suc n))
      bodyG2 = Arr fa tV
      bodyG1 : Expr (suc n)
      bodyG1 = PiB (Arr x0 tV) bodyG2

      g2E : (r : Env n) (A : D) ->
            app (den (Lam tV bodyG1) r) A ~~
               Pi (den (Arr x0 tV) (cons r A)) (den (Lam (Arr x0 tV) bodyG2) (cons r A))
      g2E r A = ~~-trans (den-Lam tV bodyG1 A) (den-Pi (Arr x0 tV) (Lam (Arr x0 tV) bodyG2))

      faE : (r : Env n) (A F : D) -> den fa (cons (cons r A) F) ~~ FA (den f r) A F
      faE r A F =
        ~~-trans (den-App (App ff x1) x0)
          (app-cong
            (~~-trans (den-App ff x1)
              (app-cong (~~-trans (den-wk-cons (cons r A) F (wkExpr f)) (den-wk-cons r A f))
                         (den-Var (fsuc fzero))))
            (den-Var fzero))

      g3E : (r : Env n) (A F : D) ->
            app (den (Lam (Arr x0 tV) bodyG2) (cons r A)) F ~~
               Pi (FA (den f r) A F) (den (Lam fa tV) (cons (cons r A) F))
      g3E r A F =
        ~~-trans (den-Lam (Arr x0 tV) bodyG2 F)
          (~~-trans (den-Pi fa (Lam fa tV))
             (Pi-cong (faE r A F) ~~-refl))

    decodeG : {rho rho' : Env n} {b1 b2 : D} ->
              TmV (den OpF rho) (den OpF rho') (den f rho) (den f rho') ->
              TmV (den (OpG f) rho) (den (OpG f) rho') b1 b2 ->
              (A A' F F' c c' : D) -> R A A' -> FamEq V A F F' ->
              I (FA (den f rho) A F) c c' -> R (GA b1 A F c) (GA b2 A' F' c')
    decodeG {rho} {rho'} tf tg A A' F F' c c' rA fe ic =
      elAt (tmvTr (vLamE (cons (cons rho A) F) fa c) (vLamE (cons (cons rho' A') F') fa c')
                  ~~-refl ~~-refl t3) tyVV
      where
        t1 = piElim (TmV.ty tg) (topE rho bodyG1) (topE rho' bodyG1) (TmV.el tg) tyVV rA
        dt = domTy (cons rho A) (cons rho' A') rA
        t2 = piElim (TmV.ty t1) (g2E rho A) (g2E rho' A') (TmV.el t1)
                    (TyV.ty dt) (domEl (cons rho A) (cons rho' A') rA fe)
        rFA = decodeF tf A A' F F' rA fe
        t3 = piElim (TmV.ty t2) (g3E rho A F) (g3E rho' A' F') (TmV.el t2)
                    (tySm rFA ~-refl) ic

  -- the interpretation of the operator types is Op(V*)
  opSem : (f : Expr n) {rho rho' : Env n} {a2 b1 b2 : D} ->
          TmV (den OpF rho) (den OpF rho') (den f rho) a2 ->
          TmV (den OpF rho) (den OpF rho') (den f rho) (den f rho') ->
          TmV (den (OpG f) rho) (den (OpG f) rho') b1 b2 ->
          Op V (\ a -> R a a) (den f rho) b1 a2 b2
  opSem f tf tf0 tg A A' F F' r _ _ fe _ _ =
    decodeF tf A A' F F' r fe , (\ c c' i -> decodeG f tf0 tg A A' F F' c c' r fe i)

------------------------------------------------------------------------
-- U_{f,g} : V, fhat, ghat, delta
------------------------------------------------------------------------

module _ {n : Num} {G : Ctx n} where

  v-conv-Ucode : {f f' g g' : Expr n} -> ValTm G f OpF ->
                 ValConv G f f' OpF -> ValConv G g g' (OpG f) ->
                 ValConv G (Ucode f g) (Ucode f' g') tV
  v-conv-Ucode {f} {f'} {g} {g'} hf hfc hgc e =
    tmvTr ~~-refl ~~-refl (~~-sym (den-Ucode f g)) (~~-sym (den-Ucode f' g'))
      (inV (mahlo-code (opSem f (hfc e) (hf e) (hgc e))))

  v-ty-Ucode : {f g : Expr n} -> ValTm G f OpF -> ValTm G g (OpG f) ->
               ValTm G (Ucode f g) tV
  v-ty-Ucode hf hg = v-conv-Ucode hf hf hg

  v-conv-Fhat : {f f' g g' A A' : Expr n} {B B' : Expr (suc n)} ->
                ValConv G f f' OpF ->
                ValConv G A A' (Ucode f g) ->
                ValConv (extend G A) B B' (wkExpr (Ucode f g)) ->
                ValConv G (Fhat f g A (Lam A B)) (Fhat f' g' A' (Lam A' B')) (Ucode f g)
  v-conv-Fhat {f} {f'} {g} {g'} {A} {A'} {B} {B'} hfc hAA hBB e =
    tmvTr ~~-refl ~~-refl (~~-sym (den-Fhat f g A (Lam A B))) (~~-sym (den-Fhat f' g' A' (Lam A' B')))
      (tmv _ (TmV.ty pA) (snd eX (rFF , (preF , pre-sat _ _ preF rFF))))
    where
      open Fam hAA hBB e
      rFF = decodeF (hfc e) Ar Ar' Fr Fr' rA fe
      preF = pre-f _ Ar Fr ~~-refl preA rF hF (fst (snd ix))

  v-conv-Ghat : {f f' g g' A A' c c' : Expr n} {B B' : Expr (suc n)} ->
                ValConv G f f' OpF -> ValConv G g g' (OpG f) ->
                ValConv G A A' (Ucode f g) ->
                ValConv (extend G A) B B' (wkExpr (Ucode f g)) ->
                ValConv G c c' (Fhat f g A (Lam A B)) ->
                ValConv G (Ghat f g A (Lam A B) c) (Ghat f' g' A' (Lam A' B') c') (Ucode f g)
  v-conv-Ghat {f} {f'} {g} {g'} {A} {A'} {c} {c'} {B} {B'} hfc hgc hAA hBB hcc {rho} {rho'} e =
    tmvTr ~~-refl ~~-refl (~~-sym (den-Ghat f g A (Lam A B) c))
          (~~-sym (den-Ghat f' g' A' (Lam A' B') c'))
      (tmv _ (TmV.ty pA) (snd eX (rG , (preG , pre-sat _ _ preG rG))))
    where
      open Fam hAA hBB e
      Rff = fst (snd ix)
      ic : I (FA fr Ar Fr) (den c rho) (den c' rho')
      ic = elAt (tmvTr (den-Fhat f g A (Lam A B)) (den-Fhat f g A (Lam A B)) ~~-refl ~~-refl (hcc e))
                (tySm Rff ~-refl)
      icc = IsPER.rl (I-per _ Rff) ic
      rG = decodeG f (vconv-l {G = G} hfc e) (hgc e) Ar Ar' Fr Fr' _ _ rA fe ic
      preG = pre-g _ Ar Fr (den c rho) ~~-refl preA rF hF Rff icc (snd (snd ix) _ icc)

  v-conv-delta-f : {f g A : Expr n} {B : Expr (suc n)} ->
                   ValTm G f OpF -> ValTm G A (Ucode f g) ->
                   ValTm (extend G A) B (wkExpr (Ucode f g)) ->
                   ValConv G (Fhat f g A (Lam A B)) (App (App f A) (Lam A B)) tV
  v-conv-delta-f {f} {g} {A} {B} hf hA hB {rho} {rho'} e =
    tmvTr ~~-refl ~~-refl ~~-refl E (inV (fst (uEl f g (v-conv-Fhat hf hA hB e))))
    where
      E : den (Fhat f g A (Lam A B)) rho' ~~ den (App (App f A) (Lam A B)) rho'
      E = ~~-trans (den-Fhat f g A (Lam A B))
            (~~-sym (~~-trans (den-App (App f A) (Lam A B))
                      ((\ e -> app-cong e ~~-refl) (den-App f A))))

  v-conv-delta-g : {f g A c : Expr n} {B : Expr (suc n)} ->
                   ValTm G f OpF -> ValTm G g (OpG f) -> ValTm G A (Ucode f g) ->
                   ValTm (extend G A) B (wkExpr (Ucode f g)) ->
                   ValTm G c (Fhat f g A (Lam A B)) ->
                   ValConv G (Ghat f g A (Lam A B) c) (App (App (App g A) (Lam A B)) c) tV
  v-conv-delta-g {f} {g} {A} {c} {B} hf hg hA hB hc {rho} {rho'} e =
    tmvTr ~~-refl ~~-refl ~~-refl E (inV (fst (uEl f g (v-conv-Ghat hf hg hA hB hc e))))
    where
      E : den (Ghat f g A (Lam A B) c) rho' ~~ den (App (App (App g A) (Lam A B)) c) rho'
      E = ~~-trans (den-Ghat f g A (Lam A B) c)
            (~~-sym (~~-trans (den-App (App (App g A) (Lam A B)) c)
                      ((\ e -> app-cong e ~~-refl)
                        (~~-trans (den-App (App g A) (Lam A B))
                                  ((\ e -> app-cong e ~~-refl) (den-App g A))))))
