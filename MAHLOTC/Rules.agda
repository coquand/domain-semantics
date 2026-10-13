{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOTC/Rules.agda
--
-- One inference result / one checking decision per term former, given
-- the decisions for its immediate subterms.  Soundness is by the typing
-- rule; completeness by inversion (MAHLOINJ) and TCHyp.
------------------------------------------------------------------------

open import MAHLOTC.Base

module MAHLOTC.Rules (H : TCHyp) where

open import MAHLO.Syntax
open import MAHLO.Typing
open TCHyp H
open InjHyp inj
open import MAHLOINJ.Inversion.Inv inj
open import MAHLOINJ.Syntax.Lemmas using (elTy ; trTy ; trHT)
open import MAHLOINJ.Syntax.Weaken using (wkTy ; wkTE ; renUniv)
open import MAHLOINJ.Syntax.Subst using (s1Ty ; ws1 ; sbTy)
open import MAHLOINJ.Syntax.Wf using (wfTm ; wfTy ; NatTy)
open import MAHLOINJ.Syntax.CtxConv using (ccTy ; ccTm)
open import MAHLOINJ.Syntax.Presup using (pTm ; pTE ; opFTy ; opGTy)
open import MAHLOINJ.Syntax.Funct using (s1fTy)
open import MAHLOTC.Lemmas inj
open import MAHLOTC.Res H

-- a decision procedure for "t : C" over all types C
Chkr : {n : Num} -> Ctx n -> Expr n -> Set
Chkr {n} G a = (C : Expr n) -> IsType G C -> Dec (HasType G a C)

private
  s1TE' : {n : Num} {G : Ctx n} {A a : Expr n} {B B' : Expr (suc n)} -> WfCtx G ->
          HasType G a A -> TyEq (extend G A) B B' -> TyEq G (subst1 B a) (subst1 B' a)
  s1TE' w ha q = MAHLOINJ.Syntax.Subst.s1TE w ha q

module _ {n : Num} {G : Ctx n} (w : WfCtx G) where

  ----------------------------------------------------------------------
  -- variables
  ----------------------------------------------------------------------

  varRes : (i : Fin n) -> Res G (Var i)
  varRes i = weakRes (\ C h -> invVar h) (sat (lookup G i) (ty-var w))

  vRes : Res G V
  vRes = nilRes (\ C h -> noV h)

  ----------------------------------------------------------------------
  -- application
  ----------------------------------------------------------------------

  private
    RApp : (a X C : Expr n) -> Set
    RApp a X C = Sg (Expr n) (\ A0 -> Sg (Expr (suc n)) (\ B0 ->
                   TyEq G (PiB A0 B0) X * (HasType G a A0 * UpTo G C (subst1 B0 a))))

    appOne : {t a X : Expr n} -> HasType G t X -> Chkr G a -> LRes G (App t a) (RApp a X)
    appOne {t} {a} {X} hX chkA = go (decPi (pTm hX))
      where
        go : Dec (Sg (Expr n) (\ A -> Sg (Expr (suc n)) (\ B -> TyEq G X (PiB A B)))) ->
             LRes G (App t a) (RApp a X)
        go (no k) = nilRes (\ { C (A0 , (B0 , (q , _))) -> k (A0 , (B0 , tyeq-sym q)) })
        go (yes (A , (B , e))) = go2 (chkA A hA)
          where
            hAB = piTyInv (snd (pTE e))
            hA = fst hAB
            hB = snd hAB
            go2 : Dec (HasType G a A) -> LRes G (App t a) (RApp a X)
            go2 (no k) = nilRes (\ { C (A0 , (B0 , (q , (ha , up)))) ->
                           k (ty-conv ha (fst (Pi-inj (tyeq-trans q e)))) })
            go2 (yes ha) =
              weakRes (\ { C (A0 , (B0 , (q , (ha0 , up)))) ->
                           upConvR up (s1TE' w ha0 (snd (Pi-inj (tyeq-trans q e)))) })
                (sat (subst1 B a) (ty-App hA hB (ty-conv hX e) ha))

  appRes : {t a : Expr n} -> Res G t -> Chkr G a -> Res G (App t a)
  appRes {t} {a} rt chkA =
    weakRes (\ C h -> let r = invApp h in
                      any-map (\ X q -> AppInv.A r , (AppInv.B r , (q , (AppInv.ha r , AppInv.up r))))
                              (cmp rt _ (AppInv.ht r)))
      (bindRes (L rt) (sound rt) (\ X hX -> appOne hX chkA))

  ----------------------------------------------------------------------
  -- projections
  ----------------------------------------------------------------------

  private
    RFst : (X C : Expr n) -> Set
    RFst X C = Sg (Expr n) (\ A0 -> Sg (Expr (suc n)) (\ B0 ->
                 TyEq G (SigmaB A0 B0) X * UpTo G C A0))

    fstOne : {t X : Expr n} -> HasType G t X -> LRes G (Fst t) (RFst X)
    fstOne {t} {X} hX = go (decSig (pTm hX))
      where
        go : Dec (Sg (Expr n) (\ A -> Sg (Expr (suc n)) (\ B -> TyEq G X (SigmaB A B)))) ->
             LRes G (Fst t) (RFst X)
        go (no k) = nilRes (\ { C (A0 , (B0 , (q , _))) -> k (A0 , (B0 , tyeq-sym q)) })
        go (yes (A , (B , e))) =
          weakRes (\ { C (A0 , (B0 , (q , up))) -> upConvR up (fst (Sig-inj (tyeq-trans q e))) })
            (sat A (ty-Fst hA hB (ty-conv hX e)))
          where
            hAB = sigTyInv (snd (pTE e))
            hA = fst hAB
            hB = snd hAB

    RSnd : (t X C : Expr n) -> Set
    RSnd t X C = Sg (Expr n) (\ A0 -> Sg (Expr (suc n)) (\ B0 ->
                   TyEq G (SigmaB A0 B0) X *
                   ((IsType G A0 * (IsType (extend G A0) B0 * HasType G t (SigmaB A0 B0))) *
                    UpTo G C (subst1 B0 (Fst t)))))

    sndOne : {t X : Expr n} -> HasType G t X -> LRes G (Snd t) (RSnd t X)
    sndOne {t} {X} hX = go (decSig (pTm hX))
      where
        go : Dec (Sg (Expr n) (\ A -> Sg (Expr (suc n)) (\ B -> TyEq G X (SigmaB A B)))) ->
             LRes G (Snd t) (RSnd t X)
        go (no k) = nilRes (\ { C (A0 , (B0 , (q , _))) -> k (A0 , (B0 , tyeq-sym q)) })
        go (yes (A , (B , e))) =
          weakRes (\ { C (A0 , (B0 , (q , ((hA0 , (hB0 , ht0)) , up)))) ->
                       upConvR up (s1TE' w (ty-Fst hA0 hB0 ht0) (snd (Sig-inj (tyeq-trans q e)))) })
            (sat (subst1 B (Fst t)) (ty-Snd hA hB (ty-conv hX e)))
          where
            hAB = sigTyInv (snd (pTE e))
            hA = fst hAB
            hB = snd hAB

  fstRes : {t : Expr n} -> Res G t -> Res G (Fst t)
  fstRes rt =
    weakRes (\ C h -> let r = invFst h in
                      any-map (\ X q -> FstInv.A r , (FstInv.B r , (q , FstInv.up r)))
                              (cmp rt _ (FstInv.ht r)))
      (bindRes (L rt) (sound rt) (\ X hX -> fstOne hX))

  sndRes : {t : Expr n} -> Res G t -> Res G (Snd t)
  sndRes rt =
    weakRes (\ C h -> let r = invSnd h in
                      any-map (\ X q -> SndInv.A r , (SndInv.B r ,
                                 (q , ((SndInv.hA r , (SndInv.hB r , SndInv.ht r)) , SndInv.up r))))
                              (cmp rt _ (SndInv.ht r)))
      (bindRes (L rt) (sound rt) (\ X hX -> sndOne hX))

  ----------------------------------------------------------------------
  -- lambda (inferable body)
  ----------------------------------------------------------------------

  lamRes : {A : Expr n} {b : Expr (suc n)} -> Dec (IsType G A) ->
           ((hA : IsType G A) -> Res (extend G A) b) -> Res G (Lam A b)
  lamRes (no k) rb = nilRes (\ C h -> k (LamInv.hA (invLam h)))
  lamRes {A} {b} (yes hA) rb = lres (mapPi (L r)) (mapS (L r) (sound r)) c
    where
      r = rb hA
      mapPi : List (Expr (suc n)) -> List (Expr n)
      mapPi [] = []
      mapPi (X :: Xs) = PiB A X :: mapPi Xs
      mapS : (Xs : List (Expr (suc n))) -> All (HasType (extend G A) b) Xs ->
             All (HasType G (Lam A b)) (mapPi Xs)
      mapS [] u = unit
      mapS (X :: Xs) (h , hs) = ty-Lam hA (pTm h) h , mapS Xs hs
      mapA : {C : Expr n} {B0 : Expr (suc n)} -> TyEq G C (PiB A B0) -> IsType (extend G A) B0 ->
             (Xs : List (Expr (suc n))) -> All (HasType (extend G A) b) Xs ->
             Any (TyEq (extend G A) B0) Xs -> Any (TyEq G C) (mapPi Xs)
      mapA eq hB0 (X :: Xs) (h , hs) (here q) =
        here (tyeq-trans eq (tyeq-Pi hA hB0 (pTm h) (tyeq-refl hA) q))
      mapA eq hB0 (X :: Xs) (h , hs) (there a) = there (mapA eq hB0 Xs hs a)
      c : (C : Expr n) -> HasType G (Lam A b) C -> Any (TyEq G C) (mapPi (L r))
      c C h = mapA (LamInv.eq i) (LamInv.hB i) (L r) (sound r) (cmp r _ (LamInv.ht i))
        where i = invLam h

  ----------------------------------------------------------------------
  -- Pi and Sigma with an inferable domain
  ----------------------------------------------------------------------

  private
    RPi : (A : Expr n) (B : Expr (suc n)) (X C : Expr n) -> Set
    RPi A B X C = Sg (Expr n) (\ u -> Univ u * (TyEq G u X *
                    (HasType (extend G A) B (wkExpr u) * TyEq G C u)))

    -- the universes a Pi/Sigma lands in, for one type X of the domain
    univOne : {T A : Expr n} {B : Expr (suc n)} ->
              ((hA : IsType G A) -> Chkr (extend G A) B) ->
              ({u : Expr n} -> Univ u -> HasType G A u -> HasType (extend G A) B (wkExpr u) ->
                HasType G T u) ->
              {X : Expr n} -> HasType G A X -> LRes G T (RPi A B X)
    univOne {T} {A} {B} chkB mk {X} hX =
      weakRes (\ { C (u , (univ-V refl , (q , (hB , eq)))) -> inl (q , (hB , eq))
                 ; C (u , (univ-U f g refl , (q , (hB , eq)))) -> inr (f , (g , (q , (hB , eq)))) })
        (orRes (vPart (decTyEq (pTm hX) (isty-V w))) (uPart (decU (pTm hX))))
      where
        vPart : Dec (TyEq G X V) ->
                LRes G T (\ C -> TyEq G V X * (HasType (extend G A) B V * TyEq G C V))
        vPart (no k) = nilRes (\ { C (q , _) -> k (tyeq-sym q) })
        vPart (yes eV) = vB (chkB hAty V (isty-V (wf-extend hAty)))
          where
            hAV = ty-conv hX eV
            hAty = isty-el hAV
            vB : Dec (HasType (extend G A) B V) ->
                 LRes G T (\ C -> TyEq G V X * (HasType (extend G A) B V * TyEq G C V))
            vB (no k) = nilRes (\ { C (q , (hB , eq)) -> k hB })
            vB (yes hB) = lres (V :: []) (mk (univ-V refl) hAV hB , unit)
                               (\ { C (q , (hB' , eq)) -> here eq })
        uPart : Dec (Sg (Expr n) (\ f -> Sg (Expr n) (\ g -> TyEq G X (Ucode f g)))) ->
                LRes G T (\ C -> Sg (Expr n) (\ f -> Sg (Expr n) (\ g ->
                  TyEq G (Ucode f g) X * (HasType (extend G A) B (wkExpr (Ucode f g)) *
                                          TyEq G C (Ucode f g)))))
        uPart (no k) = nilRes (\ { C (f , (g , (q , _))) -> k (f , (g , tyeq-sym q)) })
        uPart (yes (f , (g , eU))) = uB (chkB hAty (wkExpr (Ucode f g)) hWU)
          where
            hAU = ty-conv hX eU
            hAty = isty-el (ty-sub hAU)
            hU = ucTy (snd (pTE eU))
            hWU = wkTy hAty (isty-el hU)
            conv : {f' g' : Expr n} -> TyEq G (Ucode f' g') X -> TyEq G (Ucode f' g') (Ucode f g)
            conv q = tyeq-trans q eU
            uB : Dec (HasType (extend G A) B (wkExpr (Ucode f g))) ->
                 LRes G T (\ C -> Sg (Expr n) (\ f' -> Sg (Expr n) (\ g' ->
                   TyEq G (Ucode f' g') X * (HasType (extend G A) B (wkExpr (Ucode f' g')) *
                                             TyEq G C (Ucode f' g')))))
            uB (no k) = nilRes (\ { C (f' , (g' , (q , (hB , eq)))) ->
                          k (ty-conv hB (wkTE hAty (conv q))) })
            uB (yes hB) = lres (Ucode f g :: []) (mk (univ-U f g refl) hAU hB , unit)
                               (\ { C (f' , (g' , (q , (hB' , eq)))) -> here (tyeq-trans eq (conv q)) })

  piRes : {A : Expr n} {B : Expr (suc n)} -> Res G A ->
          ((hA : IsType G A) -> Chkr (extend G A) B) -> Res G (PiB A B)
  piRes {A} {B} rA chkB =
    weakRes (\ C h -> let r = invPi h ; e = snd (lam-inj (PiInv.eF r)) in
                      any-map (\ X q -> PiInv.u r , (PiInv.un r , (q ,
                                 (transport (\ Z -> HasType (extend G A) Z (wkExpr (PiInv.u r))) (Eq-sym e) (PiInv.hB r) ,
                                  PiInv.eq r))))
                              (cmp rA _ (PiInv.hA r)))
      (bindRes (L rA) (sound rA) (\ X hX -> univOne chkB (\ un hA hB -> ty-Pi un hA hB) hX))

  sigRes : {A : Expr n} {B : Expr (suc n)} -> Res G A ->
           ((hA : IsType G A) -> Chkr (extend G A) B) -> Res G (SigmaB A B)
  sigRes {A} {B} rA chkB =
    weakRes (\ C h -> let r = invSigma h ; e = snd (lam-inj (PiInv.eF r)) in
                      any-map (\ X q -> PiInv.u r , (PiInv.un r , (q ,
                                 (transport (\ Z -> HasType (extend G A) Z (wkExpr (PiInv.u r))) (Eq-sym e) (PiInv.hB r) ,
                                  PiInv.eq r))))
                              (cmp rA _ (PiInv.hA r)))
      (bindRes (L rA) (sound rA) (\ X hX -> univOne chkB (\ un hA hB -> ty-Sigma un hA hB) hX))

  ----------------------------------------------------------------------
  -- Nat, codes, fhat, ghat, rec
  ----------------------------------------------------------------------

  zeroRes : Res G Zero
  zeroRes = lres (Nat :: []) (ty-Zero w , unit) (\ C h -> here (invZero h))

  sucRes : {t : Expr n} -> Chkr G t -> Res G (Suc t)
  sucRes {t} chk = h (chk Nat (NatTy w))
    where
      h : Dec (HasType G t Nat) -> Res G (Suc t)
      h (yes ht) = lres (Nat :: []) (ty-Suc ht , unit) (\ C h' -> here (snd (invSuc h')))
      h (no k) = nilRes (\ C h' -> k (fst (invSuc h')))

  ucodeRes : {f g : Expr n} -> Chkr G f -> Chkr G g -> Res G (Ucode f g)
  ucodeRes {f} {g} chkf chkg = h1 (chkf OpF (opFTy w))
    where
      h1 : Dec (HasType G f OpF) -> Res G (Ucode f g)
      h1 (no k) = nilRes (\ C h -> k (fst (invUcode h)))
      h1 (yes hf) = h2 (chkg (OpG f) (opGTy w hf))
        where
          h2 : Dec (HasType G g (OpG f)) -> Res G (Ucode f g)
          h2 (no k) = nilRes (\ C h -> k (fst (snd (invUcode h))))
          h2 (yes hg) = lres (V :: []) (ty-Ucode hf hg , unit)
                             (\ C h -> here (snd (snd (invUcode h))))

  private
    -- the common premises of fhat and ghat
    record FG (f g A : Expr n) (B : Expr (suc n)) : Set where
      constructor fg
      field
        hf : HasType G f OpF
        hg : HasType G g (OpG f)
        hA : HasType G A (Ucode f g)
        hB : HasType (extend G A) B (wkExpr (Ucode f g))

    decFG : {f g A : Expr n} {B : Expr (suc n)} -> Chkr G f -> Chkr G g -> Chkr G A ->
            ((hA : IsType G A) -> Chkr (extend G A) B) -> Dec (FG f g A B)
    decFG {f} {g} {A} {B} chkf chkg chkA chkB = h1 (chkf OpF (opFTy w))
      where
        h1 : Dec (HasType G f OpF) -> Dec (FG f g A B)
        h1 (no k) = no (\ x -> k (FG.hf x))
        h1 (yes hf) = h2 (chkg (OpG f) (opGTy w hf))
          where
            h2 : Dec (HasType G g (OpG f)) -> Dec (FG f g A B)
            h2 (no k) = no (\ x -> k (FG.hg x))
            h2 (yes hg) = h3 (chkA (Ucode f g) (isty-el hU))
              where
                hU = ty-Ucode hf hg
                h3 : Dec (HasType G A (Ucode f g)) -> Dec (FG f g A B)
                h3 (no k) = no (\ x -> k (FG.hA x))
                h3 (yes hA) = h4 (chkB hAty (wkExpr (Ucode f g)) (wkTy hAty (isty-el hU)))
                  where
                    hAty = isty-el (ty-sub hA)
                    h4 : Dec (HasType (extend G A) B (wkExpr (Ucode f g))) -> Dec (FG f g A B)
                    h4 (no k) = no (\ x -> k (FG.hB x))
                    h4 (yes hB) = yes (fg hf hg hA hB)

  fhatRes : {f g A : Expr n} {B : Expr (suc n)} -> Chkr G f -> Chkr G g -> Chkr G A ->
            ((hA : IsType G A) -> Chkr (extend G A) B) -> Res G (Fhat f g A (Lam A B))
  fhatRes {f} {g} {A} {B} chkf chkg chkA chkB = h (decFG chkf chkg chkA chkB)
    where
      h : Dec (FG f g A B) -> Res G (Fhat f g A (Lam A B))
      h (yes (fg hf hg hA hB)) =
        lres (Ucode f g :: V :: []) (hF , (ty-sub hF , unit))
             (\ C h' -> c (FhatInv.ty (invFhat h')))
        where
          hF = ty-Fhat hf hg hA hB
          c : {C : Expr n} -> TyEq G C (Ucode f g) + TyEq G C V -> Any (TyEq G C) (Ucode f g :: V :: [])
          c (inl e) = here e
          c (inr e) = there (here e)
      h (no k) = nilRes (\ C h' -> let r = invFhat h' in
                   k (fg (FhatInv.hf r) (FhatInv.hg r) (FhatInv.hA r)
                         (transport (\ Z -> HasType (extend G A) Z (wkExpr (Ucode f g)))
                            (Eq-sym (snd (lam-inj (FhatInv.eF r)))) (FhatInv.hB r))))

  ghatRes : {f g A c : Expr n} {B : Expr (suc n)} -> Chkr G f -> Chkr G g -> Chkr G A ->
            ((hA : IsType G A) -> Chkr (extend G A) B) -> Chkr G c ->
            Res G (Ghat f g A (Lam A B) c)
  ghatRes {f} {g} {A} {c} {B} chkf chkg chkA chkB chkc = h (decFG chkf chkg chkA chkB)
    where
      fromInv : {C : Expr n} -> HasType G (Ghat f g A (Lam A B) c) C -> FG f g A B
      fromInv h' = let r = invGhat h' in
        fg (GhatInv.hf r) (GhatInv.hg r) (GhatInv.hA r)
           (transport (\ Z -> HasType (extend G A) Z (wkExpr (Ucode f g)))
              (Eq-sym (snd (lam-inj (GhatInv.eF r)))) (GhatInv.hB r))
      h : Dec (FG f g A B) -> Res G (Ghat f g A (Lam A B) c)
      h (no k) = nilRes (\ C h' -> k (fromInv h'))
      h (yes (fg hf hg hA hB)) = h5 (chkc (Fhat f g A (Lam A B)) (isty-el (ty-sub (ty-Fhat hf hg hA hB))))
        where
          h5 : Dec (HasType G c (Fhat f g A (Lam A B))) -> Res G (Ghat f g A (Lam A B) c)
          h5 (no k) = nilRes (\ C h' -> let r = invGhat h' in
                        k (transport (\ Z -> HasType G c (Fhat f g A (Lam A Z)))
                             (Eq-sym (snd (lam-inj (GhatInv.eF r)))) (GhatInv.hc r)))
          h5 (yes hc) =
            lres (Ucode f g :: V :: []) (hGh , (ty-sub hGh , unit))
                 (\ C h' -> cc (GhatInv.ty (invGhat h')))
            where
              hGh = ty-Ghat hf hg hA hB hc
              cc : {C : Expr n} -> TyEq G C (Ucode f g) + TyEq G C V -> Any (TyEq G C) (Ucode f g :: V :: [])
              cc (inl e) = here e
              cc (inr e) = there (here e)

  private
    wsSuc : MAHLOINJ.Syntax.Subst.WtSub (extend G Nat) (extend G Nat) sucSub
    wsSuc fzero = ty-Suc (ty-var (wf-extend (NatTy w)))
    wsSuc (fsuc i) =
      trHT refl (Eq-sym (MAHLOINJ.Syntax.Lemmas.sucSub-wk (lookup G i))) (ty-var (wf-extend (NatTy w)))

  recStepTy : {C0 : Expr (suc n)} -> IsType (extend G Nat) C0 -> IsType G (RecStep C0)
  recStepTy hC =
    isty-Pi (NatTy w) (isty-Pi hC (wkTy hC (sbTy sucSub wsSuc (wf-extend (NatTy w)) hC)))

  recRes : {C0 : Expr (suc n)} {z s k : Expr n} -> Dec (IsType (extend G Nat) C0) ->
           Chkr G z -> Chkr G s -> Chkr G k -> Res G (Rec (Lam Nat C0) z s k)
  recRes {C0} {z} {s} {k} (no kC) chkz chks chkk =
    nilRes (\ C h -> let r = invRec h in
                     kC (transport (IsType (extend G Nat)) (Eq-sym (snd (lam-inj (RecInv.eF r)))) (RecInv.hC r)))
  recRes {C0} {z} {s} {k} (yes hC) chkz chks chkk =
    h1 (chkz (subst1 C0 Zero) (s1Ty w (ty-Zero w) hC))
    where
      same : {C : Expr n} (r : RecInv G (Lam Nat C0) z s k C) -> Eq (RecInv.C0 r) C0
      same r = Eq-sym (snd (lam-inj (RecInv.eF r)))
      h1 : Dec (HasType G z (subst1 C0 Zero)) -> Res G (Rec (Lam Nat C0) z s k)
      h1 (no kz) = nilRes (\ C h -> let r = invRec h in
                     kz (transport (\ Z -> HasType G z (subst1 Z Zero)) (same r) (RecInv.hz r)))
      h1 (yes hz) = h2 (chks (RecStep C0) (recStepTy hC))
        where
          h2 : Dec (HasType G s (RecStep C0)) -> Res G (Rec (Lam Nat C0) z s k)
          h2 (no ks) = nilRes (\ C h -> let r = invRec h in
                         ks (transport (\ Z -> HasType G s (RecStep Z)) (same r) (RecInv.hs r)))
          h2 (yes hs) = h3 (chkk Nat (NatTy w))
            where
              h3 : Dec (HasType G k Nat) -> Res G (Rec (Lam Nat C0) z s k)
              h3 (no kk) = nilRes (\ C h -> kk (RecInv.hk (invRec h)))
              h3 (yes hk) =
                weakRes (\ C h -> let r = invRec h in
                                  transport (\ Z -> UpTo G C (subst1 Z k)) (same r) (RecInv.up r))
                  (sat (subst1 C0 k) (ty-Rec hC hz hs hk))

  ----------------------------------------------------------------------
  -- check-only forms
  ----------------------------------------------------------------------

  pairChk : {a b : Expr n} -> Chkr G a -> Chkr G b -> Chkr G (Pair a b)
  pairChk {a} {b} chka chkb C hC = h (decSig hC)
    where
      h : Dec (Sg (Expr n) (\ A -> Sg (Expr (suc n)) (\ B -> TyEq G C (SigmaB A B)))) ->
          Dec (HasType G (Pair a b) C)
      h (no k) = no (\ x -> let r = invPair x in k (PairInv.A r , (PairInv.B r , PairInv.eq r)))
      h (yes (A , (B , e))) = h2 (chka A hA)
        where
          hAB = sigTyInv (snd (pTE e))
          hA = fst hAB
          hB = snd hAB
          sinj : {A0 : Expr n} {B0 : Expr (suc n)} -> TyEq G C (SigmaB A0 B0) ->
                TyEq G A0 A * TyEq (extend G A0) B0 B
          sinj eq = Sig-inj (tyeq-trans (tyeq-sym eq) e)
          h2 : Dec (HasType G a A) -> Dec (HasType G (Pair a b) C)
          h2 (no k) = no (\ x -> let r = invPair x in
                        k (ty-conv (PairInv.ht r) (fst (sinj (PairInv.eq r)))))
          h2 (yes ha) = h3 (chkb (subst1 B a) (s1Ty w ha hB))
            where
              h3 : Dec (HasType G b (subst1 B a)) -> Dec (HasType G (Pair a b) C)
              h3 (no k) = no (\ x -> let r = invPair x in
                            k (ty-conv (PairInv.hu r)
                                 (s1TE' w (PairInv.ht r) (snd (sinj (PairInv.eq r))))))
              h3 (yes hb) = yes (ty-conv (ty-Pair hA hB ha hb) (tyeq-sym e))

  lamChk : {A : Expr n} {b : Expr (suc n)} -> Dec (IsType G A) ->
           ((hA : IsType G A) -> Chkr (extend G A) b) -> Chkr G (Lam A b)
  lamChk (no k) chkb C hC = no (\ x -> k (LamInv.hA (invLam x)))
  lamChk {A} {b} (yes hA) chkb C hC = h (decPi hC)
    where
      h : Dec (Sg (Expr n) (\ A' -> Sg (Expr (suc n)) (\ B' -> TyEq G C (PiB A' B')))) ->
          Dec (HasType G (Lam A b) C)
      h (no k) = no (\ x -> let r = invLam x in k (A , (LamInv.B r , LamInv.eq r)))
      h (yes (A' , (B' , e))) = h2 (decTyEq hA hA')
        where
          hAB = piTyInv (snd (pTE e))
          hA' = fst hAB
          hB' = snd hAB
          sinj : {B0 : Expr (suc n)} -> TyEq G C (PiB A B0) -> TyEq G A A' * TyEq (extend G A) B0 B'
          sinj eq = Pi-inj (tyeq-trans (tyeq-sym eq) e)
          h2 : Dec (TyEq G A A') -> Dec (HasType G (Lam A b) C)
          h2 (no k) = no (\ x -> k (fst (sinj (LamInv.eq (invLam x)))))
          h2 (yes qA) = h3 (chkb hA B' hB'A)
            where
              hB'A = ccTy hA qA hB'
              h3 : Dec (HasType (extend G A) b B') -> Dec (HasType G (Lam A b) C)
              h3 (no k) = no (\ x -> let r = invLam x in
                            k (ty-conv (LamInv.ht r) (snd (sinj (LamInv.eq r)))))
              h3 (yes hb) =
                yes (ty-conv (ty-Lam hA hB'A hb)
                       (tyeq-trans (tyeq-Pi hA hB'A hB'A qA (tyeq-refl hB'A)) (tyeq-sym e)))

  natChk : Chkr G Nat
  natChk C hC = h (decTyEq hC (isty-V w))
    where
      h : Dec (TyEq G C V) -> Dec (HasType G Nat C)
      h (yes e) = yes (ty-conv (ty-Nat-V w) (tyeq-sym e))
      h (no kV) = h2 (decU hC)
        where
          h2 : Dec (Sg (Expr n) (\ f -> Sg (Expr n) (\ g -> TyEq G C (Ucode f g)))) ->
               Dec (HasType G Nat C)
          h2 (yes (f , (g , e))) = yes (ty-conv (ty-Nat-U (ucTy (snd (pTE e)))) (tyeq-sym e))
          h2 (no kU) = no (\ x -> c (invNat x))
            where
              c : TyEq G C V + Sg (Expr n) (\ f -> Sg (Expr n) (\ g ->
                    HasType G (Ucode f g) V * TyEq G C (Ucode f g))) -> Empty
              c (inl e) = kV e
              c (inr (f , (g , (hU , e)))) = kU (f , (g , e))

  private
    -- Pi / Sigma checked against a given universe C
    univChk : {T A : Expr n} {B : Expr (suc n)} ->
              Chkr G A -> ((hA : IsType G A) -> Chkr (extend G A) B) ->
              ({u : Expr n} -> Univ u -> HasType G A u -> HasType (extend G A) B (wkExpr u) ->
                HasType G T u) ->
              ({C : Expr n} -> HasType G T C -> PiInv G A (Lam A B) C) ->
              Chkr G T
    univChk {T} {A} {B} chkA chkB mk inv C hC = h (decTyEq hC (isty-V w))
      where
        inv' : {C' : Expr n} -> HasType G T C' -> Sg (Expr n) (\ u -> Univ u *
                 (HasType G A u * (HasType (extend G A) B (wkExpr u) * TyEq G C' u)))
        inv' x = let r = inv x in
          PiInv.u r , (PiInv.un r , (PiInv.hA r ,
            (transport (\ Z -> HasType (extend G A) Z (wkExpr (PiInv.u r)))
               (Eq-sym (snd (lam-inj (PiInv.eF r)))) (PiInv.hB r) , PiInv.eq r)))
        h : Dec (TyEq G C V) -> Dec (HasType G T C)
        h (yes eV) = h1 (chkA V (isty-V w))
          where
            h1 : Dec (HasType G A V) -> Dec (HasType G T C)
            h1 (no k) = no (\ x -> let r = inv' x in k (toV (fst (snd r)) (fst (snd (snd r)))))
            h1 (yes hAV) = h2 (chkB (isty-el hAV) V (isty-V (wf-extend (isty-el hAV))))
              where
                h2 : Dec (HasType (extend G A) B V) -> Dec (HasType G T C)
                h2 (no k) = no (\ x -> let r = inv' x in
                              k (toV (renUniv wkRen (fst (snd r))) (fst (snd (snd (snd r))))))
                h2 (yes hBV) = yes (ty-conv (mk (univ-V refl) hAV hBV) (tyeq-sym eV))
        h (no kV) = h1 (decU hC)
          where
            h1 : Dec (Sg (Expr n) (\ f -> Sg (Expr n) (\ g -> TyEq G C (Ucode f g)))) ->
                 Dec (HasType G T C)
            h1 (no kU) = no (\ x -> c (inv' x))
              where
                c : Sg (Expr n) (\ u -> Univ u * (HasType G A u *
                      (HasType (extend G A) B (wkExpr u) * TyEq G C u))) -> Empty
                c (u , (univ-V refl , (_ , (_ , e)))) = kV e
                c (u , (univ-U f g refl , (_ , (_ , e)))) = kU (f , (g , e))
            h1 (yes (f , (g , eU))) = h2 (chkA (Ucode f g) (isty-el hU))
              where
                hU = ucTy (snd (pTE eU))
                -- any universe of T, given C ~ U(f,g), is U(f,g) up to TyEq
                conv : {u : Expr n} -> Univ u -> TyEq G C u -> TyEq G u (Ucode f g)
                conv (univ-V refl) e = Empty-elim (kV e)
                conv (univ-U f' g' refl) e = tyeq-trans (tyeq-sym e) eU
                h2 : Dec (HasType G A (Ucode f g)) -> Dec (HasType G T C)
                h2 (no k) = no (\ x -> let r = inv' x in
                              k (ty-conv (fst (snd (snd r)))
                                   (conv (fst (snd r)) (snd (snd (snd (snd r)))))))
                h2 (yes hAU) = h3 (chkB hAty (wkExpr (Ucode f g)) (wkTy hAty (isty-el hU)))
                  where
                    hAty = isty-el (ty-sub hAU)
                    h3 : Dec (HasType (extend G A) B (wkExpr (Ucode f g))) -> Dec (HasType G T C)
                    h3 (no k) = no (\ x -> let r = inv' x in
                                  k (ty-conv (fst (snd (snd (snd r))))
                                       (wkTE hAty (conv (fst (snd r)) (snd (snd (snd (snd r))))))))
                    h3 (yes hBU) = yes (ty-conv (mk (univ-U f g refl) hAU hBU) (tyeq-sym eU))

  piChk : {A : Expr n} {B : Expr (suc n)} -> Chkr G A ->
          ((hA : IsType G A) -> Chkr (extend G A) B) -> Chkr G (PiB A B)
  piChk chkA chkB = univChk chkA chkB (\ un hA hB -> ty-Pi un hA hB) invPi

  sigChk : {A : Expr n} {B : Expr (suc n)} -> Chkr G A ->
           ((hA : IsType G A) -> Chkr (extend G A) B) -> Chkr G (SigmaB A B)
  sigChk chkA chkB = univChk chkA chkB (\ un hA hB -> ty-Sigma un hA hB) invSigma
