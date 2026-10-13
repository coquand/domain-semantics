{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Model/EvalFwd.agda
--
-- Forward substitution with a witness environment:
--   EvalRel (sigma M) rho u  ->  exists rho' (coherent), SubRel sigma rho rho',
--                                EvalRel M rho' u.
-- Witness environments are joined pointwise (they are compatible, being
-- below the same ideals [sigma i]rho).
------------------------------------------------------------------------

module MAHLOINJ.Model.EvalFwd where

open import MAHLOINJ.Domain.Basic
  using ( Top ; tt ; Empty ; Pair ; mkSigma ; fst ; snd ; Sigma
        ; Eq ; refl ; Eq-transport ; Eq-sym
        ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl
        ; PairEl ; SigmaCode ; FinFun ; nil ; cons )
open import MAHLOINJ.Domain.Kernel
open import MAHLOINJ.Model.Selection
open import MAHLOINJ.Model.Comb
open import MAHLOINJ.Model.Eval
open import MAHLOINJ.Model.EvalSubst
open import MAHLO.Syntax
  using ( Num ; Fin ; fzero ; fsuc ; Expr
        ; Var ; Lam ; App ; Pi ; Fst ; Snd ; Nat ; Zero ; Suc ; Rec
        ; V ; Ucode ; Fhat ; Ghat
        ; Sub ; liftSub ; substExpr ; subst1Sub ; subst1 ; wkExpr )
  renaming (zero to nzero ; suc to nsuc ; Sigma to SigmaE ; Pair to PairE)

------------------------------------------------------------------------
-- Environments: bottom, point, join
------------------------------------------------------------------------

botEnv : {n : Num} -> EnvApprox n
botEnv {nzero}  = emptyEnv
botEnv {nsuc n} = extendEnv botEnv Bot

botEnv-coh : {n : Num} -> CoherentEnv (botEnv {n})
botEnv-coh {nzero}  = tt
botEnv-coh {nsuc n} = mkSigma botEnv-coh tt

lookup-botEnv : {n : Num} (i : Fin n) -> Eq (lookupEnv i (botEnv {n})) Bot
lookup-botEnv fzero    = refl
lookup-botEnv (fsuc i) = lookup-botEnv i

pointEnv : {n : Num} -> Fin n -> FinEl -> EnvApprox n
pointEnv fzero    u = extendEnv botEnv u
pointEnv (fsuc i) u = extendEnv (pointEnv i u) Bot

pointEnv-coh : {n : Num} (i : Fin n) (u : FinEl) -> Coherent u -> CoherentEnv (pointEnv i u)
pointEnv-coh fzero    u c = mkSigma botEnv-coh c
pointEnv-coh (fsuc i) u c = mkSigma (pointEnv-coh i u c) tt

pointEnv-at : {n : Num} (i : Fin n) (u : FinEl) -> Eq (lookupEnv i (pointEnv i u)) u
pointEnv-at fzero    u = refl
pointEnv-at (fsuc i) u = pointEnv-at i u

supEnv : {n : Num} -> EnvApprox n -> EnvApprox n -> EnvApprox n
supEnv emptyEnv emptyEnv = emptyEnv
supEnv (extendEnv r1 u1) (extendEnv r2 u2) = extendEnv (supEnv r1 r2) (Sup u1 u2)

CompEnv : {n : Num} -> EnvApprox n -> EnvApprox n -> Set
CompEnv emptyEnv emptyEnv = Top
CompEnv (extendEnv r1 u1) (extendEnv r2 u2) = Pair (CompEnv r1 r2) (Comp u1 u2)

supEnv-coh : {n : Num} (r1 r2 : EnvApprox n) -> CoherentEnv r1 -> CoherentEnv r2 -> CompEnv r1 r2 ->
  CoherentEnv (supEnv r1 r2)
supEnv-coh emptyEnv emptyEnv c1 c2 cc = tt
supEnv-coh (extendEnv r1 u1) (extendEnv r2 u2) c1 c2 cc =
  mkSigma (supEnv-coh r1 r2 (fst c1) (fst c2) (fst cc)) (Coherent-Sup u1 u2 (snd cc) (snd c1) (snd c2))

supEnv-le-l : {n : Num} (r1 r2 : EnvApprox n) -> CoherentEnv r1 -> CoherentEnv r2 -> CompEnv r1 r2 ->
  EnvLe r1 (supEnv r1 r2)
supEnv-le-l emptyEnv emptyEnv c1 c2 cc = tt
supEnv-le-l (extendEnv r1 u1) (extendEnv r2 u2) c1 c2 cc =
  mkSigma (supEnv-le-l r1 r2 (fst c1) (fst c2) (fst cc))
    (mkSigma (snd c1) (mkSigma (Coherent-Sup u1 u2 (snd cc) (snd c1) (snd c2))
      (LeCode-Sup-left u1 u2 (snd cc) (snd c1) (snd c2))))

supEnv-le-r : {n : Num} (r1 r2 : EnvApprox n) -> CoherentEnv r1 -> CoherentEnv r2 -> CompEnv r1 r2 ->
  EnvLe r2 (supEnv r1 r2)
supEnv-le-r emptyEnv emptyEnv c1 c2 cc = tt
supEnv-le-r (extendEnv r1 u1) (extendEnv r2 u2) c1 c2 cc =
  mkSigma (supEnv-le-r r1 r2 (fst c1) (fst c2) (fst cc))
    (mkSigma (snd c2) (mkSigma (Coherent-Sup u1 u2 (snd cc) (snd c1) (snd c2))
      (LeCode-Sup-right u1 u2 (snd cc) (snd c1) (snd c2))))

------------------------------------------------------------------------
-- Witnesses for a fixed  sigma, rho
------------------------------------------------------------------------

module W {h g : Num} (sigma : Sub h g) (rho : EnvApprox h) (crho : CoherentEnv rho) where

  Wit : EnvApprox g -> Set
  Wit r = Pair (CoherentEnv r) (SubRel sigma rho r)

  -- SubRel components restricted to the tail
  sr-tail : {n : Num} -> Sub h (nsuc n) -> Sub h n
  sr-tail s i = s (fsuc i)

  bot-wit : Wit botEnv
  bot-wit = mkSigma botEnv-coh
    (\ i -> Eq-transport (EvalRel (sigma i) rho) (Eq-sym (lookup-botEnv i)) (EvalRel-Bot (sigma i) rho crho))

  point-wit : (i : Fin g) (u : FinEl) -> EvalRel (sigma i) rho u -> Wit (pointEnv i u)
  point-wit i u e = mkSigma (pointEnv-coh i u (EvalRel-coh (sigma i) rho crho u e)) (pw sigma i u e)
    where
      pw : {n : Num} (s : Sub h n) (i : Fin n) (u : FinEl) -> EvalRel (s i) rho u -> SubRel s rho (pointEnv i u)
      pw s fzero    u e fzero    = e
      pw s fzero    u e (fsuc j) =
        Eq-transport (EvalRel (s (fsuc j)) rho) (Eq-sym (lookup-botEnv j)) (EvalRel-Bot (s (fsuc j)) rho crho)
      pw s (fsuc i) u e fzero    = EvalRel-Bot (s fzero) rho crho
      pw s (fsuc i) u e (fsuc j) = pw (\ k -> s (fsuc k)) i u e j

  compEnv : {n : Num} (s : Sub h n) (r1 r2 : EnvApprox n) -> SubRel s rho r1 -> SubRel s rho r2 -> CompEnv r1 r2
  compEnv s emptyEnv emptyEnv s1 s2 = tt
  compEnv s (extendEnv r1 u1) (extendEnv r2 u2) s1 s2 =
    mkSigma (compEnv (\ k -> s (fsuc k)) r1 r2 (\ k -> s1 (fsuc k)) (\ k -> s2 (fsuc k)))
            (EvalRel-Comp (s fzero) rho crho u1 u2 (s1 fzero) (s2 fzero))

  supSub : {n : Num} (s : Sub h n) (r1 r2 : EnvApprox n) -> SubRel s rho r1 -> SubRel s rho r2 ->
    SubRel s rho (supEnv r1 r2)
  supSub s (extendEnv r1 u1) (extendEnv r2 u2) s1 s2 fzero =
    EvalRel-Sup (s fzero) rho crho u1 u2 (s1 fzero) (s2 fzero)
  supSub s (extendEnv r1 u1) (extendEnv r2 u2) s1 s2 (fsuc i) =
    supSub (\ k -> s (fsuc k)) r1 r2 (\ k -> s1 (fsuc k)) (\ k -> s2 (fsuc k)) i

  record Join (r1 r2 : EnvApprox g) : Set where
    field
      env : EnvApprox g
      wit : Wit env
      le1 : EnvLe r1 env
      le2 : EnvLe r2 env

  join : (r1 r2 : EnvApprox g) -> Wit r1 -> Wit r2 -> Join r1 r2
  join r1 r2 w1 w2 =
    let cc = compEnv sigma r1 r2 (snd w1) (snd w2)
    in record { env = supEnv r1 r2
              ; wit = mkSigma (supEnv-coh r1 r2 (fst w1) (fst w2) cc) (supSub sigma r1 r2 (snd w1) (snd w2))
              ; le1 = supEnv-le-l r1 r2 (fst w1) (fst w2) cc
              ; le2 = supEnv-le-r r1 r2 (fst w1) (fst w2) cc }

  -- forward property of a pair (source predicate, env-indexed target predicate)
  Fwd : Pred -> (EnvApprox g -> Pred) -> Set
  Fwd Ps Pt = (u : FinEl) -> Ps u -> Sigma (EnvApprox g) (\ r -> Pair (Wit r) (Pt r u))

  MonT : (EnvApprox g -> Pred) -> Set
  MonT Pt = (r1 r2 : EnvApprox g) -> EnvLe r1 r2 -> (u : FinEl) -> Pt r1 u -> Pt r2 u

  -- target predicates contain Bot at every witness env
  BotT : (EnvApprox g -> Pred) -> Set
  BotT Pt = (r : EnvApprox g) -> CoherentEnv r -> Pt r Bot

  fwd-bot : (Pt : EnvApprox g -> Pred) -> BotT Pt -> Sigma (EnvApprox g) (\ r -> Pair (Wit r) (Pt r Bot))
  fwd-bot Pt bt = mkSigma botEnv (mkSigma bot-wit (bt botEnv botEnv-coh))

  -- combine two forward results
  fwd2 : (Pt Qt : EnvApprox g -> Pred) -> MonT Pt -> MonT Qt -> (u v : FinEl) ->
    Sigma (EnvApprox g) (\ r -> Pair (Wit r) (Pt r u)) ->
    Sigma (EnvApprox g) (\ r -> Pair (Wit r) (Qt r v)) ->
    Sigma (EnvApprox g) (\ r -> Pair (Wit r) (Pair (Pt r u) (Qt r v)))
  fwd2 Pt Qt mp mq u v x y =
    let J = join (fst x) (fst y) (fst (snd x)) (fst (snd y))
    in mkSigma (Join.env J) (mkSigma (Join.wit J)
         (mkSigma (mp (fst x) (Join.env J) (Join.le1 J) u (snd (snd x)))
                  (mq (fst y) (Join.env J) (Join.le2 J) v (snd (snd y)))))

  AppS-fwd : (Pf Pa : Pred) (Tf Ta : EnvApprox g -> Pred) -> Fwd Pf Tf -> Fwd Pa Ta -> MonT Tf -> MonT Ta ->
    Fwd (AppS Pf Pa) (\ r -> AppS (Tf r) (Ta r))
  AppS-fwd Pf Pa Tf Ta ff fa mf ma u e = go (bot-or u)
    where
      go : Or (Eq u Bot) (NotBot u) -> Sigma (EnvApprox g) (\ r -> Pair (Wit r) (AppS (Tf r) (Ta r) u))
      go (left refl) = mkSigma botEnv (mkSigma bot-wit tt)
      go (right nb) =
        let b = guard-elim u nb e
            v = fst b
            x = fwd2 Ta Tf ma mf v (sing v u) (fa v (fst (snd b))) (ff (sing v u) (snd (snd b)))
        in mkSigma (fst x) (mkSigma (fst (snd x))
             (guard-intro u nb (mkSigma v (mkSigma (fst (snd (snd x))) (snd (snd (snd x)))))))

  AppS-monT : (Tf Ta : EnvApprox g -> Pred) -> MonT Tf -> MonT Ta -> MonT (\ r -> AppS (Tf r) (Ta r))
  AppS-monT Tf Ta mf ma r1 r2 le = AppS-map _ _ _ _ (mf r1 r2 le) (ma r1 r2 le)

  EvalRel-monT : (M : Expr g) -> MonT (EvalRel M)
  EvalRel-monT M r1 r2 le = EvalRel-mon-env M r1 r2 le

  CodeBody-fwd : (PA PF : Pred) (TA TF : EnvApprox g -> Pred) -> Fwd PA TA -> Fwd PF TF ->
    MonT TA -> MonT TF -> BotT TA -> (a : FinEl) (f : FinFun) -> CodeBody PA PF a f ->
    Sigma (EnvApprox g) (\ r -> Pair (Wit r) (CodeBody (TA r) (TF r) a f))
  CodeBody-fwd PA PF TA TF fA fF mA mF bA a nil e =
    let x = fA a (fst (snd e)) in
    mkSigma (fst x) (mkSigma (fst (snd x)) (mkSigma (fst e) (mkSigma (snd (snd x)) tt)))
  CodeBody-fwd PA PF TA TF fA fF mA mF bA a (cons p ps) e =
    let x = fwd2 TA TF mA mF a (FunEl (cons p ps)) (fA a (fst (snd e))) (fF _ (snd (snd e)))
    in mkSigma (fst x) (mkSigma (fst (snd x)) (mkSigma (fst e) (snd (snd x))))

  PairS-fwd : (P Q : Pred) (Tp Tq : EnvApprox g -> Pred) -> Fwd P Tp -> Fwd Q Tq -> MonT Tp -> MonT Tq ->
    Fwd (PairS P Q) (\ r -> PairS (Tp r) (Tq r))
  PairS-fwd P Q Tp Tq fp fq mp mq Bot e = mkSigma botEnv (mkSigma bot-wit tt)
  PairS-fwd P Q Tp Tq fp fq mp mq (PairEl a b) e =
    let x = fwd2 Tp Tq mp mq a b (fp a (fst (snd e))) (fq b (snd (snd e)))
    in mkSigma (fst x) (mkSigma (fst (snd x)) (mkSigma (fst e) (snd (snd x))))

  FstS-fwd : (P : Pred) (Tp : EnvApprox g -> Pred) -> Fwd P Tp -> Fwd (FstS P) (\ r -> FstS (Tp r))
  FstS-fwd P Tp fp u e = go (bot-or u)
    where
      go : Or (Eq u Bot) (NotBot u) -> Sigma (EnvApprox g) (\ r -> Pair (Wit r) (FstS (Tp r) u))
      go (left refl) = mkSigma botEnv (mkSigma bot-wit tt)
      go (right nb) = let x = fp _ (guard-elim u nb e)
                      in mkSigma (fst x) (mkSigma (fst (snd x)) (guard-intro u nb (snd (snd x))))

  SndS-fwd : (P : Pred) (Tp : EnvApprox g -> Pred) -> Fwd P Tp -> Fwd (SndS P) (\ r -> SndS (Tp r))
  SndS-fwd P Tp fp u e = go (bot-or u)
    where
      go : Or (Eq u Bot) (NotBot u) -> Sigma (EnvApprox g) (\ r -> Pair (Wit r) (SndS (Tp r) u))
      go (left refl) = mkSigma botEnv (mkSigma bot-wit tt)
      go (right nb) = let x = fp _ (guard-elim u nb e)
                      in mkSigma (fst x) (mkSigma (fst (snd x)) (guard-intro u nb (snd (snd x))))

  SucS-fwd : (P : Pred) (Tp : EnvApprox g -> Pred) -> Fwd P Tp -> Fwd (SucS P) (\ r -> SucS (Tp r))
  SucS-fwd P Tp fp u e =
    let x = fp (fst (snd e)) (fst (snd (snd e)))
    in mkSigma (fst x) (mkSigma (fst (snd x))
         (mkSigma (fst e) (mkSigma (fst (snd e)) (mkSigma (snd (snd x)) (snd (snd (snd e)))))))

  RecB-fwd : (Pz Ps : Pred) (Tz Ts : EnvApprox g -> Pred) -> Fwd Pz Tz -> Fwd Ps Ts -> MonT Tz -> MonT Ts ->
    (c w : FinEl) -> RecB Pz Ps c w ->
    Sigma (EnvApprox g) (\ r -> Pair (Wit r) (RecB (Tz r) (Ts r) c w))
  RecB-fwd Pz Ps Tz Ts fz fs mz ms c ZeroEl e = fz c e
  RecB-fwd Pz Ps Tz Ts fz fs mz ms c (SucEl w) e = go (bot-or (fst e))
    where
      r0 = fst e
      sv = sing w (sing r0 c)
      go : Or (Eq r0 Bot) (NotBot r0) -> Sigma (EnvApprox g) (\ r -> Pair (Wit r) (RecB (Tz r) (Ts r) c (SucEl w)))
      go (left q) =
        let x = fs sv (snd (snd e))
        in mkSigma (fst x) (mkSigma (fst (snd x))
             (mkSigma r0 (mkSigma (Eq-transport (\ z -> Guard z (RecB (Tz (fst x)) (Ts (fst x)) z w)) (Eq-sym q) tt)
                                  (snd (snd x)))))
      go (right nb) =
        let y = RecB-fwd Pz Ps Tz Ts fz fs mz ms r0 w (guard-elim r0 nb (fst (snd e)))
            x = fs sv (snd (snd e))
            J = join (fst y) (fst x) (fst (snd y)) (fst (snd x))
            r' = Join.env J
        in mkSigma r' (mkSigma (Join.wit J)
             (mkSigma r0 (mkSigma
                (guard-intro r0 nb (RecB-map _ _ _ _ (mz _ _ (Join.le1 J)) (ms _ _ (Join.le1 J)) r0 w (snd (snd y))))
                (ms _ _ (Join.le2 J) sv (snd (snd x))))))

  RecS-fwd : (Pz Ps Pk : Pred) (Tz Ts Tk : EnvApprox g -> Pred) -> Fwd Pz Tz -> Fwd Ps Ts -> Fwd Pk Tk ->
    MonT Tz -> MonT Ts -> MonT Tk -> Fwd (RecS Pz Ps Pk) (\ r -> RecS (Tz r) (Ts r) (Tk r))
  RecS-fwd Pz Ps Pk Tz Ts Tk fz fs fk mz ms mk c e = go (bot-or c)
    where
      go : Or (Eq c Bot) (NotBot c) -> Sigma (EnvApprox g) (\ r -> Pair (Wit r) (RecS (Tz r) (Ts r) (Tk r) c))
      go (left refl) = mkSigma botEnv (mkSigma bot-wit tt)
      go (right nb) =
        let b = guard-elim c nb e
            w = fst b
            xk = fk w (fst (snd b))
            xb = RecB-fwd Pz Ps Tz Ts fz fs mz ms c w (snd (snd b))
            J  = join (fst xk) (fst xb) (fst (snd xk)) (fst (snd xb))
        in mkSigma (Join.env J) (mkSigma (Join.wit J)
             (guard-intro c nb (mkSigma w (mkSigma (mk _ _ (Join.le1 J) w (snd (snd xk)))
               (RecB-map _ _ _ _ (mz _ _ (Join.le2 J)) (ms _ _ (Join.le2 J)) c w (snd (snd xb)))))))

------------------------------------------------------------------------
-- The main theorem
------------------------------------------------------------------------

unlift : {h g : Num} (sigma : Sub h g) (rho : EnvApprox h) (x : FinEl) (r : EnvApprox (nsuc g)) ->
  CoherentEnv r -> SubRel (liftSub sigma) (extendEnv rho x) r ->
  Sigma (EnvApprox g) (\ r1 -> Sigma FinEl (\ x1 ->
    Pair (Eq r (extendEnv r1 x1)) (Pair (CoherentEnv r1)
      (Pair (SubRel sigma rho r1) (Pair (Coherent x1) (LeCode x1 x))))))
unlift sigma rho x (extendEnv r1 x1) c sr =
  mkSigma r1 (mkSigma x1 (mkSigma refl (mkSigma (fst c)
    (mkSigma (\ i -> EvalRel-unwk (sigma i) rho x (lookupEnv i r1) (sr (fsuc i)))
      (mkSigma (snd c) (snd (sr fzero)))))))

EvalRel-fwd : {h g : Num} (sigma : Sub h g) (M : Expr g) (rho : EnvApprox h) (crho : CoherentEnv rho) ->
  W.Fwd sigma rho crho (EvalRel (substExpr sigma M) rho) (EvalRel M)
EvalRel-fwd sigma (Var i) rho crho u e =
  mkSigma (pointEnv i u) (mkSigma (W.point-wit sigma rho crho i u e)
    (mkSigma (EvalRel-coh (sigma i) rho crho u e)
      (Eq-transport (LeCode u) (Eq-sym (pointEnv-at i u)) (LeCode-refl u (EvalRel-coh (sigma i) rho crho u e)))))
EvalRel-fwd sigma (App t a) rho crho =
  W.AppS-fwd sigma rho crho _ _ (EvalRel t) (EvalRel a) (EvalRel-fwd sigma t rho crho) (EvalRel-fwd sigma a rho crho)
    (W.EvalRel-monT sigma rho crho t) (W.EvalRel-monT sigma rho crho a)
EvalRel-fwd sigma (Pi A F) rho crho Bot e = W.fwd-bot sigma rho crho (EvalRel (Pi A F)) (\ r c -> tt)
EvalRel-fwd sigma (Pi A F) rho crho (PiCode a f) e =
  W.CodeBody-fwd sigma rho crho _ _ (EvalRel A) (EvalRel F) (EvalRel-fwd sigma A rho crho) (EvalRel-fwd sigma F rho crho)
    (W.EvalRel-monT sigma rho crho A) (W.EvalRel-monT sigma rho crho F) (\ r c -> EvalRel-Bot A r c) a f e
EvalRel-fwd sigma (SigmaE A F) rho crho Bot e = W.fwd-bot sigma rho crho (EvalRel (SigmaE A F)) (\ r c -> tt)
EvalRel-fwd sigma (SigmaE A F) rho crho (SigmaCode a f) e =
  W.CodeBody-fwd sigma rho crho _ _ (EvalRel A) (EvalRel F) (EvalRel-fwd sigma A rho crho) (EvalRel-fwd sigma F rho crho)
    (W.EvalRel-monT sigma rho crho A) (W.EvalRel-monT sigma rho crho F) (\ r c -> EvalRel-Bot A r c) a f e
EvalRel-fwd sigma (PairE t u) rho crho =
  W.PairS-fwd sigma rho crho _ _ (EvalRel t) (EvalRel u) (EvalRel-fwd sigma t rho crho) (EvalRel-fwd sigma u rho crho)
    (W.EvalRel-monT sigma rho crho t) (W.EvalRel-monT sigma rho crho u)
EvalRel-fwd sigma (Fst t) rho crho = W.FstS-fwd sigma rho crho _ (EvalRel t) (EvalRel-fwd sigma t rho crho)
EvalRel-fwd sigma (Snd t) rho crho = W.SndS-fwd sigma rho crho _ (EvalRel t) (EvalRel-fwd sigma t rho crho)
EvalRel-fwd sigma Nat rho crho u e = mkSigma botEnv (mkSigma (W.bot-wit sigma rho crho) e)
EvalRel-fwd sigma Zero rho crho u e = mkSigma botEnv (mkSigma (W.bot-wit sigma rho crho) e)
EvalRel-fwd sigma (Suc t) rho crho = W.SucS-fwd sigma rho crho _ (EvalRel t) (EvalRel-fwd sigma t rho crho)
EvalRel-fwd sigma (Rec C z s k) rho crho =
  W.RecS-fwd sigma rho crho _ _ _ (EvalRel z) (EvalRel s) (EvalRel k)
    (EvalRel-fwd sigma z rho crho) (EvalRel-fwd sigma s rho crho) (EvalRel-fwd sigma k rho crho)
    (W.EvalRel-monT sigma rho crho z) (W.EvalRel-monT sigma rho crho s) (W.EvalRel-monT sigma rho crho k)
EvalRel-fwd sigma V rho crho u e = mkSigma botEnv (mkSigma (W.bot-wit sigma rho crho) e)
EvalRel-fwd sigma (Ucode f g) rho crho u e = mkSigma botEnv (mkSigma (W.bot-wit sigma rho crho) e)
EvalRel-fwd sigma (Fhat f g A F) rho crho =
  W.AppS-fwd sigma rho crho _ _ _ (EvalRel F)
    (W.AppS-fwd sigma rho crho _ _ (EvalRel f) (EvalRel A) (EvalRel-fwd sigma f rho crho) (EvalRel-fwd sigma A rho crho)
       (W.EvalRel-monT sigma rho crho f) (W.EvalRel-monT sigma rho crho A))
    (EvalRel-fwd sigma F rho crho)
    (W.AppS-monT sigma rho crho _ _ (W.EvalRel-monT sigma rho crho f) (W.EvalRel-monT sigma rho crho A))
    (W.EvalRel-monT sigma rho crho F)
EvalRel-fwd sigma (Ghat f g A F c) rho crho =
  W.AppS-fwd sigma rho crho _ _ _ (EvalRel c)
    (W.AppS-fwd sigma rho crho _ _ _ (EvalRel F)
      (W.AppS-fwd sigma rho crho _ _ (EvalRel g) (EvalRel A) (EvalRel-fwd sigma g rho crho) (EvalRel-fwd sigma A rho crho)
         (W.EvalRel-monT sigma rho crho g) (W.EvalRel-monT sigma rho crho A))
      (EvalRel-fwd sigma F rho crho)
      (W.AppS-monT sigma rho crho _ _ (W.EvalRel-monT sigma rho crho g) (W.EvalRel-monT sigma rho crho A))
      (W.EvalRel-monT sigma rho crho F))
    (EvalRel-fwd sigma c rho crho)
    (W.AppS-monT sigma rho crho _ _
      (W.AppS-monT sigma rho crho _ _ (W.EvalRel-monT sigma rho crho g) (W.EvalRel-monT sigma rho crho A))
      (W.EvalRel-monT sigma rho crho F))
    (W.EvalRel-monT sigma rho crho c)
EvalRel-fwd sigma (Lam A t) rho crho Bot e = W.fwd-bot sigma rho crho (EvalRel (Lam A t)) (\ r c -> tt)
EvalRel-fwd {h} {g} sigma (Lam A t) rho crho (FunEl gf) e =
  let a = fst e ; cgf = fst (snd e) ; aU = fst (snd (snd e)) ; evA = fst (snd (snd (snd e)))
      body = snd (snd (snd (snd e)))
      ca = coh-from-aU a aU
      xA = EvalRel-fwd sigma A rho crho a evA
      xE = edges gf (LamBody-edge a _ gf body)
      J  = W.join sigma rho crho (fst xA) (fst xE) (fst (snd xA)) (fst (snd xE))
      r  = W.Join.env J
      cr = fst (W.Join.wit J)
      bB : BodyOK (\ x -> EvalRel t (extendEnv r x))
      bB = record { ideal = \ x cx -> EvalRel-ideal t (extendEnv r x) (mkSigma cr cx)
                  ; mon = \ x x' v cx cx' le ev ->
                      EvalRel-mon-env t (extendEnv r x) (extendEnv r x')
                        (mkSigma (EnvLe-refl r cr) (mkSigma cx (mkSigma cx' le))) v ev }
      ew : (p : Edge) -> EdgeIn p gf ->
           Sigma FinEl (\ x -> Pair (LeCode x (fst p)) (Pair (FinMem x a) (EvalRel t (extendEnv r x) (snd p))))
      ew p ein =
        let w = snd (snd xE) p ein ; x = fst w ; cx = FinMem-coh-u x a (fst (snd (snd w)))
        in mkSigma x (mkSigma (fst (snd w)) (mkSigma (fst (snd (snd w)))
             (EvalRel-mon-env t (extendEnv (fst xE) x) (extendEnv r x)
                (EnvLe-extend (fst xE) r x (W.Join.le2 J) cx) (snd p) (snd (snd (snd w))))))
  in mkSigma r (mkSigma (W.Join.wit J)
       (mkSigma a (mkSigma cgf (mkSigma aU
         (mkSigma (EvalRel-mon-env A (fst xA) r (W.Join.le1 J) a (snd (snd xA)))
           (LamEdges.from-edges _ bB a gf (cft-from-cf gf cgf) aU ew))))))
  where
    EW : EnvApprox g -> FinFun -> FinEl -> Set
    EW r gg a = (p : Edge) -> EdgeIn p gg ->
      Sigma FinEl (\ x -> Pair (LeCode x (fst p)) (Pair (FinMem x a) (EvalRel t (extendEnv r x) (snd p))))
    consEW : (p : Edge) (ps : FinFun) (a : FinEl) (r1 : EnvApprox g) -> W.Wit sigma rho crho r1 ->
      (x : FinEl) -> Coherent x -> LeCode x (fst p) -> FinMem x a -> EvalRel t (extendEnv r1 x) (snd p) ->
      Sigma (EnvApprox g) (\ r -> Pair (W.Wit sigma rho crho r) (EW r ps a)) ->
      Sigma (EnvApprox g) (\ r -> Pair (W.Wit sigma rho crho r) (EW r (cons p ps) a))
    consEW p ps a r1 w1 x cx lx mx ev tl =
      mkSigma (W.Join.env J) (mkSigma (W.Join.wit J) ewr)
      where
        J = W.join sigma rho crho r1 (fst tl) w1 (fst (snd tl))
        ewr : EW (W.Join.env J) (cons p ps) a
        ewr .p here = mkSigma x (mkSigma lx (mkSigma mx
          (EvalRel-mon-env t (extendEnv r1 x) (extendEnv (W.Join.env J) x)
             (EnvLe-extend r1 (W.Join.env J) x (W.Join.le1 J) cx) (snd p) ev)))
        ewr q (there ein) =
          let w' = snd (snd tl) q ein ; x' = fst w' ; cx' = FinMem-coh-u x' a (fst (snd (snd w')))
          in mkSigma x' (mkSigma (fst (snd w')) (mkSigma (fst (snd (snd w')))
               (EvalRel-mon-env t (extendEnv (fst tl) x') (extendEnv (W.Join.env J) x')
                  (EnvLe-extend (fst tl) (W.Join.env J) x' (W.Join.le2 J) cx') (snd q) (snd (snd (snd w'))))))
    edges : (gg : FinFun) ->
      ((p : Edge) -> EdgeIn p gg ->
        Sigma FinEl (\ x -> Pair (LeCode x (fst p)) (Pair (FinMem x (fst e))
          (EvalRel (substExpr (liftSub sigma) t) (extendEnv rho x) (snd p))))) ->
      Sigma (EnvApprox g) (\ r -> Pair (W.Wit sigma rho crho r) (EW r gg (fst e)))
    edges nil ew0 = mkSigma botEnv (mkSigma (W.bot-wit sigma rho crho) (\ p ()))
    edges (cons p ps) ew0 =
      let a = fst e ; aU = fst (snd (snd e)) ; ca = coh-from-aU a aU
          w  = ew0 p here
          x  = fst w ; cx = FinMem-coh-u x a (fst (snd (snd w)))
          fw = EvalRel-fwd (liftSub sigma) t (extendEnv rho x) (mkSigma crho cx) (snd p) (snd (snd (snd w)))
          ul = unlift sigma rho x (fst fw) (fst (fst (snd fw))) (snd (fst (snd fw)))
          r1 = fst ul ; x1 = fst (snd ul)
          eq = fst (snd (snd ul)) ; cr1 = fst (snd (snd (snd ul)))
          sr1 = fst (snd (snd (snd (snd ul))))
          cx1 = fst (snd (snd (snd (snd (snd ul)))))
          lx1 = snd (snd (snd (snd (snd (snd ul)))))
          ev1 = Eq-transport (\ z -> EvalRel t z (snd p)) eq (snd (snd fw))
          ev1' = EvalRel-mon-env t (extendEnv r1 x1) (extendEnv r1 x)
                   (mkSigma (EnvLe-refl r1 cr1) (mkSigma cx1 (mkSigma cx lx1))) (snd p) ev1
          tl = edges ps (\ q ein -> ew0 q (there ein))
      in consEW p ps a r1 (mkSigma cr1 sr1) x cx (fst (snd w)) (fst (snd (snd w))) ev1' tl
------------------------------------------------------------------------
-- Unary corollary
------------------------------------------------------------------------

EvalRel-subst1-forward : {n : Num} (M : Expr (nsuc n)) (N : Expr n) (rho : EnvApprox n) (u : FinEl) ->
  CoherentEnv rho -> EvalRel (subst1 M N) rho u ->
  Sigma FinEl (\ v -> Pair (EvalRel N rho v) (EvalRel M (extendEnv rho v) u))
EvalRel-subst1-forward M N rho u crho e =
  let fw = EvalRel-fwd (subst1Sub N) M rho crho u e
  in go (fst fw) (fst (snd fw)) (snd (snd fw))
  where
    lerho : {k : Num} (r' rho' : EnvApprox k) -> CoherentEnv r' -> CoherentEnv rho' ->
      ((i : Fin k) -> AtomS (lookupEnv i rho') (lookupEnv i r')) -> EnvLe r' rho'
    lerho emptyEnv emptyEnv c c' h = tt
    lerho (extendEnv r' x) (extendEnv rho' y) c c' h =
      mkSigma (lerho r' rho' (fst c) (fst c') (\ i -> h (fsuc i)))
        (mkSigma (snd c) (mkSigma (snd c') (snd (h fzero))))
    go : (r : EnvApprox (nsuc _)) -> W.Wit (subst1Sub N) rho crho r -> EvalRel M r u ->
      Sigma FinEl (\ v -> Pair (EvalRel N rho v) (EvalRel M (extendEnv rho v) u))
    go (extendEnv r1 v) w ev =
      let le : EnvLe (extendEnv r1 v) (extendEnv rho v)
          le = mkSigma (lerho r1 rho (fst (fst w)) crho (\ i -> snd w (fsuc i)))
                       (mkSigma (snd (fst w)) (mkSigma (snd (fst w)) (LeCode-refl v (snd (fst w)))))
      in mkSigma v (mkSigma (snd w fzero) (EvalRel-mon-env M (extendEnv r1 v) (extendEnv rho v) le u ev))

