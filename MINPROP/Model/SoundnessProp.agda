{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- SoundnessProp.agda  (MINPROP/ — Pi + U + Prop)
--
-- The Prop cases of the soundness theorem (theorem1 / convSound'):
--
--   * InvTyp-Prop-U   : InvTyp M Prop  ->  InvTyp M U          (Prop <= U)
--   * InvConv-Prop    : definitional proof irrelevance is sound:
--                       every approximant of a proof is Bot (prop-collapse),
--                       and Bot approximates every term.
--   * InvTyp-Pi-Prop  : Pi into Prop, from InvTyp-Pi (Pi into U) plus the
--                       observation that the produced Pi code has Prop-code
--                       values (each edge value is typed in Prop).
--
-- NO postulates.
------------------------------------------------------------------------

module MINPROP.Model.SoundnessProp where

import MINPROP.Domain.Basic as S
open S using (Nat ; suc ; Top ; tt ; Empty ; mkSigma ; fst ; snd ; Pair ;
              nil ; cons ; Eq ; refl ; Eq-transport ; Eq-sym ;
              FinEl ; Bot ; UCode ; PropCode ; FunEl ; PiCode ; FinFun)
open import MINPROP.Domain.Kernel using (LeCode ; FinMem ;
  IsProp ; IsPropFun ; IsProp-down ;
  finMem-prop-U ; finMem-prop-isProp ; finMem-prop-mk ; prop-collapse)
open import MINPROP.Model.Selection using (Edge ; EdgeIn ; here ; there)
open import MINPROP.Syntax.Raw using (Expr ; U ; Prop ; Pi)
open import MINPROP.Syntax.Typing using (Ctx ; extend)
open import MINPROP.Model.Eval using (EnvApprox ; extendEnv ; EvalRel ; EvalRel-Bot ; Pi-edgewise)
open import MINPROP.Model.SoundnessLemmas using (Fits ; Typed ; InvTyp ; InvConv ; InvTyp-Pi)

------------------------------------------------------------------------
-- Members of codes below UCode / PropCode.
------------------------------------------------------------------------

memU-to-U : (u a : FinEl) -> FinMem u a -> LeCode a UCode -> FinMem u UCode
memU-to-U u            UCode        fm le = fm
memU-to-U u            PropCode     fm ()
memU-to-U u            (FunEl g)    fm ()
memU-to-U u            (PiCode b f) fm ()
memU-to-U Bot          Bot          fm le = tt
memU-to-U UCode        Bot          ()
memU-to-U PropCode     Bot          ()
memU-to-U (FunEl g)    Bot          ()
memU-to-U (PiCode b f) Bot          ()

memProp-to-U : (u a : FinEl) -> FinMem u a -> LeCode a PropCode -> FinMem u UCode
memProp-to-U u            UCode        fm ()
memProp-to-U u            PropCode     fm le = finMem-prop-U u fm
memProp-to-U u            (FunEl g)    fm ()
memProp-to-U u            (PiCode b f) fm ()
memProp-to-U Bot          Bot          fm le = tt
memProp-to-U UCode        Bot          ()
memProp-to-U PropCode     Bot          ()
memProp-to-U (FunEl g)    Bot          ()
memProp-to-U (PiCode b f) Bot          ()

isProp-below : (u a : FinEl) -> FinMem u a -> LeCode a PropCode -> IsProp u
isProp-below u            UCode        fm ()
isProp-below u            PropCode     fm le = finMem-prop-isProp u fm
isProp-below u            (FunEl g)    fm ()
isProp-below u            (PiCode b f) fm ()
isProp-below Bot          Bot          fm le = tt
isProp-below UCode        Bot          ()
isProp-below PropCode     Bot          ()
isProp-below (FunEl g)    Bot          ()
isProp-below (PiCode b f) Bot          ()

-- Anything typed in Prop has a Prop-code approximant.
typed-isProp : {n : Nat} (M : Expr n) (rho : EnvApprox n) (u : FinEl) ->
  Typed M Prop rho u -> IsProp u
typed-isProp M rho u (mkSigma u' (mkSigma b (mkSigma le (mkSigma evM (mkSigma fm evB))))) =
  IsProp-down u u' le (isProp-below u' b fm (snd evB))

leBot : (u : FinEl) -> LeCode u Bot -> Eq u Bot
leBot Bot          le = refl
leBot UCode        ()
leBot PropCode     ()
leBot (FunEl g)    ()
leBot (PiCode a f) ()

------------------------------------------------------------------------
-- Prop <= U.
------------------------------------------------------------------------

InvTyp-Prop-U : {n : Nat} {G : Ctx n} {M : Expr n} {rho : EnvApprox n} ->
  InvTyp G M Prop rho -> InvTyp G M U rho
InvTyp-Prop-U inv u ev =
  let mkSigma u' (mkSigma a' (mkSigma le (mkSigma evM (mkSigma fm evA)))) = inv u ev
  in mkSigma u' (mkSigma UCode
       (mkSigma le (mkSigma evM (mkSigma (memProp-to-U u' a' fm (snd evA)) (mkSigma tt tt)))))

------------------------------------------------------------------------
-- Proof irrelevance.
------------------------------------------------------------------------

-- Every approximant of a proof is Bot.
proof-Bot : {n : Nat} {G : Ctx n} {M A : Expr n} {rho : EnvApprox n} ->
  InvTyp G M A rho -> InvTyp G A Prop rho ->
  (u : FinEl) -> EvalRel M rho u -> Eq u Bot
proof-Bot {A = A} {rho = rho} invM invA u ev =
  let mkSigma u' (mkSigma a' (mkSigma le (mkSigma evM (mkSigma fm evA)))) = invM u ev
      u'Bot = prop-collapse u' a' fm (typed-isProp A rho a' (invA a' evA))
  in leBot u (Eq-transport (LeCode u) u'Bot le)

InvConv-Prop : {n : Nat} {G : Ctx n} {M N A : Expr n} {rho : EnvApprox n} ->
  InvTyp G A Prop rho -> InvTyp G M A rho -> InvTyp G N A rho ->
  InvConv G M N A rho
InvConv-Prop {G = G} {M = M} {N = N} {A = A} {rho = rho} invA invM invN =
  mkSigma invM (mkSigma invN
    (mkSigma (\ u ev -> Eq-transport (EvalRel N rho) (Eq-sym (proof-Bot {G = G} {M = M} {A = A} invM invA u ev)) (EvalRel-Bot N rho))
             (\ u ev -> Eq-transport (EvalRel M rho) (Eq-sym (proof-Bot {G = G} {M = N} {A = A} invN invA u ev)) (EvalRel-Bot M rho))))

------------------------------------------------------------------------
-- Pi into Prop.
------------------------------------------------------------------------

private
  edges-isProp : (f : FinFun) -> ((p : Edge) -> EdgeIn p f -> IsProp (snd p)) -> IsPropFun f
  edges-isProp nil         h = tt
  edges-isProp (cons p ps) h = mkSigma (h p here) (edges-isProp ps (\ q qin -> h q (there qin)))

isProp-Pi : {n : Nat} {G : Ctx n} (A : Expr n) (B : Expr (suc n)) (rho : EnvApprox n) ->
  ((x a : FinEl) -> FinMem x a -> EvalRel A rho a ->
    InvTyp (extend G A) B Prop (extendEnv rho x)) ->
  (u : FinEl) -> EvalRel (Pi A B) rho u -> IsProp u
isProp-Pi A B rho bodyP Bot          ev = tt
isProp-Pi A B rho bodyP UCode        ()
isProp-Pi A B rho bodyP PropCode     ()
isProp-Pi A B rho bodyP (FunEl g)    ()
isProp-Pi A B rho bodyP (PiCode b f) ev =
  let pew  = Pi-edgewise A B rho b f ev
      a''  = fst (snd (snd pew))
      evA'' = fst (snd (snd (snd pew)))
      ew   = snd (snd (snd (snd pew)))
  in edges-isProp f (\ p ein ->
       let w = ew p ein
           x = fst w
       in typed-isProp B (extendEnv rho x) (snd p)
            (bodyP x a'' (fst (snd (snd w))) evA'' (snd p) (snd (snd (snd w)))))

InvTyp-Pi-Prop : {n : Nat} {G : Ctx n} (A : Expr n) (B : Expr (suc n)) ->
  (rho : EnvApprox n) -> Fits G rho ->
  InvTyp G A U rho ->
  ((x a : FinEl) -> FinMem x a -> EvalRel A rho a ->
    InvTyp (extend G A) B Prop (extendEnv rho x)) ->
  InvTyp G (Pi A B) Prop rho
InvTyp-Pi-Prop {G = G} A B rho fits invA bodyP u ev =
  let mkSigma u' (mkSigma a' (mkSigma le (mkSigma evPi (mkSigma fm evU)))) =
        InvTyp-Pi A B rho fits invA (\ x a fmx evA -> InvTyp-Prop-U {G = extend G A} {M = B} (bodyP x a fmx evA)) u ev
      u'U = memU-to-U u' a' fm (snd evU)
  in mkSigma u' (mkSigma PropCode
       (mkSigma le (mkSigma evPi
         (mkSigma (finMem-prop-mk u' u'U (isProp-Pi {G = G} A B rho bodyP u' evPi)) (mkSigma tt tt)))))
