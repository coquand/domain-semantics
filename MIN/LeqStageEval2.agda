{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- LeqStageEval2.agda  (MIN/ — Pi + U fragment)
--
-- The remaining structural pieces of the re-founded order layer:
--   * leFinEl        := leiC  (the finished stage decision; the cone uses
--                       it only as the firing number + leFinEl-sound,
--                       never via its old structural reduction)
--   * leFinEl-sound  : isPos (leFinEl u v) -> LeCode u v
--   * comp-EvalFun   : Comp of two EvalFun values (helper)
--   * EvalFun-append-eq : EvalFun (append k h) = Sup (EvalFun k) (EvalFun h)
--
-- comp-EvalFun / EvalFun-append-eq fire on leiC (the new EvalFun's
-- decision) and use the EvalFun-step shape, via LeqC-to-LeCode . leiC-sound.
--
-- NO TERMINATING, NO postulates.
------------------------------------------------------------------------

module MIN.LeqStageEval2 where

open import MIN.Basic
  using ( Top ; tt ; Empty
        ; Nat ; zero ; suc ; isPos
        ; Eq ; refl ; Eq-sym ; Eq-cong ; Eq-transport
        ; Pair ; mkSigma ; fst ; snd
        ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ; nil ; cons )
open import MIN.LeqStage
  using ( Sup ; append ; leiC
        ; Comp ; CompFun ; CompStepFun ; CompStepStep
        ; Coherent ; CoherentFunTail ; CFTcons ; CoherentWith )
open import MIN.LeqStageComp
  using ( comp-Bot-l ; comp-Sup-sym ; Sup-assoc ; coherentWith-to-compStepFun
        ; compStepFun-to-coherentWith )
open import MIN.LeqStageStable using ( leiC-sound )
open import MIN.LeqStageBridge
  using ( EvalFun ; EvalFun-step ; LeCode ; LeFunCode ; LeqC-to-LeCode )
open import MIN.LeqStageInterface using ( Comp-value-EvalFun )

------------------------------------------------------------------------
-- leFinEl := leiC  + soundness
------------------------------------------------------------------------

leFinEl : FinEl -> FinEl -> Nat
leFinEl = leiC

leFinEl-sound : (u v : FinEl) -> isPos (leFinEl u v) -> LeCode u v
leFinEl-sound u v p = LeqC-to-LeCode u v (leiC-sound u v p)

------------------------------------------------------------------------
-- comp-EvalFun  (fires on leiC, EvalFun-step shape)
------------------------------------------------------------------------

mutual
  comp-EvalFun : (k h : FinFun) (xi : FinEl) ->
    CompFun k h -> CoherentFunTail k -> Coherent xi ->
    Comp (EvalFun k xi) (EvalFun h xi)
  comp-EvalFun nil          h xi ckh cohk cxi = comp-Bot-l (EvalFun h xi)
  comp-EvalFun (cons q rest) h xi ckh cohk cxi =
    comp-EvalFun-step (leiC (fst q) xi) q rest h xi refl
      (fst ckh) (snd ckh) cohk cxi

  comp-EvalFun-step : (w : Nat) (q : Pair FinEl FinEl) (rest h : FinFun) (xi : FinEl) ->
    Eq w (leiC (fst q) xi) ->
    CompStepFun q h -> CompFun rest h ->
    CoherentFunTail (cons q rest) -> Coherent xi ->
    Comp (EvalFun-step w (snd q) rest xi) (EvalFun h xi)
  comp-EvalFun-step zero    q rest h xi eq csf crf cohk cxi =
    comp-EvalFun rest h xi crf (CFTcons.tail-coh cohk) cxi
  comp-EvalFun-step (suc w) q rest h xi eq csf crf cohk cxi =
    let comp1 = Comp-value-EvalFun q h xi
                  (LeqC-to-LeCode (fst q) xi (leiC-sound (fst q) xi (Eq-transport isPos eq tt)))
                  cxi (CFTcons.val-coh cohk)
                  (compStepFun-to-coherentWith q h csf) csf
        comp2 = comp-EvalFun rest h xi crf (CFTcons.tail-coh cohk) cxi
    in comp-Sup-sym (snd q) (EvalFun rest xi) (EvalFun h xi) comp1 comp2

------------------------------------------------------------------------
-- EvalFun-append-eq  (fires on leiC, EvalFun-step shape)
------------------------------------------------------------------------

mutual
  EvalFun-append-eq : (k h : FinFun) (xi : FinEl) ->
    CompFun k h -> CoherentFunTail k -> Coherent xi ->
    Eq (EvalFun (append k h) xi) (Sup (EvalFun k xi) (EvalFun h xi))
  EvalFun-append-eq nil          h xi ckh cohk cxi = refl
  EvalFun-append-eq (cons q rest) h xi ckh cohk cxi =
    EvalFun-append-eq-step (leiC (fst q) xi) q rest h xi refl
      (fst ckh) (snd ckh) cohk cxi

  EvalFun-append-eq-step : (w : Nat) (q : Pair FinEl FinEl) (rest h : FinFun) (xi : FinEl) ->
    Eq w (leiC (fst q) xi) ->
    CompStepFun q h -> CompFun rest h ->
    CoherentFunTail (cons q rest) -> Coherent xi ->
    Eq (EvalFun-step w (snd q) (append rest h) xi)
       (Sup (EvalFun-step w (snd q) rest xi) (EvalFun h xi))
  EvalFun-append-eq-step zero    q rest h xi eq csf crf cohk cxi =
    EvalFun-append-eq rest h xi crf (CFTcons.tail-coh cohk) cxi
  EvalFun-append-eq-step (suc w) q rest h xi eq csf crf cohk cxi =
    let ih = EvalFun-append-eq rest h xi crf (CFTcons.tail-coh cohk) cxi
        step1 : Eq (Sup (snd q) (EvalFun (append rest h) xi))
                   (Sup (snd q) (Sup (EvalFun rest xi) (EvalFun h xi)))
        step1 = Eq-cong (Sup (snd q)) ih
        le-q  = LeqC-to-LeCode (fst q) xi (leiC-sound (fst q) xi (Eq-transport isPos eq tt))
        comp-qr = Comp-value-EvalFun q rest xi le-q cxi (CFTcons.val-coh cohk)
                    (CFTcons.compat cohk)
                    (coherentWith-to-compStepFun q rest (CFTcons.compat cohk))
        comp-rh = comp-EvalFun rest h xi crf (CFTcons.tail-coh cohk) cxi
        step2 : Eq (Sup (Sup (snd q) (EvalFun rest xi)) (EvalFun h xi))
                   (Sup (snd q) (Sup (EvalFun rest xi) (EvalFun h xi)))
        step2 = Sup-assoc (snd q) (EvalFun rest xi) (EvalFun h xi) comp-qr comp-rh
    in Eq-transport
         (\ z -> Eq (Sup (snd q) (EvalFun (append rest h) xi)) z)
         (Eq-sym step2) step1
