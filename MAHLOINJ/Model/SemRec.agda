{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Model/SemRec.agda
--
-- Semantic content of the Nat rules: typing of 0, S, rec, and the two
-- iota equalities, generically.  Typing of rec needs NO induction: the
-- successor step is two applications of the (typed) step function.
------------------------------------------------------------------------

module MAHLOINJ.Model.SemRec where

open import MAHLOINJ.Domain.Basic
  using ( Top ; tt ; Empty ; Pair ; mkSigma ; fst ; snd ; Sigma
        ; Eq ; refl ; Eq-transport ; Eq-sym
        ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl
        ; PairEl ; SigmaCode ; FinFun ; nil ; cons )
open import MAHLOINJ.Domain.Kernel
open import MAHLOINJ.Model.Selection
open import MAHLOINJ.Model.Comb
open import MAHLOINJ.Model.SemLam
open import MAHLOINJ.Model.SemConv using (Incl)

------------------------------------------------------------------------
-- Nat, 0, S
------------------------------------------------------------------------

Atom-typed : (c t : FinEl) -> Coherent c -> FinMem c t -> (PT : Pred) -> PT t -> InvTypP (AtomS c) PT
Atom-typed c t cc fm PT et u e = mkSigma c (mkSigma t (mkSigma (snd e) (mkSigma (mkSigma cc (LeCode-refl c cc))
                                   (mkSigma fm et))))

mem-from-Nat : (x : FinEl) -> AtomS NatCode x -> (y : FinEl) -> FinMem y x -> FinMem y NatCode
mem-from-Nat Bot     e Bot fm = tt
mem-from-Nat NatCode e y   fm = fm

Suc-typed : (P : Pred) -> Ideal P -> InvTypP P (AtomS NatCode) -> InvTypP (SucS P) (AtomS NatCode)
Suc-typed P iP inv u e =
  let v = fst (snd e) ; t = inv v (fst (snd (snd e)))
      v' = fst t ; fv' = mem-from-Nat (fst (snd t)) (snd (snd (snd (snd (snd t))))) v' (fst (snd (snd (snd (snd t)))))
      cv = Ideal.coh iP v (fst (snd (snd e))) ; cv' = FinMem-coh-u v' NatCode fv'
      le = LeCode-trans u (SucEl v) (SucEl v') (fst e) cv cv' (snd (snd (snd e))) (fst (snd (snd t)))
  in mkSigma (SucEl v') (mkSigma NatCode (mkSigma le
       (mkSigma (mkSigma cv' (mkSigma v' (mkSigma (fst (snd (snd (snd t)))) (LeCode-refl v' cv'))))
         (mkSigma (sucNat-from v' fv') (mkSigma tt tt)))))

------------------------------------------------------------------------
-- rec : typing
------------------------------------------------------------------------

module RecTyping (Pz Ps Pk PZ PT : Pred) (Cm : FinEl -> Pred)
  (Cs : FinEl -> Pred) (D : FinEl -> FinEl -> Pred)
  (iz : Ideal Pz) (is : Ideal Ps) (ik : Ideal Pk)
  -- the type of the step:  Pi x:Nat. (C x -> C (S x))
  (okC : BodyOK Cm)
  (okS : BodyOK (\ x -> PiS (Cm x) (LamS (Cm x) (D x))))
  (okD : (x : FinEl) -> Coherent x -> BodyOK (D x))
  (invZ : InvTypP Pz PZ) (fromZ : (g : FinEl) -> PZ g -> Cm ZeroEl g)
  (invS : InvTypP Ps (PiS (AtomS NatCode) (LamS (AtomS NatCode) (\ x -> PiS (Cm x) (LamS (Cm x) (D x))))))
  (fromD : (x y v : FinEl) -> Coherent x -> D x y v -> Cm (SucEl x) v)
  (toT : (w g : FinEl) -> Pk w -> Cm w g -> PT g) (tBot : PT Bot) where

  Bs : FinEl -> Pred
  Bs x = PiS (Cm x) (LamS (Cm x) (D x))

  -- one successor step: typed enlargement of c from the step function
  step : (w r c : FinEl) -> Coherent w -> Coherent r -> NotBot c -> Ps (sing w (sing r c)) ->
    Sigma FinEl (\ c' -> Sigma FinEl (\ g ->
      Pair (LeCode c c') (Pair (AppS (AppS Ps (AtomS w)) (AtomS r) c')
        (Pair (FinMem c' g) (Cm (SucEl w) g)))))
  step w r c cw cr nbc ep =
    let iw = AtomS-ideal w cw ; ir = AtomS-ideal r cr
        inner = AppTyping.App-typed Ps (AtomS w) (AtomS NatCode) Bs (Bs w) is iw okS invS
                  (\ w0 v e0 b -> BodyOK.mon okS w0 w v (fst e0) cw (snd e0) b)
                  (Ideal.bot (BodyOK.ideal okS w cw))
        outer = AppTyping.App-typed (AppS Ps (AtomS w)) (AtomS r) (Cm w) (D w) (Cm (SucEl w))
                  (AppS-ideal _ _ is iw) ir (okD w cw) inner
                  (\ y v e0 dv -> fromD w y v cw dv)
                  (Ideal.bot (BodyOK.ideal okC (SucEl w) cw))
        app : AppS (AppS Ps (AtomS w)) (AtomS r) c
        app = guard-intro c nbc (mkSigma r (mkSigma (mkSigma cr (LeCode-refl r cr))
                (guard-intro (sing r c) tt (mkSigma w (mkSigma (mkSigma cw (LeCode-refl w cw)) ep)))))
        t = outer c app
    in mkSigma (fst t) (mkSigma (fst (snd t)) (snd (snd t)))

  Rec-typed : InvTypP (RecS Pz Ps Pk) PT
  Rec-typed c e = go (bot-or c)
    where
      go : Or (Eq c Bot) (NotBot c) -> TypedP (RecS Pz Ps Pk) PT c
      go (left refl) = TypedP-Bot _ _ tt tBot
      go (right nbc) = byw (fst b) (fst (snd b)) (snd (snd b))
        where
          b = guard-elim c nbc e
          byw : (w : FinEl) -> Pk w -> RecB Pz Ps c w -> TypedP (RecS Pz Ps Pk) PT c
          byw ZeroEl ek eb =
            let t = invZ c eb
                c' = fst t ; nb' = NotBot-from-Le c c' nbc (fst (snd (snd t)))
            in mkSigma c' (mkSigma (fst (snd t)) (mkSigma (fst (snd (snd t)))
                 (mkSigma (guard-intro c' nb' (mkSigma ZeroEl (mkSigma ek (fst (snd (snd (snd t)))))))
                   (mkSigma (fst (snd (snd (snd (snd t)))))
                     (toT ZeroEl (fst (snd t)) ek (fromZ (fst (snd t)) (snd (snd (snd (snd (snd t)))))))))))
          byw (SucEl w') ek eb =
            let r = fst eb ; ep = snd (snd eb)
                cw' = Ideal.coh ik (SucEl w') ek
                cs = Ideal.coh is _ ep
                cr = sing-key-coh r c (sing-val-coh w' (sing r c) cs)
                st = step w' r c cw' cr nbc ep
                c' = fst st ; g = fst (snd st) ; le = fst (snd (snd st))
                app' = fst (snd (snd (snd st))) ; fm = fst (snd (snd (snd (snd st))))
                cg = snd (snd (snd (snd (snd st))))
                nb' = NotBot-from-Le c c' nbc le
                b1 = guard-elim c' nb' app'
                r1 = fst b1 ; le-r1 = snd (fst (snd b1))
                b2 = guard-elim (sing r1 c') tt (snd (snd b1))
                w1 = fst b2 ; le-w1 = snd (fst (snd b2)) ; ep1 = snd (snd b2)
                cs1 = Ideal.coh is _ ep1
                cr1c = sing-val-coh w1 (sing r1 c') cs1
                cr1 = sing-key-coh r1 c' cr1c
                rb : Guard r1 (RecB Pz Ps r1 w')
                rb = guard-build r1 (\ nb1 -> RecProps.down-B Pz Ps iz is r r1 w'
                        (guard-elim r (NotBot-from-Le r1 r nb1 le-r1) (fst (snd eb))) nb1 cr1 le-r1)
                ep' = Ideal.down is (sing w1 (sing r1 c')) (sing w' (sing r1 c')) ep1
                        (sing-coh w' (sing r1 c') cw' cr1c tt) (sing-le-key w1 w' (sing r1 c') cs1 cw' le-w1)
            in mkSigma c' (mkSigma g (mkSigma le
                 (mkSigma (guard-intro c' nb' (mkSigma (SucEl w') (mkSigma ek (mkSigma r1 (mkSigma rb ep')))))
                   (mkSigma fm (toT (SucEl w') g ek cg)))))

------------------------------------------------------------------------
-- rec : iota equalities
------------------------------------------------------------------------

module RecIota (Pz Ps Pk : Pred) (iz : Ideal Pz) (is : Ideal Ps) (ik : Ideal Pk) where

  zero-1 : Incl (RecS Pz Ps (AtomS ZeroEl)) Pz
  zero-1 c e = go (bot-or c)
    where
      go : Or (Eq c Bot) (NotBot c) -> Pz c
      go (left refl) = Ideal.bot iz
      go (right nb) = byw (fst b) (fst (snd b)) (snd (snd b))
        where
          b = guard-elim c nb e
          byw : (w : FinEl) -> AtomS ZeroEl w -> RecB Pz Ps c w -> Pz c
          byw ZeroEl ew eb = eb

  zero-2 : Incl Pz (RecS Pz Ps (AtomS ZeroEl))
  zero-2 c e = guard-build c (\ nb -> mkSigma ZeroEl (mkSigma (mkSigma tt tt) e))

  suc-1 : Incl (RecS Pz Ps (SucS Pk)) (AppS (AppS Ps Pk) (RecS Pz Ps Pk))
  suc-1 c e = guard-build c (\ nb -> let b = guard-elim c nb e in byw (fst b) (fst (snd b)) (snd (snd b)))
    where
      byw : (w : FinEl) -> SucS Pk w -> RecB Pz Ps c w -> AppBody (AppS Ps Pk) (RecS Pz Ps Pk) c
      byw (SucEl w') ew eb =
        let v = fst (snd ew) ; ev = fst (snd (snd ew))
            cw' = fst ew
            ek = Ideal.down ik v w' ev cw' (snd (snd (snd ew)))
            r = fst eb
        in mkSigma r (mkSigma (guard-map r (\ nbr br -> mkSigma w' (mkSigma ek br)) (fst (snd eb)))
             (guard-intro (sing r c) tt (mkSigma w' (mkSigma ek (snd (snd eb))))))

  suc-2 : Incl (AppS (AppS Ps Pk) (RecS Pz Ps Pk)) (RecS Pz Ps (SucS Pk))
  suc-2 c e = guard-build c body
    where
      body : NotBot c -> Sigma FinEl (\ w -> Pair (SucS Pk w) (RecB Pz Ps c w))
      body nb =
        let b = guard-elim c nb e
            r = fst b ; er = fst (snd b)
            b2 = guard-elim (sing r c) tt (snd (snd b))
            w2 = fst b2 ; ek2 = fst (snd b2) ; ep = snd (snd b2)
            cs = Ideal.coh is _ ep
            crc = sing-val-coh w2 (sing r c) cs
            cw2 = Ideal.coh ik w2 ek2
            h = choose r er w2 ek2 (bot-or r)
            w0 = fst h ; ek0 = fst (snd h) ; le20 = fst (snd (snd h)) ; gr = snd (snd (snd h))
            cw0 = Ideal.coh ik w0 ek0
        in mkSigma (SucEl w0)
             (mkSigma (mkSigma cw0 (mkSigma w0 (mkSigma ek0 (LeCode-refl w0 cw0))))
               (mkSigma r (mkSigma gr
                 (Ideal.down is (sing w2 (sing r c)) (sing w0 (sing r c)) ep
                    (sing-coh w0 (sing r c) cw0 crc tt) (sing-le-key w2 w0 (sing r c) cs cw0 le20)))))
        where
          choose : (r : FinEl) -> RecS Pz Ps Pk r -> (w2 : FinEl) -> Pk w2 -> Or (Eq r Bot) (NotBot r) ->
            Sigma FinEl (\ w0 -> Pair (Pk w0) (Pair (LeCode w2 w0) (Guard r (RecB Pz Ps r w0))))
          choose .Bot er w2 ek2 (left refl) =
            mkSigma w2 (mkSigma ek2 (mkSigma (LeCode-refl w2 (Ideal.coh ik w2 ek2)) tt))
          choose r er w2 ek2 (right nbr) =
            let b3 = guard-elim r nbr er
                w3 = fst b3 ; ek3 = fst (snd b3) ; eb3 = snd (snd b3)
                cw2 = Ideal.coh ik w2 ek2 ; cw3 = Ideal.coh ik w3 ek3
                cmp = Ideal.comp ik w2 w3 ek2 ek3
                csup = Coherent-Sup w2 w3 cmp cw2 cw3
            in mkSigma (Sup w2 w3) (mkSigma (Ideal.sup ik w2 w3 ek2 ek3)
                 (mkSigma (LeCode-Sup-left w2 w3 cmp cw2 cw3)
                   (guard-intro r nbr (RecProps.monw Pz Ps iz is r w3 (Sup w2 w3) csup
                      (LeCode-Sup-right w2 w3 cmp cw2 cw3) eb3))))
