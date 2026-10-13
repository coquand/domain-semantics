{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLO/EndExt.agda
--
-- End-extension of candidates and Lemmas 8, 12, 13 of mahlo-plan.tex:
-- transfer of families, extended predicativity, monotonicity of Gamma.
------------------------------------------------------------------------

open import MAHLO.Basic
open import MAHLO.TermModel

module MAHLO.EndExt (TM : TermModel) where

open TermModel TM
open import MAHLO.Candidate TM
open import MAHLO.Pre TM
open import MAHLO.Congruence TM
open import MAHLO.Gamma TM

record _<<_ (X Y : Cand) : Set where
  field
    inc : Cand.R X <= Cand.R Y
    end : {a b : D} -> Cand.R X a a -> Cand.R Y a b -> Cand.R X a b
    int : (a : D) -> Cand.R X a a -> Cand.I X a ~ Cand.I Y a

module _ (X Y : Cand) (E : X << Y) where
  open _<<_ E
  private
    module X = Cand X
    module Y = Cand Y
    module RX = IsPER X.R-per
    module RY = IsPER Y.R-per

  ----------------------------------------------------------------------
  -- Lemma 12 (1): pre(f,g,X) is included in pre(f,g,Y)
  ----------------------------------------------------------------------

  pre-inc : {f g a : D} -> Pre X f g a -> Pre Y f g a
  pre-inc (pre-ne a n) = pre-ne a n
  pre-inc (pre-nat a e) = pre-nat a e
  pre-inc (pre-sat a b p r) = pre-sat a b (pre-inc p) (inc r)
  pre-inc (pre-pi a A F e p r h q) =
    pre-pi a A F e (pre-inc p)
      (\ v v' i -> inc (r v v' (snd (int A (Pre-car X p)) i)))
      (\ v i -> pre-inc (h v (snd (int A (Pre-car X p)) i)))
      (inc q)
  pre-inc (pre-sig a A F e p r h q) =
    pre-sig a A F e (pre-inc p)
      (\ v v' i -> inc (r v v' (snd (int A (Pre-car X p)) i)))
      (\ v i -> pre-inc (h v (snd (int A (Pre-car X p)) i)))
      (inc q)
  pre-inc (pre-f a A F e p r h q) =
    pre-f a A F e (pre-inc p)
      (\ v v' i -> inc (r v v' (snd (int A (Pre-car X p)) i)))
      (\ v i -> pre-inc (h v (snd (int A (Pre-car X p)) i)))
      (inc q)
  pre-inc (pre-g a A F c e p r h rf i q) =
    pre-g a A F c e (pre-inc p)
      (\ v v' j -> inc (r v v' (snd (int A (Pre-car X p)) j)))
      (\ v j -> pre-inc (h v (snd (int A (Pre-car X p)) j)))
      (inc rf) (fst (int _ rf) i) (inc q)

  ----------------------------------------------------------------------
  -- Lemma 8 (transfer of families) in the form used below
  ----------------------------------------------------------------------

  respX : {A F : D} {P : D -> Set} -> X.R A A ->
          ((a : D) -> P a -> X.R a a) ->
          FamResp Y A F -> FamIn X P A F -> FamResp X A F
  respX {A} {F} rAA car rY hX v v' i =
    end (car _ (hX v (IsPER.rl (X.I-per A rAA) i)))
        (rY v v' (fst (int A rAA) i))

  ----------------------------------------------------------------------
  -- Lemma 12 (2): with Indep, pre(f,g,Y) is included in pre(f,g,X)
  ----------------------------------------------------------------------

  module _ {f g : D} (ind : Indep X f g) where

    pre-dec : {a : D} -> Pre Y f g a -> Pre X f g a
    pre-dec (pre-ne a n) = pre-ne a n
    pre-dec (pre-nat a e) = pre-nat a e
    pre-dec (pre-sat a b p r) =
      pre-sat a b (pre-dec p) (end (Pre-car X (pre-dec p)) r)
    pre-dec (pre-pi a A F e p r h q) =
      pre-pi a A F e pA rX hX
        (CandCl.R-self X (fst (fst (ind A F pA rX hX))) (~~-sym e))
      where
        pA = pre-dec p
        rAA = Pre-car X pA
        hX : FamIn X (Pre X f g) A F
        hX v i = pre-dec (h v (fst (int A rAA) i))
        rX : FamResp X A F
        rX = respX rAA (\ a p -> Pre-car X p) r hX
    pre-dec (pre-sig a A F e p r h q) =
      pre-sig a A F e pA rX hX
        (CandCl.R-self X (snd (fst (ind A F pA rX hX))) (~~-sym e))
      where
        pA = pre-dec p
        rAA = Pre-car X pA
        hX : FamIn X (Pre X f g) A F
        hX v i = pre-dec (h v (fst (int A rAA) i))
        rX : FamResp X A F
        rX = respX rAA (\ a p -> Pre-car X p) r hX
    pre-dec (pre-f a A F e p r h q) =
      pre-f a A F e pA rX hX
        (CandCl.R-self X (fst (snd (ind A F pA rX hX))) (~~-sym e))
      where
        pA = pre-dec p
        rAA = Pre-car X pA
        hX : FamIn X (Pre X f g) A F
        hX v i = pre-dec (h v (fst (int A rAA) i))
        rX : FamResp X A F
        rX = respX rAA (\ a p -> Pre-car X p) r hX
    pre-dec (pre-g a A F c e p r h rf i q) =
      pre-g a A F c e pA rX hX Rff ic
        (CandCl.R-self X (snd (snd (ind A F pA rX hX)) c ic) (~~-sym e))
      where
        pA = pre-dec p
        rAA = Pre-car X pA
        hX : FamIn X (Pre X f g) A F
        hX v j = pre-dec (h v (fst (int A rAA) j))
        rX : FamResp X A F
        rX = respX rAA (\ a p -> Pre-car X p) r hX
        Rff = fst (snd (ind A F pA rX hX))
        ic = snd (int (FA f A F) Rff) i

    pre-eq : Pre X f g <=> Pre Y f g
    pre-eq = (\ a p -> pre-inc p) , (\ a p -> pre-dec p)

    indep-up : Indep Y f g
    indep-up A F pY rY hY =
      (inc (fst (fst o)) , inc (snd (fst o))) , (inc (fst (snd o)) ,
        (\ c i -> inc (snd (snd o) c (snd (int (FA f A F) (fst (snd o))) i))))
      where
        pA = pre-dec pY
        rAA = Pre-car X pA
        hX : FamIn X (Pre X f g) A F
        hX v i = pre-dec (hY v (fst (int A rAA) i))
        rX = respX rAA (\ a p -> Pre-car X p) rY hX
        o = ind A F pA rX hX

    op-up : {f' g' : D} -> Op X (Pre X f g) f g f' g' -> Op Y (Pre Y f g) f g f' g'
    op-up op A A' F F' rY pA pA' eY hF hF' =
      inc (fst o) , (\ c c' i -> inc (snd o c c' (snd (int _ (RX.rl (fst o))) i)))
      where
        pAx = pre-dec pA
        pA'x = pre-dec pA'
        rAA = Pre-car X pAx
        rX = end rAA rY
        hFx : FamIn X (Pre X f g) A F
        hFx v i = pre-dec (hF v (fst (int A rAA) i))
        hF'x : FamIn X (Pre X f g) A F'
        hF'x v i = pre-dec (hF' v (fst (int A rAA) i))
        eX : FamEq X A F F'
        eX v v' i =
          end (Pre-car X (hFx v (IsPER.rl (X.I-per A rAA) i)))
              (eY v v' (fst (int A rAA) i))
        o = op A A' F F' rX pAx pA'x eX hFx hF'x

    op-down : {f' g' : D} -> Op Y (Pre Y f g) f g f' g' -> Op X (Pre X f g) f g f' g'
    op-down op A A' F F' rX pA pA' eX hF hF' =
      end Rff (fst o) ,
      (\ c c' i ->
         end (snd (snd ix) c (IsPER.rl (X.I-per _ Rff) i))
             (snd o c c' (fst (int _ Rff) i)))
      where
        rAA = RX.rl rX
        eY : FamEq Y A F F'
        eY v v' i = inc (eX v v' (snd (int A rAA) i))
        hFy : FamIn Y (Pre Y f g) A F
        hFy v i = pre-inc (hF v (snd (int A rAA) i))
        hF'y : FamIn Y (Pre Y f g) A F'
        hF'y v i = pre-inc (hF' v (snd (int A rAA) i))
        o = op A A' F F' (inc rX) (pre-inc pA) (pre-inc pA') eY hFy hF'y
        ix = ind A F pA (FamEq-l X rAA eX) hF
        Rff = fst (snd ix)

  ----------------------------------------------------------------------
  -- Lemma 13: monotonicity of Gamma
  ----------------------------------------------------------------------

  private
    Res-change : {P Q : D -> Set} -> P <=> Q -> ((a : D) -> P a -> X.R a a) ->
                 Res X P ~ Res Y Q
    Res-change (h , k) car =
      (\ { (r , (p , p')) -> inc r , (h _ p , h _ p') }) ,
      (\ { (r , (q , q')) -> end (car _ (k _ q)) r , (k _ q , k _ q') })

  mono-inc : Cand.R (Gam X) <= Cand.R (Gam Y)
  mono-inc (gne n) = gne n
  mono-inc (gnat e1 e2) = gnat e1 e2
  mono-inc (gpi (mkPi A A' F F' ea eb rA rF)) =
    gpi (mkPi A A' F F' ea eb (inc rA)
          (\ v v' i -> inc (rF v v' (snd (int A (RX.rl rA)) i))))
  mono-inc (gsig (mkSig A A' F F' ea eb rA rF)) =
    gsig (mkSig A A' F F' ea eb (inc rA)
          (\ v v' i -> inc (rF v v' (snd (int A (RX.rl rA)) i))))
  mono-inc (gU (mkU f g f' g' ea eb ind ind' op)) =
    gU (mkU f g f' g' ea eb (indep-up ind) (indep-up ind') (op-up ind op))

  mono-int : (a : D) -> Cand.R (Gam X) a a -> Cand.I (Gam X) a ~ Cand.I (Gam Y) a
  mono-int a (gne n) = ~-trans (GI-ne X a n) (~-sym (GI-ne Y a n))
  mono-int a (gnat e _) = ~-trans (GI-nat X a e) (~-sym (GI-nat Y a e))
  mono-int a (gpi p) =
    ~-trans (GI-pi X a A F (PiRel.ea p))
      (~-trans (Fun-cong (X.I A) (Y.I A) (\ w -> X.I (app F w)) (\ w -> Y.I (app F w))
                 (X.I-per A rAA) (int A rAA)
                 (\ v i -> int (app F v) (piResp X p v v i)))
               (~-sym (GI-pi Y a A F (PiRel.ea p))))
    where
      A = PiRel.A p
      F = PiRel.F p
      rAA = RX.rl (PiRel.rA p)
  mono-int a (gsig p) =
    ~-trans (GI-sig X a A F (SigRel.ea p))
      (~-trans (SigF-cong (X.I A) (Y.I A) (\ w -> X.I (app F w)) (\ w -> Y.I (app F w))
                 (X.I-per A rAA) (int A rAA)
                 (\ v i -> int (app F v) (sigResp X p v v i)))
               (~-sym (GI-sig Y a A F (SigRel.ea p))))
    where
      A = SigRel.A p
      F = SigRel.F p
      rAA = RX.rl (SigRel.rA p)
  mono-int a (gU u) =
    ~-trans (GI-U X a f g (URel.ea u))
      (~-trans (Res-change (pre-eq (URel.ind u)) (\ b p -> Pre-car X p))
               (~-sym (GI-U Y a f g (URel.ea u))))
    where
      f = URel.f u
      g = URel.g u

  private
    ne-pi : {a A F : D} -> N a a -> a ~~ Pi A F -> Empty
    ne-pi n e = ne-Pi (N-self e n)
    ne-sig : {a A F : D} -> N a a -> a ~~ Sig A F -> Empty
    ne-sig n e = ne-Sig (N-self e n)
    ne-u : {a f g : D} -> N a a -> a ~~ U f g -> Empty
    ne-u n e = ne-U (N-self e n)

  mono-end : {a b : D} -> Cand.R (Gam X) a a -> Cand.R (Gam Y) a b ->
             Cand.R (Gam X) a b
  mono-end s (gne m) = gne m
  mono-end s (gnat e1 e2) = gnat e1 e2
  -- Pi case
  mono-end (gne n) (gpi p) = Empty-elim (ne-pi n (PiRel.ea p))
  mono-end (gnat e _) (gpi p) =
    Empty-elim (Pi-Nat (~~-trans (~~-sym (PiRel.ea p)) e))
  mono-end (gU u) (gpi p) =
    Empty-elim (Pi-U (~~-trans (~~-sym (PiRel.ea p)) (URel.ea u)))
  mono-end (gsig q) (gpi p) =
    Empty-elim (Sig-Pi (~~-trans (~~-sym (SigRel.ea q)) (PiRel.ea p)))
  mono-end (gpi (mkPi A A2 F F2 ea _ rA rF)) (gpi (mkPi B B' G G' ea' eb' rB rG)) =
    gpi (mkPi B B' G G' ea' eb' (end rBB rB) rGX)
    where
      ij = Pi-inj (~~-trans (~~-sym ea) ea')
      rBB : Cand.R X B B
      rBB = CandCl.R-self X (RX.rl rA) (fst ij)
      respG : FamResp X B G
      respG = FamEq-tr X (fst ij) (snd ij) (snd ij) (FamEq-l X (RX.rl rA) rF)
      rGX : FamEq X B G G'
      rGX v v' i =
        end (respG v v (IsPER.rl (X.I-per B rBB) i)) (rG v v' (fst (int B rBB) i))
  -- Sigma case
  mono-end (gne n) (gsig p) = Empty-elim (ne-sig n (SigRel.ea p))
  mono-end (gnat e _) (gsig p) =
    Empty-elim (Sig-Nat (~~-trans (~~-sym (SigRel.ea p)) e))
  mono-end (gU u) (gsig p) =
    Empty-elim (Sig-U (~~-trans (~~-sym (SigRel.ea p)) (URel.ea u)))
  mono-end (gpi q) (gsig p) =
    Empty-elim (Sig-Pi (~~-trans (~~-sym (SigRel.ea p)) (PiRel.ea q)))
  mono-end (gsig (mkSig A A2 F F2 ea _ rA rF)) (gsig (mkSig B B' G G' ea' eb' rB rG)) =
    gsig (mkSig B B' G G' ea' eb' (end rBB rB) rGX)
    where
      ij = Sig-inj (~~-trans (~~-sym ea) ea')
      rBB : Cand.R X B B
      rBB = CandCl.R-self X (RX.rl rA) (fst ij)
      respG : FamResp X B G
      respG = FamEq-tr X (fst ij) (snd ij) (snd ij) (FamEq-l X (RX.rl rA) rF)
      rGX : FamEq X B G G'
      rGX v v' i =
        end (respG v v (IsPER.rl (X.I-per B rBB) i)) (rG v v' (fst (int B rBB) i))
  -- U case
  mono-end (gne n) (gU u) = Empty-elim (ne-u n (URel.ea u))
  mono-end (gnat e _) (gU u) =
    Empty-elim (Nat-U (~~-trans (~~-sym e) (URel.ea u)))
  mono-end (gpi p) (gU u) =
    Empty-elim (Pi-U (~~-trans (~~-sym (PiRel.ea p)) (URel.ea u)))
  mono-end (gsig p) (gU u) =
    Empty-elim (Sig-U (~~-trans (~~-sym (SigRel.ea p)) (URel.ea u)))
  mono-end (gU (mkU f g f2 g2 ea _ ind _ _))
           (gU (mkU h k h' k' ea' eb' indY indY' opY)) =
    gU (mkU h k h' k' ea' eb' indX indX' opX)
    where
      ij = U-inj (~~-trans (~~-sym ea) ea')
      indX : Indep X h k
      indX = Indep-cong X (fst ij) (snd ij) ind
      opX : Op X (Pre X h k) h k h' k'
      opX = op-down indX opY
      toP : {a : D} -> Pre X h' k' a -> Pre X h k a
      toP p = pre-dec indX (cong-sub Y indY opY (pre-inc p))
      indX' : Indep X h' k'
      indX' A F pA rA hF =
        fst (indX A F pAP rA hFP) ,
        (IsPER.rr X.R-per (fst o) ,
         (\ c i ->
            IsPER.rr X.R-per
              (snd o c c (snd (X.I-resp (fst o)) i))))
        where
          pAP = toP pA
          hFP : FamIn X (Pre X h k) A F
          hFP v i = toP (hF v i)
          o = opX A A F F (Pre-car X pAP) pAP pAP rA hFP hFP

  mono : Gam X << Gam Y
  mono = record { inc = mono-inc ; end = mono-end ; int = mono-int }
