{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLO/Gamma.agda
--
-- The operator Gamma (mahlo-plan.tex, Definition 7) and Lemma 11:
-- Gamma maps candidates to candidates.
------------------------------------------------------------------------

open import MAHLO.Basic
open import MAHLO.TermModel

module MAHLO.Gamma (TM : TermModel) where

open TermModel TM
open import MAHLO.Candidate TM
open import MAHLO.Pre TM
open import MAHLO.Congruence TM

module _ (X : Cand) where
  open Cand X

  -- the Pi-clause
  record PiRel (a b : D) : Set where
    constructor mkPi
    field
      A A' F F' : D
      ea : a ~~ Pi A F
      eb : b ~~ Pi A' F'
      rA : R A A'
      rF : FamEq X A F F'

  -- the Sigma-clause
  record SigRel (a b : D) : Set where
    constructor mkSig
    field
      A A' F F' : D
      ea : a ~~ Sig A F
      eb : b ~~ Sig A' F'
      rA : R A A'
      rF : FamEq X A F F'

  -- the U-clause
  record URel (a b : D) : Set where
    constructor mkU
    field
      f g f' g' : D
      ea   : a ~~ U f g
      eb   : b ~~ U f' g'
      ind  : Indep X f g
      ind' : Indep X f' g'
      op   : Op X (Pre X f g) f g f' g'

  -- the relation of Gamma(X)
  data GR (a b : D) : Set where
    gne  : N a b -> GR a b
    gnat : a ~~ Nat -> b ~~ Nat -> GR a b
    gpi  : PiRel a b -> GR a b
    gsig : SigRel a b -> GR a b
    gU   : URel a b -> GR a b

  -- the interpretation of Gamma(X)
  data GI (a v v' : D) : Set where
    ine  : N a a -> S v v' -> GI a v v'
    inat : a ~~ Nat -> NatR v v' -> GI a v v'
    ipi  : (A F : D) -> a ~~ Pi A F ->
           Fun (I A) (\ w -> I (app F w)) v v' -> GI a v v'
    isig : (A F : D) -> a ~~ Sig A F ->
           SigF (I A) (\ w -> I (app F w)) v v' -> GI a v v'
    iU   : (f g : D) -> a ~~ U f g -> Res X (Pre X f g) v v' -> GI a v v'

module _ (X : Cand) where
  open Cand X
  private
    module R' = IsPER R-per

  ----------------------------------------------------------------------
  -- shapes of the interpretation
  ----------------------------------------------------------------------

  GI-ne : (n : D) -> N n n -> GI X n ~ S
  GI-ne n nn = to , ine nn
    where
      to : GI X n <= S
      to (ine _ s) = s
      to (inat e _) = Empty-elim (ne-Nat (N-self e nn))
      to (ipi A F e _) = Empty-elim (ne-Pi (N-self e nn))
      to (isig A F e _) = Empty-elim (ne-Sig (N-self e nn))
      to (iU f g e _) = Empty-elim (ne-U (N-self e nn))

  GI-nat : (a : D) -> a ~~ Nat -> GI X a ~ NatR
  GI-nat a ea = to , inat ea
    where
      to : GI X a <= NatR
      to (ine n _) = Empty-elim (ne-Nat (N-self ea n))
      to (inat _ r) = r
      to (ipi A F e _) = Empty-elim (Pi-Nat (~~-trans (~~-sym e) ea))
      to (isig A F e _) = Empty-elim (Sig-Nat (~~-trans (~~-sym e) ea))
      to (iU f g e _) = Empty-elim (Nat-U (~~-trans (~~-sym ea) e))

  GI-pi : (a A F : D) -> a ~~ Pi A F -> GI X a ~ Fun (I A) (\ w -> I (app F w))
  GI-pi a A F ea = to , ipi A F ea
    where
      to : GI X a <= Fun (I A) (\ w -> I (app F w))
      to (ine n _) = Empty-elim (ne-Pi (N-self ea n))
      to (inat e _) = Empty-elim (Pi-Nat (~~-trans (~~-sym ea) e))
      to {v} {v'} (ipi A2 F2 e h) =
        let ij = Pi-inj (~~-trans (~~-sym e) ea) in
        fst (Fun-~ {I A2} {I A} {\ w -> I (app F2 w)} {\ w -> I (app F w)} (I-idx (fst ij)) (\ w -> I-idx (app-cong (snd ij) ~~-refl))) h
      to (isig A2 F2 e _) = Empty-elim (Sig-Pi (~~-trans (~~-sym e) ea))
      to (iU f g e _) = Empty-elim (Pi-U (~~-trans (~~-sym ea) e))

  GI-sig : (a A F : D) -> a ~~ Sig A F -> GI X a ~ SigF (I A) (\ w -> I (app F w))
  GI-sig a A F ea = to , isig A F ea
    where
      to : GI X a <= SigF (I A) (\ w -> I (app F w))
      to (ine n _) = Empty-elim (ne-Sig (N-self ea n))
      to (inat e _) = Empty-elim (Sig-Nat (~~-trans (~~-sym ea) e))
      to (ipi A2 F2 e _) = Empty-elim (Sig-Pi (~~-trans (~~-sym ea) e))
      to {v} {v'} (isig A2 F2 e h) =
        let ij = Sig-inj (~~-trans (~~-sym e) ea) in
        fst (SigF-~ {I A2} {I A} {\ w -> I (app F2 w)} {\ w -> I (app F w)} (I-idx (fst ij)) (\ w -> I-idx (app-cong (snd ij) ~~-refl))) h
      to (iU f g e _) = Empty-elim (Sig-U (~~-trans (~~-sym ea) e))

  GI-U : (a f g : D) -> a ~~ U f g -> GI X a ~ Res X (Pre X f g)
  GI-U a f g ea = to , iU f g ea
    where
      to : GI X a <= Res X (Pre X f g)
      to (ine n _) = Empty-elim (ne-U (N-self ea n))
      to (inat e _) = Empty-elim (Nat-U (~~-trans (~~-sym e) ea))
      to (ipi A F e _) = Empty-elim (Pi-U (~~-trans (~~-sym e) ea))
      to (isig A F e _) = Empty-elim (Sig-U (~~-trans (~~-sym e) ea))
      to {v} {v'} (iU f2 g2 e h) =
        let ij = U-inj (~~-trans (~~-sym e) ea) in
        fst h , (Pre-cong X (fst ij) (snd ij) (fst (snd h)) ,
                 Pre-cong X (fst ij) (snd ij) (snd (snd h)))

  ----------------------------------------------------------------------
  -- auxiliary facts
  ----------------------------------------------------------------------

  Res-per : (P : D -> Set) -> IsPER (Res X P)
  Res-per P = record
    { sy = \ { (r , (p , p')) -> R'.sy r , (p' , p) }
    ; tr = \ { (r , (p , _)) (r' , (_ , p'')) -> R'.tr r r' , (p , p'') } }

  Res-cong : {P Q : D -> Set} -> P <=> Q -> Res X P ~ Res X Q
  Res-cong (h , k) =
    (\ { (r , (p , p')) -> r , (h _ p , h _ p') }) ,
    (\ { (r , (q , q')) -> r , (k _ q , k _ q') })

  -- data of a family over A, for Fun-per / Fun-lo / Fun-hi
  famResp~ : {A F : D} -> FamResp X A F ->
             {v v' : D} -> I A v v' -> I (app F v) ~ I (app F v')
  famResp~ r {v} {v'} i = I-resp (r v v' i)

  famPer : {A F : D} -> FamResp X A F ->
           (v : D) -> I A v v -> IsPER (I (app F v))
  famPer r v i = I-per _ (r v v i)

  -- Pi-pairs: from a PiRel get the respect of the left family
  piResp : {a b : D} (p : PiRel X a b) -> FamResp X (PiRel.A p) (PiRel.F p)
  piResp p = FamEq-l X (R'.rl (PiRel.rA p)) (PiRel.rF p)

  sigResp : {a b : D} (p : SigRel X a b) -> FamResp X (SigRel.A p) (SigRel.F p)
  sigResp p = FamEq-l X (R'.rl (SigRel.rA p)) (SigRel.rF p)

  ----------------------------------------------------------------------
  -- Gamma(X) is a PER
  ----------------------------------------------------------------------

  GR-sym : {a b : D} -> GR X a b -> GR X b a
  GR-sym (gne n) = gne (N-sym n)
  GR-sym (gnat e1 e2) = gnat e2 e1
  GR-sym (gpi (mkPi A A' F F' ea eb rA rF)) =
    gpi (mkPi A' A F' F eb ea (R'.sy rA) rF')
    where
      rF' : FamEq X A' F' F
      rF' v v' i =
        R'.sy (rF v' v (IsPER.sy (I-per A (R'.rl rA)) (snd (I-resp rA) i)))
  GR-sym (gsig (mkSig A A' F F' ea eb rA rF)) =
    gsig (mkSig A' A F' F eb ea (R'.sy rA) rF')
    where
      rF' : FamEq X A' F' F
      rF' v v' i =
        R'.sy (rF v' v (IsPER.sy (I-per A (R'.rl rA)) (snd (I-resp rA) i)))
  GR-sym (gU (mkU f g f' g' ea eb ind ind' op)) =
    gU (mkU f' g' f g eb ea ind' ind
         (Op-pred X (\ a p -> cong-sub X ind op p) (Op-sym X op)))

  private
    ne-not-nat : {b : D} -> N b b -> b ~~ Nat -> Empty
    ne-not-nat n e = ne-Nat (N-self e n)
    ne-not-pi : {b A F : D} -> N b b -> b ~~ Pi A F -> Empty
    ne-not-pi n e = ne-Pi (N-self e n)
    ne-not-sig : {b A F : D} -> N b b -> b ~~ Sig A F -> Empty
    ne-not-sig n e = ne-Sig (N-self e n)
    ne-not-U : {b f g : D} -> N b b -> b ~~ U f g -> Empty
    ne-not-U n e = ne-U (N-self e n)

  GR-trans : {a b c : D} -> GR X a b -> GR X b c -> GR X a c
  GR-trans (gne n) (gne m) = gne (N-trans n m)
  GR-trans (gne n) (gnat e1 e2) = Empty-elim (ne-not-nat (IsPER.rr N-per n) e1)
  GR-trans (gne n) (gpi p) = Empty-elim (ne-not-pi (IsPER.rr N-per n) (PiRel.ea p))
  GR-trans (gne n) (gU u) = Empty-elim (ne-not-U (IsPER.rr N-per n) (URel.ea u))
  GR-trans (gnat e1 e2) (gne m) = Empty-elim (ne-not-nat (IsPER.rl N-per m) e2)
  GR-trans (gnat e1 e2) (gnat e3 e4) = gnat e1 e4
  GR-trans (gnat e1 e2) (gpi p) =
    Empty-elim (Pi-Nat (~~-trans (~~-sym (PiRel.ea p)) e2))
  GR-trans (gnat e1 e2) (gU u) =
    Empty-elim (Nat-U (~~-trans (~~-sym e2) (URel.ea u)))
  GR-trans (gpi p) (gne m) = Empty-elim (ne-not-pi (IsPER.rl N-per m) (PiRel.eb p))
  GR-trans (gpi p) (gnat e3 e4) =
    Empty-elim (Pi-Nat (~~-trans (~~-sym (PiRel.eb p)) e3))
  GR-trans (gpi p) (gU u) =
    Empty-elim (Pi-U (~~-trans (~~-sym (PiRel.eb p)) (URel.ea u)))
  GR-trans (gU u) (gne m) = Empty-elim (ne-not-U (IsPER.rl N-per m) (URel.eb u))
  GR-trans (gU u) (gnat e3 e4) =
    Empty-elim (Nat-U (~~-trans (~~-sym e3) (URel.eb u)))
  GR-trans (gU u) (gpi p) =
    Empty-elim (Pi-U (~~-trans (~~-sym (PiRel.ea p)) (URel.eb u)))
  GR-trans (gne n) (gsig p) = Empty-elim (ne-not-sig (IsPER.rr N-per n) (SigRel.ea p))
  GR-trans (gsig p) (gne m) = Empty-elim (ne-not-sig (IsPER.rl N-per m) (SigRel.eb p))
  GR-trans (gnat e1 e2) (gsig p) =
    Empty-elim (Sig-Nat (~~-trans (~~-sym (SigRel.ea p)) e2))
  GR-trans (gsig p) (gnat e3 e4) =
    Empty-elim (Sig-Nat (~~-trans (~~-sym (SigRel.eb p)) e3))
  GR-trans (gpi p) (gsig q) =
    Empty-elim (Sig-Pi (~~-trans (~~-sym (SigRel.ea q)) (PiRel.eb p)))
  GR-trans (gsig q) (gpi p) =
    Empty-elim (Sig-Pi (~~-trans (~~-sym (SigRel.eb q)) (PiRel.ea p)))
  GR-trans (gsig p) (gU u) =
    Empty-elim (Sig-U (~~-trans (~~-sym (SigRel.eb p)) (URel.ea u)))
  GR-trans (gU u) (gsig p) =
    Empty-elim (Sig-U (~~-trans (~~-sym (SigRel.ea p)) (URel.eb u)))
  GR-trans (gsig (mkSig A A' F F' ea eb rA rF)) (gsig (mkSig B B' G G' ea2 eb2 rB rG)) =
    gsig (mkSig A B' F G' ea eb2 (R'.tr rA rB') rFG)
    where
      ij = Sig-inj (~~-trans (~~-sym ea2) eb)
      rB' : R A' B'
      rB' = R-cl (fst ij) rB
      rG' : FamEq X A' F' G'
      rG' = FamEq-tr X (fst ij) (snd ij) ~~-refl rG
      rFG : FamEq X A F G'
      rFG v v' i =
        R'.tr (rF v v' i)
              (rG' v' v' (IsPER.rr (I-per A' (R'.rr rA)) (fst (I-resp rA) i)))
  GR-trans (gpi (mkPi A A' F F' ea eb rA rF)) (gpi (mkPi B B' G G' ea2 eb2 rB rG)) =
    gpi (mkPi A B' F G' ea eb2 (R'.tr rA rB') rFG)
    where
      ij = Pi-inj (~~-trans (~~-sym ea2) eb)
      rB' : R A' B'
      rB' = R-cl (fst ij) rB
      rG' : FamEq X A' F' G'
      rG' = FamEq-tr X (fst ij) (snd ij) ~~-refl rG
      rFG : FamEq X A F G'
      rFG v v' i =
        R'.tr (rF v v' i)
              (rG' v' v' (IsPER.rr (I-per A' (R'.rr rA)) (fst (I-resp rA) i)))
  GR-trans (gU (mkU f g f' g' ea eb ind ind' op))
           (gU (mkU h k h' k' ea2 eb2 indh indh' op2)) =
    gU (mkU f g h' k' ea eb2 ind indh' op3)
    where
      ij = U-inj (~~-trans (~~-sym ea2) eb)
      op2' : Op X (Pre X f' g') f' g' h' k'
      op2' = Op-cong X (fst ij) (snd ij) ~~-refl ~~-refl
               (Op-pred X (\ a p -> Pre-cong X (~~-sym (fst ij)) (~~-sym (snd ij)) p) op2)
      op3 : Op X (Pre X f g) f g h' k'
      op3 = Op-trans X op (Op-pred X (\ a p -> cong-sup X ind' op p) op2')

  GR-per : IsPER (GR X)
  GR-per = record { sy = GR-sym ; tr = GR-trans }

  ----------------------------------------------------------------------
  -- Lemma 11: Gamma(X) is a candidate
  ----------------------------------------------------------------------

  -- the PER structure of GI at a PiRel
  piFun-per : {a b : D} (p : PiRel X a b) ->
              IsPER (Fun (I (PiRel.A p)) (\ w -> I (app (PiRel.F p) w)))
  piFun-per p =
    Fun-per (I A) (\ w -> I (app F w)) (I-per A (R'.rl (PiRel.rA p)))
            (famResp~ (piResp p)) (famPer (piResp p))
    where
      A = PiRel.A p
      F = PiRel.F p

  sigFun-per : {a b : D} (p : SigRel X a b) ->
               IsPER (SigF (I (SigRel.A p)) (\ w -> I (app (SigRel.F p) w)))
  sigFun-per p =
    SigF-per (I A) (\ w -> I (app F w)) (I-per A (R'.rl (SigRel.rA p)))
             (famResp~ (sigResp p)) (famPer (sigResp p))
    where
      A = SigRel.A p
      F = SigRel.F p

  GI-per : (a : D) -> GR X a a -> IsPER (GI X a)
  GI-per a (gne n) = per-~ (~-sym (GI-ne a n)) S-per
  GI-per a (gnat e _) = per-~ (~-sym (GI-nat a e)) NatR-per
  GI-per a (gpi p) =
    per-~ (~-sym (GI-pi a (PiRel.A p) (PiRel.F p) (PiRel.ea p))) (piFun-per p)
  GI-per a (gsig p) =
    per-~ (~-sym (GI-sig a (SigRel.A p) (SigRel.F p) (SigRel.ea p))) (sigFun-per p)
  GI-per a (gU u) =
    per-~ (~-sym (GI-U a (URel.f u) (URel.g u) (URel.ea u)))
          (Res-per (Pre X (URel.f u) (URel.g u)))

  GI-resp : {a b : D} -> GR X a b -> GI X a ~ GI X b
  GI-resp {a} {b} (gne n) =
    ~-trans (GI-ne a (IsPER.rl N-per n)) (~-sym (GI-ne b (IsPER.rr N-per n)))
  GI-resp {a} {b} (gnat e1 e2) = ~-trans (GI-nat a e1) (~-sym (GI-nat b e2))
  GI-resp {a} {b} (gpi (mkPi A A' F F' ea eb rA rF)) =
    ~-trans (GI-pi a A F ea)
      (~-trans (Fun-cong (I A) (I A') (\ w -> I (app F w)) (\ w -> I (app F' w))
                 (I-per A (R'.rl rA)) (I-resp rA)
                 (\ v i -> I-resp (rF v v i)))
               (~-sym (GI-pi b A' F' eb)))
  GI-resp {a} {b} (gsig (mkSig A A' F F' ea eb rA rF)) =
    ~-trans (GI-sig a A F ea)
      (~-trans (SigF-cong (I A) (I A') (\ w -> I (app F w)) (\ w -> I (app F' w))
                 (I-per A (R'.rl rA)) (I-resp rA)
                 (\ v i -> I-resp (rF v v i)))
               (~-sym (GI-sig b A' F' eb)))
  GI-resp {a} {b} (gU (mkU f g f' g' ea eb ind ind' op)) =
    ~-trans (GI-U a f g ea)
      (~-trans (Res-cong (congruence X ind ind' op)) (~-sym (GI-U b f' g' eb)))

  GR-ne-only : {n b : D} -> N n n -> GR X n b -> N n b
  GR-ne-only nn (gne m) = m
  GR-ne-only nn (gnat e _) = Empty-elim (ne-not-nat nn e)
  GR-ne-only nn (gpi p) = Empty-elim (ne-not-pi nn (PiRel.ea p))
  GR-ne-only nn (gsig p) = Empty-elim (ne-not-sig nn (SigRel.ea p))
  GR-ne-only nn (gU u) = Empty-elim (ne-not-U nn (URel.ea u))

  GR-nat-only : {b : D} -> GR X Nat b -> b ~~ Nat
  GR-nat-only (gne m) = Empty-elim (ne-Nat m)
  GR-nat-only (gnat _ e) = e
  GR-nat-only (gpi p) = Empty-elim (Pi-Nat (~~-sym (PiRel.ea p)))
  GR-nat-only (gsig p) = Empty-elim (Sig-Nat (~~-sym (SigRel.ea p)))
  GR-nat-only (gU u) = Empty-elim (Nat-U (URel.ea u))

  GR-safe : GR X <= S
  GR-safe (gne n) = N-S n
  GR-safe (gnat e1 e2) = S-back e1 e2 S-Nat
  GR-safe (gpi (mkPi A A' F F' ea eb rA rF)) =
    S-back ea eb (S-Pi (R-safe rA) sF)
    where
      x  = fst (ext F F')
      nx = fst (snd (ext F F'))
      k  = snd (snd (ext F F'))
      sF : S F F'
      sF = k (R-safe (rF x x (I-lo A (R'.rl rA) nx)))
  GR-safe (gsig (mkSig A A' F F' ea eb rA rF)) =
    S-back ea eb (S-Sig (R-safe rA) sF)
    where
      x  = fst (ext F F')
      nx = fst (snd (ext F F'))
      k  = snd (snd (ext F F'))
      sF : S F F'
      sF = k (R-safe (rF x x (I-lo A (R'.rl rA) nx)))
  GR-safe (gU (mkU f g f' g' ea eb ind ind' op)) =
    S-back ea eb
      (S-U (fst (safe-op X op)) (snd (safe-op X op)))

  GI-lo : (a : D) -> GR X a a -> N <= GI X a
  GI-lo a (gne n) m = snd (GI-ne a n) (N-S m)
  GI-lo a (gnat e _) m = snd (GI-nat a e) (N-NatR m)
  GI-lo a (gpi p) m =
    snd (GI-pi a A F (PiRel.ea p))
      (Fun-lo (I A) (\ w -> I (app F w)) (I-per A rAA)
              (famResp~ (piResp p)) (famPer (piResp p))
              (I-hi A rAA) (\ v i -> I-lo (app F v) (piResp p v v i)) m)
    where
      A = PiRel.A p
      F = PiRel.F p
      rAA = R'.rl (PiRel.rA p)
  GI-lo a (gsig p) m =
    snd (GI-sig a A F (SigRel.ea p))
      (SigF-lo (I A) (\ w -> I (app F w)) (I-per A rAA)
               (famResp~ (sigResp p)) (famPer (sigResp p))
               (I-lo A rAA) (\ v i -> I-lo (app F v) (sigResp p v v i)) m)
    where
      A = SigRel.A p
      F = SigRel.F p
      rAA = R'.rl (SigRel.rA p)
  GI-lo a (gU u) m =
    snd (GI-U a (URel.f u) (URel.g u) (URel.ea u))
      (seed-ne m , (pre-ne _ (IsPER.rl N-per m) , pre-ne _ (IsPER.rr N-per m)))

  GI-hi : (a : D) -> GR X a a -> GI X a <= S
  GI-hi a (gne n) q = fst (GI-ne a n) q
  GI-hi a (gnat e _) q = NatR-S (fst (GI-nat a e) q)
  GI-hi a (gpi p) q =
    Fun-hi (I A) (\ w -> I (app F w)) (I-per A rAA)
           (famResp~ (piResp p)) (famPer (piResp p))
           (I-lo A rAA) (\ v i -> I-hi (app F v) (piResp p v v i))
           (fst (GI-pi a A F (PiRel.ea p)) q)
    where
      A = PiRel.A p
      F = PiRel.F p
      rAA = R'.rl (PiRel.rA p)
  GI-hi a (gsig p) q =
    SigF-hi (I A) (\ w -> I (app F w)) (I-per A rAA)
            (famResp~ (sigResp p)) (famPer (sigResp p))
            (I-hi A rAA) (\ v i -> I-hi (app F v) (sigResp p v v i))
            (fst (GI-sig a A F (SigRel.ea p)) q)
    where
      A = SigRel.A p
      F = SigRel.F p
      rAA = R'.rl (SigRel.rA p)
  GI-hi a (gU u) q = R-safe (fst (fst (GI-U a (URel.f u) (URel.g u) (URel.ea u)) q))

  ----------------------------------------------------------------------
  -- closure under the equality of D
  ----------------------------------------------------------------------

  GR-cl : {a a' b : D} -> a ~~ a' -> GR X a b -> GR X a' b
  GR-cl e (gne n) = gne (N-resp e n)
  GR-cl e (gnat e1 e2) = gnat (~~-trans (~~-sym e) e1) e2
  GR-cl e (gpi (mkPi A A' F F' ea eb rA rF)) =
    gpi (mkPi A A' F F' (~~-trans (~~-sym e) ea) eb rA rF)
  GR-cl e (gsig (mkSig A A' F F' ea eb rA rF)) =
    gsig (mkSig A A' F F' (~~-trans (~~-sym e) ea) eb rA rF)
  GR-cl e (gU (mkU f g f' g' ea eb ind ind' op)) =
    gU (mkU f g f' g' (~~-trans (~~-sym e) ea) eb ind ind' op)

  private
    GI-idx1 : {a a' : D} -> a ~~ a' -> GI X a <= GI X a'
    GI-idx1 e (ine n s) = ine (N-self e n) s
    GI-idx1 e (inat ea r) = inat (~~-trans (~~-sym e) ea) r
    GI-idx1 e (ipi A F ea h) = ipi A F (~~-trans (~~-sym e) ea) h
    GI-idx1 e (isig A F ea h) = isig A F (~~-trans (~~-sym e) ea) h
    GI-idx1 e (iU f g ea h) = iU f g (~~-trans (~~-sym e) ea) h

  GI-idx : {a a' : D} -> a ~~ a' -> GI X a ~ GI X a'
  GI-idx e = GI-idx1 e , GI-idx1 (~~-sym e)

  GI-el : {a v w v' : D} -> v ~~ w -> GI X a v v' -> GI X a w v'
  GI-el e (ine n s) = ine n (S-resp e s)
  GI-el e (inat ea r) = inat ea (NatR-resp e r)
  GI-el e (ipi A F ea h) = ipi A F ea (Fun-clL {I A} {\ w -> I (app F w)} (\ w -> I-el) e h)
  GI-el e (isig A F ea h) =
    isig A F ea (SigF-clL {I A} {\ w -> I (app F w)} I-el (\ e' -> I-idx (app-cong ~~-refl e')) (\ w -> I-el) e h)
  GI-el e (iU f g ea (r , (p , p'))) = iU f g ea (R-cl e r , (Pre-cl X e p , p'))

  GI-er : {a v v' w' : D} -> v' ~~ w' -> GI X a v v' -> GI X a v w'
  GI-er e (ine n s) = ine n (S-clR e s)
  GI-er e (inat ea r) = inat ea (NatR-clR e r)
  GI-er e (ipi A F ea h) = ipi A F ea (Fun-clR {I A} {\ w -> I (app F w)} (\ w -> I-er) e h)
  GI-er e (isig A F ea h) = isig A F ea (SigF-clR {I A} {\ w -> I (app F w)} I-er (\ w -> I-er) e h)
  GI-er e (iU f g ea (r , (p , p'))) =
    iU f g ea (CandCl.R-cl2 X ~~-refl e r , (p , Pre-cl X e p'))

-- Lemma 11
Gam : Cand -> Cand
Gam X = record
  { R = GR X
  ; I = GI X
  ; R-per = GR-per X
  ; I-per = GI-per X
  ; I-resp = GI-resp X
  ; seed-ne = gne
  ; ne-int = GI-ne X
  ; ne-only = GR-ne-only X
  ; seed-nat = gnat ~~-refl ~~-refl
  ; nat-int = GI-nat X Nat ~~-refl
  ; nat-only = GR-nat-only X
  ; R-safe = GR-safe X
  ; I-lo = GI-lo X
  ; I-hi = GI-hi X
  ; R-cl = GR-cl X
  ; I-idx = GI-idx X
  ; I-el = GI-el X
  ; I-er = GI-er X }
