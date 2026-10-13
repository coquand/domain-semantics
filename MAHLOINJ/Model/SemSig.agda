{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Model/SemSig.agda
--
-- Semantic content of the Sigma rules (paper1 Sec. 3.1):
--   Pair-typed, Fst-typed, Snd-typed, projection betas, and
--   surjective pairing (pair extensionality), generically.
------------------------------------------------------------------------

module MAHLOINJ.Model.SemSig where

open import MAHLOINJ.Domain.Basic
  using ( Top ; tt ; Empty ; Pair ; mkSigma ; fst ; snd ; Sigma
        ; Eq ; refl ; Eq-transport ; Eq-sym
        ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl
        ; PairEl ; SigmaCode ; FinFun ; nil ; cons )
open import MAHLOINJ.Domain.Kernel
open import MAHLOINJ.Model.Selection
open import MAHLOINJ.Model.Comb
open import MAHLOINJ.Model.SemLam
open import MAHLOINJ.Model.SemCode using (mem-from-U)
open import MAHLOINJ.Model.SemConv using (Incl ; ew-single)

------------------------------------------------------------------------
-- small facts
------------------------------------------------------------------------

PairNB-mono : (a b a' b' : FinEl) -> PairNB a b -> LeCode a a' -> LeCode b b' -> PairNB a' b'
PairNB-mono a b a' b' nb la lb = go (bot-or a)
  where
    go : Or (Eq a Bot) (NotBot a) -> PairNB a' b'
    go (left refl) = PairNB-intro2 a' b' (NotBot-from-Le b b' nb lb)
    go (right na) = PairNB-intro1 a' b' (NotBot-from-Le a a' na la)

-- elements typed in a Sigma code are Bot or pairs
data Shape (w : FinEl) : Set where
  sh-bot  : Eq w Bot -> Shape w
  sh-pair : (a b : FinEl) -> Eq w (PairEl a b) -> Shape w

shape : (PA PF : Pred) (w w' s : FinEl) -> LeCode w w' -> FinMem w' s -> SigS PA PF s -> Shape w
shape PA PF Bot w' s le fm e = sh-bot refl
shape PA PF (PairEl a b) w' s le fm e = sh-pair a b refl
shape PA PF UCode UCode Bot le () e
shape PA PF UCode UCode (SigmaCode _ _) le () e
shape PA PF (FunEl _) (FunEl _) Bot le () e
shape PA PF (FunEl _) (FunEl _) (SigmaCode _ _) le () e
shape PA PF (PiCode _ _) (PiCode _ _) Bot le () e
shape PA PF (PiCode _ _) (PiCode _ _) (SigmaCode _ _) le () e
shape PA PF NatCode NatCode Bot le () e
shape PA PF NatCode NatCode (SigmaCode _ _) le () e
shape PA PF ZeroEl ZeroEl Bot le () e
shape PA PF ZeroEl ZeroEl (SigmaCode _ _) le () e
shape PA PF (SucEl _) (SucEl _) Bot le () e
shape PA PF (SucEl _) (SucEl _) (SigmaCode _ _) le () e
shape PA PF (SigmaCode _ _) (SigmaCode _ _) Bot le () e
shape PA PF (SigmaCode _ _) (SigmaCode _ _) (SigmaCode _ _) le () e

------------------------------------------------------------------------
-- Pair
------------------------------------------------------------------------

module PairTyping (PA Pt Pu PBt : Pred) (Bb : FinEl -> Pred)
  (iA : Ideal PA) (iT : Ideal Pt) (iU : Ideal Pu) (okb : BodyOK Bb)
  (invT : InvTypP Pt PA) (invU : InvTypP Pu PBt)
  (fwdB : (b : FinEl) -> PBt b -> Sigma FinEl (\ v -> Pair (Pt v) (Bb v b)))
  (bodyU : (x a : FinEl) -> FinMem x a -> PA a -> InvTypP (Bb x) (AtomS UCode)) where

  T = SigS PA (LamS PA Bb)

  build : (k' a' b1 : FinEl) -> Pt k' -> PA a' -> FinMem k' a' -> Pu b1 ->
    (beta : FinEl) -> Bb k' beta -> FinMem beta UCode -> FinMem b1 beta -> PairNB k' b1 ->
    Sigma FinEl (\ s -> Pair (FinMem (PairEl k' b1) s) (T s))
  build k' a' b1 ek ea fk eb beta bb bU fb nb = go (bot-or beta)
    where
      ck = FinMem-coh-u k' a' fk
      a'U = FinMem-a-in-U k' a' fk
      ca' = coh-from-aU a' a'U
      cb1 = FinMem-coh-u b1 beta fb
      cpair : Coherent (PairEl k' b1)
      cpair = mkSigma ck (mkSigma cb1 nb)
      go : Or (Eq beta Bot) (NotBot beta) -> Sigma FinEl (\ s -> Pair (FinMem (PairEl k' b1) s) (T s))
      go (left refl) =
        let sU = finMem-sigU-mk a' nil a'U tt tt
        in mkSigma (SigmaCode a' nil)
               (mkSigma (finMemC-pair-mk k' b1 a' nil fk fb nb sU)
                 (mkSigma (mkSigma ca' tt) (mkSigma ea tt)))
      go (right nbb) =
        let f = cons (mkSigma k' beta) nil
            cbeta = coh-from-aU beta bU
            cf = sing-coh k' beta ck cbeta nbb
            allU : FinMemAllU f a'
            allU = mkSigma (mkSigma fk bU) tt
            sU = finMem-sigU-mk a' f a'U allU cf
            le-ev = sing-EvalFun k' beta k' cf ck (LeCode-refl k' ck)
            cev = Coherent-EvalFun f k' cf ck
            evU = EvalFun-in-UCode f k' a' cf ck allU
            fb' = finMem-upward b1 beta (EvalFun f k') le-ev cbeta cev fb evU
            lb : LamBody PA Bb f
            lb = mkSigma a' (mkSigma cf (mkSigma a'U (mkSigma ea
                   (LamEdges.from-edges Bb okb a' f cf a'U (ew-single Bb k' beta a' (LeCode-refl k' ck) fk bb)))))
        in mkSigma (SigmaCode a' f)
               (mkSigma (finMemC-pair-mk k' b1 a' f fk fb' nb sU)
                 (mkSigma (mkSigma ca' cf) (mkSigma ea lb)))

  Pair-typed : InvTypP (PairS Pt Pu) T
  Pair-typed Bot e = TypedP-Bot _ _ tt tt
  Pair-typed (PairEl a b) e =
    let ta = invT a (fst (snd e))
        a1 = fst ta ; le-a = fst (snd (snd ta)) ; ea1 = fst (snd (snd (snd ta)))
        tb = invU b (snd (snd e))
        b1 = fst tb ; beta0 = fst (snd tb) ; le-b = fst (snd (snd tb)) ; eb1 = fst (snd (snd (snd tb)))
        fb1 = fst (snd (snd (snd (snd tb)))) ; ebt = snd (snd (snd (snd (snd tb))))
        fw = fwdB beta0 ebt
        v = fst fw ; ev = fst (snd fw) ; bbv = snd (snd fw)
        cva = Ideal.comp iT a1 v ea1 ev
        k = Sup a1 v
        ek = Ideal.sup iT a1 v ea1 ev
        tk = invT k ek
        k' = fst tk ; a' = fst (snd tk) ; le-k = fst (snd (snd tk)) ; ek' = fst (snd (snd (snd tk)))
        fk' = fst (snd (snd (snd (snd tk)))) ; ea' = snd (snd (snd (snd (snd tk))))
        ca1 = Ideal.coh iT a1 ea1 ; cv = Ideal.coh iT v ev ; ck = Ideal.coh iT k ek
        ck' = FinMem-coh-u k' a' fk'
        le-v-k' = LeCode-trans v k k' cv ck ck' (LeCode-Sup-right a1 v cva ca1 cv) le-k
        le-a-k' = LeCode-trans a k k' (fst (fst e)) ck ck'
                    (LeCode-trans a a1 k (fst (fst e)) ca1 ck le-a (LeCode-Sup-left a1 v cva ca1 cv)) le-k
        bbk = BodyOK.mon okb v k' beta0 cv ck' le-v-k' bbv
        tbeta = bodyU k' a' fk' ea' beta0 bbk
        beta' = fst tbeta ; le-beta = fst (snd (snd tbeta)) ; bb' = fst (snd (snd (snd tbeta)))
        beta'U = mem-from-U (fst (snd tbeta)) (snd (snd (snd (snd (snd tbeta))))) beta'
                   (fst (snd (snd (snd (snd tbeta)))))
        cbeta0 = coh-from-aU beta0 (FinMem-a-in-U b1 beta0 fb1)
        fb1' = finMem-upward b1 beta0 beta' le-beta cbeta0 (coh-from-aU beta' beta'U) fb1 beta'U
        nb = PairNB-mono a b k' b1 (snd (snd (fst e))) le-a-k' le-b
        r = build k' a' b1 ek' ea' fk' eb1 beta' bb' beta'U fb1' nb
        cpair = mkSigma ck' (mkSigma (FinMem-coh-u b1 beta' fb1') nb)
    in mkSigma (PairEl k' b1) (mkSigma (fst r) (mkSigma (mkSigma le-a-k' le-b)
         (mkSigma (mkSigma cpair (mkSigma ek' eb1)) (snd r))))

------------------------------------------------------------------------
-- Projections
------------------------------------------------------------------------

module ProjTyping (PA Pt : Pred) (Bb : FinEl -> Pred) (iA : Ideal PA) (iT : Ideal Pt) (okb : BodyOK Bb)
  (invT : InvTypP Pt (SigS PA (LamS PA Bb))) where

  -- typed enlargement of a pair approximant of t
  enl : (w : FinEl) -> Pt w -> NotBot w ->
    Sigma FinEl (\ a1 -> Sigma FinEl (\ b1 -> Sigma FinEl (\ al -> Sigma FinFun (\ f ->
      Pair (LeCode w (PairEl a1 b1)) (Pair (Pt (PairEl a1 b1))
        (Pair (FinMem (PairEl a1 b1) (SigmaCode al f)) (CodeBody PA (LamS PA Bb) al f)))))))
  enl w e nbw = go (fst t) (fst (snd t)) (fst (snd (snd t))) (fst (snd (snd (snd t))))
                   (fst (snd (snd (snd (snd t))))) (snd (snd (snd (snd (snd t)))))
    where
      t = invT w e
      go : (w' s : FinEl) -> LeCode w w' -> Pt w' -> FinMem w' s -> SigS PA (LamS PA Bb) s ->
        Sigma FinEl (\ a1 -> Sigma FinEl (\ b1 -> Sigma FinEl (\ al -> Sigma FinFun (\ f ->
          Pair (LeCode w (PairEl a1 b1)) (Pair (Pt (PairEl a1 b1))
            (Pair (FinMem (PairEl a1 b1) (SigmaCode al f)) (CodeBody PA (LamS PA Bb) al f)))))))
      go (PairEl a1 b1) (SigmaCode al f) le ew fm es =
        mkSigma a1 (mkSigma b1 (mkSigma al (mkSigma f (mkSigma le (mkSigma ew (mkSigma fm es))))))
      go Bot s le ew fm es = Empty-elim (notle w nbw le)
        where
          notle : (w : FinEl) -> NotBot w -> LeCode w Bot -> Empty
          notle Bot () l
      go UCode (SigmaCode _ _) le ew () es
      go (FunEl _) (SigmaCode _ _) le ew () es
      go (PiCode _ _) (SigmaCode _ _) le ew () es
      go NatCode (SigmaCode _ _) le ew () es
      go ZeroEl (SigmaCode _ _) le ew () es
      go (SucEl _) (SigmaCode _ _) le ew () es
      go (SigmaCode _ _) (SigmaCode _ _) le ew () es

  -- the first component of a typed pair, as an element of Fst t
  fst-in : (a1 b1 : FinEl) -> Pt (PairEl a1 b1) -> Coherent a1 -> FstS Pt a1
  fst-in a1 b1 e ca1 = go (bot-or a1)
    where
      go : Or (Eq a1 Bot) (NotBot a1) -> FstS Pt a1
      go (left refl) = tt
      go (right nb) = guard-intro a1 nb
        (Ideal.down iT (PairEl a1 b1) (PairEl a1 Bot) e (mkSigma ca1 (mkSigma tt (pairNB-l a1 nb)))
           (mkSigma (LeCode-refl a1 ca1) tt))

  Fst-typed : InvTypP (FstS Pt) PA
  Fst-typed u e = go (bot-or u)
    where
      go : Or (Eq u Bot) (NotBot u) -> TypedP (FstS Pt) PA u
      go (left refl) = TypedP-Bot _ _ tt (Ideal.bot iA)
      go (right nb) =
        let r = enl (PairEl u Bot) (guard-elim u nb e) tt
            a1 = fst r ; b1 = fst (snd r) ; al = fst (snd (snd r)) ; f = fst (snd (snd (snd r)))
            le = fst (snd (snd (snd (snd r)))) ; ep = fst (snd (snd (snd (snd (snd r)))))
            fm = fst (snd (snd (snd (snd (snd (snd r))))))
            es = snd (snd (snd (snd (snd (snd (snd r))))))
            fa1 = finMemC-pair-fst a1 b1 al f fm
            ca1 = FinMem-coh-u a1 al fa1
        in mkSigma a1 (mkSigma al (mkSigma (fst le) (mkSigma (fst-in a1 b1 ep ca1)
             (mkSigma fa1 (fst (snd es))))))

  module SndT (PT : Pred) (toT : (a1 b : FinEl) -> FstS Pt a1 -> Bb a1 b -> PT b) (tBot : PT Bot) where

    cod : (a1 : FinEl) (al : FinEl) (f : FinFun) -> Coherent a1 -> FstS Pt a1 ->
      CoherentFunTail f -> FamRel (LamS PA Bb) f -> PT (EvalFun f a1)
    cod a1 al nil ca1 ef cf fr = tBot
    cod a1 al (cons q qs) ca1 ef cf lb =
      let f = cons q qs
          sb = selectionBelow f a1 cf ca1
          x-f = fst sb ; w-f = fst (snd sb) ; sel-f = fst (snd (snd sb))
          le-xf = fst (snd (snd (snd sb))) ; eq-wf = snd (snd (snd (snd sb)))
          rr = snd (snd (snd (snd lb))) x-f w-f sel-f
          z = fst rr ; cz = FinMem-coh-u z (fst lb) (fst (snd (snd rr)))
          cxf = Coherent-Selection sel-f cf
          le-z = LeCode-trans z x-f a1 cz cxf ca1 (fst (snd rr)) le-xf
          bz = Eq-transport (Bb z) (Eq-sym eq-wf) (snd (snd (snd rr)))
      in toT a1 (EvalFun f a1) ef (BodyOK.mon okb z a1 (EvalFun f a1) cz ca1 le-z bz)

    Snd-typed : InvTypP (SndS Pt) PT
    Snd-typed u e = go (bot-or u)
      where
        go : Or (Eq u Bot) (NotBot u) -> TypedP (SndS Pt) PT u
        go (left refl) = TypedP-Bot _ _ tt tBot
        go (right nb) =
          let r = enl (PairEl Bot u) (guard-elim u nb e) tt
              a1 = fst r ; b1 = fst (snd r) ; al = fst (snd (snd r)) ; f = fst (snd (snd (snd r)))
              le = fst (snd (snd (snd (snd r)))) ; ep = fst (snd (snd (snd (snd (snd r)))))
              fm = fst (snd (snd (snd (snd (snd (snd r))))))
              es = snd (snd (snd (snd (snd (snd (snd r))))))
              fa1 = finMemC-pair-fst a1 b1 al f fm
              fb1 = finMemC-pair-snd a1 b1 al f fm
              ca1 = FinMem-coh-u a1 al fa1
              cb1 = FinMem-coh-u b1 _ fb1
              nbb1 = NotBot-from-Le u b1 nb (snd le)
              eb1 = guard-intro b1 nbb1
                      (Ideal.down iT (PairEl a1 b1) (PairEl Bot b1) ep (mkSigma tt (mkSigma cb1 nbb1))
                         (mkSigma tt (LeCode-refl b1 cb1)))
          in mkSigma b1 (mkSigma (EvalFun f a1) (mkSigma (snd le) (mkSigma eb1
               (mkSigma fb1 (cod a1 al f ca1 (fst-in a1 b1 ep ca1) (snd (fst es)) (snd (snd es)))))))

------------------------------------------------------------------------
-- Projection betas and surjective pairing
------------------------------------------------------------------------

fst-beta-l : (Pt Pu : Pred) -> Incl (FstS (PairS Pt Pu)) Pt -> Incl (FstS (PairS Pt Pu)) Pt
fst-beta-l Pt Pu h = h

module PairEq (Pt Pu : Pred) (iT : Ideal Pt) (iU : Ideal Pu) where

  fst-beta-1 : Incl (FstS (PairS Pt Pu)) Pt
  fst-beta-1 u e = go (bot-or u)
    where
      go : Or (Eq u Bot) (NotBot u) -> Pt u
      go (left refl) = Ideal.bot iT
      go (right nb) = fst (snd (guard-elim u nb e))

  fst-beta-2 : Incl Pt (FstS (PairS Pt Pu))
  fst-beta-2 u e = go (bot-or u)
    where
      go : Or (Eq u Bot) (NotBot u) -> FstS (PairS Pt Pu) u
      go (left refl) = tt
      go (right nb) = guard-intro u nb (mkSigma (mkSigma (Ideal.coh iT u e) (mkSigma tt (pairNB-l u nb)))
                                                (mkSigma e (Ideal.bot iU)))

  snd-beta-1 : Incl (SndS (PairS Pt Pu)) Pu
  snd-beta-1 u e = go (bot-or u)
    where
      go : Or (Eq u Bot) (NotBot u) -> Pu u
      go (left refl) = Ideal.bot iU
      go (right nb) = snd (snd (guard-elim u nb e))

  snd-beta-2 : Incl Pu (SndS (PairS Pt Pu))
  snd-beta-2 u e = go (bot-or u)
    where
      go : Or (Eq u Bot) (NotBot u) -> SndS (PairS Pt Pu) u
      go (left refl) = tt
      go (right nb) = guard-intro u nb (mkSigma (mkSigma tt (mkSigma (Ideal.coh iU u e) nb))
                                                (mkSigma (Ideal.bot iT) e))

-- surjective pairing: a Sigma-typed t is determined by its projections
module PairExt (PA PF Pt Pt' : Pred) (iT : Ideal Pt) (iT' : Ideal Pt')
  (invT : InvTypP Pt (SigS PA PF))
  (hf : Incl (FstS Pt) (FstS Pt')) (hs : Incl (SndS Pt) (SndS Pt')) where

  pieces : (a b : FinEl) -> Pt (PairEl a b) -> Coherent (PairEl a b) -> Pt' (PairEl a b)
  pieces a b e c = go (bot-or a) (bot-or b)
    where
      ca = fst c ; cb = fst (snd c)
      fstp : NotBot a -> Pt' (PairEl a Bot)
      fstp na = guard-elim a na (hf a (guard-intro a na
                  (Ideal.down iT (PairEl a b) (PairEl a Bot) e (mkSigma ca (mkSigma tt (pairNB-l a na)))
                     (mkSigma (LeCode-refl a ca) tt))))
      sndp : NotBot b -> Pt' (PairEl Bot b)
      sndp nb = guard-elim b nb (hs b (guard-intro b nb
                  (Ideal.down iT (PairEl a b) (PairEl Bot b) e (mkSigma tt (mkSigma cb nb))
                     (mkSigma tt (LeCode-refl b cb)))))
      go : Or (Eq a Bot) (NotBot a) -> Or (Eq b Bot) (NotBot b) -> Pt' (PairEl a b)
      go (left refl) (left refl) = Empty-elim (snd (snd c))
      go (left refl) (right nb) = sndp nb
      go (right na) (left refl) = fstp na
      go (right na) (right nb) =
        Eq-transport (\ z -> Pt' (PairEl z (Sup Bot b))) (Sup-Bot-r a)
          (Ideal.sup iT' (PairEl a Bot) (PairEl Bot b) (fstp na) (sndp nb))

  incl : Incl Pt Pt'
  incl w e =
    let t = invT w e
    in go (shape PA PF w (fst t) (fst (snd t)) (fst (snd (snd t))) (fst (snd (snd (snd (snd t)))))
             (snd (snd (snd (snd (snd t))))))
    where
      go : Shape w -> Pt' w
      go (sh-bot refl) = Ideal.bot iT'
      go (sh-pair a b refl) = pieces a b e (Ideal.coh iT (PairEl a b) e)
