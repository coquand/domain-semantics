{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Model/SemCode.agda
--
-- Formation typing for Pi and Sigma codes (one proof, two wrappers):
-- every approximant of  Pi(A, \x:A.B)  (resp. Sigma) is below a
-- well-formed code, i.e. an element of U.
-- (Port of NAT InvTyp-Pi; the family is a Lam predicate.)
------------------------------------------------------------------------

module MAHLOINJ.Model.SemCode where

open import MAHLOINJ.Domain.Basic
  using ( Top ; tt ; Empty ; Pair ; mkSigma ; fst ; snd ; Sigma
        ; Eq ; refl ; Eq-transport ; Eq-sym
        ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl
        ; PairEl ; SigmaCode ; FinFun ; nil ; cons )
open import MAHLOINJ.Domain.Kernel
open import MAHLOINJ.Model.Selection
open import MAHLOINJ.Model.Comb
open import MAHLOINJ.Model.SemLam

mapEdges : (g : FinFun) -> ((p : Edge) -> EdgeIn p g -> Edge) -> FinFun
mapEdges nil         f = nil
mapEdges (cons p ps) f = cons (f p here) (mapEdges ps (\ q ein -> f q (there ein)))

mapEdges-corr : (g : FinFun) (f : (p : Edge) -> EdgeIn p g -> Edge) (q : Edge) (ein : EdgeIn q g) ->
  EdgeIn (f q ein) (mapEdges g f)
mapEdges-corr (cons p ps) f .p here = here
mapEdges-corr (cons p ps) f q (there ein) = there (mapEdges-corr ps (\ r rin -> f r (there rin)) q ein)

-- an element of U-approximant  x <= UCode  types only elements of U
mem-from-U : (x : FinEl) -> AtomS UCode x -> (y : FinEl) -> FinMem y x -> FinMem y UCode
mem-from-U Bot   e Bot fm = tt
mem-from-U UCode e y   fm = fm

module CodeTyping (PA : Pred) (iA : Ideal PA) (Bb : FinEl -> Pred) (okb : BodyOK Bb)
  (invA : InvTypP PA (AtomS UCode))
  (body-ih : (x a : FinEl) -> FinMem x a -> PA a -> InvTypP (Bb x) (AtomS UCode)) where

  open LamProps PA Bb iA okb using () renaming (comp-via-body to compB)

  record Enl (b : FinEl) (f : FinFun) : Set where
    field
      b'   : FinEl
      f'   : FinFun
      leb  : LeCode b b'
      lef  : LeFunCode f f'
      body : CodeBody PA (LamS PA Bb) b' f'
      b'U  : FinMem b' UCode
      allU : FinMemAllU f' b'
      cft  : CoherentFunTail f'

  -- enlarging the domain only
  enl-dom : (b : FinEl) -> PA b -> Sigma FinEl (\ b1 -> Pair (LeCode b b1) (Pair (PA b1) (FinMem b1 UCode)))
  enl-dom b eb =
    let t = invA b eb
    in mkSigma (fst t) (mkSigma (fst (snd (snd t))) (mkSigma (fst (snd (snd (snd t))))
         (mem-from-U (fst (snd t)) (snd (snd (snd (snd (snd t))))) (fst t) (fst (snd (snd (snd (snd t))))))))

  enlarge : (b : FinEl) (f : FinFun) -> CodeBody PA (LamS PA Bb) b f -> Enl b f
  enlarge b nil e =
    let d = enl-dom b (fst (snd e))
    in record { b' = fst d ; f' = nil ; leb = fst (snd d) ; lef = tt
              ; body = mkSigma (mkSigma (coh-from-aU (fst d) (snd (snd (snd d)))) tt)
                               (mkSigma (fst (snd (snd d))) tt)
              ; b'U = snd (snd (snd d)) ; allU = tt ; cft = tt }
  enlarge b (cons p0 ps0) e = result
    where
      f = cons p0 ps0
      cb = fst (fst e) ; cf = snd (fst e)
      evA-b = fst (snd e)
      lb = snd (snd e)
      a' = fst lb ; a'U = fst (snd (snd lb)) ; evA-a' = fst (snd (snd (snd lb)))
      ew = LamBody-edge a' Bb f (snd (snd (snd (snd lb))))
      d  = enl-dom b evA-b
      b1 = fst d ; le-b-b1 = fst (snd d) ; evA-b1 = fst (snd (snd d)) ; b1U = snd (snd (snd d))
      cb1 = coh-from-aU b1 b1U
      ca' = coh-from-aU a' a'U
      cmp = Ideal.comp iA a' b1 evA-a' evA-b1
      bn  = Sup a' b1
      bnU = finMemUCode-Sup a' b1 cmp a'U b1U
      cbn = coh-from-aU bn bnU
      le-a'-bn = LeCode-Sup-left a' b1 cmp ca' cb1
      le-b-bn = LeCode-trans b b1 bn cb cb1 cbn le-b-b1 (LeCode-Sup-right a' b1 cmp ca' cb1)
      evA-bn = Ideal.sup iA a' b1 evA-a' evA-b1

      ED : Edge -> Set
      ED p = Sigma FinEl (\ xi -> Sigma FinEl (\ vi' ->
               Pair (LeCode xi (fst p)) (Pair (FinMem xi a') (Pair (LeCode (snd p) vi')
                 (Pair (Bb xi vi') (FinMem vi' UCode))))))

      edge-data : (p : Edge) -> EdgeIn p f -> ED p
      edge-data p ein =
        let w = ew p ein ; xi = fst w
            t = body-ih xi a' (fst (snd (snd w))) evA-a' (snd p) (snd (snd (snd w)))
        in mkSigma xi (mkSigma (fst t) (mkSigma (fst (snd w)) (mkSigma (fst (snd (snd w)))
             (mkSigma (fst (snd (snd t))) (mkSigma (fst (snd (snd (snd t))))
               (mem-from-U (fst (snd t)) (snd (snd (snd (snd (snd t))))) (fst t) (fst (snd (snd (snd (snd t)))))))))))

      ne : (p : Edge) -> EdgeIn p f -> Edge
      ne p ein = mkSigma (fst (edge-data p ein)) (fst (snd (edge-data p ein)))

      f' = mapEdges f ne

      me-ek : (g : FinFun) (ed : (p : Edge) -> EdgeIn p g -> ED p) ->
        (e : Edge) -> EdgeIn e (mapEdges g (\ p ein -> mkSigma (fst (ed p ein)) (fst (snd (ed p ein))))) ->
        Pair (FinMem (fst e) bn) (Bb (fst e) (snd e))
      me-ek (cons p ps) ed .(mkSigma (fst (ed p here)) (fst (snd (ed p here)))) here =
        let dd = ed p here
        in mkSigma (finMem-upward (fst dd) a' bn le-a'-bn ca' cbn (fst (snd (snd (snd dd)))) bnU)
                   (fst (snd (snd (snd (snd (snd dd))))))
      me-ek (cons p ps) ed e (there ein) = me-ek ps (\ q qin -> ed q (there qin)) e ein

      me-allU : (g : FinFun) (ed : (p : Edge) -> EdgeIn p g -> ED p) ->
        FinMemAllU (mapEdges g (\ p ein -> mkSigma (fst (ed p ein)) (fst (snd (ed p ein))))) bn
      me-allU nil ed = tt
      me-allU (cons p ps) ed =
        let dd = ed p here
        in mkSigma (mkSigma (finMem-upward (fst dd) a' bn le-a'-bn ca' cbn (fst (snd (snd (snd dd)))) bnU)
                            (snd (snd (snd (snd (snd (snd dd)))))))
                   (me-allU ps (\ q qin -> ed q (there qin)))

      me-cw : (sk sv : FinEl) (rest : FinFun) -> Coherent sk -> CoherentFunTail rest -> Bb sk sv ->
        (ed : (q : Edge) -> EdgeIn q rest -> ED q) ->
        CoherentWith (mkSigma sk sv) (mapEdges rest (\ q ein -> mkSigma (fst (ed q ein)) (fst (snd (ed q ein)))))
      me-cw sk sv nil csk crest eb ed = tt
      me-cw sk sv (cons t ts) csk crest eb ed =
        let dt = ed t here
            cxt = FinMem-coh-u (fst dt) a' (fst (snd (snd (snd dt))))
        in mkSigma (\ ck -> compB sk (fst dt) sv (fst (snd dt)) ck csk cxt eb (fst (snd (snd (snd (snd (snd dt)))))))
                   (me-cw sk sv ts csk (CFTcons.tail-coh crest) eb (\ q qin -> ed q (there qin)))

      me-cft : (g : FinFun) -> CoherentFunTail g -> (ed : (p : Edge) -> EdgeIn p g -> ED p) ->
        CoherentFunTail (mapEdges g (\ p ein -> mkSigma (fst (ed p ein)) (fst (snd (ed p ein)))))
      me-cft nil cg ed = tt
      me-cft (cons p ps) cg ed =
        let dp = ed p here
            cxp = FinMem-coh-u (fst dp) a' (fst (snd (snd (snd dp))))
            vU = snd (snd (snd (snd (snd (snd dp)))))
            nbv = NotBot-from-Le (snd p) (fst (snd dp)) (CFTcons.val-nbot cg) (fst (snd (snd (snd (snd dp)))))
        in mkCFT cxp (coh-from-aU (fst (snd dp)) vU) nbv
             (me-cw (fst dp) (fst (snd dp)) ps cxp (CFTcons.tail-coh cg) (fst (snd (snd (snd (snd (snd dp))))))
                (\ q qin -> ed q (there qin)))
             (me-cft ps (CFTcons.tail-coh cg) (\ q qin -> ed q (there qin)))

      cft' : CoherentFunTail f'
      cft' = me-cft f cf edge-data

      me-lf : (ps : FinFun) -> (shift : (q : Edge) -> EdgeIn q ps -> EdgeIn q f) -> LeFunCode ps f'
      me-lf nil shift = tt
      me-lf (cons q qs) shift =
        let dq = edge-data q (shift q here)
            ce = cft-edge cf (shift q here)
            ck-q = CFTcons.key-coh ce ; cv-q = CFTcons.val-coh ce
            head-le = EvalFun-edge-le (ne q (shift q here)) f' (fst q) cft'
                        (mapEdges-corr f ne q (shift q here)) ck-q (fst (snd (snd dq)))
            cvq' = coh-from-aU (fst (snd dq)) (snd (snd (snd (snd (snd (snd dq))))))
        in mkSigma (LeCode-trans (snd q) (fst (snd dq)) (EvalFun f' (fst q)) cv-q cvq'
                      (Coherent-EvalFun f' (fst q) cft' ck-q) (fst (snd (snd (snd (snd dq))))) head-le)
                   (me-lf qs (\ r rin -> shift r (there rin)))

      ek' = me-ek f edge-data

      result : Enl b f
      result = record
        { b' = bn ; f' = f' ; leb = le-b-bn ; lef = me-lf f (\ q qin -> qin)
        ; body = mkSigma (mkSigma cbn cft') (mkSigma evA-bn
                   (mkSigma bn (mkSigma cft' (mkSigma bnU (mkSigma evA-bn
                     (LamEdges.from-edges Bb okb bn f' cft' bnU (LamTyping.EK-to-EW PA iA Bb bn f' ek')))))))
        ; b'U = bnU ; allU = me-allU f edge-data ; cft = cft' }

  Pi-typed : InvTypP (PiS PA (LamS PA Bb)) (AtomS UCode)
  Pi-typed Bot e = TypedP-Bot _ _ tt (mkSigma tt tt)
  Pi-typed (PiCode b f) e =
    let r = enlarge b f e
    in mkSigma (PiCode (Enl.b' r) (Enl.f' r)) (mkSigma UCode (mkSigma (mkSigma (Enl.leb r) (Enl.lef r))
         (mkSigma (Enl.body r) (mkSigma (finMem-piU-mk (Enl.b' r) (Enl.f' r) (Enl.b'U r) (Enl.allU r) (Enl.cft r))
           (mkSigma tt tt)))))

  Sig-typed : InvTypP (SigS PA (LamS PA Bb)) (AtomS UCode)
  Sig-typed Bot e = TypedP-Bot _ _ tt (mkSigma tt tt)
  Sig-typed (SigmaCode b f) e =
    let r = enlarge b f e
    in mkSigma (SigmaCode (Enl.b' r) (Enl.f' r)) (mkSigma UCode (mkSigma (mkSigma (Enl.leb r) (Enl.lef r))
         (mkSigma (Enl.body r) (mkSigma (finMem-sigU-mk (Enl.b' r) (Enl.f' r) (Enl.b'U r) (Enl.allU r) (Enl.cft r))
           (mkSigma tt tt)))))
