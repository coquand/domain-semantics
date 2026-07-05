{-# OPTIONS --without-K --exact-split #-}
------------------------------------------------------------------------
-- RankSandwichFunBuild.agda  (MIN/ -- Pi + U fragment)
--
-- funBuild: assemble the reduced function element.  Reduces the type z
-- (giving z0', zf') AND the member graph g into g' : z0' -> zf', with
-- ga <= g' <= gb, by induction on the lower graph ga.  The codomain
-- family zf' carries the cf-cover (from famBuild) APPENDED with the
-- per-edge reduced codomain types T'.
------------------------------------------------------------------------
module ID.Domain.RankSandwichFunBuild where

open import ID.Domain.Basic
  using ( Nat ; zero ; suc ; max ; Le ; Le-trans ; Le-max-l ; Le-max-r ; tt ; Top
        ; FinEl ; Bot ; UCode ; FinFun ; nil ; cons
        ; Pair ; Sigma ; mkSigma ; fst ; snd )
open import ID.Domain.Order
  using ( RANK ; RANKFun ; Sup ; Coherent ; CoherentFun ; CoherentFunTail
        ; EvalFun ; LeCode ; LeFunCode ; LeCode-trans
        ; CFTcons ; mkCFT ; Comp ; CompFun ; CompFun-sym
        ; CoherentFunTail-append ; compStepFun-to-coherentWith
        ; Coherent-Sup ; Coherent-EvalFun ; LeCode-Comp
        ; LeCode-Sup-left ; LeCode-Sup-right ; LeCode-Sup-lub
        ; RANK-Sup ; RANK-append ; Le-max-lub ; append ; LeFunCode-refl )
open import ID.Domain.MemStage using ( finMemC )
open import ID.Domain.Membership
  using ( FinMemFun ; FinMemAllU ; FinMemFun-append ; finMemFun-upward
        ; finMem-funel-mk ; allU-to ; allU-from )
open import ID.Domain.MemProps
  using ( finMem-upward ; EvalFun-in-UCode ; FinMem-Sup-element ; FinMemAllU-append-Sup )
open import ID.Domain.MemUnfold using ( FinMem-coh-u )
open import ID.Domain.FamU using ( FamToU ; mkFamToU ; edge-le )
open import ID.Model.Selection using ( here )
open import ID.Domain.RankSandwichCore using ( SStmt )
open import ID.Domain.RankSandwichFam
  using ( FamOut ; famBuild ; compStep-cap ; compFun-cap
        ; lefun-append-mono-L ; lefun-append-mono-R ; finMemAllU-up )
open import ID.Domain.RankSandwichFun using ( FunEdgeOut ; funEdge )

-- append-ending-in-a-singleton is always a CoherentFun when it is a CoherentFunTail.
cf-of-append-fe : (g : FinFun) (p : Pair FinEl FinEl) ->
  CoherentFunTail (append g (cons p nil)) -> CoherentFun (append g (cons p nil))
cf-of-append-fe nil         p cft = cft
cf-of-append-fe (cons q qs) p cft = cft

record FunBuildOut (m : Nat) (c0 d0 : FinEl) (cf df gb ga : FinFun) : Set where
  constructor mkFunBuildOut
  field
    fbZ0' : FinEl
    fbZf' fbG' : FinFun
    fb-cohz0' : Coherent fbZ0'
    fb-z0'U   : finMemC fbZ0' UCode
    fb-rkz0'  : Le (RANK fbZ0') m
    fb-c0z0'  : LeCode c0 fbZ0'
    fb-z0'd0  : LeCode fbZ0' d0
    fb-zfkeys : FinMemAllU fbZf' fbZ0'
    fb-zfcoh  : CoherentFunTail fbZf'
    fb-rkzf   : Le (RANKFun fbZf') m
    fb-cf-zf  : LeFunCode cf fbZf'
    fb-zf-df  : LeFunCode fbZf' df
    fb-gfun   : FinMemFun fbG' fbZ0' fbZf'
    fb-gcoh   : CoherentFunTail fbG'
    fb-rkg    : Le (RANKFun fbG') m
    fb-ga-g   : LeFunCode ga fbG'
    fb-g-gb   : LeFunCode fbG' gb

funBuild : (m : Nat) (ih : SStmt m)
  (z0 c0 d0 : FinEl) (zf gb df g : FinFun) ->
  Coherent z0 -> finMemC z0 UCode -> Le (RANK z0) (suc m) ->
  Coherent c0 -> Le (RANK c0) m -> LeCode c0 z0 ->
  Coherent d0 -> Le (RANK d0) m -> LeCode z0 d0 ->
  CoherentFunTail zf -> FinMemAllU zf z0 -> Le (RANKFun zf) (suc m) ->
  CoherentFunTail gb -> Le (RANKFun gb) m ->
  CoherentFunTail df -> Le (RANKFun df) m -> LeFunCode zf df ->
  CoherentFunTail g -> FinMemFun g z0 zf -> Le (RANKFun g) (suc m) -> LeFunCode g gb ->
  (cf : FinFun) -> CoherentFunTail cf -> Le (RANKFun cf) m -> LeFunCode cf zf ->
  (ga : FinFun) -> CoherentFunTail ga -> Le (RANKFun ga) m -> LeFunCode ga g ->
  FunBuildOut m c0 d0 cf df gb ga
funBuild m ih z0 c0 d0 zf gb df g
  cz0 z0U rz0 cc0 rc0 c0z0 cd0 rd0 z0d0
  czf allUzf rzf cgb rgb cdf rdf zfdf cg fmg rg ggb
  cf ccf rcf cfzf nil cga rga ga-g =
  mkFunBuildOut z0' zf' nil
    (FamOut.f-cohx0' tf) (FamOut.f-x0'U tf) (FamOut.f-rkx0' tf)
    (FamOut.f-a0x0' tf) (FamOut.f-x0'b0 tf)
    (FamOut.f-keys tf) (FamOut.f-cohf tf) (FamOut.f-rkf tf)
    (FamOut.f-af tf) (FamOut.f-bf tf)
    tt tt tt tt tt
  where
    tf = famBuild m ih z0 c0 d0 zf df cz0 z0U rz0 cc0 rc0 c0z0 cd0 rd0 z0d0
                  czf allUzf rzf cdf rdf zfdf cf ccf rcf cfzf
    z0' = FamOut.fX0' tf
    zf' = FamOut.fXf' tf
funBuild m ih z0 c0 d0 zf gb df g
  cz0 z0U rz0 cc0 rc0 c0z0 cd0 rd0 z0d0
  czf allUzf rzf cgb rgb cdf rdf zfdf cg fmg rg ggb
  cf ccf rcf cfzf (cons kw rest) cga rga ga-g =
  mkFunBuildOut z0' zf' g'
    cohz0' z0'U rk-z0' c0-z0' z0'-d0
    zfkeys zfcoh rk-zf cf-zf zf-df
    gfun gcoh rk-g ga-g' g-gb
  where
    ka = fst kw ; wa = snd kw
    cka = CFTcons.key-coh cga ; cwa = CFTcons.val-coh cga ; nbwa = CFTcons.val-nbot cga
    cohrest = CFTcons.tail-coh cga
    wa-gka : LeCode wa (EvalFun g ka)
    wa-gka = fst ga-g
    rka : Le (RANK ka) m
    rka = Le-trans (RANK ka) (RANKFun (cons kw rest)) m
            (Le-max-l (RANK ka) (max (RANK wa) (RANKFun rest))) rga
    rwa : Le (RANK wa) m
    rwa = Le-trans (RANK wa) (RANKFun (cons kw rest)) m
            (Le-trans (RANK wa) (max (RANK wa) (RANKFun rest)) (RANKFun (cons kw rest))
              (Le-max-l (RANK wa) (RANKFun rest))
              (Le-max-r (RANK ka) (max (RANK wa) (RANKFun rest)))) rga
    rrest : Le (RANKFun rest) m
    rrest = Le-trans (RANKFun rest) (RANKFun (cons kw rest)) m
              (Le-trans (RANKFun rest) (max (RANK wa) (RANKFun rest)) (RANKFun (cons kw rest))
                (Le-max-r (RANK wa) (RANKFun rest))
                (Le-max-r (RANK ka) (max (RANK wa) (RANKFun rest)))) rga
    rec = funBuild m ih z0 c0 d0 zf gb df g
            cz0 z0U rz0 cc0 rc0 c0z0 cd0 rd0 z0d0
            czf allUzf rzf cgb rgb cdf rdf zfdf cg fmg rg ggb
            cf ccf rcf cfzf rest cohrest rrest (snd ga-g)
    z0'r = FunBuildOut.fbZ0' rec ; zf'r = FunBuildOut.fbZf' rec ; g'r = FunBuildOut.fbG' rec
    cohz0r = FunBuildOut.fb-cohz0' rec ; z0rU = FunBuildOut.fb-z0'U rec
    fe = funEdge m ih z0 c0 d0 zf g gb df ka wa
           cz0 z0U rz0 cc0 rc0 c0z0 cd0 rd0 z0d0
           czf allUzf rzf cg fmg rg cgb rgb ggb cdf rdf zfdf
           cka rka cwa rwa nbwa wa-gka
    z0'e = FunEdgeOut.feZ0' fe ; k' = FunEdgeOut.feK' fe
    T'   = FunEdgeOut.feT' fe ; w' = FunEdgeOut.feW' fe
    cohz0e : Coherent z0'e
    cohz0e = FinMem-coh-u z0'e UCode (FunEdgeOut.fe-z0'U fe)
    ck' = FunEdgeOut.fe-ck' fe ; cT' = FunEdgeOut.fe-cT' fe ; cw' = FunEdgeOut.fe-cw' fe
    -- domain join
    comp-re : Comp z0'r z0'e
    comp-re = LeCode-Comp z0'r z0'e d0 cd0 (FunBuildOut.fb-z0'd0 rec) (FunEdgeOut.fe-b0 fe)
    z0' = Sup z0'r z0'e
    cohz0' : Coherent z0'
    cohz0' = Coherent-Sup z0'r z0'e comp-re cohz0r cohz0e
    z0'U : finMemC z0' UCode
    z0'U = FinMem-Sup-element z0'r z0'e UCode comp-re tt z0rU (FunEdgeOut.fe-z0'U fe)
    rk-z0' : Le (RANK z0') m
    rk-z0' = Le-trans (RANK z0') (max (RANK z0'r) (RANK z0'e)) m (RANK-Sup z0'r z0'e)
               (Le-max-lub (RANK z0'r) (RANK z0'e) m (FunBuildOut.fb-rkz0' rec) (FunEdgeOut.fe-rk-z0' fe))
    c0-z0' : LeCode c0 z0'
    c0-z0' = LeCode-trans c0 z0'r z0' cc0 cohz0r cohz0' (FunBuildOut.fb-c0z0' rec)
               (LeCode-Sup-left z0'r z0'e comp-re cohz0r cohz0e)
    z0'-d0 : LeCode z0' d0
    z0'-d0 = LeCode-Sup-lub z0'r z0'e d0 (FunBuildOut.fb-z0'd0 rec) (FunEdgeOut.fe-b0 fe)
    z0e-z0' : LeCode z0'e z0'
    z0e-z0' = LeCode-Sup-right z0'r z0'e comp-re cohz0r cohz0e
    z0r-z0' : LeCode z0'r z0'
    z0r-z0' = LeCode-Sup-left z0'r z0'e comp-re cohz0r cohz0e
    -- codomain family zf' = append zf'r {(k', T')}
    feT = cons (mkSigma k' T') nil
    cohfeT : CoherentFunTail feT
    cohfeT = mkCFT ck' cT' (FunEdgeOut.fe-nb-T' fe) tt tt
    comp-zf : CompFun zf'r feT
    comp-zf = CompFun-sym feT zf'r
                (compFun-cap k' T' zf'r df cdf ck' cT' (FunEdgeOut.fe-T'df fe)
                  (FunBuildOut.fb-zfcoh rec) (FunBuildOut.fb-zf-df rec))
    zf' = append zf'r feT
    zfcoh : CoherentFunTail zf'
    zfcoh = CoherentFunTail-append zf'r feT (FunBuildOut.fb-zfcoh rec) cohfeT comp-zf
    zfkeys : FinMemAllU zf' z0'
    zfkeys = allU-from zf' z0'
               (FinMemAllU-append-Sup z0'r z0'e zf'r feT comp-re cohz0r cohz0e z0rU
                 (FunEdgeOut.fe-z0'U fe) (FunBuildOut.fb-zfcoh rec) cohfeT
                 (allU-to zf'r z0'r (FunBuildOut.fb-zfkeys rec))
                 (allU-to feT z0'e
                   (mkSigma (mkSigma (FunEdgeOut.fe-k'z0' fe) (FunEdgeOut.fe-T'U fe)) tt)))
    rk-feT : Le (RANKFun feT) m
    rk-feT = Le-max-lub (RANK k') (max (RANK T') 0) m (FunEdgeOut.fe-rk-k' fe)
               (Le-max-lub (RANK T') 0 m (FunEdgeOut.fe-rk-T' fe) tt)
    rk-zf : Le (RANKFun zf') m
    rk-zf = Le-trans (RANKFun zf') (max (RANKFun zf'r) (RANKFun feT)) m (RANK-append zf'r feT)
              (Le-max-lub (RANKFun zf'r) (RANKFun feT) m (FunBuildOut.fb-rkzf rec) rk-feT)
    cf-zf : LeFunCode cf zf'
    cf-zf = lefun-append-mono-L cf zf'r feT zfcoh comp-zf
              (FunBuildOut.fb-zfcoh rec) cohfeT ccf (FunBuildOut.fb-cf-zf rec)
    zf-df : LeFunCode zf' df
    zf-df = lefun-append-bf zf'r feT df (FunBuildOut.fb-zf-df rec) (mkSigma (FunEdgeOut.fe-T'df fe) tt)
      where
        open import ID.Domain.RankSandwichFam using ( lefun-append-bf )
    -- T' <= EvalFun zf' k'
    czf' : Coherent (EvalFun zf' k')
    czf' = Coherent-EvalFun zf' k' zfcoh ck'
    T'-zf'k' : LeCode T' (EvalFun zf' k')
    T'-zf'k' = fst (lefun-append-mono-R feT zf'r feT zfcoh comp-zf
                     (FunBuildOut.fb-zfcoh rec) cohfeT cohfeT (LeFunCode-refl feT cohfeT))
    -- graph g' = append g'r {(k', w')}
    feW = cons (mkSigma k' w') nil
    cohfeW : CoherentFunTail feW
    cohfeW = mkCFT ck' cw' (FunEdgeOut.fe-nb-w' fe) tt tt
    comp-g : CompFun g'r feW
    comp-g = CompFun-sym feW g'r
               (compFun-cap k' w' g'r gb cgb ck' cw' (FunEdgeOut.fe-w'gb fe)
                 (FunBuildOut.fb-gcoh rec) (FunBuildOut.fb-g-gb rec))
    g' = append g'r feW
    gcoh : CoherentFunTail g'
    gcoh = CoherentFunTail-append g'r feW (FunBuildOut.fb-gcoh rec) cohfeW comp-g
    rk-feW : Le (RANKFun feW) m
    rk-feW = Le-max-lub (RANK k') (max (RANK w') 0) m (FunEdgeOut.fe-rk-k' fe)
               (Le-max-lub (RANK w') 0 m (FunEdgeOut.fe-rk-w' fe) tt)
    rk-g : Le (RANKFun g') m
    rk-g = Le-trans (RANKFun g') (max (RANKFun g'r) (RANKFun feW)) m (RANK-append g'r feW)
             (Le-max-lub (RANKFun g'r) (RANKFun feW) m (FunBuildOut.fb-rkg rec) rk-feW)
    g-gb : LeFunCode g' gb
    g-gb = lefun-append-bf g'r feW gb (FunBuildOut.fb-g-gb rec) (mkSigma (FunEdgeOut.fe-w'gb fe) tt)
      where
        open import ID.Domain.RankSandwichFam using ( lefun-append-bf )
    -- ga <= g'
    k'z0' : finMemC k' z0'
    k'z0' = finMem-upward k' z0'e z0' z0e-z0' cohz0e cohz0' (FunEdgeOut.fe-k'z0' fe) z0'U
    w'-zf'k' : finMemC w' (EvalFun zf' k')
    w'-zf'k' = finMem-upward w' T' (EvalFun zf' k') T'-zf'k' cT' czf'
                 (FunEdgeOut.fe-w'T' fe) (EvalFun-in-UCode zf' k' z0' zfcoh ck' (allU-to zf' z0' zfkeys))
    g'r-typed : FinMemFun g'r z0' zf'
    g'r-typed = finMemFun-upward g'r z0'r z0' zf'r zf' z0r-z0' cohz0r cohz0'
                  (FunBuildOut.fb-zfcoh rec) zfcoh
                  (lefun-append-mono-L zf'r zf'r feT zfcoh comp-zf
                    (FunBuildOut.fb-zfcoh rec) cohfeT (FunBuildOut.fb-zfcoh rec)
                    (LeFunCode-refl zf'r (FunBuildOut.fb-zfcoh rec)))
                  (FunBuildOut.fb-gfun rec) z0'U zfkeys
    feW-typed : FinMemFun feW z0' zf'
    feW-typed = mkSigma (mkSigma k'z0' w'-zf'k') tt
    gfun : FinMemFun g' z0' zf'
    gfun = FinMemFun-append g'r feW z0' zf' g'r-typed feW-typed
    -- ga <= g' : new demand via mono-R, rest via mono-L
    w'-gk_a : LeCode w' (EvalFun feW ka)
    w'-gk_a = edge-le (mkSigma k' w') feW ka cohfeW here cka cw' (FunEdgeOut.fe-k'ka fe)
    demand-feW : LeFunCode (cons kw nil) feW
    demand-feW = mkSigma (LeCode-trans wa w' (EvalFun feW ka) cwa cw'
                            (Coherent-EvalFun feW ka cohfeW cka) (FunEdgeOut.fe-wa-w' fe) w'-gk_a) tt
    ga-g' : LeFunCode (cons kw rest) g'
    ga-g' = mkSigma
              (fst (lefun-append-mono-R (cons kw nil) g'r feW gcoh comp-g
                     (FunBuildOut.fb-gcoh rec) cohfeW
                     (mkCFT cka cwa nbwa tt tt) demand-feW))
              (lefun-append-mono-L rest g'r feW gcoh comp-g
                (FunBuildOut.fb-gcoh rec) cohfeW cohrest (FunBuildOut.fb-ga-g rec))

------------------------------------------------------------------------
-- A graph that dominates a non-Bot demand is non-empty, hence CoherentFun.
------------------------------------------------------------------------
open import ID.Domain.Order using ( NotBot )
open import ID.Domain.Basic using ( FunEl ; PiCode )

toCoherentFun : (g : FinFun) (wa ka : FinEl) ->
  CoherentFunTail g -> LeCode wa (EvalFun g ka) -> NotBot wa -> CoherentFun g
toCoherentFun nil          Bot          ka cft le nb = nb
toCoherentFun nil          UCode        ka cft le nb = le
toCoherentFun nil          (FunEl h)    ka cft le nb = le
toCoherentFun nil          (PiCode a f) ka cft le nb = le
toCoherentFun (cons p ps)  wa ka cft le nb = cft

------------------------------------------------------------------------
-- funShrink: the goodS C clause.  x = FunEl g : PiCode z0 zf in [a,b],
-- type PiCode z0 zf in [c,d]; produce (x', z').
------------------------------------------------------------------------
open import ID.Domain.Basic using ( Empty )
open import ID.Domain.Order using ( LeCode-Bot )
open import ID.Domain.MemUnfold
  using ( finMemC-bot-from
        ; finMemC-funel-fun ; finMemC-funel-coh ; finMemC-funel-wf
        ; finMemC-piU-dom ; finMemC-piU-allU ; finMemC-piU-cft )
open import ID.Domain.Membership using ( finMem-funel-mk )
open import ID.Domain.RankSandwichCore using ( SOut )

exF : {A : Set} -> Empty -> A
exF ()

open import ID.Domain.Order using ( cft-from-cf )
open import ID.Domain.FamU using ( piU-intro )

funShrink : (m : Nat) (ih : SStmt m) (a b c d : FinEl) (z0 : FinEl) (zf g : FinFun) ->
  Le (RANK a) (suc m) -> Le (RANK b) (suc m) -> Le (RANK c) (suc m) -> Le (RANK d) (suc m) ->
  Le (max (RANK z0) (RANKFun zf)) (suc m) -> Le (RANKFun g) (suc m) ->
  Coherent a -> Coherent b -> Coherent c -> Coherent d ->
  CoherentFun g -> Coherent z0 -> CoherentFunTail zf ->
  finMemC z0 UCode -> FinMemAllU zf z0 -> FinMemFun g z0 zf ->
  LeCode a (FunEl g) -> LeCode (FunEl g) b -> LeCode c (PiCode z0 zf) -> LeCode (PiCode z0 zf) d ->
  SOut (suc m) a b c d
-- a = Bot, c = Bot
funShrink m ih Bot (FunEl gb) Bot (PiCode d0 df) z0 zf g
  ra rb rc rd rz rg ca cb cc cd cgF cz0 czf z0U allUzf fmg la lb lc ld =
  mkSigma Bot (mkSigma z' (mkSigma tt (mkSigma rk-z'
    (mkSigma tt (mkSigma tt (mkSigma tt (mkSigma z'-d (finMemC-bot-from z' z'U))))))))
  where
    rz0 = Le-trans (RANK z0) (max (RANK z0) (RANKFun zf)) (suc m) (Le-max-l (RANK z0) (RANKFun zf)) rz
    rzf = Le-trans (RANKFun zf) (max (RANK z0) (RANKFun zf)) (suc m) (Le-max-r (RANK z0) (RANKFun zf)) rz
    rd0 = Le-trans (RANK d0) (max (RANK d0) (RANKFun df)) m (Le-max-l (RANK d0) (RANKFun df)) rd
    rdf = Le-trans (RANKFun df) (max (RANK d0) (RANKFun df)) m (Le-max-r (RANK d0) (RANKFun df)) rd
    fb = funBuild m ih z0 Bot d0 zf gb df g cz0 z0U rz0 tt tt (LeCode-Bot z0) (fst cd) rd0 (fst ld)
           czf allUzf rzf (cft-from-cf gb cb) rb (snd cd) rdf (snd ld)
           (cft-from-cf g cgF) fmg rg lb nil tt tt tt nil tt tt tt
    z0' = FunBuildOut.fbZ0' fb ; zf' = FunBuildOut.fbZf' fb
    z' = PiCode z0' zf'
    z'U = piU-intro z0' zf' (FunBuildOut.fb-z0'U fb) (mkFamToU (FunBuildOut.fb-zfkeys fb) (FunBuildOut.fb-zfcoh fb))
    rk-z' = Le-max-lub (RANK z0') (RANKFun zf') m (FunBuildOut.fb-rkz0' fb) (FunBuildOut.fb-rkzf fb)
    z'-d = mkSigma (FunBuildOut.fb-z0'd0 fb) (FunBuildOut.fb-zf-df fb)
-- a = Bot, c = PiCode c0 cf
funShrink m ih Bot (FunEl gb) (PiCode c0 cf) (PiCode d0 df) z0 zf g
  ra rb rc rd rz rg ca cb cc cd cgF cz0 czf z0U allUzf fmg la lb lc ld =
  mkSigma Bot (mkSigma z' (mkSigma tt (mkSigma rk-z'
    (mkSigma tt (mkSigma tt (mkSigma c-z' (mkSigma z'-d (finMemC-bot-from z' z'U))))))))
  where
    rz0 = Le-trans (RANK z0) (max (RANK z0) (RANKFun zf)) (suc m) (Le-max-l (RANK z0) (RANKFun zf)) rz
    rzf = Le-trans (RANKFun zf) (max (RANK z0) (RANKFun zf)) (suc m) (Le-max-r (RANK z0) (RANKFun zf)) rz
    rc0 = Le-trans (RANK c0) (max (RANK c0) (RANKFun cf)) m (Le-max-l (RANK c0) (RANKFun cf)) rc
    rcf = Le-trans (RANKFun cf) (max (RANK c0) (RANKFun cf)) m (Le-max-r (RANK c0) (RANKFun cf)) rc
    rd0 = Le-trans (RANK d0) (max (RANK d0) (RANKFun df)) m (Le-max-l (RANK d0) (RANKFun df)) rd
    rdf = Le-trans (RANKFun df) (max (RANK d0) (RANKFun df)) m (Le-max-r (RANK d0) (RANKFun df)) rd
    fb = funBuild m ih z0 c0 d0 zf gb df g cz0 z0U rz0 (fst cc) rc0 (fst lc) (fst cd) rd0 (fst ld)
           czf allUzf rzf (cft-from-cf gb cb) rb (snd cd) rdf (snd ld)
           (cft-from-cf g cgF) fmg rg lb cf (snd cc) rcf (snd lc) nil tt tt tt
    z0' = FunBuildOut.fbZ0' fb ; zf' = FunBuildOut.fbZf' fb
    z' = PiCode z0' zf'
    z'U = piU-intro z0' zf' (FunBuildOut.fb-z0'U fb) (mkFamToU (FunBuildOut.fb-zfkeys fb) (FunBuildOut.fb-zfcoh fb))
    rk-z' = Le-max-lub (RANK z0') (RANKFun zf') m (FunBuildOut.fb-rkz0' fb) (FunBuildOut.fb-rkzf fb)
    c-z' = mkSigma (FunBuildOut.fb-c0z0' fb) (FunBuildOut.fb-cf-zf fb)
    z'-d = mkSigma (FunBuildOut.fb-z0'd0 fb) (FunBuildOut.fb-zf-df fb)
-- a = FunEl (cons p ps), c = Bot
funShrink m ih (FunEl (cons p ps)) (FunEl gb) Bot (PiCode d0 df) z0 zf g
  ra rb rc rd rz rg ca cb cc cd cgF cz0 czf z0U allUzf fmg la lb lc ld =
  mkSigma (FunEl g') (mkSigma z' (mkSigma rg' (mkSigma rk-z'
    (mkSigma (FunBuildOut.fb-ga-g fb) (mkSigma (FunBuildOut.fb-g-gb fb)
    (mkSigma tt (mkSigma z'-d x'z')))))))
  where
    rz0 = Le-trans (RANK z0) (max (RANK z0) (RANKFun zf)) (suc m) (Le-max-l (RANK z0) (RANKFun zf)) rz
    rzf = Le-trans (RANKFun zf) (max (RANK z0) (RANKFun zf)) (suc m) (Le-max-r (RANK z0) (RANKFun zf)) rz
    rd0 = Le-trans (RANK d0) (max (RANK d0) (RANKFun df)) m (Le-max-l (RANK d0) (RANKFun df)) rd
    rdf = Le-trans (RANKFun df) (max (RANK d0) (RANKFun df)) m (Le-max-r (RANK d0) (RANKFun df)) rd
    fb = funBuild m ih z0 Bot d0 zf gb df g cz0 z0U rz0 tt tt (LeCode-Bot z0) (fst cd) rd0 (fst ld)
           czf allUzf rzf (cft-from-cf gb cb) rb (snd cd) rdf (snd ld)
           (cft-from-cf g cgF) fmg rg lb nil tt tt tt (cons p ps) ca ra la
    z0' = FunBuildOut.fbZ0' fb ; zf' = FunBuildOut.fbZf' fb ; g' = FunBuildOut.fbG' fb
    z' = PiCode z0' zf'
    z'U = piU-intro z0' zf' (FunBuildOut.fb-z0'U fb) (mkFamToU (FunBuildOut.fb-zfkeys fb) (FunBuildOut.fb-zfcoh fb))
    rk-z' = Le-max-lub (RANK z0') (RANKFun zf') m (FunBuildOut.fb-rkz0' fb) (FunBuildOut.fb-rkzf fb)
    rg' = FunBuildOut.fb-rkg fb
    z'-d = mkSigma (FunBuildOut.fb-z0'd0 fb) (FunBuildOut.fb-zf-df fb)
    cohG' = toCoherentFun g' (snd p) (fst p) (FunBuildOut.fb-gcoh fb) (fst (FunBuildOut.fb-ga-g fb)) (CFTcons.val-nbot ca)
    x'z' = finMem-funel-mk g' z0' zf' (FunBuildOut.fb-gfun fb) cohG' z'U
-- a = FunEl (cons p ps), c = PiCode c0 cf
funShrink m ih (FunEl (cons p ps)) (FunEl gb) (PiCode c0 cf) (PiCode d0 df) z0 zf g
  ra rb rc rd rz rg ca cb cc cd cgF cz0 czf z0U allUzf fmg la lb lc ld =
  mkSigma (FunEl g') (mkSigma z' (mkSigma rg' (mkSigma rk-z'
    (mkSigma (FunBuildOut.fb-ga-g fb) (mkSigma (FunBuildOut.fb-g-gb fb)
    (mkSigma c-z' (mkSigma z'-d x'z')))))))
  where
    rz0 = Le-trans (RANK z0) (max (RANK z0) (RANKFun zf)) (suc m) (Le-max-l (RANK z0) (RANKFun zf)) rz
    rzf = Le-trans (RANKFun zf) (max (RANK z0) (RANKFun zf)) (suc m) (Le-max-r (RANK z0) (RANKFun zf)) rz
    rc0 = Le-trans (RANK c0) (max (RANK c0) (RANKFun cf)) m (Le-max-l (RANK c0) (RANKFun cf)) rc
    rcf = Le-trans (RANKFun cf) (max (RANK c0) (RANKFun cf)) m (Le-max-r (RANK c0) (RANKFun cf)) rc
    rd0 = Le-trans (RANK d0) (max (RANK d0) (RANKFun df)) m (Le-max-l (RANK d0) (RANKFun df)) rd
    rdf = Le-trans (RANKFun df) (max (RANK d0) (RANKFun df)) m (Le-max-r (RANK d0) (RANKFun df)) rd
    fb = funBuild m ih z0 c0 d0 zf gb df g cz0 z0U rz0 (fst cc) rc0 (fst lc) (fst cd) rd0 (fst ld)
           czf allUzf rzf (cft-from-cf gb cb) rb (snd cd) rdf (snd ld)
           (cft-from-cf g cgF) fmg rg lb cf (snd cc) rcf (snd lc) (cons p ps) ca ra la
    z0' = FunBuildOut.fbZ0' fb ; zf' = FunBuildOut.fbZf' fb ; g' = FunBuildOut.fbG' fb
    z' = PiCode z0' zf'
    z'U = piU-intro z0' zf' (FunBuildOut.fb-z0'U fb) (mkFamToU (FunBuildOut.fb-zfkeys fb) (FunBuildOut.fb-zfcoh fb))
    rk-z' = Le-max-lub (RANK z0') (RANKFun zf') m (FunBuildOut.fb-rkz0' fb) (FunBuildOut.fb-rkzf fb)
    rg' = FunBuildOut.fb-rkg fb
    c-z' = mkSigma (FunBuildOut.fb-c0z0' fb) (FunBuildOut.fb-cf-zf fb)
    z'-d = mkSigma (FunBuildOut.fb-z0'd0 fb) (FunBuildOut.fb-zf-df fb)
    cohG' = toCoherentFun g' (snd p) (fst p) (FunBuildOut.fb-gcoh fb) (fst (FunBuildOut.fb-ga-g fb)) (CFTcons.val-nbot ca)
    x'z' = finMem-funel-mk g' z0' zf' (FunBuildOut.fb-gfun fb) cohG' z'U
-- a = FunEl nil : incoherent
funShrink m ih (FunEl nil) (FunEl gb) c d z0 zf g ra rb rc rd rz rg ca cb cc cd cgF cz0 czf z0U allUzf fmg la lb lc ld = exF ca
-- absurd a
funShrink m ih UCode b c d z0 zf g ra rb rc rd rz rg ca cb cc cd cgF cz0 czf z0U allUzf fmg la lb lc ld = exF la
funShrink m ih (PiCode q h) b c d z0 zf g ra rb rc rd rz rg ca cb cc cd cgF cz0 czf z0U allUzf fmg la lb lc ld = exF la
-- absurd c (a = Bot or FunEl, b = FunEl, d = PiCode)
funShrink m ih a (FunEl gb) UCode (PiCode d0 df) z0 zf g ra rb rc rd rz rg ca cb cc cd cgF cz0 czf z0U allUzf fmg la lb lc ld = exF lc
funShrink m ih a (FunEl gb) (FunEl h) (PiCode d0 df) z0 zf g ra rb rc rd rz rg ca cb cc cd cgF cz0 czf z0U allUzf fmg la lb lc ld = exF lc
-- absurd d (b = FunEl)
funShrink m ih a (FunEl gb) c Bot z0 zf g ra rb rc rd rz rg ca cb cc cd cgF cz0 czf z0U allUzf fmg la lb lc ld = exF ld
funShrink m ih a (FunEl gb) c UCode z0 zf g ra rb rc rd rz rg ca cb cc cd cgF cz0 czf z0U allUzf fmg la lb lc ld = exF ld
funShrink m ih a (FunEl gb) c (FunEl h) z0 zf g ra rb rc rd rz rg ca cb cc cd cgF cz0 czf z0U allUzf fmg la lb lc ld = exF ld
-- absurd b
funShrink m ih a Bot c d z0 zf g ra rb rc rd rz rg ca cb cc cd cgF cz0 czf z0U allUzf fmg la lb lc ld = exF lb
funShrink m ih a UCode c d z0 zf g ra rb rc rd rz rg ca cb cc cd cgF cz0 czf z0U allUzf fmg la lb lc ld = exF lb
funShrink m ih a (PiCode q h) c d z0 zf g ra rb rc rd rz rg ca cb cc cd cgF cz0 czf z0U allUzf fmg la lb lc ld = exF lb
