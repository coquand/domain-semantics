{-# OPTIONS --without-K --exact-split #-}
------------------------------------------------------------------------
-- RankSandwichFun.agda  (MIN/ -- Pi + U fragment)
--
-- Building blocks for the function-element couple (Lemma S case C).
-- typedKeyJoinFun: the typed key-join for a member GRAPH g : z0 -> zf,
-- returning the firing-key join  kx : z0  together with the application
-- value  v : EvalFun zf kx  (the dependent codomain value).
------------------------------------------------------------------------
module MIN.Domain.RankSandwichFun where

open import MIN.Domain.Basic
  using ( Nat ; max ; Le ; Le-trans ; Le-max-l ; Le-max-r ; tt
        ; FinEl ; FinFun ; Bot ; UCode ; cons
        ; Pair ; Sigma ; mkSigma ; fst ; snd ; Eq ; Eq-transport )
open import MIN.Domain.Order
  using ( RANK ; RANKFun ; Sup ; Coherent ; CoherentFunTail ; EvalFun
        ; LeCode ; LeFunCode ; LeCode-trans ; RANK-Sup ; Le-max-lub
        ; Coherent-EvalFun ; LeFunCode-refl )
open import MIN.Model.Selection using ( Selection-le-EvalFun )
open import MIN.Domain.MemStage using ( finMemC )
open import MIN.Domain.Membership using ( FinMemFun ; FinMemAllU )
open import MIN.Domain.MemUnfold using ( FinMem-coh-u )
open import MIN.Model.Selection
  using ( Edge ; Selection ; sel-nil ; sel-skip ; sel-take
        ; selectionBelow ; Coherent-Selection
        ; FinMem-Selection ; FinMem-Selection-codomain )
open import MIN.Domain.KeyJoinLemma using ( sel-rank ; tail-le )

-- value-side: RANK (snd p) <= RANKFun (cons p g).
val-le : (p : Edge) (g : FinFun) -> Le (RANK (snd p)) (RANKFun (cons p g))
val-le p g =
  Le-trans (RANK (snd p)) (max (RANK (snd p)) (RANKFun g)) (RANKFun (cons p g))
    (Le-max-l (RANK (snd p)) (RANKFun g))
    (Le-max-r (RANK (fst p)) (max (RANK (snd p)) (RANKFun g)))

-- the selection codomain has rank <= RANKFun of the function.
sel-rank-cod : {l : FinFun} {u v : FinEl} -> Selection l u v -> Le (RANK v) (RANKFun l)
sel-rank-cod sel-nil = tt
sel-rank-cod (sel-skip {p} {g} {u} {v} sel) =
  Le-trans (RANK v) (RANKFun g) (RANKFun (cons p g)) (sel-rank-cod sel) (tail-le p g)
sel-rank-cod (sel-take {p} {u} {v} {g} ck cv sel) =
  Le-trans (RANK (Sup (snd p) v)) (max (RANK (snd p)) (RANK v)) (RANKFun (cons p g))
    (RANK-Sup (snd p) v)
    (Le-max-lub (RANK (snd p)) (RANK v) (RANKFun (cons p g))
      (val-le p g)
      (Le-trans (RANK v) (RANKFun g) (RANKFun (cons p g)) (sel-rank-cod sel) (tail-le p g)))

------------------------------------------------------------------------
-- typedKeyJoinFun.
------------------------------------------------------------------------
typedKeyJoinFun : (g : FinFun) (z0 : FinEl) (zf : FinFun) (x w : FinEl) ->
  CoherentFunTail g -> Coherent x -> Coherent w ->
  Coherent z0 -> finMemC z0 UCode -> CoherentFunTail zf -> FinMemAllU zf z0 ->
  FinMemFun g z0 zf ->
  LeCode w (EvalFun g x) ->
  Sigma FinEl (\ kx -> Sigma FinEl (\ v ->
    Pair (LeCode kx x)
    (Pair (Le (RANK kx) (RANKFun g))
    (Pair (LeCode w v)
    (Pair (Le (RANK v) (RANKFun g))
    (Pair (finMemC kx z0)
    (Pair (finMemC v (EvalFun zf kx))
    (Pair (Coherent kx) (Pair (Coherent v) (LeCode v (EvalFun g kx)))))))))))
typedKeyJoinFun g z0 zf x w cg cx cw cz0 z0U czf allUzf fmg lwgx =
  mkSigma kx (mkSigma v (mkSigma lkxx (mkSigma rkkx (mkSigma w-v
    (mkSigma rkv (mkSigma kxz0 (mkSigma vcod (mkSigma ckx (mkSigma cv v-gkx)))))))))
  where
    sb  = selectionBelow g x cg cx
    kx  = fst sb
    v   = fst (snd sb)
    sel : Selection g kx v
    sel = fst (snd (snd sb))
    lkxx : LeCode kx x
    lkxx = fst (snd (snd (snd sb)))
    eqv : Eq (EvalFun g x) v
    eqv = snd (snd (snd (snd sb)))
    ckx : Coherent kx
    ckx = Coherent-Selection sel cg
    rkkx : Le (RANK kx) (RANKFun g)
    rkkx = sel-rank sel
    rkv : Le (RANK v) (RANKFun g)
    rkv = sel-rank-cod sel
    kxz0 : finMemC kx z0
    kxz0 = FinMem-Selection z0 zf sel fmg cg cz0 z0U
    vcod : finMemC v (EvalFun zf kx)
    vcod = FinMem-Selection-codomain z0 zf sel fmg cg czf allUzf
    cv : Coherent v
    cv = FinMem-coh-u v (EvalFun zf kx) vcod
    w-v : LeCode w v
    w-v = Eq-transport (\ z -> LeCode w z) eqv lwgx
    v-gkx : LeCode v (EvalFun g kx)
    v-gkx = Selection-le-EvalFun {g} {kx} {v} g sel (LeFunCode-refl g cg) cg cg ckx

------------------------------------------------------------------------
-- funEdge: reduce one ga-demand (ka, wa) of the member graph g, coupled
-- with its dependent codomain.  Produces a reduced graph edge (k' |-> w')
-- AND the reduced codomain type T' with w' : T'.
------------------------------------------------------------------------
open import MIN.Domain.Basic using ( zero ; suc ; Bot )
open import MIN.Domain.Order
  using ( NotBot ; Comp ; EvalFun-mon ; EvalFun-mon-arg ; LeCode-Comp ; Coherent-Sup
        ; LeCode-Sup-left ; LeCode-Sup-right ; LeCode-Sup-lub )
open import MIN.Domain.Basic using ( FunEl ; PiCode )
open import MIN.Domain.MemProps using ( finMem-upward ; EvalFun-in-UCode )
open import MIN.Domain.MemUnfold using ( FinMem-a-in-U )
open import MIN.Domain.Membership using ( allU-to )
open import MIN.Domain.KeyJoinLemma using ( keyJoinLemma )
open import MIN.Domain.RankSandwichCore using ( SStmt ; SOut ; RANK-EvalFun ; notbot-le )

-- a non-Bot member forces a non-Bot type.
notbot-type : (w T : FinEl) -> finMemC w T -> NotBot w -> NotBot T
notbot-type Bot          Bot          mem nbw = nbw
notbot-type UCode        Bot          ()  nbw
notbot-type (FunEl g)    Bot          ()  nbw
notbot-type (PiCode a f) Bot          ()  nbw
notbot-type w UCode        mem nbw = tt
notbot-type w (FunEl g)    mem nbw = tt
notbot-type w (PiCode a f) mem nbw = tt

record FunEdgeOut (m : Nat) (lo b0 : FinEl) (gb df : FinFun) (ka wa : FinEl) : Set where
  constructor mkFunEdgeOut
  field
    feZ0' feK' feT' feW' : FinEl
    fe-z0'U : finMemC feZ0' UCode
    fe-rk-z0' : Le (RANK feZ0') m
    fe-lo : LeCode lo feZ0'
    fe-b0 : LeCode feZ0' b0
    fe-k'z0' : finMemC feK' feZ0'
    fe-rk-k' : Le (RANK feK') m
    fe-k'ka : LeCode feK' ka
    fe-T'U : finMemC feT' UCode
    fe-rk-T' : Le (RANK feT') m
    fe-T'df : LeCode feT' (EvalFun df feK')
    fe-w'T' : finMemC feW' feT'
    fe-rk-w' : Le (RANK feW') m
    fe-wa-w' : LeCode wa feW'
    fe-w'gb : LeCode feW' (EvalFun gb feK')
    fe-ck' : Coherent feK'
    fe-cT' : Coherent feT'
    fe-cw' : Coherent feW'
    fe-nb-w' : NotBot feW'
    fe-nb-T' : NotBot feT'

funEdge : (m : Nat) (ih : SStmt m)
  (z0 lo b0 : FinEl) (zf g gb df : FinFun) (ka wa : FinEl) ->
  Coherent z0 -> finMemC z0 UCode -> Le (RANK z0) (suc m) ->
  Coherent lo -> Le (RANK lo) m -> LeCode lo z0 ->
  Coherent b0 -> Le (RANK b0) m -> LeCode z0 b0 ->
  CoherentFunTail zf -> FinMemAllU zf z0 -> Le (RANKFun zf) (suc m) ->
  CoherentFunTail g -> FinMemFun g z0 zf -> Le (RANKFun g) (suc m) ->
  CoherentFunTail gb -> Le (RANKFun gb) m -> LeFunCode g gb ->
  CoherentFunTail df -> Le (RANKFun df) m -> LeFunCode zf df ->
  Coherent ka -> Le (RANK ka) m -> Coherent wa -> Le (RANK wa) m -> NotBot wa ->
  LeCode wa (EvalFun g ka) ->
  FunEdgeOut m lo b0 gb df ka wa
funEdge m ih z0 lo b0 zf g gb df ka wa
  cz0 z0U rz0 clo rlo loz0 cb0 rb0 z0b0
  czf allUzf rzf cg fmg rg cgb rgb ggb cdf rdf zfdf
  cka rka cwa rwa nbwa wa-gka =
  mkFunEdgeOut z0' k' T' w'
    z0'U rk-z0' lo-z0' z0'-b0 k'z0' rk-k' k'-ka
    T'U rk-T' T'-df w'T' rk-w' wa-w' w'-gb ck' cT' cw' nb-w' nb-T'
  where
    tkj = typedKeyJoinFun g z0 zf ka wa cg cka cwa cz0 z0U czf allUzf fmg wa-gka
    kx = fst tkj
    v  = fst (snd tkj)
    kx-ka : LeCode kx ka
    kx-ka = fst (snd (snd tkj))
    rk-kx0 = fst (snd (snd (snd tkj)))
    wa-v : LeCode wa v
    wa-v = fst (snd (snd (snd (snd tkj))))
    rk-v0 = fst (snd (snd (snd (snd (snd tkj)))))
    kxz0 : finMemC kx z0
    kxz0 = fst (snd (snd (snd (snd (snd (snd tkj))))))
    vcod : finMemC v (EvalFun zf kx)
    vcod = fst (snd (snd (snd (snd (snd (snd (snd tkj)))))))
    ckx : Coherent kx
    ckx = fst (snd (snd (snd (snd (snd (snd (snd (snd tkj))))))))
    cv : Coherent v
    cv = fst (snd (snd (snd (snd (snd (snd (snd (snd (snd tkj)))))))))
    v-gkx : LeCode v (EvalFun g kx)
    v-gkx = snd (snd (snd (snd (snd (snd (snd (snd (snd (snd tkj)))))))))
    T0U : finMemC (EvalFun zf kx) UCode
    T0U = EvalFun-in-UCode zf kx z0 czf ckx (allU-to zf z0 allUzf)
    cT0 : Coherent (EvalFun zf kx)
    cT0 = Coherent-EvalFun zf kx czf ckx
    rk-kx : Le (RANK kx) (suc m)
    rk-kx = Le-trans (RANK kx) (RANKFun g) (suc m) rk-kx0 rg
    rk-v : Le (RANK v) (suc m)
    rk-v = Le-trans (RANK v) (RANKFun g) (suc m) rk-v0 rg
    rk-T0 : Le (RANK (EvalFun zf kx)) (suc m)
    rk-T0 = Le-trans (RANK (EvalFun zf kx)) (RANKFun zf) (suc m) (RANK-EvalFun zf kx) rzf
    v-gbkx : LeCode v (EvalFun gb kx)
    v-gbkx = LeCode-trans v (EvalFun g kx) (EvalFun gb kx) cv
               (Coherent-EvalFun g kx cg ckx) (Coherent-EvalFun gb kx cgb ckx)
               v-gkx (EvalFun-mon g gb kx cg cgb ckx ggb)
    T0-dfkx : LeCode (EvalFun zf kx) (EvalFun df kx)
    T0-dfkx = EvalFun-mon zf df kx czf cdf ckx zfdf
    kjg = keyJoinLemma gb kx v cgb ckx cv v-gbkx
    mug = fst kjg
    mug-kx = fst (snd kjg)
    v-gbmug = fst (snd (snd (snd kjg)))
    cmug = snd (snd (snd (snd kjg)))
    rk-mug0 = fst (snd (snd kjg))
    kjd = keyJoinLemma df kx (EvalFun zf kx) cdf ckx cT0 T0-dfkx
    mud = fst kjd
    mud-kx = fst (snd kjd)
    T0-dfmud = fst (snd (snd (snd kjd)))
    cmud = snd (snd (snd (snd kjd)))
    rk-mud0 = fst (snd (snd kjd))
    comp-gd : Comp mug mud
    comp-gd = LeCode-Comp mug mud kx ckx mug-kx mud-kx
    mu = Sup mug mud
    cmu : Coherent mu
    cmu = Coherent-Sup mug mud comp-gd cmug cmud
    mu-kx : LeCode mu kx
    mu-kx = LeCode-Sup-lub mug mud kx mug-kx mud-kx
    rk-mu : Le (RANK mu) m
    rk-mu = Le-trans (RANK mu) (max (RANK mug) (RANK mud)) m (RANK-Sup mug mud)
              (Le-max-lub (RANK mug) (RANK mud) m
                (Le-trans (RANK mug) (RANKFun gb) m rk-mug0 rgb)
                (Le-trans (RANK mud) (RANKFun df) m rk-mud0 rdf))
    mug-mu : LeCode mug mu
    mug-mu = LeCode-Sup-left mug mud comp-gd cmug cmud
    mud-mu : LeCode mud mu
    mud-mu = LeCode-Sup-right mug mud comp-gd cmug cmud
    keyred = ih mu ka lo b0 kx z0 rk-mu rka rlo rb0 rk-kx rz0
                cmu cka clo cb0 ckx cz0 mu-kx kx-ka loz0 z0b0 kxz0
    k'  = fst keyred
    z0' = fst (snd keyred)
    krest = snd (snd keyred)
    rk-k' : Le (RANK k') m
    rk-k' = fst krest
    rk-z0' : Le (RANK z0') m
    rk-z0' = fst (snd krest)
    mu-k' : LeCode mu k'
    mu-k' = fst (snd (snd krest))
    k'-ka : LeCode k' ka
    k'-ka = fst (snd (snd (snd krest)))
    lo-z0' : LeCode lo z0'
    lo-z0' = fst (snd (snd (snd (snd krest))))
    z0'-b0 : LeCode z0' b0
    z0'-b0 = fst (snd (snd (snd (snd (snd krest)))))
    k'z0' : finMemC k' z0'
    k'z0' = snd (snd (snd (snd (snd (snd krest)))))
    ck' : Coherent k'
    ck' = FinMem-coh-u k' z0' k'z0'
    z0'U : finMemC z0' UCode
    z0'U = FinMem-a-in-U k' z0' k'z0'
    cgbk' : Coherent (EvalFun gb k')
    cgbk' = Coherent-EvalFun gb k' cgb ck'
    cdfk' : Coherent (EvalFun df k')
    cdfk' = Coherent-EvalFun df k' cdf ck'
    rk-gbk' : Le (RANK (EvalFun gb k')) m
    rk-gbk' = Le-trans (RANK (EvalFun gb k')) (RANKFun gb) m (RANK-EvalFun gb k') rgb
    rk-dfk' : Le (RANK (EvalFun df k')) m
    rk-dfk' = Le-trans (RANK (EvalFun df k')) (RANKFun df) m (RANK-EvalFun df k') rdf
    v-gbk' : LeCode v (EvalFun gb k')
    v-gbk' = LeCode-trans v (EvalFun gb mug) (EvalFun gb k') cv
               (Coherent-EvalFun gb mug cgb cmug) cgbk' v-gbmug
               (EvalFun-mon-arg gb mug k' (LeCode-trans mug mu k' cmug cmu ck' mug-mu mu-k')
                 cgb cmug ck')
    T0-dfk' : LeCode (EvalFun zf kx) (EvalFun df k')
    T0-dfk' = LeCode-trans (EvalFun zf kx) (EvalFun df mud) (EvalFun df k') cT0
                (Coherent-EvalFun df mud cdf cmud) cdfk' T0-dfmud
                (EvalFun-mon-arg df mud k' (LeCode-trans mud mu k' cmud cmu ck' mud-mu mu-k')
                  cdf cmud ck')
    valred = ih wa (EvalFun gb k') Bot (EvalFun df k') v (EvalFun zf kx)
                rwa rk-gbk' tt rk-dfk' rk-v rk-T0
                cwa cgbk' tt cdfk' cv cT0
                wa-v v-gbk' tt T0-dfk' vcod
    w'  = fst valred
    T'  = fst (snd valred)
    vrest = snd (snd valred)
    rk-w' : Le (RANK w') m
    rk-w' = fst vrest
    rk-T' : Le (RANK T') m
    rk-T' = fst (snd vrest)
    wa-w' : LeCode wa w'
    wa-w' = fst (snd (snd vrest))
    w'-gb : LeCode w' (EvalFun gb k')
    w'-gb = fst (snd (snd (snd vrest)))
    T'-df : LeCode T' (EvalFun df k')
    T'-df = fst (snd (snd (snd (snd (snd vrest)))))
    w'T' : finMemC w' T'
    w'T' = snd (snd (snd (snd (snd (snd vrest)))))
    cw' : Coherent w'
    cw' = FinMem-coh-u w' T' w'T'
    T'U : finMemC T' UCode
    T'U = FinMem-a-in-U w' T' w'T'
    cT' : Coherent T'
    cT' = FinMem-coh-u T' UCode T'U
    nb-w' : NotBot w'
    nb-w' = notbot-le wa w' wa-w' nbwa
    nb-T' : NotBot T'
    nb-T' = notbot-type w' T' w'T' nb-w'
