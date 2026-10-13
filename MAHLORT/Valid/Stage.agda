{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Valid/Stage.agda
--
-- The logical relation (two-sided), stratified by a stage index:
--   RT G T T' a       "T = T' as types, at the type code a"
--   RM G M M' T u a   "M = M' : T, at the element u of the code a"
-- Stage (suc k) is built from Stage k; the recursion goes to codes of
-- strictly smaller RANK (domain b, Selection values, EvalFun results,
-- predecessors, pair components), so one stage strips one rank level.
-- The term relation at UCode uses the SAME-stage type relation
-- (no lag).  Public relations at the canonical level.
--
-- Universe clause: both sides reduce to SOME universe (V or U(f,g)).
--
-- Tarski port: an element M of a universe type T is related through
-- its DECODING (El_V M if T reduces to V, El_V (T^ M) if T reduces to
-- U_{f,g}, i.e. the full decoding); the application / projection fields quantify over all
-- convertible annotations (one per side), which makes the relation
-- stable under conversion of the types.
------------------------------------------------------------------------

module MAHLORT.Valid.Stage where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
open import MAHLOINJ.Domain.Basic
  using (Top ; tt ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl ; PairEl ; SigmaCode
        ; FinFun ; max) renaming (suc to nsuc ; zero to nzero ; Nat to Lev)
open import MAHLOINJ.Domain.Kernel using (EvalFun ; RANK)
open import MAHLOINJ.Model.Selection using (Selection)
open import MAHLORT.Valid.HeadRed

------------------------------------------------------------------------
-- relation types
------------------------------------------------------------------------

RTyT : Set1
RTyT = {n : Num} -> Ctx n -> Expr n -> Expr n -> FinEl -> Set

RTmT : Set1
RTmT = {n : Num} -> Ctx n -> Expr n -> Expr n -> Expr n -> FinEl -> FinEl -> Set

Shape : Set
Shape = {n : Num} -> Expr n -> Expr (suc n) -> Expr n

-- universes
data Univ {n : Num} (u : Expr n) : Set where
  univ-V : Eq u V -> Univ u
  univ-U : (f g : Expr n) -> Eq u (TyU f g) -> Univ u

-- the decoding of an element of a universe
decU : {n : Num} {u : Expr n} -> Univ u -> Expr n -> Expr n
decU (univ-V _) M = ElV M
decU (univ-U f g _) M = ElV (That M)

UnivR : {n : Num} -> Ctx n -> Expr n -> Set
UnivR {n} G T = Sg (Expr n) (\ u -> HRs T u * (Univ u * TyEq G T u))

decR : {n : Num} {G : Ctx n} {T : Expr n} -> UnivR G T -> Expr n -> Expr n
decR w M = decU (fst (snd (snd w))) M

-- universes of the same kind (both V, or both some U_{f,g})
data SameK {n : Num} {u u' : Expr n} : Univ u -> Univ u' -> Set where
  kV : {e : Eq u V} {e' : Eq u' V} -> SameK (univ-V e) (univ-V e')
  kU : {f g f' g' : Expr n} {e : Eq u (TyU f g)} {e' : Eq u' (TyU f' g')} -> SameK (univ-U f g e) (univ-U f' g' e')

kindR : {n : Num} {G : Ctx n} {T : Expr n} (w : UnivR G T) -> Univ (fst w)
kindR w = fst (snd (snd w))

-- two universe types related as types: same kind
record UnivR2 {n : Num} (G : Ctx n) (T T' : Expr n) : Set where
  constructor univR2
  field
    wl : UnivR G T
    wr : UnivR G T'
    sk : SameK (kindR wl) (kindR wr)

-- elements of a universe: related decodings
UTm : RTyT -> {n : Num} -> Ctx n -> Expr n -> Expr n -> Expr n -> FinEl -> Set
UTm RT G M M' T x = Sg (UnivR G T) (\ w -> RT G (decR w M) (decR w M') x)

NatR : {n : Num} -> Ctx n -> Expr n -> Set
NatR G T = HRs T Nat * TyEq G T Nat

-- an element reducing to 0, with its conversion
ZeroR : {n : Num} -> Ctx n -> Expr n -> Set
ZeroR G M = HRs M Zero * ConvTm G M Zero Nat

------------------------------------------------------------------------
-- clause records
------------------------------------------------------------------------

record CodeTy (S : Shape) (RT : RTyT) (RM : RTmT) {n : Num} (G : Ctx n) (T T' : Expr n)
  (b : FinEl) (f : FinFun) : Set where
  constructor mkCodeTy
  field
    A A'  : Expr n
    B B'  : Expr (suc n)
    rT    : HRs T (S A B)
    rT'   : HRs T' (S A' B')
    tT    : TyEq G T (S A B)
    tT'   : TyEq G T' (S A' B')
    iA    : IsType G A
    iB    : IsType (extend G A) B
    iA'   : IsType G A'
    iB'   : IsType (extend G A') B'
    eA    : TyEq G A A'
    eB    : TyEq (extend G A) B B'
    dom   : RT G A A' b
    cod   : (w c : FinEl) -> Selection f w c -> (N N' : Expr n) -> ConvTm G N N' A ->
            RM G N N' A w b -> RT G (subst1 B N) (subst1 B' N') c

record PiTm (RM : RTmT) {n : Num} (G : Ctx n) (M M' T : Expr n) (g : FinFun) (b : FinEl) (f : FinFun) : Set where
  constructor mkPiTm
  field
    A   : Expr n
    B   : Expr (suc n)
    rT  : HRs T (PiB A B)
    tT  : TyEq G T (PiB A B)
    iA  : IsType G A
    iB  : IsType (extend G A) B
    app : (w v : FinEl) -> Selection g w v ->
          (A0 A1 : Expr n) (B0 B1 : Expr (suc n)) ->
          TyEq G A A0 -> TyEq (extend G A) B B0 -> TyEq G A A1 -> TyEq (extend G A) B B1 ->
          (N N' : Expr n) -> ConvTm G N N' A ->
          RM G N N' A w b -> RM G (appB A0 B0 M N) (appB A1 B1 M' N') (subst1 B N) v (EvalFun f w)

record SigTm (RM : RTmT) {n : Num} (G : Ctx n) (M M' T : Expr n) (u1 u2 b : FinEl) (f : FinFun) : Set where
  constructor mkSigTm
  field
    A    : Expr n
    B    : Expr (suc n)
    rT   : HRs T (SigmaB A B)
    tT   : TyEq G T (SigmaB A B)
    iA   : IsType G A
    iB   : IsType (extend G A) B
    cF   : (A0 A1 : Expr n) (B0 B1 : Expr (suc n)) ->
           TyEq G A A0 -> TyEq (extend G A) B B0 -> TyEq G A A1 -> TyEq (extend G A) B B1 ->
           ConvTm G (Fst A0 (Lam A0 B0) M) (Fst A1 (Lam A1 B1) M') A
    fstR : (A0 A1 : Expr n) (B0 B1 : Expr (suc n)) ->
           TyEq G A A0 -> TyEq (extend G A) B B0 -> TyEq G A A1 -> TyEq (extend G A) B B1 ->
           RM G (Fst A0 (Lam A0 B0) M) (Fst A1 (Lam A1 B1) M') A u1 b
    sndR : (A0 A1 : Expr n) (B0 B1 : Expr (suc n)) ->
           TyEq G A A0 -> TyEq (extend G A) B B0 -> TyEq G A A1 -> TyEq (extend G A) B B1 ->
           RM G (Snd A0 (Lam A0 B0) M) (Snd A1 (Lam A1 B1) M') (subst1 B (Fst A (Lam A B) M)) u2 (EvalFun f u1)

record SucTm (RM : RTmT) {n : Num} (G : Ctx n) (M M' : Expr n) (v : FinEl) : Set where
  constructor mkSucTm
  field
    P P' : Expr n
    rM   : HRs M (Suc P)
    rM'  : HRs M' (Suc P')
    cM   : ConvTm G M (Suc P) Nat
    cM'  : ConvTm G M' (Suc P') Nat
    cP   : ConvTm G P P' Nat
    pred : RM G P P' Nat v NatCode

------------------------------------------------------------------------
-- stages
------------------------------------------------------------------------

record Pack : Set1 where
  field
    RT : RTyT
    RM : RTmT

trivPack : Pack
trivPack = record { RT = \ _ _ _ _ -> Top ; RM = \ _ _ _ _ _ _ -> Top }

build : Pack -> Pack
build P = record { RT = rt ; RM = rm }
  where
    open Pack P renaming (RT to RTp ; RM to RMp)

    rt : RTyT
    rt G T T' Bot             = Top
    rt G T T' UCode           = UnivR2 G T T'
    rt G T T' (FunEl _)       = Empty
    rt G T T' (PiCode b f)    = CodeTy PiB RTp RMp G T T' b f
    rt G T T' NatCode         = NatR G T * NatR G T'
    rt G T T' ZeroEl          = Empty
    rt G T T' (SucEl _)       = Empty
    rt G T T' (PairEl _ _)    = Empty
    rt G T T' (SigmaCode b f) = CodeTy SigmaB RTp RMp G T T' b f

    rm : RTmT
    rm G M M' T Bot a = Top
    rm G M M' T UCode Bot = Top
    rm G M M' T UCode UCode = UTm rt G M M' T UCode
    rm G M M' T UCode (FunEl _) = Top
    rm G M M' T UCode (PiCode _ _) = Empty
    rm G M M' T UCode NatCode = Empty
    rm G M M' T UCode ZeroEl = Top
    rm G M M' T UCode (SucEl _) = Top
    rm G M M' T UCode (PairEl _ _) = Top
    rm G M M' T UCode (SigmaCode _ _) = Empty
    rm G M M' T (FunEl _) Bot = Top
    rm G M M' T (FunEl g) UCode = UTm rt G M M' T (FunEl g)
    rm G M M' T (FunEl _) (FunEl _) = Top
    rm G M M' T (FunEl g) (PiCode b f) = PiTm RMp G M M' T g b f
    rm G M M' T (FunEl _) NatCode = Empty
    rm G M M' T (FunEl _) ZeroEl = Top
    rm G M M' T (FunEl _) (SucEl _) = Top
    rm G M M' T (FunEl _) (PairEl _ _) = Top
    rm G M M' T (FunEl _) (SigmaCode _ _) = Empty
    rm G M M' T (PiCode _ _) Bot = Top
    rm G M M' T (PiCode b f) UCode = UTm rt G M M' T (PiCode b f)
    rm G M M' T (PiCode _ _) (FunEl _) = Top
    rm G M M' T (PiCode _ _) (PiCode _ _) = Empty
    rm G M M' T (PiCode _ _) NatCode = Empty
    rm G M M' T (PiCode _ _) ZeroEl = Top
    rm G M M' T (PiCode _ _) (SucEl _) = Top
    rm G M M' T (PiCode _ _) (PairEl _ _) = Top
    rm G M M' T (PiCode _ _) (SigmaCode _ _) = Empty
    rm G M M' T NatCode Bot = Top
    rm G M M' T NatCode UCode = UTm rt G M M' T NatCode
    rm G M M' T NatCode (FunEl _) = Top
    rm G M M' T NatCode (PiCode _ _) = Empty
    rm G M M' T NatCode NatCode = Empty
    rm G M M' T NatCode ZeroEl = Top
    rm G M M' T NatCode (SucEl _) = Top
    rm G M M' T NatCode (PairEl _ _) = Top
    rm G M M' T NatCode (SigmaCode _ _) = Empty
    rm G M M' T ZeroEl Bot = Top
    rm G M M' T ZeroEl UCode = UTm rt G M M' T ZeroEl
    rm G M M' T ZeroEl (FunEl _) = Top
    rm G M M' T ZeroEl (PiCode _ _) = Empty
    rm G M M' T ZeroEl NatCode = TyEq G T Nat * (ZeroR G M * ZeroR G M')
    rm G M M' T ZeroEl ZeroEl = Top
    rm G M M' T ZeroEl (SucEl _) = Top
    rm G M M' T ZeroEl (PairEl _ _) = Top
    rm G M M' T ZeroEl (SigmaCode _ _) = Empty
    rm G M M' T (SucEl _) Bot = Top
    rm G M M' T (SucEl v) UCode = UTm rt G M M' T (SucEl v)
    rm G M M' T (SucEl _) (FunEl _) = Top
    rm G M M' T (SucEl _) (PiCode _ _) = Empty
    rm G M M' T (SucEl v) NatCode = TyEq G T Nat * SucTm RMp G M M' v
    rm G M M' T (SucEl _) ZeroEl = Top
    rm G M M' T (SucEl _) (SucEl _) = Top
    rm G M M' T (SucEl _) (PairEl _ _) = Top
    rm G M M' T (SucEl _) (SigmaCode _ _) = Empty
    rm G M M' T (PairEl _ _) Bot = Top
    rm G M M' T (PairEl u1 u2) UCode = UTm rt G M M' T (PairEl u1 u2)
    rm G M M' T (PairEl _ _) (FunEl _) = Top
    rm G M M' T (PairEl _ _) (PiCode _ _) = Empty
    rm G M M' T (PairEl _ _) NatCode = Empty
    rm G M M' T (PairEl _ _) ZeroEl = Top
    rm G M M' T (PairEl _ _) (SucEl _) = Top
    rm G M M' T (PairEl _ _) (PairEl _ _) = Top
    rm G M M' T (PairEl u1 u2) (SigmaCode b f) = SigTm RMp G M M' T u1 u2 b f
    rm G M M' T (SigmaCode _ _) Bot = Top
    rm G M M' T (SigmaCode b f) UCode = UTm rt G M M' T (SigmaCode b f)
    rm G M M' T (SigmaCode _ _) (FunEl _) = Top
    rm G M M' T (SigmaCode _ _) (PiCode _ _) = Empty
    rm G M M' T (SigmaCode _ _) NatCode = Empty
    rm G M M' T (SigmaCode _ _) ZeroEl = Top
    rm G M M' T (SigmaCode _ _) (SucEl _) = Top
    rm G M M' T (SigmaCode _ _) (PairEl _ _) = Top
    rm G M M' T (SigmaCode _ _) (SigmaCode _ _) = Empty

Stage : Lev -> Pack
Stage nzero    = trivPack
Stage (nsuc k) = build (Stage k)

module St (k : Lev) = Pack (Stage k)

------------------------------------------------------------------------
-- public relations at the canonical level
------------------------------------------------------------------------

RTy : RTyT
RTy G T T' a = St.RT (nsuc (RANK a)) G T T' a

RTm : RTmT
RTm G M M' T u a = St.RM (nsuc (max (RANK u) (RANK a))) G M M' T u a

------------------------------------------------------------------------
-- universes: determinism of the kind, and the decoding
------------------------------------------------------------------------

private
  noredU : {n : Num} {u : Expr n} -> Univ u -> NoRed u
  noredU (univ-V refl) = nored-V
  noredU (univ-U f g refl) = nored-TyU

  V-TyU : {n : Num} {f g : Expr n} -> Eq V (TyU f g) -> Empty
  V-TyU ()

  kindSame : {n : Num} {u u' : Expr n} -> Eq u u' -> (k : Univ u) (k' : Univ u') -> SameK k k'
  kindSame e (univ-V e1) (univ-V e2) = kV
  kindSame e (univ-V e1) (univ-U f g e2) = Empty-elim (V-TyU (Eq-trans (Eq-sym e1) (Eq-trans e e2)))
  kindSame e (univ-U f g e1) (univ-V e2) = Empty-elim (V-TyU (Eq-trans (Eq-sym e2) (Eq-trans (Eq-sym e) e1)))
  kindSame e (univ-U f g e1) (univ-U f' g' e2) = kU

kind-det : {n : Num} {G : Ctx n} {T : Expr n} (w1 w2 : UnivR G T) -> SameK (kindR w1) (kindR w2)
kind-det w1 w2 =
  kindSame (HRs-det (fst (snd w1)) (fst (snd w2)) (noredU (kindR w1)) (noredU (kindR w2))) (kindR w1) (kindR w2)

sk-sym : {n : Num} {u u' : Expr n} {k : Univ u} {k' : Univ u'} -> SameK k k' -> SameK k' k
sk-sym kV = kV
sk-sym kU = kU

sk-trans : {n : Num} {u u' u'' : Expr n} {k : Univ u} {k' : Univ u'} {k'' : Univ u''} ->
  SameK k k' -> SameK k' k'' -> SameK k k''
sk-trans kV kV = kV
sk-trans kU kU = kU

decSame : {n : Num} {u u' : Expr n} {k : Univ u} {k' : Univ u'} -> SameK k k' -> (M : Expr n) -> Eq (decU k M) (decU k' M)
decSame kV M = refl
decSame kU M = refl

decR-det : {n : Num} {G : Ctx n} {T : Expr n} (w1 w2 : UnivR G T) (M : Expr n) -> Eq (decR w1 M) (decR w2 M)
decR-det w1 w2 = decSame (kind-det w1 w2)

-- moving a relation between decodings along the universe witnesses
realignU : {n : Num} {G : Ctx n} {T M M' : Expr n} (P : Expr n -> Expr n -> Set) (w w' : UnivR G T) ->
  P (decR w M) (decR w M') -> P (decR w' M) (decR w' M')
realignU {M = M} {M'} P w w' p = transport2 P (decR-det w w' M) (decR-det w w' M') p

convU : {n : Num} {G : Ctx n} {T T' M M' : Expr n} (P : Expr n -> Expr n -> Set) (vt : UnivR2 G T T') (w : UnivR G T) ->
  P (decR w M) (decR w M') -> P (decR (UnivR2.wr vt) M) (decR (UnivR2.wr vt) M')
convU {M = M} {M'} P vt w p =
  transport2 P (decSame (UnivR2.sk vt) M) (decSame (UnivR2.sk vt) M') (realignU P w (UnivR2.wl vt) p)
