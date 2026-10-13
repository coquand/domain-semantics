{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Valid/Stage.agda
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
------------------------------------------------------------------------

module MAHLOINJ.Valid.Stage where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLO.Syntax
open import MAHLO.Typing
open import MAHLOINJ.Domain.Basic
  using (Top ; tt ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl ; PairEl ; SigmaCode
        ; FinFun ; max) renaming (suc to nsuc ; zero to nzero ; Nat to Lev)
open import MAHLOINJ.Domain.Kernel using (EvalFun ; RANK)
open import MAHLOINJ.Model.Selection using (Selection)
open import MAHLOINJ.Valid.HeadRed

------------------------------------------------------------------------
-- relation types
------------------------------------------------------------------------

RTyT : Set1
RTyT = {n : Num} -> Ctx n -> Expr n -> Expr n -> FinEl -> Set

RTmT : Set1
RTmT = {n : Num} -> Ctx n -> Expr n -> Expr n -> Expr n -> FinEl -> FinEl -> Set

Shape : Set
Shape = {n : Num} -> Expr n -> Expr (suc n) -> Expr n

UnivR : {n : Num} -> Ctx n -> Expr n -> Set
UnivR {n} G T = Sg (Expr n) (\ u -> HRs T u * (Univ u * TyEq G T u))

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
    app : (w v : FinEl) -> Selection g w v -> (N N' : Expr n) -> ConvTm G N N' A ->
          RM G N N' A w b -> RM G (App M N) (App M' N') (subst1 B N) v (EvalFun f w)

record SigTm (RM : RTmT) {n : Num} (G : Ctx n) (M M' T : Expr n) (u1 u2 b : FinEl) (f : FinFun) : Set where
  constructor mkSigTm
  field
    A    : Expr n
    B    : Expr (suc n)
    rT   : HRs T (SigmaB A B)
    tT   : TyEq G T (SigmaB A B)
    iA   : IsType G A
    iB   : IsType (extend G A) B
    cF   : ConvTm G (Fst M) (Fst M') A
    fstR : RM G (Fst M) (Fst M') A u1 b
    sndR : RM G (Snd M) (Snd M') (subst1 B (Fst M)) u2 (EvalFun f u1)

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
    rt G T T' UCode           = UnivR G T * UnivR G T'
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
    rm G M M' T UCode UCode = UnivR G T * rt G M M' UCode
    rm G M M' T UCode (FunEl _) = Top
    rm G M M' T UCode (PiCode _ _) = Empty
    rm G M M' T UCode NatCode = Empty
    rm G M M' T UCode ZeroEl = Top
    rm G M M' T UCode (SucEl _) = Top
    rm G M M' T UCode (PairEl _ _) = Top
    rm G M M' T UCode (SigmaCode _ _) = Empty
    rm G M M' T (FunEl _) Bot = Top
    rm G M M' T (FunEl g) UCode = UnivR G T * rt G M M' (FunEl g)
    rm G M M' T (FunEl _) (FunEl _) = Top
    rm G M M' T (FunEl g) (PiCode b f) = PiTm RMp G M M' T g b f
    rm G M M' T (FunEl _) NatCode = Empty
    rm G M M' T (FunEl _) ZeroEl = Top
    rm G M M' T (FunEl _) (SucEl _) = Top
    rm G M M' T (FunEl _) (PairEl _ _) = Top
    rm G M M' T (FunEl _) (SigmaCode _ _) = Empty
    rm G M M' T (PiCode _ _) Bot = Top
    rm G M M' T (PiCode b f) UCode = UnivR G T * rt G M M' (PiCode b f)
    rm G M M' T (PiCode _ _) (FunEl _) = Top
    rm G M M' T (PiCode _ _) (PiCode _ _) = Empty
    rm G M M' T (PiCode _ _) NatCode = Empty
    rm G M M' T (PiCode _ _) ZeroEl = Top
    rm G M M' T (PiCode _ _) (SucEl _) = Top
    rm G M M' T (PiCode _ _) (PairEl _ _) = Top
    rm G M M' T (PiCode _ _) (SigmaCode _ _) = Empty
    rm G M M' T NatCode Bot = Top
    rm G M M' T NatCode UCode = UnivR G T * rt G M M' NatCode
    rm G M M' T NatCode (FunEl _) = Top
    rm G M M' T NatCode (PiCode _ _) = Empty
    rm G M M' T NatCode NatCode = Empty
    rm G M M' T NatCode ZeroEl = Top
    rm G M M' T NatCode (SucEl _) = Top
    rm G M M' T NatCode (PairEl _ _) = Top
    rm G M M' T NatCode (SigmaCode _ _) = Empty
    rm G M M' T ZeroEl Bot = Top
    rm G M M' T ZeroEl UCode = UnivR G T * rt G M M' ZeroEl
    rm G M M' T ZeroEl (FunEl _) = Top
    rm G M M' T ZeroEl (PiCode _ _) = Empty
    rm G M M' T ZeroEl NatCode = TyEq G T Nat * (ZeroR G M * ZeroR G M')
    rm G M M' T ZeroEl ZeroEl = Top
    rm G M M' T ZeroEl (SucEl _) = Top
    rm G M M' T ZeroEl (PairEl _ _) = Top
    rm G M M' T ZeroEl (SigmaCode _ _) = Empty
    rm G M M' T (SucEl _) Bot = Top
    rm G M M' T (SucEl v) UCode = UnivR G T * rt G M M' (SucEl v)
    rm G M M' T (SucEl _) (FunEl _) = Top
    rm G M M' T (SucEl _) (PiCode _ _) = Empty
    rm G M M' T (SucEl v) NatCode = TyEq G T Nat * SucTm RMp G M M' v
    rm G M M' T (SucEl _) ZeroEl = Top
    rm G M M' T (SucEl _) (SucEl _) = Top
    rm G M M' T (SucEl _) (PairEl _ _) = Top
    rm G M M' T (SucEl _) (SigmaCode _ _) = Empty
    rm G M M' T (PairEl _ _) Bot = Top
    rm G M M' T (PairEl u1 u2) UCode = UnivR G T * rt G M M' (PairEl u1 u2)
    rm G M M' T (PairEl _ _) (FunEl _) = Top
    rm G M M' T (PairEl _ _) (PiCode _ _) = Empty
    rm G M M' T (PairEl _ _) NatCode = Empty
    rm G M M' T (PairEl _ _) ZeroEl = Top
    rm G M M' T (PairEl _ _) (SucEl _) = Top
    rm G M M' T (PairEl _ _) (PairEl _ _) = Top
    rm G M M' T (PairEl u1 u2) (SigmaCode b f) = SigTm RMp G M M' T u1 u2 b f
    rm G M M' T (SigmaCode _ _) Bot = Top
    rm G M M' T (SigmaCode b f) UCode = UnivR G T * rt G M M' (SigmaCode b f)
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
