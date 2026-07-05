{-# OPTIONS --without-K --exact-split #-}
------------------------------------------------------------------------
-- RankCouple.agda  (MIN/ -- Pi + U fragment)
--
-- The interval / type-couple rank-reduction property (Coquand), to be
-- attempted by induction on n:
--
--   given  v, a, u : rank n   and   w, b : rank (suc n)
--   with   v <= w <= u,   w : b,   b <= a   (all coherent),
--   find   w1, b1 : rank n   with   v <= w1 <= u,   w1 : b1,   b1 <= a.
--
-- NB: a need NOT be a type (a : U), so `w : b` + `b <= a` does NOT give
-- `w : a`; we genuinely must shrink the type b to some b1 <= a and find a
-- member w1 : b1 in the interval.  This is strictly stronger than the
-- fixed-type version P, whose `a = UCode` sub-case it contains.
--
-- STATUS: statement set up; trivial reductions filled; the two
-- substantive sub-cases (a = UCode and a = PiCode) are left as explicit
-- goals -- these are the kernel (the typed family-key reduction) that we
-- could neither prove nor refute on paper.
------------------------------------------------------------------------
module ID.Domain.RankCouple where

open import ID.Domain.Basic
  using ( Top ; tt ; Empty ; Nat ; zero ; suc ; max
        ; Le ; Le-refl
        ; Pair ; mkSigma ; fst ; snd ; Sigma
        ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ; nil ; cons )
open import ID.Domain.Order
  using ( RANK ; Coherent ; LeCode ; LeCode-Bot )
open import ID.Domain.MemStage using ( finMemC )

exFalso : {A : Set} -> Empty -> A
exFalso ()

------------------------------------------------------------------------
-- The statement.
------------------------------------------------------------------------

QStmt : Nat -> Set
QStmt n =
  (v a u w b : FinEl) ->
  Le (RANK v) n -> Le (RANK a) n -> Le (RANK u) n ->
  Le (RANK w) (suc n) -> Le (RANK b) (suc n) ->
  Coherent v -> Coherent a -> Coherent u ->
  LeCode v w -> LeCode w u -> finMemC w b -> LeCode b a ->
  Sigma FinEl (\ w1 -> Sigma FinEl (\ b1 ->
    Pair (Le (RANK w1) n) (Pair (Le (RANK b1) n)
    (Pair (LeCode v w1) (Pair (LeCode w1 u)
    (Pair (finMemC w1 b1) (LeCode b1 a)))))))

-- output (existential) for given n v a u
QOut : Nat -> FinEl -> FinEl -> FinEl -> Set
QOut n v a u =
  Sigma FinEl (\ w1 -> Sigma FinEl (\ b1 ->
    Pair (Le (RANK w1) n) (Pair (Le (RANK b1) n)
    (Pair (LeCode v w1) (Pair (LeCode w1 u)
    (Pair (finMemC w1 b1) (LeCode b1 a)))))))

-- nothing is a member of a function element
funElAbsurd : (w : FinEl) (g : FinFun) -> finMemC w (FunEl g) -> Empty
funElAbsurd Bot          g ()
funElAbsurd UCode        g ()
funElAbsurd (FunEl h)    g ()
funElAbsurd (PiCode a f) g ()

-- b = Bot : w must be Bot, and w1 = b1 = Bot works (b1 <= a for free)
botCase : (n : Nat) (v a u w : FinEl) -> LeCode v w -> finMemC w Bot -> QOut n v a u
botCase n v a u Bot          lvw wb =
  mkSigma Bot (mkSigma Bot (mkSigma tt (mkSigma tt
    (mkSigma lvw (mkSigma (LeCode-Bot u) (mkSigma wb (LeCode-Bot a)))))))
botCase n v a u UCode        lvw ()
botCase n v a u (FunEl g)    lvw ()
botCase n v a u (PiCode c f) lvw ()

goodQ : (n : Nat) -> QStmt n
-- b = Bot
goodQ n v a u w Bot          rv ra ru rw rb cv ca cu lvw lwu wb lba =
  botCase n v a u w lvw wb
-- b = FunEl : impossible (FunEl is not a type)
goodQ n v a u w (FunEl g)    rv ra ru rw rb cv ca cu lvw lwu wb lba =
  exFalso (funElAbsurd w g wb)
-- b = UCode : forces a = UCode (else b <= a absurd).
-- Split the type code w; only w = PiCode is substantive.
goodQ n v UCode u Bot          UCode rv ra ru rw rb cv ca cu lvw lwu wb lba =
  mkSigma Bot (mkSigma UCode (mkSigma tt (mkSigma tt
    (mkSigma lvw (mkSigma (LeCode-Bot u) (mkSigma tt tt))))))
goodQ n v UCode u UCode        UCode rv ra ru rw rb cv ca cu lvw lwu wb lba =
  mkSigma UCode (mkSigma UCode (mkSigma tt (mkSigma tt
    (mkSigma lvw (mkSigma lwu (mkSigma tt tt))))))
goodQ n v UCode u (FunEl g)    UCode rv ra ru rw rb cv ca cu lvw lwu wb lba =
  exFalso wb
-- n = 0 base: w = PiCode .. has rank 1, so v (rank 0) must be Bot; take w1 = Bot.
goodQ zero Bot          UCode u (PiCode w0 wf) UCode rv ra ru rw rb cv ca cu lvw lwu wb lba =
  mkSigma Bot (mkSigma UCode (mkSigma tt (mkSigma tt
    (mkSigma tt (mkSigma (LeCode-Bot u) (mkSigma tt tt))))))
goodQ zero UCode        UCode u (PiCode w0 wf) UCode rv ra ru rw rb cv ca cu lvw lwu wb lba = exFalso lvw
goodQ zero (FunEl c)    UCode u (PiCode w0 wf) UCode rv ra ru rw rb cv ca cu lvw lwu wb lba = exFalso rv
goodQ zero (PiCode c f) UCode u (PiCode w0 wf) UCode rv ra ru rw rb cv ca cu lvw lwu wb lba = exFalso rv
-- inductive step: goodQ m is the IH (used for the domain reduction).
-- Split the lower bound v; Bot/UCode/FunEl close, only v = PiCode is substantive.
goodQ (suc m) Bot          UCode u (PiCode w0 wf) UCode rv ra ru rw rb cv ca cu lvw lwu wb lba =
  mkSigma Bot (mkSigma UCode (mkSigma tt (mkSigma tt
    (mkSigma tt (mkSigma (LeCode-Bot u) (mkSigma tt tt))))))
goodQ (suc m) UCode        UCode u (PiCode w0 wf) UCode rv ra ru rw rb cv ca cu lvw lwu wb lba = exFalso lvw
goodQ (suc m) (FunEl c)    UCode u (PiCode w0 wf) UCode rv ra ru rw rb cv ca cu lvw lwu wb lba = exFalso lvw
goodQ (suc m) (PiCode v0 vf) UCode u (PiCode w0 wf) UCode rv ra ru rw rb cv ca cu lvw lwu wb lba =
  {! UCODE-PI-step (v = PiCode): domain w0 via goodQ m, family via build-h2 + edge induction, assemble via piU-intro !}
goodQ n v Bot        u w UCode rv ra ru rw rb cv ca cu lvw lwu wb ()
goodQ n v (FunEl c)  u w UCode rv ra ru rw rb cv ca cu lvw lwu wb ()
goodQ n v (PiCode c f) u w UCode rv ra ru rw rb cv ca cu lvw lwu wb ()
-- b = PiCode : forces a = PiCode -- SUBSTANTIVE KERNEL
goodQ n v (PiCode a0 af) u w (PiCode b0 bf) rv ra ru rw rb cv ca cu lvw lwu wb lba = {! PICODE-KERNEL !}
goodQ n v Bot        u w (PiCode b0 bf) rv ra ru rw rb cv ca cu lvw lwu wb ()
goodQ n v UCode      u w (PiCode b0 bf) rv ra ru rw rb cv ca cu lvw lwu wb ()
goodQ n v (FunEl c)  u w (PiCode b0 bf) rv ra ru rw rb cv ca cu lvw lwu wb ()
