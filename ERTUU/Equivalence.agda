{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERTUU.Equivalence
--
-- Lift-back (paper Theorem 4.13, section of erasure) and the final
-- equivalence statement.  Soundness of erasure (Lemma 4.6) is in
-- ERTUU.EraseDeriv.  Postulate-free.
------------------------------------------------------------------------

module ERTUU.Equivalence where

open import ERTUU.Basic
import ERTUU.RussellSyntax  as R
import ERTUU.RussellTyping  as RT
import ERTUU.TarskiSyntax   as T
import ERTUU.TarskiTyping   as TT
import ERTUU.Erasure        as E
import ERTUU.TarskiMeta     as TM
open import ERTUU.Uniqueness
open import ERTUU.LiftBack
open import ERTUU.EraseDeriv

------------------------------------------------------------------------
-- Lift-back: existence
--
-- A Russell derivation lifts to *some* Tarski derivation with the
-- prescribed erasure. We package the lift as a record carrying the
-- chosen Tarski context, the chosen Tarski terms, the erasure
-- equalities, and the Tarski derivation.
------------------------------------------------------------------------

record LiftIsType {n : Nat} (G : RT.Ctx n) (A : R.Expr n) : Set where
  constructor mkLiftIsType
  field
    G' : TT.Ctx n
    A' : T.Expr n
    G≡ : Eq (eraseCtx G') G
    A≡ : Eq (E.erase A') A
    der : TT.IsType G' A'

record LiftHasType {n : Nat} (G : RT.Ctx n) (M A : R.Expr n) : Set where
  constructor mkLiftHasType
  field
    G' : TT.Ctx n
    M' : T.Expr n
    A' : T.Expr n
    G≡ : Eq (eraseCtx G') G
    M≡ : Eq (E.erase M') M
    A≡ : Eq (E.erase A') A
    der : TT.HasType G' M' A'

record LiftConvTy {n : Nat} (G : RT.Ctx n) (A B : R.Expr n) : Set where
  constructor mkLiftConvTy
  field
    G' : TT.Ctx n
    A' : T.Expr n
    B' : T.Expr n
    G≡ : Eq (eraseCtx G') G
    A≡ : Eq (E.erase A') A
    B≡ : Eq (E.erase B') B
    der : TT.ConvTy G' A' B'

record LiftConvTm {n : Nat} (G : RT.Ctx n) (M N A : R.Expr n) : Set where
  constructor mkLiftConvTm
  field
    G' : TT.Ctx n
    M' : T.Expr n
    N' : T.Expr n
    A' : T.Expr n
    G≡ : Eq (eraseCtx G') G
    M≡ : Eq (E.erase M') M
    N≡ : Eq (E.erase N') N
    A≡ : Eq (E.erase A') A
    der : TT.ConvTm G' M' N' A'

------------------------------------------------------------------------
-- LiftWfCtx (auxiliary record used internally by Stage B)
------------------------------------------------------------------------

record LiftWfCtx {n : Nat} (G : RT.Ctx n) : Set where
  constructor mkLiftWfCtx
  field
    G' : TT.Ctx n
    G≡ : Eq (eraseCtx G') G
    wf : TT.WfCtx G'

------------------------------------------------------------------------
-- Stage B: the four lift-* statements, by mutual induction
-- on Russell derivations.  Mirrors Rocq's section_* family
-- (Equivalence.v:1371-1700).
------------------------------------------------------------------------

lift-WfCtx : {n : Nat} {G : RT.Ctx n}
  -> RT.WfCtx G -> LiftWfCtx G

lift-IsType :
  {n : Nat} {G : RT.Ctx n} {A : R.Expr n}
  -> RT.IsType G A
  -> LiftIsType G A

lift-HasType :
  {n : Nat} {G : RT.Ctx n} {M A : R.Expr n}
  -> RT.HasType G M A
  -> LiftHasType G M A

lift-ConvTy :
  {n : Nat} {G : RT.Ctx n} {A B : R.Expr n}
  -> RT.ConvTy G A B
  -> LiftConvTy G A B

lift-ConvTm :
  {n : Nat} {G : RT.Ctx n} {M N A : R.Expr n}
  -> RT.ConvTm G M N A
  -> LiftConvTm G M N A

------------------------------------------------------------------------
-- lift-WfCtx
------------------------------------------------------------------------

lift-WfCtx RT.wf-empty = mkLiftWfCtx TT.empty refl TT.wf-empty
lift-WfCtx (RT.wf-extend dA) =
  let IH = lift-IsType dA
  in mkLiftWfCtx
       (TT.extend (LiftIsType.G' IH) (LiftIsType.A' IH))
       (Eq-cong2 RT.extend (LiftIsType.G≡ IH) (LiftIsType.A≡ IH))
       (TT.wf-extend (LiftIsType.der IH))

------------------------------------------------------------------------
-- lift-IsType
------------------------------------------------------------------------

lift-IsType (RT.is-Ty-from-U dM) =
  let IH = lift-HasType dM
      G' = LiftHasType.G' IH
      M' = LiftHasType.M' IH
      G≡ = LiftHasType.G≡ IH
      M≡ = LiftHasType.M≡ IH
      A≡ = LiftHasType.A≡ IH
      der = LiftHasType.der IH
      der-at-U = coerce-to-U der A≡
  in mkLiftIsType G' (T.El M') G≡ M≡ (TT.is-Ty-El der-at-U)

------------------------------------------------------------------------
-- lift-HasType
------------------------------------------------------------------------

lift-HasType (RT.ty-var {i = i} dG) =
  let IH = lift-WfCtx dG
      G' = LiftWfCtx.G' IH
      G≡ = LiftWfCtx.G≡ IH
      wf = LiftWfCtx.wf IH
      A' = TT.lookup G' i
      A≡ : Eq (E.erase A') _
      A≡ = Eq-trans (Eq-sym (lookup-erase G' i))
                    (Eq-cong (\ ctx -> RT.lookup ctx i) G≡)
  in mkLiftHasType G' (T.Var i) A' G≡ refl A≡ (TT.ty-var {i = i} wf)

lift-HasType (RT.ty-conv dM dAB) =
  let IH_M = lift-HasType dM
      G_M = LiftHasType.G' IH_M
      M' = LiftHasType.M' IH_M
      A_M = LiftHasType.A' IH_M
      G≡_M = LiftHasType.G≡ IH_M
      M≡ = LiftHasType.M≡ IH_M
      A≡_M = LiftHasType.A≡ IH_M
      der_M = LiftHasType.der IH_M
      IH_C = lift-ConvTy dAB
      G_C = LiftConvTy.G' IH_C
      A_C = LiftConvTy.A' IH_C
      B_C = LiftConvTy.B' IH_C
      G≡_C = LiftConvTy.G≡ IH_C
      A≡_C = LiftConvTy.A≡ IH_C
      B≡_C = LiftConvTy.B≡ IH_C
      der_C = LiftConvTy.der IH_C
      wf_M = TM.typing-WfCtx der_M
      eq_CM = Eq-trans G≡_C (Eq-sym G≡_M)
      der_C' = move-ConvTy G_C G_M wf_M eq_CM der_C
      dAM = typing-IsType der_M
      dAC = TM.presup-l-ConvTy der_C'
      eqAM_AC = Eq-trans A≡_M (Eq-sym A≡_C)
      bridge = type-uniq dAM dAC eqAM_AC
      cAM_BC = TT.conv-Ty-trans bridge der_C'
      der' = TT.ty-conv der_M cAM_BC
  in mkLiftHasType G_M M' B_C G≡_M M≡ B≡_C der'

lift-HasType (RT.ty-U dG) =
  let IH = lift-WfCtx dG
      G' = LiftWfCtx.G' IH
      G≡ = LiftWfCtx.G≡ IH
      wf = LiftWfCtx.wf IH
  in mkLiftHasType G' T.UCode T.U G≡ refl refl (TT.ty-UCode wf)

lift-HasType (RT.ty-Pi dA dB) =
  let IH_A = lift-HasType dA
      G_A = LiftHasType.G' IH_A
      A_T = LiftHasType.M' IH_A
      G≡_A = LiftHasType.G≡ IH_A
      A_eq = LiftHasType.M≡ IH_A
      ATy≡_A = LiftHasType.A≡ IH_A
      der_A = LiftHasType.der IH_A
      der_A_U = coerce-to-U der_A ATy≡_A
      ElA = TT.is-Ty-El der_A_U
      target_inner = TT.extend G_A (T.El A_T)
      wf_inner = TT.wf-extend ElA
      IH_B = lift-HasType dB
      G_B = LiftHasType.G' IH_B
      B_T = LiftHasType.M' IH_B
      G≡_B = LiftHasType.G≡ IH_B
      B_eq = LiftHasType.M≡ IH_B
      ATy≡_B = LiftHasType.A≡ IH_B
      der_B = LiftHasType.der IH_B
      eq_B-tgt : Eq (eraseCtx G_B) (eraseCtx target_inner)
      eq_B-tgt = Eq-trans G≡_B (Eq-sym (Eq-cong2 RT.extend G≡_A A_eq))
      der_B' = move-HasType G_B target_inner wf_inner eq_B-tgt der_B
      der_B_U = coerce-to-U der_B' ATy≡_B
      final = TT.ty-PiCode der_A_U der_B_U
      M-eq : Eq (E.erase (T.PiCode A_T B_T)) _
      M-eq = Eq-cong2 R.Pi A_eq B_eq
  in mkLiftHasType G_A (T.PiCode A_T B_T) (T.U) G≡_A M-eq refl final

lift-HasType (RT.ty-Lam dA dB db) =
  let IH_A = lift-IsType dA
      G_A = LiftIsType.G' IH_A
      A_T = LiftIsType.A' IH_A
      G≡_A = LiftIsType.G≡ IH_A
      A_eq = LiftIsType.A≡ IH_A
      der_A = LiftIsType.der IH_A
      target_inner = TT.extend G_A A_T
      wf_inner = TT.wf-extend der_A
      IH_B = lift-IsType dB
      G_B = LiftIsType.G' IH_B
      B_T = LiftIsType.A' IH_B
      G≡_B = LiftIsType.G≡ IH_B
      B_eq = LiftIsType.A≡ IH_B
      der_B = LiftIsType.der IH_B
      eq_B-tgt : Eq (eraseCtx G_B) (eraseCtx target_inner)
      eq_B-tgt = Eq-trans G≡_B (Eq-sym (Eq-cong2 RT.extend G≡_A A_eq))
      der_B' = move-IsType G_B target_inner wf_inner eq_B-tgt der_B
      IH_b = lift-HasType db
      G_b = LiftHasType.G' IH_b
      b_T = LiftHasType.M' IH_b
      Ab_T = LiftHasType.A' IH_b
      G≡_b = LiftHasType.G≡ IH_b
      b_eq = LiftHasType.M≡ IH_b
      Ab_eq = LiftHasType.A≡ IH_b
      der_b = LiftHasType.der IH_b
      eq_b-tgt : Eq (eraseCtx G_b) (eraseCtx target_inner)
      eq_b-tgt = Eq-trans G≡_b (Eq-sym (Eq-cong2 RT.extend G≡_A A_eq))
      der_b' = move-HasType G_b target_inner wf_inner eq_b-tgt der_b
      eq-Ab-B : Eq (E.erase Ab_T) (E.erase B_T)
      eq-Ab-B = Eq-trans Ab_eq (Eq-sym B_eq)
      der_b'' = coerce-HasType-to der_b' der_B' eq-Ab-B
      final = TT.ty-Lam der_A der_B' der_b''
      M-eq : Eq (E.erase (T.Lam A_T B_T b_T)) _
      M-eq = Eq-cong3 R.Lam A_eq B_eq b_eq
      A-eq : Eq (E.erase (T.Pi A_T B_T)) _
      A-eq = Eq-cong2 R.Pi A_eq B_eq
  in mkLiftHasType G_A (T.Lam A_T B_T b_T) (T.Pi A_T B_T) G≡_A M-eq A-eq final

lift-HasType (RT.ty-App {A = AR} {B = BR} {c = cR} {a = aR} dA dB dc da) =
  let IH_A = lift-IsType dA
      G_A = LiftIsType.G' IH_A
      A_T = LiftIsType.A' IH_A
      G≡_A = LiftIsType.G≡ IH_A
      A_eq = LiftIsType.A≡ IH_A
      der_A = LiftIsType.der IH_A
      target_inner = TT.extend G_A A_T
      wf_inner = TT.wf-extend der_A
      IH_B = lift-IsType dB
      G_B = LiftIsType.G' IH_B
      B_T = LiftIsType.A' IH_B
      G≡_B = LiftIsType.G≡ IH_B
      B_eq = LiftIsType.A≡ IH_B
      der_B = LiftIsType.der IH_B
      eq_B-tgt : Eq (eraseCtx G_B) (eraseCtx target_inner)
      eq_B-tgt = Eq-trans G≡_B (Eq-sym (Eq-cong2 RT.extend G≡_A A_eq))
      der_B' = move-IsType G_B target_inner wf_inner eq_B-tgt der_B
      Pi_T = T.Pi A_T B_T
      dPi : TT.IsType G_A Pi_T
      dPi = TT.is-Ty-Pi der_A der_B'
      Pi_eq : Eq (E.erase Pi_T) (R.Pi AR BR)
      Pi_eq = Eq-cong2 R.Pi A_eq B_eq
      IH_c = lift-HasType dc
      G_c = LiftHasType.G' IH_c
      c_T = LiftHasType.M' IH_c
      Ac_T = LiftHasType.A' IH_c
      G≡_c = LiftHasType.G≡ IH_c
      c_eq = LiftHasType.M≡ IH_c
      Ac_eq = LiftHasType.A≡ IH_c
      der_c = LiftHasType.der IH_c
      wf_A = TM.isType-WfCtx der_A
      eq_c-A : Eq (eraseCtx G_c) (eraseCtx G_A)
      eq_c-A = Eq-trans G≡_c (Eq-sym G≡_A)
      der_c' = move-HasType G_c G_A wf_A eq_c-A der_c
      eq-Ac-Pi : Eq (E.erase Ac_T) (E.erase Pi_T)
      eq-Ac-Pi = Eq-trans Ac_eq (Eq-sym Pi_eq)
      der_c'' = coerce-HasType-to der_c' dPi eq-Ac-Pi
      IH_a = lift-HasType da
      G_a = LiftHasType.G' IH_a
      a_T = LiftHasType.M' IH_a
      Aa_T = LiftHasType.A' IH_a
      G≡_a = LiftHasType.G≡ IH_a
      a_eq = LiftHasType.M≡ IH_a
      Aa_eq = LiftHasType.A≡ IH_a
      der_a = LiftHasType.der IH_a
      eq_a-A : Eq (eraseCtx G_a) (eraseCtx G_A)
      eq_a-A = Eq-trans G≡_a (Eq-sym G≡_A)
      der_a' = move-HasType G_a G_A wf_A eq_a-A der_a
      eq-Aa-A : Eq (E.erase Aa_T) (E.erase A_T)
      eq-Aa-A = Eq-trans Aa_eq (Eq-sym A_eq)
      der_a'' = coerce-HasType-to der_a' der_A eq-Aa-A
      final = TT.ty-App der_A der_B' der_c'' der_a''
      M-eq : Eq (E.erase (T.App A_T B_T c_T a_T)) (R.App AR BR cR aR)
      M-eq = Eq-cong4 R.App A_eq B_eq c_eq a_eq
      Subst-eq : Eq (E.erase (T.subst1 B_T a_T)) (R.subst1 BR aR)
      Subst-eq = Eq-trans (E.erase-subst1 B_T a_T)
                          (Eq-cong2 R.subst1 B_eq a_eq)
  in mkLiftHasType G_A (T.App A_T B_T c_T a_T) (T.subst1 B_T a_T)
                   G≡_A M-eq Subst-eq final

------------------------------------------------------------------------
-- lift-ConvTy
------------------------------------------------------------------------

lift-ConvTy (RT.conv-Ty-refl dA) =
  let IH = lift-IsType dA
      G' = LiftIsType.G' IH
      A' = LiftIsType.A' IH
      G≡ = LiftIsType.G≡ IH
      A≡ = LiftIsType.A≡ IH
      der = LiftIsType.der IH
  in mkLiftConvTy G' A' A' G≡ A≡ A≡ (TT.conv-Ty-refl der)

lift-ConvTy (RT.conv-Ty-sym d) =
  let IH = lift-ConvTy d
      G' = LiftConvTy.G' IH
      A' = LiftConvTy.A' IH
      B' = LiftConvTy.B' IH
      G≡ = LiftConvTy.G≡ IH
      A≡ = LiftConvTy.A≡ IH
      B≡ = LiftConvTy.B≡ IH
      der = LiftConvTy.der IH
  in mkLiftConvTy G' B' A' G≡ B≡ A≡ (TT.conv-Ty-sym der)

lift-ConvTy (RT.conv-Ty-trans d1 d2) =
  let IHa = lift-ConvTy d1
      Ga = LiftConvTy.G' IHa
      A_T = LiftConvTy.A' IHa
      B_Ta = LiftConvTy.B' IHa
      G≡a = LiftConvTy.G≡ IHa
      A≡a = LiftConvTy.A≡ IHa
      B≡a = LiftConvTy.B≡ IHa
      der_a = LiftConvTy.der IHa
      IHb = lift-ConvTy d2
      Gb = LiftConvTy.G' IHb
      B_Tb = LiftConvTy.A' IHb
      C_T = LiftConvTy.B' IHb
      G≡b = LiftConvTy.G≡ IHb
      A2≡ = LiftConvTy.A≡ IHb
      C≡ = LiftConvTy.B≡ IHb
      der_b = LiftConvTy.der IHb
      wf_a = TM.isType-WfCtx (TM.presup-l-ConvTy der_a)
      eq_b-a = Eq-trans G≡b (Eq-sym G≡a)
      der_b' = move-ConvTy Gb Ga wf_a eq_b-a der_b
      eq-Ba-Bb = Eq-trans B≡a (Eq-sym A2≡)
      final = bridge-ConvTy der_a der_b' eq-Ba-Bb
  in mkLiftConvTy Ga A_T C_T G≡a A≡a C≡ final

lift-ConvTy (RT.conv-Ty-Pi _ _ dA dB) =
  let IH_A = lift-ConvTy dA
      G_A = LiftConvTy.G' IH_A
      A_L = LiftConvTy.A' IH_A
      A_R = LiftConvTy.B' IH_A
      G≡_A = LiftConvTy.G≡ IH_A
      A_L≡ = LiftConvTy.A≡ IH_A
      A_R≡ = LiftConvTy.B≡ IH_A
      der_A = LiftConvTy.der IH_A
      dAL = TM.presup-l-ConvTy der_A
      target_inner = TT.extend G_A A_L
      wf_inner = TT.wf-extend dAL
      IH_B = lift-ConvTy dB
      G_B = LiftConvTy.G' IH_B
      B_L = LiftConvTy.A' IH_B
      B_R = LiftConvTy.B' IH_B
      G≡_B = LiftConvTy.G≡ IH_B
      B_L≡ = LiftConvTy.A≡ IH_B
      B_R≡ = LiftConvTy.B≡ IH_B
      der_B = LiftConvTy.der IH_B
      eq_B-tgt = Eq-trans G≡_B (Eq-sym (Eq-cong2 RT.extend G≡_A A_L≡))
      der_B' = move-ConvTy G_B target_inner wf_inner eq_B-tgt der_B
      final = TM.mk-conv-Ty-Pi der_A der_B'
      L-eq = Eq-cong2 R.Pi A_L≡ B_L≡
      R-eq = Eq-cong2 R.Pi A_R≡ B_R≡
  in mkLiftConvTy G_A (T.Pi A_L B_L) (T.Pi A_R B_R) G≡_A L-eq R-eq final

lift-ConvTy (RT.conv-Ty-from-U d) =
  let IH = lift-ConvTm d
      G' = LiftConvTm.G' IH
      M' = LiftConvTm.M' IH
      N' = LiftConvTm.N' IH
      AT' = LiftConvTm.A' IH
      G≡ = LiftConvTm.G≡ IH
      M≡ = LiftConvTm.M≡ IH
      N≡ = LiftConvTm.N≡ IH
      A≡ = LiftConvTm.A≡ IH
      der = LiftConvTm.der IH
      der-U = coerce-ConvTm-to-U der A≡
  in mkLiftConvTy G' (T.El M') (T.El N') G≡ M≡ N≡ (TT.conv-Ty-El der-U)

------------------------------------------------------------------------
-- lift-ConvTm
------------------------------------------------------------------------

lift-ConvTm (RT.conv-refl dM) =
  let IH = lift-HasType dM
      G' = LiftHasType.G' IH
      M' = LiftHasType.M' IH
      A' = LiftHasType.A' IH
      G≡ = LiftHasType.G≡ IH
      M≡ = LiftHasType.M≡ IH
      A≡ = LiftHasType.A≡ IH
      der = LiftHasType.der IH
  in mkLiftConvTm G' M' M' A' G≡ M≡ M≡ A≡ (TT.conv-refl der)

lift-ConvTm (RT.conv-sym d) =
  let IH = lift-ConvTm d
      G' = LiftConvTm.G' IH
      M' = LiftConvTm.M' IH
      N' = LiftConvTm.N' IH
      A' = LiftConvTm.A' IH
      G≡ = LiftConvTm.G≡ IH
      M≡ = LiftConvTm.M≡ IH
      N≡ = LiftConvTm.N≡ IH
      A≡ = LiftConvTm.A≡ IH
      der = LiftConvTm.der IH
  in mkLiftConvTm G' N' M' A' G≡ N≡ M≡ A≡ (TT.conv-sym der)

lift-ConvTm (RT.conv-trans d1 d2) =
  let IHa = lift-ConvTm d1
      Ga = LiftConvTm.G' IHa
      M_T = LiftConvTm.M' IHa
      N_Ta = LiftConvTm.N' IHa
      A_Ta = LiftConvTm.A' IHa
      G≡a = LiftConvTm.G≡ IHa
      M≡a = LiftConvTm.M≡ IHa
      N≡a = LiftConvTm.N≡ IHa
      A≡a = LiftConvTm.A≡ IHa
      der_a = LiftConvTm.der IHa
      IHb = lift-ConvTm d2
      Gb = LiftConvTm.G' IHb
      N_Tb = LiftConvTm.M' IHb
      P_T = LiftConvTm.N' IHb
      A_Tb = LiftConvTm.A' IHb
      G≡b = LiftConvTm.G≡ IHb
      N≡b = LiftConvTm.M≡ IHb
      P≡b = LiftConvTm.N≡ IHb
      A≡b = LiftConvTm.A≡ IHb
      der_b = LiftConvTm.der IHb
      wf_a = TM.typing-WfCtx (TM.presup-l-ConvTm der_a)
      eq_b-a = Eq-trans G≡b (Eq-sym G≡a)
      der_b' = move-ConvTm Gb Ga wf_a eq_b-a der_b
      dA-a = typing-IsType (TM.presup-l-ConvTm der_a)
      dA-b = typing-IsType (TM.presup-l-ConvTm der_b')
      eq_Aa-Ab = Eq-trans A≡a (Eq-sym A≡b)
      bridgeTy = type-uniq dA-a dA-b eq_Aa-Ab
      dN-a = TM.presup-r-ConvTm der_a
      der_b'' = TT.conv-conv der_b' (TT.conv-Ty-sym bridgeTy)
      dN-b = TM.presup-l-ConvTm der_b''
      eqN = Eq-trans N≡a (Eq-sym N≡b)
      tu-N = term-uniq dN-a dN-b eqN
      bridgeN-tm : TT.ConvTm Ga N_Ta N_Tb A_Ta
      bridgeN-tm = extract-conv-same tu-N
      der_a-to-Nb = TT.conv-trans der_a bridgeN-tm
      final = TT.conv-trans der_a-to-Nb der_b''
  in mkLiftConvTm Ga M_T P_T A_Ta G≡a M≡a P≡b A≡a final

lift-ConvTm (RT.conv-conv dMN dAB) =
  let IH_M = lift-ConvTm dMN
      G_M = LiftConvTm.G' IH_M
      M' = LiftConvTm.M' IH_M
      N' = LiftConvTm.N' IH_M
      A_M = LiftConvTm.A' IH_M
      G≡_M = LiftConvTm.G≡ IH_M
      M≡ = LiftConvTm.M≡ IH_M
      N≡ = LiftConvTm.N≡ IH_M
      A≡_M = LiftConvTm.A≡ IH_M
      der_M = LiftConvTm.der IH_M
      IH_C = lift-ConvTy dAB
      G_C = LiftConvTy.G' IH_C
      A_C = LiftConvTy.A' IH_C
      B_C = LiftConvTy.B' IH_C
      G≡_C = LiftConvTy.G≡ IH_C
      A≡_C = LiftConvTy.A≡ IH_C
      B≡_C = LiftConvTy.B≡ IH_C
      der_C = LiftConvTy.der IH_C
      wf_M = TM.typing-WfCtx (TM.presup-l-ConvTm der_M)
      eq_C-M = Eq-trans G≡_C (Eq-sym G≡_M)
      der_C' = move-ConvTy G_C G_M wf_M eq_C-M der_C
      dAM = typing-IsType (TM.presup-l-ConvTm der_M)
      dAC = TM.presup-l-ConvTy der_C'
      bridgeT = type-uniq dAM dAC (Eq-trans A≡_M (Eq-sym A≡_C))
      cAM_BC = TT.conv-Ty-trans bridgeT der_C'
      final = TT.conv-conv der_M cAM_BC
  in mkLiftConvTm G_M M' N' B_C G≡_M M≡ N≡ B≡_C final

lift-ConvTm (RT.conv-cong-Pi _ _ daa' dbb') =
  let IH_A = lift-ConvTm daa'
      G_A = LiftConvTm.G' IH_A
      A_L = LiftConvTm.M' IH_A
      A_R = LiftConvTm.N' IH_A
      AT_A = LiftConvTm.A' IH_A
      G≡_A = LiftConvTm.G≡ IH_A
      AL≡ = LiftConvTm.M≡ IH_A
      AR≡ = LiftConvTm.N≡ IH_A
      ATy≡_A = LiftConvTm.A≡ IH_A
      der_A = LiftConvTm.der IH_A
      der_A_U = coerce-ConvTm-to-U der_A ATy≡_A
      dA_L = TM.presup-l-ConvTm der_A_U
      ElA = TT.is-Ty-El dA_L
      target_inner = TT.extend G_A (T.El A_L)
      wf_inner = TT.wf-extend ElA
      IH_B = lift-ConvTm dbb'
      G_B = LiftConvTm.G' IH_B
      B_L = LiftConvTm.M' IH_B
      B_R = LiftConvTm.N' IH_B
      AT_B = LiftConvTm.A' IH_B
      G≡_B = LiftConvTm.G≡ IH_B
      BL≡ = LiftConvTm.M≡ IH_B
      BR≡ = LiftConvTm.N≡ IH_B
      ATy≡_B = LiftConvTm.A≡ IH_B
      der_B = LiftConvTm.der IH_B
      eq_B-tgt = Eq-trans G≡_B (Eq-sym (Eq-cong2 RT.extend G≡_A AL≡))
      der_B' = move-ConvTm G_B target_inner wf_inner eq_B-tgt der_B
      der_B_U = coerce-ConvTm-to-U der_B' ATy≡_B
      final = TM.mk-conv-cong-PiCode der_A_U der_B_U
      M-eq = Eq-cong2 R.Pi AL≡ BL≡
      N-eq = Eq-cong2 R.Pi AR≡ BR≡
  in mkLiftConvTm G_A (T.PiCode A_L B_L) (T.PiCode A_R B_R) (T.U)
                  G≡_A M-eq N-eq refl final

lift-ConvTm (RT.conv-cong-Lam-body dA dB _ db) =
  let IH_A = lift-IsType dA
      G_A = LiftIsType.G' IH_A
      A_T = LiftIsType.A' IH_A
      G≡_A = LiftIsType.G≡ IH_A
      A_eq = LiftIsType.A≡ IH_A
      der_A = LiftIsType.der IH_A
      target_inner = TT.extend G_A A_T
      wf_inner = TT.wf-extend der_A
      IH_B = lift-IsType dB
      G_B = LiftIsType.G' IH_B
      B_T = LiftIsType.A' IH_B
      G≡_B = LiftIsType.G≡ IH_B
      B_eq = LiftIsType.A≡ IH_B
      der_B = LiftIsType.der IH_B
      eq_B-tgt = Eq-trans G≡_B (Eq-sym (Eq-cong2 RT.extend G≡_A A_eq))
      der_B' = move-IsType G_B target_inner wf_inner eq_B-tgt der_B
      IH_b = lift-ConvTm db
      G_b = LiftConvTm.G' IH_b
      b_L = LiftConvTm.M' IH_b
      b_R = LiftConvTm.N' IH_b
      Ab_T = LiftConvTm.A' IH_b
      G≡_b = LiftConvTm.G≡ IH_b
      bL≡ = LiftConvTm.M≡ IH_b
      bR≡ = LiftConvTm.N≡ IH_b
      Ab_eq = LiftConvTm.A≡ IH_b
      der_b = LiftConvTm.der IH_b
      eq_b-tgt = Eq-trans G≡_b (Eq-sym (Eq-cong2 RT.extend G≡_A A_eq))
      der_b' = move-ConvTm G_b target_inner wf_inner eq_b-tgt der_b
      eq-Ab-B = Eq-trans Ab_eq (Eq-sym B_eq)
      der_b'' = coerce-ConvTm-to der_b' der_B' eq-Ab-B
      final = TT.conv-cong-Lam-body der_A der_B' der_b''
      L-eq = Eq-cong3 R.Lam A_eq B_eq bL≡
      R-eq = Eq-cong3 R.Lam A_eq B_eq bR≡
      Ty-eq = Eq-cong2 R.Pi A_eq B_eq
  in mkLiftConvTm G_A (T.Lam A_T B_T b_L) (T.Lam A_T B_T b_R)
                  (T.Pi A_T B_T) G≡_A L-eq R-eq Ty-eq final

lift-ConvTm (RT.conv-cong-Lam-Ty _ _ dA dB db) =
  let IH_A = lift-ConvTy dA
      G_A = LiftConvTy.G' IH_A
      A_L = LiftConvTy.A' IH_A
      A_R = LiftConvTy.B' IH_A
      G≡_A = LiftConvTy.G≡ IH_A
      AL_eq = LiftConvTy.A≡ IH_A
      AR_eq = LiftConvTy.B≡ IH_A
      der_A = LiftConvTy.der IH_A
      dAL = TM.presup-l-ConvTy der_A
      target_inner = TT.extend G_A A_L
      wf_inner = TT.wf-extend dAL
      IH_B = lift-ConvTy dB
      G_B = LiftConvTy.G' IH_B
      B_L = LiftConvTy.A' IH_B
      B_R = LiftConvTy.B' IH_B
      G≡_B = LiftConvTy.G≡ IH_B
      BL_eq = LiftConvTy.A≡ IH_B
      BR_eq = LiftConvTy.B≡ IH_B
      der_B = LiftConvTy.der IH_B
      eq_B-tgt = Eq-trans G≡_B (Eq-sym (Eq-cong2 RT.extend G≡_A AL_eq))
      der_B' = move-ConvTy G_B target_inner wf_inner eq_B-tgt der_B
      dBL = TM.presup-l-ConvTy der_B'
      IH_b = lift-HasType db
      G_b = LiftHasType.G' IH_b
      b_T = LiftHasType.M' IH_b
      Ab_T = LiftHasType.A' IH_b
      G≡_b = LiftHasType.G≡ IH_b
      b_eq = LiftHasType.M≡ IH_b
      Ab_eq = LiftHasType.A≡ IH_b
      der_b = LiftHasType.der IH_b
      eq_b-tgt = Eq-trans G≡_b (Eq-sym (Eq-cong2 RT.extend G≡_A AL_eq))
      der_b' = move-HasType G_b target_inner wf_inner eq_b-tgt der_b
      eq-Ab-BL = Eq-trans Ab_eq (Eq-sym BL_eq)
      der_b'' = coerce-HasType-to der_b' dBL eq-Ab-BL
      final = TM.mk-conv-cong-Lam-Ty der_A der_B' der_b''
      L-eq = Eq-cong3 R.Lam AL_eq BL_eq b_eq
      R-eq = Eq-cong3 R.Lam AR_eq BR_eq b_eq
      Ty-eq = Eq-cong2 R.Pi AL_eq BL_eq
  in mkLiftConvTm G_A (T.Lam A_L B_L b_T) (T.Lam A_R B_R b_T)
                  (T.Pi A_L B_L) G≡_A L-eq R-eq Ty-eq final

lift-ConvTm (RT.conv-cong-App-fun dA dB dc da) =
  let IH_A = lift-IsType dA
      G_A = LiftIsType.G' IH_A
      A_T = LiftIsType.A' IH_A
      G≡_A = LiftIsType.G≡ IH_A
      A_eq = LiftIsType.A≡ IH_A
      der_A = LiftIsType.der IH_A
      target_inner = TT.extend G_A A_T
      wf_inner = TT.wf-extend der_A
      IH_B = lift-IsType dB
      G_B = LiftIsType.G' IH_B
      B_T = LiftIsType.A' IH_B
      G≡_B = LiftIsType.G≡ IH_B
      B_eq = LiftIsType.A≡ IH_B
      der_B = LiftIsType.der IH_B
      eq_B-tgt = Eq-trans G≡_B (Eq-sym (Eq-cong2 RT.extend G≡_A A_eq))
      der_B' = move-IsType G_B target_inner wf_inner eq_B-tgt der_B
      Pi_T = T.Pi A_T B_T
      dPi = TT.is-Ty-Pi der_A der_B'
      Pi_eq = Eq-cong2 R.Pi A_eq B_eq
      IH_c = lift-ConvTm dc
      G_c = LiftConvTm.G' IH_c
      c_L = LiftConvTm.M' IH_c
      c_R = LiftConvTm.N' IH_c
      Ac_T = LiftConvTm.A' IH_c
      G≡_c = LiftConvTm.G≡ IH_c
      cL≡ = LiftConvTm.M≡ IH_c
      cR≡ = LiftConvTm.N≡ IH_c
      Ac_eq = LiftConvTm.A≡ IH_c
      der_c = LiftConvTm.der IH_c
      wf_A = TM.isType-WfCtx der_A
      eq_c-A = Eq-trans G≡_c (Eq-sym G≡_A)
      der_c' = move-ConvTm G_c G_A wf_A eq_c-A der_c
      der_c'' = coerce-ConvTm-to der_c' dPi (Eq-trans Ac_eq (Eq-sym Pi_eq))
      IH_a = lift-HasType da
      G_a = LiftHasType.G' IH_a
      a_T = LiftHasType.M' IH_a
      Aa_T = LiftHasType.A' IH_a
      G≡_a = LiftHasType.G≡ IH_a
      a_eq = LiftHasType.M≡ IH_a
      Aa_eq = LiftHasType.A≡ IH_a
      der_a = LiftHasType.der IH_a
      eq_a-A = Eq-trans G≡_a (Eq-sym G≡_A)
      der_a' = move-HasType G_a G_A wf_A eq_a-A der_a
      der_a'' = coerce-HasType-to der_a' der_A (Eq-trans Aa_eq (Eq-sym A_eq))
      final = TT.conv-cong-App-fun der_A der_B' der_c'' der_a''
      L-eq = Eq-cong4 R.App A_eq B_eq cL≡ a_eq
      R-eq = Eq-cong4 R.App A_eq B_eq cR≡ a_eq
      Subst-eq = Eq-trans (E.erase-subst1 B_T a_T)
                          (Eq-cong2 R.subst1 B_eq a_eq)
  in mkLiftConvTm G_A (T.App A_T B_T c_L a_T) (T.App A_T B_T c_R a_T)
                  (T.subst1 B_T a_T)
                  G≡_A L-eq R-eq Subst-eq final

lift-ConvTm (RT.conv-cong-App-arg dA dB dc da Bsubst-conv) =
  let IH_A = lift-IsType dA
      G_A = LiftIsType.G' IH_A
      A_T = LiftIsType.A' IH_A
      G≡_A = LiftIsType.G≡ IH_A
      A_eq = LiftIsType.A≡ IH_A
      der_A = LiftIsType.der IH_A
      target_inner = TT.extend G_A A_T
      wf_inner = TT.wf-extend der_A
      IH_B = lift-IsType dB
      G_B = LiftIsType.G' IH_B
      B_T = LiftIsType.A' IH_B
      G≡_B = LiftIsType.G≡ IH_B
      B_eq = LiftIsType.A≡ IH_B
      der_B = LiftIsType.der IH_B
      eq_B-tgt = Eq-trans G≡_B (Eq-sym (Eq-cong2 RT.extend G≡_A A_eq))
      der_B' = move-IsType G_B target_inner wf_inner eq_B-tgt der_B
      Pi_T = T.Pi A_T B_T
      dPi = TT.is-Ty-Pi der_A der_B'
      Pi_eq = Eq-cong2 R.Pi A_eq B_eq
      IH_c = lift-HasType dc
      G_c = LiftHasType.G' IH_c
      c_T = LiftHasType.M' IH_c
      Ac_T = LiftHasType.A' IH_c
      G≡_c = LiftHasType.G≡ IH_c
      c_eq = LiftHasType.M≡ IH_c
      Ac_eq = LiftHasType.A≡ IH_c
      der_c = LiftHasType.der IH_c
      wf_A = TM.isType-WfCtx der_A
      eq_c-A = Eq-trans G≡_c (Eq-sym G≡_A)
      der_c' = move-HasType G_c G_A wf_A eq_c-A der_c
      der_c'' = coerce-HasType-to der_c' dPi (Eq-trans Ac_eq (Eq-sym Pi_eq))
      IH_a = lift-ConvTm da
      G_a = LiftConvTm.G' IH_a
      a_L = LiftConvTm.M' IH_a
      a_R = LiftConvTm.N' IH_a
      Aa_T = LiftConvTm.A' IH_a
      G≡_a = LiftConvTm.G≡ IH_a
      aL_eq = LiftConvTm.M≡ IH_a
      aR_eq = LiftConvTm.N≡ IH_a
      Aa_eq = LiftConvTm.A≡ IH_a
      der_a = LiftConvTm.der IH_a
      eq_a-A = Eq-trans G≡_a (Eq-sym G≡_A)
      der_a' = move-ConvTm G_a G_A wf_A eq_a-A der_a
      der_a'' = coerce-ConvTm-to der_a' der_A (Eq-trans Aa_eq (Eq-sym A_eq))
      IH_S = lift-ConvTy Bsubst-conv
      G_S = LiftConvTy.G' IH_S
      L_S = LiftConvTy.A' IH_S
      R_S = LiftConvTy.B' IH_S
      G≡_S = LiftConvTy.G≡ IH_S
      L_S_eq = LiftConvTy.A≡ IH_S
      R_S_eq = LiftConvTy.B≡ IH_S
      der_S = LiftConvTy.der IH_S
      eq_S-A = Eq-trans G≡_S (Eq-sym G≡_A)
      der_S' = move-ConvTy G_S G_A wf_A eq_S-A der_S
      -- der_S' : ConvTy G_A L_S R_S, erase L_S = R.subst1 B (Russell-a),
      --                              erase R_S = R.subst1 B (Russell-a')
      -- We need ConvTy G_A (T.subst1 B_T a_L) (T.subst1 B_T a_R)
      -- Build target subst1 IsTypes:
      dHL = TM.presup-l-ConvTm der_a''  -- HasType G_A a_L A_T
      dHR = TM.presup-r-ConvTm der_a''  -- HasType G_A a_R A_T
      ws_L = TM.subst1-WtSub der_A dHL
      ws_R = TM.subst1-WtSub der_A dHR
      d_subst_L = TM.subst-IsType ws_L wf_A der_B'
      d_subst_R = TM.subst-IsType ws_R wf_A der_B'
      d_subst-L_eq : Eq (E.erase (T.subst1 B_T a_L)) _
      d_subst-L_eq = Eq-trans (E.erase-subst1 B_T a_L)
                              (Eq-cong2 R.subst1 B_eq aL_eq)
      d_subst-R_eq : Eq (E.erase (T.subst1 B_T a_R)) _
      d_subst-R_eq = Eq-trans (E.erase-subst1 B_T a_R)
                              (Eq-cong2 R.subst1 B_eq aR_eq)
      eq_substL_LS = Eq-trans d_subst-L_eq (Eq-sym L_S_eq)
      eq_substR_RS = Eq-trans d_subst-R_eq (Eq-sym R_S_eq)
      bridge_L = type-uniq d_subst_L (TM.presup-l-ConvTy der_S') eq_substL_LS
      bridge_R = type-uniq (TM.presup-r-ConvTy der_S') d_subst_R
                           (Eq-sym eq_substR_RS)
      subst_conv : TT.ConvTy G_A (T.subst1 B_T a_L) (T.subst1 B_T a_R)
      subst_conv = TT.conv-Ty-trans bridge_L
                     (TT.conv-Ty-trans der_S' bridge_R)
      final = TT.conv-cong-App-arg der_A der_B' der_c'' der_a'' subst_conv
      L-eq = Eq-cong4 R.App A_eq B_eq c_eq aL_eq
      R-eq = Eq-cong4 R.App A_eq B_eq c_eq aR_eq
  in mkLiftConvTm G_A (T.App A_T B_T c_T a_L) (T.App A_T B_T c_T a_R)
                  (T.subst1 B_T a_L)
                  G≡_A L-eq R-eq d_subst-L_eq final

lift-ConvTm (RT.conv-cong-App-Ty _ _ dA dB dc da) =
  let IH_A = lift-ConvTy dA
      G_A = LiftConvTy.G' IH_A
      A_L = LiftConvTy.A' IH_A
      A_R = LiftConvTy.B' IH_A
      G≡_A = LiftConvTy.G≡ IH_A
      AL_eq = LiftConvTy.A≡ IH_A
      AR_eq = LiftConvTy.B≡ IH_A
      der_A = LiftConvTy.der IH_A
      dAL = TM.presup-l-ConvTy der_A
      target_inner = TT.extend G_A A_L
      wf_inner = TT.wf-extend dAL
      IH_B = lift-ConvTy dB
      G_B = LiftConvTy.G' IH_B
      B_L = LiftConvTy.A' IH_B
      B_R = LiftConvTy.B' IH_B
      G≡_B = LiftConvTy.G≡ IH_B
      BL_eq = LiftConvTy.A≡ IH_B
      BR_eq = LiftConvTy.B≡ IH_B
      der_B = LiftConvTy.der IH_B
      eq_B-tgt = Eq-trans G≡_B (Eq-sym (Eq-cong2 RT.extend G≡_A AL_eq))
      der_B' = move-ConvTy G_B target_inner wf_inner eq_B-tgt der_B
      dBL = TM.presup-l-ConvTy der_B'
      Pi_L = T.Pi A_L B_L
      dPi_L = TT.is-Ty-Pi dAL dBL
      Pi_L_eq = Eq-cong2 R.Pi AL_eq BL_eq
      IH_c = lift-HasType dc
      G_c = LiftHasType.G' IH_c
      c_T = LiftHasType.M' IH_c
      Ac_T = LiftHasType.A' IH_c
      G≡_c = LiftHasType.G≡ IH_c
      c_eq = LiftHasType.M≡ IH_c
      Ac_eq = LiftHasType.A≡ IH_c
      der_c = LiftHasType.der IH_c
      wf_A = TM.isType-WfCtx dAL
      eq_c-A = Eq-trans G≡_c (Eq-sym G≡_A)
      der_c' = move-HasType G_c G_A wf_A eq_c-A der_c
      der_c'' = coerce-HasType-to der_c' dPi_L (Eq-trans Ac_eq (Eq-sym Pi_L_eq))
      IH_a = lift-HasType da
      G_a = LiftHasType.G' IH_a
      a_T = LiftHasType.M' IH_a
      Aa_T = LiftHasType.A' IH_a
      G≡_a = LiftHasType.G≡ IH_a
      a_eq = LiftHasType.M≡ IH_a
      Aa_eq = LiftHasType.A≡ IH_a
      der_a = LiftHasType.der IH_a
      eq_a-A = Eq-trans G≡_a (Eq-sym G≡_A)
      der_a' = move-HasType G_a G_A wf_A eq_a-A der_a
      der_a'' = coerce-HasType-to der_a' dAL (Eq-trans Aa_eq (Eq-sym AL_eq))
      final = TM.mk-conv-cong-App-Ty der_A der_B' der_c'' der_a''
      L-eq = Eq-cong4 R.App AL_eq BL_eq c_eq a_eq
      R-eq = Eq-cong4 R.App AR_eq BR_eq c_eq a_eq
      Subst-eq = Eq-trans (E.erase-subst1 B_L a_T)
                          (Eq-cong2 R.subst1 BL_eq a_eq)
  in mkLiftConvTm G_A (T.App A_L B_L c_T a_T) (T.App A_R B_R c_T a_T)
                  (T.subst1 B_L a_T)
                  G≡_A L-eq R-eq Subst-eq final

lift-ConvTm (RT.conv-beta dA dB db da) =
  let IH_A = lift-IsType dA
      G_A = LiftIsType.G' IH_A
      A_T = LiftIsType.A' IH_A
      G≡_A = LiftIsType.G≡ IH_A
      A_eq = LiftIsType.A≡ IH_A
      der_A = LiftIsType.der IH_A
      target_inner = TT.extend G_A A_T
      wf_inner = TT.wf-extend der_A
      IH_B = lift-IsType dB
      G_B = LiftIsType.G' IH_B
      B_T = LiftIsType.A' IH_B
      G≡_B = LiftIsType.G≡ IH_B
      B_eq = LiftIsType.A≡ IH_B
      der_B = LiftIsType.der IH_B
      eq_B-tgt = Eq-trans G≡_B (Eq-sym (Eq-cong2 RT.extend G≡_A A_eq))
      der_B' = move-IsType G_B target_inner wf_inner eq_B-tgt der_B
      IH_b = lift-HasType db
      G_b = LiftHasType.G' IH_b
      b_T = LiftHasType.M' IH_b
      Ab_T = LiftHasType.A' IH_b
      G≡_b = LiftHasType.G≡ IH_b
      b_eq = LiftHasType.M≡ IH_b
      Ab_eq = LiftHasType.A≡ IH_b
      der_b = LiftHasType.der IH_b
      eq_b-tgt = Eq-trans G≡_b (Eq-sym (Eq-cong2 RT.extend G≡_A A_eq))
      der_b' = move-HasType G_b target_inner wf_inner eq_b-tgt der_b
      der_b'' = coerce-HasType-to der_b' der_B' (Eq-trans Ab_eq (Eq-sym B_eq))
      IH_a = lift-HasType da
      G_a = LiftHasType.G' IH_a
      a_T = LiftHasType.M' IH_a
      Aa_T = LiftHasType.A' IH_a
      G≡_a = LiftHasType.G≡ IH_a
      a_eq = LiftHasType.M≡ IH_a
      Aa_eq = LiftHasType.A≡ IH_a
      der_a = LiftHasType.der IH_a
      wf_A = TM.isType-WfCtx der_A
      eq_a-A = Eq-trans G≡_a (Eq-sym G≡_A)
      der_a' = move-HasType G_a G_A wf_A eq_a-A der_a
      der_a'' = coerce-HasType-to der_a' der_A (Eq-trans Aa_eq (Eq-sym A_eq))
      final = TT.conv-beta der_A der_B' der_b'' der_a''
      L-eq = Eq-cong4 R.App A_eq B_eq
                (Eq-cong3 R.Lam A_eq B_eq b_eq) a_eq
      R-eq = Eq-trans (E.erase-subst1 b_T a_T)
                      (Eq-cong2 R.subst1 b_eq a_eq)
      Subst-eq = Eq-trans (E.erase-subst1 B_T a_T)
                          (Eq-cong2 R.subst1 B_eq a_eq)
  in mkLiftConvTm G_A
                  (T.App A_T B_T (T.Lam A_T B_T b_T) a_T)
                  (T.subst1 b_T a_T)
                  (T.subst1 B_T a_T)
                  G≡_A L-eq R-eq Subst-eq final

lift-ConvTm (RT.conv-eta dA dB dc) =
  let IH_A = lift-IsType dA
      G_A = LiftIsType.G' IH_A
      A_T = LiftIsType.A' IH_A
      G≡_A = LiftIsType.G≡ IH_A
      A_eq = LiftIsType.A≡ IH_A
      der_A = LiftIsType.der IH_A
      target_inner = TT.extend G_A A_T
      wf_inner = TT.wf-extend der_A
      IH_B = lift-IsType dB
      G_B = LiftIsType.G' IH_B
      B_T = LiftIsType.A' IH_B
      G≡_B = LiftIsType.G≡ IH_B
      B_eq = LiftIsType.A≡ IH_B
      der_B = LiftIsType.der IH_B
      eq_B-tgt = Eq-trans G≡_B (Eq-sym (Eq-cong2 RT.extend G≡_A A_eq))
      der_B' = move-IsType G_B target_inner wf_inner eq_B-tgt der_B
      Pi_T = T.Pi A_T B_T
      dPi = TT.is-Ty-Pi der_A der_B'
      Pi_eq = Eq-cong2 R.Pi A_eq B_eq
      IH_c = lift-HasType dc
      G_c = LiftHasType.G' IH_c
      c_T = LiftHasType.M' IH_c
      Ac_T = LiftHasType.A' IH_c
      G≡_c = LiftHasType.G≡ IH_c
      c_eq = LiftHasType.M≡ IH_c
      Ac_eq = LiftHasType.A≡ IH_c
      der_c = LiftHasType.der IH_c
      wf_A = TM.isType-WfCtx der_A
      eq_c-A = Eq-trans G≡_c (Eq-sym G≡_A)
      der_c' = move-HasType G_c G_A wf_A eq_c-A der_c
      der_c'' = coerce-HasType-to der_c' dPi (Eq-trans Ac_eq (Eq-sym Pi_eq))
      final = TT.conv-eta der_A der_B' der_c''
      body-eq = Eq-cong4 R.App
                  (E.erase-wk A_T)
                  (E.erase-ren (liftRen wkRen) B_T)
                  (E.erase-wk c_T)
                  (refl {x = R.Var fzero})
      body-eq-full : Eq (E.erase (T.App (T.wkExpr A_T)
                                         (T.renExpr (liftRen wkRen) B_T)
                                         (T.wkExpr c_T) (T.Var fzero))) _
      body-eq-full = Eq-trans body-eq
                       (Eq-cong4 R.App
                          (Eq-cong R.wkExpr A_eq)
                          (Eq-cong (R.renExpr (liftRen wkRen)) B_eq)
                          (Eq-cong R.wkExpr c_eq)
                          refl)
      L-eq = c_eq
      R-eq = Eq-cong3 R.Lam A_eq B_eq body-eq-full
  in mkLiftConvTm G_A c_T
       (T.Lam A_T B_T (T.App (T.wkExpr A_T)
                              (T.renExpr (liftRen wkRen) B_T)
                              (T.wkExpr c_T) (T.Var fzero)))
       Pi_T G≡_A L-eq R-eq Pi_eq final

------------------------------------------------------------------------
-- Final theorem record
------------------------------------------------------------------------

record Equivalence : Set₁ where
  field
    sound-IsType  : {n : Nat} {G : TT.Ctx n} {A : T.Expr n}
                  -> TT.IsType G A -> RT.IsType (eraseCtx G) (E.erase A)
    sound-HasType : {n : Nat} {G : TT.Ctx n} {M A : T.Expr n}
                  -> TT.HasType G M A
                  -> RT.HasType (eraseCtx G) (E.erase M) (E.erase A)
    lifts-IsType  : {n : Nat} {G : RT.Ctx n} {A : R.Expr n}
                  -> RT.IsType G A -> LiftIsType G A
    lifts-HasType : {n : Nat} {G : RT.Ctx n} {M A : R.Expr n}
                  -> RT.HasType G M A -> LiftHasType G M A
    uniq-Ty : TypeUniqStatement
    uniq-Tm : TermUniqStatement

equivalence : Equivalence
equivalence = record
  { sound-IsType  = erase-IsType
  ; sound-HasType = erase-HasType
  ; lifts-IsType  = lift-IsType
  ; lifts-HasType = lift-HasType
  ; uniq-Ty       = type-uniq
  ; uniq-Tm       = term-uniq
  }
