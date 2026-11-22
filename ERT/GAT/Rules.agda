{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERT.GAT.Rules
--
-- The judgements and rules of the Ehrhard-style GAT, one family GDer
-- indexed by the judgement form (as UNIT/GAT.seg, with ERT's levels:
-- guc m l, glf m l a for l < m, and ERT's six Tarski equations).
-- Extra (admissible) premises as in UNIT/GAT.seg; gs-cx converts both
-- ends of a substitution.
------------------------------------------------------------------------

module ERT.GAT.Rules where

open import ERT.Basic
open import ERT.GAT.Syntax

data GJ : Set where
  gjwf    : {n : Nat} -> GC n -> GJ
  gjty    : {n : Nat} -> GC n -> GE n -> GJ
  gjtm    : {n : Nat} -> GC n -> GE n -> GE n -> GJ
  gjsub   : {n m : Nat} -> GC n -> GS n m -> GC m -> GJ
  gjeqcx  : {n : Nat} -> GC n -> GC n -> GJ
  gjeqty  : {n : Nat} -> GC n -> GE n -> GE n -> GJ
  gjeqtm  : {n : Nat} -> GC n -> GE n -> GE n -> GE n -> GJ
  gjeqsub : {n m : Nat} -> GC n -> GS n m -> GS n m -> GC m -> GJ

variable
  m n p l nu : Nat
  G G' D D' T Q : GC _
  A A' B B' C a a' b b' c c' f : GE _
  s s' t u d d' e : GS _ _

data GDer : GJ -> Set where
  g-nil : GDer (gjwf gnil)
  g-ext : GDer (gjty G A) -> GDer (gjwf (gext G A))
  gc-nil : GDer (gjeqcx gnil gnil)
  gc-refl : GDer (gjwf G) -> GDer (gjeqcx G G)
  gc-ext : GDer (gjeqcx G D) -> GDer (gjeqty G A B) -> GDer (gjeqcx (gext G A) (gext D B))
  gs-id : GDer (gjwf G) -> GDer (gjsub G gid G)
  gs-comp : GDer (gjsub D s G) -> GDer (gjsub T d D) -> GDer (gjsub T (gcomp s d) G)
  gs-eps : GDer (gjwf G) -> GDer (gjsub G geps gnil)
  gs-p : GDer (gjty G A) -> GDer (gjsub (gext G A) gp G)
  gs-lift : GDer (gjsub D s G) -> GDer (gjty G A) -> GDer (gjsub (gext D (gsb A s)) (glift A s) (gext G A))
  gs-sec : GDer (gjty G A) -> GDer (gjtm G a A) -> GDer (gjsub G (gsec A a) (gext G A))
  gs-cx : GDer (gjwf D') -> GDer (gjwf G') -> GDer (gjeqcx D D') -> GDer (gjeqcx G G') -> GDer (gjsub D s G) -> GDer (gjsub D' s G')
  gt-pi : GDer (gjty G A) -> GDer (gjty (gext G A) B) -> GDer (gjty G (gpi A B))
  gt-uu : GDer (gjwf G) -> GDer (gjty G (guu n))
  gt-el : GDer (gjtm G a (guu n)) -> GDer (gjty G (gel n a))
  gt-sb : GDer (gjty G A) -> GDer (gjsub D s G) -> GDer (gjty D (gsb A s))
  gt-cx : GDer (gjwf D) -> GDer (gjeqcx G D) -> GDer (gjty G A) -> GDer (gjty D A)
  gm-lam : GDer (gjty G A) -> GDer (gjty (gext G A) B) -> GDer (gjtm (gext G A) b B) -> GDer (gjtm G (glam A B b) (gpi A B))
  gm-app : GDer (gjty G A) -> GDer (gjty (gext G A) B) -> GDer (gjtm G c (gpi A B)) -> GDer (gjtm G a A) -> GDer (gjtm G (gapp A B c a) (gsb B (gsec A a)))
  gm-pic : GDer (gjtm G a (guu n)) -> GDer (gjtm (gext G (gel n a)) b (guu n)) -> GDer (gjtm G (gpic n a b) (guu n))
  gm-uc : GDer (gjwf G) -> Lt l m -> GDer (gjtm G (guc m l) (guu m))
  gm-lf : Lt l m -> GDer (gjtm G a (guu l)) -> GDer (gjtm G (glf m l a) (guu m))
  gm-q : GDer (gjty G A) -> GDer (gjtm (gext G A) gq (gsb A gp))
  gm-sb : GDer (gjty G A) -> GDer (gjtm G a A) -> GDer (gjsub D s G) -> GDer (gjtm D (gsb a s) (gsb A s))
  gm-conv : GDer (gjtm G a A) -> GDer (gjeqty G A B) -> GDer (gjtm G a B)
  gm-cx : GDer (gjwf D) -> GDer (gjeqcx G D) -> GDer (gjtm G a A) -> GDer (gjtm D a A)
  ge-refl : GDer (gjty G A) -> GDer (gjeqty G A A)
  ge-sym : GDer (gjeqty G A B) -> GDer (gjeqty G B A)
  ge-trans : GDer (gjeqty G A B) -> GDer (gjeqty G B C) -> GDer (gjeqty G A C)
  ge-pi : GDer (gjty G A) -> GDer (gjeqty G A A') -> GDer (gjeqty (gext G A) B B') -> GDer (gjeqty G (gpi A B) (gpi A' B'))
  ge-el : GDer (gjeqtm G a a' (guu n)) -> GDer (gjeqty G (gel n a) (gel n a'))
  ge-sb : GDer (gjty G A) -> GDer (gjeqty G A A') -> GDer (gjsub D s G) -> GDer (gjsub D s' G) -> GDer (gjeqsub D s s' G) -> GDer (gjeqty D (gsb A s) (gsb A' s'))
  ge-el-lf : Lt l m -> GDer (gjtm G a (guu l)) -> GDer (gjeqty G (gel m (glf m l a)) (gel l a))
  ge-el-pic : GDer (gjtm G a (guu n)) -> GDer (gjtm (gext G (gel n a)) b (guu n)) -> GDer (gjeqty G (gel n (gpic n a b)) (gpi (gel n a) (gel n b)))
  ge-el-uc : GDer (gjwf G) -> Lt l m -> GDer (gjeqty G (gel m (guc m l)) (guu l))
  ge-sb-id : GDer (gjty G A) -> GDer (gjeqty G (gsb A gid) A)
  ge-sb-comp : GDer (gjty G A) -> GDer (gjsub D s G) -> GDer (gjsub T d D) -> GDer (gjeqty T (gsb (gsb A s) d) (gsb A (gcomp s d)))
  ge-pi-sb : GDer (gjty G A) -> GDer (gjty (gext G A) B) -> GDer (gjsub D s G) -> GDer (gjeqty D (gsb (gpi A B) s) (gpi (gsb A s) (gsb B (glift A s))))
  ge-uu-sb : GDer (gjsub D s G) -> GDer (gjeqty D (gsb (guu n) s) (guu n))
  ge-el-sb : GDer (gjtm G a (guu n)) -> GDer (gjsub D s G) -> GDer (gjeqty D (gsb (gel n a) s) (gel n (gsb a s)))
  ge-cx : GDer (gjwf D) -> GDer (gjeqcx G D) -> GDer (gjeqty G A B) -> GDer (gjeqty D A B)
  gm-refl : GDer (gjtm G a A) -> GDer (gjeqtm G a a A)
  gm-sym : GDer (gjty G A) -> GDer (gjeqtm G a b A) -> GDer (gjeqtm G b a A)
  gm-trans : GDer (gjeqtm G a b A) -> GDer (gjeqtm G b c A) -> GDer (gjeqtm G a c A)
  gm-eqconv : GDer (gjeqtm G a b A) -> GDer (gjeqty G A B) -> GDer (gjeqtm G a b B)
  gm-elam : GDer (gjty G A) -> GDer (gjeqty G A A') -> GDer (gjeqty (gext G A) B B') -> GDer (gjeqtm (gext G A) b b' B) -> GDer (gjeqtm G (glam A B b) (glam A' B' b') (gpi A B))
  gm-eapp : GDer (gjty G A) -> GDer (gjty (gext G A) B) -> GDer (gjtm G a A) -> GDer (gjeqty G A A') -> GDer (gjeqty (gext G A) B B') -> GDer (gjeqtm G c c' (gpi A B)) -> GDer (gjeqtm G a a' A) -> GDer (gjeqtm G (gapp A B c a) (gapp A' B' c' a') (gsb B (gsec A a)))
  gm-epic : GDer (gjtm G a (guu n)) -> GDer (gjeqtm G a a' (guu n)) -> GDer (gjeqtm (gext G (gel n a)) b b' (guu n)) -> GDer (gjeqtm G (gpic n a b) (gpic n a' b') (guu n))
  gm-elf : Lt l m -> GDer (gjeqtm G a a' (guu l)) -> GDer (gjeqtm G (glf m l a) (glf m l a') (guu m))
  gm-esb : GDer (gjty G A) -> GDer (gjtm G a A) -> GDer (gjeqtm G a a' A) -> GDer (gjsub D s G) -> GDer (gjsub D s' G) -> GDer (gjeqsub D s s' G) -> GDer (gjeqtm D (gsb a s) (gsb a' s') (gsb A s))
  gm-beta : GDer (gjty G A) -> GDer (gjty (gext G A) B) -> GDer (gjtm (gext G A) b B) -> GDer (gjtm G a A) -> GDer (gjeqtm G (gapp A B (glam A B b) a) (gsb b (gsec A a)) (gsb B (gsec A a)))
  gm-eta : GDer (gjty G A) -> GDer (gjty (gext G A) B) -> GDer (gjtm G f (gpi A B)) -> GDer (gjeqtm G f (glam A B (gapp (gsb A gp) (gsb B (glift A gp)) (gsb f gp) gq)) (gpi A B))
  gm-lf-pic : Lt l m -> GDer (gjtm G a (guu l)) -> GDer (gjtm (gext G (gel l a)) b (guu l)) ->
      GDer (gjeqtm G (glf m l (gpic l a b)) (gpic m (glf m l a) (glf m l b)) (guu m))
  gm-lf-uc : GDer (gjwf G) -> Lt nu l -> Lt l m -> GDer (gjeqtm G (glf m l (guc l nu)) (guc m nu) (guu m))
  gm-lf-lf : Lt l m -> Lt m nu -> GDer (gjtm G a (guu l)) ->
      GDer (gjeqtm G (glf nu m (glf m l a)) (glf nu l a) (guu nu))
  gm-sb-id : GDer (gjtm G a A) -> GDer (gjeqtm G (gsb a gid) a A)
  gm-sb-comp : GDer (gjtm G a A) -> GDer (gjsub D s G) -> GDer (gjsub T d D) -> GDer (gjeqtm T (gsb (gsb a s) d) (gsb a (gcomp s d)) (gsb A (gcomp s d)))
  gm-lam-sb : GDer (gjty G A) -> GDer (gjty (gext G A) B) -> GDer (gjtm (gext G A) b B) -> GDer (gjsub D s G) -> GDer (gjeqtm D (gsb (glam A B b) s) (glam (gsb A s) (gsb B (glift A s)) (gsb b (glift A s))) (gpi (gsb A s) (gsb B (glift A s))))
  gm-app-sb : GDer (gjty G A) -> GDer (gjty (gext G A) B) -> GDer (gjtm G c (gpi A B)) -> GDer (gjtm G a A) -> GDer (gjsub D s G) -> GDer (gjeqtm D (gsb (gapp A B c a) s) (gapp (gsb A s) (gsb B (glift A s)) (gsb c s) (gsb a s)) (gsb (gsb B (glift A s)) (gsec (gsb A s) (gsb a s))))
  gm-pic-sb : GDer (gjtm G a (guu n)) -> GDer (gjtm (gext G (gel n a)) b (guu n)) -> GDer (gjsub D s G) -> GDer (gjeqtm D (gsb (gpic n a b) s) (gpic n (gsb a s) (gsb b (glift (gel n a) s))) (guu n))
  gm-uc-sb : GDer (gjsub D s G) -> Lt l m -> GDer (gjeqtm D (gsb (guc m l) s) (guc m l) (guu m))
  gm-lf-sb : Lt l m -> GDer (gjtm G a (guu l)) -> GDer (gjsub D s G) ->
      GDer (gjeqtm D (gsb (glf m l a) s) (glf m l (gsb a s)) (guu m))
  gm-q-lift : GDer (gjty G A) -> GDer (gjsub D s G) -> GDer (gjeqtm (gext D (gsb A s)) (gsb gq (glift A s)) gq (gsb (gsb A s) gp))
  gm-q-sec : GDer (gjty G A) -> GDer (gjtm G a A) -> GDer (gjeqtm G (gsb gq (gsec A a)) a A)
  gm-ecx : GDer (gjwf D) -> GDer (gjeqcx G D) -> GDer (gjeqtm G a b A) -> GDer (gjeqtm D a b A)
  gq-refl : GDer (gjsub D s G) -> GDer (gjeqsub D s s G)
  gq-sym : GDer (gjeqsub D s t G) -> GDer (gjeqsub D t s G)
  gq-trans : GDer (gjeqsub D s t G) -> GDer (gjeqsub D t u G) -> GDer (gjeqsub D s u G)
  gq-comp : GDer (gjeqsub D s s' G) -> GDer (gjeqsub T d d' D) -> GDer (gjeqsub T (gcomp s d) (gcomp s' d') G)
  gq-lift : GDer (gjty G A) -> GDer (gjeqty G A A') -> GDer (gjsub D s G) -> GDer (gjeqsub D s s' G) -> GDer (gjeqsub (gext D (gsb A s)) (glift A s) (glift A' s') (gext G A))
  gq-sec : GDer (gjty G A) -> GDer (gjtm G a A) -> GDer (gjtm G a' A) -> GDer (gjeqty G A A') -> GDer (gjeqtm G a a' A) -> GDer (gjeqsub G (gsec A a) (gsec A' a') (gext G A))
  gq-idl : GDer (gjsub D s G) -> GDer (gjeqsub D (gcomp gid s) s G)
  gq-idr : GDer (gjsub D s G) -> GDer (gjeqsub D (gcomp s gid) s G)
  gq-assoc : GDer (gjsub D s G) -> GDer (gjsub T d D) -> GDer (gjsub Q e T) -> GDer (gjeqsub Q (gcomp (gcomp s d) e) (gcomp s (gcomp d e)) G)
  gq-eps : GDer (gjsub G s gnil) -> GDer (gjeqsub G s geps gnil)
  gq-lift-id : GDer (gjty G A) -> GDer (gjeqsub (gext G (gsb A gid)) (glift A gid) gid (gext G A))
  gq-lift-comp : GDer (gjty G A) -> GDer (gjsub D s G) -> GDer (gjsub T d D) -> GDer (gjeqsub (gext T (gsb A (gcomp s d))) (glift A (gcomp s d)) (gcomp (glift A s) (glift (gsb A s) d)) (gext G A))
  gq-p-lift : GDer (gjty G A) -> GDer (gjsub D s G) -> GDer (gjeqsub (gext D (gsb A s)) (gcomp gp (glift A s)) (gcomp s gp) G)
  gq-p-sec : GDer (gjty G A) -> GDer (gjtm G a A) -> GDer (gjeqsub G (gcomp gp (gsec A a)) gid G)
  gq-sec-comp : GDer (gjty G A) -> GDer (gjtm G a A) -> GDer (gjsub D s G) -> GDer (gjeqsub D (gcomp (gsec A a) s) (gcomp (glift A s) (gsec (gsb A s) (gsb a s))) (gext G A))
  gq-lift-p-sec-q : GDer (gjty G A) -> GDer (gjeqsub (gext G A) (gcomp (glift A gp) (gsec (gsb A gp) gq)) gid (gext G A))
