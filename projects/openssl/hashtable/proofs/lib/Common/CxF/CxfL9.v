(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec AxSymExec3 AsanPlanCore CxPlan CxfCarry CxfExec CxfNodes CxfPlan.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxfCheck CxfL1 CxfL2 CxfL3 CxfL4 CxfL5 CxfL6 CxfL7 CxfL8 CxfLeaf CxfNat.
Import ListNotations.
Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module CXFL.
Import CXF.
Notation "x && y" := (if x then y else false) (at level 40, left associativity) : bool_scope.
Notation "x || y" := (if x then true else y) (at level 50, left associativity) : bool_scope.
Import AX2.
Import AX2L.
Import APC.
Import APCL.
Import CAP.
Import CAPL.
Definition check_f (segs : list Segment) (IT : itab) (A : atable) (nx0 : nat) (LIMIT : Z)
  (XN : nat -> list expr -> acs -> option acs) (XE : nat -> list expr -> acs -> option (Z * list spiece * acs))
  (XB : nat -> list expr -> acs -> option (acs * acs)) (HS : nat -> option acs) (KC : nat) (FO SPIN GC : bool) (bfuel : nat)
  (fuel : nat) (lc : option loopctx) (cs : acs) (p : plan) : cres :=
  CXFPL.check_g segs IT A nx0 LIMIT XN XE XB HS FO SPIN (CXFEL.RB_f segs IT GC KC bfuel) (node_x segs A nx0) CXFNL.node_respell_f (entails_x segs A nx0)
               fuel lc cs p.
Lemma L_CXFL_check_f : @check_f = @CXF.check_f.
Proof. unfold check_f. rewrite ?CXFEL.L_CXFEL_RB_f, ?CXFPL.L_CXFPL_check_g, ?APCL.L_APCL_entails_x, ?AX2L.L_AX2L_itab, ?CXFNL.L_CXFNL_node_respell_f, ?CAPL.L_CAPL_node_x. reflexivity. Qed.

End CXFL.
