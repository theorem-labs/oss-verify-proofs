(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AxSymExec3Sound AsanPlanCore CxPlan CxPlanSound H0Sel H0TgtGlue HTSpec H0FiPre H0FiTail.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import H0FamilyAllDefs H0FamilyAll.
From OSSVerify.Proofs.openssl.hashtable.lib Require H0FamilyAllDefs.
From OSSVerify.Proofs.openssl.hashtable.lib.H0Chk Require Import H0BrGlue2 H0GlueK H0Chk0 H0Chk1 H0Chk2 H0Chk3 H0Chk4 H0Chk5 H0Chk6 H0Chk7 H0Chk8 H0Chk9 H0Chk10.
Import ListNotations. Import AX2. Import CAP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Definition HASHF0 : kentry := H0FamilyAllDefs.HASHF.
Lemma hashf0_shape : HASHF0 = KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 11)) (ehash_of HASHF0)) 0 0.
Proof. reflexivity. Qed.
Lemma hashf0_closed : CAP.expr_vars_lt 0 (ehash_of HASHF0) = true.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma heokc : forall k content CS E, In CS (CSL k) -> tin_ok k (tin_of content) ->
  eokx (CAP.nxt CS - 3) (CAP.nxt CS - 4) (CAP.nxt CS - 2) (CAP.nxt CS - 1) HASHF0 (tin_of content) E -> EOKc k content CS E.
Proof.
  intros k content CS E HCS Htin He. unfold EOKc. split; [exact Htin|].
  repeat match goal with |- _ /\ _ => split end; intros -> ->; exact He.
Qed.
Lemma CHK : forall k, In k KS -> forallb (leaf_chk k (TB_std k) (CSL k) XRNGf (XCHKf k)) (tree_leaves (the_tree k FUEL)) = true.
Proof.
  intros k Hk. unfold KS in Hk.
  destruct Hk as [<-|Hk]; [exact chk_0|].
  destruct Hk as [<-|Hk]; [exact chk_1|].
  destruct Hk as [<-|Hk]; [exact chk_2|].
  destruct Hk as [<-|Hk]; [exact chk_3|].
  destruct Hk as [<-|Hk]; [exact chk_4|].
  destruct Hk as [<-|Hk]; [exact chk_5|].
  destruct Hk as [<-|Hk]; [exact chk_6|].
  destruct Hk as [<-|Hk]; [exact chk_7|].
  destruct Hk as [<-|Hk]; [exact chk_8|].
  destruct Hk as [<-|Hk]; [exact chk_9|].
  destruct Hk as [<-|Hk]; [exact chk_10|].
  destruct Hk.
Qed.
Theorem h0_leaf_tail : leaf_tail_stmt t_target_ht.
Proof. exact (h0_leaf_tail_k HASHF0 hashf0_shape hashf0_closed CSL EOKc family_all heokc CHK). Qed.
(* [comment removed for export] *)
