(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctShape AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Section Iface.
Context {fx : FPState}.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.

(* [comment removed for export] *)
Definition OBL_mmap : Prop := mmap_stmtW SEGS A nx0 LIMIT SINV argH FS0.   (* [comment removed for export] *)
Definition OBL_mmapin : Prop := node1_stmt SEGS A nx0 LIMIT SINV argH FS0 (is_ecall_at SEGS) (node_mmapin A LIMIT).
Definition OBL_mprotect : Prop := node1_stmt SEGS A nx0 LIMIT SINV argH FS0 (is_ecall_at SEGS) (node_mprotect A LIMIT).
(* [comment removed for export] *)
Definition OBL_sys : Prop := forall y : snode, sys_stmt SEGS A nx0 LIMIT SINV argH FS0 y.
Definition OBL_exit : Prop := exit_stmt SEGS A LIMIT SINV argH FS0.

(* [comment removed for export] *)
Definition OBL_all : Prop := OBL_mmap /\ OBL_mmapin /\ OBL_mprotect /\ OBL_sys /\ OBL_exit.

(* [comment removed for export] *)
Lemma OBL_mmap_unfold :
  OBL_mmap <->
  forall cs cs' E R FULL model T,
    cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model ->
    is_ecall_at SEGS cs = true ->
    node_mmap A nx0 LIMIT cs = Some cs' ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' ->
        cs_ok SEGS A LIMIT SINV argH FS0 E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
        (forall W a, AP.mmap_win A cs' = Some W -> ws_out E' W a -> FULL' a = FULL a) ->
        (forall W a, AP.mmap_win A cs' = Some W -> ws_out E' W a -> hid A argH E' cs' model' a = hid A argH E cs model a) ->
        srealizes SEGS (cfg_of SEGS R' (pc cs') FULL' model') T) ->
    srealizes SEGS (cfg_of SEGS R (pc cs) FULL model) T.
Proof. unfold OBL_mmap, mmap_stmtW, node1_stmtWP. tauto. Qed.
(* [comment removed for export] *)
Lemma OBL_mmap_plain : OBL_mmap -> node1_stmt SEGS A nx0 LIMIT SINV argH FS0 (is_ecall_at SEGS) (node_mmap A nx0 LIMIT).
Proof. intros H. exact (node1_stmtWP_stmt SEGS A nx0 LIMIT SINV argH FS0 _ _ _ H). Qed.
End Iface.
