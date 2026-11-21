(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: every obligation holds at every flag of the flagged relation SpinAlg.srealizesM, and the mmap2 unfolding leaves its refused arm at the flag false. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import
  PropExec ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctShape.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import
  AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Section Iface.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : N.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.

(* [comment removed for export] *)
(* Every obligation at every flag of [SpinAlg.srealizesM]. *)
Definition OBL_mmap2 : Prop := forall fl, mm2_stmt SEGS A nx0 LIMIT SINV argH FS0 fl (node_mmap2 A nx0 LIMIT).
Definition OBL_mmapin : Prop := forall fl (hole : bool), mm3_stmt SEGS A nx0 LIMIT SINV argH FS0 fl (node_mmapin A LIMIT hole).
Definition OBL_mprotect2 : Prop := forall fl, mm2_stmt SEGS A nx0 LIMIT SINV argH FS0 fl (node_mprotect2 A LIMIT).
Definition OBL_brk2 : Prop := forall fl, brk2_stmt SEGS A nx0 LIMIT SINV argH FS0 fl.
Definition OBL_sys : Prop := forall fl (y : snode), sys_stmt SEGS A nx0 LIMIT SINV argH FS0 fl y.
Definition OBL_exit : Prop := forall fl, exit_stmt SEGS A LIMIT SINV argH FS0 fl.

(* [comment removed for export] *)
Definition OBL_all : Prop := OBL_mmap2 /\ OBL_mmapin /\ OBL_mprotect2 /\ OBL_brk2 /\ OBL_sys /\ OBL_exit.

(* [comment removed for export] *)
Lemma OBL_mmap2_unfold :
  OBL_mmap2 <->
  forall fl cs csa csb E R FULL model TA TB,
    cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model ->
    is_ecall_at SEGS cs = true ->
    node_mmap2 A nx0 LIMIT cs = Some (csa, csb) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' ->
        cs_ok SEGS A LIMIT SINV argH FS0 E' csa R' FULL' model' -> m_fs model' = m_fs model ->
        srealizesM SEGS false (cfg_of SEGS R' (pc csa) FULL' model') TA) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' ->
        cs_ok SEGS A LIMIT SINV argH FS0 E' csb R' FULL' model' -> m_fs model' = m_fs model ->
        srealizesM SEGS fl (cfg_of SEGS R' (pc csb) FULL' model') TB) ->
    srealizesM SEGS fl (cfg_of SEGS R (pc cs) FULL model) (t_alt2 TA TB).
Proof. unfold OBL_mmap2, mm2_stmt. tauto. Qed.
End Iface.
