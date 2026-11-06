(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctShape AxSymExec3K AxSymExec3SoundK AxSymRun3K AsanPlanCoreK AsanPlanK AsanPlanSoundK.
Import ListNotations.
Import AX2K.
Unset Nia Cache. Unset Nra Cache. Import AX2SK. Import APK. Import APSK.
Open Scope Z_scope.

Section Iface.
Variable SEGS : list Segment.
Variable scfg : SpuriousCfg.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.

(* [comment removed for export] *)
Definition OBL_mmap2 : Prop := forall split : bool, mm2_stmt SEGS scfg A nx0 LIMIT SINV argH FS0 (node_mmap2 A nx0 LIMIT split).   (* [comment removed for export] *)
Definition OBL_mmapin : Prop := forall hole : bool, mm3_stmt SEGS scfg A nx0 LIMIT SINV argH FS0 (node_mmapin A LIMIT hole).   (* [comment removed for export] *)
Definition OBL_mprotect2 : Prop := mm2_stmt SEGS scfg A nx0 LIMIT SINV argH FS0 (node_mprotect2 A LIMIT).
Definition OBL_brk2 : Prop := brk2_stmt SEGS scfg A nx0 LIMIT SINV argH FS0.
Definition OBL_sys : Prop := forall y : snode, sys_stmt SEGS scfg A nx0 LIMIT SINV argH FS0 y.
Definition OBL_exit : Prop := exit_stmt SEGS scfg A LIMIT SINV argH FS0.

(* [comment removed for export] *)
Definition OBL_all : Prop := OBL_mmap2 /\ OBL_mmapin /\ OBL_mprotect2 /\ OBL_brk2 /\ OBL_sys /\ OBL_exit.

(* [comment removed for export] *)
Lemma OBL_mmap2_unfold :
  OBL_mmap2 <->
  forall split cs csa csb E R FULL model TB,
    cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model ->
    is_ecall_at SEGS cs = true ->
    node_mmap2 A nx0 LIMIT split cs = Some (csa, csb) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' ->
        cs_ok SEGS A LIMIT SINV argH FS0 E' csa R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS scfg (cfg_of SEGS R' (pc csa) FULL' model') TB) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' ->
        cs_ok SEGS A LIMIT SINV argH FS0 E' csb R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS scfg (cfg_of SEGS R' (pc csb) FULL' model') TB) ->
    srealizes SEGS scfg (cfg_of SEGS R (pc cs) FULL model) TB.
Proof. unfold OBL_mmap2, mm2_stmt. tauto. Qed.
End Iface.
