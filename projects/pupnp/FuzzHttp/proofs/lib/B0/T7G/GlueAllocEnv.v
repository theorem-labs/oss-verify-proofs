(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes Image Ceiling.
From OSSVerify.pupnp.FuzzHttp.images Require Import AsanUbsan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import MainExport MainFactsBoth B0Img MainEntryBoth B0Handoff.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout PEnv AInitReps AQuar AQuarT F_hooks F_free_icpt F_alloc_env F_ialloc.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7G Require Import GlueKit GlueIcpt GlueAllocKit GlueAllocLay.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma poison_env_init : forall V (m : mem), Forall (mfact_ok asegs V m) both_mem_facts -> poison_env (E_of V) m.
Proof.
  intros V m HM. unfold poison_env, E_of. cbn [pe_canary pe_dontdump pe_nohuge].
  split. { lcells V m HM constr:(GOT_CF) [C8 (wz CF)] H. exact H. }
  split. { lcells V m HM constr:(CF_CLEAR_THR) [C8 (wz 18446744073709551615)] H. exact H. }
  split. { lcells V m HM constr:(CF_LIMIT) [C8 (wz 0)] H. exact H. }
  split. { lcells V m HM constr:(CF_DECOR) [C1 (Z_to_bv 8 0)] H. exact H. }
  split. { lcells V m HM constr:(GOT_AF) [C8 (wz AF)] H. exact H. }
  split. { lcells V m HM constr:(AF_PSG) [C1 (Z_to_bv 8 1)] H. exact H. }
  split. { lcells V m HM constr:(GOT_SHB) [C8 (wz SHB_CELL)] H. exact H. }
  split. { lcells V m HM constr:(SHB_CELL) [C8 (wz 2147450880)] H. exact H. }
  split. { lcells V m HM constr:(GOT_MIDB) [C8 (wz 741928); C8 (wz 741936); C8 (wz HME_CELL); C8 (wz RMS_CELL)] H. exact H. }
  split. { lcells V m HM constr:(HME_CELL) [C8 (wz 140737488355327); C8 (wz 0); C8 (wz 0)] H. exact H. }
  split. { lcells V m HM constr:(RMS_CELL) [C8 (wz A0_MEMSET)] H. exact H. }
  split. { lcells V m HM constr:(CANPOISON) [C1 (Z_to_bv 8 1)] H. exact H. }
  split. { lcells V m HM constr:(SEALED) [C8 (wz 1)] H. exact H. }
  split. { lcells V m HM constr:(GOT_PAGE) [C8 (wz PAGE_CELL)] H. exact H. }
  split. { lcells V m HM constr:(PAGE_CELL) [C8 (wz 4096)] H. exact H. }
  split. { lcells V m HM constr:(CF_DONTDUMP) [C1 (Z_to_bv 8 1)] H. exact H. }
  split. { lcells V m HM constr:(CF_NOHUGE) [C1 (Z_to_bv 8 1)] H. exact H. }
  split. { lcells V m HM constr:(GOT_GUARD) [C8 (wz GUARD_CELL)] H. exact H. }
  split. { mf V m HM (MRo (ZLit 6321648) 8 (ZV 45)) G. exact (canary_cell m _ G). }
  split. { lcells V m HM constr:(LIBC_PAGESIZE) [C8 (wz 4096)] H. exact H. }
  split; lia.
Qed.

Lemma thread_env_init : forall V (m : mem), Forall (mfact_ok asegs V m) both_mem_facts -> thread_env (al_thread (AL_of V)) m.
Proof.
  intros V m HM. unfold thread_env, AL_of, top_of. cbn [al_thread at_ctx at_thr at_top at_bottom].
  split. { lcells V m HM constr:(A0_TSD_INITED) [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (wz 0)] H. exact H. }
  split. { lcells V m HM constr:(A0_ASAN_INITED) [C1 (Z_to_bv 8 1)] H. exact H. }
  split. { lcells V m HM 6190424 [C8 (wz A0_TSD)] H. exact H. }
  split. { mf V m HM (MCell (ZLit 6326616) 8 (ZMul (ZLit 4096) (ZV 228))) H. exact H. }
  split. { mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 152)) 8 (ZMul (ZLit 4096) (ZV 227))) H. exact H. }
  split. { mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 8)) 8 (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 4096) (ZV 10)) (ZMul (ZLit 4096) (ZV 344))))) H1.
           mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 16)) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 4096) (ZV 10)) (ZMul (ZLit 4096) (ZV 344)))) (ZLit (-8388608)))) H2.
           apply (proj2 (GlueIcpt.rw_cells_app asegs m _ [_] [_])). split; [exact H1|]. cbn [cells_size csize Nat.add].
           replace (4096 * V 227%nat + 8 + Z.of_nat 8) with (4096 * V 227%nat + 16) by lia. exact H2. }
  split. { mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 40)) 1 (ZLit 0)) H. exact H. }
  split. { mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 3168)) 1 (ZLit 0)) H. exact H. }
  split. { lcells V m HM constr:(GOT_PAGE) [C8 (wz PAGE_CELL)] H. exact H. }
  lcells V m HM constr:(PAGE_CELL) [C8 (wz 4096)] H. exact H.
Qed.

Lemma thread_env2_init : forall V (m : mem), Forall (mfact_ok asegs V m) both_mem_facts -> thread_env2 (AL_of V) m.
Proof.
  intros V m HM. unfold thread_env2, AL_of. cbn [al_thread at_ctx at_thr]. split.
  - mf V m HM (MCell (ZMul (ZLit 4096) (ZV 227)) 8 (ZMul (ZLit 4096) (ZV 228))) H. exact H.
  - exists (wz 0). mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 8)) 4 (ZLit 0)) H. exact H.
Qed.

Lemma quar_env_init : forall V (m : mem), Forall (mfact_ok asegs V m) both_mem_facts -> quar_env m.
Proof.
  intros V m HM. unfold quar_env. split.
  - lcells V m HM constr:(QUAR_CONST) [C8 (wz Q_MAX); C8 (wz Q_MIN); C8 (wz Q_CACHE)] H. exact H.
  - lcells V m HM constr:(AF_MAXFILL) [C4 (wz 0)] H. exact H.
Qed.

Lemma hooks_env_init : forall V (m : mem), Forall (mfact_ok asegs V m) both_mem_facts -> hooks_env m.
Proof. intros V m HM. unfold hooks_env. lcells V m HM constr:(HOOKS) [C8 (wz 0); C8 (wz 0)] H. exact H. Qed.

Lemma trace_env_init : forall V (m : mem), Forall (mfact_ok asegs V m) both_mem_facts -> trace_env m.
Proof.
  intros V m HM. unfold trace_env.
  split. { lcells V m HM 0xb523c [C4 (wz 30)] H. exact H. }
  split. { lcells V m HM 0xaad20 [C8 (wz 0x146068)] H. exact H. }
  lcells V m HM 0x14608a [C1 (Z_to_bv 8 1)] H. exact H.
Qed.

Lemma alloc_env_init : forall V (m : mem), Forall (mfact_ok asegs V m) both_mem_facts -> alloc_env m.
Proof.
  intros V m HM. unfold alloc_env.
  split. { lcells V m HM constr:(INST_MAXMALLOC) [C8 (wz 1099511627776); C2 (wz 16); C2 (wz 2048)] H. exact H. }
  split. { lcells V m HM constr:(AF_MALLOCFILL) [C4 (wz 4096)] H. exact H. }
  split. { lcells V m HM constr:(AF_FILLBYTE) [C4 (wz 190)] H. exact H. }
  split. { lcells V m HM constr:(AF_PARTIAL) [C1 (Z_to_bv 8 1)] H. exact H. }
  split. { lcells V m HM constr:(RSS_EXCEEDED) [C1 (Z_to_bv 8 0)] H. exact H. }
  split. { lcells V m HM constr:(GOT_LSAN_OFF) [C8 (wz 16)] H. exact H. }
  lcells V m HM constr:(LSAN_DISABLED) [C4 (wz 0)] H. exact H.
Qed.

Lemma ia_cells_init : forall V (m : mem), Forall (mfact_ok asegs V m) both_mem_facts -> exists inited, ia_cells 262144 262728 inited m.
Proof.
  intros V m HM. exists false. unfold ia_cells, ia_flag.
  split. { lcells V m HM constr:(IA_FLAG) [CB 4 [b8 0; b8 0; b8 0; b8 0]] H. exact H. }
  split. { exact (junk_cells m IA_BASE 8 ltac:(lia) ltac:(lia)). }
  split. { destruct (junk_cells m IA_MAP1 (Z.to_nat 262144) ltac:(lia) ltac:(lia)) as (j & J). exists j. split; [exact J| intros X; discriminate X]. }
  split. { exact (junk_cells m IA_R3 3456 ltac:(lia) ltac:(lia)). }
  split. { exact (junk_cells m IA_R4 (Z.to_nat 262728) ltac:(lia) ltac:(lia)). }
  exact (junk_cells m IA_R1 40 ltac:(lia) ltac:(lia)).
Qed.
