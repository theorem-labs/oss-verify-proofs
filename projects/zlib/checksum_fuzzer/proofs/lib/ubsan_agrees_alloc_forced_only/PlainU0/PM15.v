(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Tac.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Image.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require ZBridge.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require SysStep.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Walk.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require ITree.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Nodes.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Decode.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require SFModel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU0 Require PImg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM11.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocTree.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocFacts_A.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocKit_A.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM14.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM08.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM13.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM12.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Malloc.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Malloc_fp.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocNat.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocFacts_AS.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require ASlot_W0.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require ASlot_W1.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require ASlot_I.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU0 Require RMallocRep.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU0 Require RMallocTree.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU0 Require RMallocKit_B.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU0 Require PM22.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU0 Require PM02.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU0 Require PM03.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU0 Require RASlot_W2.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU0 Require PM01.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM06.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM07.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU0 Require PM20.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM10.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU0 Require PM17.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require F_malloc_entry.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU0 Require PM21.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU0 Require RF_malloc_enf.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU0 Require RF_malloc_entry.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU0 Require RF_malloc_small.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module RASlot_W19.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Decode. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU0 Require Import PImg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM11. Import MM11. Import MM11.F_malloc_enframe. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocFacts_A. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocKit_A. Import MM11.MallocKit_AB. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM14. Import MM14. Import MM14.MallocKit_A2. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM08. Import MM08. Import MM08.MallocKit_A3. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM13. Import MM13. Import MM13.MallocKit_B. Import MM14.MallocKit_B3. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM12. Import MM12. Import MM12.MallocModel_B.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01. Import SM01.Monad.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import Malloc_fp. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocNat. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocFacts_AS. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import ASlot_W0. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import ASlot_W1. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import ASlot_I.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU0 Require Import RMallocRep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU0 Require Import RMallocTree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU0 Require Import RMallocKit_B. Import PM22. Import PM22.RMallocKit_B2. Import PM02. Import PM02.RMallocKit_B3. Import PM22.RMallocKit_A. Import PM03. Import PM03.RMallocKit_A2. Import PM22.RMalloc_fp. Import PM02.RAllocSlot_iface. Import PM02.RASlot_I. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU0 Require Import RASlot_W2.
Import PM01. Import PM01.RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1.
Context {RCa1 : RunCtx}. Context {rc : runConstT}.
Lemma ras_ret0 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc (m : word -> option byte) (junk : list byte) (st' : mstate) (lo : Z),
  rmrep st' m -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (bv_unsigned sp + -144) (rta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp + -144) -> ATOP <= lo -> lo <= bv_unsigned sp - 144 ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (fun ms' => exists (a1' a2' : word),
      ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v a0 a1' a2' a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3 t4 t5 t6)
              F (ret_pc rav) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
      /\ stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x176ac) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until lo. intros MR' MI FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof MR' as (_ & _ & (_ & _ & _ & _ & GUARD) & _).
  unfold RSSP_GUARD, rta_frame in *. atop_facts.
  step. step. step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
  step. step. step. step. step. step. step. step. step. step. step. step. step.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. do 2 eexists. split; [reflexivity| exact ST].
Qed.
End CANSEC1.
End RASlot_W19.

Module RF_am_A.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU0 Require Import PImg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.F_malloc_free. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM12. Import MM12. Import MM12.MallocModel_B. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM06. Import MM06. Import MM06.F_ntf_A. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM07. Import MM07. Import MM07.F_ntf_B. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM13. Import MM13. Import MM13.MallocKit_B. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM14. Import MM14. Import MM14.MallocKit_B3. Import MM07.F_am_A.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU0 Require Import RMallocRep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU0 Require Import RMallocTree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU0 Require Import RMallocKit_B. Import PM02. Import PM02.RMallocKit_B3. Import PM20. Import PM20.RF_ntf_A.
Import PM01. Import PM01.RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Section CANSEC1.
Context {RCa1 : RunCtx}. Context {rc : runConstT}.
Definition ram_fp (st : mstate) (lo sp : Z) (a : Z) : Prop :=
  lo <= a < sp
  \/ RCTX <= a < RCTX + 928
  \/ exists rid r, (s_regions st) !! rid = Some r /\ r_kind r <> RKGroup /\ lr_lo r <= a < r_base r + round_up_pg (r_len r).

Lemma ram_fp_alloc_fp st lo sp a : ram_fp st lo sp a -> ralloc_fp (fun k => k <> RKGroup) st lo sp a.
Proof. unfold ram_fp, ralloc_fp. tauto. Qed.
Lemma ram_fp_stack st lo sp a : lo <= a < sp -> ram_fp st lo sp a.
Proof. intros; left; assumption. Qed.
Lemma ram_fp_ctx st lo sp a : RCTX <= a < RCTX + 928 -> ram_fp st lo sp a.
Proof. intros; right; left; assumption. Qed.
Lemma ram_fp_region st lo sp a rid r : (s_regions st) !! rid = Some r -> r_kind r <> RKGroup ->
  lr_lo r <= a < r_base r + round_up_pg (r_len r) -> ram_fp st lo sp a.
Proof. intros; right; right. exists rid, r. auto. Qed.
Lemma ram_fp_not_errno st lo sp a : ram_fp st lo sp a -> rregions_wf st -> ATOP <= lo ->
  ~ (errno_addr (Z_to_bv 64 0x2fd80) <= a < errno_addr (Z_to_bv 64 0x2fd80) + 4).
Proof.
  intros [H|[H|(rid & r & Hr & _ & H)]] (_ & WR & _) LO; unfold RCTX in *; rewrite ?unsigned_lit by lia; try lia.
  destruct (WR _ _ Hr) as (_ & _ & _ & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (_ & _ & D23 & D2).
  pose proof (lr_lo_ge r). atop_facts. lia.
Qed.
Lemma ram_fp_meta : forall st m lo sp q a, rmrep st m -> meta_slot st q ->
  conc st q <= a < conc st q + 40 -> ram_fp st lo sp a.
Proof.
  intros st m lo sp q a MR (ar & arr & k & Har & Hk & Eq) Ha. pose proof MR as (WF & _).
  destruct (rarea_conc st ar arr WF Har) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
  assert (HG : conc st q = conc st ar + (AREA_HDR + META_SIZE * k)) by (rewrite Eq, conc_aadd by (rewrite Hra; eauto); reflexivity).
  pose proof (rarea_lr_lo st ar arr ra WF Har Hra).
  unfold AREA_HDR, META_SIZE, NSLOTS in *.
  eapply ram_fp_region; [exact Hra | exact NK | lia].
Qed.
Lemma ram_fp_area : forall st m lo sp ak ar a, rmrep st m -> (s_areas st) !! ak = Some ar ->
  conc st ak <= a < conc st ak + 4096 -> ram_fp st lo sp a.
Proof.
  intros st m lo sp ak ar a MR Har Ha. pose proof MR as (WF & _).
  destruct (rarea_conc st ak ar WF Har) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
  pose proof (rarea_lr_lo st ak ar ra WF Har Hra).
  eapply ram_fp_region; [exact Hra | exact NK | lia].
Qed.
Lemma ram_fp_same st st' lo sp a : s_regions st' = s_regions st -> ram_fp st' lo sp a <-> ram_fp st lo sp a.
Proof. intros ER. unfold ram_fp. rewrite ER. tauto. Qed.

Definition ram_ret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (stF : mstate) (m : word -> option byte) (st' : mstate) (rv : word) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 rv a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
    /\ rpres_except (ram_fp stF lo (bv_unsigned sp)) m m' /\ wmono (run_segments psegs rc_inp rc_sp rc_mb) m m' /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m'
    /\ stk (run_segments psegs rc_inp rc_sp rc_mb) m' lo (bv_unsigned sp)
    /\ rmrep st' m'.

Definition ram_frame (junk : list byte) (s4 s3 s2 s1 s0 ra : word) : list cell :=
  [CB 8 junk; C8 CAN; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma ram_tail : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
    (m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (q : aptr),
  rmrep st m -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m -> meta_slot st q ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp + -64) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m (upd_meta q clr_links st) (Z_to_bv 64 (conc st q)))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st q)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16a78) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until q. intros MR MI MSq FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st _ q MR MSq) as (GB0 & GB1 & GB2 & GB4 & _).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (conc st q, conc st q + 40)]%Z m) as MU.
  pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) m) as WM.
  pose proof MR as (_ & _ & (_ & _ & _ & _ & GUARD) & _).
  rmeta_chunk MR MSq CH.
  unfold RSSP_GUARD, ram_frame in *. atop_facts.
  rmeta_open (conc st q) MUq WMq.
  st1. st1.
  rmeta_close MR MSq MUq WMq CH (put_meta q (clr_links (get_meta_rec st q)) st) MR2.
  rewrite <- upd_meta_put in MR2.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z mX) as MUs; pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) mX) as WMs end.
  st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
  st1. st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR3 : rmrep (upd_meta q clr_links st) mX)
      by (eapply rmrep_transport_high; [exact MR2 | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; atop_facts; lia]) end.
  clear MUs WMs.
  release_frame FR ST (bv_unsigned sp).
  apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
  2:{ cbn [ivs_covered]. split; [|split; [|exact I]].
      - intros x Hx. apply ram_fp_stack. lia.
      - intros x Hx. eapply ram_fp_meta; [exact MR | exact MSq | lia]. }
  apply evt_done. unfold ram_ret_post. do 15 eexists.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. exact MR3.
Qed.
Lemma ram_b0 : forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
    (m : word -> option byte) (junk : list byte) (lo cnt : Z) (st : mstate) (q : aptr),
  rmrep st m -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m -> meta_slot st q -> 0 <= cnt < 2^64 ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp + -64) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m (am_took st q cnt) (Z_to_bv 64 (conc st q)))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st q)) (Z_to_bv 64 cnt) a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16a6c) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until q. intros MR MI MSq HC FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st _ q MR MSq) as (GB0 & GB1 & GB2 & GB4 & _).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 928)]%Z m) as MU.
  pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) m) as WM.
  pose proof MR as (WF & (C1 & _) & _). unfold rctx_head_cells, rsecw in C1.
  unfold RCTX, RMLOCK in *. atop_facts.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(RCTX + 24, RCTX + 40)]%Z mX) as MUc; pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) mX) as WMc end.
  unfold RCTX in MUc.
  st1. st1. st1.
  set (st1 := upd_ctx (fun c => set_avail_meta (Some (aadd q META_SIZE)) (set_avail_meta_count cnt c)) st).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR1 : rmrep st1 mX) end.
  { eapply (rmrep_ctx_frameW st st1 _ _ _ MR MUc WMc); try reflexivity.
    - intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
    - left. unfold rctx_head_cells, rsecw, RCTX. cbn [ctx st1 upd_ctx s_ctx set_avail_meta set_avail_meta_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
            c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
      unfold pw at 2. cbn [oconc]. change (conc st1 (aadd q META_SIZE)) with (conc st (aadd q META_SIZE)).
      rewrite (conc_aadd st q META_SIZE) by (destruct MSq as (a & ar & k & Ha & Hk & ->); cbn; pose proof MR as (WF' & _);
          destruct (rarea_conc st a ar WF' Ha) as (ra & Hra & _); rewrite Hra; eauto).
      unfold META_SIZE, wz. exact C1.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia. }
  clear MUc WMc C1.
  change (conc st q) with (conc st1 q).
  eapply evt_mono.
  { eapply (ram_tail sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc _ junk lo st1 q);
      [exact MR1 | assumption | exact MSq | exact FR | exact ST | atop_facts; lia | lia]. }
  intros ms' RP. unfold ram_ret_post in RP |- *.
  destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m' & -> & PE' & WM' & MI' & ST' & MR').
  do 15 eexists. split; [reflexivity|].
  split.
  { apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
    - eapply rpres_except_trans; [exact MU|]. eapply rpres_except_mono; [exact PE'|]. intros a Ha. apply (proj1 (ram_fp_same st st1 lo _ a eq_refl)). exact Ha.
    - cbn [ivs_covered]. split; [|split; [|exact I]].
      + intros x Hx. apply ram_fp_stack. lia.
      + intros x Hx. apply ram_fp_ctx. unfold RCTX. lia. }
  split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
Qed.
End CANSEC1.
End RF_am_A.

Module RF_am_C.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU0 Require Import PImg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.F_malloc_free. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM12. Import MM12. Import MM12.MallocModel_B. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM06. Import MM06. Import MM06.F_ntf_A. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM07. Import MM07. Import MM07.F_ntf_B. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM13. Import MM13. Import MM13.MallocKit_B. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM14. Import MM14. Import MM14.MallocKit_B3. Import MM07.F_am_A. Import MM07.F_am_K. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM10. Import MM10. Import MM10.F_am_C.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU0 Require Import RMallocRep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU0 Require Import RMallocTree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU0 Require Import RMallocKit_B. Import PM02. Import PM02.RMallocKit_B3. Import PM20. Import PM20.RF_ntf_A. Import RF_am_A. Import PM17. Import PM17.RF_am_K.
Import PM01. Import PM01.RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib.Step.simpl_sizes ::=
  rewrite ?app_length;
  try change (Z.of_nat (cells_size [CB 4072 (zeros 4072)])) with 4072;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?app_length; cbn [length].

Section CANSEC1.
Context {RCa1 : RunCtx}. Context {rc : runConstT}.
Lemma ram_carve2 : forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
    (m0 m : word -> option byte) (junk : list byte) (lo : Z) (st0 st : mstate) (p : aptr) (r : region),
  rmrep st m -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m -> s_regions st = s_regions st0 ->
  (s_regions st) !! (fst p) = Some r -> r_kind r <> RKGroup -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
  pgal (snd p) -> lr_lo r <= r_base r + snd p ->
  (s_areas st) !! p = None -> (forall k, 0 <= k < NSLOTS -> (s_metas st) !! (aadd p (AREA_HDR + META_SIZE * k)) = None) ->
  0 <= c_secret (ctx st) < 2^64 -> c_init_done (ctx st) = 1 ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (conc st p) [C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0)] ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (conc st p + 24) [CB 4072 (zeros 4072)] ->
  rpres_except (ram_fp st0 lo (bv_unsigned sp)) m0 m -> wmono (run_segments psegs rc_inp rc_sp rc_mb) m0 m ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp + -64) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  let stC := upd_ctx (set_meta_area_tail (Some p)) st in
  let stD := set_areas (<[p := mkArea (c_secret (ctx st)) None NSLOTS]> (s_areas stC)) stC in
  evt (run_segments psegs rc_inp rc_sp rc_mb) (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st0 m0
               (am_took stD (aadd p AREA_HDR) 100) (Z_to_bv 64 (conc st p + 24)))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 (Z_to_bv 64 (conc st p)) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16a48) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until r. intros MR MI ER0 Hr NK S0 S1 SAL SLR ANone FRESH SEC HID HDR0 REST PE0 WM0 FR ST LO LOLE stC stD.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof MR as (WF & (C1 & _) & _). pose proof WF as (Hres & WR & DJ & WA & WG).
  pose proof (conc_region' st p r Hr) as Cp.
  destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (DR1 & _ & DR23 & DR2). atop_facts.
  pose proof (lr_lo_ge r) as LRG. pose proof (round_up_pg_ge (r_len r)) as RU.
  unfold rctx_head_cells, rsecw in C1.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. atop_facts.
  assert (PD : conc st p + 4096 <= 0x1e000 \/ 0x51000 <= conc st p) by lia.
  assert (PB : 0 <= conc st p /\ conc st p + 4096 <= lo) by lia.
  clear RBAL RL0 RB0 RF DR1 DR23 DR2 LRG RU Hres DJ WA WG.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 928); (conc st p, conc st p + 4096)]%Z m) as MU.
  pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) m) as WM. unfold RCTX in MU.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(RCTX + 64, RCTX + 72)]%Z mX) as MUc; pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) mX) as WMc end.
  unfold RCTX in MUc.
  st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRC : rmrep stC mX) end.
  { eapply (rmrep_ctx_frameW st stC _ _ _ MR MUc WMc); try reflexivity.
    - intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - left. unfold rctx_head_cells, rsecw, RCTX. cbn [ctx stC upd_ctx s_ctx set_meta_area_tail c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
            c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
      unfold pw at 4. cbn [oconc]. change (conc stC p) with (conc st p). exact C1.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia. }
  clear MUc WMc.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(conc st p, conc st p + 4096)]%Z mX) as MUp; pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) mX) as WMp end.
  st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRC3 : rmrep stC mX) end.
  { eapply rmrep_transport_unowned; [exact MRC | exact MUp | exact WMp |].
    intros lo' hi' a [E|[]] Ha. inversion E; subst lo' hi'. eapply (rfresh_page_avoids stC _ p r a MRC); try assumption. }
  clear MUp WMp MRC.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRD : rmrep stD mX) end.
  { unfold stD. eapply (rmrep_new_area stC _ p r (c_secret (ctx st))); try first [exact MRC3 | exact Hr | exact NK | exact S0 | exact S1 | exact SLR | exact ANone | exact FRESH | idtac].
    - exact SAL.
    - change (conc stC p) with (conc st p). rewrite HID, Z.mul_1_r in HDR0. exact HDR0.
    - intros k Hk. change (conc stC p) with (conc st p). rewrite meta_cells_meta0.
      destruct REST as [[_ B] W]. change (cells_size [CB 4072 (zeros 4072)]) with 4072%nat in W. cbn [cells_bytes cbytes cells_size csize Nat.add] in B, W. rewrite app_nil_r in B.
      replace (conc st p + AREA_HDR + META_SIZE * k) with ((conc st p + 24) + 40 * k) by (unfold AREA_HDR, META_SIZE; lia).
      eapply (rrw_cells_of_zeros _ (conc st p + 24) 4072 (40 * k)); [exact B| exact W| cbn; ftauto| reflexivity| lia| cbn [cells_size csize Nat.add]; unfold NSLOTS in Hk; lia].
    - change (conc stC p) with (conc st p).
      destruct REST as [[_ B] W]. change (cells_size [CB 4072 (zeros 4072)]) with 4072%nat in W. cbn [cells_bytes cbytes cells_size csize Nat.add] in B, W. rewrite app_nil_r in B.
      replace (conc st p + 4064) with ((conc st p + 24) + 4040) by lia.
      eapply (rrw_cells_of_zeros _ (conc st p + 24) 4072 4040); [exact B| exact W| cbn; split; [reflexivity| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity| lia| cbn [cells_size csize Nat.add]; lia]. }
  clear MRC3 HDR0 REST.
  assert (MSq : meta_slot stD (aadd p AREA_HDR)).
  { exists p, (mkArea (c_secret (ctx st)) None NSLOTS), 0. split; [| split; [unfold NSLOTS; lia| unfold AREA_HDR, META_SIZE; rewrite Z.mul_0_r, Z.add_0_r; reflexivity]].
    unfold stD. cbn [s_areas set_areas]. rewrite lookup_insert_eq. reflexivity. }
  assert (CQ : conc st p + 24 = conc stD (aadd p AREA_HDR)).
  { change (conc stD (aadd p AREA_HDR)) with (conc st (aadd p AREA_HDR)). rewrite (conc_aadd st p AREA_HDR) by (rewrite Hr; eauto). reflexivity. }
  rewrite CQ. change (Z_to_bv 64 327664) with (Z_to_bv 64 RSSP_GUARD). change (Z_to_bv 64 327808) with (Z_to_bv 64 RMLOCK).
  eapply evt_mono.
  { eapply (ram_b0 sp gp tp _ _ _ s0 _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc _ junk lo 100 stD (aadd p AREA_HDR));
      [exact MRD | assumption | exact MSq | lia | | | atop_facts; lia | lia].
    - lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
    - lazymatch goal with H : stk (run_segments psegs rc_inp rc_sp rc_mb) ?mX lo _ |- _ => exact H end. }
  intros ms' RP. unfold ram_ret_post in RP |- *.
  destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m' & -> & PE' & WM' & MI' & ST' & MR').
  do 15 eexists. split; [reflexivity|].
  split.
  { eapply rpres_except_trans; [exact PE0|].
    apply (rpres_except_of_munch_cov (ram_fp st0 lo (bv_unsigned sp))) in MU; [|exact WM|].
    - eapply rpres_except_trans; [exact MU|]. eapply rpres_except_mono; [exact PE'|]. intros a Ha.
      apply (proj1 (ram_fp_same st0 stD lo _ a ltac:(rewrite <- ER0; reflexivity))). exact Ha.
    - cbn [ivs_covered]. split; [|split; [|split; [|exact I]]].
      + intros x Hx. apply ram_fp_stack. lia.
      + intros x Hx. apply ram_fp_ctx. unfold RCTX. lia.
      + intros x Hx. eapply (ram_fp_region st0 lo _ x (fst p) r); [rewrite <- ER0; exact Hr| exact NK|].
        pose proof (lr_lo_ge r). lia. }
  split; [eapply wmono_trans; [exact WM0| exact WM']|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
Qed.

Lemma ram_carve_walk : forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
    (m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (p : aptr) (r : region),
  rmrep st m -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m ->
  (s_regions st) !! (fst p) = Some r -> r_kind r <> RKGroup -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
  pgal (snd p) -> lr_lo r <= r_base r + snd p ->
  (s_areas st) !! p = None -> (forall k, 0 <= k < NSLOTS -> (s_metas st) !! (aadd p (AREA_HDR + META_SIZE * k)) = None) ->
  (forall tl, c_meta_area_tail (ctx st) = Some tl -> is_Some ((s_areas st) !! tl)) ->
  1 <= c_avail_meta_area_count (ctx st) < 2^64 -> 0 <= c_secret (ctx st) < 2^64 -> c_init_done (ctx st) = 1 ->
  bytes_at (run_segments psegs rc_inp rc_sp rc_mb) m (conc st p) (zeros 4096) -> wr_at (run_segments psegs rc_inp rc_sp rc_mb) m (conc st p) 4096 ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp + -64) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo (carve_st st p) m
               (am_took (carve_st st p) (aadd p AREA_HDR) 100) (Z_to_bv 64 (conc st p + 24)))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 (Z_to_bv 64 (conc st p)) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16a1c) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until r. intros MR MI Hr NK S0 S1 SAL SLR ANone FRESH TL CNT SEC HID ZB ZW FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof MR as (WF & (C1 & _) & _ & AR & _). pose proof WF as (Hres & WR & DJ & WA & WG).
  pose proof (conc_region' st p r Hr) as Cp.
  destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (DR1 & _ & DR23 & DR2). atop_facts.
  pose proof (lr_lo_ge r) as LRG. pose proof (round_up_pg_ge (r_len r)) as RU.
  unfold rctx_head_cells, rsecw in C1.
  assert (HDR0 : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (conc st p) [C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0)]).
  { rewrite <- (Z.add_0_r (conc st p)). eapply (rrw_cells_of_zeros m (conc st p) 4096 0); [exact ZB| exact ZW| cbn; ftauto| reflexivity| lia| cbn; lia]. }
  assert (REST : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (conc st p + 24) [CB 4072 (zeros 4072)]).
  { eapply (rrw_cells_of_zeros m (conc st p) 4096 24); [exact ZB| exact ZW| cbn [cells_wf]; split; [first [reflexivity | apply zeros_length]| exact I] | change (cells_size [CB 4072 (zeros 4072)]) with 4072%nat; cbn [cells_bytes cbytes cells_size csize Nat.add]; rewrite app_nil_r; reflexivity| lia| change (cells_size [CB 4072 (zeros 4072)]) with 4072%nat; cbn; lia]. }
  clear ZB ZW.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. atop_facts.
  assert (PD : conc st p + 4096 <= 0x1e000 \/ 0x51000 <= conc st p) by lia.
  assert (PB : 0 <= conc st p /\ conc st p + 4096 <= lo) by lia.
  clear RBAL RL0 RF DR1 DR23 DR2 RU.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 928); (conc st p, conc st p + 4096)]%Z m) as MU0.
  pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) m) as WM0. unfold RCTX in MU0.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(RCTX + 40, RCTX + 48); (RCTX + 72, RCTX + 80)]%Z mX) as MUc; pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) mX) as WMc end.
  unfold RCTX in MUc.
  st1. st1. st1. st1. st1. st1. st1.
  set (st1 := upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) st).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR1 : rmrep st1 mX) end.
  { eapply (rmrep_ctx_frameW st st1 _ _ _ MR MUc WMc); try reflexivity.
    - intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - left. unfold rctx_head_cells, rsecw, RCTX. cbn [ctx st1 upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
            c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
      unfold pw at 5. cbn [oconc]. change (conc st1 (aadd p 4096)) with (conc st (aadd p 4096)).
      rewrite (conc_aadd st p 4096) by (rewrite Hr; eauto). unfold wz at 6 7.
      lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) ?mX 327816 _ |- _ => exact H end.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia. }
  clear MUc WMc.
  st1.
  destruct (c_meta_area_tail (ctx st)) as [tl|] eqn:HT.
  -
    destruct (TL tl eq_refl) as [ar Har].
    destruct (rarea_conc st tl ar WF Har) as (rt & Hrt & Ct & St0 & St1 & StL & NKt & RBt & RBAt & RBCt). atop_facts.
    pose proof (rarea_lr_lo st tl ar rt WF Har Hrt) as LRt.
    destruct (WR _ _ Hrt) as (_ & _ & _ & _ & RFt). destruct (rreserved_disjoint _ _ RFt) as (DT1 & _ & DT23 & DT2).
    assert (TD : conc st tl + 4096 <= 0x1e000 \/ 0x51000 <= conc st tl) by lia.
    assert (TB : 0 < conc st tl /\ conc st tl + 4096 <= lo) by lia.
    assert (TP : conc st tl + 4096 <= conc st p \/ conc st p + 4096 <= conc st tl).
    { destruct (N.eq_dec (fst tl) (fst p)) as [E|NE].
      - rewrite E, Hr in Hrt. assert (rt = r) by congruence. subst rt.
        assert (NEo : snd tl <> snd p) by (intros E2; assert (tl = p) by (clear - E E2; destruct tl, p; cbn in *; congruence); subst tl; rewrite ANone in Har; discriminate).
        unfold pgal in SAL. clear - Ct Cp NEo SAL StL E. Z.div_mod_to_equations. lia.
      - destruct (DJ _ _ _ _ Hrt Hr NE); lia. }
    clear RBAt StL RFt DT1 DT23 DT2 St0 St1 LRt RBt RBCt DJ WA WG.
    unfold pw. cbn [oconc]. unfold wz.
    assert (CF : bv_eqb (Z_to_bv 64 (conc st tl)) (Z_to_bv 64 0) = false) by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
    rewrite CF. clear CF.
    pose proof MR1 as (_ & _ & _ & AR1 & _). destruct (AR1 tl ar Har) as (ARh & _ & _). clear AR1.
    change (conc st1 tl) with (conc st tl) in ARh.
    apply (munch_grow2 _ (conc st tl, conc st tl + 4096)) in MU0.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (munch_refl [(conc st tl + 8, conc st tl + 16)]%Z mX) as MUa; pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) mX) as WMa end.
    st1. st1.
    set (st2 := set_areas (<[tl := mkArea (a_check ar) (Some p) (a_nslots ar)]> (s_areas st1)) st1).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR2 : rmrep st2 mX) end.
    { eapply (rmrep_set_area_next st1 _ _ tl ar p MR1 Har); [cbn; rewrite Hr; eauto| exact MUa| exact WMa|].
      change (conc st1 tl) with (conc st tl). change (conc st1 p) with (conc st p). unfold wz at 2. exact ARh. }
    clear MUa WMa ARh MR1.
    rewrite (carve_st_some st p tl ar HT Har ANone). cbv zeta. fold st1. fold st2.
    change (Z_to_bv 64 327664) with (Z_to_bv 64 RSSP_GUARD). change (Z_to_bv 64 327808) with (Z_to_bv 64 RMLOCK).
    eapply evt_mono.
    { eapply (ram_carve2 sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc m _ junk lo st st2 p r);
        first [exact MR2 | reflexivity | exact Hr | exact NK | exact S0 | exact S1 | exact SAL | exact SLR | exact FRESH | exact SEC | exact HID | exact WM0 | idtac].
      - lazymatch goal with H : mem_inv (run_segments psegs rc_inp rc_sp rc_mb) ?mX |- _ => exact H end.
      - cbn [s_areas set_areas upd_ctx st2 st1]. rewrite lookup_insert_ne; [exact ANone|]. intros ->. rewrite ANone in Har; discriminate.
      - lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) ?mX (conc st p) _ |- _ => exact H end.
      - lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) ?mX (conc st p + 24) _ |- _ => exact H end.
      - apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU0; [exact MU0|exact WM0|].
        cbn [ivs_covered]. split; [|split; [|split; [|split; [|exact I]]]].
        + intros x Hx. apply ram_fp_stack. lia.
        + intros x Hx. eapply ram_fp_area; [exact MR| exact Har| lia].
        + intros x Hx. apply ram_fp_ctx. unfold RCTX. lia.
        + intros x Hx. eapply (ram_fp_region st lo _ x (fst p) r); [exact Hr| exact NK| lia].
      - lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
      - lazymatch goal with H : stk (run_segments psegs rc_inp rc_sp rc_mb) ?mX lo _ |- _ => exact H end.
      - atop_facts; lia.
      - lia. }
    intros ms' RP. exact RP.
  -
    unfold pw. cbn [oconc]. unfold wz.
    change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true. cbv iota.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (munch_refl [(RCTX + 56, RCTX + 64)]%Z mX) as MUc; pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) mX) as WMc end.
    unfold RCTX in MUc.
    st1.
    set (st2 := upd_ctx (set_meta_area_head (Some p)) st1).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR2 : rmrep st2 mX) end.
    { eapply (rmrep_ctx_frameW st1 st2 _ _ _ MR1 MUc WMc); try reflexivity.
      - intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - left. unfold rctx_head_cells, rsecw, RCTX. cbn [ctx st2 st1 upd_ctx s_ctx set_meta_area_head set_avail_meta_areas set_avail_meta_area_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
              c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
        rewrite HT. unfold pw. cbn [oconc]. change (conc st2 ?q) with (conc st q). change (conc st2 p) with (conc st p).
        rewrite (conc_aadd st p 4096) by (rewrite Hr; eauto). unfold wz.
        lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) ?mX 327816 _ |- _ => exact H end.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia. }
    clear MUc WMc MR1.
    rewrite (carve_st_none st p HT ANone). cbv zeta. fold st1. fold st2.
    change (Z_to_bv 64 327664) with (Z_to_bv 64 RSSP_GUARD). change (Z_to_bv 64 327808) with (Z_to_bv 64 RMLOCK).
    eapply evt_mono.
    { eapply (ram_carve2 sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc m _ junk lo st st2 p r);
        first [exact MR2 | reflexivity | exact Hr | exact NK | exact S0 | exact S1 | exact SAL | exact SLR | exact ANone | exact FRESH | exact SEC | exact HID | exact WM0 | idtac].
      - lazymatch goal with H : mem_inv (run_segments psegs rc_inp rc_sp rc_mb) ?mX |- _ => exact H end.
      - lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) ?mX (conc st p) _ |- _ => exact H end.
      - lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) ?mX (conc st p + 24) _ |- _ => exact H end.
      - apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU0; [exact MU0|exact WM0|].
        cbn [ivs_covered]. split; [|split; [|split; [|exact I]]].
        + intros x Hx. apply ram_fp_stack. lia.
        + intros x Hx. apply ram_fp_ctx. unfold RCTX. lia.
        + intros x Hx. eapply (ram_fp_region st lo _ x (fst p) r); [exact Hr| exact NK| lia].
      - lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
      - lazymatch goal with H : stk (run_segments psegs rc_inp rc_sp rc_mb) ?mX lo _ |- _ => exact H end.
      - atop_facts; lia.
      - lia. }
    intros ms' RP. exact RP.
Qed.
End CANSEC1.
End RF_am_C.

Module RF_malloc_core.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Decode. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU0 Require Import PImg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM11. Import MM11. Import MM11.F_malloc_enframe. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocFacts_A. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocKit_A. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM13. Import MM13. Import MM13.MallocBlocks.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01. Import SM01.Monad.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import Malloc_fp. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM08. Import MM08. Import MM08.F_malloc_enf. Import MM08.F_malloc_join. Import MM08.F_malloc_small. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import F_malloc_entry.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU0 Require Import RMallocRep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU0 Require Import RMallocTree. Import PM21. Import PM21.RF_get_meta. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU0 Require Import RMallocKit_B. Import PM22. Import PM22.RMallocKit_B2. Import PM22.RMallocKit_A. Import PM22.RMalloc_fp. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU0 Require Import RF_malloc_enf. Import PM02. Import PM02.RAllocSlot_iface. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU0 Require Import RF_malloc_entry. Import PM03. Import PM03.RF_malloc_join. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU0 Require Import RF_malloc_small.
Import PM01. Import PM01.RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Notation RAREACH := (AREACH_from ref_reserved).

Section CANSEC1.
Context {RCa1 : RunCtx}. Context {rc : runConstT}.
Definition rcoreQ (o m0 : mem) (st : mstate) (s : PState)
    (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z)
    (res : mstate * option (aptr * Z)) (s' : PState) (ms' : machine_state) : Prop :=
  match res with
  | (st2, Some (g, idx)) =>
    exists (b : aptr) (r : region) (m1 : mem) (errv : word) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
                   a0 a1 a2 a3 a4 a5 a6 a7 (pw st2 (Some g)) (wz idx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x16e00) fc None m1 (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
      /\ rmrep st2 m1 /\ ticks_ok st2 /\ unk_agree st2 o m1 /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m1
      /\ stk (run_segments psegs rc_inp rc_sp rc_mb) m1 lo (bv_unsigned sp + -48)
      /\ rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra]
      /\ rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m1 (errno_addr tp) [C4 errv] /\ rauxv_ok m1 (bv_unsigned sp)
      /\ rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1
      /\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx - 4 <= a
                   < r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) - 4 ->
            rmalloc_fp st st2 lo (bv_unsigned sp) a)
      /\ 0 <= c_mmap_counter (ctx st2) < 2^32
      /\ slot_ok st2 g b r idx n
      /\ (expo_cond st n -> rdv pans_mem o st2 (fst b, snd b + (16 + get_stride (get_meta_rec st2 g) * idx) + -3) = 0)
      /\ mrel st st2 /\ brk_link_ps st2 s' /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
  | (st2, None) =>
    exists (m1 : mem) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m1 (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
      /\ rmrep st2 m1 /\ ticks_ok st2 /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m1 /\ stk (run_segments psegs rc_inp rc_sp rc_mb) m1 lo (bv_unsigned sp)
      /\ rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m1 (errno_addr tp) [C4 errv] /\ rauxv_ok m1 (bv_unsigned sp)
      /\ rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1
      /\ mrel st st2 /\ brk_link_ps st2 s' /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
  end.

Lemma renf_hyp_ret o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo :
  renf_hyp (fun st1 r => ret (st1, r)) o m0 st s (rcoreQ o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo)
           ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo.
Proof.
  intros st2 g b r idx m1 s' errv t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra'; intros.
  apply rimplT_ret. apply evt_done. cbn [rcoreQ].
  exists b, r, m1, errv. do 17 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.

Lemma rfail_hyp_ret o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo :
  rfail_hyp (fun st1 r => ret (st1, r)) o m0 st s (rcoreQ o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo)
            ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc lo.
Proof.
  intros st2 m1 s' errv t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6; intros.
  apply rimplT_ret. apply evt_done. cbn [rcoreQ].
  exists m1, errv. do 14 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.

Definition rbig_stmt : Prop :=
  forall (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
         (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N)
         (m1 : mem) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4r t3 t4 t5 t6 ra' : word),
  let st1 := set_tick t st in
  RAREACH st LB -> RMFACTS st LB -> rmrep st m0 -> tp = Z_to_bv 64 RATP ->
  ATOP <= lo -> lo <= bv_unsigned sp - 48 - RAM_STACK -> MMAP_THRESHOLD <= n < 2^32 -> brk_link_ps st s ->
  rmrep st1 m1 -> ticks_ok st1 -> unk_agree st1 o m1 -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m1 ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) m1 lo (bv_unsigned sp + -48) ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
  rpres_except (rmalloc_fp st st1 lo (bv_unsigned sp)) m0 m1 ->
  rimplT o (malloc_core full_lay st1 n) s (rcoreQ o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 131052) a1 a2 a3 a4 a5 a6 a7
                 s2r s3r s4r s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16b50) fc None m1 (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).

Section CORE.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis AS_PRE : forall st LB t sc n, RAREACH st LB -> RMFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
  n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.
Hypothesis RBIG : rbig_stmt.

Lemma rmalloc_core_implT :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (st : mstate) (LB : list block) (s : PState) (n lo : Z) (errv : word) (t : N),
  RAREACH st LB -> RMFACTS st LB -> rmrep st m -> brk_link_ps st s ->
  rauxv_ok m (bv_unsigned sp) ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 8192 ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (errno_addr tp) [C4 errv] -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 n -> 0 <= n < 2^32 -> (s_tick st < t)%N ->
  rimplT m (malloc_core full_lay (set_tick t st) n) s
        (rcoreQ m m st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until t. intros AR MF MR BL AUX ST CLO LO ERR MI TP HA N TT.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (RAS_STACK_ge 0) as ASG.
  assert (RB0 : forall rid r1, (s_regions st) !! rid = Some r1 -> 0 <= r_base r1 /\ r_base r1 + round_up_pg (r_len r1) <= ATOP).
  { intros rid r1 H1. pose proof (rregion_facts st m rid r1 MR H1) as (X1 & _ & X2 & _). atop_facts. lia. }
  pose proof MR as (WF0 & CX0 & GL0 & _). destruct GL0 as (_ & NL & _).
  assert (PREP : forall m1, munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 -> wmono (run_segments psegs rc_inp rc_sp rc_mb) m m1 ->
            rmrep (set_tick t st) m1 /\ ticks_ok (set_tick t st) /\ unk_agree (set_tick t st) m m1
            /\ rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m1 (errno_addr tp) [C4 errv] /\ rauxv_ok m1 (bv_unsigned sp)
            /\ rpres_except (rmalloc_fp st (set_tick t st) lo (bv_unsigned sp)) m m1).
  { intros m1 MU WM. atop_facts.
    split. { apply rmrep_set_tick. eapply rmrep_transport_high; [exact MR| exact MU| exact WM| intros lo' hi' [E|[]]; inversion E; atop_facts; lia]. }
    split. { apply ticks_ok_set_tick; [lia|]. exact (mf_ticks _ _ MF). }
    split. { eapply unk_agree_munch; [| exact MU| |].
             - eapply unk_agree_ext; [apply unk_agree_refl| reflexivity| intros; reflexivity| reflexivity].
             - intros rid r1 H1 K1. pose proof (RB0 rid r1 H1). cbn. lia.
             - intros rid r1 H1. pose proof (RB0 rid r1 H1). lia. }
    split. { eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. subst tp. unfold RATP. rewrite unsigned_lit by lia. cbn. lia. }
    split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL. constructor; [cbn; lia| constructor]. }
    eapply rpres_except_of_munch; [exact MU| exact WM|]. intros a Ha NC. cbn. split; [|exact I]. intros HX. apply NC. left. left. lia. }
  destruct (Z.le_gt_cases MMAP_THRESHOLD n) as [TH|TH].
  -
    riprefixT. eapply evt_cut.
    { eapply (rentry_big_walk ra sp gp tp); [exact HA| unfold MMAP_THRESHOLD in *; lia| exact ST| atop_facts; lia| lia| exact MI]. }
    intros ms' (a1' & m1 & -> & FR & ST1 & MU & WM & MI1).
    destruct (PREP m1 MU WM) as (MR1 & TK1 & UA1 & ERR1 & AUX1 & PE1).
    apply evt_done.
    eapply (RBIG m m st LB s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo t); try eassumption.
    + unfold RAM_STACK. lia.
    + lia.
  -
    unfold malloc_core.
    replace (size_overflows n) with false by (symmetry; unfold size_overflows; apply Z.leb_gt; lia).
    replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; lia).
    riprefixT. eapply evt_cut.
    { eapply (rmalloc_entry_walk ra sp gp tp); [exact HA| unfold MMAP_THRESHOLD in *; lia| exact ST| atop_facts; lia| lia| exact MI| exact NL]. }
    intros ms' (a0' & a1' & a2' & a3' & m1 & -> & FR & ST1 & MU & WM & MI1).
    destruct (PREP m1 MU WM) as (MR1 & TK1 & UA1 & ERR1 & AUX1 & PE1).
    pose proof (size_to_class_props n ltac:(lia)) as (SCR & SFIT & _).
    apply evt_done.
    eapply (rmalloc_small_implT (fun st1 r => ret (st1, r)) (ret (set_tick t st, None)) m m st LB s _ ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo t as_pre as_inv RAS).
    all: try eassumption.
    + apply renf_hyp_ret.
    + apply rfail_hyp_ret.
    + unfold RAS_STACK. lia.
    + reflexivity.
    + intros sc' Hsc' Hfit'. eapply AS_PRE; [exact AR| exact MF| exact TT| exact Hsc'| lia| exact Hfit'].
Qed.
End CORE.
End CANSEC1.
End RF_malloc_core.
