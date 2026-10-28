(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare RefMemcpyLib.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import MemsetLib.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.musl Require Pm6MemcpyBase_u5 Pm6Memcpy_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Pm6SumsMemset_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import AsanPlanSoundSums SumsSpecLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma src0_copy_spec_memcpy : forall fx : PropExec.FPState, @APSX.copy_spec fx RSEGS 0xbe048.
Proof.
  intros fx mem0 dst src n bs regs ret Hn Hlen Hrd Hst Hdisj Hnws Hnwd Hret R1 R10 R11 R12.
  pose proof (u64_range dst) as Hdr.
  assert (HOK : Pm6MemcpyBase_u5.mcH mem0 dst src n bs) by (constructor; try assumption; lia).
  destruct (Pm6Memcpy_u5.ref_memcpy mem0 dst src n bs (seg_rom RSEGS) HOK regs ret Hret R1 R10 R11 R12) as (regs' & Hms & Hk).
  exists regs'. split; [replace (Z_to_bv 64 0xbe048) with (0xbe048%bv : word) by (apply bv_eq; reflexivity); exact Hms|].
  split; [apply kept_ok_of_keeps; exact Hk|].
  rewrite <- R10. apply Hk. unfold callee_kept. in_list.
Qed.

Lemma src0_fill_spec_memset : forall fx : PropExec.FPState, @APSX.fill_spec fx RSEGS 0xbe5c8 AX2.two64.
Proof.
  intros fx. apply fill_spec_of_memset. intros mem0 d cv ret n rom Hn Hnw Hst Hret regs R10 R11 R12 R1.
  exact (Pm6SumsMemset_u5.memset_summary mem0 d cv ret n rom Hn Hnw Hst Hret regs R10 R11 R12 R1).
Qed.
