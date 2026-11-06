(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare RefMemcpyLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import MemsetLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Ja0MemcpyBase Ja0Memcpy Ja0SumsMemset.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanPlanSoundSums SumsSpecLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
#[local] Abbreviation RSEGS := Asan.M.loaded_segments.
Lemma as0_copy_spec_memcpy : forall fx : PropExec.FPState, @APSX.copy_spec fx RSEGS 0x1249ac.
Proof.
intros fx mem0 dst src n bs regs ret Hn Hlen Hrd Hst Hdisj Hnws Hnwd Hret R1 R10 R11 R12.
pose proof (u64_range dst) as Hdr.
assert (HOK : Ja0MemcpyBase.mcH mem0 dst src n bs) by (constructor; try assumption; lia).
destruct (Ja0Memcpy.ref_memcpy mem0 dst src n bs (seg_rom RSEGS) HOK regs ret Hret R1 R10 R11 R12) as (regs' & Hms & Hk).
exists regs'. split; [replace (Z_to_bv 64 0x1249ac) with (0x1249ac%bv : word) by (apply bv_eq; reflexivity); exact Hms|].
split; [apply kept_ok_of_keeps; exact Hk|].
rewrite <- R10. apply Hk. unfold callee_kept. in_list.
Qed.
Lemma as0_fill_spec_memset : forall fx : PropExec.FPState, @APSX.fill_spec fx RSEGS 0x124db0 AX2.two64.
Proof.
intros fx. apply fill_spec_of_memset. intros mem0 d cv ret n rom Hn Hnw Hst Hret regs R10 R11 R12 R1.
exact (Ja0SumsMemset.memset_summary mem0 d cv ret n rom Hn Hnw Hst Hret regs R10 R11 R12 R1).
Qed.
