(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib Require Import SFModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec Require Import SoftFloat FmtFp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require Import RProgNotJ. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require Import RProgNot. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require RegFold. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require RProgAt. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require JunkAbs.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition signbitl_prog (B : Z) : RStep.ptree :=
  PLeaf
    (PJ_ShiftImm_ALU_SRL_nnn 0 10 11 63 4
    (PJ_Jalr_nnn 4 0 1 0 4 nil)).

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
Definition PROGAT_CODE_signbitl (IMG : RImg) := signbitl_prog (sym 0x1b128).
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_signbitl : CodeAtT img_segs (sym 0x1b128) (PROGAT_CODE_signbitl IMG)}.
  Context {RB_signbitl : RelCode (sym 0x1b128) 8}.
  Collection ImgHyps := IMG CODE_signbitl RB_signbitl.



Definition signbitl_entry := (sym 0x1b128)%Z.

(* [comment removed for export] *)
Definition signbitl_post (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (r : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' =>
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom img_segs)
    /\ munch [] m m /\ wmono img_segs m m /\ mem_inv img_segs m.

Lemma signbitl_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv img_segs m ->
  evt img_segs (signbitl_post ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
               (signbitl (bv_unsigned a0 + 2^64 * bv_unsigned a1)) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1b128)) fc None m (seg_rom img_segs)).
Proof.
  intros until m. intros MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl img_segs m) as WM. pose_word_ranges.
  unfold signbitl. rewrite hi64_words by lia.
  zstep. zstep. sf_finish.
Qed.

(* [comment removed for export] *)
Definition signbitl_contract : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv img_segs m ->
  evt img_segs (signbitl_post ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
               (signbitl (bv_unsigned a0 + 2^64 * bv_unsigned a1)) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1b128)) fc None m (seg_rom img_segs)).
Lemma signbitl_contract_ok : signbitl_contract.
Proof. exact signbitl_spec. Qed.


End Img.

(* [comment removed for export] *)
Existing Class signbitl_contract.
