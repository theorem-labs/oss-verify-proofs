From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Prog Require Import memcpy_c memset_c bcmp_c
  reac_ctrl_build_scene_step_c check_step_c reac_ctrl_scene_set_mac_c reac_ctrl_scene_build_c.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Prog Require memcpy memset bcmp reac_ctrl_build_scene_step check_step
  reac_ctrl_parse kind_of_link1 reac_ctrl_checksum_verify reac_ctrl_scene_set_mac reac_ctrl_scene_build
  reac_ctrl_block_cksum_stamp.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Prog.Seg Require Import SInv SCut SLink SEarly
  SSegE SSegB SSegT SSegC SSegM SSegD SSegF SSegG.
From OSSVerify.libreac.fuzz_scene Require Statements.
Import ListNotations.
Open Scope Z_scope.

(* The ubsan slot entry from the segment lemmas E, B, T, C, M, D, F, G, and ubsan_halts from it. *)

Section Entry.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis MALLOC : malloc_contract B (APIf rc).
Hypothesis FREE : free_contract B (APIf rc).
Hypothesis MEMC : memcpy_contract.
Hypothesis MEMS : memset_contract.
Hypothesis BCMP : bcmp_contract.
Hypothesis BUILD : reac_ctrl_build_scene_step_contract.
Hypothesis CHECK : check_step_contract.
Hypothesis SETMAC : reac_ctrl_scene_set_mac_contract.
Hypothesis SBUILD : reac_ctrl_scene_build_contract.

Theorem slot_entry : Hcut B APIf ra (Inv_ENTRY B APIf ra empty).
Proof.
  assert (HG : Hcut B APIf ra (Inv_K15458 B APIf ra empty)) by (eapply seg_G; eassumption).
  assert (HF : Hcut B APIf ra (Inv_K15450 B APIf ra empty)) by (eapply seg_F; eassumption).
  assert (HD : Hcut B APIf ra (Inv_K152a0 B APIf ra empty)) by (eapply seg_D; eassumption).
  assert (HM : Hcut B APIf ra (Inv_K15298 B APIf ra empty)) by (eapply seg_M; eassumption).
  assert (HC : Hcut B APIf ra (Inv_K15294 B APIf ra empty)) by (eapply seg_C; eassumption).
  assert (HT : Hcut B APIf ra (Inv_K151b4 B APIf ra empty)) by (eapply seg_T; eassumption).
  assert (HB : Hcut B APIf ra (Inv_K15010 B APIf ra empty)) by (eapply seg_B; eassumption).
  eapply seg_E; eassumption.
Qed.

End Entry.

Theorem ubsan_halts_holds : OSSVerify.libreac.fuzz_scene.Statements.ubsan_halts.
Proof.
  apply ubsan_halts_of_entry; [|exact scene_early_holds].
  intros fx rc B APIf LS SH SK ra empty FF HMAL HFREE.
  pose proof memcpy.memcpy_holds as MEMC. pose proof memset.memset_holds as MEMS. pose proof bcmp.bcmp_holds as BCMP.
  pose proof (reac_ctrl_build_scene_step.reac_ctrl_build_scene_step_holds MEMS MEMC
    reac_ctrl_block_cksum_stamp.reac_ctrl_block_cksum_stamp_holds) as BUILD.
  pose proof (check_step.check_step_holds BCMP MEMC
    (reac_ctrl_parse.reac_ctrl_parse_holds MEMS MEMC BCMP kind_of_link1.kind_of_link1_holds)
    reac_ctrl_checksum_verify.reac_ctrl_checksum_verify_holds) as CHECK.
  pose proof (reac_ctrl_scene_set_mac.reac_ctrl_scene_set_mac_holds MEMC) as SETMAC.
  pose proof (reac_ctrl_scene_build.reac_ctrl_scene_build_holds MEMS MEMC) as SBUILD.
  eapply slot_entry; eassumption.
Qed.
