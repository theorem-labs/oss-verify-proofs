(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/YZ03.v (agreement) and lib/Halts_tfib.v (halting) for fuzz_command's ASan+UBSan statements: the plain side is lib/A/AsanTop.v cmd_plain_rz at 2^34, brought to the statement's plain budget by shape_strong_equiv_efs_relim; the halting proof takes srealizes (halts_budgets_of_srealizes); names and module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/AsanUbsanTop.v (origin/ossv/recipes bf33659295b7) for reac-pw/fuzz_segconf's image B (fuzz_segconf.asan-ubsan) as lib/B/SegAsanUbsanTop.v: module paths; cmd_shape / CmdTFIBB / HaltsSpecC / AsanTop -> seg_shape / lib/B/SegTFIBB.v / HaltsSpecS / SegAsanTop, cmd_ -> seg_ in the lemma names, cmdsegsB -> segsegsB; the plain side is SegAsanTop.seg_plain_rz at its two Section premises discharged by the released plain tree: lib/AgreeSeg.v plain_slot_ag and lib/Prog/SegEnd.v segs_holds at the plain walks' cut record (the arguments lib/Prog/SegTop.v plain_halts_holds gives plain_halts_of_callees). *)
(* segconf's two ASan+UBSan statements from the ASan+UBSan side TFIB_T_B (lib/B/SegTFIBB.v), in the form of
   proofs/cgif/cgif_file_fuzzer/lib/YZ03.v (agreement) and lib/Halts_tfib.v (halting), the twin of SegAsanTop.v:
   - asan_ubsan_agrees: shape_strong_equiv_efs_relim (Reusable/YM09.v) over the plain build's proved realization of
     SPECX at 2^34 (SegAsanTop.v seg_plain_rz), the statement's plain budget premise, TFIB_T_B and t_eq_refl;
   - asan_ubsan_halts: halts_budgets_of_srealizes (Reusable/HaltsKitB.v) over TFIB_T_B and SPECX_shape_ok
     (HaltsSpecS.v). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.reac_pw.fuzz_segconf Require Statements Images.
From OSSVerify.reac_pw.fuzz_segconf.images Require Plain AsanUbsan.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
  YK11 YK15 YK18 YM05 YM02 YM0b YM09 YO0i YO0f YO05 YO09 YO06 HaltsKitB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import SegShape HaltsSpecS SegAsanTop.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import SegTFIBB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require AgreeSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require SegEnd SegTop.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require SegWalkMainA E01 M01 L01 L02T L03 M02 V01 X01.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

Section a.
Hypothesis TFIB : TFIB_T_B.

Theorem seg_asan_ubsan_agrees_of_tfib : Statements.asan_ubsan_agrees.
Proof.
  unfold Statements.asan_ubsan_agrees, agrees_in.
  intros en_s [sp' brk' mb' rnd'] inp Hens Hent Hinp SWB.
  pose proof (SegAsanTop.seg_plain_rz AgreeSeg.plain_slot_ag lib.Prog.Seg.SegWalkMainA.CPseg
    (lib.Prog.SegEnd.segs_holds lib.Prog.Seg.SegWalkMainA.CPseg _ _ _ _ _
       lib.Prog.Seg.E01.seg_E01_holds lib.Prog.Seg.M01.seg_M01_holds lib.Prog.Seg.L01.seg_L01_holds
       lib.Prog.Seg.L02T.seg_L02 lib.Prog.Seg.L03.seg_L03_holds lib.Prog.Seg.M02.seg_M02 lib.Prog.Seg.V01.seg_V01
       lib.Prog.Seg.X01.seg_X01_holds
       lib.Prog.SegTop.K_M01_holds lib.Prog.SegTop.K_L01_holds lib.Prog.SegTop.K_L02_holds
       lib.Prog.SegTop.K_M02_holds lib.Prog.SegTop.K_V01_holds lib.Prog.SegTop.calloc_concrete_holds)
    en_s inp Hens Hinp) as HP.
  destruct en_s as [sp brk mb rnd].
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  unfold Images.asan_ubsan in Hent.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent. destruct Hent as [Hsp' [Hbrk' [Hmb' Hfit']]].
  exact (shape_strong_equiv_efs_relim SanitizerBudgets.lim_source ShippedBudgets.lim_source SanitizerBudgets.lim_target
    Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mb rnd
    segsegsB AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp' brk' mb' rnd'
    (SPECX (LS:=seg_shape) inp) (SPECX (LS:=seg_shape) inp) inp
    asan_lim_source_le SWB HP (TFIB sp' brk' mb' rnd' inp Hsp' Hbrk' Hmb' Hfit' Hinp) (t_eq_refl _)).
Qed.

Theorem seg_asan_ubsan_halts_of_tfib : Statements.asan_ubsan_halts.
Proof.
  unfold Statements.asan_ubsan_halts, Images.asan_ubsan.
  change (halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source Exits.ok_or_refused
    (mkImage segsegsB AsanUbsan.M.init_pc AsanUbsan.M.phdrs)).
  apply (halts_budgets_of_srealizes forced_only_cfg Exits.ok_or_refused segsegsB AsanUbsan.M.init_pc AsanUbsan.M.phdrs
    target_alloc_limit ShippedBudgets.lim_source lim_source_le_target (forced_only_cfg_least _)).
  intros sp brk mb rnd inp Hen Hinp. exists (SPECX (LS:=seg_shape) inp). split.
  - pose proof (valid_input_va_size _ Hinp) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
    exact (TFIB sp brk mb rnd inp Hsp Hbrk Hmb Hfit Hinp).
  - exact (SPECX_shape_ok inp).
Qed.
End a.

Print Assumptions seg_asan_ubsan_agrees_of_tfib.
Print Assumptions seg_asan_ubsan_halts_of_tfib.
