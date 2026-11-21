(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (walks lifted to the run's segments, the launch input's kernel build): changed must_exit_cfg0_big. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import ShapeAlg DivergeSim SpinAlg Spec BigintSpec HeapIface LibIface LibIfaceFp L5Defs L5Core VmLimitFrame HaltsBridge HaltsSpec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import AsanAcct HeapIfaceA HeapIfaceANull PmHeapIfaceA IcptIfaceA PmIcptIfaceA Pm8IcptLayout Pm8ArtIfaceInst Pm8ArtIfaceInstX
  PmLibDefsA PmLibSpecsA PmCurSpecsA PmLibAssemblyCA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require PmFinal.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmCasanFinal.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Common.LimSim Require Import LimSimSys.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Common.Cfg Require SRomStable.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmInteg Require PmCasanLibTop.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PmHaltsAsanC.
Section FPX_1.
#[local] Existing Instance PropExec.fx0.
Abbreviation TGT := (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).

Definition CODES : list word := [Z_to_bv 64 0; Z_to_bv 64 2].
Lemma codes_0 : In (exit_code 0) CODES.  Proof. left. reflexivity. Qed.
Lemma codes_2 : In (exit_code 2) CODES.  Proof. right. left. reflexivity. Qed.

Let LIBTOP := PmCasanLibTop.PmCasanLibTop.libtop.
Let LIBA := ASMC.la4 PmCasanFinal.cfg0 art_IL art_ILX art_IL_ok art_ILX_ok LIBTOP.

Lemma must_exit_cfg0_big : forall en inp, valid_entry TGT en inp -> valid_input inp ->
  must_exit_in_scfg PmCasanFinal.cfg0 CODES TGT target_alloc_limit en inp.
Proof.
  intros [sp brk mb rnd] inp Hen Hvalid.
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb [Hfit Hlau]]]].
  (* valid_entry's 5th conjunct is the launch; valid_input is read through the model's BY-NAME
     accessors (as PmCasanFinal.fuzz_json_cursor_asan_base_scfg does), for
     [PmCasanFinal.pm_casan_tgt_stmt]'s premises. *)
  eapply (srealizes_must_exit_init_fo _ PmCasanFinal.cfg0 CODES).
  - (* the run reads the binary's segments with the run's vDSO appended
       ([Run.run_segments]); [SRomStable.srun_init] lifts the walk over the binary's own
       segments ([vdso_image] of them is [None] by computation) *)
    apply (SRomStable.srun_init PmCasanFinal.cfg0 Asan.M.loaded_segments inp sp mb _ _ _ _ _ _ eq_refl).
    exact (PmCasanFinal.pm_casan_tgt ASMC.LayC8 ASMC.LStC8 ASMC.la1 ASMC.la2 ASMC.la3 LIBA sp brk mb rnd inp Hsp Hbrk Hmb Hfit
             (valid_input_argv _ Hvalid) (valid_input_envp _ Hvalid) (valid_input_fs _ Hvalid)
             (valid_input_creds _ Hvalid) (valid_input_hwcap _ Hvalid) Hsv48 (valid_input_launch _ Hvalid) Hlau
             (valid_input_channel_reader _ Hvalid)
             (valid_input_sigpipe_terminal _ Hvalid) (valid_input_recorded_kernel _ Hvalid)).
  - apply Safe_init_big. exact nbr_limit_target.
  - reflexivity.
  - apply HaltsSpec.codes_ok_spec; [exact codes_0 | exact codes_2].
  - apply HaltsSpec.nokill_spec.
Qed.

Theorem halts_asan : halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source [Z_to_bv 64 0; Z_to_bv 64 2] TGT.
Proof.
  apply (halts_allowed_of_must_exit_wb forced_only_cfg). { apply forced_only_cfg_least. }
  intros en inp Hen Hvalid Hwb.
  apply (must_exit_in_scfg_relim_closed forced_only_cfg _ TGT target_alloc_limit ShippedBudgets.lim_source en inp).
  - cbv. discriminate.
  - exact Hwb.
  - apply (must_exit_in_scfg_forced_only PmCasanFinal.cfg0). exact (must_exit_cfg0_big en inp Hen Hvalid).
Qed.
End FPX_1.
End PmHaltsAsanC.
