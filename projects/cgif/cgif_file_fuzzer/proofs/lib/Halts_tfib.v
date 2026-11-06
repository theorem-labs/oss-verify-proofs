(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.cgif.cgif_file_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK15 YK18 YM05 YO06 YI0a YZ03 YD2p.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import HaltsKitB HaltsSpecX.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.

Lemma lim_source_le_target : ShippedBudgets.lim_source <= target_alloc_limit.
Proof. unfold ShippedBudgets.lim_source, source_alloc_limit, target_alloc_limit. cbn. lia. Qed.

Theorem tfib_realizesX : forall sp brk mb rnd inp,
  valid_entry (mkImage tfibsegs0 AsanUbsan.M.init_pc AsanUbsan.M.phdrs) (mkEntry sp brk mb rnd) inp ->
  valid_input inp ->
  realizes tfibsegs0
    (init_config tfibsegs0 AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp brk mb rnd target_alloc_limit inp)
    (SPECX (LS:=ff_lib_shape) inp).
Proof.
  intros sp brk mb rnd inp Hen Hinp.
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
  apply realizes_of_srealizes. exact (TFIB_T_closed sp brk mb rnd inp Hsp Hbrk Hmb Hfit Hinp).
Qed.

Theorem halts_allowed_cgif_cgif_file_fuzzer_halts_both_closed :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source exits02
    (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof.
  apply (halts_budgets_of_realizes forced_only_cfg exits02 _ _ _ target_alloc_limit ShippedBudgets.lim_source lim_source_le_target (forced_only_cfg_least _)).
  intros sp brk mb rnd inp Hen Hinp. exists (SPECX (LS:=ff_lib_shape) inp). split.
  - exact (tfib_realizesX sp brk mb rnd inp Hen Hinp).
  - apply SPECX_shape_ok.
Qed.
