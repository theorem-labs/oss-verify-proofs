(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.cgif.cgif_rgb_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK15 YK18 YN05 YP01 YB0l YZ00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import HaltsFO HaltsKitFO DriverClosedHalts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.

Lemma tra_lim_source_le_target : ShippedBudgets.lim_source <= target_alloc_limit.
Proof. unfold ShippedBudgets.lim_source, source_alloc_limit, target_alloc_limit. cbn. lia. Qed.

Theorem halts_allowed_cgif_cgif_rgb_fuzzer_halts_asan_closed :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source codes02
    (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).
Proof.
  apply (halts_budgets_of_srealizes codes02 _ _ _ target_alloc_limit ShippedBudgets.lim_source tra_lim_source_le_target).
  intros sp brk mb rnd inp Hen Hinp. exists (CLOSED inp). split.
  - pose proof (valid_input_va_size _ Hinp) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
    change Asan.M.loaded_segments with TSEGS.
    exact (tra_srealizes_top sp rnd brk mb inp Hsp Hbrk Hmb Hfit Hinp).
  - apply CLOSED_shape_ok.
Qed.
