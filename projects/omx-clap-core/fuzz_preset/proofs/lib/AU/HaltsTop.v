(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/Halts_tfib.v (the asan-ubsan halting theorem), by way of grant_asan_halts_of_tfib in proofs/libreac/fuzz_grant/lib/A/AsanTop.v (a working branch 0bed23e5b69) and fuzz_preset's lib/A/AsanTop.v (a working branch 7837446fad0), for omx-clap-core/fuzz_preset: the halting theorem only, over fuzz_preset's asan-ubsan image; the hypothesis gives the trace set and its exit lemma together (lib/AU/HaltsTFIB.v); module paths and the image changed. *)
(* fuzz_preset's asan_ubsan_halts from the ASan side TFIB_T_AU_H (lib/AU/HaltsTFIB.v), its one hypothesis, in the
   form of proofs/cgif/cgif_file_fuzzer/lib/Halts_tfib.v: halts_budgets_of_srealizes (Reusable/HaltsKitB.v) over
   TFIB_T_AU_H. Around it this file discharges: the entry premises from valid_entry (valid_entry_sv48); the re-limit
   of the asan-ubsan run from 512 GiB to the statement's 16 GiB with the statement's own premise (Reusable/YQ05.v
   must_exit_in_scfg_relim_closed); forced_only_cfg below ACFG = alloc_only_cfg false (must_exit_in_scfg_mono,
   forced_only_cfg_least); and the walk from srealizes and exits 0 or 2 to must-exit (HaltsKitB.v
   srealizes_must_exit_in). There is no plain run in this statement, so RelimCut.v has no part here.

   RULING (the unit owner, 2026-10-28T20:25:03Z, point 2 of the ruling on the agrees and halts tops; the ruling asks that
   each top file record it): the halts tops (A: lib/A/AsanTop.v, B: this file) carry only the halts statement's
   16 GiB premise. A full size class
   is an EXIT question (the refusal path, exit 0, measured), not a trace mismatch. So TFIB states the ASan side with
   the class-full NULL arm reachable and with no extra plain argument. A is written first (lib/A/AsanTop.v) and this
   file mirrors it. Point 1 of the same ruling (the agrees tops' extra plain no-refusal argument) does not apply. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.omx_clap_core.fuzz_preset Require Statements Images.
From OSSVerify.omx_clap_core.fuzz_preset.images Require AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 HaltsKitB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PresetTFIBAU HaltsTFIB.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

Lemma lim_source_le_target_AU : ShippedBudgets.lim_source <= target_alloc_limit.
Proof. unfold ShippedBudgets.lim_source, source_alloc_limit, target_alloc_limit. cbn. lia. Qed.

Section a.
Hypothesis TFIB : TFIB_T_AU_H.

Theorem preset_asan_ubsan_halts_of_tfib : Statements.asan_ubsan_halts.
Proof.
  unfold Statements.asan_ubsan_halts, Images.asan_ubsan.
  change (halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source Exits.ok_or_refused
    (mkImage presetsegsAU AsanUbsan.M.init_pc AsanUbsan.M.phdrs)).
  apply (halts_budgets_of_srealizes forced_only_cfg Exits.ok_or_refused presetsegsAU AsanUbsan.M.init_pc
    AsanUbsan.M.phdrs target_alloc_limit ShippedBudgets.lim_source lim_source_le_target_AU (forced_only_cfg_least _)).
  intros sp brk mb rnd inp Hen Hinp.
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
  exact (TFIB sp brk mb rnd inp Hsp Hbrk Hmb Hfit Hinp).
Qed.
End a.
