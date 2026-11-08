(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from projects/cgif/cgif_rgb_fuzzer/proofs/lib/YZ03.v (halts_src2, lines 12-23) and YZ00.v (cgif_rgb_fuzzer_asan_equiv, lines 112-116) at commit c395a1e0dfa, with src2segs replaced by ubs2segs, Plain.M.init_pc and Plain.M.phdrs by Ubsan.M.init_pc and Ubsan.M.phdrs, src2_realizes by UZ02.ubs2_realizes and cgif_rgb_fuzzer_asan_equiv_lim by UZZ0.cgif_rgb_fuzzer_ubsan_equiv_lim. *)
From Stdlib Require Import NArith ZArith List Lia Bool QArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.EquivalenceDefinition Require Import FinInput Classifier Measure.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Examples Omni SpuriousCfg.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.cgif.cgif_rgb_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK15 YN05 YN0b YN01 UH04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP07 YP08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UZ02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import HaltsFO.
Require OSSVerify.cgif.cgif_rgb_fuzzer.Images.
Require OSSVerify.cgif.cgif_rgb_fuzzer.Statements.
Require OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib.UZZ0.
Require OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib.ConstAccept.
Require OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib.HaltsPlainFO.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.

(* The UBSan build halts on every input, with any status, whatever the
   environment refuses: the plain-build argument of YZ03.halts_src2, over the
   UBSan realizes fact. *)
Theorem halts_ubs2 :
  halts_allowed_T_scfg may_fail_cfg AnyExit.codes
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof.
intros [sp brk mb rnd] inp Hen Hinp.
pose proof (valid_input_va_size _ Hinp) as Hsv48.
rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen.
destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
unfold must_exit_in_scfg.
apply (halts_of_realizes ubs2segs byte_codes _ _ sp brk mb rnd source_alloc_limit inp (SPEC inp)).
- apply ubs2_realizes; try assumption. apply SRC_LIM_MIN_le_source.
- apply SPEC_tsafe.
Qed.

(* The UBSan build exits with status 0 or 2 under the forced-only
   configuration, within the shipped source budget: the plain-build argument of
   HaltsPlainFO.halts_plain_forced_only, over the UBSan realizes fact. *)
Theorem halts_ubsan_forced_only :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source codes02
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof.
apply halts_allowed_T_scfg_budgets_of_scfg.
intros [sp brk mb rnd] inp Hen Hinp.
pose proof (valid_input_va_size _ Hinp) as Hsv48.
rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen.
destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
unfold must_exit_in_scfg.
apply (fo_exits_must_exit ubs2segs codes02 _ (SPEC inp)).
- apply fo_of_realizes. apply ubs2_realizes; try assumption. apply SRC_LIM_MIN_le_source.
- apply OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib.HaltsPlainFO.SPEC_shape_ok02.
- reflexivity.
Qed.

Lemma SRC_LIM_MIN_le_target : SRC_LIM_MIN <= target_alloc_limit.
Proof. unfold SRC_LIM_MIN, target_alloc_limit. cbn. lia. Qed.

(* The unbudgeted equivalence of the plain and UBSan builds, at the plain
   build's 16 GiB and the UBSan build's 512 GiB, from the budget-parametric
   fact UZZ0 proves. *)
Theorem cgif_rgb_fuzzer_ubsan_equiv :
  strong_universal_error_free_T
    OSSVerify.cgif.cgif_rgb_fuzzer.Images.plain
    OSSVerify.cgif.cgif_rgb_fuzzer.Images.ubsan.
Proof.
intros en_s en_t inp Hs Ht Hv.
exact (OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib.UZZ0.cgif_rgb_fuzzer_ubsan_equiv_lim
         source_alloc_limit target_alloc_limit
         SRC_LIM_MIN_le_source SRC_LIM_MIN_le_target en_s en_t inp Hs Ht Hv).
Qed.

Lemma ubsan_base :
  strong_universal_error_free_T_scfg Env.may_fail
    OSSVerify.cgif.cgif_rgb_fuzzer.Images.plain
    OSSVerify.cgif.cgif_rgb_fuzzer.Images.ubsan.
Proof.
exact (proj2 (strong_universal_error_free_T_scfg_may_fail
                OSSVerify.cgif.cgif_rgb_fuzzer.Images.plain
                OSSVerify.cgif.cgif_rgb_fuzzer.Images.ubsan)
         cgif_rgb_fuzzer_ubsan_equiv).
Qed.

Theorem ubsan_bound_0 : OSSVerify.cgif.cgif_rgb_fuzzer.Statements.ubsan_disagrees_at_most 0.
Proof. exact (OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib.ConstAccept.disagrees_at_most_0 _ _ _ _ _ ubsan_base). Qed.

Theorem ubsan_decidable : OSSVerify.cgif.cgif_rgb_fuzzer.Statements.ubsan_agreement_decidable.
Proof. exact (OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib.ConstAccept.agreement_decidable_of_base _ _ _ ubsan_base). Qed.
