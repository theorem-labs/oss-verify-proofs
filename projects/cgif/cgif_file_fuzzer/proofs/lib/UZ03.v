(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch premises entry_launch_ok_va and valid_input; the vDSO side goals closed): changed strong_universal_error_free_cgif_file_fuzzer_ubsan. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.cgif.cgif_file_fuzzer.images Require Import Plain.
From OSSVerify.cgif.cgif_file_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK15 YK18 YM08 YM09 YM05 YM0b YI0a.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO09 YO06.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YH00 UH00.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ04 UZ04.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.
Lemma shipped_lim_source_le_SRC_LIM_MIN : ShippedBudgets.lim_source <= SRC_LIM_MIN.
Proof. unfold ShippedBudgets.lim_source, source_alloc_limit, SRC_LIM_MIN. cbn. lia. Qed.
Theorem strong_universal_error_free_cgif_file_fuzzer_ubsan :
strong_universal_error_free_T_scfg_budgets (alloc_only_cfg false) ShippedBudgets.lim_source ShippedBudgets.lim_target
(mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
(mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof.
intros [sp brk mb rnd] [sp' brk' mb' rnd'] inp Hens Hent Hinp SWB.
pose proof (valid_input_va_size _ Hinp) as Hsv48.
rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
(* 75d69e00 Run.v:3747-3755: [valid_entry_sv48] is FIVE conjuncts now, with
   [entry_launch_ok_va Sv48 en inp] appended last; f1006fe8's was four and had
   no launch conjunct.  A four-name pattern leaves the launch fact buried
   inside [Hfit], where the [try assumption] below cannot see it. *)
destruct Hens as [Hsp [Hbrk [Hmb [Hfit Hlau]]]].
destruct Hent as [Hsp' [Hbrk' [Hmb' [Hfit' Hlau']]]].
eapply (shape_strong_equiv_ef_relim ShippedBudgets.lim_source SRC_LIM_MIN ShippedBudgets.lim_target
src0segs _ _ sp brk mb rnd ubs0segs _ _ sp' brk' mb' rnd' (SPECX (LS:=ff_lib_shape) inp) (SPECX (LS:=ff_lib_shape) inp) inp).
- exact shipped_lim_source_le_SRC_LIM_MIN.
- exact SWB.
- apply YZ04.src0_realizesX; try assumption. apply Z.le_refl.
- apply UZ04.ubs0_realizesX; try assumption. exact SRC_LIM_MIN_le_target.
- apply t_eq_refl.
- RomStable.vdso_none.
- RomStable.vdso_none.
Qed.
