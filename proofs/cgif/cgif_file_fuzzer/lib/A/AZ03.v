(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Plain.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK15 YK18 YM08 YM09 YM05 YM0b YI0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO09 YO06.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YH00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YZ04.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.
Definition tfibsegs0 : list Segment := Asan.M.loaded_segments.
Definition TFIB_T : Prop :=
forall sp brk mbase rnd inp,
valid_sp sp -> valid_brk tfibsegs0 brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
srealizes tfibsegs0
(init_config tfibsegs0 Asan.M.init_pc Asan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
(SPECX (LS:=ff_lib_shape) inp).
Lemma lim_source_le_SRC_LIM_MIN : SanitizerBudgets.lim_source <= SRC_LIM_MIN.
Proof. unfold SanitizerBudgets.lim_source, sanitizer_source_limit, SRC_LIM_MIN. cbn. lia. Qed.
Section a.
Hypothesis TFIB : TFIB_T.
Theorem cgif_file_fuzzer_asan_equiv_of_tfib :
strong_universal_error_free_T_scfg_budgets (alloc_only_cfg false) SanitizerBudgets.lim_source SanitizerBudgets.lim_target
(mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
(mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).
Proof.
intros [sp brk mb rnd] [sp' brk' mb' rnd'] inp Hens Hent Hinp SWB.
pose proof (valid_input_va_size _ Hinp) as Hsv48.
rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
destruct Hens as [Hsp [Hbrk [Hmb Hfit]]]. destruct Hent as [Hsp' [Hbrk' [Hmb' Hfit']]].
eapply (shape_strong_equiv_efs_relim SanitizerBudgets.lim_source SRC_LIM_MIN SanitizerBudgets.lim_target
src0segs _ _ sp brk mb rnd tfibsegs0 _ _ sp' brk' mb' rnd' (SPECX (LS:=ff_lib_shape) inp) (SPECX (LS:=ff_lib_shape) inp) inp).
- exact lim_source_le_SRC_LIM_MIN.
- exact SWB.
- apply src0_realizesX; try assumption. apply Z.le_refl.
- apply TFIB; assumption.
- apply t_eq_refl.
Qed.
End a.
Theorem strong_universal_error_free_cgif_file_fuzzer_asan_of_tfib : TFIB_T ->
strong_universal_error_free_T_scfg_budgets (alloc_only_cfg false) SanitizerBudgets.lim_source SanitizerBudgets.lim_target
(mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
(mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).
Proof. exact cgif_file_fuzzer_asan_equiv_of_tfib. Qed.
