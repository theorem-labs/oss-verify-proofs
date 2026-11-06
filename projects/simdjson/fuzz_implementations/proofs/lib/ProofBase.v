(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import PropExec MState Frame Exec ITree Nodes RegsEquiv Image.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib Require Import TopLevel Obligations.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prog ModelInv ProgDetIface ProgDet ProgNoEnomem.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import ModelInvN MallocSome.
From OSSVerify.simdjson.fuzz_implementations.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition impl_P_stmt : Prop :=
  forall (en : ExecEntry) (inp : ProcInput),
    valid_entry (mkImage psegs SrcP.M.init_pc SrcP.M.phdrs) en inp ->
    valid_input_either inp ->
    impl psegs (at_node psegs) (the_prog psegs pstage inp en) (epost the_post)
         (ms0 psegs SrcP.M.init_pc SrcP.M.phdrs en inp).

Definition impl_U_stmt : Prop :=
  forall (en : ExecEntry) (inp : ProcInput),
    valid_entry (mkImage usegs Ubsan.M.init_pc Ubsan.M.phdrs) en inp ->
    valid_input_either inp ->
    impl usegs (at_node usegs) (the_prog usegs ustage inp en) (epost the_post)
         (ms0 usegs Ubsan.M.init_pc Ubsan.M.phdrs en inp).

Definition noenomem_P_stmt : Prop := prog_no_enomem_stmt psegs pstage SrcP.M.init_pc SrcP.M.phdrs source_alloc_limit.
Definition noenomem_U_stmt : Prop := prog_no_enomem_stmt usegs ustage Ubsan.M.init_pc Ubsan.M.phdrs target_alloc_limit.

Lemma base_obligations_of_parts :
  impl_P_stmt -> impl_U_stmt -> noenomem_P_stmt -> noenomem_U_stmt -> base_obligations.
Proof.
  intros HP HU LP LU. constructor.
  - intros en inp He Hi. split; [exact (HP en inp He Hi)|].
    destruct (prog_model_ok_P (CE__:=run_ceiling en) (raw_malloc_some (CE__:=run_ceiling en)) en inp He Hi (run_ceiling_eq _ _ _ _ _ (vie_va_size _ Hi) He) (LP en inp He Hi)) as [Hl Hs].
    split; [exact Hl|]. exact (tsafe_conj nstep nsafe unforced _ _ Hs (tsafe_mono nstep no_enomem unforced _ _ no_enomem_unforced (LP en inp He Hi))).
  - intros en inp He Hi. split; [exact (HU en inp He Hi)|].
    destruct (prog_model_ok_U (CE__:=run_ceiling en) (raw_malloc_some (CE__:=run_ceiling en)) en inp He Hi (run_ceiling_eq _ _ _ _ _ (vie_va_size _ Hi) He) (LU en inp He Hi)) as [Hl Hs].
    split; [exact Hl|]. exact (tsafe_conj nstep nsafe unforced _ _ Hs (tsafe_mono nstep no_enomem unforced _ _ no_enomem_unforced (LU en inp He Hi))).
  - intros enP enU inp HeP HeU Hi. exact (trees_equiv_of_no_enomem LP LU enP enU inp HeP HeU Hi).
Qed.

Theorem base_ubsan_of_parts :
  impl_P_stmt -> impl_U_stmt -> noenomem_P_stmt -> noenomem_U_stmt ->
  strong_universal_error_free_T_scfg ACFG
    (mkImage SrcP.M.loaded_segments SrcP.M.init_pc SrcP.M.phdrs)
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof.
  intros HP HU LP LU. apply base_ubsan_from_obligations. exact (base_obligations_of_parts HP HU LP LU).
Qed.

Theorem base_ubsan_scfg_of_parts :
  impl_P_stmt -> impl_U_stmt -> noenomem_P_stmt -> noenomem_U_stmt ->
  strong_universal_error_free_T_scfg ACFG
    (mkImage SrcP.M.loaded_segments SrcP.M.init_pc SrcP.M.phdrs)
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof.
  intros HP HU LP LU. apply base_ubsan_scfg_from_obligations. exact (base_obligations_of_parts HP HU LP LU).
Qed.

Theorem base_ubsan_of_impls :
  impl_P_stmt -> impl_U_stmt ->
  strong_universal_error_free_T_scfg ACFG
    (mkImage SrcP.M.loaded_segments SrcP.M.init_pc SrcP.M.phdrs)
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof. intros HP HU. exact (base_ubsan_of_parts HP HU prog_no_enomem_P prog_no_enomem_U). Qed.

Theorem base_ubsan_scfg_of_impls :
  impl_P_stmt -> impl_U_stmt ->
  strong_universal_error_free_T_scfg ACFG
    (mkImage SrcP.M.loaded_segments SrcP.M.init_pc SrcP.M.phdrs)
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof. intros HP HU. exact (base_ubsan_scfg_of_parts HP HU prog_no_enomem_P prog_no_enomem_U). Qed.

