(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AEvt AStep HeapIface HeapRz RegsExt Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_layout U_heap.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec TopContract SInv.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_startup U_main_entry U_main_open U_main_skel U_main_cut U_main_file U_main_body U_cutheap U_main_top.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require U_heap_rz.
Import ListNotations.
#[local] Existing Instance PropExec.fx0.
Open Scope Z_scope.

Lemma U_heap_init_full {LM : Lim} : heap_init_full U_heap_rz.U_DRV U_heap_rz.U_nosmall.
Proof.
  intros AMB sp0 rc m tid brk mbase fs0 stdin0 fd3 top HI.
  destruct (U_heap_rz.U_heap_init_drv sp0 rc m _ top HI) as (h & HP & HT & HD & HN).
  - reflexivity.
  - change (vm_limit _) with LIM. pose proof LIM_ge. lia.
  - exists h. rewrite HEAP_P_HI, heap_top_P_HI. auto.
Qed.

Section Top.
  Variable SI : forall sp0 : word, sinv (U_layout sp0).
  Hypothesis SIFP : forall (sp0 : word) (a : Z), ~ outside (si_fp (SI sp0)) a -> 0x5cf90 <= a < 0x5cff8.
  Hypothesis FUZZ : forall sp0 : word, fuzz_entry_stmt usegs (U_layout sp0) (U_HI sp0) (SI sp0) 0x1d6ec.

  #[using="SI SIFP FUZZ"] Theorem U_realizes_spec_LM {AMB : Amb} {LM : Lim} : forall sp brk mbase (rd : EntryDraw) (inp : ProcInput),
    valid_sp sp -> valid_brk usegs' brk ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->                 (* [comment removed for export] *)
    realizes usegs' (init_config usegs' upc uph sp brk mbase rd LIM inp) (spec (in_argv inp) (in_fs inp)).
  Proof.
    apply (U_realizes_spec_drv U_heap_rz.U_DRV U_heap_rz.U_nosmall U_heap_rz.U_malloc_rz U_heap_rz.U_free_c U_heap_rz.U_drv_mo SI SIFP FUZZ).
    apply heap_at_cut_of_init. apply U_heap_init_full.
    all: exact AMB.
  Qed.

  (* [comment removed for export] *)
  #[using="SI SIFP FUZZ"] Theorem U_realizes_spec_lim {AMB : Amb} : forall (lim : Z) sp brk mbase (rd : EntryDraw) (inp : ProcInput),
    2 ^ 31 <= lim ->
    valid_sp sp -> valid_brk usegs' brk ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    realizes usegs' (init_config usegs' upc uph sp brk mbase rd lim inp) (spec (in_argv inp) (in_fs inp)).
  Proof.
    intros lim sp brk mbase rd inp Hlim. exact (@U_realizes_spec_LM AMB (mkLim lim Hlim) sp brk mbase rd inp).
  Qed.

  (* [comment removed for export] *)
  #[using="SI SIFP FUZZ"] Theorem U_realizes_spec {AMB : Amb} : forall sp brk mbase (rd : EntryDraw) (inp : ProcInput),
    valid_sp sp -> valid_brk usegs' brk ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->                 (* [comment removed for export] *)
    realizes usegs' (init_config usegs' upc uph sp brk mbase rd source_alloc_limit inp) (spec (in_argv inp) (in_fs inp)).
  Proof.
    intros sp brk mbase rd inp. exact (U_realizes_spec_lim source_alloc_limit sp brk mbase rd inp source_alloc_limit_ge31).
  Qed.

  (* [comment removed for export] *)
  End Top.

(* [comment removed for export] *)
