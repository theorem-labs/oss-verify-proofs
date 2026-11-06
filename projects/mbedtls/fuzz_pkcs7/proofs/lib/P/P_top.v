(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.mbedtls.fuzz_pkcs7.images Require Import Plain.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AEvt AStep HeapIface HeapRz RegsExt Shape.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_layout P_heap.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec TopContract SInv.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Frame.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_startup P_main_entry P_main_open P_main_skel P_main_cut P_main_file P_main_body P_cutheap P_main_top.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require P_heap_rz.
Import ListNotations.
#[local] Existing Instance PropExec.fx0.
Open Scope Z_scope.

Lemma P_heap_init_full {LM : Lim} : heap_init_full P_heap_rz.P_DRV P_heap_rz.P_nosmall.
Proof.
  intros AMB sp0 rc m tid brk mbase fs0 stdin0 fd3 top HI.
  destruct (P_heap_rz.P_heap_init_drv sp0 rc m _ top HI) as (h & HP & HT & HD & HN).
  - reflexivity.
  - change (vm_limit _) with LIM. pose proof LIM_ge. lia.
  - exists h. rewrite HEAP_P_HI, heap_top_P_HI. auto.
Qed.

Section Top.
  Variable SI : forall sp0 : word, sinv (P_layout sp0).
  Hypothesis SIFP : forall (sp0 : word) (a : Z), ~ outside (si_fp (SI sp0)) a -> 0x59890 <= a < 0x598f8.
  Hypothesis FUZZ : forall sp0 : word, fuzz_entry_stmt psegs (P_layout sp0) (P_HI sp0) (SI sp0) 0x1d26c.

  #[using="SI SIFP FUZZ"] Theorem P_realizes_spec_LM {AMB : Amb} {LM : Lim} : forall sp brk mbase (rd : EntryDraw) (inp : ProcInput),
    valid_sp sp -> valid_brk psegs' brk ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->                 (* [comment removed for export] *)
    realizes psegs' (init_config psegs' ppc pph sp brk mbase rd LIM inp) (spec (in_argv inp) (in_fs inp)).
  Proof.
    apply (P_realizes_spec_drv P_heap_rz.P_DRV P_heap_rz.P_nosmall P_heap_rz.P_malloc_rz P_heap_rz.P_free_c P_heap_rz.P_drv_mo SI SIFP FUZZ).
    apply heap_at_cut_of_init. apply P_heap_init_full.
    all: exact AMB.
  Qed.

  (* [comment removed for export] *)
  #[using="SI SIFP FUZZ"] Theorem P_realizes_spec_lim {AMB : Amb} : forall (lim : Z) sp brk mbase (rd : EntryDraw) (inp : ProcInput),
    2 ^ 31 <= lim ->
    valid_sp sp -> valid_brk psegs' brk ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    realizes psegs' (init_config psegs' ppc pph sp brk mbase rd lim inp) (spec (in_argv inp) (in_fs inp)).
  Proof.
    intros lim sp brk mbase rd inp Hlim. exact (@P_realizes_spec_LM AMB (mkLim lim Hlim) sp brk mbase rd inp).
  Qed.

  (* [comment removed for export] *)
  #[using="SI SIFP FUZZ"] Theorem P_realizes_spec {AMB : Amb} : forall sp brk mbase (rd : EntryDraw) (inp : ProcInput),
    valid_sp sp -> valid_brk psegs' brk ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->                 (* [comment removed for export] *)
    realizes psegs' (init_config psegs' ppc pph sp brk mbase rd source_alloc_limit inp) (spec (in_argv inp) (in_fs inp)).
  Proof.
    intros sp brk mbase rd inp. exact (P_realizes_spec_lim source_alloc_limit sp brk mbase rd inp source_alloc_limit_ge31).
  Qed.

  (* [comment removed for export] *)
  End Top.

(* [comment removed for export] *)
