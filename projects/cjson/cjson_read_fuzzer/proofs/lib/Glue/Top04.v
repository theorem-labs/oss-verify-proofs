(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import NArith List ZArith Lia Bool.
Require OSSVerify.cjson.cjson_read_fuzzer.images.Plain.
Require OSSVerify.cjson.cjson_read_fuzzer.images.Ubsan.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import Amb ShapeAlg ShapeEF ShapeSpec
  PStartup PStartupRT UStartup UStartupRT RealizesEqv TopUbsan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState PropExec Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require DrvTop.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KInv2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require DrvTop.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Notation psegs := OSSVerify.cjson.cjson_read_fuzzer.images.Plain.M.loaded_segments (only parsing).
Local Notation ppc := OSSVerify.cjson.cjson_read_fuzzer.images.Plain.M.init_pc (only parsing).
Local Notation pph := OSSVerify.cjson.cjson_read_fuzzer.images.Plain.M.phdrs (only parsing).
Local Notation usegs := OSSVerify.cjson.cjson_read_fuzzer.images.Ubsan.M.loaded_segments (only parsing).
Local Notation upc := OSSVerify.cjson.cjson_read_fuzzer.images.Ubsan.M.init_pc (only parsing).
Local Notation uph := OSSVerify.cjson.cjson_read_fuzzer.images.Ubsan.M.phdrs (only parsing).

(* [comment removed for export] *)
Definition p_main_stmt04 : Prop :=
  forall (sp brk mbase : word) (rnd : EntryDraw) (inp : ProcInput) (tid : word) (regs : bvmap 5 word) (mem : word -> option byte),
    valid_sp sp -> valid_brk psegs brk -> valid_mmap_base mbase -> valid_input inp ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    (0 < bv_unsigned tid < 2^22)%Z ->
    @p_main_entry (amb_of inp) sp rnd (in_argv inp) (in_envp inp) tid regs mem ->
    realizes psegs
      (mkCfg (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState.MS (mkR_of regs) bvmap_empty (Z_to_bv 64 0x1214c)
                (Z_to_bv 32 0) None mem (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec.seg_rom psegs))
             (with_tid tid (init_model (segments_reserved psegs) brk mbase sp source_alloc_limit inp)))
      (spec04 (in_argv inp) (in_fs inp)).

Definition u_main_stmt04 : Prop :=
  forall (sp brk mbase : word) (rnd : EntryDraw) (inp : ProcInput) (tid : word) (regs : bvmap 5 word) (mem : word -> option byte),
    valid_sp sp -> valid_brk usegs brk -> valid_mmap_base mbase -> valid_input inp ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    (0 < bv_unsigned tid < 2^22)%Z ->
    @u_main_entry (amb_of inp) sp rnd (in_argv inp) (in_envp inp) tid regs mem ->
    realizes usegs
      (mkCfg (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState.MS (mkR_of regs) bvmap_empty (Z_to_bv 64 0x1316c)
                (Z_to_bv 32 0) None mem (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec.seg_rom usegs))
             (with_tid tid (init_model (segments_reserved usegs) brk mbase sp target_alloc_limit inp)))
      (spec04 (in_argv inp) (in_fs inp)).

Theorem p_main_proof04 : p_main_stmt04.
Proof. exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.DrvTop.p_main_proof. Qed.

Theorem u_main_proof04 : u_main_stmt04.
Proof. exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.DrvTop.u_main_proof. Qed.

(* [comment removed for export] *)
Theorem plain_realizes04 : forall (sp brk mbase : word) (rnd : EntryDraw) (inp : ProcInput),
  valid_entry SRC0 (mkEntry sp brk mbase rnd) inp -> valid_input inp ->
  realizes psegs (init_config psegs ppc pph sp brk mbase rnd source_alloc_limit inp) (spec04 (in_argv inp) (in_fs inp)).
Proof.
  intros sp brk mbase rnd inp Hen Hinp.
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen.
  destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
  pose proof Hinp as Hinp'. destruct Hinp as [Hargv [Henvp _]].
  apply (p_startup_rt sp brk mbase rnd source_alloc_limit inp _ Hsp Hbrk Hargv Henvp).
  intros tid regs mem Htid ME.
  assert (E : (0x1214c : word) = Z_to_bv 64 0x1214c) by (apply bv_eq; reflexivity).
  rewrite E. exact (p_main_proof04 sp brk mbase rnd inp tid regs mem Hsp Hbrk Hmb Hinp' Hfit Htid ME).
Qed.

(* [comment removed for export] *)
Theorem plain_realizes04_lim : forall (lim : Z), (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv2.drv_limit <= lim)%Z ->
  forall (sp brk mbase : word) (rnd : EntryDraw) (inp : ProcInput),
  valid_entry SRC0 (mkEntry sp brk mbase rnd) inp -> valid_input inp ->
  realizes psegs (init_config psegs ppc pph sp brk mbase rnd lim inp) (spec04 (in_argv inp) (in_fs inp)).
Proof.
  intros lim Hlim sp brk mbase rnd inp Hen Hinp.
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen.
  destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
  pose proof Hinp as Hinp'. destruct Hinp as [Hargv [Henvp _]].
  apply (p_startup_rt sp brk mbase rnd lim inp _ Hsp Hbrk Hargv Henvp).
  intros tid regs mem Htid ME.
  assert (E : (0x1214c : word) = Z_to_bv 64 0x1214c) by (apply bv_eq; reflexivity).
  rewrite E. exact (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.DrvTop.p_main_proof_lim lim Hlim sp brk mbase rnd inp tid regs mem Hsp Hbrk Hmb Hinp' Hfit Htid ME).
Qed.

Lemma sanitizer_limit_ok : (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv2.drv_limit <= sanitizer_source_limit)%Z.
Proof. unfold OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv2.drv_limit, sanitizer_source_limit. lia. Qed.

Theorem ubsan_realizes04 : forall (sp brk mbase : word) (rnd : EntryDraw) (inp : ProcInput),
  valid_entry UBSAN (mkEntry sp brk mbase rnd) inp -> valid_input inp ->
  realizes usegs (init_config usegs upc uph sp brk mbase rnd target_alloc_limit inp) (spec04 (in_argv inp) (in_fs inp)).
Proof.
  intros sp brk mbase rnd inp Hen Hinp.
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen.
  destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
  pose proof Hinp as Hinp'. destruct Hinp as [Hargv [Henvp _]].
  apply (u_startup_rt sp brk mbase rnd target_alloc_limit inp _ Hsp Hbrk Hargv Henvp).
  intros tid regs mem Htid ME.
  assert (E : (0x1316c : word) = Z_to_bv 64 0x1316c) by (apply bv_eq; reflexivity).
  rewrite E. exact (u_main_proof04 sp brk mbase rnd inp tid regs mem Hsp Hbrk Hmb Hinp' Hfit Htid ME).
Qed.

(* [comment removed for export] *)
Theorem ubsan_realizes04_lim : forall (lim : Z), (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv2.drv_limit <= lim)%Z ->
  forall (sp brk mbase : word) (rnd : EntryDraw) (inp : ProcInput),
  valid_entry UBSAN (mkEntry sp brk mbase rnd) inp -> valid_input inp ->
  realizes usegs (init_config usegs upc uph sp brk mbase rnd lim inp) (spec04 (in_argv inp) (in_fs inp)).
Proof.
  intros lim Hlim sp brk mbase rnd inp Hen Hinp.
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen.
  destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
  pose proof Hinp as Hinp'. destruct Hinp as [Hargv [Henvp _]].
  apply (u_startup_rt sp brk mbase rnd lim inp _ Hsp Hbrk Hargv Henvp).
  intros tid regs mem Htid ME.
  assert (E : (0x1316c : word) = Z_to_bv 64 0x1316c) by (apply bv_eq; reflexivity).
  rewrite E. exact (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.DrvTop.u_main_proof_lim lim Hlim sp brk mbase rnd inp tid regs mem Hsp Hbrk Hmb Hinp' Hfit Htid ME).
Qed.

(* [comment removed for export] *)
Theorem ubsan_base04 : strong_universal_error_free_T_scfg (alloc_only_cfg false) SRC0 UBSAN.
Proof.
  intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hinp.
  apply (shape_strong_equiv_ef _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spec04 (in_argv inp) (in_fs inp))).
  - exact (plain_realizes04 rsp rbrk rmb rrnd inp Hens Hinp).
  - exact (ubsan_realizes04 asp abrk amb arnd inp Hent Hinp).
Qed.

(* [comment removed for export] *)
Theorem ubsan_base04_budgets :
  strong_universal_error_free_T_scfg_budgets (alloc_only_cfg false) source_alloc_limit target_alloc_limit SRC0 UBSAN.
Proof. apply strong_universal_error_free_T_scfg_budgets_of_scfg. exact ubsan_base04. Qed.

