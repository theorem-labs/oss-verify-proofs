(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import NArith List ZArith Lia Bool.
Require OSSVerify.cjson.cjson_read_fuzzer.images.Plain.
Require OSSVerify.cjson.cjson_read_fuzzer.images.Ubsan.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import Amb ShapeAlg ShapeEF ShapeSpec
  PStartup PStartupRT UStartup UStartupRT RealizesEqv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState PropExec Frame.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Unset Lia Cache.

Definition SRC0 : Image :=
  mkImage OSSVerify.cjson.cjson_read_fuzzer.images.Plain.M.loaded_segments
          OSSVerify.cjson.cjson_read_fuzzer.images.Plain.M.init_pc
          OSSVerify.cjson.cjson_read_fuzzer.images.Plain.M.phdrs.

Definition UBSAN : Image :=
  mkImage OSSVerify.cjson.cjson_read_fuzzer.images.Ubsan.M.loaded_segments
          OSSVerify.cjson.cjson_read_fuzzer.images.Ubsan.M.init_pc
          OSSVerify.cjson.cjson_read_fuzzer.images.Ubsan.M.phdrs.

Local Notation psegs := OSSVerify.cjson.cjson_read_fuzzer.images.Plain.M.loaded_segments (only parsing).
Local Notation usegs := OSSVerify.cjson.cjson_read_fuzzer.images.Ubsan.M.loaded_segments (only parsing).

(* [comment removed for export] *)
Definition p_main_stmt : Prop :=
  forall (sp brk mbase : word) (rnd : EntryDraw) (inp : ProcInput) (tid : word) (regs : bvmap 5 word) (mem : word -> option byte),
    valid_sp sp -> valid_brk psegs brk -> valid_mmap_base mbase -> valid_input inp ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    (0 < bv_unsigned tid < 2^22)%Z ->
    @p_main_entry (amb_of inp) sp rnd (in_argv inp) (in_envp inp) tid regs mem ->
    realizes psegs
      (mkCfg (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState.MS (mkR_of regs) bvmap_empty (Z_to_bv 64 0x1214c)
                (Z_to_bv 32 0) None mem (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec.seg_rom psegs))
             (with_tid tid (init_model (segments_reserved psegs) brk mbase sp source_alloc_limit inp)))
      (spec (in_argv inp) (in_fs inp)).

Definition u_main_stmt : Prop :=
  forall (sp brk mbase : word) (rnd : EntryDraw) (inp : ProcInput) (tid : word) (regs : bvmap 5 word) (mem : word -> option byte),
    valid_sp sp -> valid_brk usegs brk -> valid_mmap_base mbase -> valid_input inp ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    (0 < bv_unsigned tid < 2^22)%Z ->
    @u_main_entry (amb_of inp) sp rnd (in_argv inp) (in_envp inp) tid regs mem ->
    realizes usegs
      (mkCfg (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState.MS (mkR_of regs) bvmap_empty (Z_to_bv 64 0x1316c)
                (Z_to_bv 32 0) None mem (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec.seg_rom usegs))
             (with_tid tid (init_model (segments_reserved usegs) brk mbase sp target_alloc_limit inp)))
      (spec (in_argv inp) (in_fs inp)).

Theorem ubsan_base_of : p_main_stmt -> u_main_stmt -> strong_universal_error_free_T_scfg (alloc_only_cfg false) SRC0 UBSAN.
Proof.
  intros HP HU [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hinp.
  (* [comment removed for export] *)
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
  destruct Hens as [Hrsp [Hrbrk [Hrmb Hrfit]]]. destruct Hent as [Hasp [Habrk [Hamb Hafit]]].
  pose proof Hinp as Hinp'. destruct Hinp as [Hargv [Henvp _]].
  apply (shape_strong_equiv_ef _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spec (in_argv inp) (in_fs inp))).
  - apply (p_startup_rt rsp rbrk rmb rrnd source_alloc_limit inp _ Hrsp Hrbrk Hargv Henvp).
    intros tid regs mem Htid ME.
    assert (E : (0x1214c : word) = Z_to_bv 64 0x1214c) by (apply bv_eq; reflexivity).
    rewrite E. exact (HP rsp rbrk rmb rrnd inp tid regs mem Hrsp Hrbrk Hrmb Hinp' Hrfit Htid ME).
  - apply (u_startup_rt asp abrk amb arnd target_alloc_limit inp _ Hasp Habrk Hargv Henvp).
    intros tid regs mem Htid ME.
    assert (E : (0x1316c : word) = Z_to_bv 64 0x1316c) by (apply bv_eq; reflexivity).
    rewrite E. exact (HU asp abrk amb arnd inp tid regs mem Hasp Habrk Hamb Hinp' Hafit Htid ME).
Qed.
