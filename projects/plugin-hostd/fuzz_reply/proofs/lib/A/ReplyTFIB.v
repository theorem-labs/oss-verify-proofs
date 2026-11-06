(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from the TFIB_T definition of proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v for fuzz_reply's ASan image and checksum_shape; module paths changed. *)
(* What the ASan sides of fuzz_reply's four ASan statements prove: from every valid start, the ASan build (TFIB_T)
   and the ASan+UBSan build (TFIB_B_T) realize the same trace set SPECX as the plain build (lib/Reusable/YK18.v
   srealizes, no cut). *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import Asan.
From OSSVerify.plugin_hostd.fuzz_reply.images Require AsanUbsan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK15 YK18 YM05 YO09 YO06.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
Import ListNotations.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.
Definition replysegs0 : list Segment := Asan.M.loaded_segments.
Definition TFIB_T : Prop :=
forall sp brk mbase rnd inp,
valid_sp sp -> valid_brk replysegs0 brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
srealizes replysegs0
(init_config replysegs0 Asan.M.init_pc Asan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
(SPECX (LS:=checksum_shape) inp).
Definition replysegsB : list Segment := AsanUbsan.M.loaded_segments.
Definition TFIB_B_T : Prop :=
forall sp brk mbase rnd inp,
valid_sp sp -> valid_brk replysegsB brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
srealizes replysegsB
(init_config replysegsB AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
(SPECX (LS:=checksum_shape) inp).
