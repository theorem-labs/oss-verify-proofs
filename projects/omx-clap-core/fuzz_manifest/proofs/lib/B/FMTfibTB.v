(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from the TFIB_T definition of proofs/cgif/cgif_file_fuzzer/lib/YZ03.v:19-26, by way of proofs/libreac/fuzz_grant/lib/A/GrantTFIB.v (cold/port-grant 0bed23e5b69), for fuzz_preset's asan image: TFIB_T takes any trace set whose exits are 0 or 2, which is all that halts_budgets_of_srealizes (Reusable/HaltsKitB.v) asks; cgif's form, with the trace set SPECX at fuzz_preset's checksum_shape (lib/ZTraceSpec.v), is TFIB_T_specx and gives TFIB_T; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/HaltsTFIB.v; 9 of its 15 lines of code are new or changed and 30 lines of the source are left out. *)
(* The ASan side of fuzz_manifest's asan_ubsan_agrees and asan_ubsan_halts, as one statement: the image-B
   (ASan+UBSan build) twin of lib/A/FMTfibT.v TFIB_T. Every run of fm.asan-ubsan from a valid entry on a valid input,
   at the target budget, realizes the trace set SPECX of fm's plain proof without cuts (YK18.srealizes), at the same
   library shape checksum_shape (ZTraceSpec.v). The composition (lib/B/FMTopB.v) proves Statements.asan_ubsan_agrees
   and Statements.asan_ubsan_halts from TFIB_TB; the image-B core (cgif_file_fuzzer's root Y* asan-ubsan files,
   relocated onto fm.asan-ubsan) proves TFIB_TB. Form: proofs/libreac/fuzz_decode/lib/A/DecodeTFIB.v TFIB_TB
   (a working branch 21b040f5808), the unit copy of cgif_file_fuzzer lib/YZ03.v's image. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.omx_clap_core.fuzz_manifest.images Require AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK15 YK18 YO09 YO06.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest Require Import lib.ZTraceSpec.
#[local] Existing Instance YK11.fx0.

Definition tfibsegsB0 : list Segment := AsanUbsan.M.loaded_segments.

Definition TFIB_TB : Prop :=
  forall sp brk mbase rnd inp,
    valid_sp sp -> valid_brk tfibsegsB0 brk -> valid_mmap_base mbase ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
    srealizes tfibsegsB0
      (init_config tfibsegsB0 AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
      (SPECX (LS:=checksum_shape) inp).
