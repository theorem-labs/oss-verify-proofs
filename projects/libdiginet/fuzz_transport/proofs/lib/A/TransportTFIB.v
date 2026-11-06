(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from the TFIB_T definition of proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v for fuzz_decode's ASan image (TFIB_T) and ASan+UBSan image (TFIB_TB, the form of cgif_file's lib/Halts_tfib.v image) and decode_shape; module paths changed. *)
(* What the ASan side of fuzz_decode's ASan statements proves: from every valid start, the ASan build realizes
   the same trace set SPECX as the plain build (lib/Reusable/YK18.v srealizes, no cut). TFIB_TB is the same for the
   ASan+UBSan build, the side of the two asan_ubsan statements. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libdiginet.fuzz_transport.images Require Asan.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK15 YK18 YM05 YO09 YO06.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import TransportShape.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AB1v.
Import ListNotations.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.
Module TAs := OSSVerify.libdiginet.fuzz_transport.images.Asan.
Definition TFIB_T : Prop :=
forall sp brk mbase rnd inp,
valid_sp sp -> valid_brk AB1v.tfibsegs brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
srealizes AB1v.tfibsegs
(init_config AB1v.tfibsegs TAs.M.init_pc TAs.M.phdrs sp brk mbase rnd target_alloc_limit inp)
(SPECX (LS:=transport_shape) inp).
