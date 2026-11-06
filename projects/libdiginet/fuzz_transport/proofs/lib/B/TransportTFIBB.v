(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from the TFIB_T definition of proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v for fuzz_decode's ASan image (TFIB_T) and ASan+UBSan image (TFIB_TB, the form of cgif_file's lib/Halts_tfib.v image) and decode_shape; module paths changed. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/libreac/fuzz_decode/lib/B/DecodeTFIB.v at recipes commit 88154566652a
   (itself from the TFIB_T definition of proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v, for the image of cgif_file's
   lib/Halts_tfib.v) for libdiginet/fuzz_frame's ASan+UBSan image and frame_shape (lib/A/FrameShape.v); names and
   module paths changed. *)
(* Modified by Theorem Labs, 2026-10: made from libdiginet/fuzz_frame lib/B/FrameTFIB.v (file sha256 5c0bcdd354f8;
   donor not released) for libdiginet/fuzz_transport's ASan+UBSan image (fuzz_transport.asan-ubsan 41113a03c82f) and
   transport_shape (lib/A/TransportShape.v); names and module paths changed. *)
(* What the ASan+UBSan side of fuzz_transport's two ASan+UBSan statements proves: from every valid start, the
   ASan+UBSan build realizes the same trace set SPECX as the plain build (lib/Reusable/YK18.v srealizes, no cut).
   lib/A/TransportTFIB.v TFIB_T is the same proposition over the ASan image. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libdiginet.fuzz_transport.images Require AsanUbsan.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK15 YK18 YM05 YO09 YO06.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import TransportShape.
Import ListNotations.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.
Module TAU := OSSVerify.libdiginet.fuzz_transport.images.AsanUbsan.
Definition transportsegsB0 : list Segment := TAU.M.loaded_segments.
Definition TFIB_TB : Prop :=
forall sp brk mbase rnd inp,
valid_sp sp -> valid_brk transportsegsB0 brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
srealizes transportsegsB0
(init_config transportsegsB0 TAU.M.init_pc TAU.M.phdrs sp brk mbase rnd target_alloc_limit inp)
(SPECX (LS:=transport_shape) inp).
