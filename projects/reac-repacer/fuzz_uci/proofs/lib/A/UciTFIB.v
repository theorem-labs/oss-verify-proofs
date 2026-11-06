(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from the TFIB_T definition of proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v for fuzz_decode's ASan image (TFIB_T) and ASan+UBSan image (TFIB_TB, the form of cgif_file's lib/Halts_tfib.v image) and decode_shape; module paths changed. *)
(* Modified by Theorem Labs: made from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/A/DecodeTFIB.v for reac-repacer/fuzz_uci's ASan image only (TFIB_TB dropped: image B is lib/B's); the library shape is fuzz_uci's own checksum_shape (lib/ZTraceSpec.v), the instance the image-A core states its driver theorem at (lib/A/AD1q.v), in place of decode_shape; module paths changed. *)
(* What the ASan side of fuzz_uci's ASan statements proves: from every valid start, the ASan build realizes the same
   trace set SPECX as the plain build (lib/Reusable/YK18.v srealizes, no cut). *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.reac_repacer.fuzz_uci.images Require Asan.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK11 YK15 YK18 YM05 YO09 YO06.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib Require Import ZTraceSpec.
Import ListNotations.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.
Module UAs := OSSVerify.reac_repacer.fuzz_uci.images.Asan.
Definition ucisegs0 : list Segment := UAs.M.loaded_segments.
Definition TFIB_T : Prop :=
forall sp brk mbase rnd inp,
valid_sp sp -> valid_brk ucisegs0 brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
srealizes ucisegs0
(init_config ucisegs0 UAs.M.init_pc UAs.M.phdrs sp brk mbase rnd target_alloc_limit inp)
(SPECX (LS:=checksum_shape) inp).
