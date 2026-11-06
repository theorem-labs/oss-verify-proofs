(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from the TFIB_T definition of proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v for fuzz_boxreg's ASan image (TFIB_T) and ASan+UBSan image (TFIB_TB, the form of cgif_file's lib/YZ03.v and lib/Halts_tfib.v image; the text of fuzz_decode's lib/A/DecodeTFIB.v TFIB_TB, a working branch 21b040f5808, with its unit names changed) and box_shape; module paths changed. *)
(* What the ASan side of fuzz_boxreg's ASan statements proves: from every valid start, the ASan build realizes
   the same trace set SPECX as the plain build (lib/Reusable/YK18.v srealizes, no cut). TFIB_TB is the same for the
   ASan+UBSan build, the side of the two asan_ubsan statements. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_boxreg.images Require Asan AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK15 YK18 YM05 YO09 YO06.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require Import BoxShape.
Import ListNotations.
#[local] Existing Instance OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable.YK11.fx0.
Open Scope Z_scope.
Definition boxsegs0 : list Segment := OSSVerify.libreac.fuzz_boxreg.images.Asan.M.loaded_segments.
Definition TFIB_T : Prop :=
forall sp brk mbase rnd inp,
valid_sp sp -> valid_brk boxsegs0 brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
srealizes boxsegs0
(init_config boxsegs0 OSSVerify.libreac.fuzz_boxreg.images.Asan.M.init_pc
  OSSVerify.libreac.fuzz_boxreg.images.Asan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
(SPECX (LS:=box_shape) inp).
Definition boxsegsB0 : list Segment := OSSVerify.libreac.fuzz_boxreg.images.AsanUbsan.M.loaded_segments.
Definition TFIB_TB : Prop :=
forall sp brk mbase rnd inp,
valid_sp sp -> valid_brk boxsegsB0 brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
srealizes boxsegsB0
(init_config boxsegsB0 OSSVerify.libreac.fuzz_boxreg.images.AsanUbsan.M.init_pc
  OSSVerify.libreac.fuzz_boxreg.images.AsanUbsan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
(SPECX (LS:=box_shape) inp).
