(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from the TFIB_T definition of projects/cgif/cgif_file_fuzzer/proofs/lib/YZ03.v for fuzz_identity's ASan+UBSan image and identity_shape, named TFIB_TB; module paths changed. *)
(* What the ASan+UBSan side of fuzz_identity's two ASan+UBSan statements proves: from every valid start, the
   ASan+UBSan build realizes the same trace set SPECX as the plain build (lib/Reusable/YK18.v srealizes, no cut).
   lib/A/IdentityTFIB.v TFIB_T is the same proposition over the ASan image. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_identity.images Require Import AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK15 YK18 YM05 YO09 YO06.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Agree.
(* identity_shape: the library shape of fuzz_identity's ubsan agreement (lib/Prog/Seg/Agree.v checksum_shape_ag). *)
Notation identity_shape := OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg.Agree.checksum_shape_ag (only parsing).
Import ListNotations.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.
Definition identsegsB0 : list Segment := AsanUbsan.M.loaded_segments.
Definition TFIB_TB : Prop :=
forall sp brk mbase rnd inp,
valid_sp sp -> valid_brk identsegsB0 brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
srealizes identsegsB0
(init_config identsegsB0 AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
(SPECX (LS:=identity_shape) inp).
