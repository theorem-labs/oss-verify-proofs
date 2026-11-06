(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from the TFIB_T definition of proofs/cgif/cgif_file_fuzzer/lib/YZ03.v (cgif_file's ASan+UBSan image) for fuzz_grant's ASan+UBSan image and grant_shape, as fuzz_decode's lib/A/DecodeTFIB.v states its TFIB_TB; module paths changed. *)
(* Modified by Theorem Labs, 2026-10: moved from lib/A/GrantTFIBB.v (a working branch b01a93fbf7f) to lib/B, so that lib/A stays grant image A's accepted tree; module path lib.A -> lib.B. *)
(* What the ASan+UBSan side of fuzz_grant's two asan_ubsan statements proves: from every valid start, the ASan+UBSan
   build realizes the same trace set SPECX as the plain build (lib/Reusable/YK18.v srealizes, no cut). It is
   GrantTFIB.v's TFIB_T for the image AsanUbsan in place of Asan. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_grant.images Require AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK15 YK18 YM05 YO09 YO06.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A Require Import GrantShape.
Import ListNotations.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.
Definition grantsegsB0 : list Segment := AsanUbsan.M.loaded_segments.
Definition TFIB_TB : Prop :=
forall sp brk mbase rnd inp,
valid_sp sp -> valid_brk grantsegsB0 brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
srealizes grantsegsB0
(init_config grantsegsB0 AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
(SPECX (LS:=grant_shape) inp).
