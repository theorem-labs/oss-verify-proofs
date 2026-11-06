(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from the TFIB_T definition of proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v (through a Theorem Labs lane's proofs/libreac/fuzz_grant/lib/A/GrantTFIB.v, a working branch 0bed23e5b69) for fuzz_ctrl's ASan image and its agreement shape ag_shape checksum_shape; module paths changed. *)
(* What the ASan side of fuzz_ctrl's two ASan statements proves: from every valid start, the ASan build realizes
   the same trace set SPECX as the plain build (lib/Reusable/YK18.v srealizes, no cut). *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_ctrl.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK15 YK18 YM05 YO09 YO06.
Require Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.ZTraceSpec.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import AgreeShape.
Import ListNotations.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.
Definition ctrlsegs0 : list Segment := Asan.M.loaded_segments.
Definition TFIB_T : Prop :=
forall sp brk mbase rnd inp,
valid_sp sp -> valid_brk ctrlsegs0 brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
srealizes ctrlsegs0
(init_config ctrlsegs0 Asan.M.init_pc Asan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
(SPECX (LS:=ag_shape checksum_shape) inp).
