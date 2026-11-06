(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from the TFIB_T definition of proofs/cgif/cgif_file_fuzzer/lib/YZ03.v (the asan-ubsan twin of lib/A/AZ03.v; through a Theorem Labs lane's proofs/libreac/fuzz_grant/lib/A/GrantTFIB.v, a working branch 0bed23e5b69, and its fuzz_ctrl image-A twin lib/A/CtrlTFIB.v) for fuzz_ctrl's ASan+UBSan image and its agreement shape ag_shape checksum_shape; module paths changed. *)
(* What the ASan+UBSan side of fuzz_ctrl's two ASan+UBSan statements proves: from every valid start, the ASan+UBSan build realizes
   the same trace set SPECX as the plain build (lib/Reusable/YK18.v srealizes, no cut). *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_ctrl.images Require Import AsanUbsan.



Require Import
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK15
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK18
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO06.
Require Import
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.ZTraceSpec
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.AgreeShape.
Import ListNotations.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.
Definition ctrlsegs0_b : list Segment := AsanUbsan.M.loaded_segments.
Definition TFIB_T_B : Prop :=
forall sp brk mbase rnd inp,
valid_sp sp -> valid_brk ctrlsegs0_b brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
srealizes ctrlsegs0_b
(init_config ctrlsegs0_b AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
(SPECX (LS:=ag_shape checksum_shape) inp).
