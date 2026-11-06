(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: made from the TFIB_T definition of proofs/cgif/cgif_file_fuzzer/lib/YZ03.v for fuzz_command's ASan+UBSan image and cmd_shape (lib/A/CmdShape.v); names and module paths changed, comment added. *)
(* What the ASan+UBSan side of fuzz_command's two ASan+UBSan statements proves: from every valid start, the
   ASan+UBSan build realizes the same trace set SPECX as the plain build (lib/Reusable/YK18.v srealizes, no cut). *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.plugin_hostd.fuzz_command.images Require Import AsanUbsan.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK15 YK18 YM05 YO09 YO06.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import CmdShape.
Import ListNotations.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.
Definition cmdsegsB : list Segment := AsanUbsan.M.loaded_segments.
Definition TFIB_T_B : Prop :=
forall sp brk mbase rnd inp,
valid_sp sp -> valid_brk cmdsegsB brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
srealizes cmdsegsB
(init_config cmdsegsB AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
(SPECX (LS:=cmd_shape) inp).
