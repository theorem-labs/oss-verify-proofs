(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: made from the TFIB_T definition of proofs/cgif/cgif_file_fuzzer/lib/YZ03.v for fuzz_command's ASan+UBSan image and cmd_shape (lib/A/CmdShape.v); names and module paths changed, comment added. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/CmdTFIBB.v (origin/ossv/recipes bf33659295b7) for reac-pw/fuzz_segconf's image B (fuzz_segconf.asan-ubsan) as lib/B/SegTFIBB.v: module paths; cmd_shape -> seg_shape (lib/A/SegShape.v), cmdsegsB -> segsegsB. *)
(* What the ASan+UBSan side of segconf's two ASan+UBSan statements proves: from every valid start, the
   ASan+UBSan build realizes the same trace set SPECX as the plain build (lib/Reusable/YK18.v srealizes, no cut). *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.reac_pw.fuzz_segconf.images Require Import AsanUbsan.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK15 YK18 YM05 YO09 YO06.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import SegShape.
Import ListNotations.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.
Definition segsegsB : list Segment := AsanUbsan.M.loaded_segments.
Definition TFIB_T_B : Prop :=
forall sp brk mbase rnd inp,
valid_sp sp -> valid_brk segsegsB brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
srealizes segsegsB
(init_config segsegsB AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
(SPECX (LS:=seg_shape) inp).
