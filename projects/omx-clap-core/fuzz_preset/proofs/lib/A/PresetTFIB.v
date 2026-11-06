(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from the TFIB_T definition of proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v for fuzz_preset's ASan image and checksum_shape (lib/ZTraceSpec.v, the library shape of fuzz_preset's ubsan agreement), with one more premise (below); module paths changed. *)
(* What the ASan side of fuzz_preset's ASan agreement proves: from every valid start, the ASan build realizes the
   same trace set SPECX as the plain build (lib/Reusable/YK18.v srealizes, no cut), on every input on which the plain
   build is never refused memory at the agreement's plain budget.
   That last premise is not in cgif's TFIB_T. cgif's TFIB_T has no budget premise and its room premises are program
   constants, so for fuzz_preset it would be false on accepted inputs that fill a size class. The agreement
   statement (Statements.asan_agrees) already grants the plain no-refusal premise, so TFIB_T carries it (unit owner's
   ruling, 2026-10-28 20:25Z). *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.omx_clap_core.fuzz_preset Require Images.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK15 YK18 YM05 YO09 YO06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require ZTraceSpec.
Import ListNotations.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.
Definition presetsegs0 : list Segment := Asan.M.loaded_segments.
Definition TFIB_T : Prop :=
forall sp brk mbase rnd inp (en_p : ExecEntry),
valid_sp sp -> valid_brk presetsegs0 brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
~ run_scfg_budget_refused Env.alloc_forced_only Images.plain Budgets.Asan.lim_source en_p inp ->
srealizes presetsegs0
(init_config presetsegs0 Asan.M.init_pc Asan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
(SPECX (LS:=ZTraceSpec.checksum_shape) inp).
