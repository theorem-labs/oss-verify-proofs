(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from the TFIB_T definition of proofs/cgif/cgif_file_fuzzer/lib/YZ03.v:20-26
   (the donor's asan-ubsan image; its lib/A/AZ03.v twin is the asan one) for fuzz_preset's asan-ubsan image and preset's
   shape (lib/ZTraceSpec.checksum_shape); module paths changed. Twin of lib/A/PresetTFIB.v (a Theorem Labs lane): same name
   pattern, argument order and premise text; only the image differs.
   RULING (a Theorem Labs lane 20:25Z, for all four preset tops): the agrees TFIB takes ONE extra argument, the plain
   no-refusal premise at the agrees budget (Budgets.Asan.lim_source, 2 GiB), which the statement grants and the top
   passes. Reason: cgif's TFIB_T has no budget premise and program-constant room premises (cgif YCfn.v:21-22, 38), so
   for preset it would be false on accepted inputs that fill an ASan size class. *)
(* What the asan-ubsan side of fuzz_preset's asan_ubsan_agrees proves: from every valid start whose plain run is never
   refused at the agrees budget, the asan-ubsan build realizes the same trace set SPECX as the plain build
   (lib/Reusable/YK18.v srealizes, no cut). *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.omx_clap_core.fuzz_preset Require Images.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK15 YK18 YM05 YO09 YO06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require ZTraceSpec.
Import ListNotations.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.
Definition presetsegsAU : list Segment := AsanUbsan.M.loaded_segments.
Definition TFIB_T_AU : Prop :=
forall sp brk mbase rnd inp (en_p : ExecEntry),
valid_sp sp -> valid_brk presetsegsAU brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
~ run_scfg_budget_refused Env.alloc_forced_only Images.plain Budgets.Asan.lim_source en_p inp ->
srealizes presetsegsAU
(init_config presetsegsAU AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
(SPECX (LS:=ZTraceSpec.checksum_shape) inp).
