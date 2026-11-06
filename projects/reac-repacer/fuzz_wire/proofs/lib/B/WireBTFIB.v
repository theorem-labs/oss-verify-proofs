(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: copied from proofs/libreac/fuzz_decode/lib/B/DecodeTFIB.v at recipes commit 88154566652a (a
   recipes commit newer than the unit's base 25e3d17bdb50) for reac-repacer/fuzz_uci's ASan+UBSan image, at fuzz_uci's
   library shape checksum_shape (lib/ZTraceSpec.v), the shape of the B core's closed walk lib/B/YD1q.v; module paths and
   names changed. *)
(* What the ASan+UBSan side of fuzz_wire's two asan_ubsan statements proves: from every valid start, the ASan+UBSan build
   realizes the plain build's trace set SPECX (lib/Reusable/YK18.v srealizes, no cut). *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.reac_repacer.fuzz_wire.images Require AsanUbsan.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK15 YK18 YM05 YO09 YO06.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib Require Import ZTraceSpec.
Import ListNotations.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.
Module UAU := OSSVerify.reac_repacer.fuzz_wire.images.AsanUbsan.
Definition wiresegsB0 : list Segment := UAU.M.loaded_segments.
Definition TFIB_T : Prop :=
forall sp brk mbase rnd inp,
valid_sp sp -> valid_brk wiresegsB0 brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
srealizes wiresegsB0
(init_config wiresegsB0 UAU.M.init_pc UAU.M.phdrs sp brk mbase rnd target_alloc_limit inp)
(SPECX (LS:=checksum_shape) inp).
