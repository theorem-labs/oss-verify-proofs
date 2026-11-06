(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AE37.v for plugin-hostd/fuzz_command: cgif's walk of the ASan module destructor (asan.module_dtor at X2_PC: unregistering cgif's 3 asan_globals descriptors, unrolled over cgif's data) does not carry over to fuzz_command's 180 descriptors, so its contract x2_realizes, with cgif's statement, is a named hypothesis (class DtorExit) until a walk over fuzz_command's descriptors discharges it. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/AE37.v (donor image sha256 c0661b96b5bd), with its module paths changed, names CmdBSyms -> SegBSyms and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AB1v AF0m AF0x AE3h AE23.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
Open Scope Z_scope.
(* cgif A/AE37.v:185 Theorem x2_realizes (in its Sections d (fx, rc) and S (B, TB : TfibSyms B, MU0)). *)
Class DtorExit : Prop := x2_realizes : forall {fx : YK11.FPState} {rc : YM05.RunCeil} (B : asyms), SegBSyms B ->
(forall ly, cell_lookup (Tfib_const ly) (ANum 0xa98b0) = Some (ACell (ANum 0xa98b0) 8 (AV (ANum 0)))) ->
xret_realizes_noar tfibsegs B X2_PC XW2 XTRUE.
