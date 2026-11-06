(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AE37.v for plugin-hostd/fuzz_command: cgif's walk of the ASan module destructor (asan.module_dtor at X2_PC: unregistering cgif's 3 asan_globals descriptors, unrolled over cgif's data) does not carry over to fuzz_command's 180 descriptors, so its contract x2_realizes, with cgif's statement, is a named hypothesis (class DtorExit) until a walk over fuzz_command's descriptors discharges it. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/AE37.v (donor image sha256 c0661b96b5bd), with its module paths changed, names CmdBSyms -> SegBSyms and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/AE37.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1v YF0m YF0x YE3h YE23.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
Open Scope Z_scope.
(* cgif A/AE37.v:185 Theorem x2_realizes (in its Sections d (fx, rc) and S (B, TB : TfibSyms B, MU0)). *)
Class DtorExit : Prop := x2_realizes : forall {fx : YK11.FPState} {rc : YM05.RunCeil} (B : asyms), SegBSyms B ->
(forall ly, cell_lookup (Tfib_const ly) (ANum 0xaa070) = Some (ACell (ANum 0xaa070) 8 (AV (ANum 0)))) ->
xret_realizes_noar tfibsegs B X2_PC XW2 XTRUE.
