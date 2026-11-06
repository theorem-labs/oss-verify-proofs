(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: extracted from proofs/cgif/cgif_file_fuzzer/lib/A/AB1v.v at c8557374ad2e, with its module paths changed and the image module of libreac/fuzz_knock's ASan build in place of cgif's: lines 1-11 are taken; lines 12-21 (cgif's musl text and exit-guard code table tfibmusl_*/tfibguard_*, start-up content) are left out. tfibsegs is the image of knock's pinned asan binary (sha256 61768cf4739b...). *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/A/AWalkFw0.v (donor image sha256 61768cf4739b), with its module paths changed. *)
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YP02.
From OSSVerify.reac_pw.fuzz_qdisc.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibsegs : list Segment := Asan.M.loaded_segments.
