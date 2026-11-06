(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: extracted from proofs/cgif/cgif_file_fuzzer/lib/A/AB1v.v at c8557374ad2e, with its module paths changed and the image module of libreac/fuzz_knock's ASan build in place of cgif's: lines 1-11 are taken; lines 12-21 (cgif's musl text and exit-guard code table tfibmusl_*/tfibguard_*, start-up content) are left out. tfibsegs is the image of knock's pinned asan binary (sha256 61768cf4739b...). *)
(* Modified by Theorem Labs, 2026-10: copied from projects/libreac/fuzz_knock/proofs/lib/A/AWalkFw0.v (donor image sha256 61768cf4739b), with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: derived from lib/A/AWalkFw0.v of this library by derive_y.py: module names A.Axyz -> AU.Yxyz, addresses moved from libdiginet/fuzz_codec's asan image to its asan-ubsan image. The Modified-by lines above describe how lib/A/AWalkFw0.v was made and quote that file's asan-image values; the code below carries the asan-ubsan values. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP02.
From OSSVerify.libdiginet.fuzz_codec.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibsegs : list Segment := AsanUbsan.M.loaded_segments.
