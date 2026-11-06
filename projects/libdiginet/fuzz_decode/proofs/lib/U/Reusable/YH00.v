(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: replaces the definitions of proofs/cgif/cgif_file_fuzzer/lib/YH00.v with aliases, under the same names, of those in ZImage.v. *)
(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/U/Reusable/YH00.v at bf7779f81ed764787b77895d2f5c0db2627f33f3 for libdiginet/fuzz_decode; no image value changed; module path OSSVerify.Proofs.libdiginet.fuzz_decode.lib. *)
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import ZImage.
Definition src0segs := zsegs.
Definition src0text_start := ztext_start.
Definition src0text_count := ztext_count.
Definition src0tbl := ztbl.
Definition src0tbl_eq := ztbl_eq.
Definition src0tbl_ok := ztbl_ok.
