(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require BvKH.   (* [comment removed for export] *)
From Stdlib Require Import NArith List String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
Require OSSVerify.double_conversion.string_to_double_fuzzer.images.Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module HX := OSSVerify.double_conversion.string_to_double_fuzzer.images.Ubsan.
Notation ImgU_seg_bytes_000 := HX.Ubsan_seg_bytes_000 (only parsing).
Notation ImgU_segment_000 := HX.Ubsan_segment_000 (only parsing).
Notation ImgU_seg_bytes_001 := HX.Ubsan_seg_bytes_001 (only parsing).
Notation ImgU_segment_001 := HX.Ubsan_segment_001 (only parsing).
Notation ImgU_seg_bytes_002 := HX.Ubsan_seg_bytes_002 (only parsing).
Notation ImgU_segment_002 := HX.Ubsan_segment_002 (only parsing).
Notation ImgU_seg_bytes_003 := HX.Ubsan_seg_bytes_003 (only parsing).
Notation ImgU_segment_003 := HX.Ubsan_segment_003 (only parsing).
Notation ImgU_loaded_segments := HX.Ubsan_loaded_segments (only parsing).
Notation ImgU_init_pc := HX.Ubsan_init_pc (only parsing).
Notation ImgU_phdrs := HX.Ubsan_phdrs (only parsing).
Module M := HX.M.
