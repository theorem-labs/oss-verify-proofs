(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Image.
Require OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PlainU0.PImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module U := OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PlainU0.PImg.

Definition usegs : list Segment := U.psegs.
Definition u_init_pc : N := U.p_init_pc.
Definition u_phdrs : PhdrInfo := U.p_phdrs.
Definition ubsan_reserved : list (Z * Z) := U.plain_reserved.
Definition UREAD_STAGE : Z := U.PREAD_STAGE.

Lemma reservedZ_ubsan : reservedZ usegs = ubsan_reserved.
Proof. exact U.reservedZ_plain. Qed.
Lemma segments_reserved_ubsan :
  segments_reserved usegs =
  [(Z_to_bv 64 0x10000, Z_to_bv 64 0x4000); (Z_to_bv 64 0x14000, Z_to_bv 64 0xe000);
   (Z_to_bv 64 0x22000, Z_to_bv 64 0x1000); (Z_to_bv 64 0x23000, Z_to_bv 64 0x72000)].
Proof. exact U.segments_reserved_plain. Qed.
Lemma reserved_top_ubsan : reserved_top (segments_reserved usegs) = 0x95000.
Proof. exact U.reserved_top_plain. Qed.
