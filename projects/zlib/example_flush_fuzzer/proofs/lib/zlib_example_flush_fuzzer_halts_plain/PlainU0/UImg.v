(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Lib Require Import PropExec MState Mem Image.
Require OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PlainU0.PImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module U := OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PlainU0.PImg.

Definition usegs : list Segment := U.psegs.
Definition u_init_pc : N := U.p_init_pc.
Definition u_phdrs : PhdrInfo := U.p_phdrs.
Definition UREAD_STAGE : Z := U.PREAD_STAGE.

Lemma segments_reserved_ubsan :
  segments_reserved usegs =
  [(Z_to_bv 64 0x10000, Z_to_bv 64 0x5000); (Z_to_bv 64 0x15000, Z_to_bv 64 0x17000); (Z_to_bv 64 0x2c000, Z_to_bv 64 0x1000); (Z_to_bv 64 0x2d000, Z_to_bv 64 0x32000)].
Proof. exact U.segments_reserved_plain. Qed.
Lemma reserved_top_ubsan : reserved_top (segments_reserved usegs) = 0x5f000.
Proof. exact U.reserved_top_plain. Qed.
