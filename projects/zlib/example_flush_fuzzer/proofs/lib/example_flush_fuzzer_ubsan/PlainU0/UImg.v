(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Lib Require Import PropExec MState Mem Image.
Require OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PlainU0.PImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* kitfix4 alias stage: Module U := OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PlainU0.PImg expanded *)

Definition usegs : list Segment := OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PlainU0.PImg.psegs.
Definition u_init_pc : N := OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PlainU0.PImg.p_init_pc.
Definition u_phdrs : PhdrInfo := OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PlainU0.PImg.p_phdrs.
Definition UREAD_STAGE : Z := OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PlainU0.PImg.PREAD_STAGE.

Lemma segments_reserved_ubsan :
  segments_reserved usegs =
  [(Z_to_bv 64 0x10000, Z_to_bv 64 0x5000); (Z_to_bv 64 0x15000, Z_to_bv 64 0x17000); (Z_to_bv 64 0x2c000, Z_to_bv 64 0x1000); (Z_to_bv 64 0x2d000, Z_to_bv 64 0x32000)].
Proof. exact OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PlainU0.PImg.segments_reserved_plain. Qed.
Lemma reserved_top_ubsan : reserved_top (segments_reserved usegs) = 0x5f000.
Proof. exact OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PlainU0.PImg.reserved_top_plain. Qed.
