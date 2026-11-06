(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require PlainClosed PC_closed.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require UbsanClosed PC_closed.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require AMain_final.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require NUMA_W.

Definition plain_client : OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain.PlainClosed.plain_client_stmt :=
  OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain.PC_closed.plain_client_closed.
Definition ubsan_client : OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan.UbsanClosed.ubsan_client_stmt :=
  OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan.PC_closed.ubsan_client_closed.
Definition asan_client : OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW.AMain_final.asan_client_stmt :=
  fun rc => @OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN.NUMA_W.fuzz_closedW rc.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require AMain_final.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require NUMB_W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition both_client : OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW.AMain_final.asan_client_stmt :=
  fun rc => @OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN.NUMB_W.fuzz_closedW rc.
