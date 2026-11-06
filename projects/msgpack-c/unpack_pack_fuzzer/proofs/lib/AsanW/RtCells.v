(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Lemma no_image_asan : forall s1 s2, 0x62f000 <= s1 -> no_image asegs s1 s2.
Proof. intros s1 s2 H z Hz. apply ref_find_segment_none; lia. Qed.

End CANSEC1.
Notation rt_got m :=
  (rw_cells asegs m 0xd1508 [C8 (Z_to_bv 64 0x16b5e8); C8 (Z_to_bv 64 0xd72b8); C8 (Z_to_bv 64 0xd9ab8);
                              C8 (Z_to_bv 64 0xda7a8); C8 (Z_to_bv 64 0xda7b0); C8 (Z_to_bv 64 0xda7a0)]).

Notation rt_got_ric m := (rw_cells asegs m 0xd2080 [C8 (Z_to_bv 64 0xda799)]).

Notation rt_shbase m := (rw_cells asegs m 0xd9ab8 [C8 (Z_to_bv 64 0x7fff8000)]).

Notation rt_inited m := (rw_cells asegs m 0xda798 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]).

Notation rt_layout m := (rw_cells asegs m 0xda7a0 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).

Notation rt_real_mem m := (rw_cells asegs m 0xd3420 [C8 (Z_to_bv 64 0xc74a0); C8 (Z_to_bv 64 0xc78a4)]).
Notation rt_real_wcslen m := (rw_cells asegs m 0xd33b0 [C8 (Z_to_bv 64 0xc2aa0)]).
Notation rt_real_read m := (rw_cells asegs m 0xd32f0 [C8 (Z_to_bv 64 0xccba4)]).
Notation rt_real_printf m := (rw_cells asegs m 0xd3310 [C8 (Z_to_bv 64 0xc6dec); C8 (Z_to_bv 64 0xc3cdc)]).

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Lemma no_image_asan : forall s1 s2, 0x631000 <= s1 -> no_image bsegs s1 s2.
Proof. intros s1 s2 H z Hz. apply ref_find_segment_none; lia. Qed.

End CANSEC1.
Notation rt_got m :=
  (rw_cells bsegs m 0xd3620 [C8 (Z_to_bv 64 0x16d7a8); C8 (Z_to_bv 64 0xd9478); C8 (Z_to_bv 64 0xdbc78);
                              C8 (Z_to_bv 64 0xdc968); C8 (Z_to_bv 64 0xdc970); C8 (Z_to_bv 64 0xdc960)]).

Notation rt_got_ric m := (rw_cells bsegs m 0xd4198 [C8 (Z_to_bv 64 0xdc959)]).

Notation rt_shbase m := (rw_cells bsegs m 0xdbc78 [C8 (Z_to_bv 64 0x7fff8000)]).

Notation rt_inited m := (rw_cells bsegs m 0xdc958 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]).

Notation rt_layout m := (rw_cells bsegs m 0xdc960 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).

Notation rt_real_mem m := (rw_cells bsegs m 0xd5538 [C8 (Z_to_bv 64 0xc95bc); C8 (Z_to_bv 64 0xc99c0)]).
Notation rt_real_wcslen m := (rw_cells bsegs m 0xd54c8 [C8 (Z_to_bv 64 0xc4bbc)]).
Notation rt_real_read m := (rw_cells bsegs m 0xd5408 [C8 (Z_to_bv 64 0xcecc0)]).
Notation rt_real_printf m := (rw_cells bsegs m 0xd5428 [C8 (Z_to_bv 64 0xc8f08); C8 (Z_to_bv 64 0xc5df8)]).
End TwinB.
