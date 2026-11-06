(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List.
From Stdlib Require Import PrimInt63 Uint63.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface AMalloc_iface2 AInstanceU AInstanceUF AInstanceU2 AInstanceU2F.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.W2 Require ExhFirst.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_sm0. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_sm0. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_sm0.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Op FakeLaw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import SmWorld SmSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Notation AIu2 := (AInstanceU2.AIu2 ExhFirst.exh_first).
Local Notation AIu_fake := (FakeLaw.AIu_fake ExhFirst.exh_first).
Section Inst.
Context {rc : runConstT}.
Lemma sm_walk_0 : sm_walk_stmt AIu2 AIu_fake (to_Z 0%uint63) (fsize (to_Z 0%uint63)) 16384 AFake_sm0.AFake_sm0.ASTKMALLOC0.
Proof. exact AHU2_stack_malloc_0. Qed.
Lemma sm_walk_1 : sm_walk_stmt AIu2 AIu_fake (to_Z 1%uint63) (fsize (to_Z 1%uint63)) 8192 AFake_sm0.AFake_sm1g.ASTKMALLOC1.
Proof. exact AHU2_stack_malloc_1. Qed.
Lemma sm_walk_2 : sm_walk_stmt AIu2 AIu_fake (to_Z 2%uint63) (fsize (to_Z 2%uint63)) 4096 AFake_sm0.AFake_sm2.ASTKMALLOC2.
Proof. exact AHU2_stack_malloc_2. Qed.
End Inst.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB AMalloc_iface2.TwinB AInstanceU.TwinB AInstanceUF.TwinB AInstanceU2.TwinB AInstanceU2F.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import Op.TwinB FakeLaw.TwinB.
Import SmWorld.TwinB SmSound.TwinB.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Notation AIu2 := (AInstanceU2.TwinB.AIu2 ExhFirst.TwinB.exh_first).
Local Notation AIu_fake := (FakeLaw.TwinB.AIu_fake ExhFirst.TwinB.exh_first).
Section Inst.
Context {rc : runConstT}.
Lemma sm_walk_0 : sm_walk_stmt AIu2 AIu_fake (to_Z 0%uint63) (fsize (to_Z 0%uint63)) 16384 AFake_sm0.TwinB.AFake_sm0.ASTKMALLOC0.
Proof. exact AHU2_stack_malloc_0. Qed.
Lemma sm_walk_1 : sm_walk_stmt AIu2 AIu_fake (to_Z 1%uint63) (fsize (to_Z 1%uint63)) 8192 AFake_sm0.TwinB.AFake_sm1g.ASTKMALLOC1.
Proof. exact AHU2_stack_malloc_1. Qed.
Lemma sm_walk_2 : sm_walk_stmt AIu2 AIu_fake (to_Z 2%uint63) (fsize (to_Z 2%uint63)) 4096 AFake_sm0.TwinB.AFake_sm2.ASTKMALLOC2.
Proof. exact AHU2_stack_malloc_2. Qed.
End Inst.

End TwinB.
