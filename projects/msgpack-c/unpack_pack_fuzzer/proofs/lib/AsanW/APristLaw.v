(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AProto ABase AMalloc_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition aprist (st : astate) : Prop :=
  forall c, 1 <= c < 32 -> c <> 24 -> c_allocated_user (get_cls st c) = 0 /\ c_mapped_user (get_cls st c) = 0.

Definition prist_det_law (AH : alayout -> footprint -> astate -> list ablock -> amem -> Prop) : Prop :=
  forall L RNG st LB m L' RNG' st' LB' m', AH L RNG st LB m -> AH L' RNG' st' LB' m' ->
    (forall a, (0 <= a < AIMG_HI \/ 0x10007fff8000 <= a < 2^47) -> m' (wa a) = m (wa a)) ->
    aprist st -> aprist st'.

Module TwinB.
Import stdpp.gmap.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition aprist (st : astate) : Prop :=
  forall c, 1 <= c < 32 -> c <> 24 -> c_allocated_user (get_cls st c) = 0 /\ c_mapped_user (get_cls st c) = 0.

Definition prist_det_law (AH : alayout -> footprint -> astate -> list ablock -> amem -> Prop) : Prop :=
  forall L RNG st LB m L' RNG' st' LB' m', AH L RNG st LB m -> AH L' RNG' st' LB' m' ->
    (forall a, (0 <= a < AIMG_HI \/ 0x10007fff8000 <= a < 2^47) -> m' (wa a) = m (wa a)) ->
    aprist st -> aprist st'.
End TwinB.
