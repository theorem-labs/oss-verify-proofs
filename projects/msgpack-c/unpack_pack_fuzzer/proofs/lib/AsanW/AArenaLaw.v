(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AProto ABase AMalloc_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition arena_law (AH : alayout -> footprint -> astate -> list ablock -> amem -> Prop) : Prop :=
  forall L RNG st LB m p A n, AH L RNG st LB m -> In (HB p A n) LB -> is_primary n = true ->
    exists c, 1 <= c <= 31
      /\ al_space_beg L + c * K_REGION <= A
      /\ A + n <= al_space_beg L + c * K_REGION + c_allocated_user (get_cls st c).

Module TwinB.
Import stdpp.gmap.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition arena_law (AH : alayout -> footprint -> astate -> list ablock -> amem -> Prop) : Prop :=
  forall L RNG st LB m p A n, AH L RNG st LB m -> In (HB p A n) LB -> is_primary n = true ->
    exists c, 1 <= c <= 31
      /\ al_space_beg L + c * K_REGION <= A
      /\ A + n <= al_space_beg L + c * K_REGION + c_allocated_user (get_cls st c).
End TwinB.
