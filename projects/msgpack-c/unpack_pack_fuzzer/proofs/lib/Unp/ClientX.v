(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem State MemProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv OpsBridge TdOps PkOps.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem St MemP HeapOp UB.
Open Scope Z_scope.
Unset Lia Cache.

Module CX.
Section WithSegs.
Variable segs : list Segment.

Definition x_holds (md : Z) (ca : list word) (LB : blocks) (ws : list window) (m : word -> option byte) : Prop :=
  if md =? TD.CM_TD then TD.td_client segs ca LB ws m
  else if md =? PK.CM_PK then PK.cw_pk_holds segs ca LB ws m
  else False.

Lemma x_frame : forall md ca LB ws m m', x_holds md ca LB ws m ->
  (forall a, 0 <= a < two64 -> in_user LB a -> ~ in_ws (heap_ws ws) a -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  x_holds md ca LB ws m'.
Proof.
  intros md ca LB ws m m' H FR. unfold x_holds in *.
  destruct (md =? TD.CM_TD); [exact (TD.td_frame segs ca LB ws m m' H FR)|].
  destruct (md =? PK.CM_PK); [exact (PK.cw_pk_frame segs ca LB ws m m' H FR)| exact H].
Qed.
Lemma x_grow : forall md ca LB ws m b n, x_holds md ca LB ws m ->
  (forall a, in_iv (b, n) a -> ~ in_user LB a) ->
  x_holds md ca ((b, n) :: LB) (ws ++ [Win b n K_BLOCK]) m.
Proof.
  intros md ca LB ws m b n H FR. unfold x_holds in *.
  destruct (md =? TD.CM_TD); [exact (TD.td_grow segs ca LB ws m b n H FR)|].
  destruct (md =? PK.CM_PK); [exact (PK.cw_pk_grow segs ca LB ws m b n H FR)| exact H].
Qed.
Lemma x_free : forall md ca LB ws m b n ws', x_holds md ca LB ws m -> In (Win b n K_BLOCK) ws ->
  (forall w, In w ws' <-> In w ws /\ w <> Win b n K_BLOCK) ->
  x_holds md ca (remove iv_eq_dec (b, n) LB) ws' m.
Proof.
  intros md ca LB ws m b n ws' H Hin Hws'. unfold x_holds in *.
  destruct (md =? TD.CM_TD); [exact (TD.td_free segs ca LB ws m b n ws' H Hin Hws')|].
  destruct (md =? PK.CM_PK); [exact (PK.cw_pk_free segs ca LB ws m b n ws' H Hin Hws')| exact H].
Qed.

Definition XTP : client_world := CW x_holds x_frame x_grow x_free.

End WithSegs.
End CX.
