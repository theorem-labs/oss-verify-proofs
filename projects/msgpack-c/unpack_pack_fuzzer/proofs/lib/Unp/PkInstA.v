(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv OpsBridge Ops ClientX GLib Seal PkOps TdOps PkLoad2 PkFld2 OpShLoad.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS HeapOp UB UO UG CX.
Open Scope Z_scope.

Module PkInstA.
Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW (unp_cw segs (XTP segs)) OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Hypothesis HMPA : forall mo acc mo', MP mo -> materialize_model_accesses mo acc = Some mo' -> MP mo'.

Lemma cw3 : forall ca LB ws m, cw_holds (unp_cw segs (XTP segs)) 3 ca LB ws m -> PK.cw_pk_holds segs ca LB ws m.
Proof. intros ca LB ws m H. exact H. Qed.

Theorem pkload2_sound : forall pc, contract_sound segs OPS MP PB (PkLoad2.pkload2_contract segs pc).
Proof. exact (PkLoad2.pkload2_sound segs IMGX AW (unp_cw segs (XTP segs)) OPS HOPS cw3 MP PB HMPA). Qed.
Theorem pkfld2_sound : forall pc, contract_sound segs OPS MP PB (PkFld2.pkfld2_contract segs pc).
Proof. exact (PkFld2.pkfld2_sound segs IMGX AW (unp_cw segs (XTP segs)) OPS HOPS cw3 MP PB HMPA). Qed.

Section ShLoad.
Variable CHS : list oinst -> (word -> option byte) -> Model -> Z -> Prop.
Hypothesis LAWS : forall (os : list oinst) (m : word -> option byte) (mo : Model) (acc : list (word * nat)),
  op_minv OPS mo -> Forall (fun o => op_holds OPS (fst o) (snd o) m mo) os ->
  (forall a n j, In (a, n) acc -> 0 <= j < Z.of_nat n -> CHS os m mo (bv_unsigned a + j)) ->
  exists mo', materialize_model_accesses mo acc = Some mo' /\ op_minv OPS mo' /\
              Forall (fun o => op_holds OPS (fst o) (snd o) m mo') os.
Hypothesis SHLAW : forall os args md aw ws ca LB m mo cs c p,
  In (OPID, args) os -> decode args = Some (md, aw, ws, ca) ->
  aw_holds segs IMGX AW aw LB ws m mo -> windows_wf ws LB (aw_ceiling segs IMGX AW mo) ->
  Seal.seal_ok ws cs -> In c cs -> In (chunk_block c) LB ->
  (forall w, In w ws -> (w_kind w = K_BLOCK \/ K_GHOST <= w_kind w) -> forall a, in_iv (w_iv w) a -> ~ in_iv (chunk_block c) a) ->
  in_iv (chunk_block c) p ->
  m (Z_to_bv 64 (Seal.shadZ p)) = Some (Z_to_bv 8 0) /\ CHS os m mo (Seal.shadZ p).

Theorem opshload_sound : forall pc, contract_sound segs OPS MP PB (OpShLoad.opshload_c segs pc).
Proof.
  intros pc. refine (OpShLoad.opshload_sound segs IMGX AW (unp_cw segs (XTP segs)) OPS HOPS _ _ CHS LAWS SHLAW MP PB HMPA pc).
  -
    intros ca LB ws m H. change (PK.cw_pk_holds segs ca LB ws m) in H. unfold PK.cw_pk_holds in H.
    destruct (PK.decode_pk ca) as [u|]; [| exact H].
    destruct H as (g & ls & L & P & O & Wk & M & [SE _] & _). exists g, ls. repeat (split; [assumption|]). exact SE.
  -
    intros ca LB ws m H. change (TD.td_client segs ca LB ws m) in H. destruct H as [H _]. unfold TD.td_client0 in H.
    destruct (TD.decode_td ca) as [[cur cnt]|]; [| exact H].
    destruct H as (cs & INV). exists cs. split; [exact INV|]. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))).
Qed.
End ShLoad.
End Sound.
End PkInstA.
