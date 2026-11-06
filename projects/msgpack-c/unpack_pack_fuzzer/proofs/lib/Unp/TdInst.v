(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv OpsBridge Ops TdOps PkOps ClientX GLib Td TdEnter.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS HeapOp UB UO UG TD CX.
Open Scope Z_scope.
Unset Lia Cache.

Module TdInst.
Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW (unp_cw segs (XTP segs)) OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma cw5 : forall ca LB ws m, cw_holds (unp_cw segs (XTP segs)) 5 ca LB ws m -> TD.td_client segs ca LB ws m.
Proof. intros ca LB ws m H. exact H. Qed.
Lemma cw5' : forall ca LB ws m, TD.td_client segs ca LB ws m -> cw_holds (unp_cw segs (XTP segs)) 5 ca LB ws m.
Proof. intros ca LB ws m H. exact H. Qed.
Lemma cw0 : forall ca LB ws m, TD.nosub ws -> cw_holds (unp_cw segs (XTP segs)) 0 ca LB ws m.
Proof. intros ca LB ws m NS. first [exact I | exact NS | (apply Forall_forall; intros w Hw; exact (proj1 (Forall_forall _ _) NS w Hw))]. Qed.
Lemma cw12 : forall md ca LB ws m, (md = 1 \/ md = 2) -> cw_holds (unp_cw segs (XTP segs)) md ca LB ws m ->
  match decode_uc ca with Some u => unp_client segs md u LB ws m | None => False end.
Proof.
  intros md ca LB ws m [-> | ->] H; cbn [cw_holds unp_cw] in H; unfold cw_unp_holds in H;
    cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb] in H; exact H.
Qed.

Theorem znext_sound : forall pc, contract_sound segs OPS MP PB (Td.znext_contract pc).
Proof. exact (Td.znext_sound segs IMGX AW (unp_cw segs (XTP segs)) OPS HOPS cw5 cw5' cw0 MP PB). Qed.

Theorem tdenter_sound : forall pc, contract_sound segs OPS MP PB (TdEnter.tdenter_contract pc).
Proof. exact (TdEnter.tdenter_sound segs IMGX AW (unp_cw segs (XTP segs)) OPS HOPS cw12 cw5' MP PB). Qed.

End Sound.
End TdInst.
