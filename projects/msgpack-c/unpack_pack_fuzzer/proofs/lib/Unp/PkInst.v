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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv OpsBridge Ops TdOps PkOps ClientX GLib
     PkPeek PkStack PkRoome PkPush0 PkPush PkNext PkPop PkEnter PkExit PkFld PkCap PkInv.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS HeapOp UB UO UG TD PK CX.
Open Scope Z_scope.
Unset Lia Cache.

Module PkInst.
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
Lemma cw3' : forall ca LB ws m, PK.cw_pk_holds segs ca LB ws m -> cw_holds (unp_cw segs (XTP segs)) 3 ca LB ws m.
Proof. intros ca LB ws m H. exact H. Qed.
Lemma cw5' : forall ca LB ws m, TD.td_client segs ca LB ws m -> cw_holds (unp_cw segs (XTP segs)) 5 ca LB ws m.
Proof. intros ca LB ws m H. exact H. Qed.
Lemma cw2 : forall ca LB ws m, cw_holds (unp_cw segs (XTP segs)) 2 ca LB ws m ->
  match decode_uc ca with Some u => unp_client segs 2 u LB ws m | None => False end.
Proof. intros ca LB ws m H. exact H. Qed.

Theorem pkenter_sound : forall pc, contract_sound segs OPS MP PB (PkEnter.pkenter_contract pc).
Proof. exact (PkEnter.pkenter_sound segs IMGX AW (unp_cw segs (XTP segs)) OPS HOPS cw2 cw3' MP PB). Qed.

Theorem peek_sound : forall pc, contract_sound segs OPS MP PB (PkPeek.peek_contract segs pc).
Proof. exact (PkPeek.peek_sound segs IMGX AW (unp_cw segs (XTP segs)) OPS HOPS cw3 cw3' MP PB HMPA). Qed.
Theorem pkload_sound : forall pc, contract_sound segs OPS MP PB (PkPeek.pkload_contract segs pc).
Proof. exact (PkPeek.pkload_sound segs IMGX AW (unp_cw segs (XTP segs)) OPS HOPS cw3 MP PB HMPA). Qed.

Theorem roome_sound : forall pc, contract_sound segs OPS MP PB (PkStack.roome_contract pc).
Proof. exact (PkRoome.roome_sound segs IMGX AW (unp_cw segs (XTP segs)) OPS HOPS cw3 cw3' MP PB). Qed.
Theorem push0_sound : forall pc, contract_sound segs OPS MP PB (PkStack.push0_contract pc).
Proof. exact (PkPush0.push0_sound segs IMGX AW (unp_cw segs (XTP segs)) OPS HOPS cw3 cw3' MP PB). Qed.
Theorem push_sound : forall pc, contract_sound segs OPS MP PB (PkStack.push_contract pc).
Proof. exact (PkPush.push_sound segs IMGX AW (unp_cw segs (XTP segs)) OPS HOPS cw3 cw3' MP PB). Qed.
Theorem roome_a_sound : forall pc, contract_sound segs OPS MP PB (PkStack.roome_contract_a pc).
Proof. exact (PkRoome.roome_a_sound segs IMGX AW (unp_cw segs (XTP segs)) OPS HOPS cw3 cw3' MP PB). Qed.
Theorem push_a_sound : forall pc, contract_sound segs OPS MP PB (PkStack.push_contract_a pc).
Proof. exact (PkPush.push_a_sound segs IMGX AW (unp_cw segs (XTP segs)) OPS HOPS cw3 cw3' MP PB). Qed.
Theorem pop_a_sound : forall pc, contract_sound segs OPS MP PB (PkStack.pop_contract_a pc).
Proof. exact (PkPop.pop_a_sound segs IMGX AW (unp_cw segs (XTP segs)) OPS HOPS cw3 cw3' MP PB). Qed.
Theorem next_sound : forall pc, contract_sound segs OPS MP PB (PkStack.next_contract pc).
Proof. exact (PkNext.next_sound segs IMGX AW (unp_cw segs (XTP segs)) OPS HOPS cw3 cw3' MP PB). Qed.
Theorem pop_sound : forall pc, contract_sound segs OPS MP PB (PkStack.pop_contract pc).
Proof. exact (PkPop.pop_sound segs IMGX AW (unp_cw segs (XTP segs)) OPS HOPS cw3 cw3' MP PB). Qed.

Theorem pkfld_sound : forall pc, contract_sound segs OPS MP PB (PkFld.pkfld_contract segs pc).
Proof. exact (PkFld.pkfld_sound segs IMGX AW (unp_cw segs (XTP segs)) OPS HOPS cw3 MP PB HMPA). Qed.

Theorem pkexit_sound : forall pc, contract_sound segs OPS MP PB (PkExit.pkexit_contract pc).
Proof. exact (PkExit.pkexit_sound segs IMGX AW (unp_cw segs (XTP segs)) OPS HOPS cw3 cw5' MP PB). Qed.

Theorem pkinv_sound : forall pc, contract_sound segs OPS MP PB (PkInv.pkinv_contract pc).
Proof. exact (fun pc => PkInv.pkinv_sound pc segs IMGX AW (unp_cw segs (XTP segs)) OPS HOPS cw3 MP PB). Qed.

Theorem pkcap_sound : forall pc, contract_sound segs OPS MP PB (PkCap.pkcap_contract pc).
Proof. intros pc. exact (PkCap.pkcap_sound segs IMGX AW (unp_cw segs (XTP segs)) OPS HOPS cw3 pc MP PB). Qed.

End Sound.
End PkInst.
