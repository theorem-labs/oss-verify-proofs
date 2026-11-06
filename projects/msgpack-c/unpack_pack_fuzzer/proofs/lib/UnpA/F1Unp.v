(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Op Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Ops Seal OpsTwin OpsKeep OpsLaws PkOps TdOps ClientX XwTwin.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA Require WPatSub.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import HeapOp UO.
Open Scope Z_scope.
Unset Lia Cache.

Module F1Unp.
Section WithSegs.
Variable segs : list Segment.
Local Abbreviation Cw := (unp_cw segs (CX.XTP segs)).

Theorem cw_sub_ghost : forall md ca LB ws m w g a, cw_holds Cw md ca LB ws m -> In w ws -> In g ws ->
  K_SUB <= w_kind w < K_GHOST -> K_GHOST <= w_kind g -> in_iv (w_iv w) a -> in_iv (w_iv g) a -> False.
Proof. exact (UOL.cw_sub_ghost segs (CX.XTP segs) (XWT.XW_sub_ghost segs)). Qed.

Theorem cw_zc : forall md ca LB ws ws' m zc zc', cw_holds Cw md ca LB ws m -> Bridge.Op.ZC_BASE + zc' < Bridge.Op.ZC_BAND ->
  (forall w, In w ws' <-> (In w ws /\ w <> Bridge.Op.zc_win zc) \/ w = Bridge.Op.zc_win zc') -> cw_holds Cw md ca LB ws' m.
Proof.
  intros md ca LB ws ws' m zc zc' H B Hws'.

  assert (B48 : Bridge.Op.ZC_BASE + zc' < 2 ^ 48) by (unfold Bridge.Op.ZC_BAND, Bridge.Op.ZC_BASE in *; lia).
  exact (UOL.cw_zc segs (CX.XTP segs) (XWT.XW_zc segs) md ca LB ws ws' m (Bridge.Op.ZC_BASE + zc) (Bridge.Op.ZC_BASE + zc') H B48 Hws').
Qed.

Theorem cw_k0_del : forall md ca LB ws ws' m w0, cw_holds Cw md ca LB ws m -> w_kind w0 = K_STACK ->
  (forall w, In w ws' <-> In w ws /\ w <> w0) -> cw_holds Cw md ca LB ws' m.
Proof. exact (UOL.cw_k0_del segs (CX.XTP segs) (XWT.XW_k0_del segs)). Qed.

Theorem cw_vecs_distinct : forall md ca LB ws m i j a b, cw_holds Cw md ca LB ws m -> In i (Actr.ActrA.VECS md) -> In j (Actr.ActrA.VECS md) -> i <> j ->
  nth_error ca i = Some a -> nth_error ca j = Some b -> bv_unsigned a <> 0 -> bv_unsigned b <> 0 -> bv_unsigned a <> bv_unsigned b.
Proof.
  intros md ca LB ws m i j a b H Ii Ij NE NA NB _ _. unfold Actr.ActrA.VECS in Ii, Ij.
  destruct ((md =? 1) || (md =? 2)) eqn:M12.
  - assert (MD : md = CM_UNP \/ md = CM_CONS) by (apply orb_prop in M12 as [M|M]; apply Z.eqb_eq in M; [left| right]; exact M).
    apply (UOL.cw_unp_vecs_distinct_ij segs (CX.XTP segs) md ca LB ws m i j a b H MD); try assumption.
    + destruct Ii as [<-|[<-|[]]]; [left| right]; reflexivity.
    + destruct Ij as [<-|[<-|[]]]; [left| right]; reflexivity.
  - destruct (md =? 3); [| destruct Ii]. destruct Ii as [<-|[]]. destruct Ij as [<-|[]]. exfalso. exact (NE eq_refl).
Qed.

Theorem cw_vec_unowned : forall md ca LB ws m i a, cw_holds Cw md ca LB ws m -> In i (Actr.ActrA.VECS md) -> nth_error ca i = Some a -> bv_unsigned a <> 0 ->
  forall w, In w ws -> w_kind w = K_BLOCK -> 0 < w_len w -> w_lo w <> bv_unsigned a.
Proof.
  intros md ca LB ws m i a H Ii NA A0. unfold Actr.ActrA.VECS in Ii.
  destruct ((md =? 1) || (md =? 2)) eqn:M12.
  - assert (MD : md = CM_UNP \/ md = CM_CONS) by (apply orb_prop in M12 as [M|M]; apply Z.eqb_eq in M; [left| right]; exact M).
    apply (UOT.cw_unp_vec_unowned segs (CX.XTP segs) md ca LB ws m i a H MD); [| exact NA].
    destruct Ii as [<-|[<-|[]]]; [left| right]; reflexivity.
  - destruct (Z.eqb_spec md 3) as [->|N3]; [| destruct Ii]. destruct Ii as [<-|[]].
    exact (XWT.pk_vec_unowned segs ca LB ws m a H NA A0).
Qed.

Definition cgl : client_ghost_laws Cw Seal.shadZ Seal.K_TWIN :=
  UOT.unp_cgl segs (CX.XTP segs) (CGL (CX.XTP segs) Seal.shadZ Seal.K_TWIN (XWT.XW_twin_grow segs) (XWT.XW_ghost_grow segs) (XWT.XW_ghost_free segs)).
End WithSegs.
End F1Unp.

Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Model OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Layout OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Inv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Ops OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Seal OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.OpsTwin OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.OpsKeep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.OpsLaws OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkOps OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.TdOps OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.ClientX OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.XwTwin.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import HeapOp UO.
Open Scope Z_scope.
Unset Lia Cache.

Module F1Unp.
Section WithSegs.
Variable segs : list Segment.
Local Abbreviation Cw := (unp_cw segs (CX.XTP segs)).

Theorem cw_sub_ghost : forall md ca LB ws m w g a, cw_holds Cw md ca LB ws m -> In w ws -> In g ws ->
  K_SUB <= w_kind w < K_GHOST -> K_GHOST <= w_kind g -> in_iv (w_iv w) a -> in_iv (w_iv g) a -> False.
Proof. exact (UOL.cw_sub_ghost segs (CX.XTP segs) (XWT.XW_sub_ghost segs)). Qed.

Theorem cw_zc : forall md ca LB ws ws' m zc zc', cw_holds Cw md ca LB ws m -> Bridge.Op.TwinB.ZC_BASE + zc' < Bridge.Op.TwinB.ZC_BAND ->
  (forall w, In w ws' <-> (In w ws /\ w <> Bridge.Op.TwinB.zc_win zc) \/ w = Bridge.Op.TwinB.zc_win zc') -> cw_holds Cw md ca LB ws' m.
Proof.
  intros md ca LB ws ws' m zc zc' H B Hws'.

  assert (B48 : Bridge.Op.TwinB.ZC_BASE + zc' < 2 ^ 48) by (unfold Bridge.Op.TwinB.ZC_BAND, Bridge.Op.TwinB.ZC_BASE in *; lia).
  exact (UOL.cw_zc segs (CX.XTP segs) (XWT.XW_zc segs) md ca LB ws ws' m (Bridge.Op.TwinB.ZC_BASE + zc) (Bridge.Op.TwinB.ZC_BASE + zc') H B48 Hws').
Qed.

Theorem cw_k0_del : forall md ca LB ws ws' m w0, cw_holds Cw md ca LB ws m -> w_kind w0 = K_STACK ->
  (forall w, In w ws' <-> In w ws /\ w <> w0) -> cw_holds Cw md ca LB ws' m.
Proof. exact (UOL.cw_k0_del segs (CX.XTP segs) (XWT.XW_k0_del segs)). Qed.

Theorem cw_vecs_distinct : forall md ca LB ws m i j a b, cw_holds Cw md ca LB ws m -> In i (Actr.TwinB.ActrA.VECS md) -> In j (Actr.TwinB.ActrA.VECS md) -> i <> j ->
  nth_error ca i = Some a -> nth_error ca j = Some b -> bv_unsigned a <> 0 -> bv_unsigned b <> 0 -> bv_unsigned a <> bv_unsigned b.
Proof.
  intros md ca LB ws m i j a b H Ii Ij NE NA NB _ _. unfold Actr.TwinB.ActrA.VECS in Ii, Ij.
  destruct ((md =? 1) || (md =? 2)) eqn:M12.
  - assert (MD : md = CM_UNP \/ md = CM_CONS) by (apply orb_prop in M12 as [M|M]; apply Z.eqb_eq in M; [left| right]; exact M).
    apply (UOL.cw_unp_vecs_distinct_ij segs (CX.XTP segs) md ca LB ws m i j a b H MD); try assumption.
    + destruct Ii as [<-|[<-|[]]]; [left| right]; reflexivity.
    + destruct Ij as [<-|[<-|[]]]; [left| right]; reflexivity.
  - destruct (md =? 3); [| destruct Ii]. destruct Ii as [<-|[]]. destruct Ij as [<-|[]]. exfalso. exact (NE eq_refl).
Qed.

Theorem cw_vec_unowned : forall md ca LB ws m i a, cw_holds Cw md ca LB ws m -> In i (Actr.TwinB.ActrA.VECS md) -> nth_error ca i = Some a -> bv_unsigned a <> 0 ->
  forall w, In w ws -> w_kind w = K_BLOCK -> 0 < w_len w -> w_lo w <> bv_unsigned a.
Proof.
  intros md ca LB ws m i a H Ii NA A0. unfold Actr.TwinB.ActrA.VECS in Ii.
  destruct ((md =? 1) || (md =? 2)) eqn:M12.
  - assert (MD : md = CM_UNP \/ md = CM_CONS) by (apply orb_prop in M12 as [M|M]; apply Z.eqb_eq in M; [left| right]; exact M).
    apply (UOT.cw_unp_vec_unowned segs (CX.XTP segs) md ca LB ws m i a H MD); [| exact NA].
    destruct Ii as [<-|[<-|[]]]; [left| right]; reflexivity.
  - destruct (Z.eqb_spec md 3) as [->|N3]; [| destruct Ii]. destruct Ii as [<-|[]].
    exact (XWT.pk_vec_unowned segs ca LB ws m a H NA A0).
Qed.

Definition cgl : client_ghost_laws Cw Seal.shadZ Seal.K_TWIN :=
  UOT.unp_cgl segs (CX.XTP segs) (CGL (CX.XTP segs) Seal.shadZ Seal.K_TWIN (XWT.XW_twin_grow segs) (XWT.XW_ghost_grow segs) (XWT.XW_ghost_free segs)).
End WithSegs.
End F1Unp.
End TwinB.
