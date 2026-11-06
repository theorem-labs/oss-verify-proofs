(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface AMalloc_iface2 AInstanceU2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.W2 Require ExhFirst.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require FakeLaw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Ops Seal ClientX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA Require F1Unp WPatSub.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require MemsetPre WPat.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Local Notation AIu2 := (AInstanceU2.AIu2 ExhFirst.exh_first).
Local Notation AIu_fake := (FakeLaw.AIu_fake ExhFirst.exh_first).
Section F1Cw.
Context {rc : runConstT}.
Definition CwA : client_world := Ops.UO.unp_cw asegs (ClientX.CX.XTP asegs).
Let CGL := F1Unp.F1Unp.cgl asegs.

Lemma shad_shadZ : forall a, shad a = Seal.Seal.shadZ a.
Proof. intros a. unfold shad, Seal.Seal.shadZ, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold Seal.Seal.SBz. lia. Qed.

Theorem Cw_ghost_grow : forall md ca LB ws m b0 n0 n, cw_holds CwA md ca LB ws m ->
  In (Win b0 n0 K_BLOCK) ws -> 0 < n0 -> b0 mod 8 = 0 ->
  (forall a, in_iv (shad b0, n) a -> ~ in_user LB a) -> cw_holds CwA md ca ((shad b0, n) :: LB) (ws ++ [Win (shad b0) n K_TWINz]) m.
Proof.
  intros md ca LB ws m b0 n0 n H IW N0 A8 FR. rewrite shad_shadZ in *.
  exact (cg_twin_grow _ _ _ CGL md ca LB ws m b0 n0 n H IW N0 A8 FR).
Qed.

Theorem Cw_ghost_free : forall md ca LB ws m b n ws', cw_holds CwA md ca LB ws m -> In (Win b n K_TWINz) ws ->
  (forall w, In w ws' <-> In w ws /\ w <> Win b n K_TWINz) -> cw_holds CwA md ca (remove iv_eq_dec (b, n) LB) ws' m.
Proof.
  intros md ca LB ws m b n ws' H IW EQ.
  exact (cg_ghost_free _ _ _ CGL md ca LB ws m b n K_TWINz ws' H ltac:(unfold K_GHOST, K_TWINz; lia) IW EQ).
Qed.

Theorem Cw_ghost_grow_f : forall kd md ca LB ws m b n, kd = K_FRAMEz \/ kd = K_FTWINz -> cw_holds CwA md ca LB ws m ->
  (forall a, in_iv (b, n) a -> ~ in_user LB a) -> cw_holds CwA md ca ((b, n) :: LB) (ws ++ [Win b n kd]) m.
Proof.
  intros kd md ca LB ws m b n K H FR.
  apply (cg_ghost_grow _ _ _ CGL md ca LB ws m b n kd H); [| | exact FR];
    destruct K as [->| ->]; unfold K_GHOST, K_FRAMEz, K_FTWINz, Seal.Seal.K_TWIN; lia.
Qed.

Theorem Cw_ghost_free_f : forall kd md ca LB ws m b n ws', kd = K_FRAMEz \/ kd = K_FTWINz -> cw_holds CwA md ca LB ws m -> In (Win b n kd) ws ->
  (forall w, In w ws' <-> In w ws /\ w <> Win b n kd) -> cw_holds CwA md ca (remove iv_eq_dec (b, n) LB) ws' m.
Proof.
  intros kd md ca LB ws m b n ws' K H IW EQ.
  apply (cg_ghost_free _ _ _ CGL md ca LB ws m b n kd ws' H); [| exact IW| exact EQ].
  destruct K as [->| ->]; unfold K_GHOST, K_FRAMEz, K_FTWINz; lia.
Qed.
End F1Cw.

Section WPat.
Context {rc : runConstT}.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Theorem W_PAT_SUB_A : MemsetPre.w_pat_sub_stmt AIu2 ACCT UNIV CwA.
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw kd wlen kind p A nb H1 H2 _ _ _ _ K45.
  exact (WPatSub.WPatSub.w_pat_sub_unp AIu2 ACCT UNIV asegs AIu_fake E st ms mo r hargs wnl L RNG sta LBa aw kd wlen kind p A nb H1 H2 K45).
Qed.
End WPat.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB AMalloc_iface2.TwinB AInstanceU2.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import Op.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Local Notation AIu2 := (AInstanceU2.TwinB.AIu2 ExhFirst.TwinB.exh_first).
Local Notation AIu_fake := (FakeLaw.TwinB.AIu_fake ExhFirst.TwinB.exh_first).
Section F1Cw.
Context {rc : runConstT}.
Definition CwA : client_world := Ops.UO.unp_cw bsegs (ClientX.CX.XTP bsegs).
Let CGL := F1Unp.TwinB.F1Unp.cgl bsegs.

Lemma shad_shadZ : forall a, shad a = Seal.Seal.shadZ a.
Proof. intros a. unfold shad, Seal.Seal.shadZ, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold Seal.Seal.SBz. lia. Qed.

Theorem Cw_ghost_grow : forall md ca LB ws m b0 n0 n, cw_holds CwA md ca LB ws m ->
  In (Win b0 n0 K_BLOCK) ws -> 0 < n0 -> b0 mod 8 = 0 ->
  (forall a, in_iv (shad b0, n) a -> ~ in_user LB a) -> cw_holds CwA md ca ((shad b0, n) :: LB) (ws ++ [Win (shad b0) n K_TWINz]) m.
Proof.
  intros md ca LB ws m b0 n0 n H IW N0 A8 FR. rewrite shad_shadZ in *.
  exact (cg_twin_grow _ _ _ CGL md ca LB ws m b0 n0 n H IW N0 A8 FR).
Qed.

Theorem Cw_ghost_free : forall md ca LB ws m b n ws', cw_holds CwA md ca LB ws m -> In (Win b n K_TWINz) ws ->
  (forall w, In w ws' <-> In w ws /\ w <> Win b n K_TWINz) -> cw_holds CwA md ca (remove iv_eq_dec (b, n) LB) ws' m.
Proof.
  intros md ca LB ws m b n ws' H IW EQ.
  exact (cg_ghost_free _ _ _ CGL md ca LB ws m b n K_TWINz ws' H ltac:(unfold K_GHOST, K_TWINz; lia) IW EQ).
Qed.

Theorem Cw_ghost_grow_f : forall kd md ca LB ws m b n, kd = K_FRAMEz \/ kd = K_FTWINz -> cw_holds CwA md ca LB ws m ->
  (forall a, in_iv (b, n) a -> ~ in_user LB a) -> cw_holds CwA md ca ((b, n) :: LB) (ws ++ [Win b n kd]) m.
Proof.
  intros kd md ca LB ws m b n K H FR.
  apply (cg_ghost_grow _ _ _ CGL md ca LB ws m b n kd H); [| | exact FR];
    destruct K as [->| ->]; unfold K_GHOST, K_FRAMEz, K_FTWINz, Seal.Seal.K_TWIN; lia.
Qed.

Theorem Cw_ghost_free_f : forall kd md ca LB ws m b n ws', kd = K_FRAMEz \/ kd = K_FTWINz -> cw_holds CwA md ca LB ws m -> In (Win b n kd) ws ->
  (forall w, In w ws' <-> In w ws /\ w <> Win b n kd) -> cw_holds CwA md ca (remove iv_eq_dec (b, n) LB) ws' m.
Proof.
  intros kd md ca LB ws m b n ws' K H IW EQ.
  apply (cg_ghost_free _ _ _ CGL md ca LB ws m b n kd ws' H); [| exact IW| exact EQ].
  destruct K as [->| ->]; unfold K_GHOST, K_FRAMEz, K_FTWINz; lia.
Qed.
End F1Cw.

Section WPat.
Context {rc : runConstT}.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Theorem W_PAT_SUB_A : MemsetPre.TwinB.w_pat_sub_stmt AIu2 ACCT UNIV CwA.
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw kd wlen kind p A nb H1 H2 _ _ _ _ K45.
  exact (WPatSub.TwinB.WPatSub.w_pat_sub_unp AIu2 ACCT UNIV bsegs AIu_fake E st ms mo r hargs wnl L RNG sta LBa aw kd wlen kind p A nb H1 H2 K45).
Qed.
End WPat.
End TwinB.
