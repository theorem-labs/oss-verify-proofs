(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodeAnn OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeC3 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodeAnn OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeC3 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import GPS.
Open Scope Z_scope.
#[local] Notation u := bv_unsigned.

Section BridgeAnn.
Context {RC : run_ceil}.
Variable SEGS : list Segment.
Variable IA : AsVocab.AsCells.as_addrs.
Variable FXOK : FX -> Prop.
Variable AAINVH : option Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable G : gtable.
Hypothesis G_ro_img : g_img_lo G <= g_ro_lo G /\ g_ro_lo G <= g_ro_hi G <= g_img_hi G.
Hypothesis G_tp : g_tp G = AsVocab.AsCells.ia_tp IA.

#[local] Notation ANNOTATE_ATW := (AsIface3.ANNOTATE_ATW SEGS FXOK IA AAINVH).   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma accessible_addressable : forall M b hi, AsVocab.accessible M b (hi - b) -> addressable M b hi.
Proof.
  intros M b hi H z Hz. specialize (H z ltac:(lia)). pose proof (Z.mod_pos_bound z 8 ltac:(lia)) as MB. unfold AsVocab.sbyte, AsVocab.sh_lo, AsVocab.SB in H. unfold SB.
  destruct (M (Z_to_bv 64 (2147450880 + z / 8))) as [bt|] eqn:Hm; [|lia].
  exists bt. split; [reflexivity|].
  pose proof (bv_unsigned_in_range 8 bt) as Hr. change (bv_modulus 8) with 256 in Hr.
  assert (S : bv_signed bt = u bt \/ bv_signed bt = u bt - 256).
  { unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus. change (bv_modulus 8) with 256. change (256 / 2) with 128.
    destruct (Z_lt_le_dec (u bt) 128); [left; rewrite Z.mod_small by lia; lia | right; replace (u bt + 128) with (u bt - 128 + 1 * 256) by lia; rewrite Z.mod_add by lia; rewrite Z.mod_small by lia; lia]. }
  lia.
Qed.

Section GenRZ.   (* [comment removed for export] *)
Variable RZg : GPS.rz_t.
Hypothesis RZg_kc : forall T, AsIface3.AsK.kclosedD SEGS (fun c => RZg c T).

Theorem h_annot_wj : forall entry, ANNOTATE_ATW entry -> h_annot_at SEGS G FXOK (AzBridgeC3.AINVH0 AAINVH) RZg entry.
Proof.
  intros entry AN fx R0 M mdl L LF B C K ret sp beg n om nm L1 L2 T HFX Hh (FF & HLF & HA) Hpre HL R10 R11 R12 R13 Hom Hnm Hadr Hpost. subst LF.
  assert (E10 : (10%bv : bv 5) = Z_to_bv 5 10) by (apply bv_eq; reflexivity).
  assert (E11 : (11%bv : bv 5) = Z_to_bv 5 11) by (apply bv_eq; reflexivity).
  assert (E12 : (12%bv : bv 5) = Z_to_bv 5 12) by (apply bv_eq; reflexivity).
  assert (E13 : (13%bv : bv 5) = Z_to_bv 5 13) by (apply bv_eq; reflexivity).
  refine (AzBridgeC3.katD_g SEGS RZg RZg_kc _ _ T (AN None fx R0 M mdl L FF B C K ret sp beg n om nm HFX Hh HA (AzBridgeC3.call_pre_w SEGS IA G G_tp _ _ _ _ _ Hpre) _ _ _ _ _ Hom Hnm _) _);
    try (rewrite ?E10, ?E11, ?E12, ?E13; first [exact R10 | exact R11 | exact R12 | exact R13]).
  - rewrite HL. apply in_app_iff. right. left. reflexivity.
  - replace (om - beg) with (om - beg) by lia. apply AzBridgeC3.nacc_w. intros z Hz. apply Hadr. lia.
  - intros c' (fx' & R' & M' & mdl' & -> & HFX' & Hkept & Hacc & Hch & Hdef & Hscr & HA' & Hvm & Hlz & Hh').
    apply (Hpost fx' R' M' mdl' HFX' (AzBridgeC3.regs_kept_w _ _ Hkept)).
    + intros a Ha. destruct (Hch a Ha) as [X|X]; [left | right; unfold scratch, MSTK_C; unfold AsVocab.MSTK_C in X; exact X].
      apply (AzBridgeC3.in_shadow_sh G G_ro_img). split; [|exact (proj2 X)].
      destruct X as [X _]. unfold AsVocab.sh_lo. assert (beg / 8 <= Z.min om nm / 8) by (apply Z.div_le_mono; lia). lia.
    + intros a Ha. destruct (decide (M' a = M a)) as [Heq|Hne]; [rewrite Heq; exact Ha | exact (Hdef a Hne)].
    + exact (accessible_addressable M' beg nm Hacc).
    + exact Hscr.
    + exists FF. split; [reflexivity | exact HA'].
    + exact (AzBridgeC3.nmodel_of_vm _ _ Hvm Hh').
Qed.
End GenRZ.

Theorem h_annot_f : forall entry, ANNOTATE_ATW entry -> h_annot_at SEGS G FXOK (AzBridgeC3.AINVH0 AAINVH) (realizes SEGS) entry.
Proof. exact (h_annot_wj (realizes SEGS) (AsIface3.AsKInst.kclosedD_realizes SEGS)). Qed.
End BridgeAnn.
