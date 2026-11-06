(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodeSf5 OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeLG OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeC3 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodeSf5 OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeLG OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeC3 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsSetShIface OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import GPS.
Open Scope Z_scope.
#[local] Notation u := bv_unsigned.

Section BridgeSf5.
Context {RC : run_ceil}.
Variable SEGS : list Segment.
Variable IA : AsVocab.AsCells.as_addrs.
Variable FXOK : FX -> Prop.
Variable AAINVH : option Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable G : gtable.
Hypothesis G_tp : g_tp G = AsVocab.AsCells.ia_tp IA.

#[local] Notation SETSHADOW_AT := (AsSetShIface.SETSHADOW_AT SEGS FXOK IA).

Section GenRZ.   (* [comment removed for export] *)
Variable RZg : GPS.rz_t.
Hypothesis RZg_kc : forall T, AsIface3.AsK.kclosedD SEGS (fun c => RZg c T).

Theorem h_setsh_wj : forall entry, SETSHADOW_AT AAINVH entry -> h_setsh_at SEGS G FXOK (AzBridgeC3.AINVH0 AAINVH) RZg entry.
Proof.
  intros entry ST fx R0 M mdl L LF B C K ret sp f n m F1 F2 T HFX Hh (FF & HLF & HA) Hpre HL R10 R11 Hm1 Hmn Hpost. subst LF.
  assert (E10 : (10%bv : bv 5) = Z_to_bv 5 10) by (apply bv_eq; reflexivity).
  assert (E11 : (11%bv : bv 5) = Z_to_bv 5 11) by (apply bv_eq; reflexivity).
  assert (Hfk : exists k, In (f, k) FF /\ AsVocab.FS k = n).
  { assert (Hin : In (f, n) (map AzBridgeH.wfr FF)) by (rewrite HL; apply in_app_iff; right; left; reflexivity).
    apply in_map_iff in Hin as [[f0 k0] [Heq Hin]]. unfold AzBridgeH.wfr in Heq. cbn [fst snd] in Heq. injection Heq as -> <-.
    exists k0. split; [exact Hin | reflexivity]. }
  destruct Hfk as (k & Hin & HFS).
  refine (AzBridgeC3.katD_g SEGS RZg RZg_kc _ _ T (ST None fx R0 M mdl L FF B C K ret sp f k m HFX Hh HA (AzBridgeC3.call_pre_w SEGS IA G G_tp _ _ _ _ _ Hpre) Hin _ _ Hm1 _) _).
  - rewrite E10, R10. unfold AsVocab.sh_lo, AsVocab.SB, SB. reflexivity.
  - rewrite E11. exact R11.
  - rewrite HFS. exact Hmn.
  - intros c' (fx' & R' & M' & mdl' & -> & HFX' & Hkept & Hch & Hdef & Hscr & HA' & Hvm & Hlz & Hh').
    apply (Hpost fx' R' M' mdl' HFX' (AzBridgeC3.regs_kept_w _ _ Hkept)).
    + intros a Ha. destruct (Hch a Ha) as [X|X]; [left | right; unfold scratch, MSTK_SF; unfold AsSetShIface.MSTK_SF in X; exact X].
      unfold AsVocab.sh_lo, AsVocab.SB in X. unfold in_shadow, SB.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    + intros a Ha. destruct (decide (M' a = M a)) as [Heq|Hne]; [rewrite Heq; exact Ha | exact (Hdef a Hne)].
    + exact Hscr.
    + exists FF. split; [reflexivity | exact HA'].
    + exact (AzBridgeC3.nmodel_of_vm _ _ Hvm Hh').
Qed.
End GenRZ.

Theorem h_setsh_f : forall entry, SETSHADOW_AT AAINVH entry -> h_setsh_at SEGS G FXOK (AzBridgeC3.AINVH0 AAINVH) (realizes SEGS) entry.
Proof. exact (h_setsh_wj (realizes SEGS) (AsIface3.AsKInst.kclosedD_realizes SEGS)). Qed.
End BridgeSf5.

(* [comment removed for export] *)
Section LG.
Context {RC : run_ceil}.
Variable SEGS : list Segment.
Variable IA : AsVocab.AsCells.as_addrs.
Variable FXOK : FX -> Prop.
Variable AAINVH : option Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis ZONE : forall h Lc FF B C K M mdl b n, AAINVH h Lc FF B C K M mdl -> In (b, n) Lc -> AsVocab.ablk_ok IA b n /\ 1 <= n /\ b mod 16 = 0.
Hypothesis FZONE : forall h Lc FF B C K M mdl f k, AAINVH h Lc FF B C K M mdl -> In (f, k) FF -> 0 <= k /\ f mod AsVocab.FS k = 0.
Hypothesis BFDISJ : forall h Lc FF B C K M mdl b n f k, AAINVH h Lc FF B C K M mdl -> In (b, n) Lc -> In (f, k) FF -> b + n <= f \/ f + AsVocab.FS k <= b.

#[local] Notation SETSHADOW_AT := (AsSetShIface.SETSHADOW_AT SEGS FXOK IA).

Lemma FS_mul8 : forall k f, 0 <= k -> f mod AsVocab.FS k = 0 -> f mod 8 = 0.
Proof.
  intros k f Hk Hf. unfold AsVocab.FS in Hf. pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk) as Hp.
  apply Z.mod_divide in Hf; [|lia]. destruct Hf as [q Hq]. apply Z.mod_divide; [lia|]. exists (q * (8 * 2 ^ k)). lia.
Qed.

Theorem SETSHADOW_LG : forall entry, SETSHADOW_AT AAINVH entry -> SETSHADOW_AT (AzBridgeLG.AAINVL AAINVH) entry.
Proof.
  intros entry ST h fx R M mdl Lc FF B C K ret sp f k m HFX Hh (HA & HL) Hpre Hin R10 R11 Hm1 Hmn.
  refine (AsIface3.AsK.katD_conseq SEGS _ _ _ (ST h fx R M mdl Lc FF B C K ret sp f k m HFX Hh HA Hpre Hin R10 R11 Hm1 Hmn) _).
  intros c' (fx' & R' & M' & mdl' & Ec & HFX' & Hk & Hch & Hdef & Hscr & HA' & Hrest).
  exists fx', R', M', mdl'. repeat (split; [assumption|]). split; [|exact Hrest].
  split; [exact HA'|].
  apply (AzBridgeLG.LG_kept M M' Lc Lc HL (fun x H => H)). intros b n Hbin Hm.
  destruct (ZONE h _ _ _ _ _ _ _ b n HA Hbin) as (Hab & Hn & Hal).
  destruct (AzBridgeLG.egb_band IA b n Hab Hn) as (E1 & E2 & E3).
  destruct (decide (M' (Z_to_bv 64 (AzBridgeLG.egb b n)) = M (Z_to_bv 64 (AzBridgeLG.egb b n)))) as [Heq|Hne]; [exact Heq|]. exfalso.
  pose proof (Hch _ Hne) as X. rewrite Spec4.AgentLib.u64_lit in X by (unfold AsVocab.SB, AsVocab.AS_HEAPLO in *; lia).
  destruct X as [X|X].
  - destruct (FZONE h _ _ _ _ _ _ _ f k HA Hin) as (Hk0 & Hfm).
    pose proof (FS_mul8 k f Hk0 Hfm) as F8.
    assert (B8 : b mod 8 = 0).
    { apply Z.mod_divide in Hal; [|lia]. destruct Hal as [q Hq]. apply Z.mod_divide; [lia|]. exists (q * 2). lia. }
    destruct Hab as (A1 & _). unfold AsVocab.PTRLO in A1.
    destruct (AzBridgeLG.egb_in_shadow b n Hm Hal ltac:(lia) ltac:(lia)) as (G1 & G2).
    pose proof (BFDISJ h _ _ _ _ _ _ _ b n f k HA Hbin Hin) as D.
    unfold AsVocab.sh_lo, AsVocab.sh_hi in *. set (F := AsVocab.FS k) in *. set (z := AzBridgeLG.egb b n) in *. clearbody F z.
    clear - X G1 G2 D F8 B8 Hmn Hm1.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  - pose proof (AzBridgeLG.call_pre_sp SEGS IA _ _ _ _ _ Hpre) as SP. unfold AsSetShIface.MSTK_SF in *. lia.
Qed.
End LG.

(* [comment removed for export] *)
Section Inst.
Context {RC : run_ceil}.
Variable bt : AsAinvDefs3.as_boot.
Variable SEGS : list Segment.
Variable FXOK : FX -> Prop.
Variable G : gtable.
Hypothesis G_tp : g_tp G = AsVocab.AsCells.ia_tp (AsAinvDefs3.bt_ia bt).

Lemma HS_fzone : forall h Lc FF B C K M mdl f k, AsAinvEntry3.AsAinvHole3.AAINV_HS bt h Lc FF B C K M mdl -> In (f, k) FF -> 0 <= k /\ f mod AsVocab.FS k = 0.
Proof.
  intros h Lc FF B C K M mdl f k HA Hin.
  destruct (AsVocab.aap_fzone _ _ _ _ (AsAinvFrame3b.AAINV_props_all bt (AsAinvEntry3.AsAinvHole3.holes_lsopt h)) _ _ _ _ _ _ _ f k HA Hin) as ((K0 & _) & _ & Hm & _).
  split; [exact K0 | exact Hm].
Qed.
Lemma HS_bfdisj : forall h Lc FF B C K M mdl b n f k, AsAinvEntry3.AsAinvHole3.AAINV_HS bt h Lc FF B C K M mdl -> In (b, n) Lc -> In (f, k) FF -> b + n <= f \/ f + AsVocab.FS k <= b.
Proof. intros h Lc FF B C K M mdl b n f k HA Hb Hf. exact (AsVocab.aap_bfdisj _ _ _ _ (AsAinvFrame3b.AAINV_props_all bt (AsAinvEntry3.AsAinvHole3.holes_lsopt h)) _ _ _ _ _ _ _ b n f k HA Hb Hf). Qed.

Theorem setsh_HL : forall entry,
  AsSetShIface.SETSHADOW_AT SEGS FXOK (AsAinvDefs3.bt_ia bt) (AsAinvEntry3.AsAinvHole3.AAINV_HS bt) entry ->
  AsSetShIface.SETSHADOW_AT SEGS FXOK (AsAinvDefs3.bt_ia bt) (AzBridgeH.AAINV_HL bt) entry.
Proof. intros entry ST. exact (SETSHADOW_LG SEGS (AsAinvDefs3.bt_ia bt) FXOK (AsAinvEntry3.AsAinvHole3.AAINV_HS bt) (AzBridgeH.HS_zone bt) HS_fzone HS_bfdisj entry ST). Qed.


Theorem h_setsh_bt_f : forall entry,
  AsSetShIface.SETSHADOW_AT SEGS FXOK (AsAinvDefs3.bt_ia bt) (AsAinvEntry3.AsAinvHole3.AAINV_HS bt) entry ->
  h_setsh_at SEGS G FXOK (AzBridgeH.AINVH_bt bt) (realizes SEGS) entry.
Proof. intros entry ST. exact (h_setsh_f SEGS (AsAinvDefs3.bt_ia bt) FXOK (AzBridgeH.AAINV_HL bt) G G_tp entry (setsh_HL entry ST)). Qed.
End Inst.
