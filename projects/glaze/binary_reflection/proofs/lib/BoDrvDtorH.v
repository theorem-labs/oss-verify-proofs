(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvConstRw3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAinvMuFrameB OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeLG OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS0SoundA. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvLowSh3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvConstRw3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAinvMuFrameB.AsAinvMuFrameA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAinvMuFrameB OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeLG OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS0SoundA.BoDrvNodesSoundA11.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import GPS.
Open Scope Z_scope.
#[local] Notation u := bv_unsigned.
#[local] Notation LE8 z := (word_to_le_bytes 8 (Z_to_bv 64 z)).

Section DtorH.
Context {RC : run_ceil}.
Variable bt : as_boot.
Variable G : gtable.
Hypothesis G_imglo : g_img_lo G = AsVocab.AsCells.ia_img_lo (bt_ia bt).
Hypothesis G_hi : g_img_hi G = AsVocab.AsCells.ia_img_hi (bt_ia bt).
Hypothesis G_ro_img : g_img_lo G <= g_ro_lo G /\ g_ro_lo G <= g_ro_hi G <= g_img_hi G.
Hypothesis G_img_al : 0 <= g_img_lo G /\ g_img_lo G mod 8 = 0 /\ g_img_hi G mod 8 = 0.
Hypothesis G_errno : g_ro_hi G <= g_errno G /\ g_errno G + 4 <= g_img_hi G.
(* [comment removed for export] *)
Hypothesis IMG_lo : AsVocab.AsCells.ia_img_lo (bt_ia bt) = DNA.IMG_LO.
Hypothesis IMG_hi : AsVocab.AsCells.ia_img_hi (bt_ia bt) = DNA.IMG_HI.
Hypothesis BT_SEGS : bt_segs bt = BSEGS.
Hypothesis K_mu : In (DNA.DTOR_MU, 8%nat, 0) (bt_consts bt).
Hypothesis K_cpm : In (0x10da1c, 1%nat, 1) (bt_consts bt).
(* [comment removed for export] *)
Hypothesis BT_IA : bt_ia bt = both_addrs.
Hypothesis BT_TLSFS : bt_tls_fs bt = ia_tp both_addrs.
Hypothesis K_rows : mu_rows_ok MU_B (bt_consts bt).
(* [comment removed for export] *)
#[local] Notation GF P := (AzBridgeH.AINVw (AzBridgeLG.AAINV_LG (AAINVP P bt))).
Lemma AAINVP_mu_frame : forall (P : ast -> Prop) Lc FF B C K (M M' : word -> option byte) mdl,
  AAINVP P bt Lc FF B C K M mdl ->
  (forall a : word, M' a <> M a -> DNA.DTOR_MU <= u a < DNA.DTOR_MU + 8 /\ M' a <> None) ->
  rdn (bt_segs bt) M' (Z_to_bv 64 DNA.DTOR_MU) 8 = Some (LE8 0) ->
  AAINVP P bt Lc FF B C K M' mdl.
Proof.
  intros P Lc FF B C K M M' mdl HA CH RD. unfold DNA.DTOR_MU in *.
  apply (AAINVP_const_rw bt (fun i => MU_B <= i < MU_B + 8)) with (M := M); unfold MU_B in *.
  - intros i Hi. rewrite BT_IA. cbn [ia_img_lo ia_img_hi both_addrs]. lia.
  - intros i Hi HD. unfold img_dyn in HD. rewrite BT_IA in HD. cbn [ia_instance ia_depot_tab ia_stackstore ia_ialloc_flag ia_ialloc_inst both_addrs] in HD. unfold IASZ in HD. lia.
  - intros i Hi HT. rewrite BT_TLSFS in HT. cbn [ia_tp both_addrs] in HT. lia.
  - intros i Hi HR. unfold rtc_cells in HR. rewrite BT_IA in HR. cbn [ia_rtc_sb ia_rtc_uar both_addrs] in HR. lia.
  - exact HA.
  - intros a Ha. exact (proj1 (CH a Ha)).
  - unfold mu_rows_ok in K_rows. rewrite Forall_forall in *. intros c Hc. destruct (K_rows c Hc) as [D | [D | E]].
    + left. intros i Hi. lia.
    + left. intros i Hi. lia.
    + right. subst c. cbn [fst snd]. exact RD.
Qed.

Theorem DTOR_H_P : forall (P : ast -> Prop) L LF B C K M mdl, GF P L LF B C K M mdl ->
  rdn BSEGS M (Z_to_bv 64 DNA.DTOR_MU) 8 = Some (LE8 0)
  /\ exists cpm : byte, rdn BSEGS M (Z_to_bv 64 0x10da1c) 1 = Some [cpm] /\ u cpm <> 0.
Proof.
  intros P L LF B C K M mdl (FF & _ & (HA & _)).
  destruct HA as (st & _ & RP & _).
  pose proof (read_consts bt st L FF M mdl RP) as CH. unfold cells_hold in CH. rewrite Forall_forall in CH. rewrite BT_SEGS in CH.
  pose proof (CH _ K_mu) as C1. pose proof (CH _ K_cpm) as C2.
  cbn beta iota in C1, C2. unfold cellN in C1, C2.
  split; [exact C1|]. exists (Z_to_bv 8 1). split; [exact C2 | vm_compute; discriminate].
Qed.

Theorem DTOR_FRAME_P : forall (P : ast -> Prop) L LF B C K M M' mdl, GF P L LF B C K M mdl ->
  (forall a : word, M' a <> M a -> (in_lsb (u a) = true \/ in_mub (u a) = true) /\ M' a <> None) ->
  rdn BSEGS M' (Z_to_bv 64 DNA.DTOR_MU) 8 = Some (LE8 0) ->
  GF P L LF B C K M' mdl.
Proof.
  intros P L LF B C K M M' mdl HAw Hch Hmu.
  set (M1 := fun a : word => if in_mub (u a) then M a else M' a).
  destruct HAw as (FF & HL & (HA & HG)).
  assert (ZN : forall b n, In (b, n) L -> AsVocab.ablk_ok (bt_ia bt) b n /\ 1 <= n /\ b mod 16 = 0)
    by (intros b n Hin; exact (AsVocab.aap_zone _ _ _ _ (AsAinvFrame3b.AAINV_props_all bt P) _ _ _ _ _ _ _ b n HA Hin)).
  (* [comment removed for export] *)
  assert (HA1 : AAINVP P bt L FF B C K M1 mdl).
  { apply (AsAinvZone3b.AsAinvLowSh3.AAINVP_lowsh_frame bt P L FF B C K M M1 mdl HA).
    intros a Ha. unfold M1 in Ha |- *. destruct (in_mub (u a)) eqn:Hm; [exfalso; apply Ha; reflexivity|].
    destruct (Hch a Ha) as [[Hl|Hm'] Hd]; [|rewrite Hm in Hm'; discriminate Hm']. split; [|exact Hd].
    unfold AsAinvZone3b.AsAinvLowSh3.img_shadow. rewrite IMG_lo, IMG_hi. unfold in_lsb in Hl.
    apply andb_prop in Hl as [L1 L2]. apply Z.leb_le in L1. apply Z.ltb_lt in L2.
    change DNA.LOWSH_LO with (0x7fff8000 + 0x10000 / 8) in L1. change DNA.LOWSH_HI with (0x7fff8000 + 0x663000 / 8) in L2.
    unfold DNA.IMG_LO, DNA.IMG_HI, AsVocab.SB in *.
    change (65536 / 8) with 8192 in *. change (6696960 / 8) with 837120 in *. change ((6696960 + 7) / 8) with 837120. lia. }
  assert (HG1 : AzBridgeLG.LG M1 L).
  { apply (AzBridgeLG.LG_kept M M1 L L HG (fun x H => H)). intros b n Hin Hm.
    unfold M1. destruct (in_mub (u (Z_to_bv 64 (AzBridgeLG.egb b n)))) eqn:Hmb; [reflexivity|].
    destruct (decide (M' (Z_to_bv 64 (AzBridgeLG.egb b n)) = M (Z_to_bv 64 (AzBridgeLG.egb b n)))) as [Heq|Hne]; [exact Heq|]. exfalso.
    destruct (Hch _ Hne) as [[Hl|Hm'] _]; [|rewrite Hmb in Hm'; discriminate Hm'].
    destruct (ZN b n Hin) as (Hab & Hn & Hal).
    destruct (AzBridgeLG.egb_band (bt_ia bt) b n Hab Hn) as (E1 & E2 & E3).
    rewrite u64_lit in Hl by (unfold AsVocab.SB, AsVocab.AS_HEAPLO in *; lia).
    unfold in_lsb in Hl. apply andb_prop in Hl as [L1 L2]. apply Z.ltb_lt in L2.
    change DNA.LOWSH_HI with (0x7fff8000 + 0x663000 / 8) in L2. destruct Hab as (A1 & A2 & A3 & A4).
    apply Z.leb_le in L1. change DNA.LOWSH_LO with (0x7fff8000 + 0x10000 / 8) in L1. rewrite IMG_lo, IMG_hi in A3.
    unfold AzBridgeLG.egb, AsVocab.SB, AsVocab.PTRLO, AsVocab.AS_LO, DNA.IMG_LO, DNA.IMG_HI in *.
    clear - L1 L2 A1 A2 A3 A4 Hn Hal Hm. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  exists FF. split; [exact HL|]. split.
  - apply (AAINVP_mu_frame P _ _ _ _ _ M1 M' mdl HA1).
    + intros a Ha. unfold M1 in Ha. destruct (in_mub (u a)) eqn:Hm; [|exfalso; apply Ha; reflexivity].
      split; [unfold in_mub in Hm; apply andb_prop in Hm as [X1 X2]; apply Z.leb_le in X1; apply Z.ltb_lt in X2; lia|].
      exact (proj2 (Hch a Ha)).
    + rewrite BT_SEGS. exact Hmu.
  - apply (AzBridgeLG.LG_kept M1 M' L L HG1 (fun x H => H)). intros b n Hin Hm.
    unfold M1. destruct (in_mub (u (Z_to_bv 64 (AzBridgeLG.egb b n)))) eqn:Hmb; [|reflexivity]. exfalso.
    destruct (ZN b n Hin) as (Hab & Hn & Hal).
    destruct (AzBridgeLG.egb_band (bt_ia bt) b n Hab Hn) as (E1 & E2 & E3).
    rewrite u64_lit in Hmb by (unfold AsVocab.SB, AsVocab.AS_HEAPLO in *; lia).
    unfold in_mub, DNA.DTOR_MU in Hmb. apply andb_prop in Hmb as [X1 X2]. apply Z.ltb_lt in X2. unfold AsVocab.SB in E1. lia.
Qed.

Theorem DTOR_H_h : forall h L LF B C K M mdl, AzBridgeH.AINVw (AzBridgeH.AAINV_HL bt h) L LF B C K M mdl ->
  rdn BSEGS M (Z_to_bv 64 DNA.DTOR_MU) 8 = Some (LE8 0)
  /\ exists cpm : byte, rdn BSEGS M (Z_to_bv 64 0x10da1c) 1 = Some [cpm] /\ u cpm <> 0.
Proof. intros h. exact (DTOR_H_P (AsAinvEntry3.AsAinvHole3.holes_lsopt h)). Qed.
Theorem DTOR_FRAME_h : forall h L LF B C K M M' mdl, AzBridgeH.AINVw (AzBridgeH.AAINV_HL bt h) L LF B C K M mdl ->
  (forall a : word, M' a <> M a -> (in_lsb (u a) = true \/ in_mub (u a) = true) /\ M' a <> None) ->
  rdn BSEGS M' (Z_to_bv 64 DNA.DTOR_MU) 8 = Some (LE8 0) ->
  AzBridgeH.AINVw (AzBridgeH.AAINV_HL bt h) L LF B C K M' mdl.
Proof. intros h. exact (DTOR_FRAME_P (AsAinvEntry3.AsAinvHole3.holes_lsopt h)). Qed.
End DtorH.
