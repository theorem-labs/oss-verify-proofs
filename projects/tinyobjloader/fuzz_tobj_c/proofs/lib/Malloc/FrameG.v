(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "not"; "ex"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "add"; "le"; "of_nat"; "pow"; "@Corelib.Init.Datatypes"; "option"; "Some"; "true"; "bool"; "nat"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "byteview_of"; "holds"; "auxv_ok"; "mc_chk_guard"; "mc_chk_guard_got"; "mc_ctz_tab"; "mc_libc"; "mc_lock"; "mc_med_cnt_tab"; "mc_replaced"; "mc_size_classes"; "mc_small_cnt_tab"; "topL"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "mkMA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "Inv"; "cell_holds"; "in_footprint"; "loc_addr"; "mc_loc"; "mc_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FrameG"; "static_ng"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "st_init_done"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLayout MallocFooter NestTier MallocIface MallocIfaceI MallocLaws FpLaws ErrnoFrame Zones2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition static_ng (C : mconsts) (a : Z) : Prop := ltac2:(tb__ "0|9|
S3S1S8S17VC;A1M0Va;A2S6Va;S7G0Z38A2A2A2S3S1S8S1aVC;A1M1Va;A2S6Va;S7G1Z4M2A2A2A2S3S1S8S1bVC;A1M3Va;A2S6Va;S7G3Z60A2A2A2S3S1S8S1cVC;A1M4Va;A2S6Va;S7G4Z1bA2A2A2S3S1S8S19VC;A1M5Va;A2S6Va;S7G5G2A2A2A2S3S1S8S16VC;A1M6Va;A2S6Va;S7G6Z20A2A2A2S3S1S8S15VC;A1M7Va;A2S6Va;S7G7Z8A2A2A2S1S8S18VC;A1M8Va;A2S6Va;S7G8G2A2A2A2A2A2A2A2A2A2A2").

Section FG.
  Variables (C : mconsts) (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate) (L : layout).
  Variables (rd rd' : word -> option byte) (wok wok' : word -> bool) (vm : VmMaps).
  Variable D : Z -> Prop.

  Hypothesis HMI : ltac2:(tb__ "0|0|
S22VC;S23VX;VR;VU;A3S21Vs;VL;A2Vrd;Vwok;Vvm;A6").
  Hypothesis HXr : xraw X s.
  Hypothesis AG : ltac2:(tb__ "0|1|
S0S1S8Z0R1A2S6R1SaZ2Z40A2A2A2S4VD;R2A1A1S1S2SbS1eQ8A1A1Vrd';S1fQ40R3A2M0A1Vrd;G0A1A3S2SeVwok';G0A1Vwok;G0A1A3A2F_;F_;Fa;").

  Hypothesis RDg : ltac2:(tb__ "0|2|
S0VD;R1A1S1S8S14VC;A1M0R2A2S6R2S7G0Z8A2A2A2S5S1eQ8A1M1G1S2SbG1A1Vrd';S1fQ40R4A2A1ScG1R1A2A3Lb;A2F_;F_;Fa;").
  Hypothesis D_dec : ltac2:(tb__ "0|1|
S0S3VD;R1A1M0S4G0A1A2Fa;").
  Hypothesis D_fp : ltac2:(tb__ "0|0|
S0VD;R1A1S4S25VL;Vs;R2A3A1F_;Fa;").
  Hypothesis D_static : ltac2:(tb__ "0|0|
S0VD;R1A1S4S29VC;R2A2A1F_;Fa;").
  Lemma BA a : ltac2:(tb__ "0|2|
S4VD;Va;A1A1S1S2SbS0A1M0S11Vrd';Vwok';Va;A3S11Vrd;Vwok;Va;A3A3S2G0S11Vrd';S1eQ40A1SdL_;M1Va;A3S11Vrd;G1Va;A3A3A2F_;").
  Proof using AG.
    intros Ha. unfold byteview_of.
    destruct ((0 <=? a) && (a <? 2 ^ 64))%bool eqn:E; [|split; reflexivity].
    apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    destruct (AG a ltac:(lia) Ha) as [R1 W1]. rewrite R1, W1. split; reflexivity.
  Qed.

  Lemma RD' a v : ltac2:(tb__ "0|4|
VD;Va;A1S5S1eQ8A1M0G0S2SbG0A1Vrd';S1fQ40M1Va;A2A1ScG0R1A2A3Lb;A2F_;S2SbS0A1M2S11Vrd;S1eG1A1SdL_;M3Va;A3ScS0Vv;A2A3S5S0S0S1S2G2S11Vrd';G3Va;A3ScS0R1A2A3S1S8Z0R1A2S6R1Z100A2A2A2Lv';A2F_;F_;").
  Proof using AG D_dec.
    intros RD Hv. unfold byteview_of in *. destruct ((0 <=? a) && (a <? 2 ^ 64))%bool eqn:E; [|discriminate].
    apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. cbn [andb] in *.
    destruct (D_dec a) as [Ha|Ha].
    - destruct (RD Ha) as [b Hb]. rewrite Hb. exists (bv_unsigned b). split; [reflexivity|].
      pose proof (bv_unsigned_in_range 8 b) as U8. change (bv_modulus 8%N) with 256 in U8. lia.
    - rewrite (proj1 (AG a ltac:(lia) Ha)). destruct (rd (Z_to_bv 64 a)) as [b|]; [|discriminate].
      exists (bv_unsigned b). split; [reflexivity|]. pose proof (bv_unsigned_in_range 8 b) as U8. change (bv_modulus 8%N) with 256 in U8. lia.
  Qed.

  Lemma holds_ext (b0 b1 : byteview) a0 w v : ltac2:(tb__ "0|1|
SfS20R1Vw;A2S2SbS0A1Vb1;S7Va0;S9R2A1A2M0A1Vb0;G0A1A3F_;Fk;S12Vb0;Va0;Vw;Vv;A4S12Vb1;Va0;Vw;Vv;A4F_;F_;").
  Proof using . intros B H k Hk. rewrite (B k Hk). exact (H k Hk). Qed.

  Lemma cell_holds_ext (b0 b1 : byteview) c : ltac2:(tb__ "0|2|
SfS20R1S28Vc;A1M0A2S2SbS0A1Vb1;S7S26VL;S27Vc;A1A2S9R2A1A2M1A1Vb0;G1A1A3F_;Fk;S20U0G0A2S24VL;Vb0;Vc;A3S24VL;Vb1;Vc;A3F_;F_;F_;").
  Proof using .
    intros B Hw Hc. unfold cell_holds in *. destruct (mc_val c).
    - intros j Hj. rewrite (B j Hj). exact (Hc j Hj).
    - intros j Hj. rewrite (B j Hj). exact (Hc j Hj).
    - destruct Hc as (b & Hb & Hm5). exists b. split; [|exact Hm5]. specialize (B 0%nat Hw). rewrite Z.add_0_r in B. rewrite B. exact Hb.
    - intros j Hj. rewrite (B j Hj). exact (Hc j Hj).
  Qed.

  Theorem minvG_frame_core : ltac2:(tb__ "0|0|
S2SeS2aVs;A1S10A3S13VC;VL;S11Vrd';S1eQ40A1SdL_;A2A3F_;S22VC;S23VX;VR;VU;A3S21Vs;VL;A2Vrd';Vwok';Vvm;A6F_;").
  Proof using AG D_dec D_fp D_static HMI HXr RDg.
    intros HAUX.
    pose proof HMI as (HI & HB & HC & ((HL & HCI & HO) & HF) & HV & HST & HA & HLG & HIMG & HMW). cbn [ma_s ma_L] in *.
    set (bv := byteview_of rd wok) in *. set (bv' := byteview_of rd' wok').
    set (rv := byteview_of rd (fun _ => true)) in *. set (rv' := byteview_of rd' (fun _ => true)).
    assert (BA1 : forall a, ~ D a -> bv' a = bv a) by (intros a Ha; exact (proj1 (BA a Ha))).
    assert (BA2 : forall a, ~ D a -> rv' a = rv a) by (intros a Ha; exact (proj2 (BA a Ha))).

    assert (CELLB : forall c k, In c (image s ++ footer_cells s) -> (k < mc_w c)%nat -> ~ D (loc_addr L (mc_loc c) + Z.of_nat k)).
    { intros c k Hc Hk HD. apply (D_fp _ HD).
      destruct (Zones2.cell_in_footprintI X R U s L HI HXr c Hc) as (e & He & [I1 I2]).
      unfold cell_range, crange in I1, I2. cbn [fst snd] in I1, I2.
      assert (ZK : Z.of_nat k < Z.of_nat (mc_w c)) by (apply Nat2Z.inj_lt; exact Hk).
      exists e. split; [exact He|]. lia. }
    assert (CE : forall c, In c (image s ++ footer_cells s) -> cell_holds L bv c -> cell_holds L bv' c).
    { intros c Hc Hh. apply (cell_holds_ext bv bv' c); [| exact (Zones2.cell_w_posI s c Hc) | exact Hh].
      intros k Hk. exact (BA1 _ (CELLB c k Hc Hk)). }
    assert (RVs : forall a, static_ng C a -> rv' a = rv a).
    { intros a Hs. apply BA2. intros HD. exact (D_static a HD Hs). }
    assert (ST : forall a0 w v, (forall k, (k < w)%nat -> static_ng C (a0 + Z.of_nat k)) -> holds rv a0 w v -> holds rv' a0 w v).
    { intros a0 w v Hk Hh. apply (holds_ext rv); [|exact Hh]. intros k Kk. exact (RVs _ (Hk k Kk)). }
    split; [exact HI|]. split; [exact HB|]. split; [exact HC|].
    split.
    { split; [split; [exact HL | split]|].
      - apply Forall_forall. intros c Hc. apply CE; [apply in_app_iff; left; exact Hc | exact (proj1 (Forall_forall _ _) HCI c Hc)].
      - intros x Hx. unfold bv' in BA1. rewrite (BA1 x ltac:(intros HD; exact (D_fp x HD (proj1 Hx)))). exact (HO x Hx).
      - apply Forall_forall. intros c Hc. apply CE; [apply in_app_iff; right; exact Hc | exact (proj1 (Forall_forall _ _) HF c Hc)]. }
    split; [exact HV|].
    split.
    { destruct HST as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & (gd & S9 & S10)).
      unfold statics_ok, mc_need_locks, mc_page_size, mc_auxv in *.
      split; [apply ST; [intros k Hk; unfold static_ng; cbn in Hk; lia | exact S1]|].
      split; [apply ST; [intros k Hk; unfold static_ng; cbn in Hk; lia | exact S2]|].
      split; [apply ST; [intros k Hk; unfold static_ng; cbn in Hk; lia | exact S3]|].
      split; [apply (holds_ext bv); [intros k Hk; apply BA1; intros HD; apply (D_static _ HD); unfold static_ng; cbn in Hk; lia | exact S4]|].
      split; [intros k Hk; rewrite RVs by (unfold static_ng; lia); exact (S5 k Hk)|].
      split; [intros k Hk; rewrite RVs by (unfold static_ng; lia); exact (S6 k Hk)|].
      split; [intros k Hk; rewrite RVs by (unfold static_ng; lia); exact (S7 k Hk)|].
      split; [intros k Hk; rewrite RVs by (unfold static_ng; lia); exact (S8 k Hk)|].

      assert (GR : forall j, (j < 8)%nat -> exists b, rv' (mc_chk_guard C + Z.of_nat j) = Some b /\ 0 <= b < 256).
      { intros j Hj. apply (RD' (mc_chk_guard C + Z.of_nat j) _ (fun HD => RDg _ HD ltac:(lia)) (S10 j Hj)). }
      destruct (holds_of_readable rv' (mc_chk_guard C) 8 GR) as [g' Hg'].
      exists g'. split; [|exact Hg']. apply ST; [intros k Hk; unfold static_ng; cbn in Hk; lia | exact S9]. }
    split.
    { exact HAUX. }
    split; [exact HLG|]. split; [exact HIMG|]. exact HMW.
  Qed.
  Hypothesis D_low : ltac2:(tb__ "0|0|
S0VD;R1A1S6R2S1dVL;A1A2F_;Fa;").
  Hypothesis RD : ltac2:(tb__ "0|1|
S0VD;R1A1S5S1eQ8A1M0G0S2SbG0A1Vrd';S1fQ40R3A2A1ScG0R1A2A3Lb;A2F_;Fa;").

  Theorem minvG_frame : ltac2:(tb__ "0|0|
S22VC;S23VX;VR;VU;A3S21Vs;VL;A2Vrd';Vwok';Vvm;A6").
  Proof using AG D_dec D_fp D_low D_static HMI HXr RD RDg.
    apply minvG_frame_core.
    pose proof HMI as (HI & HB & HC & ((HL & HCI & HO) & HF) & HV & HST & HA & HLG & HIMG & HMW). cbn [ma_s ma_L] in *.
    set (rv := byteview_of rd (fun _ => true)) in *. set (rv' := byteview_of rd' (fun _ => true)).
    assert (BA2 : forall a, ~ D a -> rv' a = rv a) by (intros a Ha; exact (proj2 (BA a Ha))).
    assert (RVs : forall a, static_ng C a -> rv' a = rv a).
    { intros a Hs. apply BA2. intros HD. exact (D_static a HD Hs). }
    assert (RHI : forall a, topL L <= a -> rv' a = rv a).
    { intros a Ha. apply BA2. intros HD. pose proof (D_low a HD). lia. }
    assert (AGH : forall b z, topL L <= b -> holds rv b 8 z -> holds rv' b 8 z).
    { intros b z Hb Hh. apply (holds_ext rv); [|exact Hh]. intros k Hk. apply RHI. lia. }
    intros Hf. destruct (HA Hf) as (av & q & n & A1 & A2 & A3 & A4 & A5 & A6 & Aav & Aq & Aq2 & Hn).
    exists av, q, n. unfold mc_auxv in *.
    split; [apply (holds_ext rv); [intros k Hk; apply RVs; unfold static_ng; cbn in Hk; lia | exact A1]|].
    split; [apply AGH; [lia | exact A2]|]. split; [apply AGH; [lia | exact A3]|]. split; [apply AGH; [lia | exact A4]|].
    split.
    { intros i Hi. destruct (A5 i Hi) as (k & v & B1 & B2 & B3 & B4). exists k, v.
      split; [apply AGH; [lia | exact B1]|]. split; [exact B2|]. split; [apply AGH; [lia | exact B3]|].
      intros Hk. destruct (B4 Hk) as [w Hw]. apply (holds_of_readable _ (v + 8) 8).
      intros j Hj. destruct (RD' (v + 8 + Z.of_nat j) _ (RD _) (Hw j Hj)) as (v' & E' & R'). exists v'. auto. }
    split.
    { destruct A6 as (t & Hnt & T0 & T1). exists t. split; [exact Hnt|]. split; [apply AGH; [lia | exact T0]|].
      intros i Hi. destruct (T1 i Hi) as (k & K1 & K2 & K3). exists k. split; [apply AGH; [lia | exact K1] | auto]. }
    repeat split; assumption.
  Qed.
End FG.
