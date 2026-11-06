(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "not"; "eq"; "or"; "ex"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "le"; "add"; "pow"; "of_nat"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "image"; "alloc_owned"; "cell_holds"; "mc_w"; "CTX_SIZE"; "loc_addr"; "mc_loc"; "footprint"; "loc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapShrink.GapS"; "sg_bv1"; "s_meets"; "sg_bv0"; "sg_rv1"; "sg_rv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "owned_mapped"; "@Corelib.Init.Datatypes"; "app"; "option"; "None"; "bool"; "nat"; "Some"; "false"; "list"; "prod"; "@Stdlib.Lists.List"; "In"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "mc_ctx"; "mc_errno"; "mc_img_hi"; "mc_img_lo"; "auxv_ok"; "byteview_of"; "mc_chk_guard"; "mc_chk_guard_got"; "mc_ctz_tab"; "mc_libc"; "mc_lock"; "mc_med_cnt_tab"; "mc_replaced"; "mc_size_classes"; "mc_small_cnt_tab"; "statics_ok"; "vm_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "st_init_done"; "@Corelib.Init.Specif"; "sumbool"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "mkMA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvG"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLayout MallocFooter MallocIface MallocIfaceI MallocLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section GapS.
  Variables (C : mconsts) (I I' : astate -> Prop) (s s' : astate) (L : layout).
  Variables (rd0 rd1 : word -> option byte) (wok0 wok1 : word -> bool) (vm : VmMaps).
  Definition sg_bv0 : byteview := byteview_of rd0 wok0.
  Definition sg_bv1 : byteview := byteview_of rd1 wok1.
  Definition sg_rv0 : byteview := byteview_of rd0 (fun _ => true).
  Definition sg_rv1 : byteview := byteview_of rd1 (fun _ => true).

  Hypothesis HMI : ltac2:(tb__ "0|0|
S3cVC;VI;S3bVs;VL;A2Vrd0;Vwok0;Vvm;A6").

  Hypothesis HI' : I' s'.
  Hypothesis Hbounded' : bounded s'.
  Hypothesis Hlayout' : layout_ok L s'.
  Hypothesis Hfp : ltac2:(tb__ "0|0|
S2S23S24S14SaA2A1S13Vs';A1S13Vs;A1A3").

  Variable newly : Z -> Prop.
  Hypothesis Hown : ltac2:(tb__ "0|0|
SaSdVL;Vs';R1A3S3SdVL;Vs;R2A3Vnewly;R2A1A2F_;Fx;").
  Hypothesis Hinit : ltac2:(tb__ "0|0|
S2S1fS38Vs';A1S38Vs;A1A3").
  Hypothesis Hvm : ltac2:(tb__ "0|0|
S37VL;Vs';Vvm;A3").

  Variable touched : Z -> Prop.
  Hypothesis touched_dec : ltac2:(tb__ "0|1|
SaS39Vtouched;R1A1M0S1G0A1A2Fx;").
  Definition s_meets (c : mcell) : Prop := ltac2:(tb__ "0|0|
S4S20S20S0S26R1SfVc;A1A2Vtouched;S7S11VL;S12Vc;A1A2S9R1A1A2A1A2Lk;A2").

  Hypothesis V1 : ltac2:(tb__ "0|1|
SaS0S6Z0R1A2S5R1S8Z2Z40A2A2A2S1Vtouched;R2A1A1S0S2S1dSaA1M0S15R3A1S17R3A1A3S2G0S18R3A1S19R3A1A3A2F_;F_;Fx;").
  Hypothesis VIN : ltac2:(tb__ "0|0|
SbS25SbR1S1cSbScVs';A1S1aVs';A1A3A3S16R2A1SeVL;S15R3A3F_;F_;Fc;").
  Hypothesis VM : ltac2:(tb__ "0|0|
SaS0S6Z0R1A2S5R1S8Z2Z40A2A2A2Vtouched;R2A1SdVL;Vs';R3A3S1S2S1dSaA1S15R4A1S1eSaA1A3A1F_;F_;F_;Fx;").
  Hypothesis VB : ltac2:(tb__ "0|0|
SaS0S6Z0R1A2S5R1S8Z2Z40A2A2A2S1Vtouched;R2A1A1Vnewly;R3A1S1S2S1dSaA1S17R4A1S1eSaA1A3A1F_;F_;F_;Fx;").

  Hypothesis OLD : ltac2:(tb__ "0|0|
SbS25SbR1S1cSbScVs';A1S1aVs';A1A3A3S1S16R2A1A1S25SbR3S1cSbScVs;A1S1aVs;A1A3A3F_;F_;Fc;").
  Hypothesis SPAN : ltac2:(tb__ "0|1|
SbS25SbR1S1cSbScVs';A1S1aVs';A1A3A3S0S5Z0S11VL;S12R2A1A2M0A2S5S7G0S9SfR2A1A1A2S8Z2Z3fA2A2A2F_;Fc;").
  Hypothesis OWNSPAN : ltac2:(tb__ "0|0|
SaSdVL;Vs';R1A3S0S5Z0R2A2S5R2S8Z2Z3fA2A2A2F_;Fx;").

  Lemma s_meets_dec c : ltac2:(tb__ "0|1|
S39S16Vc;A1M0S1G0A1A2").
  Proof using touched_dec.
    unfold s_meets. induction (mc_w c) as [|w IH].
    - right. intros (k & Hk & _). lia.
    - destruct IH as [Y|N]; [left; destruct Y as (k & Hk & Ht); exists k; split; [lia|exact Ht]|].
      destruct (touched_dec (loc_addr L (mc_loc c) + Z.of_nat w)) as [T|T].
      + left. exists w. split; [lia|exact T].
      + right. intros (k & Hk & Ht). destruct (Nat.eq_dec k w) as [->|]; [exact (T Ht)|]. apply N. exists k. split; [lia|exact Ht].
  Qed.

  Lemma s_cell_keep c : ltac2:(tb__ "0|2|
SeVL;S17Vc;A3S1S16Vc;A1A1S5Z0S11VL;S12Vc;A1A2M0A2S5S7G0S9SfVc;A1M1A1A2S8Z2Z3fA2A2S26U0G1A2SeVL;S15Vc;A3F_;F_;F_;F_;F_;").
  Proof using V1.
    intros Hc Hm Hlo Hhi Hw.
    assert (B : forall k, (k < mc_w c)%nat -> sg_bv1 (loc_addr L (mc_loc c) + Z.of_nat k) = sg_bv0 (loc_addr L (mc_loc c) + Z.of_nat k)).
    { intros k Hk. apply (proj1 (V1 (loc_addr L (mc_loc c) + Z.of_nat k) ltac:(lia) ltac:(intros T; apply Hm; exists k; auto))). }
    unfold cell_holds in *. destruct (mc_val c).
    - intros j Hj. rewrite (B j Hj). exact (Hc j Hj).
    - intros j Hj. rewrite (B j Hj). exact (Hc j Hj).
    - destruct Hc as (b & Hb & Hm5). exists b. split; [|exact Hm5].
      specialize (B 0%nat Hw). rewrite Z.add_0_r in B. rewrite B. exact Hb.
    - intros j Hj. rewrite (B j Hj). exact (Hc j Hj).
  Qed.

  Hypothesis WIDTH : ltac2:(tb__ "0|0|
SbS25SbR1S1cSbScVs';A1S1aVs';A1A3A3S26U0SfR2A1A2F_;Fc;").

  Lemma s_cells_post : ltac2:(tb__ "0|1|
S0S3aSbSeVL;S15A2M0ScVs';A1A3S3aSbG0S1aVs';A1A3A2").
  Proof using HMI OLD SPAN V1 VIN WIDTH touched_dec.
    pose proof (mig_reprO HMI) as [[_ [HI0 _]] HF0]. cbn [ma_s ma_L] in HI0, HF0.
    assert (ALL : forall c, In c (image s' ++ footer_cells s') -> cell_holds L sg_bv1 c).
    { intros c Hin. destruct (s_meets_dec c) as [M|M]; [exact (VIN c Hin M)|].
      pose proof (SPAN c Hin) as [P1 P2]. pose proof (OLD c Hin M) as Hold.
      apply s_cell_keep; [| exact M | exact P1 | exact P2 | exact (WIDTH c Hin)].
      apply in_app_iff in Hold as [Ho|Ho]; [exact (proj1 (Forall_forall _ _) HI0 c Ho) | exact (proj1 (Forall_forall _ _) HF0 c Ho)]. }
    split; apply Forall_forall; intros c Hc; apply ALL; apply in_app_iff; [left|right]; exact Hc.
  Qed.

  Lemma s_owned_post : ltac2:(tb__ "0|0|
S1bVL;Vs';S15A3").
  Proof using HMI Hown OWNSPAN V1 VB VM touched_dec.
    pose proof (mig_reprO HMI) as [[_ [_ HO0]] _]. cbn [ma_s ma_L] in HO0.
    intros x Hx. pose proof (OWNSPAN x Hx) as R.
    destruct (touched_dec x) as [T|T]; [apply VM; [lia | exact T | exact Hx]|].
    rewrite (proj1 (V1 x ltac:(lia) T)). destruct (Hown x Hx) as [Ho|Hn]; [apply HO0; exact Ho | apply VB; [lia | exact T | exact Hn]].
  Qed.

  Hypothesis HS : statics_in_image C.
  Hypothesis NOSTAT : ltac2:(tb__ "0|2|
SaVtouched;R1A1S0S6S2aVC;A1R2A2S5R2S29VC;A1A2A2S3S0S6S27VC;A1M0R3A2S5R3S7G0S10A2A2A2S0S6S28VC;A1M1R3A2S5R3S7G1Z4A2A2A2A2F_;F_;Fx;").

  Hypothesis HSD : ltac2:(tb__ "0|d|
SaS3S0S6S27VC;A1M0R1A2S5R1S7G0S10A2A2A2S0S6S28VC;A1M1R1A2S5R1S7G1Z4M2A2A2A2A2S0S1S0S6S30VC;A1M3R2A2S5R2S7G3Z38A2A2A2A1S0S1S0S6S33VC;A1M4R2A2S5R2S7G4G2A2A2A2A1S0S1S0S6S31VC;A1M5R2A2S5R2S7G5G2A2A2A2A1S0S1S0S6S34VC;A1M6R2A2S5R2S7G6Z60A2A2A2A1S0S1S0S6S35VC;A1M7R2A2S5R2S7G7Z1bA2A2A2A1S0S1S0S6S32VC;A1M8R2A2S5R2S7G8G2A2A2A2A1S0S1S0S6S2fVC;A1M9R2A2S5R2S7G9Z20A2A2A2A1S0S1S0S6S2eVC;A1MaR2A2S5R2S7GaZ8MbA2A2A2A1S1S0S6S2dVC;A1McR2A2S5R2S7GcGbA2A2A2A1A2A2A2A2A2A2A2A2F_;Fx;").

  Lemma s_bv_some_range (rd : word -> option byte) (wok : word -> bool) x v : ltac2:(tb__ "0|0|
S2S1dSaA1S2cVrd;Vwok;Vx;A3S21SaVv;A2A3S0S6Z0Vx;A2S5Vx;S8Z2Z40A2A2A2F_;").
  Proof using .
    unfold byteview_of. intros H. destruct (0 <=? x) eqn:E1; [apply Z.leb_le in E1|discriminate].
    destruct (x <? 2 ^ 64) eqn:E2; [apply Z.ltb_lt in E2|discriminate]. lia.
  Qed.

  Lemma s_static_keep lo n0 x : ltac2:(tb__ "0|4|
S0S6S2aVC;A1Vlo;A2S6S7Vlo;Vn0;A2M0S29VC;A1A2A2S0S6Vlo;Vx;A2S5Vx;G0A2A2SaS3S0S6S27VC;A1M1R1A2S5R1S7G1S10A2A2A2S0S6S28VC;A1M2R1A2S5R1S7G2Z4A2A2A2A2S1S0S6Vlo;R2A2S5R2G0A2A2A1F_;Fy;S0S6Z0Vx;A2S5Vx;S8Z2Z40A2A2A2S0S2S1dSaA1M3S18Vx;A1S19Vx;A1A3S2G3S15Vx;A1S17Vx;A1A3A2F_;F_;F_;F_;").
  Proof using NOSTAT V1 touched_dec.
    intros Hlo Hx Hmiss Hr. destruct (touched_dec x) as [T|T].
    - exfalso. destruct (NOSTAT x T ltac:(lia)) as [H|H]; exact (Hmiss x ltac:(auto) Hx).
    - destruct (V1 x Hr T) as [B R]. auto.
  Qed.

  Lemma s_statics_post : ltac2:(tb__ "0|0|
S36VC;S18S15A3").
  Proof using HMI HS HSD NOSTAT V1 touched_dec.
    pose proof (mig_statics HMI) as ST. cbn [ma_s ma_L] in ST. fold sg_rv0 sg_bv0 in ST.
    pose proof HS as HS0. unfold statics_in_image in HS0. cbn beta zeta delta [CTX_SIZE PGSZ UNIT] in HS0.
    destruct HS0 as (Ilibc & Irep & Isc & Ismall & Imed & Ictz & Igot & Iguard & Ilock & Ictx & Ierr & Hpg & Hceil).
    destruct ST as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & (gd & T9 & T10)).
    assert (HR : forall a0 w v lo n0, holds sg_rv0 a0 w v -> mc_img_lo C <= lo /\ lo + n0 <= mc_img_hi C -> lo <= a0 -> a0 + Z.of_nat w <= lo + n0 ->
              (forall y, (mc_ctx C <= y < mc_ctx C + CTX_SIZE \/ mc_errno C <= y < mc_errno C + 4) -> ~ (lo <= y < lo + n0)) ->
              holds sg_rv1 a0 w v).
    { intros a0 w v lo n0 Hh Hlo Ha Hw Hmiss j Hj. pose proof (Hh j Hj) as E.
      rewrite (proj1 (s_static_keep lo n0 (a0 + Z.of_nat j) Hlo ltac:(lia) Hmiss (s_bv_some_range _ _ _ _ E))). exact E. }
    assert (HB : forall a0 w v lo n0, holds sg_bv0 a0 w v -> mc_img_lo C <= lo /\ lo + n0 <= mc_img_hi C -> lo <= a0 -> a0 + Z.of_nat w <= lo + n0 ->
              (forall y, (mc_ctx C <= y < mc_ctx C + CTX_SIZE \/ mc_errno C <= y < mc_errno C + 4) -> ~ (lo <= y < lo + n0)) ->
              holds sg_bv1 a0 w v).
    { intros a0 w v lo n0 Hh Hlo Ha Hw Hmiss j Hj. pose proof (Hh j Hj) as E.
      rewrite (proj2 (s_static_keep lo n0 (a0 + Z.of_nat j) Hlo ltac:(lia) Hmiss (s_bv_some_range _ _ _ _ E))). exact E. }
    unfold CTX_SIZE in *.
    unfold statics_ok, mc_need_locks, mc_page_size in *.
    split; [apply (HR _ _ _ _ _ T1 Ilibc); [cbn; lia | cbn; lia | intros y Hy; pose proof (HSD y Hy); lia]|].
    split; [apply (HR _ _ _ _ _ T2 Ilibc); [cbn; lia | cbn; lia | intros y Hy; pose proof (HSD y Hy); lia]|].
    split; [apply (HR _ _ _ _ _ T3 Irep); [cbn; lia | cbn; lia | intros y Hy; pose proof (HSD y Hy); lia]|].
    split; [apply (HB _ _ _ _ _ T4 Ilock); [cbn; lia | cbn; lia | intros y Hy; pose proof (HSD y Hy); lia]|].
    split; [intros j Hj; pose proof (T5 j Hj) as E; rewrite (proj1 (s_static_keep _ _ (mc_size_classes C + Z.of_nat j) Isc ltac:(lia) ltac:(intros y Hy; pose proof (HSD y Hy); lia) (s_bv_some_range _ _ _ _ E))); exact E|].
    split; [intros j Hj; pose proof (T6 j Hj) as E; rewrite (proj1 (s_static_keep _ _ (mc_small_cnt_tab C + Z.of_nat j) Ismall ltac:(lia) ltac:(intros y Hy; pose proof (HSD y Hy); lia) (s_bv_some_range _ _ _ _ E))); exact E|].
    split; [intros j Hj; pose proof (T7 j Hj) as E; rewrite (proj1 (s_static_keep _ _ (mc_med_cnt_tab C + Z.of_nat j) Imed ltac:(lia) ltac:(intros y Hy; pose proof (HSD y Hy); lia) (s_bv_some_range _ _ _ _ E))); exact E|].
    split; [intros j Hj; pose proof (T8 j Hj) as E; rewrite (proj1 (s_static_keep _ _ (mc_ctz_tab C + Z.of_nat j) Ictz ltac:(lia) ltac:(intros y Hy; pose proof (HSD y Hy); lia) (s_bv_some_range _ _ _ _ E))); exact E|].
    exists gd. split.
    - apply (HR _ _ _ _ _ T9 Igot); [cbn; lia | cbn; lia | intros y Hy; pose proof (HSD y Hy); lia].
    - apply (HR _ _ _ _ _ T10 Iguard); [cbn; lia | cbn; lia | intros y Hy; pose proof (HSD y Hy); lia].
  Qed.

  Hypothesis AUXV : ltac2:(tb__ "0|0|
S2S1fS38Vs';A1S22A3S2bVC;VL;S18A3F_;").

  Theorem minv_postS : ltac2:(tb__ "0|0|
S3cVC;VI';S3bVs';VL;A2Vrd1;Vwok1;Vvm;A6").
  Proof using AUXV HI' HMI HS HSD Hbounded' Hlayout' Hown Hvm NOSTAT OLD OWNSPAN SPAN V1 VB VIN VM WIDTH touched_dec.
    pose proof (mig_ctx HMI) as HC0. pose proof (mig_ledger HMI) as HLG. cbn [ma_s ma_L] in HC0.
    destruct s_cells_post as [CI CF].
    split; [exact HI'|]. split; [exact Hbounded'|]. split; [exact HC0|].
    split; [split; [split; [exact Hlayout' | split; [exact CI | exact s_owned_post]] | exact CF]|].
    split; [exact Hvm|]. split; [exact s_statics_post|]. split; [exact AUXV | split; [exact HLG | split; [exact (mig_img HMI) | exact (mig_maps HMI)]]].
  Qed.
End GapS.
