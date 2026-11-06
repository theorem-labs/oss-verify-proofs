(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "not"; "eq"; "or"; "ex"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "add"; "le"; "pow"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "loc_addr"; "image"; "loc"; "cell_holds"; "footprint"; "mc_loc"; "mc_w"; "sval_num"; "user_blocks"; "CTX_SIZE"; "alloc_owned"; "ly_ctx"; "mc_val"; "LMem"; "@Stdlib.Lists.List"; "In"; "@Corelib.Init.Datatypes"; "prod"; "app"; "fst"; "list"; "nat"; "option"; "None"; "bool"; "false"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "owned_mapped"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGrow.Grow"; "gmeets"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "st_init_done"; "@Corelib.Init.Specif"; "sumbool"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "vm_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "mkMA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "mc_ctx"; "mc_errno"; "auxv_ok"; "mc_chk_guard"; "mc_chk_guard_got"; "mc_ctz_tab"; "mc_img_hi"; "mc_img_lo"; "mc_libc"; "mc_lock"; "mc_med_cnt_tab"; "mc_replaced"; "mc_size_classes"; "mc_small_cnt_tab"; "statics_ok"; "vm_ok"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLayout MallocFooter NestTier MallocIface MallocIfaceI MallocLaws GapGeneric.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Grow.
  Variables (C : mconsts) (I I' : astate -> Prop) (s s' : astate) (L L' : layout).
  Variables (rd0 rd1 : word -> option byte) (wok0 wok1 : word -> bool) (vm vm' : VmMaps).
  Let bv0 : byteview := byteview_of rd0 wok0.
  Let bv1 : byteview := byteview_of rd1 wok1.
  Let rv0 : byteview := byteview_of rd0 (fun _ => true).
  Let rv1 : byteview := byteview_of rd1 (fun _ => true).

  Hypothesis HMI : ltac2:(tb__ "0|0|
S2fVC;VI;S2eVs;VL;A2Vrd0;Vwok0;Vvm;A6").

  Hypothesis HI' : I' s'.
  Hypothesis Hbounded' : bounded s'.
  Hypothesis Hlayout' : layout_ok L' s'.
  Hypothesis HLX : ltac2:(tb__ "0|0|
S2S5S17VL';A1S17VL;A1A3").
  Hypothesis Hub : ltac2:(tb__ "0|0|
S2S1eS1bS29S5A2A1S14Vs';A1S14Vs;A1A3").
  Hypothesis Hvm : ltac2:(tb__ "0|0|
S3fVL';Vs';Vvm';A3").
  Hypothesis Hledger : ledger_ok C vm'.
  Hypothesis Hres : ltac2:(tb__ "0|1|
S2S1eS1bS40Q40A1M0G0A2A1S2dVvm';A1S2dVvm;A1A3").

  Variable touched : Z -> Prop.
  Hypothesis touched_dec : ltac2:(tb__ "0|1|
S5S2bVtouched;R1A1M0S1G0A1A2Fx;").
  Definition gmeets (c : mcell) : Prop := ltac2:(tb__ "0|0|
S4S1fS1fS0S28R1S12Vc;A1A2Vtouched;S7ScVL';S11Vc;A1A2SaR1A1A2A1A2Lk;A2").

  Variable NEW : list (loc * Z).
  Hypothesis Hfp : ltac2:(tb__ "0|1|
S1bSeS5A2M0S1aG0R1S10Vs';A1A3S3S1aG0R2S10Vs;A1A3S1aG0R2VNEW;A3A2F_;Fe;").
  Hypothesis FPO : ltac2:(tb__ "0|2|
S1bSeS5A2M0S1aG0R1S10Vs;A1A3S1aG0R2S10Vs';A1A3S2S5ScVL';S1dSeS5R3A3M1A2ScVL;G1A2A3F_;F_;Fe;").
  Hypothesis UBO : ltac2:(tb__ "0|2|
S1bS29S5A2M0S1aG0R1S14Vs;A1A3S2S5ScVL';S19S1dS29S5R2A3A1M1A2ScVL;G1A2A3F_;Fb;").
  Hypothesis NEWT : ltac2:(tb__ "0|2|
S1bSeS5A2M0S5S1aG0R2VNEW;A3S0S8ScVL';S1dSeS5R3A3A2M1R2A2S6R2S7G1S24SeS5R3A3A2A2A2Vtouched;R3A1F_;F_;Fx;Fe;").

  Hypothesis V1 : ltac2:(tb__ "0|1|
S5S0S8Z0R1A2S6R1S9Z2Z40A2A2A2S1Vtouched;R2A1A1S0S2S20S5A1M0Vbv1;R3A1Vbv0;R3A1A3S2G0Vrv1;R3A1Vrv0;R3A1A3A2F_;F_;Fx;").
  Hypothesis VIN : ltac2:(tb__ "0|0|
SbS1aSbR1S1cSbSdVs';A1S25Vs';A1A3A3S27R2A1SfVL';Vbv1;R3A3F_;F_;Fc;").
  Hypothesis VM : ltac2:(tb__ "0|0|
S5S0S8Z0R1A2S6R1S9Z2Z40A2A2A2Vtouched;R2A1S16VL';Vs';R3A3S1S2S20S5A1Vbv1;R4A1S21S5A1A3A1F_;F_;F_;Fx;").

  Hypothesis OLD : ltac2:(tb__ "0|2|
SbS1aSbR1S1cSbSdVs';A1S25Vs';A1A3A3S1S27R2A1A1S0S1aSbR3S1cSbSdVs;A1S25Vs;A1A3A3S0S2S5ScVL';S11R3A1M0A2ScVL;G0A2A3S2S5S13VL';S18R3A1M1A2S13VL;G1A2A3A2A2F_;F_;Fc;").
  Hypothesis SPAN : ltac2:(tb__ "0|1|
SbS1aSbR1S1cSbSdVs';A1S25Vs';A1A3A3S0S6Z0ScVL';S11R2A1A2M0A2S6S7G0SaS12R2A1A1A2S9Z2Z3fA2A2A2F_;Fc;").
  Hypothesis OWNSPAN : ltac2:(tb__ "0|0|
S5S16VL';Vs';R1A3S0S6Z0R2A2S6R2S9Z2Z3fA2A2A2F_;Fx;").

  Lemma gmeets_dec c : ltac2:(tb__ "0|1|
S2bS27Vc;A1M0S1G0A1A2").
  Proof using touched_dec.
    unfold gmeets. induction (mc_w c) as [|w IH].
    - right. intros (k & Hk & _). lia.
    - destruct IH as [Y|N]; [left; destruct Y as (k & Hk & Ht); exists k; split; [lia|exact Ht]|].
      destruct (touched_dec (loc_addr L' (mc_loc c) + Z.of_nat w)) as [T|T].
      + left. exists w. split; [lia|exact T].
      + right. intros (k & Hk & Ht). destruct (Nat.eq_dec k w) as [->|]; [exact (T Ht)|]. apply N. exists k. split; [lia|exact Ht].
  Qed.

  Lemma cell_keepX c : ltac2:(tb__ "0|4|
SfVL;Vbv0;Vc;A3S1S27Vc;A1A1S2S5ScVL';S11Vc;A1M0A2M1ScVL;G0A2A3S2S5S13VL';S18Vc;A1M2A2S13VL;G2A2A3S6Z0G1A2S6S7G1SaS12Vc;A1M3A1A2S9Z2Z3fA2A2S28U0G3A2SfVL';Vbv1;Vc;A3F_;F_;F_;F_;F_;F_;F_;").
  Proof using V1.
    intros Hc Hm Ea Ev Hlo Hhi Hw.
    assert (B : forall k, (k < mc_w c)%nat -> bv1 (loc_addr L' (mc_loc c) + Z.of_nat k) = bv0 (loc_addr L (mc_loc c) + Z.of_nat k)).
    { intros k Hk. rewrite <- Ea. apply (proj1 (V1 (loc_addr L' (mc_loc c) + Z.of_nat k) ltac:(lia) ltac:(intros T; apply Hm; exists k; auto))). }
    unfold cell_holds in *. destruct (mc_val c).
    - intros j Hj. rewrite (B j Hj). cbn [sval_num] in *. exact (Hc j Hj).
    - intros j Hj. rewrite (B j Hj). rewrite Ev. exact (Hc j Hj).
    - destruct Hc as (b & Hb & Hm5). exists b. split; [|exact Hm5].
      specialize (B 0%nat Hw). rewrite Z.add_0_r in B. rewrite Z.add_0_r in B. rewrite B. exact Hb.
    - intros j Hj. rewrite (B j Hj). rewrite Ev. exact (Hc j Hj).
  Qed.

  Hypothesis WIDTH : ltac2:(tb__ "0|0|
SbS1aSbR1S1cSbSdVs';A1S25Vs';A1A3A3S28U0S12R2A1A2F_;Fc;").

  Lemma cells_postX : ltac2:(tb__ "0|1|
S0S2cSbSfVL';Vbv1;A2M0SdVs';A1A3S2cSbG0S25Vs';A1A3A2").
  Proof using HMI OLD SPAN V1 VIN WIDTH touched_dec.
    pose proof (mig_reprO HMI) as [[_ [HI0 _]] HF0]. cbn [ma_s ma_L] in HI0, HF0.
    assert (ALL : forall c, In c (image s' ++ footer_cells s') -> cell_holds L' bv1 c).
    { intros c Hin. destruct (gmeets_dec c) as [M|M]; [exact (VIN c Hin M)|].
      pose proof (SPAN c Hin) as [P1 P2]. destruct (OLD c Hin M) as (Hold & Ea & Ev).
      apply cell_keepX; [| exact M | exact Ea | exact Ev | exact P1 | exact P2 | exact (WIDTH c Hin)].
      apply in_app_iff in Hold as [Ho|Ho]; [exact (proj1 (Forall_forall _ _) HI0 c Ho) | exact (proj1 (Forall_forall _ _) HF0 c Ho)]. }
    split; apply Forall_forall; intros c Hc; apply ALL; apply in_app_iff; [left|right]; exact Hc.
  Qed.

  Lemma owned_postX : ltac2:(tb__ "0|0|
S26VL';Vs';Vbv1;A3").
  Proof using FPO HMI Hfp Hub NEWT OWNSPAN UBO V1 VM touched_dec.
    pose proof (mig_reprO HMI) as [[_ [_ HO0]] _]. cbn [ma_s ma_L] in HO0.
    intros x Hx. pose proof (OWNSPAN x Hx) as R.
    destruct (touched_dec x) as [T|T]; [apply VM; [lia | exact T | exact Hx]|].
    rewrite (proj1 (V1 x ltac:(lia) T)). apply HO0.
    destruct Hx as [(rg & Hrg & Hin) Hnu].
    destruct (Hfp rg Hrg) as [Hold|Hnew].
    - split.
      + exists rg. split; [exact Hold|]. rewrite <- (FPO rg Hold Hrg). exact Hin.
      + intros (b & Hb & Hxb). apply Hnu. exists b. rewrite Hub. split; [exact Hb|]. rewrite (UBO b Hb). exact Hxb.
    - exfalso. apply T. exact (NEWT rg x Hnew Hin).
  Qed.

  Hypothesis HS : statics_in_image C.
  Hypothesis NOSTAT : ltac2:(tb__ "0|2|
S5Vtouched;R1A1S0S8S37VC;A1R2A2S6R2S36VC;A1A2A2S3S0S8S30VC;A1M0R3A2S6R3S7G0S15A2A2A2S0S8S31VC;A1M1R3A2S6R3S7G1Z4A2A2A2A2F_;F_;Fx;").
  Hypothesis HSD : ltac2:(tb__ "0|d|
S5S3S0S8S30VC;A1M0R1A2S6R1S7G0S15A2A2A2S0S8S31VC;A1M1R1A2S6R1S7G1Z4M2A2A2A2A2S0S1S0S8S38VC;A1M3R2A2S6R2S7G3Z38A2A2A2A1S0S1S0S8S3bVC;A1M4R2A2S6R2S7G4G2A2A2A2A1S0S1S0S8S39VC;A1M5R2A2S6R2S7G5G2A2A2A2A1S0S1S0S8S3cVC;A1M6R2A2S6R2S7G6Z60A2A2A2A1S0S1S0S8S3dVC;A1M7R2A2S6R2S7G7Z1bA2A2A2A1S0S1S0S8S3aVC;A1M8R2A2S6R2S7G8G2A2A2A2A1S0S1S0S8S35VC;A1M9R2A2S6R2S7G9Z20A2A2A2A1S0S1S0S8S34VC;A1MaR2A2S6R2S7GaZ8MbA2A2A2A1S1S0S8S33VC;A1McR2A2S6R2S7GcGbA2A2A2A1A2A2A2A2A2A2A2A2F_;Fx;").

  Lemma statics_postX : ltac2:(tb__ "0|0|
S3eVC;Vrv1;Vbv1;A3").
  Proof using HMI HS HSD NOSTAT V1 touched_dec.
    exact (statics_post C I s L rd0 rd1 wok0 wok1 vm HMI touched touched_dec V1 HS NOSTAT HSD).
  Qed.

  Hypothesis AUXV : ltac2:(tb__ "0|0|
S2S22S2aVs';A1S23A3S32VC;VL';Vrv1;A3F_;").

  Hypothesis MAPS : maps_wf vm'.

  Theorem minv_postGX : ltac2:(tb__ "0|0|
S2fVC;VI';S2eVs';VL';A2Vrd1;Vwok1;Vvm';A6").
  Proof using AUXV FPO HI' HLX HMI HS HSD Hbounded' Hfp Hlayout' Hledger Hres Hub Hvm MAPS NEWT NOSTAT OLD OWNSPAN SPAN UBO V1 VIN VM WIDTH touched_dec.
    pose proof (mig_ctx HMI) as HC0. cbn [ma_s ma_L] in HC0.
    destruct cells_postX as [CI CF].
    split; [exact HI'|]. split; [exact Hbounded'|]. split; [cbn [ma_L]; rewrite HLX; exact HC0|].
    split; [split; [split; [exact Hlayout' | split; [exact CI | exact owned_postX]] | exact CF]|].
    split; [exact Hvm|]. split; [exact statics_postX|]. split; [exact AUXV | split; [exact Hledger |]].
    split; [| exact MAPS].
    intros x Hx. rewrite Hres. exact (mig_img HMI x Hx).
  Qed.
End Grow.
