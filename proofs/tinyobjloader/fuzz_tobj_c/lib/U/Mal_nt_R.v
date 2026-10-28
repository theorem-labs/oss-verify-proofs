(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "ex"; "not"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "ma_s"; "MA"; "ma_L"; "mkMA"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "addr_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "astate"; "region"; "ameta"; "IRet"; "RkMap"; "am_maplen"; "am_mem"; "am_sc"; "itree"; "nontrivial_free"; "page_round"; "prid"; "rg_kind"; "rg_len"; "rg_live"; "rkind"; "st_init_done"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init"; "segsU"; "@Corelib.Init.Datatypes"; "nat"; "prod"; "Some"; "pair"; "option"; "None"; "bool"; "true"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "rm"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT"; "xzomb"; "JL_nt"; "nt_stack"; "J_nt_pre"; "V_RES1"; "magree"; "zv"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@Corelib.Init.Peano"; "le"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "usedX"; "layout"; "ly_reg"; "region_of"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "V_RES"; "mem_kept_owned"; "rd_of"; "wok_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "ub_same"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFree"; "corr"; "fneed"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier"; "reach_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zomb"; "zomb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G3.Mal_fslow"; "JL_ntR"; "J_nt_preR"].
#[local] Ltac2 tb__ s := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymFrame SymSummary.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocWfInv MallocWfFrame MallocWfFree MallocLayout MallocIface MallocIfaceI MallocLaws
  Contract ContractI ContractNT NestTier Zomb FreeNtReal FreeNtRealN.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G5 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G6 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G5.Mal_nt_V10 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G6.Mal_nt_T OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G3.Mal_fslow.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma nt_stack_mono (a b : nat) : ltac2:(tb__ "0|0|
S33Va;Vb;A2S39S2dVa;A1S2dVb;A1A2F_;").
Proof. intros H. unfold nt_stack, NT_D. nia. Qed.
Lemma mkMA_eta (A : MA) : ltac2:(tb__ "0|0|
S1S7S9S6VA;A1S8VA;A1A2VA;A3").
Proof. destruct A; reflexivity. Qed.

Lemma zv_id X A g i U rd wok vm : ltac2:(tb__ "0|0|
S32SaVX;S21S20ScS5A2S22ScS5Vg;Vi;A4A2VU;VA;Vrd;Vwok;Vvm;A8S2bVX;S6VA;A1A2S1S7S31VX;VA;A2VA;A3F_;F_;").
Proof.
  intros HMI HXz. destruct A as [s L]. unfold zv. cbn [ma_s ma_L] in *.
  rewrite (zomb_id X s (proj1 (inv_keys (mig_I HMI)))); [reflexivity|].
  intros x Hx _. exact (HXz x Hx).
Qed.

Lemma J_nt_preR_pre X U A Kc rho tr md : ltac2:(tb__ "0|0|
S45S1eSaVX;VU;VA;VKc;Vrho;Vtr;Vmd;A9S2eS1eSaVX;VU;VA;VKc;Vrho;Vtr;Vmd;A9F_;").
Proof.

  intros (g & am & mv & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & _ & H10 & H11).
  exists g, am, mv. rewrite (zv_id X A g _ U _ _ _ H2 H4).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact (mig_I H2)|]. split; [exact H5|]. split; [exact H6|]. split; [exact H7|].
  split; [|split; [cbn [ma_s]; exact H9 | split; [exact H10 | exact H11]]].
  pose proof (nt_stack_mono (NestTier.tier (am_sc am)) 3 (NestTier.tier_le3 _)). lia.
Qed.

Section Post.
  Variables (X : list sptr) (U : Z -> Z) (A : MA) (Kc : list event -> Model -> Prop) (rho0 rho' : valuation) (tr : list event) (md : Model).
  Hypothesis HXz : xzomb X (ma_s A).
  Hypothesis ND : List.NoDup (keys (ma_s A)).
  Hypothesis HJL : ltac2:(tb__ "0|0|
S2cS1eSaVX;VU;VA;VKc;Vrho0;Vrho';Vtr;Vmd;Aa").

  Lemma sA_id : ltac2:(tb__ "0|1|
S1SdS43VX;S6VA;A1M0A2G0A3").
  Proof using HXz ND. apply (zomb_id X (ma_s A) ND). intros x Hx _. exact (HXz x Hx). Qed.

  Lemma JL_nt_RY : ltac2:(tb__ "0|d|
S2S7S7S2S2aQ40M0A1S23S2aQ8A1A1F_;M1G1S2S23S20S1fS5A2M2A1M3G3S0S32SaVX;S24S20ScS5A2A1VU;R3S3dS1eR2A2S3eS1eR2A2S3aVmd;A1A8S0S30S8VA;A1M4VX;R2S28Vrho';A1M5A4S0S2bVX;S6R3A1M6A2S0S1S35S8R3A1G4A3S0S1S25S1dG6A1S26A3S0S40VX;S6VA;A1M7G6A3S0S3fG7G6A2S0S42G6A1S0S4S0S1G3R1S24G2A1A3S0S1S5S29G0S27Vrho';S2fA2A2M8Z0M9A3S1S5S29G0S27Vrho';S3bA2A2MaG9A3A2A2S2S1fS1fS2SeSeS0S1G3R3S21G2S22S1fS5R2S1aR1A1MbA4A2A3S0S38G9G8A2S0S1S23SeA1S37S6R5A1R2A2S21SeR1A2A3S0S1S1cS19R1A1S11A3S0S1S25S1bR1A1S26A3S0S1S5GbS17G8A1A3S0S1S5S36S8R5A1R2A2GaA3ScSfS34VX;S6R7A1R2R1A4S38G9S12R2A1A2S3S1S1fS18S13R3A1A1R6A3A1F_;F_;Fa;Fq;A2A2A2A2A2A2A2Lrg;A2Lk;A2A2S0ScSfS1fS1S5SbG4R3A2S29G0S27Vrho0;PcA2A2A3S34VX;G7R4R3A4S33S41S14R4A1A1R3A2S1S15SdS20G3SdA2McA2S16R4R6S29G0S27Vrho0;PdA2A2G7A4S10SdGcS22G3SdR7S6R9A1A4A3A3F_;F_;F_;FF;Fam;Fg;S0S3cSaVA;R3S28Vrho0;A1G5A5VKc;Vtr;Vmd;A2A2A2A2A2A2A2A2A2A2A2A2Lr;A2Lmv';A2LA';A2").
  Proof using HJL HXz ND.
    destruct HJL as (A' & mv' & r & HMI & HZ & HL & Hinit & HIr' & Hxk & Hcorr & Hub & Hreach & Hres & Heq & Hkept & _ & HK).
    assert (E' : zomb X (ma_s A') = ma_s A').
    { apply (zomb_id X (ma_s A') (proj1 (inv_keys HIr'))). intros x Hx _. rewrite (Hxk x Hx). exact (HXz x Hx). }
    assert (EzA : zv X A = A) by (unfold zv; rewrite sA_id; apply mkMA_eta).
    assert (EzA' : zv X A' = A') by (unfold zv; rewrite E'; apply mkMA_eta).
    rewrite EzA' in HMI, Hreach. rewrite EzA, EzA' in Hkept.
    exists A', mv', r. split; [exact HMI|]. split; [exact HZ|].
    split; [rewrite <- E'; exact (xzomb_real X None U (ma_s A') HIr')|].
    split; [exact HL|]. split; [exact Hinit|]. split; [exact Hcorr|]. split; [exact Hub|]. split; [exact Hreach|].
    split; [exact Hres|]. split; [exact Heq|]. split; [exact Hkept | exact HK].
  Qed.
End Post.

Lemma JL_nt_R X U A Kc rho0 rho' tr md g i rd wok vm : ltac2:(tb__ "0|0|
S32SaVX;S21S20ScS5A2S22ScS5Vg;Vi;A4A2VU;VA;Vrd;Vwok;Vvm;A8S2bVX;S6VA;A1A2S2cS1eSaVX;VU;VA;VKc;Vrho0;Vrho';Vtr;Vmd;AaS44S1eSaVX;VU;VA;VKc;Vrho0;Vrho';Vtr;Vmd;AaF_;F_;F_;").
Proof.
  intros HMI HXz HJL.
  destruct (JL_nt_RY X U A Kc rho0 rho' tr md HXz (proj1 (inv_keys (mig_I HMI))) HJL)
    as (A' & mv' & r & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & Hres & _ & H10 & H11).
  exists A', mv'. repeat (split; [assumption|]). split; [|split; [exact H10 | exact H11]].
  destruct Hres as [(_ & L0 & B0)|(k & rg & _ & Hlen & R)]; [left; auto | right]. split; [exact Hlen|]. exists k, rg. exact R.
Qed.

Theorem nt_contractR_P_ok : nt_contractR_P.
Proof.
  intros ok X U A Kc rho (HokF & _ & _) n Hg w [Hsm HJ].
  pose proof HJ as (g & am & mv & _ & HMI & _ & HXz & _).
  apply (nt_sumI_frame ok X U A Kc rho HokF n); [|split; [exact Hsm | exact (J_nt_preR_pre _ _ _ _ _ _ _ HJ)]].
  intros w' (Lx & JLx & rho' & Hin & Hag & Hsm' & HJL). apply Hg.
  destruct Hin as [E|[]]. injection E as <- <-.
  exists (L_nt NTE_U), (JL_ntR segsU C_U X U A Kc), rho'.
  split; [left; reflexivity|]. split; [exact Hag|]. split; [exact Hsm'|]. exact (JL_nt_R _ _ _ _ _ _ _ _ _ _ _ _ _ HMI HXz HJL).
Qed.

Theorem nt_contractR_ex_P_ok : nt_contractR_ex_P.
Proof.
  intros X U A Kc rho _ w [Hsm HJ].
  pose proof HJ as (g & am & mv & _ & HMI & _ & HXz & _).
  destruct (nt_sumI_eframe X U A Kc rho w (conj Hsm (J_nt_preR_pre _ _ _ _ _ _ _ HJ))) as (w' & Hs & (Lx & JLx & rho' & Hin & Hag & Hsm' & HJL)).
  exists w'. split; [exact Hs|]. destruct Hin as [E|[]]. injection E as <- <-.
  exists (L_nt NTE_U), (JL_ntR segsU C_U X U A Kc), rho'.
  split; [left; reflexivity|]. split; [exact Hag|]. split; [exact Hsm'|]. exact (JL_nt_R _ _ _ _ _ _ _ _ _ _ _ _ _ HMI HXz HJL).
Qed.

Theorem nt_contractR_exd_P_ok : nt_contractR_exd_P.
Proof.
  intros g i X U A Kc rho w [Hsm HJ].
  pose proof HJ as (Hg & Hi & am & mv & HMI & HZ & HXz & Hu & HU & HR2g & Hdep & Hreach & _ & HK & Htop).
  assert (HJ' : J_nt_pre segsU C_U X U A Kc rho (w_tr w) (cfg_model (w_cfg w))).
  { exists g, am, mv. rewrite (zv_id X A g _ U _ _ _ HMI HXz). rewrite <- Hi.
    split; [exact Hg|]. split; [exact HMI|]. split; [exact HZ|]. split; [exact (mig_I HMI)|]. split; [exact Hu|]. split; [exact HU|]. split; [exact HR2g|].
    split; [|split; [cbn [ma_s]; exact Hreach | split; [exact HK | exact Htop]]].
    pose proof (nt_stack_mono (NestTier.tier (am_sc am)) 3 (NestTier.tier_le3 _)). lia. }
  destruct (nt_sumI_eframe X U A Kc rho w (conj Hsm HJ')) as (w' & Hs & (Lx & JLx & rho' & Hin & Hag & Hsm' & HJL)).
  exists w'. split; [exact Hs|]. destruct Hin as [E|[]]. injection E as <- <-.
  exists (L_nt NTE_U), (JL_ntRY segsU C_U g i X U A Kc), rho'.
  split; [left; reflexivity|]. split; [exact Hag|]. split; [exact Hsm'|].
  cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HJL |- *.
  destruct (JL_nt_RY X U A Kc rho rho' _ _ HXz (proj1 (inv_keys (mig_I HMI))) HJL)
    as (A' & mv' & r & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & Hres & Heq & H10 & H11).
  exists A', mv'. repeat (split; [assumption|]). split; [|split; [exact H10 | exact H11]].
  exists [], r. split.
  - rewrite <- Hi in Heq. pose proof (inv_groups (mig_I HMI) g am Hu) as (_ & _ & _ & GC & _).
    assert (Hsc0 : 0 <= am_sc am) by (destruct GC as [(E & _)|(R & _)]; lia).
    rewrite (Heq g am NEST_FUEL Hg Hu (fneed_le _ Hsc0)). reflexivity.
  - destruct Hres as [(-> & L0 & B0)|(k & rg & -> & Hlen & R)]; [left; auto | right]. exists k, rg. split; [reflexivity|]. split; [exact Hlen | exact R].
Qed.

Theorem nt_contractR_d_P_ok : nt_contractR_d_P.
Proof.
  intros ok g i X U A Kc rho HokF n Hg w [Hsm HJ].
  pose proof HJ as (Hg0 & Hi & am & mv & HMI & HZ & HXz & Hu & HU & HR2g & Hdep & Hreach & _ & HK & Htop).
  assert (HJ' : J_nt_pre segsU C_U X U A Kc rho (w_tr w) (cfg_model (w_cfg w))).
  { exists g, am, mv. rewrite (zv_id X A g _ U _ _ _ HMI HXz). rewrite <- Hi.
    split; [exact Hg0|]. split; [exact HMI|]. split; [exact HZ|]. split; [exact (mig_I HMI)|]. split; [exact Hu|]. split; [exact HU|]. split; [exact HR2g|].
    split; [|split; [cbn [ma_s]; exact Hreach | split; [exact HK | exact Htop]]].
    pose proof (nt_stack_mono (NestTier.tier (am_sc am)) 3 (NestTier.tier_le3 _)). lia. }
  destruct w as [trw [msw mdw]]. cbn [w_tr w_cfg fst snd cfg_model] in HJ'.
  apply (nt_sumI_frame ok X U A Kc rho HokF n); [|split; [exact Hsm | exact HJ']].
  intros w' (Lx & JLx & rho' & Hin & Hag & Hsm' & HJL). apply Hg.
  destruct Hin as [E|[]]. injection E as <- <-.
  exists (L_nt NTE_U), (JL_ntRY segsU C_U g i X U A Kc), rho'.
  split; [left; reflexivity|]. split; [exact Hag|]. split; [exact Hsm'|].
  destruct w' as [tr' [ms' md']]. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HJL |- *.
  destruct (JL_nt_RY X U A Kc rho rho' _ _ HXz (proj1 (inv_keys (mig_I HMI))) HJL)
    as (A' & mv' & r & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & Hres & Heq & H10 & H11).
  exists A', mv'. repeat (split; [assumption|]). split; [|split; [exact H10 | exact H11]].
  exists [], r. split.
  - rewrite <- Hi in Heq. pose proof (inv_groups (mig_I HMI) g am Hu) as (_ & _ & _ & GC & _).
    assert (Hsc0 : 0 <= am_sc am) by (destruct GC as [(E & _)|(R & _)]; lia).
    rewrite (Heq g am NEST_FUEL Hg0 Hu (fneed_le _ Hsc0)). reflexivity.
  - destruct Hres as [(-> & L0 & B0)|(k & rg & -> & Hlen & R)]; [left; auto | right]. exists k, rg. split; [reflexivity|]. split; [exact Hlen | exact R].
Qed.
