(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init"; "segsU"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "ma_s"; "MA"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "of_nat"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_U"; "Pre_malloc"; "vm_insensitive"; "L_malloc_ok"; "top_high"; "top_var"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "IEC_U"; "Pre_as"; "@Corelib.Init.Datatypes"; "nat"; "nil"; "true"; "bool"; "cons"; "list"; "pair"; "prod"; "@Corelib.Init.Logic"; "and"; "False"; "True"; "eq"; "ex"; "@Corelib.Numbers.BinNums"; "Z"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sstate"; "valuation"; "rw"; "smatch"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "LQP"; "jpost"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractASK"; "B_as"; "Posts_asG"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "MMAP_THRESHOLD"; "sptr"; "st_init_done"; "@Corelib.Init.Peano"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AmPam"; "Pam_cnt"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv"; "DRV_OPS"; "JLi_ok"; "J_payload_ex"; "drvN"; "payload_cost"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractMK"; "JN_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.DrvReach"; "drv_inv"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "U0"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocSlowPost"; "slow_case"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier"; "reach_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "TR_ang"; "@stdpp.bitvector.definitions"; "bv_unsigned"].
#[local] Ltac2 tb__ s := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundR SymFrame SymSummary SymCall SymEntail Glue3 ExampleMemcpy.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CallocLib.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocWfArith MallocLayout MallocFooter NestTier
  MallocIface MallocIfaceI MallocLaws Contract ContractI ContractAM ContractAMT ContractDrv Pristine TRRulesK VmRoom
  AllocGroupPost MallocFastPost MallocSlowPost MallocDirectPost ContractASK ContractMK AmPam AmPriv DrvReach ZEval FreeNtPost TopGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G6 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_X1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G6.Mal_ameta_sum OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_X1.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].

Lemma top_high_pre A rho w : ltac2:(tb__ "0|0|
S22S0Vrho;S8S7A1Vw;A4ScVA;Vrho;A2SbVA;Vrho;A2F_;F_;").
Proof.
  intros Hsm HV.
  destruct (TopGlue.pre_window segsU rho malloc_stack (Pre_malloc EC_U) w ltac:(unfold malloc_stack; lia) Hsm
              ltac:(eexists; reflexivity) ltac:(intros p Hp; exact Hp)) as (Wlo & Wneg & Wf).
  exact (TopGlue.top_high_of_facts _ rho Wf Wlo Wneg HV).
Qed.

Definition direct_ok_stmt : Prop := ltac2:(tb__ "0|1|
S2S1cS1cS14S2cA1S2bOF_;F_;S20S9R2A1S4S27S3aQ40S21R2PcA2A2A2S2dS0S1eS0S31S0S3S11R7R6R5R4A7S8S7A1R3A4S23S0S1dR3S13S16S1fS24A2M0S15S1fS24SaS7A1S30S0S3R7R4A4A4S10G0A1A3A4A3F_;F_;Frho0;FKc;FX;Fk;FA;").

Section DRV.
Variables (A : MA) (k : Z).
Hypothesis HD : drvN C_U k A.

Lemma D_inv : ltac2:(tb__ "0|0|
S1bSfSfS17S35R1S1VA;A1A2S4S6R1A1S2fA2A2Lj;A2").
Proof using HD. destruct HD as (j & Hr & Hk & Hj). exists j. split; [exact (drv_reach_inv C_U j A Hr) | lia]. Qed.
Lemma D_init : ltac2:(tb__ "0|0|
S1aS12S29S1VA;A1A1S11A3").
Proof using HD. destruct D_inv as (j & (_ & Hi & _) & _). exact Hi. Qed.
Lemma D_full : full_all (ma_s A).
Proof using HD. destruct D_inv as (j & (_ & _ & _ & _ & Hf) & _). exact Hf. Qed.
Lemma D_cnt n : ltac2:(tb__ "0|0|
S2aVn;U3A2S2eVn;S1VA;A1A2F_;").
Proof using HD.
  intros Hn. destruct D_inv as (j & (_ & Hi & Hc & Hcj & _) & Hj). split; [exact Hi|]. unfold DRV_OPS in Hj. lia.
Qed.

Lemma D_slow n : ltac2:(tb__ "0|0|
S17S4Z0Vn;A2S5Vn;S27A2A2S37S1VA;A1Vn;A2F_;").
Proof using HD.
  intros Hn. split; [exact Hn|]. intros g am Hg M.
  exact (proj1 (D_full g am (mlookup_In _ _ _ M))).
Qed.
End DRV.

Section X3.
Hypothesis MS : malloc_slow_TRK_U.
Hypothesis AS : alloc_slot_TRK_U.
Hypothesis DO : direct_ok_stmt.

Lemma budget_payload n : ltac2:(tb__ "0|1|
S5Z0M0Vn;A2S4S25U3G0A2S33Vn;A1A2F_;").
Proof using . intros Hn. unfold B_as, payload_cost. cbn. lia. Qed.

Lemma AS_drv (A : MA) (k : Z) (Kc : list event -> Model -> Prop) (n : Z) : ltac2:(tb__ "0|0|
S32S3Vk;VA;A3S38S1VA;A1A1S9VKc;A1S20S39S0S25U3Z0A2S1eS0S34S0S3SdVA;VKc;Vn;A6SeSdA1R1A4S23S0S1dR1S26S0S3SdS18S19S10S28A1S36VA;VKc;A9A4A4Frho1;F_;F_;F_;").
Proof using AS.
  intros HD HR HVI rho1. pose proof (tr_rules_angelic segsU Kc) as RR.
  apply (trr_pre RR (SPJ segsU (J_as_pre segsU C_U [] U0 A Kc) (Pre_as IEC_U) rho1)); [intros w [Hsm HJ]; split; [exact Hsm | exact (proj1 HJ)]|].
  apply (trr_post RR _ (LQP segsU NF rho1 (Posts_asG segsU C_U IEC_U (False \/ False) (True \/ True) [] U0 A Kc))).
  { intros w' HL. apply (LQP_asG_mono (False \/ False) False (True \/ True) True); [tauto | tauto | exact HL]. }
  apply (AS Kc False True (TR_ang segsU) RR HVI Pam_cnt True False 0 ltac:(lia)
    (fun n sc s s' HP E => Pam_cnt_pure n s s' HP (try_avail_private sc s 0 s' E))
    (fun n s ktr m s' HP HY => Pam_cnt_am n s s' ktr m HP HY)
    (fun n sc s HP => Pam_cnt_pure n s (mm_pre sc s) HP (mm_pre_private sc s))
    (fun _ _ _ _ _ _ _ _ => I)
    (fun n X R U A' r1 HP => AM_cnt segsU C_U IEC_U alloc_meta_avail_ex_P_proof False n X R U A' Kc r1 HP)
    3%nat [] U0 A rho1 HR (fun _ => eq_refl) (D_cnt A k HD 3 ltac:(lia))).
  apply tier_le3_I || (unfold tier; repeat (destruct (_ : bool)); lia).
Qed.

Theorem malloc_payload_ex_true_of : malloc_payload_ex_U true.
Proof using AS DO MS.
  intros A k X Kc rho HVI. pose proof (tr_rules_angelic segsU Kc) as RR.
  intros w [Hsm HJ]. destruct w as [tr [ms md]]. cbn [w_tr w_cfg cfg_model] in HJ.
  pose proof HJ as (HMR & HD & Hn & HKc & Hroom & Htp & HTV). destruct (Hroom eq_refl) as [HVR HX].
  destruct (Z_lt_ge_dec (bv_unsigned (rw rho 12%positive)) MMAP_THRESHOLD) as [LT|GE].
  2:{
      exact (DO A k X Kc rho HVI ltac:(lia) (tr, mkCfg ms md) (conj Hsm HJ)). }
  pose proof (proj1 (MInvR_IR segsU C_U A rho md) HMR) as [_ HR].
  set (kk := B_as 3 0).
  pose proof (MS Kc False True (TR_ang segsU) RR HVI False True kk ltac:(apply B_as_nonneg; lia) A rho) as M.
  cbn zeta in M. specialize (M (D_slow A k HD (bv_unsigned (rw rho 12%positive)) ltac:(lia)) (AS_drv A k Kc _ HD HR HVI)).
  destruct M as [Hk M]. pose proof (budget_payload (bv_unsigned (rw rho 12%positive)) ltac:(lia)) as BI. fold kk in BI.
  specialize (M (X - kk) ltac:(lia)).
  destruct (M (tr, mkCfg ms md)) as (w' & Hsteps & HQ & HRw').
  { split.
    - split; [exact Hsm|]. cbn [w_tr w_cfg cfg_model]. split; [exact HMR|]. split; [exact HKc|]. split; [exact Htp|].
      split; [intros Hf; rewrite (D_init A k HD) in Hf; discriminate Hf|]. exact (top_high_pre A rho _ Hsm HTV).
    - unfold roomw. cbn [w_cfg cfg_model]. replace (X - kk + kk) with X by lia. exact HVR. }
  exists w'. split; [exact Hsteps|].
  destruct HQ as (L & JL & rho' & Hin & Hag & Hsm' & HJ').
  destruct Hin as [EQ | [EQ | []]]; injection EQ as <- <-; [exact (False_ind _ (proj1 HJ'))|].
  exists (L_malloc_ok EC_U), (JLi_ok segsU C_U A Kc), rho'.
  split; [left; reflexivity|]. split; [exact Hag|]. split; [exact Hsm'|].
  exact (JLm_ok_JLi segsU C_U _ _ _ _ _ _ (proj2 HJ')).
Qed.

End X3.
