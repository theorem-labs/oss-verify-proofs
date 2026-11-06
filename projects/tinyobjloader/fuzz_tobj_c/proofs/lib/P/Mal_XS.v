(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Init"; "segsP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "IEC_P"; "Pre_as"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_P"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "PGSZ"; "@Corelib.Init.Logic"; "True"; "False"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "LQP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "ok_sideK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesS"; "TR_angS"; "@Corelib.Init.Datatypes"; "list"; "nil"; "nat"; "option"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractASK"; "B_as"; "Posts_asG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractMK"; "JN_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "ma_s"; "MA"; "MA_init"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "U0"; "@Stdlib.ZArith.BinInt.Z"; "mul"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM"; "J_am_pre"; "Pre_am"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAMT"; "Posts_amG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv"; "drvN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier"; "reach_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Mal_ameta_AMX"; "Pam_init"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundR SymFrame SymSummary SymCall SymEntail Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CallocLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocWfArith MallocLayout MallocFooter NestTier
  MallocIface MallocIfaceI MallocLaws Contract ContractI ContractAM ContractAMT ContractDrv Pristine TRRulesK VmRoom
  AllocGroupPost MallocFastPost MallocSlowPost MallocDirectPost ContractASK ContractMK AmPam AmPriv DrvReach ZEval FreeNtPost TopGlue
  RoomS TRRulesS HeapS ContractS.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Mal_ameta__G6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Mal_ameta_AMX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Mal_X1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Mal_X3
  OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Mal_ameta_S OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Mal_mdirect_S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Mal_ameta__G6.Mal_ameta_IN3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Mal_ameta__G6.Mal_ameta_sum
  OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Mal_ameta_AMX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Mal_X1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Mal_X3
  OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Mal_ameta_S OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Mal_mdirect_S.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].

Section X3S.
Hypothesis MS : malloc_slow_TRK_P.
Hypothesis AS : alloc_slot_TRK_P.

Lemma AS_drvS (ok : world -> Prop) (A : MA) (k : Z) (Kc : list event -> Model -> Prop) (n : Z) : ltac2:(tb__ "0|0|
SdS0Vok;VKc;A3S22S3Vk;VA;A3S23S17VA;A1A1SbSeS0Vok;S14U3Z0A2SaS0S16S0S3S1VA;VKc;Vn;A6S2S1A1R1A4ScS0S9R1S15S0S3S1S7S6S10S4A1S1aVA;VKc;A9A4A5Frho1;F_;F_;F_;").
Proof using AS.
  intros HS HD HR rho1. pose proof (tr_rules_angelicS segsP Kc ok HS) as RR. pose proof HS as (_ & _ & HVI).
  apply (trr_pre RR (SPJ segsP (J_as_pre segsP C_P [] U0 A Kc) (Pre_as IEC_P) rho1)); [intros w [Hsm HJ]; split; [exact Hsm | exact (proj1 HJ)]|].
  apply (trr_post RR _ (LQP segsP NF rho1 (Posts_asG segsP C_P IEC_P (False \/ False) (True \/ True) [] U0 A Kc))).
  { intros w' HL. apply (LQP_asG_mono (False \/ False) False (True \/ True) True); [tauto | tauto | exact HL]. }
  apply (AS Kc False True (TR_angS segsP ok) RR HVI Pam_cnt True False 0 ltac:(lia)
    (fun n sc s s' HP E => Pam_cnt_pure n s s' HP (try_avail_private sc s 0 s' E))
    (fun n s ktr m s' HP HY => Pam_cnt_am n s s' ktr m HP HY)
    (fun n sc s HP => Pam_cnt_pure n s (mm_pre sc s) HP (mm_pre_private sc s))
    (fun _ _ _ _ _ _ _ _ => I)
    (fun n X R U A' r1 HP => AM_cntS segsP C_P IEC_P alloc_meta_avail_P_proof ok Kc HS False n X R U A' r1 HP)
    3%nat [] U0 A rho1 HR (fun _ => eq_refl) (D_cnt A k HD 3 ltac:(lia))).
  apply tier_le3_I || (unfold tier; repeat (destruct (_ : bool)); lia).
Qed.

Theorem malloc_payload_S_of : malloc_payload_S_P.
Proof using AS MS.
  intros ok A k X Kc rho HS. pose proof (tr_rules_angelicS segsP Kc ok HS) as RR. pose proof HS as (_ & _ & HVI).
  apply triple_inh. intros [tr [ms md]] [Hsm HJ]. cbn [w_tr w_cfg cfg_model] in HJ.
  pose proof HJ as (HMR & HD & Hn & HKc & [HVR HX] & Htp & HTV).
  destruct (Z_lt_ge_dec (bv_unsigned (rw rho 12%positive)) MMAP_THRESHOLD) as [LT|GE].
  2:{   exact (malloc_direct_ok_S_P ok A k X Kc rho HS ltac:(unfold MallocModel.MMAP_THRESHOLD; unfold MMAP_THRESHOLD in GE; lia)). }
  pose proof (proj1 (MInvR_IR segsP C_P A rho md) HMR) as [_ HR].
  set (kk := B_as 3 0).
  pose proof (MS Kc False True (TR_angS segsP ok) RR HVI False True kk ltac:(apply B_as_nonneg; lia) A rho) as M.
  cbn zeta in M. specialize (M (D_slow A k HD (bv_unsigned (rw rho 12%positive)) ltac:(lia)) (AS_drvS ok A k Kc _ HS HD HR)).
  destruct M as [Hk M]. pose proof (budget_payload (bv_unsigned (rw rho 12%positive)) ltac:(lia)) as BI. fold kk in BI.
  specialize (M (X - kk) ltac:(lia)).
  eapply triple_conseq; [| | exact M].
  - intros w [Hsm' HJ']. destruct w as [tr' [ms' md']]. cbn [w_tr w_cfg cfg_model] in HJ'.
    pose proof HJ' as (HMR' & _ & _ & HKc' & [HVR' _] & Htp' & HTV').
    split.
    + split; [exact Hsm'|]. cbn [w_tr w_cfg cfg_model]. split; [exact HMR'|]. split; [exact HKc'|]. split; [exact Htp'|].
      split; [intros Hf; rewrite (D_init A k HD) in Hf; discriminate Hf|]. exact (top_high_pre A rho _ Hsm' HTV').
    + unfold roomwS. cbn [w_cfg cfg_model]. replace (X - kk + kk) with X by lia. exact HVR'.
  - intros w' [HQ HRw'].
    destruct HQ as (L & JL & rho' & Hin & Hag & Hsm' & HJ').
    destruct Hin as [EQ | [EQ | []]]; injection EQ as <- <-; [exact (False_ind _ (proj1 HJ'))|].
    exists (L_malloc_ok EC_P), (JLi_ok segsP C_P A Kc), rho'.
    split; [left; reflexivity|]. split; [exact Hag|]. split; [exact Hsm'|].
    exact (JLm_ok_JLi segsP C_P _ _ _ _ _ _ (proj2 HJ')).
Qed.
End X3S.

Section X1S.
Hypothesis MS : malloc_slow_TRK_P.
Hypothesis AS : alloc_slot_TRK_P.

Theorem AM_initS : ltac2:(tb__ "0|0|
S1eOF_;SfS1dA1S1cOF_;F_;SdS0R2R1A3OS11SfS4A1S12S13S4S8A2A1S8S8F_;S18SbS24R6S17R2A1A2SeS0RbS1bZ2S5A2SaS0S1fS0S3R6R5R4R3RaA7S20S1A1R2A4ScS0S9R2S21S0S3S1R8S6R6R5R4R3RaAaA4A5F_;Frho1;FA;FU;FR;FX;Fn;FNG;F_;FKc;Fok;").
Proof using .
  intros ok Kc HS NG n X R U A rho1 [[(P1 & P2 & _ & _) _] | HC].
  - exact (am_IN_S auxv_brk0_P ok Kc HS NG X R U A rho1 P1 P2).
  - apply ((trr_mono (tr_rules_angelicS segsP Kc ok HS)) 0 (2 * PGSZ)); [unfold PGSZ; lia|].
    exact (AM_cntS segsP C_P IEC_P alloc_meta_avail_P_proof ok Kc HS NG n X R U A rho1 HC).
Qed.

Lemma AS_initS (ok : world -> Prop) (Kc : list event -> Model -> Prop) brk0 : ltac2:(tb__ "0|1|
SdS0Vok;VKc;A3SbSeS0Vok;S14U0S1bZ2S5A2A2SaS0S16S0S3S1S19S3Vbrk0;A2M0VKc;Z10000A6S2S1A1R1A4ScS0S9R1S15S0S3S1S7S6S10S4A1S1aG0VKc;A9A4A5Frho1;F_;").
Proof using AS.
  intros HS rho1. pose proof (tr_rules_angelicS segsP Kc ok HS) as RR. pose proof HS as (_ & _ & HVI).
  apply (trr_inhP RR); [apply B_as_nonneg; unfold PGSZ; lia|]. intros w [Hsm HJ].
  pose proof HJ as (HJas & H12 & H13). cbn [ma_s MA_init] in H12. rewrite class_init in H12.
  exists (SPJ segsP (J_as_pre segsP C_P [] U0 (MA_init C_P brk0) Kc) (Pre_as IEC_P) rho1). split; [split; [exact Hsm | exact HJas]|].
  apply (trr_post RR _ (LQP segsP NF rho1 (Posts_asG segsP C_P IEC_P (False \/ False) (True \/ True) [] U0 (MA_init C_P brk0) Kc))).
  { intros w' HL. apply (LQP_asG_mono (False \/ False) False (True \/ True) True); [tauto | tauto | exact HL]. }
  apply (AS Kc False True (TR_angS segsP ok) RR HVI Pam_init True False (2 * PGSZ) ltac:(unfold PGSZ; lia)
    (fun n sc s s' HP E => Pam_init_pure n s s' HP (try_avail_private sc s 0 s' E))
    (fun n s ktr m s' HP HY => Pam_init_am n s s' ktr m HP HY)
    (fun n sc s HP => Pam_init_pure n s (mm_pre sc s) HP (mm_pre_private sc s))
    (fun _ _ _ _ _ _ _ _ => I)
    (fun n X R U A' r1 HP => AM_initS ok Kc HS False n X R U A' r1 HP)
    0%nat [] U0 (MA_init C_P brk0) rho1 (reach_ok_nometas init_state eq_refl) (fun _ => eq_refl) (Pam_init_start 0 ltac:(lia))).
  rewrite H12, tier_44. lia.
Qed.

Theorem malloc_init_S_of : malloc_init_S_P.
Proof using AS MS.
  intros ok brk0 X Kc rho HS. pose proof (tr_rules_angelicS segsP Kc ok HS) as RR. pose proof HS as (_ & _ & HVI).
  apply triple_inh. intros [tr [ms md]] [Hsm HJ]. cbn [w_tr w_cfg cfg_model] in HJ.
  destruct HJ as (PRQ & E12 & HKc & [HVR HX] & HAV & HTV).
  set (k := B_as 0 (2 * PGSZ)).
  pose proof (MS Kc False True (TR_angS segsP ok) RR HVI False True k ltac:(apply B_as_nonneg; unfold PGSZ; lia) (MA_init C_P brk0) rho) as M.
  cbn zeta in M. rewrite E12 in M. cbn [ma_s MA_init] in M. specialize (M slow_init (AS_initS ok Kc brk0 HS)).
  destruct M as [Hk M]. pose proof budget_init as BI. fold k in BI.
  specialize (M (X - k) ltac:(lia)).
  eapply triple_conseq; [| | exact M].
  - intros w [Hsm' HJ']. destruct w as [tr' [ms' md']]. cbn [w_tr w_cfg cfg_model] in HJ'.
    destruct HJ' as (PRQ' & _ & HKc' & [HVR' _] & HAV' & HTV').
    pose proof (minv_pristine_P brk0 rho md' PRQ') as (HMR' & _ & _).
    split.
    + split; [exact Hsm'|]. cbn [w_tr w_cfg cfg_model]. split; [exact HMR'|]. split; [exact HKc'|].
      split; [exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PRQ')))))))))))))))))))|].
      split; [intros _; split; [exact HAV' | reflexivity]|]. exact (top_high_init brk0 rho _ Hsm' HTV').
    + unfold roomwS. cbn [w_cfg cfg_model]. replace (X - k + k) with X by lia. exact HVR'.
  - intros w' [HQ HRw'].
    destruct HQ as (L & JL & rho' & Hin & Hag & Hsm' & HJ').
    destruct Hin as [EQ | [EQ | []]]; injection EQ as <- <-; [exact (False_ind _ (proj1 HJ'))|].
    destruct HJ' as [_ (A' & l1 & l2 & HM' & Hi' & HB' & HB & HK & (ktr & HR) & HKc')].
    exists (L_malloc_ok EC_P), (JLdS_ok segsP C_P (MA_init C_P brk0) DRV_OPS (X - init_cost) Kc), rho'.
    split; [left; reflexivity|]. split; [exact Hag|]. split; [exact Hsm'|].
    exists A', l1, l2. split; [exact HM'|]. split; [split; [exact Hi' | exact (malloc_rel_top_kept _ _ _ _ _ HR)]|].
    split.
    {
      exists 0%nat. split; [|unfold DRV_OPS; lia]. rewrite E12 in HR. apply (DR_init C_P brk0 ktr _ A' HR).

      pose proof (smatch_facts_hold segsP _ _ _ Hsm') as HF. unfold L_malloc_ok in HF. cbn [ss_facts] in HF.
      pose proof (proj1 (Forall_forall _ _) HF (SPNot (SPBranch BC_EQ (SVar V_RES) (SLit 0))) ltac:(cbn; tauto)) as NZ.
      rewrite (holds_zholds rho') in NZ by reflexivity. cbn [zholds zcond zeval] in NZ. unfold zr_of in NZ.
      pose proof (urange (rw rho' V_RES)) as UR. rewrite Z.mod_small in NZ by lia. change (0 mod 2 ^ 64) with 0 in NZ.
      intros E0. rewrite E0 in NZ. exact (NZ eq_refl). }
    split.
    { unfold roomwS in HRw'. destruct w' as [tr' [ms' md']]. cbn [w_cfg cfg_model] in HRw' |- *.
      apply (vm_roomS_mono md' (X - k)); [lia | exact HRw']. }
    split; [exact HB'|]. split; [exact HB|]. split; [exact HK|exact HKc'].
Qed.
End X1S.
