(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init"; "segsU"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "IEC_U"; "Pre_as"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "LQP"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractASK"; "Posts_asG"; "B_as"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA_init"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "PGSZ"; "sptr"; "@Stdlib.ZArith.BinInt.Z"; "mul"; "le"; "@Corelib.Init.Datatypes"; "nil"; "@Corelib.Init.Logic"; "False"; "True"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "smatch"; "valuation"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_U"; "Pre_malloc"; "top_high"; "top_var"; "vm_insensitive"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv"; "init_cost"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractMK"; "JN_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "U0"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "TR_ang"].
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
  AllocGroupPost MallocFastPost MallocSlowPost ContractASK ContractMK AmPam AmPriv DrvReach ZEval FreeNtPost TopGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G6 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta_AMX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G6.Mal_ameta_IN3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta_AMX OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G6.Mal_ameta_sum.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].

Lemma LQP_asG_mono (Nf Nf' Og Og' : Prop) X U A Kc rho w : ltac2:(tb__ "0|0|
VNf;VNf';F_;VOg;VOg';F_;S5S0S4Vrho;S6S0S1S2VNf;VOg;VX;VU;VA;VKc;A9Vw;A5S5S0S4Vrho;S6S0S1S2VNf';VOg';VX;VU;VA;VKc;A9Vw;A5F_;F_;F_;").
Proof.
  intros HN HO (L & JL & rho' & Hin & Hag & Hsm & HJ).
  destruct Hin as [EQ | [EQ | []]]; injection EQ as <- <-.
  - exists (L_as_fail IEC_U), (JL_as_failG segsU C_U Nf' X U A Kc), rho'. split; [left; reflexivity|].
    split; [exact Hag|]. split; [exact Hsm|]. split; [exact (HN (proj1 HJ)) | exact (proj2 HJ)].
  - exists (L_as_ok IEC_U), (JL_as_okG segsU C_U Og' X U A Kc), rho'. split; [right; left; reflexivity|].
    split; [exact Hag|]. split; [exact Hsm|]. split; [exact (HO (proj1 HJ)) | exact (proj2 HJ)].
Qed.

Lemma class_init : malloc_class init_state 65536 = 44.
Proof. vm_compute. reflexivity. Qed.
Lemma tier_44 : tier 44 = 0%nat. Proof. reflexivity. Qed.
Lemma slow_init : slow_case init_state 65536.
Proof.
  split; [unfold MMAP_THRESHOLD; lia|]. intros g am Hg _. exfalso. rewrite class_init in Hg. cbn in Hg. discriminate Hg.
Qed.
Lemma budget_init : ltac2:(tb__ "0|0|
ScS7U0SbZ2S9A2A2S18A2").
Proof. unfold B_as, PGSZ, init_cost. cbn. lia. Qed.

Lemma top_high_init brk0 rho w : ltac2:(tb__ "0|1|
S11S0Vrho;S14S13A1Vw;A4S16S8S1Vbrk0;A2M0Vrho;A2S15G0Vrho;A2F_;F_;").
Proof.
  intros Hsm HV.
  destruct (TopGlue.pre_window segsU rho malloc_stack (Pre_malloc EC_U) w ltac:(unfold malloc_stack; lia) Hsm
              ltac:(eexists; reflexivity) ltac:(intros p Hp; exact Hp)) as (Wlo & Wneg & Wf).
  exact (TopGlue.top_high_of_facts _ rho Wf Wlo Wneg HV).
Qed.

Section X1T.
Hypothesis MS : malloc_slow_TRK_U.
Hypothesis AS : alloc_slot_TRK_U.

Lemma AS_init (Kc : list event -> Model -> Prop) brk0 : ltac2:(tb__ "0|1|
S17VKc;A1S12S1bS0S7U0SbZ2S9A2A2S10S0S19S0S1S2S8S1Vbrk0;A2M0VKc;Z10000A6S3S2A1R1A4S5S0S4R1S6S0S1S2SeSfSdSaA1S1aG0VKc;A9A4A4Frho1;F_;").
Proof using AS.
  intros HVI rho1. pose proof (tr_rules_angelic segsU Kc) as RR.
  apply (trr_inhP RR); [apply B_as_nonneg; unfold PGSZ; lia|]. intros w [Hsm HJ].
  pose proof HJ as (HJas & H12 & H13). cbn [ma_s MA_init] in H12. rewrite class_init in H12.
  exists (SPJ segsU (J_as_pre segsU C_U [] U0 (MA_init C_U brk0) Kc) (Pre_as IEC_U) rho1). split; [split; [exact Hsm | exact HJas]|].
  apply (trr_post RR _ (LQP segsU NF rho1 (Posts_asG segsU C_U IEC_U (False \/ False) (True \/ True) [] U0 (MA_init C_U brk0) Kc))).
  { intros w' HL. apply (LQP_asG_mono (False \/ False) False (True \/ True) True); [tauto | tauto | exact HL]. }
  apply (AS Kc False True (TR_ang segsU) RR HVI Pam_init True False (2 * PGSZ) ltac:(unfold PGSZ; lia)
    (fun n sc s s' HP E => Pam_init_pure n s s' HP (try_avail_private sc s 0 s' E))
    (fun n s ktr m s' HP HY => Pam_init_am n s s' ktr m HP HY)
    (fun n sc s HP => Pam_init_pure n s (mm_pre sc s) HP (mm_pre_private sc s))
    (fun _ _ _ _ _ _ _ _ => I)
    (fun n X R U A' r1 HP => AM_init auxv_brk0_P False n X R U A' Kc r1 HVI HP)
    0%nat [] U0 (MA_init C_U brk0) rho1 (reach_ok_nometas init_state eq_refl) (fun _ => eq_refl) (Pam_init_start 0 ltac:(lia))).
  rewrite H12, tier_44. lia.
Qed.

Theorem malloc_init_ex_true_of : malloc_init_ex_U true.
Proof using AS MS.
  intros brk0 X Kc rho HVI. pose proof (tr_rules_angelic segsU Kc) as RR.
  intros w [Hsm HJ]. destruct w as [tr [ms md]]. cbn [w_tr w_cfg cfg_model] in HJ.
  destruct HJ as (PRQ & E12 & HKc & Hroom & HAV & HTV). destruct (Hroom eq_refl) as [HVR HX].
  pose proof (minv_pristine_U brk0 rho md PRQ) as (HMR & HB0 & Hinit0).
  set (k := B_as 0 (2 * PGSZ)).
  pose proof (MS Kc False True (TR_ang segsU) RR HVI False True k ltac:(apply B_as_nonneg; unfold PGSZ; lia) (MA_init C_U brk0) rho) as M.
  cbn zeta in M. rewrite E12 in M. cbn [ma_s MA_init] in M. specialize (M slow_init (AS_init Kc brk0 HVI)).
  destruct M as [Hk M]. pose proof budget_init as BI. fold k in BI.
  specialize (M (X - k) ltac:(lia)).
  destruct (M (tr, mkCfg ms md)) as (w' & Hsteps & HQ & HRw').
  { split.
    - split; [exact Hsm|]. cbn [w_tr w_cfg cfg_model]. split; [exact HMR|]. split; [exact HKc|].
      split; [exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PRQ)))))))))))))))))))|].
      split; [intros _; split; [exact HAV | reflexivity]|]. exact (top_high_init brk0 rho _ Hsm HTV).
    - unfold roomw. cbn [w_cfg cfg_model]. replace (X - k + k) with X by lia. exact HVR. }
  exists w'. split; [exact Hsteps|].
  destruct HQ as (L & JL & rho' & Hin & Hag & Hsm' & HJ').
  destruct Hin as [EQ | [EQ | []]]; injection EQ as <- <-; [exact (False_ind _ (proj1 HJ'))|].
  destruct HJ' as [_ (A' & l1 & l2 & HM' & Hi' & HB' & HB & HK & (ktr & HR) & HKc')].
  exists (L_malloc_ok EC_U), (JLd_ok segsU C_U (MA_init C_U brk0) DRV_OPS (X - init_cost) Kc), rho'.
  split; [left; reflexivity|]. split; [exact Hag|]. split; [exact Hsm'|].
  exists A', l1, l2. split; [exact HM'|]. split; [split; [exact Hi' | exact (malloc_rel_top_kept _ _ _ _ _ HR)]|].
  split.
  {
    exists 0%nat. split; [|unfold DRV_OPS; lia]. rewrite E12 in HR. apply (DR_init C_U brk0 ktr _ A' HR).

    pose proof (smatch_facts_hold segsU _ _ _ Hsm') as HF. unfold L_malloc_ok in HF. cbn [ss_facts] in HF.
    pose proof (proj1 (Forall_forall _ _) HF (SPNot (SPBranch BC_EQ (SVar V_RES) (SLit 0))) ltac:(cbn; tauto)) as NZ.
    rewrite (holds_zholds rho') in NZ by reflexivity. cbn [zholds zcond zeval] in NZ. unfold zr_of in NZ.
    pose proof (urange (rw rho' V_RES)) as UR. rewrite Z.mod_small in NZ by lia. change (0 mod 2 ^ 64) with 0 in NZ.
    intros E0. rewrite E0 in NZ. exact (NZ eq_refl). }
  split; [|split; [exact HB'|split; [exact HB|split; [exact HK|exact HKc']]]].
  unfold roomw in HRw'. destruct w' as [tr' [ms' md']]. cbn [w_cfg cfg_model] in HRw' |- *.
  apply (vm_room_mono md' (X - k)); [lia | exact HRw'].
Qed.
End X1T.

Definition PhiF (_ : nat) (s : astate) : Prop := full_all s.

Lemma PhiF_ta0 : Phi_ta0_stmt PhiF.
Proof. intros n sc s s' HP E. exact (proj2 (try_avail_full0 sc s 0 s' HP E)). Qed.
Lemma PhiF_am : Phi_am_stmt PhiF.
Proof. intros n s ktr m s' HP HY. exact (ct_yields _ _ ktr (Some m, s') (ft_alloc_meta s HP) HY). Qed.
Lemma PhiF_step : Phi_step_stmt PhiF.
Proof.
  intros n sc s HP. unfold PhiF, mm_pre, seq_post, ab_post.
  assert (SM : forall s1, st_metas s1 = st_metas s -> full_all s1) by (intros s1 E1 g am Hin; rewrite E1 in Hin; exact (HP g am Hin)).
  apply SM. destruct (bounce_idx sc) as [k|]; [destruct (negb _ && _)%bool|]; destruct (st_seq _ =? 255); destruct s; reflexivity.
Qed.
Lemma PhiF_hit : Phi_hit_stmt PhiF False.
Proof. intros n sc s first s' HP E NZ. exact (NZ (proj1 (try_avail_full0 sc s first s' HP E))). Qed.
Lemma PhiF_init n : PhiF n init_state.
Proof. intros g am []. Qed.

