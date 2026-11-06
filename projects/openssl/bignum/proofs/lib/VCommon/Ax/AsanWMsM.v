(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import PropExec CatExec SeqExec StoreOk ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AsanWLazy AsanWAcc AsanWBase AsanWMemset AsanSMat AsanWMat.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Section MSWM.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable e : Z.
Hypothesis HC : MSCode segs e.

Section LoopM.
Variable model0 : Model.
Variable K : TSet.
Variable ms0 : machine_state.
Variables (dst n : Z) (c : word).
Hypothesis Hh0 : m_halted model0 = None.
Hypothesis Hc : (bv_unsigned c < 256)%Z.
Hypothesis Hdst : (0 <= dst)%Z.
Hypothesis Hn : (0 <= n)%Z.
Hypothesis Hdn : (dst + n <= 2 ^ 47)%Z.
Hypothesis Hra : (bv_unsigned (rg ms0 1) mod 2 = 0)%Z.
Hypothesis Hsok : store_ok segs (ms_mem ms0) (Z_to_bv 64 dst) (Z.to_nat n) = true.
Let L : list word := range_pages dst (Z.to_nat n).
Hypothesis Hbud : (vm_backing_used model0 + Z.of_nat (length L) * page_size <= vm_limit (m_vmmaps model0))%Z.
Hypothesis HK : forall ms' m', MSR ms0 ms' ->
  filled (ms_mem ms') (ms_mem ms0) dst (dst + n) (Z_to_bv 8 (bv_unsigned c)) ->
  ms_pc_val ms' = rg ms0 1 -> matin model0 m' L -> realizes_cfg segs cfg (mkCfg ms' m') K.

Let v := Z_to_bv 8 (bv_unsigned c).

Lemma mhaltS : forall m, matin model0 m L -> m_halted m = None.
Proof. intros m Hm. rewrite (matin_halted _ _ _ Hm). exact Hh0. Qed.

Local Ltac mnext := let m' := fresh "mdl" in let H' := fresh "Hmn" in intros m' H';
  repeat match goal with
         | H : matin model0 ?x L |- _ => lazymatch x with m' => fail | _ => clear H end
         | H : m_halted ?x = None |- _ => lazymatch x with m' => fail | model0 => fail | _ => clear H end
         end;
  let Hm := fresh "Hm" in rename H' into Hm; let Hh := fresh "Hhm" in pose proof (mhaltS m' Hm) as Hh.

Lemma ms_retm : forall S m, matin model0 m L -> MSR ms0 S -> ms_pc_val S = pcw e 0x5c ->
  filled (ms_mem S) (ms_mem ms0) dst (dst + n) v -> realizes_cfg segs cfg (mkCfg S m) K.
Proof.
  intros S m Hm HS Hpc Hf. pose proof (mhaltS m Hm) as Hhm.
  eapply rzc_acc; [ exact Hhm | exact (msr_svc _ _ HS) | eapply wacc_Jalr; [ rewrite Hpc; exact (FM_5c segs e HC) | reflexivity | exact DM_5c ]
                  | apply acc_ok_nil | ].
  apply HK.
  - eapply MSR_setx; [exact HS | left; reflexivity | reflexivity | reflexivity].
  - exact Hf.
  - rewrite pc_setx. rewrite (msr_regs _ _ HS 1) by discriminate. apply ret_even. exact Hra.
  - exact Hm.
Qed.

Lemma sok_subM : forall m (a : Z) k, filled m (ms_mem ms0) dst (dst + (a - dst)) v ->
  (dst <= a)%Z -> (a + Z.of_nat k <= dst + n)%Z -> store_ok segs m (Z_to_bv 64 a) k = true.
Proof.
  intros m a k Hf Ha Hk.
  eapply store_ok_sub; [ | eapply store_ok_mono; [exact (filled_grows _ _ _ _ _ Hf) | exact Hsok] | | ];
    rewrite ?bvu_z by lia; rewrite ?Z2Nat.id by lia; lia.
Qed.

Local Ltac msr_chain HS :=
  repeat first
   [ (eapply MSR_store; [ | reflexivity ])
   | (eapply MSR_setx; [ | first [ left; reflexivity | right; left; reflexivity | right; right; left; reflexivity
                                 | right; right; right; reflexivity ] | reflexivity | reflexivity ]) ];
  exact HS.

Local Ltac inL := apply range_pages_incl; rewrite bvu_z by lia; cbn [msz_n Z.of_nat Pos.of_succ_nat Pos.succ];
                  rewrite ?Z2Nat.id by lia; lia.

Lemma byte_loopm : forall (d : nat) S (i : Z) m, matin model0 m L ->
  (n - i = Z.of_nat d)%Z -> (0 <= i < n)%Z ->
  MSR ms0 S -> ms_pc_val S = pcw e 0x18 ->
  rg S 13 = Z_to_bv 64 (dst + i) -> rg S 12 = Z_to_bv 64 (dst + n) -> rg S 11 = c ->
  filled (ms_mem S) (ms_mem ms0) dst (dst + i) v ->
  realizes_cfg segs cfg (mkCfg S m) K.
Proof.
  induction d as [|d IH]; intros S i m Hm Hd Hi HS Hpc H13 H12 H11 Hf; [lia|].
  pose proof (mhaltS m Hm) as Hhm. pose proof (msr_svc _ _ HS) as Hsvc.

  eapply (rzc_acc_in segs cfg model0 _ L); [ exact Hh0 | exact Hm | exact Hsvc
     | eapply wacc_Store; [ rewrite Hpc; exact (FM_18 segs e HC) | reflexivity | exact DM_18 | ] | | exact Hbud | ].
  { rewrite H13. mnorm. apply (sok_subM _ (dst + i) 1); [ replace (dst + (dst + i - dst))%Z with (dst + i)%Z by lia; exact Hf | lia | cbn; lia ]. }
  { rewrite H13. mnorm. inL. } mnext.
  rewrite Hpc. pcn. rewrite H13, H11. mnorm. rewrite store1_byte by exact Hc.

  wst wacc_OpImm (FM_1c segs e HC) DM_1c. mnorm. rewrite H13. mnorm.

  eapply rzc_acc; [ exact Hhm | reflexivity | eapply wacc_Branch; [ fetch_tac (FM_20 segs e HC) | reflexivity | exact DM_20 ] | apply acc_ok_nil | ].
  mnorm. rewrite H12. rewrite branch_ne_z by lia. pcn.
  destruct (Z.eqb_spec (dst + i + 1) (dst + n)) as [Eq|Ne]; cbn [negb]; pcn.
  -
    wst wacc_Jal (FM_24 segs e HC) DM_24. apply (ms_retm _ _ Hm).
    + msr_chain HS.
    + reflexivity.
    + rewrite ?mem_setx. replace (dst + n)%Z with (dst + i + Z.of_nat 1)%Z by lia.
      apply (filled_step _ _ dst i 1); [lia | lia | cbn; lia | exact Hf].
  - apply (IH _ (i + 1)%Z _ Hm); [lia | lia | msr_chain HS | reflexivity | | | | ].
    + rgn. f_equal. lia.
    + rgn. exact H12.
    + rgn. exact H11.
    + rewrite ?mem_setx. replace (dst + (i + 1))%Z with (dst + i + Z.of_nat 1)%Z by lia.
      apply (filled_step _ _ dst i 1); [lia | lia | cbn; lia | exact Hf].
Qed.

Lemma word_loopm : forall (d : nat) S (i : Z) m, matin model0 m L ->
  (n - i = 16 * Z.of_nat d)%Z -> (0 <= i < n)%Z ->
  MSR ms0 S -> ms_pc_val S = pcw e 0x4c ->
  rg S 13 = Z_to_bv 64 (dst + i) -> rg S 12 = Z_to_bv 64 (dst + n) -> rg S 11 = Z_to_bv 64 (rep 8 (bv_unsigned c)) ->
  filled (ms_mem S) (ms_mem ms0) dst (dst + i) v ->
  realizes_cfg segs cfg (mkCfg S m) K.
Proof.
  induction d as [|d IH]; intros S i m Hm Hd Hi HS Hpc H13 H12 H11 Hf; [lia|].
  pose proof (mhaltS m Hm) as Hhm. pose proof (msr_svc _ _ HS) as Hsvc. pose proof (u64_range c).

  eapply (rzc_acc_in segs cfg model0 _ L); [ exact Hh0 | exact Hm | exact Hsvc
     | eapply wacc_Store; [ rewrite Hpc; exact (FM_4c segs e HC) | reflexivity | exact DM_4c | ] | | exact Hbud | ].
  { rewrite H13. mnorm. apply (sok_subM _ (dst + i) 8); [ replace (dst + (dst + i - dst))%Z with (dst + i)%Z by lia; exact Hf | lia | cbn; lia ]. }
  { rewrite H13. mnorm. inL. } mnext.
  rewrite Hpc. pcn. rewrite H13, H11. mnorm. rewrite store8_rep by lia.
  assert (Hf1 : filled (write_to_mem (ms_mem S) (Z_to_bv 64 (dst + i)) (repeat v 8)) (ms_mem ms0) dst (dst + (i + 8)) v).
  { replace (dst + (i + 8))%Z with (dst + i + Z.of_nat 8)%Z by lia. apply filled_step; [lia | lia | cbn; lia | exact Hf]. }

  eapply (rzc_acc_in segs cfg model0 _ L); [ exact Hh0 | exact Hm | reflexivity
     | eapply wacc_Store; [ fetch_tac (FM_50 segs e HC) | reflexivity | exact DM_50 | ] | | exact Hbud | ].
  { rewrite ?mem_setx. rgn. rewrite H13. mnorm. apply (sok_subM _ (dst + i + 8) 8); [ replace (dst + (dst + i + 8 - dst))%Z with (dst + (i + 8))%Z by lia; exact Hf1 | lia | cbn; lia ]. }
  { rgn. rewrite H13. mnorm. inL. } mnext.
  pcn. rgn. rewrite H13, H11. mnorm. rewrite store8_rep by lia.
  assert (Hf2 : filled (write_to_mem (write_to_mem (ms_mem S) (Z_to_bv 64 (dst + i)) (repeat v 8)) (Z_to_bv 64 (dst + i + 8)) (repeat v 8))
                  (ms_mem ms0) dst (dst + (i + 16)) v).
  { replace (dst + (i + 16))%Z with (dst + (i + 8) + Z.of_nat 8)%Z by lia.
    replace (dst + i + 8)%Z with (dst + (i + 8))%Z by lia. apply filled_step; [lia | lia | cbn; lia | exact Hf1]. }

  wst wacc_OpImm (FM_54 segs e HC) DM_54. mnorm. rewrite H13. mnorm.

  eapply rzc_acc; [ exact Hhm | reflexivity | eapply wacc_Branch; [ fetch_tac (FM_58 segs e HC) | reflexivity | exact DM_58 ] | apply acc_ok_nil | ].
  mnorm. rewrite H12. rewrite branch_ltu_z by lia. pcn.
  destruct (Z.ltb_spec (dst + i + 16) (dst + n)) as [Lt|Ge]; pcn.
  - apply (IH _ (i + 16)%Z _ Hm); [lia | lia | msr_chain HS | reflexivity | | | | ].
    + rgn. f_equal. lia.
    + rgn. exact H12.
    + rgn. exact H11.
    + rewrite ?mem_setx. exact Hf2.
  - apply (ms_retm _ _ Hm).
    + msr_chain HS.
    + reflexivity.
    + rewrite ?mem_setx. replace (dst + n)%Z with (dst + (i + 16))%Z by lia. exact Hf2.
Qed.

Lemma ms_entrym :
  ms_svc_pending ms0 = None -> ms_pc_val ms0 = pcw e 0 ->
  rg ms0 10 = Z_to_bv 64 dst -> rg ms0 11 = c -> rg ms0 12 = Z_to_bv 64 n ->
  realizes_cfg segs cfg (mkCfg ms0 model0) K.
Proof.
  intros Hsvc Hpc H10 H11 H12. pose proof (matin_refl model0 L) as Hm. pose proof Hh0 as Hhm.
  pose proof (msr_svc _ _ (MSR_refl ms0 Hsvc)) as _. pose proof (u64_range c) as Hcr.

  wst wacc_Op (FM_0 segs e HC) DM_0. mnorm. rewrite H12, H10. rewrite alu_or_z by lia.

  wst wacc_OpImm (FM_4 segs e HC) DM_4. mnorm. rewrite alu_and15_z by (pose proof (Z_lor_range n dst); lia).

  eapply rzc_acc; [ exact Hhm | reflexivity | eapply wacc_Branch; [ fetch_tac (FM_8 segs e HC) | reflexivity | exact DM_8 ] | apply acc_ok_nil | ].
  mnorm. rewrite branch_eq_z by (try lia; pose proof (Z_land_range (Z.lor n dst) 15); pose proof (Z_lor_range n dst); lia). pcn.
  destruct (Z.eqb_spec (Z.land (Z.lor n dst) 15) 0) as [Al|Al]; pcn.
  -
    pose proof (land15_mod n dst Hn Hdst Al) as Hn16.
    eapply rzc_acc; [ exact Hhm | reflexivity | eapply wacc_Branch; [ fetch_tac (FM_28 segs e HC) | reflexivity | exact DM_28 ] | apply acc_ok_nil | ].
    mnorm. rewrite H12. rewrite branch_eq_z by lia. pcn.
    destruct (Z.eqb_spec n 0) as [N0|N0]; pcn.
    + apply (ms_retm _ _ Hm); [msr_chain (MSR_refl ms0 Hsvc) | reflexivity |].
      rewrite ?mem_setx. rewrite N0, Z.add_0_r. apply filled_refl.
    + wst wacc_Op (FM_2c segs e HC) DM_10. mnorm. rewrite H10, H12. mnorm.
      wst wacc_ShiftImm (FM_30 segs e HC) DM_30. wst wacc_Op (FM_34 segs e HC) DM_34. mnorm. rewrite H11.
      rewrite <- (Z_to_bv_u c). rewrite (sll_or_z (bv_unsigned c) _ 8) by (try reflexivity; try lia). rewrite <- rep2.
      wst wacc_ShiftImm (FM_38 segs e HC) DM_38. wst wacc_Op (FM_3c segs e HC) DM_34. mnorm.
      rewrite (sll_or_z (rep 2 (bv_unsigned c)) _ 16) by (try reflexivity; pose proof (rep_range 2 (bv_unsigned c)); cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *; lia).
      rewrite <- rep4.
      wst wacc_ShiftImm (FM_40 segs e HC) DM_40. wst wacc_Op (FM_44 segs e HC) DM_34. mnorm.
      rewrite (sll_or_z (rep 4 (bv_unsigned c)) _ 32) by (try reflexivity; pose proof (rep_range 4 (bv_unsigned c)); cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *; lia).
      rewrite <- rep8.
      wst wacc_OpImm (FM_48 segs e HC) DM_14. mnorm. rewrite H10. mnorm.
      apply (word_loopm (Z.to_nat (n / 16)) _ 0%Z _ Hm).
      * pose proof (Z.div_mod n 16 ltac:(lia)). rewrite Z2Nat.id by (apply Z.div_pos; lia). lia.
      * lia.
      * msr_chain (MSR_refl ms0 Hsvc).
      * reflexivity.
      * rgn. f_equal. lia.
      * rgn. reflexivity.
      * rgn. reflexivity.
      * rewrite ?mem_setx. rewrite Z.add_0_r. apply filled_refl.
  -
    eapply rzc_acc; [ exact Hhm | reflexivity | eapply wacc_Branch; [ fetch_tac (FM_c segs e HC) | reflexivity | exact DM_c ] | apply acc_ok_nil | ].
    mnorm. rewrite H12. rewrite branch_eq_z by lia. pcn.
    destruct (Z.eqb_spec n 0) as [N0|N0]; pcn.
    + apply (ms_retm _ _ Hm); [msr_chain (MSR_refl ms0 Hsvc) | reflexivity |].
      rewrite ?mem_setx. rewrite N0, Z.add_0_r. apply filled_refl.
    + wst wacc_Op (FM_10 segs e HC) DM_10. mnorm. rewrite H10, H12. mnorm.
      wst wacc_OpImm (FM_14 segs e HC) DM_14. mnorm. rewrite H10. mnorm.
      apply (byte_loopm (Z.to_nat n) _ 0%Z _ Hm).
      * rewrite Z2Nat.id by lia. lia.
      * lia.
      * msr_chain (MSR_refl ms0 Hsvc).
      * reflexivity.
      * rgn. f_equal. lia.
      * rgn. reflexivity.
      * rgn. exact H11.
      * rewrite ?mem_setx. rewrite Z.add_0_r. apply filled_refl.
Qed.

End LoopM.
End MSWM.

Definition ms_pages (n : Z) : Z := (n / 4096 + 2)%Z.

Lemma ms_pages_L : forall dst n, (0 <= dst)%Z -> (0 <= n)%Z -> (dst + n <= 2 ^ 47)%Z ->
  (Z.of_nat (length (range_pages dst (Z.to_nat n))) <= ms_pages n)%Z.
Proof.
  intros dst n Hd Hn Hdn. unfold ms_pages.
  pose proof (range_pages_length dst (Z.to_nat n) Hd ltac:(lia)) as H1. rewrite Z2Nat.id in H1 by lia. exact H1.
Qed.

Theorem internal_memset_sum_mat : forall (segs : list Segment) (cfg : SpuriousCfg) (e : Z), MSCode segs e ->
  forall (ms : machine_state) (model : Model) (K : TSet) (dst n : Z) (c : word),
  ms_svc_pending ms = None -> ms_pc_val ms = pcw e 0 -> m_halted model = None ->
  rg ms 10 = Z_to_bv 64 dst -> rg ms 11 = c -> rg ms 12 = Z_to_bv 64 n ->
  (bv_unsigned c < 256)%Z -> (0 <= dst)%Z -> (0 <= n)%Z -> (dst + n <= 2 ^ 47)%Z ->
  (bv_unsigned (rg ms 1) mod 2 = 0)%Z ->
  store_ok segs (ms_mem ms) (Z_to_bv 64 dst) (Z.to_nat n) = true ->
  (vm_backing_used model + ms_pages n * page_size <= vm_limit (m_vmmaps model))%Z ->
  (forall ms' model', MSR ms ms' ->
     filled (ms_mem ms') (ms_mem ms) dst (dst + n) (Z_to_bv 8 (bv_unsigned c)) ->
     ms_pc_val ms' = rg ms 1 -> mat_of model model' (ms_pages n) -> realizes_cfg segs cfg (mkCfg ms' model') K) ->
  realizes_cfg segs cfg (mkCfg ms model) K.
Proof.
  intros segs cfg e HC ms model K dst n c Hsvc Hpc Hh H10 H11 H12 Hc Hdst Hn Hdn Hra Hsok Hbud HK.
  pose proof (ms_pages_L dst n Hdst Hn Hdn) as HL.
  assert (Hbud' : (vm_backing_used model + Z.of_nat (length (range_pages dst (Z.to_nat n))) * page_size
                     <= vm_limit (m_vmmaps model))%Z) by (unfold page_size in *; lia).
  refine (ms_entrym segs cfg e HC model K ms dst n c Hh Hc Hdst Hn Hdn Hra Hsok Hbud' _ Hsvc Hpc H10 H11 H12).
  intros ms' m' HS Hf Hp Hm. apply HK; [exact HS | exact Hf | exact Hp |].
  eapply mat_of_mono; [exact (matin_mat_of _ _ _ Hm) | exact HL].
Qed.
