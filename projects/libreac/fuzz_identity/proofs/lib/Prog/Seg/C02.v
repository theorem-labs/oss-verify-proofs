From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Tac.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_scd.
Import ListNotations.
Open Scope Z_scope.

Section C02.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_C02 :
  Hcut B APIf ra (Inv_K13540 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13508 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K134ec B APIf ra empty).
Proof.
  intros H540 H508 g c Hc.
  destruct Hc as (L & A & regs & mem & md & -> & HF & HP & HCB & H19 & H10).
  pose proof HF as (HGV & Hsp & Hgp & Htp & _ & _ & HMI & _ & HMR & _).
  pose proof HCB as (HNR & HNRb & HG16 & HHW & HCUR & HID).
  pose proof HHW as (Hhv & _ & _).
  set (hv := rec_have (g_in g) (NRn g)) in *.
  assert (Hhv01 : hv = 0 \/ hv = 1) by (unfold hv, rec_have; destruct (rec_hw _ _); auto).
  pose proof (sc_q64_ovr mem (spk g 24) hv Hhv) as HRD. unfold spk in HRD.
  apply (sc_run B APIf ra empty FF regs (Z_to_bv 64 0x134ec) mem md L A
    (fun R pc' mem' => mem' = mem /\ getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\
       getr R 4 = getr regs 4 /\ getr R 20 = getr regs 20 /\ getr R 26 = getr regs 26 /\
       getr R 9 = Z_to_bv 64 (FAM (idT (g_in g))) /\
       ((hv = 0 /\ pc' = Z_to_bv 64 0x13540 /\ getr R 10 = Z_to_bv 64 0) \/
        (hv = 1 /\ pc' = Z_to_bv 64 0x13508 /\ getr R 19 = Z_to_bv 64 (spk g 116) /\
         getr R 8 = Z_to_bv 64 3 /\ getr R 18 = Z_to_bv 64 HWT_ADDR))) _ HMR).
  - unfold rmk. rewrite Hsp, H10.
    step. step.
    destruct Hhv01 as [E0|E1].
    + rewrite E0. step. if_true.
      apply Exec.evt_done. do 3 eexists. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      left. split; [reflexivity|]. split; reflexivity.
    + rewrite E1. step. if_false. step. step. step. step.
      apply Exec.evt_done. do 3 eexists. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      right. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
  - intros R pc' mem' regs' (-> & E2 & E3 & E4 & E20 & E26 & E9 & Hbr) Hg.
    assert (HF' : FR B APIf ra empty g (2 * NR g) [] L A regs' mem md).
    { apply (sc_FR_regs B APIf ra empty g _ _ L A regs regs' mem md HF).
      - rewrite Hg. exact E2.
      - rewrite Hg. exact E3.
      - rewrite Hg. exact E4. }
    assert (HCUR' : CUR g (cT (g_in g)) regs').
    { destruct HCUR as (C1 & C2 & C3). split; [exact C1|]. rewrite !Hg, E20, E26. split; assumption. }
    destruct Hbr as [(E0 & -> & E10) | (E1 & -> & E19' & E8 & E18)].
    + apply H540. apply (sc_cut B APIf ra empty g _ _ _ _ L A regs' mem md HF' HP).
      split; [exact HCUR'|]. split; [split; assumption|].
      rewrite !Hg. split; [exact E9|]. split; [exact E0|]. exact E10.
    + apply H508. exists 0%nat. apply (sc_cut B APIf ra empty g _ _ _ _ L A regs' mem md HF' HP).
      split; [exact (conj HNR (conj HNRb (conj HG16 (conj HHW (conj HCUR' HID)))))|].
      split; [exact E1|]. rewrite !Hg.
      split; [exact E9|]. split; [exact E19'|]. split; [exact E8|]. split; [exact E18|].
      split; [lia|]. intros j' Hj'. lia.
Qed.

End C02.
