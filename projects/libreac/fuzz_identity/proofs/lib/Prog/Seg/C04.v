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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import reac_box_family_of_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_scd.
Import ListNotations.
Open Scope Z_scope.

Lemma c04_nil : forall inp, nlen inp = 0 -> inp = [].
Proof. intros [|b inp] H; [reflexivity|]. unfold nlen in H. cbn [length] in H. lia. Qed.

Lemma c04_nrec_nil : nrec [] = 0.
Proof. reflexivity. Qed.

Lemma c04_nrecn0 : forall inp, nrec inp = 0 -> nrecn inp = 0%nat.
Proof. intros inp H. unfold nrecn. rewrite H. reflexivity. Qed.

Section C04.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis FAMOF : reac_box_family_of_contract.

Lemma c04_530 :
  Hcut B APIf ra (Inv_K1353c B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13530 B APIf ra empty).
Proof.
  intros H53c g c Hc.
  destruct Hc as (L & A & regs & mem & md & -> & HF & HP & HNR & HCUR & HG16 & HID).
  pose proof HF as (_ & _ & _ & _ & _ & _ & _ & _ & HMR & _).
  destruct (sc_fr_facts B APIf ra empty FF g _ _ L A regs mem md HF)
    as (Hro & Hstkn & Hfsp & HSK & HS47 & Ef & Hsp).
  pose proof alloc_ceiling_val as Hc.
  pose proof (c04_nrecn0 (g_in g) HNR) as HNRn.
  assert (HIDn : bytes_at rsegs (normalize rsegs mem) (fsp g + 130) (rec_id (g_in g) 0))
    by (apply bytes_at_normalize; [exact Hro | exact HID]).
  apply (sc_run_norm B APIf ra empty FF regs (Z_to_bv 64 0x13530) mem md L A
    (fun R pc' mem' => pc' = Z_to_bv 64 0x1353c /\ munch [(fsp g - 32, fsp g)] mem mem' /\
       wmono rsegs mem mem' /\ getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\
       getr R 4 = getr regs 4 /\ getr R 20 = getr regs 20 /\
       getr R 26 = getr regs 26 /\ getr R 9 = Z_to_bv 64 (FAM (rec_id (g_in g) 0))) _ HMR Hro).
  - unfold rmk. rewrite Hsp.
    step. step.
    eapply Exec.evt_cut.
    + eapply FAMOF with (lo := g_S g - 65536) (idb := rec_id (g_in g) 0).
      * rewrite Hfsp. exact Hstkn.
      * rewrite Hfsp. unfold REAC_BOX_FAMILY_OF_FRAME. lia.
      * apply mem_inv_normalize.
      * right. rewrite Hfsp, MState.unsigned_lit by lia.
        split; [exact HIDn|]. split; [apply rec_id_length|]. right. lia.
    + intros ms' PO.
      destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                      E & HMU & HWM & _ & _).
      subst ms'.
      rewrite (sc_famof_nz (bv_unsigned (Z_to_bv 64 (fsp g + 130))) (rec_id (g_in g) 0))
        by (rewrite MState.unsigned_lit by lia; lia).
      rewrite Hfsp in HMU.
      replace (MState.ret_pc (Z_to_bv 64 0x13538)) with (Z_to_bv 64 0x13538)
        by (apply bv_eq; vm_compute; reflexivity).
      step.
      apply Exec.evt_done. do 3 eexists. split; [reflexivity|].
      intros mem' HR Hs. destruct (sc_back mem m' mem' _ Hro HMU HWM HR Hs) as [HM' HW'].
      split; [reflexivity|].
      split; [exact HM'|]. split; [exact HW'|].
      repeat (split; [reflexivity|]). reflexivity.
  - intros R pc' mem' regs' (-> & HM' & HW' & E2 & E3 & E4 & E20 & E26 & E9) Hg.
    apply H53c.
    assert (Ekm : 2 * NR g = 0) by lia.
    unfold Inv_K1353c. rewrite Ekm.
    apply (sc_cut B APIf ra empty g _ _ _ _ L A regs' mem' md); [| exact HP |].
    + apply (sc_FR_regs B APIf ra empty g _ _ L A regs regs' mem' md); [| rewrite Hg; assumption ..].
      apply (sc_after_call B APIf ra empty FF g _ _ L A regs mem md mem' 32 HF HP HM' HW'). lia.
    + assert (Hab : forall a bs, fsp g <= a -> bytes_at rsegs mem a bs -> bytes_at rsegs mem' a bs)
        by (intros a bs Ha Hb; exact (sc_ba_above rsegs mem mem' _ _ a bs Hb HM' Ha)).
      split.
      { destruct HCUR as (C1 & C2 & C3). split; [exact C1|]. rewrite !Hg, E20, E26. split; assumption. }
      split.
      { split; [apply Hab; [unfold spk; lia | exact HG16]|].
        unfold IDb, NRn. rewrite HNRn. apply Hab; [unfold spk; lia | exact HID]. }
      split.
      { rewrite Hg, E9. unfold idT. rewrite HNRn. reflexivity. }
      unfold haveT. rewrite HNRn. reflexivity.
Qed.

Lemma seg_C04 :
  Hcut B APIf ra (Inv_K1353c B APIf ra empty) ->
  Hcut B APIf ra (Inv_K1352c B APIf ra empty) /\ Hcut B APIf ra (Inv_K13530 B APIf ra empty).
Proof.
  intros H53c. pose proof (c04_530 H53c) as H530. split; [|exact H530].
  intros g c Hc.
  destruct Hc as (L & A & regs & mem & md & -> & HF & HP & Hn0 & H9 & H20 & HG16 & HID).
  pose proof HF as (_ & _ & _ & _ & _ & _ & _ & _ & HMR & _).
  pose proof (c04_nil (g_in g) Hn0) as Hnil.
  apply (sc_run B APIf ra empty FF regs (Z_to_bv 64 0x1352c) mem md L A
    (fun R pc' mem' => mem' = mem /\ pc' = Z_to_bv 64 0x13530 /\ getr R 2 = getr regs 2 /\
       getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 20 = getr regs 20 /\
       getr R 26 = Z_to_bv 64 0) _ HMR).
  - unfold rmk. step.
    apply Exec.evt_done. do 3 eexists. split; [reflexivity|].
    repeat (split; [reflexivity|]). reflexivity.
  - intros R pc' mem' regs' (-> & -> & E2 & E3 & E4 & E20 & E26) Hg.
    apply H530. apply (sc_cut B APIf ra empty g _ _ _ _ L A regs' mem md); [| exact HP |].
    + apply (sc_FR_regs B APIf ra empty g _ _ L A regs regs' mem md HF); rewrite Hg; assumption.
    + split; [unfold NR; rewrite Hnil; reflexivity|].
      split; [|split; [exact HG16 | exact HID]].
      assert (EcT : cT (g_in g) = 0) by (rewrite Hnil; reflexivity).
      unfold CUR. rewrite EcT, Hn0, !Hg, E20, E26, H20.
      split; [lia|]. split; f_equal; lia.
Qed.

End C04.
