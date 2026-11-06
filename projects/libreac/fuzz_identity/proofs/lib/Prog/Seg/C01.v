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

Section C01.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis FAMOF : reac_box_family_of_contract.

Lemma seg_C01 :
  Hcut B APIf ra (Inv_K134ec B APIf ra empty) ->
  Hcut B APIf ra (Inv_K134e4 B APIf ra empty).
Proof.
  intros H4ec g c Hc.
  destruct Hc as (L & A & regs & mem & md & -> & HF & HP & HCB & H19).
  pose proof HF as (_ & _ & _ & _ & _ & _ & _ & _ & HMR & _).
  destruct (sc_fr_facts B APIf ra empty FF g _ _ L A regs mem md HF)
    as (Hro & Hstkn & Hfsp & HSK & HS47 & Ef & Hsp).
  pose proof HCB as (HNR & HNRb & HG16 & HHW & HCUR & HID).
  pose proof alloc_ceiling_val as Hc.
  assert (HIDn : bytes_at rsegs (normalize rsegs mem) (fsp g + 130) (idT (g_in g)))
    by (apply bytes_at_normalize; [exact Hro | exact HID]).
  apply (sc_run_norm B APIf ra empty FF regs (Z_to_bv 64 0x134e4) mem md L A
    (fun R pc' mem' => pc' = Z_to_bv 64 0x134ec /\ munch [(fsp g - 32, fsp g)] mem mem' /\
       wmono rsegs mem mem' /\ getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\
       getr R 4 = getr regs 4 /\ getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\
       getr R 26 = getr regs 26 /\ getr R 10 = Z_to_bv 64 (FAM (idT (g_in g)))) _ HMR Hro).
  - unfold rmk. rewrite Hsp.
    step. step.
    eapply Exec.evt_cut.
    + eapply FAMOF with (lo := g_S g - 65536) (idb := idT (g_in g)).
      * rewrite Hfsp. exact Hstkn.
      * rewrite Hfsp. unfold REAC_BOX_FAMILY_OF_FRAME. lia.
      * apply mem_inv_normalize.
      * right. rewrite Hfsp, MState.unsigned_lit by lia.
        split; [exact HIDn|]. split; [apply rec_id_length|]. right. lia.
    + intros ms' PO.
      destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                      E & HMU & HWM & _ & _).
      subst ms'.
      rewrite (sc_famof_nz (bv_unsigned (Z_to_bv 64 (fsp g + 130))) (idT (g_in g)))
        by (rewrite MState.unsigned_lit by lia; lia).
      rewrite Hfsp in HMU.
      apply Exec.evt_done. do 3 eexists. split; [reflexivity|].
      intros mem' HR Hs. destruct (sc_back mem m' mem' _ Hro HMU HWM HR Hs) as [HM' HW'].
      split; [apply bv_eq; vm_compute; reflexivity|].
      split; [exact HM'|]. split; [exact HW'|].
      repeat (split; [reflexivity|]). reflexivity.
  - intros R pc' mem' regs' (-> & HM' & HW' & E2 & E3 & E4 & E19 & E20 & E26 & E10) Hg.
    apply H4ec. apply (sc_cut B APIf ra empty g _ _ _ _ L A regs' mem' md); [| exact HP |].
    + apply (sc_FR_regs B APIf ra empty g _ _ L A regs regs' mem' md); [| rewrite Hg; assumption ..].
      apply (sc_after_call B APIf ra empty FF g _ _ L A regs mem md mem' 32 HF HP HM' HW'). lia.
    + assert (Hab : forall a bs, fsp g <= a -> bytes_at rsegs mem a bs -> bytes_at rsegs mem' a bs)
        by (intros a bs Ha Hb; exact (sc_ba_above rsegs mem mem' _ _ a bs Hb HM' Ha)).
      destruct HHW as (W1 & W2 & W3). unfold spk in *.
      split; [|split; [rewrite Hg, E19; exact H19 | rewrite Hg; exact E10]].
      split; [exact HNR|].
      split; [apply Hab; [unfold spk; lia | exact HNRb]|].
      split; [apply Hab; [unfold spk; lia | exact HG16]|].
      split; [split; [apply Hab; [unfold spk; lia | exact W1]|split; [apply Hab; [unfold spk; lia | exact W2] | apply Hab; [unfold spk; lia | exact W3]]]|].
      split; [|apply Hab; [unfold spk; lia | exact HID]].
      destruct HCUR as (C1 & C2 & C3). split; [exact C1|]. rewrite !Hg, E20, E26. split; assumption.
Qed.

End C01.
