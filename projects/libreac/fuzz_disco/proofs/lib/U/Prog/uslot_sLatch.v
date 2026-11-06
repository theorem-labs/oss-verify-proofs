From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Reusable Require Import YK11 YK0o YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0 KindBGlue FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c slot_inv uslot_norm uslot_seg uslot_preds uslot_cells uslot_frame uslot_step.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import uslot_record.
Import ListNotations.
Open Scope Z_scope.

Lemma seg_latch : forall X d h pl regs0 i, xok X -> dok X d pl ->
  seg_ev LATCH [] (P_LAT X d h pl regs0 i) (P_NEXT X d h pl regs0 i).
Proof.
  intros X d h pl regs0 i (HX0 & HX16 & HX1 & HXlo) (Hd0 & Hd1 & Hd2 & Hdns) fx' regs m Hf HI
    (n & now & Hn & G9 & G21 & G23 & G27 & Hi & Hnow & G2 & G3 & G4 & G18 & G24 & G26 & C160 & C224 & HM).
  unfold rmk. eapply evt_mono.
  { eapply (uslot_R16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m X i n);
      try eassumption; unfold SLOT_FRAME in *; lia. }
  intros ms ->.
  destruct (Z.ltb_spec i (MAX_OPS - 1)) as [Hil|Hih]; cbn [andb].
  - destruct (Z.eqb_spec n 0) as [Hnz|Hnz]; cbn [negb].
    + do 2 eexists. exists EXIT. do 2 eexists.
      split; [reflexivity|]. split; [exact Hf|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
      right. split; [reflexivity|].
      split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
      unfold hdr_mem in HM. tauto.
    + do 2 eexists. exists HDR. do 2 eexists.
      split; [reflexivity|]. split; [exact Hf|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
      left. split; [reflexivity|]. split; [lia|]. exists n, now.
      split; [lia|]. split; [exact Hnow|]. split; [lia|].
      split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [reflexivity|]. split; [exact G9|].
      split; [exact G18|]. split; [exact G21|]. split; [exact G23|]. split; [exact G24|].
      split; [exact G26|]. split; [exact G27|]. exact HM.
  - do 2 eexists. exists EXIT. do 2 eexists.
    split; [reflexivity|]. split; [exact Hf|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
    right. split; [reflexivity|].
    split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
    unfold hdr_mem in HM. tauto.
Qed.

Lemma seg_B3b : forall X d h pl regs0 i, xok X -> dok X d pl ->
  seg_ev R27_RET [] (P_R27RET X d h pl regs0 i) (P_NEXT X d h pl regs0 i).
Proof.
  intros X d h pl regs0 i HX HD fx' regs m Hf HI
    (n & now & Hn & G21 & G23 & Hi & Hnow & G2 & G3 & G4 & G18 & G24 & G26 & C160 & C224 & HM).
  pose proof HX as (HX0 & HX16 & HX1 & HXlo).
  unfold rmk. eapply evt_cut.
  { eapply uslot_R27_ret with (X := X) (now := now); first [eassumption | unfold SLOT_FRAME in *; lia]. }
  intros ms ->.
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) => change R with (rmk R) end.
  apply (seg_latch X d h pl regs0 i HX HD fx' _ m Hf HI).
  exists n, now. split; [exact Hn|]. split; [reflexivity|]. split; [exact G21|]. split; [exact G23|].
  split; [reflexivity|].
  split; [exact Hi|]. split; [exact Hnow|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
  split; [exact G18|]. split; [exact G24|]. split; [exact G26|]. split; [exact C160|]. split; [exact C224|].
  exact HM.
Qed.
