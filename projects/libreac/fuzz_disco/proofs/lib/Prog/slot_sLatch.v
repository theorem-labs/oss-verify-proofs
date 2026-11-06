From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YK0o YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0 KindBGlue FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import LLVMFuzzerTestOneInput_c slot_inv slot_norm slot_seg slot_preds slot_cells slot_frame slot_step.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_sB1.
Import ListNotations.
Open Scope Z_scope.

Definition P_LAT (X d h : Z) (pl : list byte) (regs0 : bvmap 5 word) (i : Z)
    (R : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists n now, 0 <= n <= Z.of_nat (length pl) /\
    getr R 19 = Z_to_bv 64 n /\ getr R 20 = Z_to_bv 64 h /\
    getr R 21 = Z_to_bv 64 (d + (Z.of_nat (length pl) - n)) /\ P_BASE X d h pl regs0 i now R m.

Definition P_NEXT (X d h : Z) (pl : list byte) (regs0 : bvmap 5 word) (i q : Z)
    (R : bvmap 5 word) (m : word -> option byte) : Prop :=
  (q = HDR /\ i + 1 < MAX_OPS /\ P_HDR X d h pl regs0 (i + 1) R m) \/
  (q = EXIT /\ P_EXIT X h regs0 R m).

Lemma seg_latch : forall X d h pl regs0 i, xok X -> dok X d pl ->
  seg_ev LATCH [] (P_LAT X d h pl regs0 i) (P_NEXT X d h pl regs0 i).
Proof.
  intros X d h pl regs0 i (HX0 & HX16 & HX1 & HXlo) (Hd0 & Hd1 & Hd2 & Hdns) fx' regs m Hf HI
    (n & now & Hn & G19 & G20 & G21 & Hi & Hnow & G2 & G3 & G4 & G8 & G9 & G18 & G24 & G27 & HM).
  assert (C176 : rw_cells rsegs m (X + 176) [C8 (Z_to_bv 64 STALE_NS)]).
  { unfold hdr_mem in HM. tauto. }
  assert (R176 : ov_read_bytes rsegs m (wa (X + 176)) 8 = Some (le8 (Z_to_bv 64 STALE_NS))).
  { eapply rw_cells_read_at with (k := 0%nat) (c := C8 (Z_to_bv 64 STALE_NS));
      [exact C176|reflexivity|reflexivity|]; f_equal; lia. }
  unfold rmk. eapply evt_mono.
  { eapply (slot_R16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m X i n);
      try eassumption; unfold SLOT_FRAME in *; lia. }
  intros ms ->.
  destruct (Z.ltb_spec i (MAX_OPS - 1)) as [Hil|Hih]; cbn [andb].
  - destruct (Z.eqb_spec n 0) as [Hnz|Hnz]; cbn [negb].
    + do 2 eexists. exists EXIT. do 2 eexists.
      split; [reflexivity|]. split; [exact Hf|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
      right. split; [reflexivity|].
      split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G20|].
      unfold hdr_mem in HM. tauto.
    + do 2 eexists. exists HDR. do 2 eexists.
      split; [reflexivity|]. split; [exact Hf|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
      left. split; [reflexivity|]. split; [lia|]. exists n, now.
      split; [lia|]. split; [exact Hnow|]. split; [lia|].
      split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G8|]. split; [reflexivity|].
      split; [reflexivity|]. split; [exact G18|]. split; [exact G19|]. split; [exact G20|]. split; [exact G21|].
      split; [exact G24|]. split; [exact G27|]. exact HM.
  - do 2 eexists. exists EXIT. do 2 eexists.
    split; [reflexivity|]. split; [exact Hf|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
    right. split; [reflexivity|].
    split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G20|].
    unfold hdr_mem in HM. tauto.
Qed.

Lemma seg_B3b : forall X d h pl regs0 i, xok X -> dok X d pl ->
  seg_ev R27_RET [] (P_LAT X d h pl regs0 i) (P_NEXT X d h pl regs0 i).
Proof.
  intros X d h pl regs0 i HX HD fx' regs m Hf HI HP.
  eapply evt_cut; [apply slot_R27_ret|]. intros ms ->.
  exact (seg_latch X d h pl regs0 i HX HD fx' regs m Hf HI HP).
Qed.
