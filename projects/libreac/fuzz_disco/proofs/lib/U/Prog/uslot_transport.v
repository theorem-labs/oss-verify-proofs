From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Reusable Require Import YK11 YK0o YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0 KindBGlue FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c slot_inv uslot_norm uslot_seg uslot_preds uslot_cells.
Import ListNotations.
Open Scope Z_scope.

Definition mem_keep (X d h : Z) (pl : list byte) (m m' : word -> option byte) : Prop :=
  agree m m' X SLOT_FRAME /\ agree m m' h 480 /\ agree m m' d (Z.of_nat (length pl)).

Lemma hdr_keep : forall X d h pl regs0 m m', mem_keep X d h pl m m' ->
  hdr_mem X d h pl regs0 m -> hdr_mem X d h pl regs0 m'.
Proof.
  intros X d h pl regs0 m m' (HS & HH & HD) HM. hdr_open HM.
  repeat match goal with H : rw_cells rsegs m ?A ?cs |- _ =>
    first [apply (rw_agree m m' X SLOT_FRAME A cs HS) in H;
            [|lia|cbn [cells_size csize saved_of saved_cells]; unfold SLOT_FRAME; lia]
          | apply (rw_agree m m' h 480 A cs HH) in H;
            [|lia|cbn [cells_size csize]; lia]]
  end.
  apply (bytes_at_agree m m' d pl BD) in HD. clear BD.
  hdr_close.
Qed.

Lemma base_keep : forall X d h pl regs0 i now R R' m m', regs_preserved R R' ->
  mem_keep X d h pl m m' -> P_BASE X d h pl regs0 i now R m -> P_BASE X d h pl regs0 i now R' m'.
Proof.
  intros X d h pl regs0 i now R R' m m' RP MK
    (Hi & Hnow & G2 & G3 & G4 & G18 & G24 & G26 & C160 & C224 & HM).
  destruct (rp13 R R' RP) as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27).
  pose proof MK as (HS & _ & _).
  split; [exact Hi|]. split; [exact Hnow|].
  split; [rewrite E2; exact G2|]. split; [rewrite E3; exact G3|]. split; [rewrite E4; exact G4|].
  split; [rewrite E18; exact G18|]. split; [rewrite E24; exact G24|]. split; [rewrite E26; exact G26|].
  split.
  { apply (rw_agree m m' X SLOT_FRAME (X + 160) [C8 (Z_to_bv 64 i)] HS);
      [lia | cbn [cells_size csize]; unfold SLOT_FRAME; lia | exact C160]. }
  split.
  { apply (rw_agree m m' X SLOT_FRAME (X + 224) [C8 (Z_to_bv 64 now)] HS);
      [lia | cbn [cells_size csize]; unfold SLOT_FRAME; lia | exact C224]. }
  exact (hdr_keep X d h pl regs0 m m' MK HM).
Qed.

Lemma hdr_reqv : forall X d h pl regs0 i, reqv (P_HDR X d h pl regs0 i).
Proof. intros X d h pl regs0 i R R' m E HP. unfold P_HDR. setoid_rewrite E. exact HP. Qed.

Lemma base_reqv : forall X d h pl regs0 i now, reqv (P_BASE X d h pl regs0 i now).
Proof. intros X d h pl regs0 i now R R' m E HP. unfold P_BASE. setoid_rewrite E. exact HP. Qed.

Lemma lat_reqv : forall X d h pl regs0 i, reqv (P_LAT X d h pl regs0 i).
Proof. intros X d h pl regs0 i R R' m E HP. unfold P_LAT, P_BASE in *. setoid_rewrite E. exact HP. Qed.

Lemma exit_reqv : forall X h regs0, reqv (P_EXIT X h regs0).
Proof. intros X h regs0 R R' m E HP. unfold P_EXIT. setoid_rewrite E. exact HP. Qed.

Lemma next_reqv : forall X d h pl regs0 i q, reqv (P_NEXT X d h pl regs0 i q).
Proof. intros X d h pl regs0 i q R R' m E HP. unfold P_NEXT, P_HDR, P_EXIT in *. setoid_rewrite E. exact HP. Qed.

Lemma ret_reqv : forall regs0, reqv (P_RET regs0).
Proof.
  intros regs0 R R' m E (RP & G10). split; [exact (kb_preserved_getr regs0 R R' RP E)|rewrite E; exact G10].
Qed.
