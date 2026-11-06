From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Reusable Require Import YK11 YK0o YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0 KindBGlue FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c slot_inv uslot_norm uslot_seg uslot_preds uslot_cells uslot_step uslot_frame slot_lib uslot_exit.
Import ListNotations.
Open Scope Z_scope.

Definition P_FR (X d h : Z) (pl : list byte) (regs0 : bvmap 5 word) (i n now len k f : Z) (ob : byte)
    (R : bvmap 5 word) (m : word -> option byte) : Prop :=
  0 <= n <= Z.of_nat (length pl) /\ 0 <= len <= n /\ len < 65536 /\ 0 <= k <= 2 /\
  getr R 10 = Z_to_bv 64 f /\ getr R 19 = Z_to_bv 64 len /\ getr R 20 = Z_to_bv 64 n /\
  getr R 21 = Z_to_bv 64 k /\ getr R 22 = Z_to_bv 64 (d + (Z.of_nat (length pl) - n)) /\
  getr R 8 = sxb ob /\ getr R 25 = Z_to_bv 64 (bv_unsigned ob) /\
  getr R 9 = Z_to_bv 64 now /\ getr R 27 = Z_to_bv 64 1 /\
  junkb m f (Z.to_nat len) /\ P_BASE X d h pl regs0 i now R m.

Definition P_R27 (X d h : Z) (pl : list byte) (regs0 : bvmap 5 word) (i n now len f : Z)
    (R : bvmap 5 word) (m : word -> option byte) : Prop :=
  0 <= n <= Z.of_nat (length pl) /\ 0 <= len <= n /\
  getr R 19 = Z_to_bv 64 len /\ getr R 20 = Z_to_bv 64 n /\
  rw_cells rsegs m (X + 152) [C8 (Z_to_bv 64 (d + (Z.of_nat (length pl) - n)))] /\
  rw_cells rsegs m (X + 248) [C8 (Z_to_bv 64 f)] /\ P_BASE X d h pl regs0 i now R m.

Definition P_R27RET (X d h : Z) (pl : list byte) (regs0 : bvmap 5 word) (i : Z)
    (R : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists n now, 0 <= n <= Z.of_nat (length pl) /\
    getr R 21 = Z_to_bv 64 (d + (Z.of_nat (length pl) - n)) /\ getr R 23 = Z_to_bv 64 n /\
    P_BASE X d h pl regs0 i now R m.

Definition P_FFREE (X d h : Z) (pl : list byte) (regs0 : bvmap 5 word) (i f : Z)
    (R : bvmap 5 word) (m : word -> option byte) : Prop :=
  getr R 1 = Z_to_bv 64 R27_RET /\ getr R 10 = Z_to_bv 64 f /\ P_R27RET X d h pl regs0 i R m.

Lemma R27_ev : forall X d h pl regs0 i n now len f, xok X -> dok X d pl ->
  forall R F fc m, P_R27 X d h pl regs0 i n now len f R m ->
  evt rsegs (fun ms => exists R', ms = MS R' F (Z_to_bv 64 FREE_PC) fc None m (seg_rom rsegs) /\
    P_FFREE X d h pl regs0 i f R' m)
    (MS (rmk R) F (Z_to_bv 64 R27) fc None m (seg_rom rsegs)).
Proof.
  intros X d h pl regs0 i n now len f (HX0 & HX16 & HX1 & HXlo) (Hd0 & Hd1 & Hd2 & Hdns) R F fc m
    (Hn & Hlen & G19 & G20 & C152 & C248 & Hi & Hnow & G2 & G3 & G4 & G18 & G24 & G26 & C160 & C224 & HM).
  unfold rmk. eapply evt_mono.
  { eapply uslot_R27_call with (X := X) (f := f) (len := len) (rem := n)
      (body := d + (Z.of_nat (length pl) - n)); first [eassumption | unfold SLOT_FRAME in *; lia]. }
  intros ms ->. eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. exists (n - len), now.
  split; [lia|]. split.
  { change (Z_to_bv 64 (d + (Z.of_nat (length pl) - n) + len) =
      Z_to_bv 64 (d + (Z.of_nat (length pl) - (n - len)))). f_equal; lia. }
  split; [reflexivity|].
  split; [exact Hi|]. split; [exact Hnow|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
  split; [exact G18|]. split; [exact G24|]. split; [exact G26|]. split; [exact C160|]. split; [exact C224|].
  exact HM.
Qed.

Lemma R27RET_ev : forall X d h pl regs0 i, xok X ->
  forall R F fc m, P_R27RET X d h pl regs0 i R m ->
  evt rsegs (fun ms => exists R', ms = MS R' F (Z_to_bv 64 LATCH) fc None m (seg_rom rsegs) /\
    P_LAT X d h pl regs0 i R' m)
    (MS (rmk R) F (Z_to_bv 64 R27_RET) fc None m (seg_rom rsegs)).
Proof.
  intros X d h pl regs0 i (HX0 & HX16 & HX1 & HXlo) R F fc m
    (n & now & Hn & G21 & G23 & Hi & Hnow & G2 & G3 & G4 & G18 & G24 & G26 & C160 & C224 & HM).
  unfold rmk. eapply evt_mono.
  { eapply uslot_R27_ret with (X := X) (now := now); first [eassumption | unfold SLOT_FRAME in *; lia]. }
  intros ms ->. eexists. split; [reflexivity|].
  exists n, now. split; [exact Hn|]. split; [reflexivity|]. split; [exact G21|]. split; [exact G23|].
  split; [reflexivity|].
  split; [exact Hi|]. split; [exact Hnow|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
  split; [exact G18|]. split; [exact G24|]. split; [exact G26|]. split; [exact C160|]. split; [exact C224|].
  exact HM.
Qed.
