From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Reusable Require Import YK11 YK0o YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0 KindBGlue FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_ser_defs slot_ser_pure.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c slot_inv uslot_norm uslot_seg uslot_preds uslot_cells.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import disco_table_c hunt_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_disco_table_age_c check_table_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import slot_lib uslot_R4 uslot_age uslot_frame uslot_ser_defs uslot_ser_iface.
Import ListNotations.
Open Scope Z_scope.

Definition P_SM (X d h : Z) (pl : list byte) (regs0 : bvmap 5 word) (i n now cap : Z)
    (R : bvmap 5 word) (m : word -> option byte) : Prop :=
  0 <= n <= Z.of_nat (length pl) /\ 2 <= cap <= 1280 /\
  getr R 1 = Z_to_bv 64 uSER_RET /\ getr R 10 = Z_to_bv 64 cap /\
  getr R 21 = Z_to_bv 64 cap /\ getr R 27 = Z_to_bv 64 1 /\
  rw_cells rsegs m (X + 136) [C8 (Z_to_bv 64 n)] /\
  rw_cells rsegs m (X + 152) [C8 (Z_to_bv 64 (d + (Z.of_nat (length pl) - n)))] /\
  P_BASE X d h pl regs0 i now R m.

Definition P_FM (X d h : Z) (pl : list byte) (regs0 : bvmap 5 word) (i n now len k : Z) (ob : byte)
    (R : bvmap 5 word) (m : word -> option byte) : Prop :=
  0 <= n <= Z.of_nat (length pl) /\ 0 <= len <= n /\ len < 65536 /\ 0 <= k <= 2 /\
  getr R 1 = Z_to_bv 64 R17_RET /\ getr R 10 = Z_to_bv 64 len /\
  getr R 19 = Z_to_bv 64 len /\ getr R 20 = Z_to_bv 64 n /\
  getr R 21 = Z_to_bv 64 k /\ getr R 22 = Z_to_bv 64 (d + (Z.of_nat (length pl) - n)) /\
  getr R 8 = sxb ob /\ getr R 25 = Z_to_bv 64 (bv_unsigned ob) /\
  getr R 9 = Z_to_bv 64 now /\ getr R 27 = Z_to_bv 64 1 /\
  P_BASE X d h pl regs0 i now R m.

Definition W_B1 (X : Z) : list (Z * Z) :=
  [(LO X, X); (X + 136, X + 144); (X + 152, X + 168); (X + 224, X + 232); (X + 544, X + 944)].

Lemma rest_bytes : forall m d pl n, 0 <= n <= Z.of_nat (length pl) -> bytes_at rsegs m d pl ->
  bytes_at rsegs m (d + (Z.of_nat (length pl) - n)) (rest_of pl n) /\
  Z.of_nat (length (rest_of pl n)) = n.
Proof.
  intros m d pl n Hn BD. unfold rest_of.
  assert (E : Z.of_nat (length pl - Z.to_nat n) = Z.of_nat (length pl) - n) by lia.
  split.
  - rewrite <- E. rewrite <- (firstn_skipn (length pl - Z.to_nat n) pl) in BD.
    apply bytes_at_app in BD as [_ BD]. rewrite length_firstn in BD.
    replace (Nat.min (length pl - Z.to_nat n) (length pl)) with (length pl - Z.to_nat n)%nat in BD by lia.
    exact BD.
  - rewrite length_skipn. lia.
Qed.

Lemma now_step_range : forall op dt now, 0 <= dt -> 0 <= now < 2 ^ 64 ->
  0 <= now_step op dt now < 2 ^ 64.
Proof.
  intros op dt now Hd Hn. unfold now_step.
  destruct (op <? 128); [apply Z.mod_pos_bound; lia|].
  destruct (Z.ltb_spec now (dt * MS_NS)); unfold MS_NS in *; lia.
Qed.

Lemma seg_B1 : reac_disco_table_age_contract -> check_table_contract -> uslot_ser_chain_A ->
  forall X d h pl regs0 i, xok X -> dok X d pl -> 0 < d ->
  seg_ev HDR (W_B1 X) (fun R m => P_HDR X d h pl regs0 i R m /\ fenv X [(h, 480)] m)
    (fun q R m => q = MALLOC_PC /\
      ((exists n now cap, P_SM X d h pl regs0 i n now cap R m) \/
       (exists n now len k ob, P_FM X d h pl regs0 i n now len k ob R m))).
Proof.
  intros AGE CHECK SERA X d h pl regs0 i HX HD Hdp fx' regs m0 Hf HI
    ((n & now & Hn & Hnow & Hi & G2 & G3 & G4 & G5 & G9 & G18 & G21 & G23 & G24 & G26 & G27 & HM) &
     (STK & HBK)).
  destruct (HBK h 480 (or_introl eq_refl)) as (Hh0 & Hh1 & _). clear HBK.
  pose proof (mem_inv_of_cj m0 HI) as MI.
  unfold xok, dok, LO, SLOT_FRAME, SLOT_STACK, IMG_HI in *.
  destruct HX as (HX0 & HX16 & HX1 & HXlo). destruct HD as (Hd0 & Hd1 & Hd2 & _).
  assert (Hi64 : 0 <= i < 2 ^ 64) by (unfold MAX_OPS in Hi; lia).
  pose proof (stk_sub m0 _ _ (X + 2624 - 65536) X STK ltac:(lia) ltac:(lia) ltac:(lia)) as ST. clear STK.
  hdr_open HM.
  destruct (rest_bytes m0 d pl n ltac:(lia) BD) as [BR LR].
  assert (HOP : 0 <= rdb (rest_of pl n) 0 < 256) by (unfold rdb; apply byte_range).
  assert (HDT : 0 <= dt_of (rest_of pl n)) by (unfold dt_of, rdb; pose proof (byte_range (nth 1 (rest_of pl n) (Z_to_bv 8 0))); pose proof (byte_range (nth 2 (rest_of pl n) (Z_to_bv 8 0))); lia).
  pose proof (now_step_range (rdb (rest_of pl n) 0) _ _ HDT Hnow) as HNOW.
  pose proof (munch_refl (W_B1 X) m0) as MU. pose proof (wmono_refl rsegs m0) as WM. unfold W_B1, LO, SLOT_FRAME, SLOT_STACK in MU.
  assert (R144 : ov_read_bytes rsegs m0 (wa (X + 144)) 8 = Some (le8 (Z_to_bv 64 MS_NS))).
  { eapply rw_cells_read_at with (k := 0%nat) (c := C8 (Z_to_bv 64 MS_NS));
      [exact C144|reflexivity|reflexivity|]; f_equal; lia. }
  pose proof (rw_c8_cb m0 (X + 160) j160 C160) as C160b.
  pose proof (rw_c8_cb m0 (X + 224) j224 C224) as C224b.
  unfold rmk. eapply evt_cut.
  { eapply (uslot_R4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m0 X n
      (d + (Z.of_nat (length pl) - n)) now i (rest_of pl n) (le8 j160) (le8 j224)); try eassumption; lia. }
  intros ms (a1' & m1 & -> & MU1 & WM1 & MI1 & C160' & C224').
  clear R144.
  transport_after_call rsegs m0 m1 MU1 WM1. clear MU1 WM1.
  set (now' := now_step (rdb (rest_of pl n) 0) (dt_of (rest_of pl n)) now) in *.
  assert (HN : 0 <= n - op_take n <= Z.of_nat (length pl)) by (unfold op_take; lia).
  destruct (Z.eqb_spec (rdb (rest_of pl n) 0 mod 4) 3) as [Hop|Hop].
  - clear BR.
    eapply evt_cut.
    { eapply (uslot_R5_R7 AGE CHECK) with (X := X) (lo := X + 2624 - 65536) (now := now') (T := T);
        try first [reflexivity | eassumption | exact (proj1 TOK) | exact (proj1 (proj2 TOK)) |
          exact (proj1 (proj2 (proj2 TOK))) | exact (proj2 (proj2 (proj2 TOK))) | unfold CHECK_TABLE_K; lia | lia]. }
    intros ms (ra' & t0' & t1' & t2' & s0' & a0'' & a1'' & a2' & a3' & a4' & a5' & a6' & a7' & s3' & s4' & s5' &
      t3' & t4' & t5' & t6' & m2 & T' & removed & -> & MU2 & WM2 & MI2 & ST2 & C120' & CT' & AM & AP & T1 & T2 & T3 & T4).
    transport_after_call rsegs m1 m2 MU2 WM2. clear MU2 WM2.
    pose proof (rw_c8_cb m2 (X + 136) j136 C136) as C136b.
    pose proof (rw_c8_cb m2 (X + 152) j152 C152) as C152b.
    eapply evt_cut.
    { eapply (SERA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X (rdb (rest_of pl n) 0)
        (le8 j136) (le8 j152)); try first [reflexivity | eassumption | lia]. }
    intros ms (a1''' & m3 & -> & MU3 & WM3 & MI3 & C136' & C152').
    transport_after_call rsegs m2 m3 MU3 WM3. clear MU3 WM3.
    destruct (ser_cap_range _ HOP) as [HC EC]. rewrite EC.
    replace (d + (Z.of_nat (length pl) - n) + op_take n) with
      (d + (Z.of_nat (length pl) - (n - op_take n))) in C152' by lia.
    apply evt_done. do 2 eexists. exists MALLOC_PC. do 2 eexists.
    split; [reflexivity|]. split; [exact Hf|]. split; [unfold W_B1, LO, SLOT_FRAME, SLOT_STACK; exact MU|].
    split; [exact WM|]. split; [reflexivity|]. left.
    exists (n - op_take n), now', (ser_cap (rdb (rest_of pl n) 0)).
    split; [exact HN|]. split; [exact HC|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact G27|]. split; [exact C136'|]. split; [exact C152'|].
    split; [exact Hi|]. split; [exact HNOW|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
    split; [exact G18|]. split; [exact G24|]. split; [exact G26|]. split; [exact C160'|]. split; [exact C224'|].
    assert (TOK' : table_ok T') by exact (conj T1 (conj T2 (conj T3 T4))).
    hdr_close.
  - destruct (rest_bytes m1 d pl (n - op_take n) HN BD) as [BR1 LR1].
    replace (d + (Z.of_nat (length pl) - n) + op_take n) with
      (d + (Z.of_nat (length pl) - (n - op_take n))) by lia.
    eapply evt_cut.
    { eapply (uslot_R17_call) with (X := X) (n := n - op_take n)
        (p := d + (Z.of_nat (length pl) - (n - op_take n))) (R := rest_of pl (n - op_take n));
        try first [reflexivity | eassumption | lia]. }
    intros ms (a1'' & a2'' & ->).
    assert (HR : 0 <= rec_rem (n - op_take n) <= Z.of_nat (length pl)) by (unfold rec_rem, rec_take; lia).
    assert (HL : 0 <= rec_len (rest_of pl (n - op_take n)) (n - op_take n) <= rec_rem (n - op_take n) /\
      rec_len (rest_of pl (n - op_take n)) (n - op_take n) < 65536).
    { pose proof (byte_range (nth 0 (rest_of pl (n - op_take n)) (Z_to_bv 8 0))).
      pose proof (byte_range (nth 1 (rest_of pl (n - op_take n)) (Z_to_bv 8 0))).
      unfold rec_len, rec_want, rdb. lia. }
    assert (HK : 0 <= rdb (rest_of pl n) 0 mod 4 <= 2) by (pose proof (Z.mod_pos_bound (rdb (rest_of pl n) 0) 4 ltac:(lia)); lia).
    apply evt_done. do 2 eexists. exists MALLOC_PC. do 2 eexists.
    split; [reflexivity|]. split; [exact Hf|]. split; [unfold W_B1, LO, SLOT_FRAME, SLOT_STACK; exact MU|].
    split; [exact WM|]. split; [reflexivity|]. right.
    exists (rec_rem (n - op_take n)), now', (rec_len (rest_of pl (n - op_take n)) (n - op_take n)),
      (rdb (rest_of pl n) 0 mod 4), (nth 0 (rest_of pl n) (Z_to_bv 8 0)).
    split; [exact HR|]. split; [exact (proj1 HL)|]. split; [exact (proj2 HL)|]. split; [exact HK|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|].
    split.
    { change (Z_to_bv 64 (d + (Z.of_nat (length pl) - (n - op_take n)) + rec_take (n - op_take n)) =
        Z_to_bv 64 (d + (Z.of_nat (length pl) - rec_rem (n - op_take n)))). f_equal; unfold rec_rem; lia. }
    split; [symmetry; apply sxb_swrap|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact G27|].
    split; [exact Hi|]. split; [exact HNOW|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
    split; [exact G18|]. split; [exact G24|]. split; [exact G26|]. split; [exact C160'|]. split; [exact C224'|].
    hdr_close.
Qed.
