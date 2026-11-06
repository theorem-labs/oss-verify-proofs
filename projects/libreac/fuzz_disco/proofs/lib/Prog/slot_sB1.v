From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YK0o YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0 KindBGlue FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import LLVMFuzzerTestOneInput_c slot_inv slot_norm slot_seg slot_preds slot_cells.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_classify_c disco_table_c hunt_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_disco_table_age_c check_table_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_lib slot_R4 slot_age slot_frame slot_ser_defs slot_ser_pure slot_ser_iface.
Import ListNotations.
Open Scope Z_scope.

Definition P_BASE (X d h : Z) (pl : list byte) (regs0 : bvmap 5 word) (i now : Z)
    (R : bvmap 5 word) (m : word -> option byte) : Prop :=
  0 <= i < MAX_OPS /\ 0 <= now < 2 ^ 64 /\
  getr R 2 = Z_to_bv 64 X /\ getr R 3 = getr regs0 3 /\ getr R 4 = Z_to_bv 64 0x31260 /\
  getr R 8 = Z_to_bv 64 32 /\ getr R 9 = Z_to_bv 64 i /\ getr R 18 = Z_to_bv 64 WS_MASK /\
  getr R 24 = Z_to_bv 64 (X + 2336) /\ getr R 27 = Z_to_bv 64 now /\ hdr_mem X d h pl regs0 m.

Definition P_SM (X d h : Z) (pl : list byte) (regs0 : bvmap 5 word) (i n now cap : Z)
    (R : bvmap 5 word) (m : word -> option byte) : Prop :=
  0 <= n <= Z.of_nat (length pl) /\ 2 <= cap <= 1280 /\
  getr R 1 = Z_to_bv 64 SER_RET /\ getr R 10 = Z_to_bv 64 cap /\
  getr R 21 = Z_to_bv 64 cap /\ getr R 23 = Z_to_bv 64 (d + (Z.of_nat (length pl) - n)) /\
  rw_cells rsegs m (X + 152) [C8 (Z_to_bv 64 n)] /\
  rw_cells rsegs m (X + 200) [C8 (Z_to_bv 64 now)] /\ P_BASE X d h pl regs0 i now R m.

Definition P_FM (X d h : Z) (pl : list byte) (regs0 : bvmap 5 word) (i n now len k : Z) (ob : byte)
    (R : bvmap 5 word) (m : word -> option byte) : Prop :=
  0 <= n <= Z.of_nat (length pl) /\ 0 <= len <= n /\ len < 65536 /\ 0 <= k <= 2 /\
  getr R 1 = Z_to_bv 64 R17_RET /\ getr R 10 = Z_to_bv 64 len /\
  getr R 19 = Z_to_bv 64 len /\ getr R 21 = Z_to_bv 64 k /\
  getr R 22 = Z_to_bv 64 (d + (Z.of_nat (length pl) - n)) /\ getr R 23 = Z_to_bv 64 n /\
  getr R 20 = Z_to_bv 64 h /\ getr R 25 = sxb ob /\
  rw_cells rsegs m (X + 200) [C8 (Z_to_bv 64 now)] /\
  rw_cells rsegs m (X + 216) [C8 (Z_to_bv 64 (bv_unsigned ob))] /\
  P_BASE X d h pl regs0 i now R m.

Definition W_B1 (X : Z) : list (Z * Z) :=
  [(LO X, X); (X + 152, X + 160); (X + 200, X + 208); (X + 216, X + 224); (X + 512, X + 912)].

Ltac hdr_open H :=
  destruct H as ([j0 C0] & C24 & C32 & [j40 C40] & C144 & [j152 C152] & [j160 C160] & C168 & C176 &
    [j184 C184] & [j192 C192] & [j200 C200] & C208 & [j216 C216] & [j224 C224] & [j232 C232] &
    [Lk CLK] & (Gt & CGT & GOK) & (T & CT & TOK) & [j912 C912] & C914 & [j920 C920] & [j1024 C1024] &
    [j1048 C1048] & CSV & (Hunt & CH & HOK & OUR) & BD).

Ltac hdr_close := unfold hdr_mem, junk8, junkb; repeat first [eassumption | split | eexists].

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

Lemma seg_B1 : reac_disco_table_age_contract -> check_table_contract -> ser_chain_A ->
  forall X d h pl regs0 i, xok X -> dok X d pl ->
  seg_ev HDR (W_B1 X) (fun R m => P_HDR X d h pl regs0 i R m /\ fenv X [(h, 480)] m)
    (fun q R m => q = MALLOC_PC /\
      ((exists n now cap, P_SM X d h pl regs0 i n now cap R m) \/
       (exists n now len k ob, P_FM X d h pl regs0 i n now len k ob R m))).
Proof.
  intros AGE CHECK SERA X d h pl regs0 i HX HD fx' regs m0 Hf HI
    ((n & now & Hn & Hnow & Hi & G2 & G3 & G4 & G8 & G9 & G14 & G18 & G19 & G20 & G21 & G24 & G27 & HM) &
     (STK & HBK)).
  destruct (HBK h 480 (or_introl eq_refl)) as (Hh0 & Hh1 & _). clear HBK.
  pose proof (mem_inv_of_cj m0 HI) as MI.
  unfold xok, dok, LO, SLOT_FRAME, SLOT_STACK, IMG_HI in *.
  destruct HX as (HX0 & HX16 & HX1 & HXlo). destruct HD as (Hd0 & Hd1 & Hd2 & _).
  pose proof (stk_sub m0 _ _ (X + 2592 - 65536) X STK ltac:(lia) ltac:(lia) ltac:(lia)) as ST. clear STK.
  hdr_open HM.
  destruct (rest_bytes m0 d pl n ltac:(lia) BD) as [BR LR].
  assert (HOP : 0 <= rdb (rest_of pl n) 0 < 256) by (unfold rdb; apply byte_range).
  assert (HDT : 0 <= dt_of (rest_of pl n)) by (unfold dt_of, rdb; pose proof (byte_range (nth 1 (rest_of pl n) (Z_to_bv 8 0))); pose proof (byte_range (nth 2 (rest_of pl n) (Z_to_bv 8 0))); lia).
  pose proof (now_step_range (rdb (rest_of pl n) 0) _ _ HDT Hnow) as HNOW.
  pose proof (munch_refl (W_B1 X) m0) as MU. pose proof (wmono_refl rsegs m0) as WM. unfold W_B1, LO, SLOT_FRAME, SLOT_STACK in MU.
  assert (R168 : ov_read_bytes rsegs m0 (wa (X + 168)) 8 = Some (le8 (Z_to_bv 64 MS_NS))).
  { eapply rw_cells_read_at with (k := 0%nat) (c := C8 (Z_to_bv 64 MS_NS));
      [exact C168|reflexivity|reflexivity|]; f_equal; lia. }
  assert (ST200 : store_ok rsegs m0 (wa (X + 200)) 8 = true).
  { eapply rw_cells_store_ok_at with (k := 0%nat); [exact C200|reflexivity|reflexivity|]; f_equal; lia. }
  unfold rmk. eapply evt_cut.
  { eapply (slot_R4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m0 X n
      (d + (Z.of_nat (length pl) - n)) now (rest_of pl n)); try eassumption; lia. }
  intros ms (a1' & ->).
  set (now' := now_step (rdb (rest_of pl n) 0) (dt_of (rest_of pl n)) now) in *.
  pose proof (rw_cells_write rsegs m0 (X + 200) [C8 j200] 0 (C8 j200) (C8 (Z_to_bv 64 now'))
    C200 eq_refl eq_refl I) as C200'.
  cbn [cell_upd cbytes Nat.eqb] in C200'. rewrite Z.add_0_r in C200'. clear C200.
  pose proof (mem_inv_store rsegs m0 (wa (X + 200)) (le8 (Z_to_bv 64 now')) MI ltac:(rewrite length_le8; exact ST200)) as MI1.
  transport_chunks rsegs m0 (X + 200) (le8 (Z_to_bv 64 now')).
  footprint_after_store rsegs m0 (X + 200) (le8 (Z_to_bv 64 now')).
  set (m1 := write_to_mem m0 (wa (X + 200)) (le8 (Z_to_bv 64 now'))) in *.
  clear R168 ST200 MI BR.
  assert (HN : 0 <= n - op_take n <= Z.of_nat (length pl)) by (unfold op_take; lia).
  destruct (Z.eqb_spec (rdb (rest_of pl n) 0 mod 4) 3) as [Hop|Hop].
  - eapply evt_cut.
    { eapply (slot_R5_R7 AGE CHECK) with (X := X) (lo := X + 2592 - 65536)
        (n := n - op_take n) (p := d + (Z.of_nat (length pl) - n) + op_take n) (now := now') (T := T);
        try first [reflexivity | eassumption | exact (proj1 TOK) | exact (proj1 (proj2 TOK)) |
          exact (proj1 (proj2 (proj2 TOK))) | exact (proj2 (proj2 (proj2 TOK))) | unfold CHECK_TABLE_K; lia]. }
    intros ms (t0' & t1' & t2' & a0'' & a1'' & a2' & a3' & a4' & a5' & a6' & a7' & s3' & s4' & s5' & s6' &
      t3' & t4' & t5' & t6' & m2 & T' & removed & -> & MU2 & WM2 & MI2 & ST2 & C152' & C176' & CT' & AM & AP & T1 & T2 & T3 & T4).
    transport_after_call rsegs m1 m2 MU2 WM2. clear MU2 WM2.
    eapply evt_cut.
    { eapply SERA; [reflexivity|exact HOP]. }
    intros ms (a1''' & ->).
    destruct (ser_cap_range _ HOP) as [HC EC]. rewrite EC.
    apply evt_done. do 2 eexists. exists MALLOC_PC. do 2 eexists.
    split; [reflexivity|]. split; [exact Hf|]. split; [unfold W_B1, LO, SLOT_FRAME, SLOT_STACK; exact MU|].
    split; [exact WM|]. split; [reflexivity|]. left.
    exists (n - op_take n), now', (ser_cap (rdb (rest_of pl n) 0)).
    split; [exact HN|]. split; [exact HC|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split.
    { change (Z_to_bv 64 (d + (Z.of_nat (length pl) - n) + op_take n) =
        Z_to_bv 64 (d + (Z.of_nat (length pl) - (n - op_take n)))). f_equal; lia. }
    split; [exact C152'|]. split; [exact C200'|].
    split; [exact Hi|]. split; [exact HNOW|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
    split; [exact G8|]. split; [exact G9|]. split; [exact G18|]. split; [exact G24|]. split; [reflexivity|].
    assert (TOK' : table_ok T') by exact (conj T1 (conj T2 (conj T3 T4))).
    hdr_close.
  - destruct (rest_bytes m1 d pl (n - op_take n) HN BD) as [BR LR1].
    replace (d + (Z.of_nat (length pl) - n) + op_take n) with
      (d + (Z.of_nat (length pl) - (n - op_take n))) by lia.
    eapply evt_cut.
    { eapply (slot_R17_call) with (X := X) (n := n - op_take n)
        (p := d + (Z.of_nat (length pl) - (n - op_take n))) (R := rest_of pl (n - op_take n));
        try first [reflexivity | eassumption | lia]. }
    intros ms (a1'' & m2 & -> & MU2 & WM2 & MI2 & C216').
    transport_after_call rsegs m1 m2 MU2 WM2. clear MU2 WM2.
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
    split.
    { change (Z_to_bv 64 (d + (Z.of_nat (length pl) - (n - op_take n)) + rec_take (n - op_take n)) =
        Z_to_bv 64 (d + (Z.of_nat (length pl) - rec_rem (n - op_take n)))). f_equal; unfold rec_rem; lia. }
    split; [reflexivity|]. split; [exact G20|]. split; [symmetry; apply sxb_swrap|].
    split; [exact C200'|]. split; [exact C216'|].
    split; [exact Hi|]. split; [exact HNOW|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
    split; [exact G8|]. split; [exact G9|]. split; [exact G18|]. split; [exact G24|]. split; [reflexivity|].
    hdr_close.
Qed.
