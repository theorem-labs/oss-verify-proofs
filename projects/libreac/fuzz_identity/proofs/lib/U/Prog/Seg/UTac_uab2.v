From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac ZBridge
Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec RcIdentModel SlotModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require reac_identity_fw_str_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Spec Require StrFun.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import ListNotations.
Open Scope Z_scope.

Lemma sb2_bz_zb : forall x, bz (zb x) = x mod 256.
Proof. intros x. unfold bz, zb. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma sb2_digits : forall p j, all_digits (firstn 4 p) = true -> (j < 4)%nat -> (j < length p)%nat ->
  bz (nthb p j) <= 9.
Proof.
  intros p j H Hj Hl. unfold all_digits in H. rewrite forallb_forall in H.
  assert (E : nthb p j = nth j (firstn 4 p) (zb 0)) by (unfold nthb; symmetry; apply nth_first; exact Hj).
  rewrite E. apply Z.leb_le. apply H. apply nth_In. rewrite length_firstn. lia.
Qed.

Lemma sb2_ing_fw : forall idb a p, length idb = ID_SIZE -> fst (ING idb a p) = 1 ->
  a <> ADDR_MODEL_NAME -> a <> ADDR_REAC_VERSION ->
  a = ADDR_FIRMWARE /\ (4 <= length p)%nat /\ all_digits (firstn 4 p) = true /\
  has_fw (snd (ING idb a p)) = 1 /\ fw_milli (snd (ING idb a p)) = fw_value p.
Proof.
  intros idb a p Hl Hr Hn Hv. unfold ING in *.
  destruct (Z.eqb_spec a ADDR_FIRMWARE) as [Ea|Ea].
  - subst a. unfold ing_firmware in *.
    destruct ((4 <=? length p)%nat && all_digits (firstn 4 p)) eqn:E; cbn [fst snd] in *; [|discriminate].
    apply andb_true_iff in E as [E1 E2]. apply Nat.leb_le in E1.
    assert (D : forall j, (j < 4)%nat -> 0 <= bz (nthb p j) <= 9).
    { intros j Hj. split; [unfold bz; apply bv_unsigned_in_range | apply sb2_digits; [exact E2 | exact Hj | lia]]. }
    assert (V : 0 <= fw_value p <= 9999).
    { unfold fw_value. pose proof (D 0%nat ltac:(lia)). pose proof (D 1%nat ltac:(lia)).
      pose proof (D 2%nat ltac:(lia)). pose proof (D 3%nat ltac:(lia)). lia. }
    assert (L1 : length (upd idb OFF_FW (le16 (fw_value p))) = length idb)
      by (apply upd_length; rewrite Hl; cbn; unfold OFF_FW, ID_SIZE; lia).
    split; [reflexivity|]. split; [exact E1|]. split; [exact E2|]. split.
    + unfold has_fw, nthb, OFF_HAS_FW.
      rewrite nth_upd_in by (rewrite ?L1, ?Hl; cbn [length]; unfold OFF_HAS_FW, ID_SIZE; lia).
      reflexivity.
    + unfold fw_milli, nthb.
      rewrite (nth_upd_before _ _ OFF_HAS_FW 0), (nth_upd_before _ _ OFF_HAS_FW 1)
        by (rewrite ?L1, ?Hl; unfold OFF_HAS_FW, ID_SIZE; lia).
      unfold OFF_FW. rewrite !nth_upd_in by (rewrite ?Hl; cbn [length le16]; unfold ID_SIZE; lia).
      cbn [Nat.sub nth le16]. rewrite !sb2_bz_zb.
      rewrite !Z.mod_mod by lia.
      Z.div_mod_to_equations. lia.
  - destruct (Z.eqb_spec a ADDR_MODEL_NAME) as [En|En]; [contradiction|].
    destruct (Z.eqb_spec a ADDR_REAC_VERSION) as [Ev|Ev]; [contradiction|].
    cbn [fst] in Hr. discriminate.
Qed.

Lemma sb2_fw_value_range : forall p, (4 <= length p)%nat -> all_digits (firstn 4 p) = true ->
  0 <= fw_value p <= 9999.
Proof.
  intros p Hl H.
  assert (D : forall j, (j < 4)%nat -> 0 <= bz (nthb p j) <= 9).
  { intros j Hj. split; [unfold bz; apply bv_unsigned_in_range | apply sb2_digits; [exact H | exact Hj | lia]]. }
  unfold fw_value. pose proof (D 0%nat ltac:(lia)). pose proof (D 1%nat ltac:(lia)).
  pose proof (D 2%nat ltac:(lia)). pose proof (D 3%nat ltac:(lia)). lia.
Qed.

Lemma sb2_pick_range : forall raw, 0 <= raw < 65536 -> 0 <= pick raw < 65536.
Proof.
  intros raw H. unfold pick, ADDR_FIRMWARE, ADDR_REAC_VERSION, ADDR_MODEL_NAME.
  destruct (raw / 16384 =? 0); [lia|]. destruct (raw / 16384 =? 1); [lia|].
  destruct (raw / 16384 =? 2); lia.
Qed.

Lemma sb2_rec_addr_range : forall inp i, 0 <= rec_addr inp i < 65536.
Proof.
  intros inp i. unfold rec_addr, rec_raw, h_raw, h_lo, h_hi. apply sb2_pick_range.
  pose proof (inb_range inp (rec_c inp i)). pose proof (inb_range inp (rec_c inp i + 1)). lia.
Qed.

Lemma sb2_rec_fw : forall inp i, rec_r inp i = 1 -> rec_addr inp i <> ADDR_MODEL_NAME ->
  rec_addr inp i <> ADDR_REAC_VERSION ->
  rec_addr inp i = ADDR_FIRMWARE /\ 4 <= rec_k inp i /\
  (forall j, (j < 4)%nat -> bz (nthb (rec_pl inp i) j) <= 9) /\
  has_fw (rec_id inp (S i)) = 1 /\ fw_milli (rec_id inp (S i)) = fw_value (rec_pl inp i) /\
  0 <= fw_value (rec_pl inp i) <= 9999.
Proof.
  intros inp i Hr Hn Hv. unfold rec_r in Hr. cbn [rec_id].
  destruct (sb2_ing_fw (rec_id inp i) (rec_addr inp i) (rec_pl inp i) (rec_id_length inp i) Hr Hn Hv)
    as (E1 & E2 & E3 & E4 & E5).
  pose proof (rec_pl_length inp i) as PL. pose proof (rec_k_range inp i) as KR.
  split; [exact E1|]. split; [lia|]. split.
  { intros j Hj. apply sb2_digits; [exact E3 | exact Hj | lia]. }
  split; [exact E4|]. split; [exact E5|]. apply sb2_fw_value_range; assumption.
Qed.

Lemma sb2_rec_hw_keep : forall inp i, rec_addr inp i <> ADDR_REAC_VERSION ->
  rec_hw inp (S i) = rec_hw inp i.
Proof.
  intros inp i H. cbn [rec_hw]. destruct (Z.eqb_spec (rec_addr inp i) ADDR_REAC_VERSION) as [E|E];
    [contradiction | reflexivity].
Qed.

Lemma sb2_FW_digits : forall p, (4 <= length p)%nat -> all_digits (firstn 4 p) = true ->
  reac_identity_fw_str_c.FW (fw_value p) =
  [dg (bz (nthb p 0)); Z_to_bv 8 0x2e; dg (bz (nthb p 1)); dg (bz (nthb p 2)); dg (bz (nthb p 3))].
Proof.
  intros p Hl H. pose proof (sb2_fw_value_range p Hl H) as V.
  rewrite reac_identity_fw_str_c.reac_identity_fw_str_c3_short by lia.
  assert (D : forall j, (j < 4)%nat -> 0 <= bz (nthb p j) <= 9).
  { intros j Hj. split; [unfold bz; apply bv_unsigned_in_range | apply sb2_digits; [exact H | exact Hj | lia]]. }
  pose proof (D 0%nat ltac:(lia)). pose proof (D 1%nat ltac:(lia)).
  pose proof (D 2%nat ltac:(lia)). pose proof (D 3%nat ltac:(lia)).
  unfold fw_value.
  replace ((bz (nthb p 0) * 1000 + bz (nthb p 1) * 100 + bz (nthb p 2) * 10 + bz (nthb p 3)) / 1000)
    with (bz (nthb p 0)) by (Z.div_mod_to_equations; lia).
  replace ((bz (nthb p 0) * 1000 + bz (nthb p 1) * 100 + bz (nthb p 2) * 10 + bz (nthb p 3)) mod 1000 / 100)
    with (bz (nthb p 1)) by (Z.div_mod_to_equations; lia).
  replace ((bz (nthb p 0) * 1000 + bz (nthb p 1) * 100 + bz (nthb p 2) * 10 + bz (nthb p 3)) mod 1000 / 10 mod 10)
    with (bz (nthb p 2)) by (Z.div_mod_to_equations; lia).
  replace ((bz (nthb p 0) * 1000 + bz (nthb p 1) * 100 + bz (nthb p 2) * 10 + bz (nthb p 3)) mod 1000 mod 10)
    with (bz (nthb p 3)) by (Z.div_mod_to_equations; lia).
  reflexivity.
Qed.

Lemma sb2_fs_bound : forall (l : list Segment) (x n : Z) s, find_segment l x n = Some s ->
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 2 ^ 40) l = true -> x + n <= 2 ^ 40.
Proof.
  induction l as [|s0 l IH]; intros x n s E F; cbn [find_segment] in E; [discriminate|].
  cbv zeta in E. cbn [forallb] in F. apply andb_prop in F as [F1 F2]. apply Z.leb_le in F1.
  revert E. match goal with |- (if ?k then _ else _) = _ -> _ => destruct k eqn:C end; intros E.
  - apply andb_prop in C as [_ C2]. apply Z.leb_le in C2. lia.
  - exact (IH x n s E F2).
Qed.

Lemma sb2_fs_none : forall x, 2 ^ 40 <= x -> find_segment rsegs x 1 = None.
Proof.
  intros x H. destruct (find_segment rsegs x 1) as [s|] eqn:E; [|reflexivity].
  exfalso. pose proof (sb2_fs_bound rsegs x 1 s E ltac:(vm_compute; reflexivity)). lia.
Qed.

Lemma sb2_wview_mrd : forall (m : word -> option byte) (x : word), 2 ^ 40 <= bv_unsigned x ->
  wview rsegs m x <> None -> exists b, mrd rsegs m x = Some b.
Proof.
  intros m x Hx W. unfold wview in W. unfold mrd.
  destruct (m x) as [b|]; [exists b; reflexivity|].
  rewrite (sb2_fs_none _ Hx) in W. contradiction.
Qed.

Lemma sb2_ro_hi : forall x : word, 2 ^ 40 <= bv_unsigned x -> ro_addr rsegs x = false.
Proof. intros x H. unfold ro_addr. rewrite (sb2_fs_none _ H). reflexivity. Qed.

Lemma sb2_img_lt : forall B, ms_segs B = rsegs -> forall a, in_img B a -> 0 <= a < 2 ^ 40.
Proof.
  intros B SEG a Ha. unfold in_img in Ha. destruct Ha as [_ (s & Hin & Ha)]. rewrite SEG in Hin.
  assert (H : forallb (fun s => bv_unsigned (fst s) + bv_unsigned (snd s) <=? 2 ^ 40) (segments_reserved rsegs) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H s Hin). apply Z.leb_le in H.
  pose proof (bv_unsigned_in_range 64 (fst s)). lia.
Qed.

Lemma sb2_ro_lt : forall x : word, ro_addr rsegs x = true -> bv_unsigned x < 2 ^ 40.
Proof.
  intros x H. destruct (Z_lt_le_dec (bv_unsigned x) (2 ^ 40)) as [h|h]; [exact h|].
  rewrite (sb2_ro_hi x h) in H. discriminate.
Qed.

Lemma sb2_canon_mkst : forall {fx : FPState} (regs : bvmap 5 word) (pc : word) (mem ro : word -> option byte),
  RegisterBridge.canonical_register_state (OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable.YK11.mkst regs pc mem ro) =
  MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem ro.
Proof. reflexivity. Qed.

Lemma sb2_eqv_mkst : forall {fx : FPState} (R : bvmap 5 word) (pc : word) (m ro : word -> option byte) ms',
  Regs6ss.ms_eqv (MS R fp_regs pc fp_csr None m ro) ms' ->
  exists R', ms' = OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable.YK11.mkst R' pc m ro /\ Regs6ss.xregs_eqv R R'.
Proof.
  intros fx R pc m ro [R' F' pc' svc' rv' fc' m' ro'] (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro).
  cbn in HF, Hpc, Hsvc, Hrv, Hfc, Hm, Hro. subst. exists R'. split; [reflexivity | exact HR].
Qed.

Lemma sb2_getr_x : forall (R R' : bvmap 5 word) (r : bv 5),
  Regs6ss.xregs_eqv R R' -> is_x0 r = false -> OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable.YK11.getr R' r = OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable.YK11.getr R r.
Proof.
  intros R R' r H H0. unfold OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable.YK11.getr. unfold is_x0 in H0.
  destruct (bv_eqb r 0) eqn:E; [reflexivity|]. symmetry. apply H. exact H0.
Qed.

Lemma sb2_word_out : forall lo hi a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ (lo <= bv_unsigned (Z_to_bv 64 a) < hi).
Proof. intros lo hi a Ha H. rewrite MState.unsigned_lit by lia. exact H. Qed.

Lemma sb2_bytes_at_keep : forall segs (m m' : word -> option byte) lo hi a bs,
  bytes_at segs m a bs -> (forall x : word, ~ (lo <= bv_unsigned x < hi) -> m' x = m x) ->
  hi <= a \/ a + Z.of_nat (length bs) <= lo -> bytes_at segs m' a bs.
Proof.
  intros segs m m' lo hi a bs (H1 & H2 & H3) HE Hd. split; [exact H1|]. split; [exact H2|].
  intros i Hi. rewrite <- (H3 i Hi). unfold mrd. rewrite HE; [reflexivity|].
  unfold wa. apply sb2_word_out; lia.
Qed.

Lemma sb2_bytes_at_rd1 : forall segs m a bs k, bytes_at segs m a bs -> (k < length bs)%nat ->
  ov_read_bytes segs m (wa (a + Z.of_nat k)) 1 = Some [nth k bs (zb 0)].
Proof.
  intros segs m a bs k H Hk. rewrite (bytes_at_read segs m a bs (Z.of_nat k) 1 H) by lia.
  rewrite Nat2Z.id. f_equal. clear H.
  revert k Hk. induction bs as [|b bs IH]; intros [|k] Hk; cbn [length] in Hk.
  - exfalso. apply (Nat.nlt_0_r 0). exact Hk.
  - exfalso. apply (Nat.nlt_0_r (S k)). exact Hk.
  - reflexivity.
  - cbn [skipn nth]. apply IH. apply (proj2 (Nat.succ_lt_mono k (length bs))). exact Hk.
Qed.

Lemma sb2_le2 : forall b0 b1 : byte, le2 (Z_to_bv 64 (bz b0 + 256 * bz b1)) = [b0; b1].
Proof.
  intros b0 b1. pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
  change (bv_modulus 8) with 256 in R0, R1. unfold bz.
  unfold le2. rewrite MState.unsigned_lit by lia. cbn [Z_to_le_bytes].
  f_equal; [|f_equal]; apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256;
    rewrite ?Z.shiftr_div_pow2 by lia; change (2 ^ 8) with 256;
    Z.div_mod_to_equations; lia.
Qed.

Lemma sb2_bytes_at_rd1' : forall segs m a bs k e, bytes_at segs m a bs -> (k < length bs)%nat ->
  a + Z.of_nat k = e -> ov_read_bytes segs m (wa e) 1 = Some [nth k bs (zb 0)].
Proof. intros segs m a bs k e H Hk <-. apply sb2_bytes_at_rd1; assumption. Qed.

Definition sb2_agree (regs R : bvmap 5 word) (l : list Z) : Prop :=
  forall k, In k l -> getr R (Z_to_bv 5 k) = getr regs (Z_to_bv 5 k).

Lemma sb2_agree_eqv : forall regs R R' l, sb2_agree regs R l -> Regs6ss.xregs_eqv R R' ->
  (forall k, In k l -> 1 <= k < 32) -> sb2_agree regs R' l.
Proof.
  intros regs R R' l H X Hk k Hin. rewrite <- (H k Hin). apply sb2_getr_x; [exact X|].
  pose proof (Hk k Hin) as Hr. unfold is_x0, bv_eqb. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. apply Z.eqb_neq. vm_compute. lia.
Qed.

Lemma sb2_agree_get : forall regs R l k, sb2_agree regs R l -> In k l -> getr R (Z_to_bv 5 k) = getr regs (Z_to_bv 5 k).
Proof. intros regs R l k H Hk. exact (H k Hk). Qed.

Lemma sb2_agree_sub : forall regs R l l', sb2_agree regs R l -> (forall k, In k l' -> In k l) -> sb2_agree regs R l'.
Proof. intros regs R l l' H S k Hk. exact (H k (S k Hk)). Qed.

Ltac sb2_ag H k := etransitivity; [apply (H k); cbn [In]; tauto|].

Lemma sb2_REC : forall g i regs R m, REC g i regs m -> sb2_agree regs R [9] -> REC g i R m.
Proof.
  intros g i regs R m (H1 & H2 & H3 & H4 & H5 & H6) A. split; [exact H1|]. split; [sb2_ag A 9; exact H2|].
  split; [exact H3|]. split; [exact H4|]. split; [exact H5 | exact H6].
Qed.

Lemma sb2_RB12 : forall g i pl regs R m, RB12 g i pl regs m -> sb2_agree regs R [9; 20; 21; 26] -> RB12 g i pl R m.
Proof.
  intros g i pl regs R m (H1 & H2 & H3 & H4 & H5) A.
  split; [apply (sb2_REC g i regs); [exact H1 | apply (sb2_agree_sub regs R _ _ A); cbn [In]; tauto]|].
  split; [sb2_ag A 20; exact H2|]. split; [sb2_ag A 26; exact H3|]. split; [sb2_ag A 21; exact H4|]. exact H5.
Qed.

Lemma sb2_S6A : forall g i regs R, S6A g i regs -> sb2_agree regs R [22] -> S6A g i R.
Proof. intros g i regs R H A. unfold S6A in *. sb2_ag A 22. exact H. Qed.

Lemma sb2_RRr : forall g i regs R, RRr g i regs -> sb2_agree regs R [24] -> RRr g i R.
Proof. intros g i regs R H A. unfold RRr in *. sb2_ag A 24. exact H. Qed.

Lemma sb2_FNM : forall g i regs R, FNM g i regs -> sb2_agree regs R [18; 19; 23; 25; 27] -> FNM g i R.
Proof.
  intros g i regs R (H1 & H2 & H3 & H4 & H5) A. unfold F7, F2, F9, F3, F11 in *.
  split; [sb2_ag A 23; exact H1|]. split; [sb2_ag A 18; exact H2|]. split; [sb2_ag A 25; exact H3|].
  split; [sb2_ag A 19; exact H4|]. sb2_ag A 27. exact H5.
Qed.

Lemma sb2_FALL : forall g i regs R, FALL g i regs -> sb2_agree regs R [8; 18; 19; 23; 25; 27] -> FALL g i R.
Proof.
  intros g i regs R (H1 & H2) A. unfold F0 in *.
  split; [apply (sb2_FNM g i regs); [exact H1 | apply (sb2_agree_sub regs R _ _ A); cbn [In]; tauto]|].
  sb2_ag A 8. exact H2.
Qed.

Lemma sb2_B03 : forall g i pl regs R m, B03 g i pl regs m -> sb2_agree regs R [9; 20; 21; 22; 26] ->
  B03 g i pl R m.
Proof.
  intros g i pl regs R m ((HR & H1 & H2 & H3) & H4 & H5) A.
  split; [split; [apply (sb2_REC g i regs); [exact HR | apply (sb2_agree_sub regs R _ _ A); cbn [In]; tauto]|]|].
  - split; [sb2_ag A 22; exact H1|]. split; [sb2_ag A 20; exact H2|]. sb2_ag A 26. exact H3.
  - split; [sb2_ag A 21; exact H4|]. exact H5.
Qed.

Lemma sb2_memcmp_refl : forall (l : list byte) n, (n <= length l)%nat -> StrFun.memcmp_model l l n = Some 0.
Proof.
  intros l n. revert l. induction n as [|n IH]; intros [|b l] H; cbn [length] in H; try lia; [reflexivity|reflexivity|].
  cbn [StrFun.memcmp_model]. rewrite Z.eqb_refl. apply IH. lia.
Qed.

Lemma sb2_bytes_at_sub : forall segs m a bs k n, bytes_at segs m a bs -> (k + n <= length bs)%nat ->
  bytes_at segs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros segs m a bs k n (H1 & H2 & H3) Hk.
  assert (LN : length (firstn n (skipn k bs)) = n) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite LN; lia|]. intros i Hi. rewrite LN in Hi.
  assert (NF : forall (l : list byte) n0 j, (j < n0)%nat -> nth_error (firstn n0 l) j = nth_error l j).
  { induction l as [|b l IH]; intros [|n0] [|j] Hj; cbn [firstn nth_error]; try reflexivity; try lia.
    apply IH. lia. }
  rewrite NF by lia. rewrite nth_error_skipn.
  replace (a + Z.of_nat k + Z.of_nat i) with (a + Z.of_nat (k + i)) by lia. apply H3. lia.
Qed.

Lemma sb2_bytes_at_rd2 : forall segs m a bs k e, bytes_at segs m a bs -> (S k < length bs)%nat -> a + Z.of_nat k = e ->
  ov_read_bytes segs m (wa e) 2 =
  Some (le2 (Z_to_bv 64 (bz (nth k bs (zb 0)) + 256 * bz (nth (S k) bs (zb 0))))).
Proof.
  intros segs m a bs k e H Hk <-. rewrite sb2_le2. rewrite (bytes_at_read segs m a bs (Z.of_nat k) 2 H) by lia.
  rewrite Nat2Z.id. f_equal. clear H. revert k Hk. induction bs as [|b bs IH]; intros k Hk; cbn [length] in Hk.
  - exfalso. lia.
  - destruct k as [|k].
    + destruct bs as [|b' bs]; cbn [length] in Hk; [exfalso; lia | reflexivity].
    + cbn [skipn nth]. apply IH. lia.
Qed.

Lemma sb2_zx16 : forall v, 0 <= v < 65536 -> zx16 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof. intros v Hv. unfold zx16. rewrite MState.unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma sb2_wmono_eq : forall segs (m m' : word -> option byte), (forall x, m' x = m x) -> wmono segs m m'.
Proof. intros segs m m' H x W. unfold wview in *. rewrite H. exact W. Qed.

Lemma sb2_le16_range : forall b0 b1 : byte, 0 <= bz b0 + 256 * bz b1 < 65536.
Proof.
  intros b0 b1. unfold bz. pose proof (bv_unsigned_in_range 8 b0). pose proof (bv_unsigned_in_range 8 b1).
  change (bv_modulus 8) with 256 in *. lia.
Qed.

Lemma sb2_rec_hwb_len : forall inp j, length (rec_hwb inp j) = 8%nat.
Proof.
  intros inp j. unfold rec_hwb. induction j as [|j IH]; cbn [rec_hw]; [reflexivity|].
  destruct ((rec_addr inp j =? ADDR_REAC_VERSION) && (8 <=? rec_k inp j)) eqn:E; [|exact IH].
  apply andb_true_iff in E as [_ E]. apply Z.leb_le in E. rewrite length_firstn, rec_pl_length. lia.
Qed.

Definition sb2_keep (m m' : word -> option byte) (lo hi : Z) : Prop :=
  forall x : word, ~ (lo <= bv_unsigned x < hi) -> m' x = m x.

Definition sb2_win (g : ghost) (lo hi : Z) : Prop :=
  (spk g 184 <= lo /\ hi <= spk g 242) \/ hi <= spk g 24.

Lemma sb2_keep_all : forall m m' lo hi, (forall x, m' x = m x) -> sb2_keep m m' lo hi.
Proof. intros m m' lo hi H x _. apply H. Qed.

Lemma sb2_REC_mem : forall g i regs m m' lo hi, REC g i regs m -> sb2_keep m m' lo hi -> sb2_win g lo hi ->
  REC g i regs m'.
Proof.
  intros g i regs m m' lo hi (H1 & H2 & H3 & H4 & (H5 & H6 & H7) & H8) K W.
  unfold sb2_win, spk in W. unfold NRb, G24, HWb, EVb, q64, u32 in *.
  split; [exact H1|]. split; [exact H2|].
  split; [apply (sb2_bytes_at_keep rsegs m m' lo hi _ _ H3 K); unfold spk; rewrite length_le8; lia|].
  split; [apply (sb2_bytes_at_keep rsegs m m' lo hi _ _ H4 K); unfold spk; rewrite length_le8; lia|].
  split; [split; [|split]|].
  - apply (sb2_bytes_at_keep rsegs m m' lo hi _ _ H5 K); unfold spk; rewrite length_le8; lia.
  - apply (sb2_bytes_at_keep rsegs m m' lo hi _ _ H6 K); unfold spk; rewrite length_le4; lia.
  - apply (sb2_bytes_at_keep rsegs m m' lo hi _ _ H7 K). unfold spk. rewrite sb2_rec_hwb_len. lia.
  - apply (sb2_bytes_at_keep rsegs m m' lo hi _ _ H8 K); unfold spk; rewrite length_le8; lia.
Qed.

Lemma sb2_PLB_mem : forall g i pl m m' lo hi, PLB g i pl m -> sb2_keep m m' lo hi ->
  pl + rec_k (g_in g) i <= lo -> PLB g i pl m'.
Proof.
  intros g i pl m m' lo hi H K Hl. apply (sb2_bytes_at_keep rsegs m m' lo hi _ _ H K).
  right. rewrite rec_pl_length, Z2Nat.id by apply rec_k_range. exact Hl.
Qed.

Lemma sb2_ID_mem : forall g j off m m' lo hi, bytes_at rsegs m (spk g off) (rec_id (g_in g) j) ->
  sb2_keep m m' lo hi -> sb2_win g lo hi -> (24 <= off /\ off + 38 <= 184) \/ 242 <= off ->
  bytes_at rsegs m' (spk g off) (rec_id (g_in g) j).
Proof.
  intros g j off m m' lo hi H K W Ho. apply (sb2_bytes_at_keep rsegs m m' lo hi _ _ H K).
  rewrite rec_id_length. unfold ID_SIZE, sb2_win, spk in *. lia.
Qed.

Lemma sb2_LPm_mem : forall g i m m' lo hi, LPm g i m -> sb2_keep m m' lo hi -> sb2_win g lo hi -> LPm g i m'.
Proof.
  intros g i m m' lo hi H K W. unfold LPm, q64 in *. apply (sb2_bytes_at_keep rsegs m m' lo hi _ _ H K).
  rewrite length_le8. unfold sb2_win, spk in *. lia.
Qed.

Lemma sb2_B03_mem : forall g i pl regs m m' lo hi, B03 g i pl regs m -> sb2_keep m m' lo hi -> sb2_win g lo hi ->
  pl + rec_k (g_in g) i <= lo -> B03 g i pl regs m'.
Proof.
  intros g i pl regs m m' lo hi ((HR & H1 & H2 & H3) & H4 & H5) K W Hl.
  split; [split; [apply (sb2_REC_mem g i regs m m' lo hi HR K W) | split; [exact H1 | split; [exact H2 | exact H3]]]|].
  split; [exact H4|]. exact (sb2_PLB_mem g i pl m m' lo hi H5 K Hl).
Qed.

Lemma sb2_RB12_mem : forall g i pl regs m m' lo hi, RB12 g i pl regs m -> sb2_keep m m' lo hi -> sb2_win g lo hi ->
  pl + rec_k (g_in g) i <= lo -> RB12 g i pl regs m'.
Proof.
  intros g i pl regs m m' lo hi (HR & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) K W Hl.
  split; [exact (sb2_REC_mem g i regs m m' lo hi HR K W)|].
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split; [exact (sb2_PLB_mem g i pl m m' lo hi H4 K Hl)|].
  split; [exact (sb2_ID_mem g (S i) 146 m m' lo hi H5 K W ltac:(lia))|].
  split; [exact (sb2_ID_mem g (S i) 242 m m' lo hi H6 K W ltac:(lia))|].
  split; [exact (sb2_ID_mem g i 64 m m' lo hi H7 K W ltac:(lia))|].
  exact (sb2_LPm_mem g i m m' lo hi H8 K W).
Qed.

Lemma sb2_stk_wr : forall segs m lo hi a n, stk segs m lo hi -> lo <= a -> a + n <= hi -> 0 <= n -> wr_at segs m a n.
Proof.
  intros segs m lo hi a n (H1 & H2 & H3) Ha Hn Hz. split; [lia|]. split; [lia|].
  intros i Hi. exact (proj1 (H3 (a + i) ltac:(lia))).
Qed.

Lemma sb2_stk_sub : forall segs m lo hi lo' hi', stk segs m lo hi -> lo <= lo' -> hi' <= hi -> lo' <= hi' ->
  stk segs m lo' hi'.
Proof.
  intros segs m lo hi lo' hi' (H1 & H2 & H3) Hl Hh Hlh. split; [lia|]. split; [lia|].
  intros a Ha. apply H3. lia.
Qed.

Lemma sb2_stk_norm : forall m lo hi, stk rsegs m lo hi -> 2 ^ 40 <= lo -> stk rsegs (normalize rsegs m) lo hi.
Proof.
  intros m lo hi (H1 & H2 & H3) Hl. split; [exact H1|]. split; [exact H2|].
  intros a Ha. destruct (H3 a Ha) as [W [b Hb]].
  assert (E : normalize rsegs m (wa a) = m (wa a)).
  { unfold normalize. rewrite sb2_ro_hi; [reflexivity|]. unfold wa. rewrite MState.unsigned_lit by lia. lia. }
  split; [unfold wview in *; rewrite E; exact W | exists b; unfold mrd in *; rewrite E; exact Hb].
Qed.

Section SB2.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.

Lemma sb2_seg : ms_segs B = rsegs.
Proof. exact (proj1 FF). Qed.

Lemma sb2_seg_run : forall (regs : bvmap 5 word) (pc : Z) (mem : word -> option byte) md (P : config -> Prop)
    (Q : bvmap 5 word -> Z -> (word -> option byte) -> Prop),
  m_halted md = None -> m_vm_lazy md = [] ->
  Exec.evt rsegs (fun s => exists R pc' m', s = MS R fp_regs (Z_to_bv 64 pc') fp_csr None m' (seg_rom rsegs) /\
                                            Q R pc' m')
    (MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 pc) fp_csr None mem (seg_rom rsegs)) ->
  (forall R R' pc' m', Q R pc' m' -> Regs6ss.xregs_eqv R R' ->
     Rz (ms_segs B) (mkCfg (mkst R' (Z_to_bv 64 pc') m' (seg_rom (ms_segs B))) md) P) ->
  Rz (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros regs pc mem md P Q Hh Hl HE K. pose proof sb2_seg as SEG. rewrite SEG in K |- *.
  eapply rz_evt_canon; [exact HE | exact Hh | exact Hl |].
  intros ms' (can & (R & pc' & m' & -> & HQ) & EQ).
  destruct (sb2_eqv_mkst R (Z_to_bv 64 pc') m' (seg_rom rsegs) ms' EQ) as (R' & -> & XR).
  exact (K R R' pc' m' HQ XR).
Qed.

Lemma sb2_seg_run_norm : forall (regs : bvmap 5 word) (pc : Z) (mem : word -> option byte) md (P : config -> Prop)
    (Q : bvmap 5 word -> Z -> (word -> option byte) -> Prop),
  ro_agree rsegs mem -> m_halted md = None -> m_vm_lazy md = [] ->
  Exec.evt rsegs (fun s => exists R pc' m', s = MS R fp_regs (Z_to_bv 64 pc') fp_csr None m' (seg_rom rsegs) /\
                                            Q R pc' m')
    (MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 pc) fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall R R' pc' m0 m', Q R pc' m0 -> Regs6ss.xregs_eqv R R' -> mem_rel rsegs m' m0 -> ro_same rsegs mem m' ->
     Rz (ms_segs B) (mkCfg (mkst R' (Z_to_bv 64 pc') m' (seg_rom (ms_segs B))) md) P) ->
  Rz (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros regs pc mem md P Q HRO Hh Hl HE K. pose proof sb2_seg as SEG. rewrite SEG in K |- *.
  pose proof (evt_normalize rsegs _ _ _ _ _ _ _ _ wx_apart_rsegs HRO HE) as HN.
  eapply rz_evt_canon; [exact HN | exact Hh | exact Hl |].
  intros ms' (can & (s0 & (R & pc' & m0 & -> & HQ) & REL & ROS) & EQ).
  destruct can as [Rc Fc pcc svcc rvc fcc mc roc].
  destruct REL as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & MREL).
  cbn in E1, E2, E3, E4, E5, E6, E7, MREL, ROS. subst.
  destruct (sb2_eqv_mkst R (Z_to_bv 64 pc') mc (seg_rom rsegs) ms' EQ) as (R' & -> & XR).
  exact (K R R' pc' m0 mc HQ XR MREL ROS).
Qed.

Lemma sb2_FR_frame : forall g km hb L A regs mem md regs' mem' lo hi,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  g_S g - SLOT_K <= lo -> hi <= g_S g - 104 ->
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> mem' x = mem x) ->
  wmono rsegs mem mem' ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  FR B APIf ra empty g km hb L A regs' mem' md.
Proof.
  intros g km hb L A regs mem md regs' mem' lo hi HFR HP Hlo Hhi HEQ HWM E2 E3 E4.
  pose proof sb2_seg as SEG.
  pose proof FF as (_ & _ & _ & _ & _ & _ & HCE & _ & _ & _ & _ & _ & _ & _ & _ & _ & HTP & HEO & _ & HOH & HOL & HTH & _).
  pose proof alloc_ceiling_value as HAC.
  unfold FR in HFR |- *. cbv zeta in HFR |- *.
  destruct HFR as (HGV & H2 & H3 & H4 & HSV & HSTK & HMI & HREL & HMR & HWF & HBD & HIN & HMD & HCEIL & HIMG & HB0 &
    HERR & HSNK & HRES & HSW).
  pose proof HGV as (Hn & Hpay & Hblk & HSm & HSk & HS47 & Hroom & HgS & Hgtp & HPB).
  unfold SLOT_K, SLOT_STACK in *.
  assert (LO : 2 ^ 40 < lo) by lia.
  assert (EQZ : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a))
    by (intros a Ha Ho; apply HEQ; apply sb2_word_out; assumption).
  assert (MB : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a)
    by (intros a Ha Ho; unfold mbyte; rewrite (EQZ a Ha Ho); reflexivity).
  assert (WB : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
                 (writable_at (ms_segs B) mem' a <-> writable_at (ms_segs B) mem a))
    by (intros a Ha Ho; unfold writable_at, wview; rewrite (EQZ a Ha Ho); tauto).
  assert (WBw : forall a, writable_at (ms_segs B) mem a -> writable_at (ms_segs B) mem' a)
    by (intros a W; rewrite SEG in *; unfold writable_at in *; apply HWM; exact W).
  split; [exact HGV|]. split; [rewrite E2; exact H2|]. split; [rewrite E3; exact H3|]. split; [rewrite E4; exact H4|].
  split; [apply (sb2_bytes_at_keep rsegs mem mem' lo hi _ _ HSV HEQ); left; lia|].
  split.
  { destruct HSTK as (S1 & S2 & S3). split; [exact S1|]. split; [exact S2|]. intros a Ha.
    destruct (S3 a Ha) as [W [b Hb]]. unfold wa in *.
    destruct (Z_lt_le_dec a lo) as [h1|h1]; [|destruct (Z_lt_le_dec a hi) as [h2|h2]].
    - split; [unfold wview in *; rewrite EQZ by lia; exact W | exists b; unfold mrd in *; rewrite EQZ by lia; exact Hb].
    - pose proof (HWM (Z_to_bv 64 a) W) as W'. split; [exact W'|].
      apply sb2_wview_mrd; [rewrite MState.unsigned_lit by lia; lia | exact W'].
    - split; [unfold wview in *; rewrite EQZ by lia; exact W | exists b; unfold mrd in *; rewrite EQZ by lia; exact Hb]. }
  split.
  { unfold MI in *. rewrite SEG in HMI |- *. intros x Hx. pose proof (sb2_ro_lt x Hx) as Hxl.
    rewrite <- (HMI x Hx). unfold mrd. rewrite HEQ; [reflexivity | lia]. }
  split.
  { unfold relro, G_img_c in *. intros a Ha. rewrite <- (HREL a Ha).
    unfold in_globals, frame_RELRO in Ha. destruct Ha as (l0 & n0 & Hin & Hr). cbn [In] in Hin.
    destruct Hin as [E|[E|[]]]; injection E as <- <-; apply MB; lia. }
  split.
  { pose proof (mr_model B _ (aa_laws (APIf rc)) L A mem md HMR) as (Hh & Hlz & Hmat).
    apply (mr_frame B _ (aa_laws (APIf rc)) L A mem mem' md md HMR).
    - intros a Ho. pose proof (mr_owned_low B _ (aa_laws (APIf rc)) L A mem md a HMR Ho). apply MB; lia.
    - intros a Ho [b Hb]. exists b. pose proof (mr_owned_low B _ (aa_laws (APIf rc)) L A mem md a HMR Ho).
      rewrite EQZ by lia. exact Hb.
    - intros p n i Hu Hi. pose proof (mr_blocks B _ (aa_laws (APIf rc)) L A mem md p n i HMR Hu Hi) as ([b Hb] & R1 & R2 & _).
      exists b. rewrite EQZ by lia. exact Hb.
    - reflexivity.
    - exact Hh.
    - exact Hlz.
    - exact Hmat. }
  split; [exact HWF|]. split; [exact HBD|]. split; [exact HIN|]. split; [exact HMD|].
  split.
  { intros a Ha Hs He. destruct (HCEIL a Ha Hs He) as [M W]. split; [rewrite MB by lia; exact M|].
    rewrite WB by lia. exact W. }
  split.
  { intros a Ha Hs Hc He. pose proof (sb2_img_lt B SEG a Ha). destruct (HIMG a Ha Hs Hc He) as [M W].
    split; [rewrite MB by lia; exact M | rewrite WB by lia; exact W]. }
  split.
  { intros a k i Hin Hi. rewrite <- (HB0 a k i Hin Hi).
    assert (Hin' : In (a, k) (blocks L A))
      by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact Hin).
    unfold blocks in Hin'. apply in_map_iff in Hin'. destruct Hin' as ([p k'] & Ep & Hu). cbn [fst snd] in Ep.
    injection Ep as Ea Ek. subst a k'.
    pose proof (mr_blocks_range B _ (aa_laws (APIf rc)) L A mem md p k HMR Hu) as [R1 R2]. apply MB; lia. }
  split.
  { intros a Ha. unfold errno_addr in Ha. rewrite HTP, HEO in Ha. rewrite WB by lia. apply HERR.
    unfold errno_addr. rewrite HTP, HEO. exact Ha. }
  split.
  { unfold sink_none, closed_stdio_env, val_mem, word_mem in *. rewrite HOH, HOL, HTH in *.
    destruct HSNK as ((T1 & T2) & T3 & T4).
    split; [split|split; [|exact T4]].
    - intros k Hk. rewrite MB by lia. apply T1. exact Hk.
    - intros k Hk. rewrite MB by lia. apply T2. exact Hk.
    - intros k Hk. rewrite MB by lia. apply T3. exact Hk. }
  split; [exact HRES|].
  intros a Ha. destruct (Z_lt_le_dec a lo) as [h1|h1]; [|destruct (Z_lt_le_dec a hi) as [h2|h2]].
  - rewrite WB by lia. apply HSW. exact Ha.
  - apply WBw. apply HSW. exact Ha.
  - rewrite WB by lia. apply HSW. exact Ha.
Qed.

Lemma sb2_FR_regs : forall g km hb L A regs mem md R',
  FR B APIf ra empty g km hb L A regs mem md -> Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  sb2_agree regs R' [2; 3; 4] -> FR B APIf ra empty g km hb L A R' mem md.
Proof.
  intros g km hb L A regs mem md R' HFR HP AG.
  apply (sb2_FR_frame g km hb L A regs mem md R' mem (g_S g - 104) (g_S g - 104) HFR HP).
  - unfold SLOT_K, SLOT_STACK. lia.
  - lia.
  - intros x _. reflexivity.
  - apply wmono_refl.
  - apply (AG 2). cbn [In]. tauto.
  - apply (AG 3). cbn [In]. tauto.
  - apply (AG 4). cbn [In]. tauto.
Qed.

Lemma sb2_FR_mem : forall g km hb L A regs mem md R' mem' lo hi,
  FR B APIf ra empty g km hb L A regs mem md -> Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  g_S g - SLOT_K <= lo -> hi <= g_S g - 104 -> sb2_keep mem mem' lo hi -> wmono rsegs mem mem' ->
  sb2_agree regs R' [2; 3; 4] -> FR B APIf ra empty g km hb L A R' mem' md.
Proof.
  intros g km hb L A regs mem md R' mem' lo hi HFR HP Hlo Hhi K WM AG.
  apply (sb2_FR_frame g km hb L A regs mem md R' mem' lo hi HFR HP Hlo Hhi K WM).
  - apply (AG 2). cbn [In]. tauto.
  - apply (AG 3). cbn [In]. tauto.
  - apply (AG 4). cbn [In]. tauto.
Qed.

Lemma sb2_FR_basics : forall g km hb L A regs mem md,
  FR B APIf ra empty g km hb L A regs mem md ->
  2 ^ 40 < alloc_ceiling /\ alloc_ceiling + 65536 <= g_S g /\ g_S g <= 2 ^ 47 /\ g_S g mod 16 = 0 /\
  fsp g = g_S g - 384 /\ reg_get regs 2 = Z_to_bv 64 (fsp g) /\
  stk rsegs mem (g_S g - 65536) (g_S g) /\ ro_agree rsegs mem /\ m_halted md = None /\ m_vm_lazy md = [] /\
  aa_MR (APIf rc) L A mem md.
Proof.
  intros g km hb L A regs mem md HFR. pose proof sb2_seg as SEG. pose proof alloc_ceiling_value as HAC.
  unfold FR in HFR. cbv zeta in HFR.
  destruct HFR as (HGV & H2 & H3 & H4 & HSV & HSTK & HMI & HREL & HMR & _).
  pose proof HGV as (Hn & Hpay & Hblk & HSm & HSk & HS47 & _).
  pose proof (mr_model B _ (aa_laws (APIf rc)) L A mem md HMR) as (Hh & Hlz & _).
  unfold SLOT_K, SLOT_STACK in *. unfold MI in HMI. rewrite SEG in HMI.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [reflexivity|].
  split; [exact H2|]. split; [exact HSTK|]. split; [exact HMI|]. split; [exact Hh|]. split; [exact Hlz|]. exact HMR.
Qed.

Lemma sb2_blk_low : forall L A mem md a k, aa_MR (APIf rc) L A mem md -> In (a, k) (blocks L A) -> a + k <= alloc_ceiling.
Proof.
  intros L A mem md a k HMR Hin. unfold blocks in Hin. apply in_map_iff in Hin.
  destruct Hin as ([p k'] & Ep & Hu). cbn [fst snd] in Ep. injection Ep as Ea Ek. subst a k'.
  pose proof (mr_blocks_range B _ (aa_laws (APIf rc)) L A mem md p k HMR Hu) as [R1 R2]. exact R2.
Qed.

Lemma sb2_pl_low : forall g i pl L A mem md X, aa_MR (APIf rc) L A mem md ->
  Permutation (blocks L A) (hb_pl g i pl ++ X) -> pl + rec_k (g_in g) i <= alloc_ceiling.
Proof.
  intros g i pl L A mem md X HMR HP. apply (sb2_blk_low L A mem md); [exact HMR|].
  apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. unfold hb_pl. left. reflexivity.
Qed.

End SB2.
