From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcFin.
Import ListNotations.
Open Scope Z_scope.

Lemma rcf_eqb : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma rcf_ltu : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma rcf_chk : forall x, 0 < x < 2^64 ->
  bv_eqb (Z_to_bv 64 (Z.lxor 1 (bv_unsigned (v_sltiu (Z_to_bv 64 x) 1)))) (Z_to_bv 64 0) = false.
Proof.
  intros x Hx. rewrite v_sltiu_b2z. rewrite (unsigned_lit x) by lia.
  change (bv_wrap 64 1) with 1. replace (x <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
  reflexivity.
Qed.

Lemma rcf_negk : forall k, - 2^64 < k < 0 -> bv_unsigned (Z_to_bv 64 k) = 2^64 + k.
Proof.
  intros k Hk. rewrite unsigned_lit_wrap.
  rewrite <- (Z.mod_add k 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma rcf_ltu_neg : forall x k, 0 <= x < 2^64 -> - 2^64 < k < 0 ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 k) = (x <? 2^64 + k).
Proof. intros x k Hx Hk. unfold bv_ltu. rewrite (rcf_negk k) by lia. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma rcf_neg_byte : forall s, 0 <= s < 2^31 ->
  le1 (Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (Z_to_bv 64 s)))) = [Z_to_bv 8 ((- s) mod 256)].
Proof.
  intros s Hs. rewrite (unsigned_lit s) by lia.
  assert (HM : bv_half_modulus 32 = 2^31) by reflexivity.
  rewrite (bv_swrap_small 32 (0 - s)) by (rewrite HM; lia).
  unfold le1. cbn [Z_to_le_bytes]. f_equal. apply Z_to_bv8_mod.
  rewrite unsigned_lit_wrap. rewrite mod_mod8_of_modw by lia. change (2^8) with 256.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma rcf_u8 : forall x, bv_unsigned (Z_to_bv 8 x) = x mod 256.
Proof. intros x. rewrite Z_to_bv_unsigned. change (bv_wrap 8 x) with (x mod 2^8). reflexivity. Qed.

Lemma rcf_psum_S : forall bs k, psum bs (S k) = psum bs k + bv_unsigned (nth k bs (Z_to_bv 8 0)).
Proof. reflexivity. Qed.

Lemma rcf_nth_upd : forall bs k b i d, (k < length bs)%nat ->
  nth i (upd_bytes bs k [b]) d = if Nat.eqb i k then b else nth i bs d.
Proof.
  unfold upd_bytes. induction bs as [|x bs IH]; intros k b i d Hk; cbn [length] in Hk; [lia|].
  destruct k as [|k]; destruct i as [|i]; cbn; try reflexivity.
  apply IH. lia.
Qed.

Lemma rcf_upd_len : forall bs k b, (k < length bs)%nat -> length (upd_bytes bs k [b]) = length bs.
Proof. intros. apply upd_bytes_length. cbn [length]. lia. Qed.

Lemma rcf_upd_same : forall bs k d, (k < length bs)%nat -> upd_bytes bs k [nth k bs d] = bs.
Proof.
  unfold upd_bytes. induction bs as [|x bs IH]; intros k d Hk; cbn [length] in Hk; [lia|].
  destruct k as [|k]; cbn; [reflexivity|]. f_equal. apply IH. lia.
Qed.

Lemma rcf_psum_ext : forall bs bs' j,
  (forall i, (i < j)%nat -> nth i bs (Z_to_bv 8 0) = nth i bs' (Z_to_bv 8 0)) -> psum bs j = psum bs' j.
Proof.
  intros bs bs' j. induction j as [|j IH]; intros H; [reflexivity|].
  rewrite !rcf_psum_S. rewrite IH by (intros; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Lemma rcf_psum_upd : forall bs k b j, (k < length bs)%nat -> (j <= k)%nat ->
  psum (upd_bytes bs k [b]) j = psum bs j.
Proof.
  intros bs k b j Hk Hj. apply rcf_psum_ext. intros i Hi. rewrite rcf_nth_upd by lia.
  replace (Nat.eqb i k) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity.
Qed.

Lemma rcf_nth_skipn : forall (bs : list byte) (o i : nat) d, nth i (skipn o bs) d = nth (o + i)%nat bs d.
Proof.
  induction bs as [|x bs IH]; intros o i d; destruct o as [|o]; cbn; try reflexivity.
  destruct i; reflexivity. apply IH.
Qed.

Lemma rcf_byte_close : forall s b M, 0 < M -> 0 <= b < M -> (s + b) mod M = 0 -> b = (- s) mod M.
Proof.
  intros s b M HM Hb H. replace (- s) with (b - (s + b)) by lia.
  rewrite Zminus_mod. rewrite H. rewrite Z.sub_0_r. rewrite Z.mod_mod by lia.
  rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma rcf_self8 : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma rcf_stamp32_len : forall bs, length bs = 32%nat -> length (stamp32 bs) = 32%nat.
Proof. intros bs H. unfold stamp32. rewrite rcf_upd_len; lia. Qed.

Lemma rcf_stamp32_sum : forall bs, length bs = 32%nat -> blocksum (stamp32 bs) = 0.
Proof.
  intros bs Hl. unfold blocksum, stamp32. rewrite (rcf_psum_S (upd_bytes _ _ _) 31).
  rewrite rcf_psum_upd by lia. rewrite rcf_nth_upd by lia. rewrite Nat.eqb_refl. rewrite rcf_u8.
  rewrite !Zplus_mod_idemp_r. replace (psum bs 31 + - psum bs 31) with 0 by lia. reflexivity.
Qed.

Lemma rcf_upd_close : forall bs (k : nat) s M, (k < length bs)%nat -> 0 < M <= 256 ->
  bv_unsigned (nth k bs (Z_to_bv 8 0)) < M ->
  (s + bv_unsigned (nth k bs (Z_to_bv 8 0))) mod M = 0 -> upd_bytes bs k [Z_to_bv 8 ((- s) mod M)] = bs.
Proof.
  intros bs k s M Hk HM Hb H. pose proof (byte_range (nth k bs (Z_to_bv 8 0))) as BR.
  pose proof (rcf_byte_close s (bv_unsigned (nth k bs (Z_to_bv 8 0))) M ltac:(lia) ltac:(lia) H) as E.
  rewrite <- E. rewrite rcf_self8. apply rcf_upd_same. exact Hk.
Qed.

Lemma rcf_blocksum_S : forall bs, blocksum bs = (psum bs 31 + bv_unsigned (nth 31 bs (Z_to_bv 8 0))) mod 256.
Proof. intros bs. unfold blocksum. rewrite (rcf_psum_S bs 31). reflexivity. Qed.

Lemma rcf_stamp32_same : forall bs, length bs = 32%nat -> blocksum bs = 0 -> stamp32 bs = bs.
Proof.
  intros bs Hl H. rewrite rcf_blocksum_S in H. unfold stamp32.
  pose proof (byte_range (nth 31 bs (Z_to_bv 8 0))) as BR.
  apply rcf_upd_close; [lia | lia | lia | exact H].
Qed.

Lemma rcf_store1 : forall segs W m0 m A bs (k : nat) b,
  munch W m0 m -> wmono segs m0 m -> (mem_inv segs m0 -> mem_inv segs m) ->
  bytes_at segs m A bs -> wr_at segs m A (Z.of_nat (length bs)) -> (k < length bs)%nat ->
  inside W (A + Z.of_nat k) 1 ->
  munch W m0 (write_to_mem m (wa (A + Z.of_nat k)) [b]) /\
  wmono segs m0 (write_to_mem m (wa (A + Z.of_nat k)) [b]) /\
  (mem_inv segs m0 -> mem_inv segs (write_to_mem m (wa (A + Z.of_nat k)) [b])) /\
  bytes_at segs (write_to_mem m (wa (A + Z.of_nat k)) [b]) A (upd_bytes bs k [b]) /\
  wr_at segs (write_to_mem m (wa (A + Z.of_nat k)) [b]) A (Z.of_nat (length bs)).
Proof.
  intros segs W m0 m A bs k b MU WM MI HB HW Hk HI.
  pose proof (bytes_at_bound segs m A bs HB) as BD.
  assert (HS : store_ok segs m (wa (A + Z.of_nat k)) 1 = true)
    by (apply (wr_at_store_ok segs m A (Z.of_nat (length bs)) (Z.of_nat k) 1 HW); lia).
  split; [apply munch_write; [exact MU | lia | cbn [length]; lia | exact HI]|].
  split; [apply wmono_write; exact WM|].
  split; [intros H0; apply mem_inv_store; [exact (MI H0) | exact HS]|].
  split; [|apply wr_at_write; exact HW].
  pose proof (bytes_at_write_inside segs m A bs (Z.of_nat k) [b] HB ltac:(lia) ltac:(cbn [length]; lia)) as H.
  rewrite Nat2Z.id in H. exact H.
Qed.

Lemma rcf_bytes_skipn : forall segs m A bs (k : nat), (k <= length bs)%nat ->
  bytes_at segs m A bs -> bytes_at segs m (A + Z.of_nat k) (skipn k bs).
Proof.
  intros segs m A bs k Hk HB. rewrite <- (firstn_skipn k bs) in HB.
  apply bytes_at_app in HB. destruct HB as [_ HB]. rewrite length_firstn in HB.
  replace (Nat.min k (length bs)) with k in HB by lia. exact HB.
Qed.

Lemma rcf_u8_small : forall x M, 0 < M <= 256 -> bv_unsigned (Z_to_bv 8 (x mod M)) = x mod M.
Proof.
  intros x M HM. rewrite rcf_u8. apply Z.mod_small. pose proof (Z.mod_pos_bound x M ltac:(lia)). lia.
Qed.

Lemma rcf_fin1 : forall o n bs, fin 1 o n bs = stamp32 bs.
Proof. reflexivity. Qed.

Lemma rcf_fin2 : forall o n bs, fin 2 o n bs = stamp32 (rstamp bs o n).
Proof. reflexivity. Qed.

Lemma rcf_fin0 : forall o n bs, fin 0 o n bs = bs.
Proof. reflexivity. Qed.

Lemma rcf_rstamp_len : forall bs o n, 0 <= o -> 1 <= n -> o + n <= 32 -> length bs = 32%nat ->
  length (rstamp bs o n) = 32%nat.
Proof. intros bs o n Ho Hn Hon Hl. unfold rstamp. rewrite rcf_upd_len; lia. Qed.

Lemma rcf_rsum_S : forall bs o n, 0 <= o -> 1 <= n -> o + n <= 32 -> length bs = 32%nat ->
  rsum bs o n = rsum bs o (n - 1) + ubat bs (Z.to_nat (o + n - 1)).
Proof.
  intros bs o n Ho Hn Hon Hl. unfold rsum, ubat.
  replace (Z.to_nat n) with (S (Z.to_nat (n - 1))) by lia. rewrite rcf_psum_S.
  rewrite rcf_nth_skipn. replace (Z.to_nat (o + n - 1)) with (Z.to_nat o + Z.to_nat (n - 1))%nat by lia.
  reflexivity.
Qed.

Lemma rcf_rsum_upd : forall bs o n k b, 0 <= o -> 0 <= n -> (k < length bs)%nat ->
  (Z.to_nat (o + n) <= k \/ k < Z.to_nat o)%nat -> rsum (upd_bytes bs k [b]) o n = rsum bs o n.
Proof.
  intros bs o n k b Ho Hn Hk Hd. unfold rsum. apply rcf_psum_ext. intros i Hi.
  rewrite !rcf_nth_skipn. rewrite rcf_nth_upd by lia.
  replace (Nat.eqb (Z.to_nat o + i) k) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity.
Qed.

Lemma rcf_ubat_upd : forall bs k b j, (k < length bs)%nat -> j <> k -> ubat (upd_bytes bs k [b]) j = ubat bs j.
Proof.
  intros bs k b j Hk Hj. unfold ubat. rewrite rcf_nth_upd by lia.
  replace (Nat.eqb j k) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity.
Qed.

Lemma rcf_ubat_upd_eq : forall bs k b, (k < length bs)%nat -> ubat (upd_bytes bs k [b]) k = bv_unsigned b.
Proof. intros bs k b Hk. unfold ubat. rewrite rcf_nth_upd by lia. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma rcf_rstamp_closes : forall bs o n, 0 <= o -> 2 <= n -> o + n <= 31 -> length bs = 32%nat ->
  rsum (rstamp bs o n) o n mod 128 = 0 /\ ubat (rstamp bs o n) (Z.to_nat (o + n - 1)) < 128.
Proof.
  intros bs o n Ho Hn Hon Hl.
  assert (Hk : (Z.to_nat (o + n - 1) < length bs)%nat) by lia.
  rewrite rcf_rsum_S by (try rewrite rcf_rstamp_len; lia). unfold rstamp.
  rewrite rcf_ubat_upd_eq by exact Hk. rewrite rcf_u8_small by lia.
  rewrite rcf_rsum_upd by lia.
  split; [|pose proof (Z.mod_pos_bound (- rsum bs o (n - 1)) 128 ltac:(lia)); lia].
  rewrite Zplus_mod_idemp_r. replace (rsum bs o (n - 1) + - rsum bs o (n - 1)) with 0 by lia. reflexivity.
Qed.

Lemma rcf_rstamp_same : forall bs o n, 0 <= o -> 2 <= n -> o + n <= 31 -> length bs = 32%nat ->
  rsum bs o n mod 128 = 0 -> ubat bs (Z.to_nat (o + n - 1)) < 128 -> rstamp bs o n = bs.
Proof.
  intros bs o n Ho Hn Hon Hl H1 H2. rewrite rcf_rsum_S in H1 by lia. unfold ubat in *.
  unfold rstamp. apply rcf_upd_close; [lia | lia | exact H2 | exact H1].
Qed.

Lemma rcf_closes_fin : forall c o n bs, length bs = 32%nat -> (c = 1 \/ c = 2) ->
  (c = 2 -> 0 <= o /\ 2 <= n /\ o + n <= 31) -> closes c o n (fin c o n bs).
Proof.
  intros c o n bs Hl Hc Hr. destruct Hc as [-> | ->].
  - rewrite rcf_fin1. split; [apply rcf_stamp32_sum; exact Hl | intros H; exfalso; lia].
  - destruct (Hr eq_refl) as (Ho & Hn & Hon). rewrite rcf_fin2.
    pose proof (rcf_rstamp_len bs o n Ho ltac:(lia) ltac:(lia) Hl) as HL.
    pose proof (rcf_rstamp_closes bs o n Ho Hn Hon Hl) as [R1 R2].
    split; [apply rcf_stamp32_sum; exact HL|]. intros _. unfold stamp32.
    rewrite rcf_rsum_upd by lia. rewrite rcf_ubat_upd by lia. split; assumption.
Qed.

Lemma rcf_fin_same : forall c o n bs, length bs = 32%nat -> (c = 1 \/ c = 2) ->
  (c = 2 -> 0 <= o /\ 2 <= n /\ o + n <= 31) -> closes c o n bs -> fin c o n bs = bs.
Proof.
  intros c o n bs Hl Hc Hr [HS HR]. destruct Hc as [-> | ->].
  - rewrite rcf_fin1. apply rcf_stamp32_same; assumption.
  - destruct (Hr eq_refl) as (Ho & Hn & Hon). destruct (HR eq_refl) as [R1 R2]. rewrite rcf_fin2.
    rewrite rcf_rstamp_same by assumption. apply rcf_stamp32_same; assumption.
Qed.

Lemma rcf_bytes_munch1 : forall segs m m1 A bs (k : nat) b,
  bytes_at segs m A bs -> (k < length bs)%nat ->
  munch [(A + Z.of_nat k, A + Z.of_nat k + 1)] m m1 -> bytes_at segs m1 (A + Z.of_nat k) [b] ->
  bytes_at segs m1 A (upd_bytes bs k [b]).
Proof.
  intros segs m m1 A bs k b HB Hk MU H1.
  pose proof HB as (HA & HL & HR). pose proof H1 as (_ & _ & HR1).
  split; [lia|]. split; [rewrite rcf_upd_len by lia; lia|].
  intros i Hi. rewrite rcf_upd_len in Hi by lia.
  rewrite upd_bytes_nth by (cbn [length]; lia). cbn [length].
  destruct (Nat.eq_dec i k) as [->|Hne].
  - rewrite Nat.leb_refl. replace (Nat.ltb k (k + 1)) with true by (symmetry; apply Nat.ltb_lt; lia).
    cbn [andb]. rewrite Nat.sub_diag. specialize (HR1 0%nat ltac:(cbn; lia)).
    change (Z.of_nat 0) with 0 in HR1. rewrite Z.add_0_r in HR1. exact HR1.
  - replace (Nat.leb k i && Nat.ltb i (k + 1))%bool with false
      by (destruct (Nat.leb_spec k i); destruct (Nat.ltb_spec i (k + 1)); cbn; first [reflexivity | lia]).
    rewrite <- (HR i Hi). unfold mrd. rewrite (MU (wa (A + Z.of_nat i))); [reflexivity|].
    cbn [outside]. rewrite wa_unsigned by lia. split; [lia | exact I].
Qed.

Lemma rcf_rw32 : forall segs m A bs, length bs = 32%nat -> bytes_at segs m A bs -> wr_at segs m A 32 ->
  rw_cells segs m A [CB 32 bs].
Proof.
  intros segs m A bs Hl HB HW. unfold rw_cells, cells_at. split; [split|].
  - cbn [cells_wf cell_wf]. split; [exact Hl | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize]. exact HW.
Qed.

Lemma rcf_rw32_inv : forall segs m A bs, rw_cells segs m A [CB 32 bs] ->
  length bs = 32%nat /\ bytes_at segs m A bs /\ wr_at segs m A 32.
Proof.
  intros segs m A bs [[HWF HB] HW]. cbn [cells_bytes cbytes cells_size csize cells_wf cell_wf] in HB, HW, HWF.
  rewrite app_nil_r in HB. destruct HWF as [Hl _]. split; [exact Hl|]. split; [exact HB | exact HW].
Qed.

Lemma rcf_rec_byte : forall s, 0 <= s < 2^31 ->
  le1 (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (Z_to_bv 64 s))))) 127)) =
  [Z_to_bv 8 ((- s) mod 128)].
Proof.
  intros s Hs. rewrite (unsigned_lit s) by lia.
  assert (HM : bv_half_modulus 32 = 2^31) by reflexivity.
  rewrite (bv_swrap_small 32 (0 - s)) by (rewrite HM; lia).
  rewrite unsigned_lit_wrap. change 127 with (Z.ones 7). rewrite Z.land_ones by lia. change (2^7) with 128.
  rewrite Z.mod_mod_divide by (exists (2^57); reflexivity).
  pose proof (Z.mod_pos_bound (0 - s) 128 ltac:(lia)) as M.
  unfold le1. rewrite (unsigned_lit ((0 - s) mod 128)) by lia. reflexivity.
Qed.

Lemma rcf_stk_store_ok : forall segs m lo hi a (j : nat), stk segs m lo hi -> lo <= a -> a + Z.of_nat j <= hi ->
  store_ok segs m (wa a) j = true.
Proof.
  intros segs m lo hi a j (H1 & H2 & H) Ha Hj.
  replace a with (lo + (a - lo)) by lia.
  apply (wr_at_store_ok segs m lo (hi - lo) (a - lo) j); [|lia|lia].
  split; [lia|]. split; [lia|]. intros i Hi. apply (proj1 (H (lo + i) ltac:(lia))).
Qed.

Lemma rcf_bytes_sub : forall segs m A bs (k j : nat), (k + j <= length bs)%nat ->
  bytes_at segs m A bs -> bytes_at segs m (A + Z.of_nat k) (firstn j (skipn k bs)).
Proof.
  intros segs m A bs k j Hkj HB. pose proof (rcf_bytes_skipn segs m A bs k ltac:(lia) HB) as HS.
  rewrite <- (firstn_skipn j (skipn k bs)) in HS. apply bytes_at_app in HS. destruct HS as [HS _]. exact HS.
Qed.

Lemma rcf_nth_firstn : forall (bs : list byte) j i d, (i < j)%nat -> nth i (firstn j bs) d = nth i bs d.
Proof.
  induction bs as [|x bs IH]; intros j i d Hi; destruct j as [|j]; try lia; cbn; [destruct i; reflexivity|].
  destruct i as [|i]; [reflexivity|]. apply IH. lia.
Qed.

Lemma rcf_psum_firstn : forall bs j k, (k <= j)%nat -> psum (firstn j bs) k = psum bs k.
Proof.
  intros bs j k Hk. apply rcf_psum_ext. intros i Hi. apply rcf_nth_firstn. lia.
Qed.

Lemma rcf_ltu_neg_l : forall x k, 0 <= x < 2^64 -> - 2^64 < k < 0 ->
  bv_ltu (Z_to_bv 64 k) (Z_to_bv 64 x) = (2^64 + k <? x).
Proof. intros x k Hx Hk. unfold bv_ltu. rewrite (rcf_negk k) by lia. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma rcf_frame16 : forall segs m S W (x y : word), stk segs m (S - 16) S ->
  munch ((S - 16, S) :: W) m (write_to_mem (write_to_mem m (Z_to_bv 64 (S + -8)) (le8 x)) (Z_to_bv 64 (S + -16)) (le8 y)) /\
  wmono segs m (write_to_mem (write_to_mem m (Z_to_bv 64 (S + -8)) (le8 x)) (Z_to_bv 64 (S + -16)) (le8 y)) /\
  (mem_inv segs m ->
   mem_inv segs (write_to_mem (write_to_mem m (Z_to_bv 64 (S + -8)) (le8 x)) (Z_to_bv 64 (S + -16)) (le8 y))) /\
  stk segs (write_to_mem (write_to_mem m (Z_to_bv 64 (S + -8)) (le8 x)) (Z_to_bv 64 (S + -16)) (le8 y)) (S - 16) S /\
  bytes_at segs (write_to_mem (write_to_mem m (Z_to_bv 64 (S + -8)) (le8 x)) (Z_to_bv 64 (S + -16)) (le8 y))
    (S + -8) (le8 x) /\
  bytes_at segs (write_to_mem (write_to_mem m (Z_to_bv 64 (S + -8)) (le8 x)) (Z_to_bv 64 (S + -16)) (le8 y))
    (S + -16) (le8 y) /\
  (forall A bs, bytes_at segs m A bs -> S <= A \/ A + Z.of_nat (length bs) <= S - 16 ->
     bytes_at segs (write_to_mem (write_to_mem m (Z_to_bv 64 (S + -8)) (le8 x)) (Z_to_bv 64 (S + -16)) (le8 y)) A bs) /\
  (forall A k, wr_at segs m A k ->
     wr_at segs (write_to_mem (write_to_mem m (Z_to_bv 64 (S + -8)) (le8 x)) (Z_to_bv 64 (S + -16)) (le8 y)) A k).
Proof.
  intros segs m S W x y ST. pose proof ST as (ST1 & ST2 & _).
  change (Z_to_bv 64 (S + -8)) with (wa (S + -8)). change (Z_to_bv 64 (S + -16)) with (wa (S + -16)).
  assert (L8 : forall v : word, Z.of_nat (length (le8 v)) = 8) by (intros v; rewrite length_le8; reflexivity).
  assert (HS1 : store_ok segs m (wa (S + -8)) (length (le8 x)) = true)
    by (rewrite length_le8; apply (rcf_stk_store_ok segs m (S - 16) S); [exact ST | lia | cbn; lia]).
  pose proof (stk_write segs m (S - 16) S (S + -8) (le8 x) ST ltac:(lia) ltac:(rewrite L8; lia)) as ST'.
  assert (HS2 : store_ok segs (write_to_mem m (wa (S + -8)) (le8 x)) (wa (S + -16)) (length (le8 y)) = true)
    by (rewrite length_le8; apply (rcf_stk_store_ok segs _ (S - 16) S); [exact ST' | lia | cbn; lia]).
  split.
  { apply munch_write; [|lia|rewrite L8; lia|cbn [inside]; left; rewrite L8; lia].
    apply munch_write; [apply munch_refl|lia|rewrite L8; lia|cbn [inside]; left; rewrite L8; lia]. }
  split; [apply wmono_write; apply wmono_write; apply wmono_refl|].
  split; [intros HI; apply mem_inv_store; [apply mem_inv_store; [exact HI | exact HS1] | exact HS2]|].
  split; [apply stk_write; [exact ST' | lia | rewrite L8; lia]|].
  split.
  { apply bytes_at_write_other; [apply bytes_at_write_same; [lia | rewrite L8; lia] | lia | rewrite L8; lia |].
    rewrite !L8. lia. }
  split; [apply bytes_at_write_same; [lia | rewrite L8; lia]|].
  split.
  { intros A bs HB HD. pose proof (bytes_at_bound segs m A bs HB) as BD.
    apply bytes_at_write_other; [apply bytes_at_write_other; [exact HB | lia | rewrite L8; lia | rewrite L8; lia]
                                | lia | rewrite L8; lia | rewrite L8; lia]. }
  intros A k HW. apply wr_at_write. apply wr_at_write. exact HW.
Qed.

Lemma rcf_wr_sub : forall segs m A k j, wr_at segs m A k -> 0 <= j -> 0 <= k -> forall i, 0 <= i -> i + j <= k ->
  wr_at segs m (A + i) j.
Proof.
  intros segs m A k j (H1 & H2 & H) Hj Hk i Hi Hij. split; [lia|]. split; [lia|].
  intros x Hx. replace (A + i + x) with (A + (i + x)) by lia. apply H. lia.
Qed.

Lemma rcf_munch_in : forall lo hi W m m', munch [(lo, hi)] m m' ->
  (forall x, outside W x -> ~ (lo <= x < hi)) -> munch W m m'.
Proof.
  intros lo hi W m m' MU H. apply (munch_weaken [(lo, hi)] W); [|exact MU].
  intros x Hx. cbn [outside]. split; [apply H; exact Hx | exact I].
Qed.