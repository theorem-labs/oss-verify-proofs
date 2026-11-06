From Stdlib Require Import ZArith NArith Arith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Spec Require Import StrFun StrStr StrBytes TwoWay TwSearch.
Import ListNotations.
Open Scope Z_scope.

Lemma tw_rd8 : forall segs m a v, bytes_at segs m a (le8 v) -> ov_read_bytes segs m (wa a) 8 = Some (le8 v).
Proof.
  intros segs m a v H. rewrite <- (Z.add_0_r a). rewrite (bytes_at_read segs m a _ 0 8 H).
  - reflexivity.
  - lia.
  - rewrite length_le8. lia.
Qed.

Lemma tw_rd1 : forall segs m (A : Z) (bs : list byte) (i : nat) (b : byte) (a : word),
  bytes_at segs m A bs -> nth_error bs i = Some b -> bv_unsigned a = A + Z.of_nat i ->
  ov_read_bytes segs m a 1 = Some [b].
Proof.
  intros segs m A bs i b a H E Ha.
  apply (u8ro_read segs m A bs (Z.of_nat i) b a H); [rewrite Nat2Z.id; exact E | lia |].
  unfold wa. rewrite <- Ha. symmetry. apply Z_to_bv_lit_self.
Qed.

Lemma tw_stk_release_u64 : forall segs m lo A ws,
  stk segs m lo A -> u64arr segs m A ws -> lo <= A -> stk segs m lo (A + 8 * Z.of_nat (length ws)).
Proof.
  intros segs m lo A ws Hs [Hb Hw] Hle.
  assert (Hc : rw_cells segs m A [CB (length (u64s ws)) (u64s ws)]).
  { apply rw_cells_of_u8arr. split; [exact Hb|]. rewrite u64s_length.
    replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact Hw. }
  pose proof (stk_release segs m lo A _ Hs Hc Hle) as R. cbn [cells_size csize] in R. rewrite u64s_length in R.
  replace (A + 8 * Z.of_nat (length ws)) with (A + Z.of_nat (8 * length ws + 0)) by lia. exact R.
Qed.

Lemma tw_Z_to_le_bytes_inv : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
  pose proof (bytes_le_to_Z_nonneg bs) as Nn.
  rewrite lor_shiftl8_add by lia.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by ring.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - transitivity (Z_to_le_bytes (length bs) (bytes_le_to_Z bs)); [|exact IH]. f_equal.
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by ring.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma tw_u64s_exists : forall n (bs : list byte), length bs = (8 * n)%nat ->
  exists ws, length ws = n /\ u64s ws = bs.
Proof.
  induction n as [|n IH]; intros bs H.
  - exists []. destruct bs; [split; reflexivity | cbn in H; lia].
  - destruct (IH (skipn 8 bs) ltac:(rewrite length_skipn; lia)) as (ws & L & E).
    exists (Z_to_bv 64 (bytes_le_to_Z (firstn 8 bs)) :: ws). split; [cbn; lia|].
    cbn [u64s]. rewrite E. rewrite <- (firstn_skipn 8 bs) at 3. f_equal.
    assert (L8 : length (firstn 8 bs) = 8%nat) by (rewrite length_firstn; lia).
    pose proof (bytes_le_to_Z_nonneg (firstn 8 bs)) as N0. pose proof (bytes_le_to_Z_bound (firstn 8 bs)) as N1.
    rewrite L8 in N1. change (8 * Z.of_nat 8) with 64 in N1.
    unfold le8, word_to_le_bytes. rewrite unsigned_lit by lia.
    rewrite <- L8 at 1. apply tw_Z_to_le_bytes_inv.
Qed.

Lemma tw_u64arr_of_CB : forall segs m A n bs, rw_cells segs m A [CB (8 * n) bs] ->
  exists ws, length ws = n /\ u64arr segs m A ws.
Proof.
  intros segs m A n bs [[Hwf Hb] Hw]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Lb _].
  destruct (tw_u64s_exists n bs Lb) as (ws & L & E). exists ws. split; [exact L|].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. cbn [cells_size csize] in Hw.
  split.
  - rewrite E. exact Hb.
  - replace (8 * Z.of_nat (length ws)) with (Z.of_nat (8 * n + 0)) by lia. exact Hw.
Qed.

Lemma tw_u64arr_of_C8x4 : forall segs m A w0 w1 w2 w3,
  rw_cells segs m A [C8 w0; C8 w1; C8 w2; C8 w3] -> u64arr segs m A [w0; w1; w2; w3].
Proof.
  intros segs m A w0 w1 w2 w3 [[_ Hb] Hw]. split.
  - exact Hb.
  - exact Hw.
Qed.

Lemma tw_word_of : forall (w : word) e, bv_unsigned w = e -> w = Z_to_bv 64 e.
Proof. intros w e H. subst e. symmetry. apply Z_to_bv_lit_self. Qed.

Lemma tw_nth_upd_same : forall {X} (l : list X) i x d, (i < length l)%nat -> nth i (upd l i x) d = x.
Proof. intros X l. induction l as [|y l IH]; intros [|i] x d Hi; cbn in Hi |- *; try lia; [reflexivity|]. apply IH. lia. Qed.

Lemma tw_nth_upd_other : forall {X} (l : list X) i j x d, i <> j -> nth j (upd l i x) d = nth j l d.
Proof. intros X l. induction l as [|y l IH]; intros [|i] [|j] x d Hij; cbn; try reflexivity; [lia|]. apply IH. lia. Qed.

Lemma tw_nth_error_nth : forall {X} (l : list X) i d, (i < length l)%nat -> nth_error l i = Some (nth i l d).
Proof. intros X l. induction l as [|y l IH]; intros [|i] d Hi; cbn in Hi |- *; try lia; [reflexivity|]. apply IH. lia. Qed.

Lemma tw_firstn_S : forall (l : list Z) i, (i < length l)%nat -> firstn (S i) l = firstn i l ++ [at_ l i].
Proof.
  unfold at_. induction l as [|a l IH]; intros [|i] H; cbn [length] in H; try lia; [reflexivity|].
  cbn [firstn nth]. rewrite IH by lia. reflexivity.
Qed.

Lemma tw_fold_ext : forall (f g : nat -> nat -> nat) (l : list nat) a,
  (forall acc i, In i l -> f acc i = g acc i) -> fold_left f l a = fold_left g l a.
Proof.
  intros f g l. induction l as [|i l IH]; intros a H; cbn; [reflexivity|].
  rewrite H by (left; reflexivity). apply IH. intros acc j Hj. apply H. right. exact Hj.
Qed.

Lemma tw_shift_of_snoc : forall x v b, shift_of (x ++ [v]) b = if Z.eqb v b then S (length x) else shift_of x b.
Proof.
  intros x v b. unfold shift_of. rewrite length_app. cbn [length]. rewrite seq_app, fold_left_app.
  cbn [seq fold_left]. rewrite Nat.add_0_l.
  rewrite (tw_fold_ext _ (fun acc i => if Z.eqb (at_ x i) b then S i else acc)).
  - unfold at_ at 1. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
  - intros acc i Hi. apply in_seq in Hi. unfold at_. rewrite app_nth1 by lia. reflexivity.
Qed.

Lemma tw_inset_snoc : forall x v b, inset (x ++ [v]) b = (inset x b || Z.eqb b v)%bool.
Proof. intros x v b. unfold inset. rewrite existsb_app. cbn [existsb]. rewrite orb_false_r. reflexivity. Qed.

Lemma tw_shift_of_le : forall x b, (shift_of x b <= length x)%nat.
Proof.
  intros x b. unfold shift_of.
  assert (G : forall l a, (a <= length x)%nat -> (forall i, In i l -> i < length x)%nat ->
     (fold_left (fun acc i => if Z.eqb (at_ x i) b then S i else acc) l a <= length x)%nat).
  { induction l as [|i l IH]; intros a Ha Hl; cbn; [exact Ha|]. apply IH; [|intros j Hj; apply Hl; right; exact Hj].
    destruct (Z.eqb (at_ x i) b); [specialize (Hl i (or_introl eq_refl)); lia | exact Ha]. }
  apply G; [lia|]. intros i Hi. apply in_seq in Hi. lia.
Qed.

Definition TBL (x : list Z) (tbl : list word) : Prop :=
  length tbl = 256%nat /\
  forall v, 0 <= v < 256 -> inset x v = true -> bv_unsigned (nth (Z.to_nat v) tbl (Z_to_bv 64 0)) = Z.of_nat (shift_of x v).

Definition BSET (x : list Z) (bset : list word) : Prop :=
  length bset = 4%nat /\
  forall v, 0 <= v < 256 -> Z.testbit (bv_unsigned (nth (Z.to_nat (v / 64)) bset (Z_to_bv 64 0))) (v mod 64) = inset x v.

Lemma tw_TBL_nil : forall tbl, length tbl = 256%nat -> TBL [] tbl.
Proof. intros tbl L. split; [exact L|]. intros v _ H. discriminate. Qed.

Lemma tw_BSET_nil : BSET [] [Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0].
Proof.
  split; [reflexivity|]. intros v Hv.
  assert (E : bv_unsigned (nth (Z.to_nat (v / 64)) [Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0] (Z_to_bv 64 0)) = 0).
  { destruct (Z.to_nat (v / 64)) as [|[|[|[|[|k]]]]]; reflexivity. }
  rewrite E. apply Z.testbit_0_l.
Qed.

Lemma tw_TBL_snoc : forall x tbl v (w : word), TBL x tbl -> 0 <= v < 256 ->
  bv_unsigned w = Z.of_nat (S (length x)) -> TBL (x ++ [v]) (upd tbl (Z.to_nat v) w).
Proof.
  intros x tbl v w [L H] Hv Hw. split; [rewrite upd_length; exact L|].
  intros u Hu Hin. rewrite tw_inset_snoc in Hin. rewrite tw_shift_of_snoc.
  destruct (Z.eqb_spec v u) as [->|Ne].
  - rewrite tw_nth_upd_same by lia. exact Hw.
  - rewrite tw_nth_upd_other by lia. apply H; [exact Hu|].
    apply orb_true_iff in Hin. destruct Hin as [Hin|Hin]; [exact Hin|]. apply Z.eqb_eq in Hin. congruence.
Qed.

Lemma tw_testbit_lor_pow : forall a k j, 0 <= k -> 0 <= j ->
  Z.testbit (Z.lor a (Z.shiftl 1 k)) j = (Z.testbit a j || Z.eqb j k)%bool.
Proof.
  intros a k j Hk Hj. rewrite Z.lor_spec, Z.shiftl_spec by lia. f_equal.
  destruct (Z.eqb_spec j k) as [->|Ne].
  - rewrite Z.sub_diag. reflexivity.
  - destruct (Z.ltb_spec (j - k) 0) as [Lt|Ge].
    + apply Z.testbit_neg_r. lia.
    + apply Z.bits_above_log2; [lia | change (Z.log2 1) with 0; lia].
Qed.

Lemma tw_BSET_snoc : forall x bset v (w : word), BSET x bset -> 0 <= v < 256 ->
  bv_unsigned w = Z.lor (bv_unsigned (nth (Z.to_nat (v / 64)) bset (Z_to_bv 64 0))) (Z.shiftl 1 (v mod 64)) ->
  BSET (x ++ [v]) (upd bset (Z.to_nat (v / 64)) w).
Proof.
  intros x bset v w [L H] Hv Hw. split; [rewrite upd_length; exact L|].
  intros u Hu. rewrite tw_inset_snoc.
  assert (Q4 : 0 <= u / 64 < 4) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  assert (V4 : 0 <= v / 64 < 4) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  destruct (Z.eqb_spec (u / 64) (v / 64)) as [Eq|Ne].
  - rewrite Eq, tw_nth_upd_same by lia. rewrite Hw.
    rewrite tw_testbit_lor_pow by (apply Z.mod_pos_bound; lia).
    rewrite <- Eq. rewrite H by exact Hu. f_equal.
    destruct (Z.eqb_spec (u mod 64) (v mod 64)) as [E2|N2]; destruct (Z.eqb_spec u v) as [E3|N3]; try reflexivity.
    + exfalso. apply N3. rewrite (Z.div_mod u 64), (Z.div_mod v 64) by lia. lia.
    + exfalso. apply N2. subst. reflexivity.
  - rewrite tw_nth_upd_other by lia. rewrite H by exact Hu.
    replace (Z.eqb u v) with false; [rewrite orb_false_r; reflexivity|].
    symmetry. apply Z.eqb_neq. intros ->. apply Ne. reflexivity.
Qed.

Lemma tw_land1_shiftr : forall a k, 0 <= k -> (Z.land (Z.shiftr a k) 1 = 0 <-> Z.testbit a k = false).
Proof.
  intros a k Hk. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. change (2 ^ 1) with 2.
  rewrite Zmod_odd. rewrite <- Z.bit0_odd, Z.shiftr_spec by lia. rewrite Z.add_0_l.
  destruct (Z.testbit a k); split; intros; congruence.
Qed.

Lemma tw_bs_idx : forall v, 0 <= v < 256 -> Z.land (Z.shiftr v 3) 24 = 8 * (v / 64).
Proof.
  intros v Hv.
  assert (H : forallb (fun v => Z.land (Z.shiftr v 3) 24 =? 8 * (v / 64)) (zseq 256) = true) by (vm_compute; reflexivity).
  pose proof (forallb_zseq 256 _ H v ltac:(lia)) as E. apply Z.eqb_eq in E. exact E.
Qed.

Lemma tw_bs_idx8 : forall v, 0 <= v < 256 -> Z.land (Z.shiftr v 3) 18446744073709551608 = 8 * (v / 64).
Proof.
  intros v Hv.
  assert (H : forallb (fun v => Z.land (Z.shiftr v 3) 18446744073709551608 =? 8 * (v / 64)) (zseq 256) = true)
    by (vm_compute; reflexivity).
  pose proof (forallb_zseq 256 _ H v ltac:(lia)) as E. apply Z.eqb_eq in E. exact E.
Qed.

Lemma tw_memcmp_zero : forall n (l r : list byte) v, memcmp_model l r n = Some v ->
  (v = 0 <-> forall j, (j < n)%nat -> nth j (map bv_unsigned l) 0 = nth j (map bv_unsigned r) 0).
Proof.
  induction n as [|n IH]; intros l r v H.
  - cbn in H. inversion H; subst. split; [intros _ j Hj; lia | reflexivity].
  - destruct l as [|a l]; destruct r as [|b r]; cbn in H; try discriminate.
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|E].
    + rewrite (IH l r v H). split.
      * intros G [|j] Hj; cbn [map nth]; [exact E|]. apply G. lia.
      * intros G j Hj. exact (G (S j) ltac:(lia)).
    + inversion H; subst. split; [intros; lia|]. intros G. exfalso. apply E. exact (G 0%nat ltac:(lia)).
Qed.

Lemma tw_nth_map_skipn : forall p (l : list byte) j, nth j (map bv_unsigned (skipn p l)) 0 = at_ (map bv_unsigned l) (j + p).
Proof.
  unfold at_. induction p as [|p IH]; intros l j.
  - rewrite Nat.add_0_r. reflexivity.
  - destruct l as [|a l]; cbn [skipn map].
    + rewrite !nth_overflow by (cbn; lia). reflexivity.
    + replace (j + S p)%nat with (S (j + p)) by lia. cbn [nth]. apply IH.
Qed.
