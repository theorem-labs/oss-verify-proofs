From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcFrag.
Import ListNotations.
Open Scope Z_scope.

Lemma rf_nth_skipn : forall (l : list byte) k i d, nth i (skipn k l) d = nth (k + i) l d.
Proof.
  induction l as [|x l IH]; intros k i d; destruct k as [|k]; cbn; try reflexivity.
  - destruct i; reflexivity.
  - apply IH.
Qed.

Lemma rf_nth_firstn : forall (l : list byte) n i d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
  induction l as [|x l IH]; intros n i d Hi; destruct n as [|n]; try lia.
  - destruct i; reflexivity.
  - destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.

Lemma rf_bsl_length : forall bs k n, 0 <= k -> 0 <= n -> k + n <= Z.of_nat (length bs) ->
  length (bsl bs k n) = Z.to_nat n.
Proof. intros bs k n Hk Hn H. unfold bsl. rewrite length_firstn, length_skipn. lia. Qed.

Lemma rf_bytes_bsl : forall segs m A bs k n, bytes_at segs m A bs -> 0 <= k -> 0 <= n ->
  k + n <= Z.of_nat (length bs) -> bytes_at segs m (A + k) (bsl bs k n).
Proof.
  intros segs m A bs k n (H0 & H1 & H2) Hk Hn Hkn.
  pose proof (rf_bsl_length bs k n Hk Hn Hkn) as Hlen.
  unfold bytes_at. rewrite Hlen. split; [lia|]. split; [lia|].
  intros i Hi. replace (A + k + Z.of_nat i) with (A + Z.of_nat (Z.to_nat k + i)) by lia.
  rewrite H2 by lia. unfold bsl. rewrite nth_error_firstn.
  destruct (Nat.ltb_spec i (Z.to_nat n)); [|lia].
  rewrite nth_error_skipn. reflexivity.
Qed.

Lemma rf_bytes_skip : forall segs m A bs k, bytes_at segs m A bs -> 0 <= k <= Z.of_nat (length bs) ->
  bytes_at segs m (A + k) (skipn (Z.to_nat k) bs).
Proof.
  intros segs m A bs k HB Hk. rewrite <- (firstn_skipn (Z.to_nat k) bs) in HB.
  apply bytes_at_app in HB. destruct HB as [_ HB].
  rewrite length_firstn in HB. replace (Z.of_nat (Nat.min (Z.to_nat k) (length bs))) with k in HB by lia.
  exact HB.
Qed.

Lemma rf_bytes_first : forall segs m A bs n, bytes_at segs m A bs -> bytes_at segs m A (firstn n bs).
Proof.
  intros segs m A bs n HB. rewrite <- (firstn_skipn n bs) in HB.
  apply bytes_at_app in HB. destruct HB as [HB _]. exact HB.
Qed.

Lemma rf_rw_sub : forall segs m A bs k n, bytes_at segs m A bs -> wr_at segs m A (Z.of_nat (length bs)) ->
  0 <= k -> 0 <= n -> k + n <= Z.of_nat (length bs) ->
  rw_cells segs m (A + k) [CB (Z.to_nat n) (bsl bs k n)].
Proof.
  intros segs m A bs k n HB HW Hk Hn Hl. split; [split|].
  - cbn. split; [apply rf_bsl_length; lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply rf_bytes_bsl; assumption.
  - cbn [cells_size csize]. destruct HW as (H0 & H1 & H2). split; [lia|]. split; [lia|].
    intros i Hi. replace (A + k + i) with (A + (k + i)) by lia. apply H2. lia.
Qed.

Lemma rf_rw_parts : forall segs m A n bs, rw_cells segs m A [CB n bs] ->
  bytes_at segs m A bs /\ wr_at segs m A (Z.of_nat n) /\ length bs = n.
Proof.
  intros segs m A n bs [[Hwf Hb] Hw]. cbn in Hwf. destruct Hwf as [HL _].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. cbn [cells_size csize] in Hw.
  rewrite Nat.add_0_r in Hw. split; [exact Hb|]. split; [exact Hw | exact HL].
Qed.

Lemma rf_rd1 : forall segs m A bs k, bytes_at segs m A bs -> 0 <= k -> k < Z.of_nat (length bs) ->
  ov_read_bytes segs m (wa (A + k)) 1 = Some [nth (Z.to_nat k) bs (Z_to_bv 8 0)].
Proof.
  intros segs m A bs k HB Hk Hl.
  replace (A + k) with (A + Z.of_nat (Z.to_nat k)) by lia.
  apply rd_byte; [exact HB | lia].
Qed.

Lemma rf_wr_sub : forall segs m A n k j, wr_at segs m A n -> 0 <= k -> 0 <= j -> k + j <= n -> wr_at segs m (A + k) j.
Proof.
  intros segs m A n k j (H0 & H1 & H2) Hk Hj Hkj. split; [lia|]. split; [lia|].
  intros i Hi. replace (A + k + i) with (A + (k + i)) by lia. apply H2. lia.
Qed.

Lemma rf_beq : forall (b : byte) c, 0 <= c < 2^64 -> bv_eqb (zxb b) (Z_to_bv 64 c) = (bv_unsigned b =? c).
Proof.
  intros b c Hc. unfold bv_eqb, zxb. pose proof (byte_range b).
  rewrite !unsigned_lit by lia. reflexivity.
Qed.

Lemma rf_zxb_u : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof. intros b. unfold zxb. pose proof (byte_range b). apply unsigned_lit. lia. Qed.

Lemma rf_psum_firstn : forall bs n k, (k <= n)%nat -> psum (firstn n bs) k = psum bs k.
Proof.
  intros bs n k. induction k as [|k IH]; intros Hk; cbn [psum]; [reflexivity|].
  rewrite IH by lia. rewrite rf_nth_firstn by lia. reflexivity.
Qed.

Lemma rf_psum_ext : forall bs cs k, (forall i, (i < k)%nat -> nth i bs (Z_to_bv 8 0) = nth i cs (Z_to_bv 8 0)) ->
  psum bs k = psum cs k.
Proof.
  intros bs cs k. induction k as [|k IH]; intros H; cbn [psum]; [reflexivity|].
  rewrite IH by (intros; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Lemma rf_munch_weaken : forall W W' m m', munch W m m' -> (forall x, outside W' x -> outside W x) -> munch W' m m'.
Proof. intros W W' m m' H Hs x Hx. apply H, Hs, Hx. Qed.

Lemma rf_munch_eq : forall W W' m m', munch W m m' -> W = W' -> munch W' m m'.
Proof. intros; subst; assumption. Qed.

Lemma rf_app : forall segs m A x B y, bytes_at segs m A x -> bytes_at segs m B y -> B = A + Z.of_nat (length x) ->
  bytes_at segs m A (x ++ y).
Proof. intros segs m A x B y HX HY ->. apply bytes_at_app. split; assumption. Qed.

Lemma rf_b1 : forall b : byte, bv_ltu (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned (zxb b) + -1)) =
  negb ((bv_unsigned b =? 1) || (bv_unsigned b =? 2)).
Proof.
  intros b. rewrite rf_zxb_u. pose proof (byte_range b). unfold bv_ltu.
  rewrite (unsigned_lit 1) by lia. rewrite unsigned_lit_wrap. change (2^64) with 18446744073709551616.
  destruct (Z.eqb_spec (bv_unsigned b) 1); destruct (Z.eqb_spec (bv_unsigned b) 2); cbn [orb negb];
    first [apply Z.ltb_ge | apply Z.ltb_lt]; Z.div_mod_to_equations; lia.
Qed.

Lemma rf_n : forall b : byte, bv_ltu (Z_to_bv 64 (bv_unsigned (zxb b) + -23)) (Z_to_bv 64 (-22)) =
  negb ((1 <=? bv_unsigned b) && (bv_unsigned b <=? 22)).
Proof.
  intros b. rewrite rf_zxb_u. pose proof (byte_range b). unfold bv_ltu.
  rewrite !unsigned_lit_wrap. change (2^64) with 18446744073709551616.
  destruct (Z.leb_spec 1 (bv_unsigned b)); destruct (Z.leb_spec (bv_unsigned b) 22); cbn [andb negb];
    first [apply Z.ltb_ge | apply Z.ltb_lt]; Z.div_mod_to_equations; lia.
Qed.

Lemma rf_land_eq0 : forall s k, 0 <= s < 2^64 -> 0 <= k <= 64 ->
  bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 s)) (Z.ones k))) (Z_to_bv 64 0) = (s mod 2^k =? 0).
Proof.
  intros s k Hs Hk. rewrite (unsigned_lit s) by lia. rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound s (2^k) ltac:(lia)) as M.
  assert (2^k <= 2^64) by (apply Z.pow_le_mono_r; lia).
  unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity.
Qed.

Lemma rf_eqb_s : forall x, -2^63 <= x < 2^63 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = (x =? 0).
Proof.
  intros x Hx. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  change (2^64) with 18446744073709551616. change (2^63) with 9223372036854775808 in Hx.
  destruct (Z.eqb_spec x 0) as [E|E]; [subst; reflexivity|].
  apply Z.eqb_neq. intros E'. apply E. Z.div_mod_to_equations. lia.
Qed.

Lemma rf_recsum_bsl : forall J k n, 0 <= k -> 0 <= n -> k + n <= Z.of_nat (length J) ->
  recsum (bsl J k n) = psum (skipn (Z.to_nat k) J) (Z.to_nat n) mod 128.
Proof.
  intros J k n Hk Hn H. unfold recsum. rewrite rf_bsl_length by lia. unfold bsl.
  rewrite rf_psum_firstn by lia. reflexivity.
Qed.

Lemma rf_le1_0 : le1 (Z_to_bv 64 0) = [Z_to_bv 8 0].
Proof. reflexivity. Qed.

Lemma rf_le1_1 : le1 (Z_to_bv 64 1) = [Z_to_bv 8 1].
Proof. reflexivity. Qed.

Lemma rf_land255 : forall s, 0 <= s < 2^64 ->
  bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 s)) 255)) (Z_to_bv 64 0) = (s mod 256 =? 0).
Proof. intros s Hs. exact (rf_land_eq0 s 8 Hs ltac:(lia)). Qed.

Lemma rf_land127 : forall s, 0 <= s < 2^64 ->
  bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 s)) 127)) (Z_to_bv 64 0) = (s mod 128 =? 0).
Proof. intros s Hs. exact (rf_land_eq0 s 7 Hs ltac:(lia)). Qed.

Lemma rf_clear_length : forall st, length st = 72%nat -> length (fg_clear st) = 72%nat.
Proof. intros st HL. unfold fg_clear. rewrite !length_app, length_firstn, length_skipn. cbn [length]. lia. Qed.

Lemma rf_clear_nth : forall st i d, length st = 72%nat -> i <> 6%nat -> nth i (fg_clear st) d = nth i st d.
Proof.
  intros st i d HL Hi. unfold fg_clear.
  destruct (Nat.ltb_spec i 6) as [L|L].
  - rewrite app_nth1 by (rewrite length_firstn; lia). apply rf_nth_firstn. exact L.
  - rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
    replace (Nat.min 6 (length st)) with 6%nat by lia.
    destruct (i - 6)%nat as [|k] eqn:E; [lia|]. cbn [app nth].
    rewrite rf_nth_skipn. f_equal. lia.
Qed.

Lemma rf_clear_skipn : forall st k, length st = 72%nat -> (7 <= k)%nat -> skipn k (fg_clear st) = skipn k st.
Proof.
  intros st k HL Hk. unfold fg_clear.
  rewrite skipn_app, (skipn_all2 (firstn 6 st)) by (rewrite length_firstn; lia).
  rewrite length_firstn. replace (Nat.min 6 (length st)) with 6%nat by lia.
  rewrite skipn_app, (skipn_all2 [Z_to_bv 8 0]) by (cbn [length]; lia).
  cbn [app length]. rewrite skipn_skipn. f_equal. lia.
Qed.

Lemma rf_upd_clear : forall st, upd_bytes st 6 [Z_to_bv 8 0] = fg_clear st.
Proof. reflexivity. Qed.

Lemma rf_fg_join_length : forall st g, length st = 72%nat -> length g = 50%nat -> 1 <= fg_n g <= 22 ->
  fg_T st g <= 64 -> length (fg_join st g) = 72%nat.
Proof.
  intros st g HL HG Hn HT. unfold fg_join, fg_T, fg_lf, fg_body in *.
  pose proof (byte_range (nth (Z.to_nat 7) st (Z_to_bv 8 0))) as R. unfold bat in *.
  rewrite !length_app, length_firstn, length_skipn, rf_bsl_length by lia. lia.
Qed.

Lemma rf_class_refuse : forall f fr pa pp pn len st g,
  f = 0 \/ fr = 0 \/ pa = 0 \/ pp = 0 \/ pn = 0 -> fg_class f fr pa pp pn len st g = FgRefuse.
Proof.
  intros f fr pa pp pn len st g H. unfold fg_class.
  destruct H as [-> | [-> | [-> | [-> | ->]]]]; rewrite ?orb_true_r; reflexivity.
Qed.

Lemma rf_class_nn : forall f fr pa pp pn len st g, f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
  fg_class f fr pa pp pn len st g =
  if negb (fg_fr len g) then FgNone
  else if bat g 19 =? 1 then FgFirst
  else if negb (fg_keep st g) then FgDrop
  else if negb (fg_close st g) then FgJoin
  else FgClose.
Proof.
  intros f fr pa pp pn len st g H1 H2 H3 H4 H5. unfold fg_class.
  rewrite (proj2 (Z.eqb_neq f 0) H1), (proj2 (Z.eqb_neq fr 0) H2), (proj2 (Z.eqb_neq pa 0) H3),
    (proj2 (Z.eqb_neq pp 0) H4), (proj2 (Z.eqb_neq pn 0) H5). reflexivity.
Qed.

Lemma rf_src_eq : forall st g, fg_src_eq st g = true <->
  (forall i, (i < 6)%nat -> bv_unsigned (nth i st (Z_to_bv 8 0)) = bv_unsigned (nth i (skipn 6 g) (Z_to_bv 8 0))).
Proof.
  intros st g. unfold fg_src_eq, bat. rewrite !andb_true_iff, !Z.eqb_eq.
  setoid_rewrite rf_nth_skipn. split.
  - intros (((((E0 & E1) & E2) & E3) & E4) & E5) i Hi.
    do 6 (destruct i as [|i]; [assumption|]). lia.
  - intros H. repeat split; [apply (H 0%nat) | apply (H 1%nat) | apply (H 2%nat) | apply (H 3%nat)
                            | apply (H 4%nat) | apply (H 5%nat)]; lia.
Qed.
