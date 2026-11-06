From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel GrantModel GrantSweepModel GroupaModel.
Import ListNotations.
Open Scope Z_scope.

Definition sweep_vals (T : list byte) (t base : Z) (w : nat) : list byte :=
  map (fun j => Z_to_bv 8 (eff T t (base + Z.of_nat j / 3) (Z.of_nat j mod 3))) (seq 0 (3 * w)).

Definition bsw_ok (s al mx base w : Z) : bool :=
  negb (s =? 0) && negb (al =? 0) && fits base w && (8 + 3 * w <=? mx).

Definition tx_set01 (T : list byte) : Prop :=
  forall ch p, 0 <= ch < 48 -> 0 <= p < 3 -> tb T (144 + 3 * ch + p) = 0 \/ tb T (144 + 3 * ch + p) = 1.

Definition tx_legal (T : list byte) : Prop :=
  forall ch p, 0 <= ch < 48 -> 0 <= p < 3 -> tb T (144 + 3 * ch + p) = 1 -> legal p (tb T (3 * ch + p)).

Lemma length_sweep_vals : forall T t base w, length (sweep_vals T t base w) = (3 * w)%nat.
Proof. intros. unfold sweep_vals. rewrite length_map, length_seq. reflexivity. Qed.

Lemma nth_sweep_vals : forall T t base w (c p : nat) d, (c < w)%nat -> (p < 3)%nat ->
  nth (3 * c + p) (sweep_vals T t base w) d = Z_to_bv 8 (eff T t (base + Z.of_nat c) (Z.of_nat p)).
Proof.
  intros T t base w c p d Hc Hp. unfold sweep_vals.
  set (f := fun j : nat => Z_to_bv 8 (eff T t (base + Z.of_nat j / 3) (Z.of_nat j mod 3))).
  rewrite (nth_indep (map f (seq 0 (3 * w))) d (f 0%nat)) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. subst f. cbv beta. cbn [Nat.add].
  replace (Z.of_nat (3 * c + p) / 3) with (Z.of_nat c) by (Z.div_mod_to_equations; lia).
  replace (Z.of_nat (3 * c + p) mod 3) with (Z.of_nat p) by (Z.div_mod_to_equations; lia).
  reflexivity.
Qed.

Lemma eff_legal : forall T t ch p, tx_set01 T -> tx_legal T -> 0 <= ch < 48 -> 0 <= p < 3 ->
  legal p (eff T t ch p).
Proof.
  intros T t ch p H01 HL Hch Hp. unfold eff.
  rewrite (proj2 (Z.leb_gt 3 p)) by lia.
  assert (Hd : legal p (dflt p)) by (unfold legal, dflt; destruct (Z.eqb_spec p 2); lia).
  destruct ((t =? 0) || (48 <=? ch)); [exact Hd|].
  destruct (Z.eqb_spec (tb T (144 + 3 * ch + p)) 0) as [E|E]; [exact Hd|].
  apply HL; [lia | lia |]. destruct (H01 ch p Hch Hp); lia.
Qed.

Lemma sweep_vals_legal : forall T t base w, tx_set01 T -> tx_legal T -> 0 <= base ->
  base + Z.of_nat w <= 48 -> vals_legal w (sweep_vals T t base w).
Proof.
  intros T t base w H01 HL Hb Hw j Hj. unfold vz.
  set (c := (j / 3)%nat). set (p := (j mod 3)%nat).
  assert (Ej : j = (3 * c + p)%nat) by (subst c p; apply Nat.div_mod; lia).
  assert (Hp : (p < 3)%nat) by (subst p; apply Nat.mod_upper_bound; lia).
  assert (Hc : (c < w)%nat) by lia.
  replace (Z.of_nat (j mod 3)) with (Z.of_nat p) by reflexivity.
  rewrite Ej, nth_sweep_vals by lia. rewrite u8_lit by apply eff_range.
  apply eff_legal; [exact H01 | exact HL | lia | lia].
Qed.

Lemma firstn_S_nth : forall (l : list byte) k d, (k < length l)%nat ->
  firstn (S k) l = firstn k l ++ [nth k l d].
Proof.
  induction l as [|x l IH]; intros k d Hk; cbn in Hk; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [firstn nth app]. f_equal. apply IH. lia.
Qed.

Lemma vstore : forall (VALS J : list byte) k b d, (k < length VALS)%nat -> (length VALS <= length J)%nat ->
  nth k VALS d = b ->
  upd_bytes (firstn k VALS ++ skipn k J) k [b] = firstn (S k) VALS ++ skipn (S k) J.
Proof.
  intros VALS J k b d Hk HJ Hn. unfold upd_bytes.
  assert (L : length (firstn k VALS) = k) by (rewrite length_firstn; lia).
  rewrite firstn_app, L, Nat.sub_diag, firstn_O, app_nil_r.
  rewrite firstn_all2 by lia.
  rewrite skipn_app, L. cbn [length]. replace (k - (k + 1))%nat with 0%nat by lia.
  rewrite (skipn_all2 (firstn k VALS)) by lia. cbn [app skipn].
  replace (k + 1 - k)%nat with 1%nat by lia.
  rewrite (firstn_S_nth VALS k d Hk), Hn, <- app_assoc. cbn [app]. f_equal. f_equal.
  rewrite skipn_skipn. f_equal. all: lia.
Qed.

Lemma length_vbytes : forall (VALS J : list byte) k, (k <= length VALS)%nat -> (length VALS <= length J)%nat ->
  length (firstn k VALS ++ skipn k J) = length J.
Proof. intros. rewrite length_app, length_firstn, length_skipn. lia. Qed.

Lemma land255_small : forall x, 0 <= x < 256 -> Z.land x 255 = x.
Proof.
  intros x Hx. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. exact Hx.
Qed.

Lemma rd_byte_at : forall segs m A bs (k : Z) b,
  bytes_at segs m A bs -> 0 <= k -> (Z.to_nat k < length bs)%nat -> nth (Z.to_nat k) bs (Z_to_bv 8 0) = b ->
  ov_read_bytes segs m (wa (A + k)) 1 = Some [b].
Proof.
  intros segs m A bs k b HB Hk Hl Hn. rewrite (bytes_at_read segs m A bs k 1 HB Hk) by lia.
  rewrite <- Hn. f_equal. clear HB Hn. revert bs Hl. induction (Z.to_nat k) as [|j IH]; intros bs Hl.
  - destruct bs; cbn in *; [lia | reflexivity].
  - destruct bs; cbn in *; [lia|]. apply IH. lia.
Qed.

Lemma le1_lit8 : forall e, 0 <= e < 256 -> le1 (Z_to_bv 64 e) = [Z_to_bv 8 e].
Proof.
  intros e He. replace (Z_to_bv 64 e) with (zxb (Z_to_bv 8 e)) by (unfold zxb; rewrite u8_lit by lia; reflexivity).
  apply le1_zxb.
Qed.

Lemma bsw_ok_spec : forall s al mx base w, bsw_ok s al mx base w = true ->
  s <> 0 /\ al <> 0 /\ 1 <= w <= 40 /\ 0 <= base /\ base + w <= 48 /\ 8 + 3 * w <= mx.
Proof.
  intros s al mx base w H. unfold bsw_ok, fits in H.
  repeat rewrite andb_true_iff in H. rewrite !negb_true_iff, !Z.eqb_neq, !Z.leb_le in H. lia.
Qed.

Lemma bsw_ok_go : forall s al mx base w, s <> 0 -> al <> 0 -> 1 <= w <= 40 -> 0 <= base -> base + w <= 48 ->
  bsw_ok s al mx base w = (8 + 3 * w <=? mx).
Proof.
  intros s al mx base w Hs Hal Hw Hb Hbw. unfold bsw_ok, fits.
  rewrite (proj2 (Z.eqb_neq s 0) Hs), (proj2 (Z.eqb_neq al 0) Hal).
  rewrite (proj2 (Z.leb_le 1 w)), (proj2 (Z.leb_le w 40)), (proj2 (Z.leb_le 0 base)), (proj2 (Z.leb_le (base + w) 48))
    by lia.
  reflexivity.
Qed.
