From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcPorts RcPortsLib RcLay.
Import ListNotations.
Open Scope Z_scope.

Lemma ly_rw_split2 : forall segs m A B cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) -> B = A + Z.of_nat (cells_size cs1) ->
  rw_cells segs m A cs1 /\ rw_cells segs m B cs2.
Proof.
  intros segs m A B cs1 cs2 [[Hwf Hb] (Ha & Hn & Hw)] ->.
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_size_app in Hn, Hw.
  split.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split; [assumption|]|].
    + rewrite cells_bytes_length in B2 by assumption. exact B2.
    + split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
      apply Hw. lia.
Qed.

Lemma ly_rw_join2 : forall segs m A B cs1 cs2,
  rw_cells segs m A cs1 -> B = A + Z.of_nat (cells_size cs1) -> rw_cells segs m B cs2 ->
  rw_cells segs m A (cs1 ++ cs2).
Proof.
  intros segs m A B cs1 cs2 [[W1 B1] (Ha & Hn & Hw1)] -> [[W2 B2] (Hb & Hn2 & Hw2)].
  split; [split|].
  - apply cells_wf_app. tauto.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|].
    rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.ltb_spec i (Z.of_nat (cells_size cs1))).
    + apply Hw1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
      apply Hw2. lia.
Qed.

Lemma ly_rw_cb : forall segs m A n bs, rw_cells segs m A [CB n bs] ->
  length bs = n /\ bytes_at segs m A bs /\ wr_at segs m A (Z.of_nat n).
Proof.
  intros segs m A n bs [[[Hl _] Hb] Hw]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw. split; [exact Hl|]. split; assumption.
Qed.

Lemma ly_cb_rw : forall segs m A bs, bytes_at segs m A bs -> wr_at segs m A (Z.of_nat (length bs)) ->
  rw_cells segs m A [CB (length bs) bs].
Proof.
  intros segs m A bs Hb Hw. split; [split|].
  - cbn. split; [reflexivity|exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hw.
Qed.

Lemma ly_rw_cb_eq : forall segs m A n bs, length bs = n -> bytes_at segs m A bs -> wr_at segs m A (Z.of_nat n) ->
  rw_cells segs m A [CB n bs].
Proof. intros segs m A n bs <- Hb Hw. apply ly_cb_rw; assumption. Qed.

Lemma ly_wr_sub : forall segs m A n k j, wr_at segs m A n -> 0 <= k -> 0 <= j -> k + j <= n ->
  wr_at segs m (A + k) j.
Proof.
  intros segs m A n k j (Ha & Hn & Hw) Hk Hj Hkj. split; [lia|]. split; [lia|].
  intros i Hi. replace (A + k + i) with (A + (k + i)) by lia. apply Hw. lia.
Qed.

Lemma ly_bytes_sub : forall segs m A bs k j, bytes_at segs m A bs -> (k + j <= length bs)%nat ->
  bytes_at segs m (A + Z.of_nat k) (firstn j (skipn k bs)).
Proof.
  intros segs m A bs k j (Ha & Hl & Hb) Hkj.
  assert (L : length (firstn j (skipn k bs)) = j) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite L; lia|]. intros i Hi. rewrite L in Hi.
  replace (A + Z.of_nat k + Z.of_nat i) with (A + Z.of_nat (k + i)) by lia. rewrite Hb by lia.
  rewrite nth_error_firstn by lia. rewrite (proj2 (Nat.ltb_lt i j) Hi). rewrite nth_error_skipn; try (f_equal; lia).
Qed.

Lemma ly_rw_split3 : forall segs m A X (k j : nat), rw_cells segs m A [CB 32 X] -> (k + j <= 32)%nat ->
  rw_cells segs m A [CB k (firstn k X)] /\
  rw_cells segs m (A + Z.of_nat k) [CB j (firstn j (skipn k X))] /\
  rw_cells segs m (A + Z.of_nat k + Z.of_nat j) [CB (32 - k - j) (skipn (k + j) X)].
Proof.
  intros segs m A X k j H Hkj. destruct (ly_rw_cb segs m A 32 X H) as (HL & HB & HW).
  pose proof (bytes_at_bound segs m A X HB) as BB.
  split; [|split].
  - apply ly_rw_cb_eq; [rewrite length_firstn; lia | |].
    + pose proof (ly_bytes_sub segs m A X 0 k HB ltac:(lia)) as S. rewrite Z.add_0_r in S. exact S.
    + pose proof (ly_wr_sub segs m A 32 0 (Z.of_nat k) HW ltac:(lia) ltac:(lia) ltac:(lia)) as S.
      rewrite Z.add_0_r in S. exact S.
  - apply ly_rw_cb_eq; [rewrite length_firstn, length_skipn; lia | |].
    + apply ly_bytes_sub; [exact HB | lia].
    + apply (ly_wr_sub segs m A 32); [exact HW | lia | lia | lia].
  - apply ly_rw_cb_eq; [rewrite length_skipn; lia | |].
    + pose proof (ly_bytes_sub segs m A X (k + j) (32 - k - j) HB ltac:(lia)) as S.
      rewrite firstn_all2 in S by (rewrite length_skipn; lia).
      replace (A + Z.of_nat (k + j)) with (A + Z.of_nat k + Z.of_nat j) in S by lia. exact S.
    + replace (A + Z.of_nat k + Z.of_nat j) with (A + Z.of_nat (k + j)) by lia.
      apply (ly_wr_sub segs m A 32); [exact HW | lia | lia | lia].
Qed.

Lemma ly_rw_join3 : forall segs m A B C k j pre mid post,
  rw_cells segs m A [CB k pre] -> rw_cells segs m B [CB j mid] -> rw_cells segs m C [CB (32 - k - j) post] ->
  B = A + Z.of_nat k -> C = A + Z.of_nat k + Z.of_nat j -> (k + j <= 32)%nat ->
  rw_cells segs m A [CB 32 (pre ++ mid ++ post)].
Proof.
  intros segs m A B C k j pre mid post H1 H2 H3 -> -> Hkj.
  destruct (ly_rw_cb _ _ _ _ _ H1) as (L1 & B1 & W1).
  destruct (ly_rw_cb _ _ _ _ _ H2) as (L2 & B2 & W2).
  destruct (ly_rw_cb _ _ _ _ _ H3) as (L3 & B3 & W3).
  pose proof (bytes_at_bound _ _ _ _ B1). pose proof (bytes_at_bound _ _ _ _ B3).
  apply ly_rw_cb_eq; [rewrite !length_app; lia | |].
  - apply bytes_at_app. split; [exact B1|]. apply bytes_at_app. rewrite L1. split; [exact B2|].
    rewrite L2. exact B3.
  - destruct W1 as (Wa & Wn & Wi1). destruct W2 as (_ & _ & Wi2). destruct W3 as (_ & _ & Wi3).
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.ltb_spec i (Z.of_nat k)); [apply Wi1; lia|].
    destruct (Z.ltb_spec i (Z.of_nat k + Z.of_nat j)).
    + replace (A + i) with (A + Z.of_nat k + (i - Z.of_nat k)) by lia. apply Wi2. lia.
    + replace (A + i) with (A + Z.of_nat k + Z.of_nat j + (i - Z.of_nat k - Z.of_nat j)) by lia. apply Wi3. lia.
Qed.

Lemma ly_put_eq : forall X ao gb, (Z.to_nat ao + length gb <= 32)%nat -> 0 <= ao ->
  firstn (Z.to_nat ao) X ++ gb ++ skipn (Z.to_nat ao + length gb) X = ly_put X ao gb.
Proof. intros. reflexivity. Qed.

Lemma rc_u8_gtu : forall bs i z, 0 <= z < 2^64 ->
  bv_ltu (Z_to_bv 64 z) (zxb (nth i bs (Z_to_bv 8 0))) = (z <? rc_u8 bs i).
Proof. intros bs i z Hz. unfold zxb. pose proof (rc_u8_range bs i). unfold rc_u8 in *. apply rc_ltu; lia. Qed.

Lemma rc_zxb_lit : forall bs i z, rc_u8 bs i = z -> zxb (nth i bs (Z_to_bv 8 0)) = Z_to_bv 64 z.
Proof. intros bs i z H. unfold zxb. unfold rc_u8 in H. rewrite H. reflexivity. Qed.

Lemma ly_le_val : forall bs, ly_le bs = le_val (map bv_unsigned bs).
Proof. induction bs as [|b bs IH]; cbn [ly_le le_val map]; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma ly_le_range : forall bs, 0 <= ly_le bs < 256 ^ Z.of_nat (length bs).
Proof.
  intros bs. rewrite ly_le_val. pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as R.
  rewrite length_map in R. exact R.
Qed.

Lemma ly_ld8 : forall (fr L : list byte), length fr = 24%nat -> L = firstn 8 (skipn 8 fr) ->
  bv_extract 0 64 (le_bytes_to_word L) = Z_to_bv 64 (ly_tm fr).
Proof.
  intros fr L Hl ->. apply bv_eq. rewrite load8_le_val by (rewrite length_firstn, length_skipn; lia).
  unfold ly_tm. rewrite <- ly_le_val. pose proof (ly_le_range (firstn 8 (skipn 8 fr))) as R.
  rewrite length_firstn, length_skipn, Hl in R. change (256 ^ Z.of_nat (Nat.min 8 (24 - 8))) with (2^64) in R.
  symmetry. apply unsigned_lit. lia.
Qed.

Lemma ly_rd8 : forall segs m A (fr : list byte), bytes_at segs m A fr -> length fr = 24%nat ->
  exists L, L = firstn 8 (skipn 8 fr) /\ ov_read_bytes segs m (wa (A + 8)) 8 = Some L.
Proof.
  intros segs m A fr HB Hl. eexists. split; [reflexivity|].
  rewrite (bytes_at_read segs m A fr 8 8 HB) by lia. reflexivity.
Qed.

Definition ly_dp (j : nat) : list byte := firstn (2 * j) ly_desc ++ repeat (Z_to_bv 8 0) (32 - 2 * j).

Lemma ly_dp_0 : ly_dp 0 = ly_zero.
Proof. reflexivity. Qed.

Lemma ly_dp_16 : ly_dp 16 = ly_desc.
Proof. reflexivity. Qed.

Lemma ly_dp_len : forall j, (j <= 16)%nat -> length (ly_dp j) = 32%nat.
Proof.
  intros j Hj. do 17 (destruct j as [|j]; [reflexivity|]). lia.
Qed.

Lemma ly_dp_step : forall j, (j < 16)%nat ->
  upd_bytes (upd_bytes (ly_dp j) (2 * j) [Z_to_bv 8 0]) (2 * j + 1) [Z_to_bv 8 122] = ly_dp (S j).
Proof.
  intros j Hj. do 16 (destruct j as [|j]; [vm_compute; reflexivity|]). lia.
Qed.

Definition ly_hide (P : Prop) : Prop := P.

Lemma ly_hide_in : forall P : Prop, P -> ly_hide P.
Proof. intros P H. exact H. Qed.

Lemma ly_eqb_near : forall x y, 0 <= x -> 0 <= y -> x < y + 2^64 -> y < x + 2^64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = Z.eqb x y.
Proof.
  intros x y Hx Hy H1 H2. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec x y) as [E|E]; [subst; apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E'. apply E.
  change (2^64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia.
Qed.

Lemma ly_eqb_close : forall x y, x < y + 2^64 -> y < x + 2^64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = Z.eqb x y.
Proof.
  intros x y H1 H2. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec x y) as [E|E]; [subst; apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E'. apply E.
  change (2^64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia.
Qed.

Lemma ly_wr_not_ro : forall segs m o n J k, wr_at segs m o n -> mem_inv segs m -> 0 < n -> 0 < k ->
  (forall i, 0 <= i < k -> ro_addr segs (wa (J + i)) = true) -> 0 <= J -> J + k <= 2^64 ->
  o + n <= J \/ J + k <= o.
Proof.
  intros segs m o n J k (Ho & Hon & HW) MI Hn Hk HR HJ HJk.
  destruct (Z.le_gt_cases (o + n) J) as [L1|L1]; [left; lia|].
  destruct (Z.le_gt_cases (J + k) o) as [L2|L2]; [right; lia|].
  exfalso. set (x := Z.max o J).
  assert (W : wview segs m (wa (o + (x - o))) <> None) by (apply HW; lia).
  assert (R : ro_addr segs (wa (J + (x - J))) = true) by (apply HR; lia).
  replace (o + (x - o)) with x in W by lia. replace (J + (x - J)) with x in R by lia.
  destruct (m (wa x)) eqn:E.
  - pose proof (MI _ _ E) as F. congruence.
  - pose proof (wview_not_ro segs m (wa x) W E) as F. congruence.
Qed.

Lemma ly_ro_range : forall segs J k,
  forallb (fun i => ro_addr segs (wa (J + Z.of_nat i))) (seq 0 k) = true ->
  forall i, 0 <= i < Z.of_nat k -> ro_addr segs (wa (J + i)) = true.
Proof.
  intros segs J k H i Hi. rewrite forallb_forall in H.
  replace i with (Z.of_nat (Z.to_nat i)) by lia. apply (H (Z.to_nat i)). apply in_seq. lia.
Qed.

Lemma ly_ltu_negr : forall x y, 0 <= x -> -2^64 < y < 0 -> x < 2^64 + y ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = true.
Proof.
  intros x y Hx Hy Hxy. unfold bv_ltu. rewrite (unsigned_lit x) by lia. rewrite unsigned_lit_wrap.
  apply Z.ltb_lt. change (2^64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia.
Qed.
