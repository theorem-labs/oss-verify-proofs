From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcPorts RcPortsLib RcFin RcFinLib
  RcLay RcEmit.
Import ListNotations.
Open Scope Z_scope.

Definition em_at := bytes_at.
Definition em_stk := stk.
Definition em_mi := mem_inv.

Lemma em_unsigned_neg : forall x, -2^63 <= x < 0 -> bv_unsigned (Z_to_bv 64 x) = x + 2^64.
Proof.
  intros x Hx. rewrite unsigned_lit_wrap.
  rewrite <- (Z.mod_add x 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma em_wok_ltu : forall n, -2^31 <= n < 2^31 ->
  bv_ltu (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 n) + -41))) (Z_to_bv 64 (-39)) =
    negb ((2 <=? n) && (n <=? 40)).
Proof.
  intros n Hn.
  assert (W : bv_swrap 32 (bv_unsigned (Z_to_bv 64 n) + -41) =
              if n - 41 <? -2^31 then n - 41 + 2^32 else n - 41).
  { rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31).
    change (bv_modulus 32) with (2^32).
    destruct (Z.ltb_spec (n - 41) (-2^31)); Z.div_mod_to_equations; lia. }
  rewrite W. unfold bv_ltu. rewrite !unsigned_lit_wrap.
  destruct (Z.ltb_spec (n - 41) (-2^31)); destruct (Z.leb_spec 2 n); destruct (Z.leb_spec n 40);
    cbn [andb negb]; first [apply Z.ltb_ge | apply Z.ltb_lt]; Z.div_mod_to_equations; lia.
Qed.

Lemma em_odd : forall n, -2^63 <= n < 2^63 ->
  bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 n)) 1)) (Z_to_bv 64 0) = Z.even n.
Proof.
  intros n Hn. rewrite rc_land1. rewrite unsigned_lit_wrap.
  assert (E : (n mod 2^64) mod 2 = n mod 2) by (Z.div_mod_to_equations; lia).
  rewrite E. pose proof (Z.mod_pos_bound n 2 ltac:(lia)) as M.
  rewrite rc_eqb by lia. rewrite Zeven_mod. reflexivity.
Qed.

Lemma em_eqb0 : forall x, -2^63 <= x < 2^63 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = (x =? 0).
Proof.
  intros x Hx. unfold bv_eqb. rewrite unsigned_lit_wrap. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  destruct (Z.eqb_spec x 0) as [->|E]; [reflexivity|]. apply Z.eqb_neq. intros H.
  apply E. Z.div_mod_to_equations. lia.
Qed.

Lemma em_hid_range : forall mb, -2^31 <= em_hid mb < 2^31.
Proof. intros mb. unfold em_hid, rc_u8. pose proof (rc_s32of_range (bv_unsigned (nth 56 mb (Z_to_bv 8 0)))
  (bv_unsigned (nth 57 mb (Z_to_bv 8 0))) (bv_unsigned (nth 58 mb (Z_to_bv 8 0))) (bv_unsigned (nth 59 mb (Z_to_bv 8 0)))
  ltac:(apply byte_range) ltac:(apply byte_range) ltac:(apply byte_range) ltac:(apply byte_range)). lia. Qed.

Lemma em_len_word : forall n, em_wok n = true ->
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 n) * 36 + 52) = Z_to_bv 64 (52 + 36 * n).
Proof.
  intros n H. unfold em_wok in H. apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. rewrite unsigned_lit by lia. f_equal. lia.
Qed.

Lemma em_wok_range : forall n, em_wok n = true -> 2 <= n <= 40 /\ Z.even n = true.
Proof.
  intros n H. unfold em_wok in H. apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. auto.
Qed.

Lemma em_le1 : forall v : word, le1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof. reflexivity. Qed.

Lemma em_byte_lit : forall z, 0 <= z < 2^64 -> Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z)) = Z_to_bv 8 z.
Proof. intros z Hz. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma em_byte_zxb : forall b : byte, Z_to_bv 8 (bv_unsigned (zxb b)) = b.
Proof. intros b. rewrite rc_zxb_u. apply rc_byte_lit. Qed.

Lemma em_c16_lo : forall x : word, Z_to_bv 8 (bv_unsigned x) = Z_to_bv 8 ((bv_unsigned x mod 65536) mod 256).
Proof.
  intros x. apply Z_to_bv8_mod. change (2^8) with 256. rewrite !Z.mod_mod by lia.
  Z.div_mod_to_equations. lia.
Qed.

Lemma em_c16_hi : forall x : word,
  Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned x) 8))) = Z_to_bv 8 ((bv_unsigned x mod 65536) / 256).
Proof.
  intros x. pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R.
  rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
  rewrite unsigned_lit by (split; [apply Z.div_pos; lia | apply (Z.le_lt_trans _ (bv_unsigned x)); [apply Z.div_le_upper_bound; lia | lia]]).
  apply Z_to_bv8_mod. change (2^8) with 256. Z.div_mod_to_equations. lia.
Qed.

Lemma em_rw_split : forall segs m A n bs (k : nat), rw_cells segs m A [CB n bs] -> (k <= n)%nat ->
  rw_cells segs m A [CB k (firstn k bs)] /\ rw_cells segs m (A + Z.of_nat k) [CB (n - k) (skipn k bs)].
Proof.
  intros segs m A n bs k [[Hwf HB] HW] Hk. cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize] in *.
  destruct Hwf as [Hl _]. rewrite app_nil_r in HB. rewrite Nat.add_0_r in HW.
  rewrite <- (firstn_skipn k bs) in HB. apply bytes_at_app in HB. destruct HB as [B1 B2].
  rewrite length_firstn in B2. replace (Nat.min k (length bs)) with k in B2 by lia.
  split; (split; [split|]).
  - cbn [cells_wf cell_wf]. rewrite length_firstn. split; [lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B1.
  - cbn [cells_size csize]. rewrite Nat.add_0_r.
    destruct HW as (H1 & H2 & H). split; [lia|]. split; [lia|]. intros i Hi. apply H. lia.
  - cbn [cells_wf cell_wf]. rewrite length_skipn. split; [lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B2.
  - cbn [cells_size csize]. rewrite Nat.add_0_r.
    destruct HW as (H1 & H2 & H). split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat k + i) with (A + (Z.of_nat k + i)) by lia. apply H. lia.
Qed.

Lemma em_rw_bytes : forall segs m A n bs, rw_cells segs m A [CB n bs] ->
  length bs = n /\ bytes_at segs m A bs /\ wr_at segs m A (Z.of_nat n).
Proof.
  intros segs m A n bs [[Hwf HB] HW]. cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize] in *.
  rewrite app_nil_r in HB. rewrite Nat.add_0_r in HW. destruct Hwf as [Hl _]. auto.
Qed.

Lemma em_rw_of : forall segs m A bs, bytes_at segs m A bs -> wr_at segs m A (Z.of_nat (length bs)) ->
  rw_cells segs m A [CB (length bs) bs].
Proof.
  intros segs m A bs HB HW. split; [split|].
  - cbn [cells_wf cell_wf]. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact HW.
Qed.

Lemma em_rw_cells_bytes : forall segs m A cs, rw_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof. intros segs m A cs [[_ HB] _]. exact HB. Qed.

Lemma em_firstn_repeat : forall (x : byte) n k, (k <= n)%nat -> firstn k (repeat x n) = repeat x k.
Proof.
  intros x n. induction n as [|n IH]; intros k Hk; [destruct k; [reflexivity | lia]|].
  destruct k as [|k]; [reflexivity|]. cbn [repeat firstn]. f_equal. apply IH. lia.
Qed.

Lemma em_skipn_repeat : forall (x : byte) n k, skipn k (repeat x n) = repeat x (n - k).
Proof.
  intros x n. induction n as [|n IH]; intros k; [destruct k; reflexivity|].
  destruct k as [|k]; [reflexivity|]. cbn [repeat skipn]. rewrite IH. reflexivity.
Qed.

Lemma em_C8_CB : forall segs m A (v : word) cs, rw_cells segs m A (C8 v :: cs) -> rw_cells segs m A (CB 8 (le8 v) :: cs).
Proof.
  intros segs m A v cs [[Hwf HB] HW]. split; [split|].
  - cbn [cells_wf cell_wf] in *. split; [apply length_le8 | tauto].
  - exact HB.
  - exact HW.
Qed.

Lemma em_obj : forall segs m0 m1 Lo S o L A bs n,
  munch [(Lo, S); (o, o + L)] m0 m1 -> bytes_at segs m0 A bs -> Z.of_nat (length bs) = n ->
  (S <= A \/ A + n <= Lo) -> (o + L <= A \/ A + n <= o) -> bytes_at segs m1 A bs.
Proof.
  intros segs m0 m1 Lo S o L A bs n MU HB Hl D1 D2.
  apply (bytes_at_transport segs _ m0 m1 A bs HB MU). rewrite Hl. cbn [disjoint_from]. lia.
Qed.

Lemma em_obj0 : forall segs m0 m1 Lo S A bs n,
  munch [(Lo, S)] m0 m1 -> bytes_at segs m0 A bs -> Z.of_nat (length bs) = n ->
  (S <= A \/ A + n <= Lo) -> bytes_at segs m1 A bs.
Proof.
  intros segs m0 m1 Lo S A bs n MU HB Hl D1.
  apply (bytes_at_transport segs _ m0 m1 A bs HB MU). rewrite Hl. cbn [disjoint_from]. lia.
Qed.

Lemma em_rw_rep : forall segs m A (z : byte) n (k : nat), rw_cells segs m A [CB n (repeat z n)] -> (k <= n)%nat ->
  rw_cells segs m A [CB k (repeat z k)] /\ rw_cells segs m (A + Z.of_nat k) [CB (n - k) (repeat z (n - k))].
Proof.
  intros segs m A z n k H Hk. destruct (em_rw_split segs m A n _ k H Hk) as [H1 H2].
  rewrite em_firstn_repeat in H1 by lia. rewrite em_skipn_repeat in H2. split; assumption.
Qed.

Lemma em_split_frame : forall segs m o len (z : byte),
  rw_cells segs m o [CB (Z.to_nat len) (repeat z (Z.to_nat len))] -> 52 <= len ->
  rw_cells segs m o [CB 6 (repeat z 6)] /\ rw_cells segs m (o + 6) [CB 6 (repeat z 6)] /\
  rw_cells segs m (o + 12) [CB 6 (repeat z 6)] /\ rw_cells segs m (o + 18) [CB 32 (repeat z 32)] /\
  rw_cells segs m (o + 50) [CB (Z.to_nat (len - 52)) (repeat z (Z.to_nat (len - 52)))] /\
  rw_cells segs m (o + len + -2) [CB 2 (repeat z 2)].
Proof.
  intros segs m o len z H Hl.
  destruct (em_rw_rep segs m o z _ 6 H ltac:(lia)) as [H1 R1].
  destruct (em_rw_rep segs m _ z _ 6 R1 ltac:(lia)) as [H2 R2].
  destruct (em_rw_rep segs m _ z _ 6 R2 ltac:(lia)) as [H3 R3].
  destruct (em_rw_rep segs m _ z _ 32 R3 ltac:(lia)) as [H4 R4].
  destruct (em_rw_rep segs m _ z _ (Z.to_nat (len - 52)) R4 ltac:(lia)) as [H5 R5].
  replace (o + Z.of_nat 6) with (o + 6) in H2 by lia.
  replace (o + Z.of_nat 6 + Z.of_nat 6) with (o + 12) in H3 by lia.
  replace (o + Z.of_nat 6 + Z.of_nat 6 + Z.of_nat 6) with (o + 18) in H4 by lia.
  replace (o + Z.of_nat 6 + Z.of_nat 6 + Z.of_nat 6 + Z.of_nat 32) with (o + 50) in H5 by lia.
  replace (o + Z.of_nat 6 + Z.of_nat 6 + Z.of_nat 6 + Z.of_nat 32 + Z.of_nat (Z.to_nat (len - 52)))
    with (o + len + -2) in R5 by lia.
  replace (Z.to_nat len - 6 - 6 - 6 - 32 - Z.to_nat (len - 52))%nat with 2%nat in R5 by lia.
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 R5))))).
Qed.

Lemma em_fr_at : forall segs m o len (d6 s6 h6 blk zs t2 : list byte),
  rw_cells segs m o [CB 6 d6] -> rw_cells segs m (o + 6) [CB 6 s6] -> bytes_at segs m (o + 12) h6 ->
  rw_cells segs m (o + 18) [CB 32 blk] -> rw_cells segs m (o + 50) [CB (Z.to_nat (len - 52)) zs] ->
  bytes_at segs m (o + len + -2) t2 -> length h6 = 6%nat -> 52 <= len ->
  bytes_at segs m o (d6 ++ s6 ++ h6 ++ blk ++ zs ++ t2).
Proof.
  intros segs m o len d6 s6 h6 blk zs t2 P1 P2 B3 P4 P5 B6 L3 Hl.
  apply em_rw_bytes in P1 as (L1 & B1 & _). apply em_rw_bytes in P2 as (L2 & B2 & _).
  apply em_rw_bytes in P4 as (L4 & B4 & _). apply em_rw_bytes in P5 as (L5 & B5 & _).
  apply bytes_at_app. split; [exact B1|]. rewrite L1.
  apply bytes_at_app. split; [exact B2|]. rewrite L2.
  apply bytes_at_app. split; [replace (o + Z.of_nat 6 + Z.of_nat 6) with (o + 12) by lia; exact B3|]. rewrite L3.
  apply bytes_at_app. split; [replace (o + Z.of_nat 6 + Z.of_nat 6 + Z.of_nat 6) with (o + 18) by lia; exact B4|].
  rewrite L4.
  apply bytes_at_app. split.
  - replace (o + Z.of_nat 6 + Z.of_nat 6 + Z.of_nat 6 + Z.of_nat 32) with (o + 50) by lia. exact B5.
  - rewrite L5. replace (o + Z.of_nat 6 + Z.of_nat 6 + Z.of_nat 6 + Z.of_nat 32 + Z.of_nat (Z.to_nat (len - 52)))
      with (o + len + -2) by lia. exact B6.
Qed.

Lemma em_fr_bytes : forall segs m o len (d6 s6 blk : list byte) c16 (t0 t1 : byte),
  rw_cells segs m o [CB 6 d6] -> rw_cells segs m (o + 6) [CB 6 s6] ->
  rw_cells segs m (o + 12)
    [CB 6 [Z_to_bv 8 136; Z_to_bv 8 25; Z_to_bv 8 (c16 mod 256); Z_to_bv 8 (c16 / 256); t0; t1]] ->
  rw_cells segs m (o + 18) [CB 32 blk] ->
  rw_cells segs m (o + 50) [CB (Z.to_nat (len - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (len - 52)))] ->
  bytes_at segs m (o + len + -2) [Z_to_bv 8 194; Z_to_bv 8 234] -> 52 <= len ->
  bytes_at segs m o (em_fr d6 s6 c16 t0 t1 blk len).
Proof.
  intros segs m o len d6 s6 blk c16 t0 t1 P1 P2 P3 P4 P5 B6 Hl.
  apply em_rw_bytes in P3 as (_ & B3 & _).
  unfold em_fr, em_hdr. rewrite <- !app_assoc.
  exact (em_fr_at segs m o len d6 s6 _ blk _ _ P1 P2 B3 P4 P5 B6 eq_refl Hl).
Qed.

Lemma em_merge : forall segs m A cs, rw_cells segs m A cs -> rw_cells segs m A [CB (cells_size cs) (cells_bytes cs)].
Proof.
  intros segs m A cs H. pose proof (rw_cells_merge segs m A [] cs [] ) as M. rewrite app_nil_r in M.
  cbn [app] in M. apply M. exact H.
Qed.

Lemma em_lw_hid : forall mb L,
  L = [nth 56 mb (Z_to_bv 8 0); nth 57 mb (Z_to_bv 8 0); nth 58 mb (Z_to_bv 8 0); nth 59 mb (Z_to_bv 8 0)] ->
  sext 64 (bv_extract 0 32 (le_bytes_to_word L)) = Z_to_bv 64 (em_hid mb).
Proof. intros mb L ->. apply rc_lw4. Qed.

Lemma em_E_true : forall L G n h, (L = 2 \/ em_wok n = true) -> (G <> 1 \/ h <> 0) -> em_E L G n h = true.
Proof.
  intros L G n h H1 H2. unfold em_E. apply andb_true_iff. split.
  - destruct H1 as [H|H]; rewrite H; [reflexivity | apply orb_true_r].
  - apply orb_true_iff. destruct H2 as [H|H]; [left|right]; apply negb_true_iff, Z.eqb_neq; exact H.
Qed.

Lemma em_E_false_w : forall L G n h, L <> 2 -> em_wok n = false -> em_E L G n h = false.
Proof.
  intros L G n h H1 H2. unfold em_E. rewrite H2. replace (L =? 2) with false by (symmetry; apply Z.eqb_neq; exact H1).
  reflexivity.
Qed.

Lemma em_E_false_g : forall L G n h, G = 1 -> h = 0 -> em_E L G n h = false.
Proof. intros L G n h -> ->. unfold em_E. cbn [Z.eqb negb orb]. apply andb_false_r. Qed.

Lemma em_E_wok : forall L G n h, em_E L G n h = true -> L <> 2 -> em_wok n = true.
Proof.
  intros L G n h H HL. unfold em_E in H. apply andb_true_iff in H as [H _].
  replace (L =? 2) with false in H by (symmetry; apply Z.eqb_neq; exact HL). exact H.
Qed.

Lemma em_len_rng : forall L G n h, em_E L G n h = true -> 124 <= em_len L n <= 1492.
Proof.
  intros L G n h H. unfold em_len. destruct (Z.eqb_spec L 2) as [E|E]; [lia|].
  destruct (em_wok_range n (em_E_wok L G n h H E)) as [R _]. lia.
Qed.

Lemma em_byte_m22 : Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-22))) = Z_to_bv 8 234.
Proof. apply Z_to_bv8_mod. vm_compute. reflexivity. Qed.

Lemma em_fin_sub : forall c ro rl o, c <= 2 -> 0 <= ro -> (c = 2 -> 2 <= rl /\ ro + rl <= 31) ->
  sub_fp (fin_w c ro rl o) [(o + 18, o + 50)].
Proof.
  intros c ro rl o Hc Hro H2 x Hx. cbn [outside] in Hx. unfold fin_w.
  destruct (Z.eqb_spec c 2) as [E2|E2].
  - destruct (H2 E2). cbn [outside]. lia.
  - destruct (Z.eqb_spec c 1); cbn [outside]; lia.
Qed.

Lemma em_fin_nil : forall ro rl o, fin_w 0 ro rl o = [].
Proof. reflexivity. Qed.

Lemma em_munch_add : forall a b m m', munch [a] m m' -> munch [a; b] m m'.
Proof.
  intros [l h] [l2 h2] m m' H. apply (munch_weaken [(l, h)]); [|exact H].
  intros x Hx. cbn [outside] in *. tauto.
Qed.

Lemma em_dj_sub : forall a b c d a' b' c' d', ly_dj a b c d -> a <= a' -> b' <= b -> c <= c' -> d' <= d ->
  ly_dj a' b' c' d'.
Proof. unfold ly_dj. intros. lia. Qed.

Lemma em_cpy_dj : forall o L A d, ly_dj o (o + L) d (d + 6) -> o <= A -> A + 6 <= o + L -> d + 6 <= A \/ A + 6 <= d.
Proof. unfold ly_dj. intros. lia. Qed.

Lemma em_df1 : forall o L A n, ly_dj o (o + L) A (A + n) -> disjoint_from [(o, o + L)] A n.
Proof. unfold ly_dj. intros. cbn [disjoint_from]. split; [lia | exact I]. Qed.

Lemma em_mod16 : forall S k, S mod 16 = 0 -> k mod 16 = 0 -> (S + k) mod 16 = 0.
Proof. intros. Z.div_mod_to_equations. lia. Qed.

Lemma em_dj_raw : forall a b c d a' b' c' d', ly_dj a b c d -> a <= a' -> b' <= b -> c <= c' -> d' <= d ->
  b' <= c' \/ d' <= a'.
Proof. unfold ly_dj. intros. lia. Qed.

Lemma em_ltu_lit : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma em_ltu_neg_l : forall c x, -2^64 <= c < 0 -> 0 <= x < 2^64 ->
  bv_ltu (Z_to_bv 64 c) (Z_to_bv 64 x) = (c + 2^64 <? x).
Proof.
  intros c x Hc Hx. unfold bv_ltu. rewrite (unsigned_lit x) by lia. rewrite unsigned_lit_wrap.
  replace (c mod 2^64) with (c + 2^64); [reflexivity|].
  change (2^64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia.
Qed.

Lemma em_ltu_neg_r : forall x c, 0 <= x < 2^64 -> -2^64 <= c < 0 ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 c) = (x <? c + 2^64).
Proof.
  intros x c Hx Hc. unfold bv_ltu. rewrite (unsigned_lit x) by lia. rewrite unsigned_lit_wrap.
  replace (c mod 2^64) with (c + 2^64); [reflexivity|].
  change (2^64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia.
Qed.

Lemma em_merge3 : forall segs m A j (a b : word) cs, rw_cells segs m A (CB 8 j :: C8 a :: C8 b :: cs) ->
  exists j', rw_cells segs m A (CB 24 j' :: cs).
Proof.
  intros segs m A j a b cs H. pose proof (rw_cells_merge segs m A [] [CB 8 j; C8 a; C8 b] cs H) as M.
  cbn [app cells_size csize Nat.add] in M. eexists. exact M.
Qed.

Lemma em_fin_sub2 : forall c ro rl o w, c <= 2 -> 0 <= ro -> (c = 2 -> 2 <= rl /\ ro + rl <= 31) ->
  sub_fp (w :: fin_w c ro rl o) [w; (o + 18, o + 50)].
Proof.
  intros c ro rl o [wl wh] Hc Hro H2 x Hx. cbn [outside] in Hx |- *. destruct Hx as [H1 [H3 _]].
  split; [exact H1|]. apply (em_fin_sub c ro rl o Hc Hro H2 x). cbn [outside]. split; [exact H3 | exact I].
Qed.

(* em_lia: lia over the plain arithmetic hypotheses and the local hypotheses built from them with and, or and
   not; it drops every other proposition (section hypotheses that are implications or opaque facts), so a
   context full of conditional premises does not make lia split cases. *)
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import LiaTwx2.
#[global] Set Default Proof Mode "Classic".

Ltac2 rec em_plainish (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      if Constr.equal h 'or then (if em_plainish (Array.get args 0) then em_plainish (Array.get args 1) else false)
      else if Constr.equal h 'and then (if em_plainish (Array.get args 0) then em_plainish (Array.get args 1) else false)
      else if Constr.equal h 'not then em_plainish (Array.get args 0)
      else zt_plain_arith t
  | _ => zt_plain_arith t
  end.

Ltac2 em_prune0 () : unit :=
  let ids := List.map_filter (fun h =>
    let (id, body, ty) := h in
    match body with
    | Some _ => None
    | None =>
        if zt_plain_arith ty then None
        else if zt_is_prop ty then
          (if zt_is_local id then (if em_plainish ty then None else Some id) else Some id)
        else None
    end) (Control.hyps ()) in
  match ids with [] => () | _ :: _ => Std.clear ids end.

Ltac em_prune := ltac2:(Control.enter em_prune0).
Ltac em_lia := em_prune; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                               | Zify.zify; xlia zchecker ].
