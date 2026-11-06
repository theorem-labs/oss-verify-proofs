From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcParse RcParseLib RcReply.
Import ListNotations.
Open Scope Z_scope.

Lemma rc_map_seq : forall g, map (cp_b g) (seq 0 (length g)) = g.
Proof.
  intros g. apply nth_ext with (d := cp_z) (d' := cp_z).
  - rewrite map_length, seq_length. reflexivity.
  - intros i Hi. rewrite map_length, seq_length in Hi.
    rewrite (nth_indep _ cp_z (cp_b g 0)) by (rewrite map_length, seq_length; lia).
    rewrite map_nth, seq_nth by lia. reflexivity.
Qed.

Lemma rc_zb0 : forall x, 0 <= x < 2^64 ->
  bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 x)) 255)) (Z_to_bv 64 0) = (x mod 256 =? 0).
Proof.
  intros x Hx. rewrite unsigned_lit by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  change (2^8) with 256. pose proof (Z.mod_pos_bound x 256 ltac:(lia)). apply rc_eqb64; lia.
Qed.

Lemma rc_z127 : forall x, 0 <= x < 2^64 ->
  bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 x)) 127)) (Z_to_bv 64 0) = (x mod 128 =? 0).
Proof.
  intros x Hx. rewrite unsigned_lit by lia. change 127 with (Z.ones 7). rewrite Z.land_ones by lia.
  change (2^7) with 128. pose proof (Z.mod_pos_bound x 128 ltac:(lia)). apply rc_eqb64; lia.
Qed.

Lemma rc_lhu_pair : forall lo hi : byte,
  zext 64 (bv_extract 0 16 (le_bytes_to_word [lo; hi])) = Z_to_bv 64 (bv_unsigned hi * 256 + bv_unsigned lo).
Proof.
  intros lo hi. pose proof (byte_range lo). pose proof (byte_range hi).
  rewrite zext_small. f_equal. rewrite extract_low_mod by lia. unfold le_bytes_to_word.
  cbn [bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r. rewrite Z_to_bv_unsigned.
  assert (E : Z.lor (bv_unsigned lo) (Z.shiftl (bv_unsigned hi) 8) = bv_unsigned lo + 256 * bv_unsigned hi)
    by (apply lor_shiftl8_add; lia).
  rewrite E. change (Z.of_N 16) with 16. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  rewrite (Z.mod_small _ (2^64)) by lia. rewrite Z.mod_small by (change (2^16) with 65536; lia). lia.
Qed.

Lemma rc_srange : forall s, 0 <= s < 256 ->
  bv_ltu (Z_to_bv 64 (s + -24)) (Z_to_bv 64 (-10)) = negb ((14 <=? s) && (s <=? 23)).
Proof.
  intros s Hs. unfold bv_ltu. rewrite !unsigned_lit_wrap.
  change (-10 mod 2^64) with 18446744073709551606.
  destruct (Z.ltb_spec s 24) as [L|L].
  - replace ((s + -24) mod 2^64) with (s + -24 + 2^64)
      by (rewrite <- (Z.mod_add (s + -24) 1 (2^64)) by lia; rewrite Z.mod_small; lia).
    destruct (Z.leb_spec 14 s); cbn [andb negb].
    + replace (s <=? 23) with true by (symmetry; apply Z.leb_le; lia). apply Z.ltb_ge. lia.
    + apply Z.ltb_lt. lia.
  - rewrite Z.mod_small by lia. replace (s <=? 23) with false by (symmetry; apply Z.leb_gt; lia).
    rewrite andb_false_r. apply Z.ltb_lt. lia.
Qed.

Lemma rc_uzxb : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof. intros b. pose proof (byte_range b). unfold zxb. apply unsigned_lit. lia. Qed.

Lemma rc_b36_split : forall B : list byte, length B = 36%nat ->
  B = firstn 28 B ++ [nth 28 B cp_z; nth 29 B cp_z] ++ skipn 30 B.
Proof.
  intros B H. do 36 (destruct B as [|? B]; [discriminate|]). destruct B; [reflexivity|discriminate].
Qed.

Lemma rc_len_rec : forall g, length g = 50%nat -> 14 <= ir_s g <= 23 ->
  length (ir_rec g) = Z.to_nat (ir_s g - 8).
Proof.
  intros g Hg Hs. unfold ir_rec. rewrite firstn_length_le; [reflexivity|]. rewrite skipn_length, Hg. lia.
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma rc_ro_of_bytes : forall m A g, bytes_at segs m A g ->
  ro_cells segs m A (map C1 (map (cp_b g) (seq 0 (length g)))).
Proof.
  intros m A g H. rewrite rc_map_seq. split; [apply rc_c1_wf|]. rewrite rc_c1_bytes. exact H.
Qed.

Lemma rc_bytes_skip : forall m A bs k, bytes_at segs m A bs -> (k <= length bs)%nat ->
  bytes_at segs m (A + Z.of_nat k) (skipn k bs).
Proof.
  intros m A bs k H L. rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H.
  rewrite firstn_length_le in H by lia. exact (proj2 H).
Qed.

Lemma rc_bytes_first : forall m A bs k, bytes_at segs m A bs -> bytes_at segs m A (firstn k bs).
Proof.
  intros m A bs k H. rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

Lemma rc_rd_of_bytes : forall m f g n, length g = 50%nat -> (50 <= n -> bytes_at segs m f g) ->
  forall i, In i (cp_rd n g) -> mrd segs m (wa (f + Z.of_nat i)) = nth_error g i.
Proof.
  intros m f g n Lg H i Hi. pose proof (cp_rd_lt39 n g i Hi) as Li.
  destruct (Z.leb_spec 50 n) as [Hn|Hn].
  - destruct (H Hn) as (_ & _ & R). apply R. lia.
  - unfold cp_rd in Hi. rewrite (proj2 (Z.leb_gt 50 n) Hn) in Hi. destruct Hi.
Qed.

Lemma rc_stk_after : forall W m m' lo hi,
  stk segs m lo hi -> munch W m m' -> wmono segs m m' ->
  (forall x, lo <= x < hi -> outside W x \/ exists b, mrd segs m' (wa x) = Some b) -> stk segs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) MU WM HX. split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as [Hw [b Hb]]. split; [apply WM; exact Hw|].
  destruct (HX a Ha) as [Ho|Hs]; [|exact Hs].
  exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

Lemma rc_rw_mrd : forall m a n bs x, rw_cells segs m a [CB n bs] -> a <= x < a + Z.of_nat n ->
  exists b, mrd segs m (wa x) = Some b.
Proof.
  intros m a n bs x [[Wf (Ha & Hl & Hr)] _] Hx. cbn in Wf. destruct Wf as [Wf _].
  cbn [cells_bytes cbytes] in Hl, Hr. rewrite app_nil_r in Hl, Hr.
  assert (Hi : (Z.to_nat (x - a) < length bs)%nat) by lia.
  pose proof (Hr (Z.to_nat (x - a)) Hi) as R. rewrite Z2Nat.id in R by lia.
  replace (a + (x - a)) with x in R by lia. rewrite R.
  destruct (nth_error bs (Z.to_nat (x - a))) eqn:E; [eexists; reflexivity|].
  apply nth_error_None in E. lia.
Qed.

Lemma rc_stk_mrd : forall m lo hi x, stk segs m lo hi -> lo <= x < hi -> exists b, mrd segs m (wa x) = Some b.
Proof. intros m lo hi x (_ & _ & H) Hx. exact (proj2 (H x Hx)). Qed.

End WithSegs.
