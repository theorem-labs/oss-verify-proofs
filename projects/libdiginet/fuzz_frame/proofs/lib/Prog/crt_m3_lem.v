(* Lemmas for crt_m3.v (check_round_trip in fuzz_frame.plain, 0x13310 .. 0x13460): byte
   blocks in rw_cells, the bytes that the zero-sum build stores, and the answer of
   diginet_frame_build when the frame is built.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac
  Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Prog Require Import diginet_frame_build_c.
Import ListNotations.
Open Scope Z_scope.

(* The frame of the zero-sum build. *)
Definition m3_bf (b : list byte) : list byte :=
  build_frame (fr_dst b) (fr_src b) (fr_send b) (fr_ack b) (fr_retry b) (fr_cmd b) (fr_ncmds b) (fr_body b) true.

(** * Byte blocks *)

Lemma m3_split : forall m A B (k1 k2 : nat) l1 l2,
  B = A + Z.of_nat k1 -> length l1 = k1 ->
  rw_cells rsegs m A [CB (k1 + k2) (l1 ++ l2)] ->
  rw_cells rsegs m A [CB k1 l1] /\ rw_cells rsegs m B [CB k2 l2].
Proof.
  intros m A B k1 k2 l1 l2 -> L1 [[[Hl _] Hb] (Ha & Hn & Hw)].
  cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize] in Hl, Hb, Hn, Hw.
  rewrite app_nil_r in Hb. rewrite length_app in Hl.
  apply bytes_at_app in Hb. destruct Hb as [Hb1 Hb2]. rewrite L1 in Hb2.
  split.
  - split; [split|].
    + cbn. split; [exact L1 | exact I].
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb1.
    + split; [lia|]. split; [cbn [cells_size csize]; lia|]. intros i Hi. apply Hw.
      cbn [cells_size csize] in Hi. lia.
  - split; [split|].
    + cbn. split; [lia | exact I].
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb2.
    + split; [lia|]. split; [cbn [cells_size csize]; lia|]. intros i Hi. rewrite <- Z.add_assoc. apply Hw.
      cbn [cells_size csize] in Hi. lia.
Qed.

Lemma m3_join : forall m A B (k1 k2 : nat) l1 l2,
  B = A + Z.of_nat k1 ->
  rw_cells rsegs m A [CB k1 l1] -> rw_cells rsegs m B [CB k2 l2] ->
  rw_cells rsegs m A [CB (k1 + k2) (l1 ++ l2)].
Proof.
  intros m A B k1 k2 l1 l2 -> [[[L1 _] Hb1] (Ha1 & Hn1 & Hw1)] [[[L2 _] Hb2] (Ha2 & Hn2 & Hw2)].
  cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize] in L1, L2, Hb1, Hb2, Hn1, Hn2, Hw1, Hw2.
  rewrite app_nil_r in Hb1, Hb2.
  split; [split|].
  - cbn. split; [rewrite length_app; lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [exact Hb1|].
    rewrite L1. exact Hb2.
  - split; [lia|]. split; [cbn [cells_size csize]; lia|]. intros i Hi. cbn [cells_size csize] in Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat k1)) as [Hlt|Hge].
    + apply Hw1. lia.
    + replace (A + i) with (A + Z.of_nat k1 + (i - Z.of_nat k1)) by lia. apply Hw2. lia.
Qed.

(* The block of memset into want, cut at the fields of the frame: the MACs, the 18 header
   bytes, the body and the zero pad. *)
Lemma m3_slots : forall m A (N Lb : nat) z,
  N = (6 + (6 + (18 + (Lb + (30 - Lb)))))%nat ->
  rw_cells rsegs m A [CB N (repeat z N)] ->
  rw_cells rsegs m A [CB 6 (repeat z 6)] /\ rw_cells rsegs m (A + 6) [CB 6 (repeat z 6)] /\
  rw_cells rsegs m (A + 12) [CB 18 (repeat z 18)] /\ rw_cells rsegs m (A + 30) [CB Lb (repeat z Lb)] /\
  rw_cells rsegs m (A + 30 + Z.of_nat Lb) [CB (30 - Lb) (repeat z (30 - Lb))].
Proof.
  intros m A N Lb z -> H0. rewrite !repeat_app in H0.
  destruct (m3_split m A (A + 6) 6 _ (repeat z 6) _ eq_refl (repeat_length z 6) H0) as [H1 R1].
  destruct (m3_split m (A + 6) (A + 12) 6 _ (repeat z 6) _ ltac:(lia) (repeat_length z 6) R1) as [H2 R2].
  destruct (m3_split m (A + 12) (A + 30) 18 _ (repeat z 18) _ ltac:(lia) (repeat_length z 18) R2) as [H3 R3].
  destruct (m3_split m (A + 30) (A + 30 + Z.of_nat Lb) Lb _ (repeat z Lb) _ eq_refl (repeat_length z Lb) R3)
    as [H4 H5].
  tauto.
Qed.

Lemma m3_merge_all : forall m A cs, rw_cells rsegs m A cs -> rw_cells rsegs m A [CB (cells_size cs) (cells_bytes cs)].
Proof.
  intros m A cs H. pose proof (rw_cells_merge rsegs m A [] cs []) as M. rewrite app_nil_r in M. exact (M H).
Qed.

Lemma m3_merge2 : forall m A x y rest,
  rw_cells rsegs m A (C8 x :: C8 y :: rest) -> rw_cells rsegs m A (CB 16 (cells_bytes [C8 x; C8 y]) :: rest).
Proof. intros m A x y rest H. exact (rw_cells_merge rsegs m A [] [C8 x; C8 y] rest H). Qed.

Lemma m3_merge3 : forall m A (j j2 : list byte) v rest,
  rw_cells rsegs m A (CB 16 j :: C8 v :: CB 4 j2 :: rest) ->
  rw_cells rsegs m A (CB 28 (cells_bytes [CB 16 j; C8 v; CB 4 j2]) :: rest).
Proof. intros m A j j2 v rest H. exact (rw_cells_merge rsegs m A [] [CB 16 j; C8 v; CB 4 j2] rest H). Qed.

Lemma m3_cell_bytes : forall m A cs k c, rw_cells rsegs m A cs -> cell_at cs k = Some c ->
  bytes_at rsegs m (A + Z.of_nat k) (cbytes c).
Proof.
  intros m A cs k c [[Hwf Hb] _] Hc.
  destruct (cell_at_split _ _ _ c Hc) as (pre & post & Ecs & Hsz & _).
  rewrite Ecs in Hwf, Hb. apply cells_wf_app in Hwf. destruct Hwf as [Hwpre _].
  rewrite cells_bytes_app in Hb. cbn [cells_bytes] in Hb.
  apply bytes_at_app in Hb. destruct Hb as [_ Hb].
  rewrite cells_bytes_length in Hb by exact Hwpre. rewrite Hsz in Hb.
  apply bytes_at_app in Hb. exact (proj1 Hb).
Qed.

Lemma m3_rw_bytes : forall m A k bs, rw_cells rsegs m A [CB k bs] -> bytes_at rsegs m A bs.
Proof. intros m A k bs [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

Lemma m3_stk_rw : forall m A n, stk rsegs m A (A + n) -> 0 <= n ->
  exists junk, rw_cells rsegs m A [CB (Z.to_nat n) junk].
Proof.
  intros m A n ST Hn. destruct (stk_carve rsegs m A (A + n) (Z.to_nat n) ST ltac:(lia)) as [_ [junk H]].
  exists junk. replace (A + n - Z.of_nat (Z.to_nat n)) with A in H by lia. exact H.
Qed.

(** * The bytes of the frame at buf *)

Lemma m3_bytes_sub : forall m a l k n, bytes_at rsegs m a l -> (k <= length l)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k l)).
Proof.
  intros m a l k n H Hk. rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn, Nat.min_l in H by exact Hk.
  rewrite <- (firstn_skipn n (skipn k l)) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

Lemma m3_dst_bytes : forall m buf b, bytes_at rsegs m buf b -> bytes_at rsegs m buf (fr_dst b).
Proof.
  intros m buf b H. pose proof (m3_bytes_sub m buf b 0 6 H (Nat.le_0_l _)) as S.
  cbn [skipn Z.of_nat] in S. rewrite Z.add_0_r in S. exact S.
Qed.

Lemma m3_src_bytes : forall m buf b, (6 <= length b)%nat -> bytes_at rsegs m buf b ->
  bytes_at rsegs m (buf + 6) (fr_src b).
Proof. intros m buf b L H. exact (m3_bytes_sub m buf b 6 6 H L). Qed.

Lemma m3_body_bytes : forall m buf b, fr_code b = 0 -> bytes_at rsegs m buf b ->
  bytes_at rsegs m (buf + 30) (fr_body b).
Proof.
  intros m buf b C H. destruct (fr_code_ok b C) as (L30 & _).
  exact (m3_bytes_sub m buf b 30 (Z.to_nat (fr_body_len b)) H L30).
Qed.

Lemma m3_len_dst : forall b, (6 <= length b)%nat -> length (fr_dst b) = 6%nat.
Proof. intros b L. unfold fr_dst. rewrite length_firstn. lia. Qed.

Lemma m3_len_src : forall b, (12 <= length b)%nat -> length (fr_src b) = 6%nat.
Proof. intros b L. unfold fr_src. rewrite length_firstn, length_skipn. lia. Qed.

Lemma m3_len_bf : forall b, (12 <= length b)%nat ->
  Z.of_nat (length (m3_bf b)) = frame_len (length (fr_body b)).
Proof. intros b L. unfold m3_bf. apply length_build_frame; [apply m3_len_dst | apply m3_len_src]; lia. Qed.

(** * The bytes that the build stores *)

Lemma m3_le1_b8 : forall (v : word) z, b8 (bv_unsigned v) = b8 z -> le1 v = [b8 z].
Proof. intros v z H. change (le1 v) with [b8 (bv_unsigned v)]. rewrite H. reflexivity. Qed.

Lemma m3_le1_lit : forall (v : word) z, bv_unsigned v mod 2^8 = z mod 2^8 -> le1 v = [b8 z].
Proof. intros v z H. apply m3_le1_b8. rewrite <- (b8_mod (bv_unsigned v)), <- (b8_mod z), H. reflexivity. Qed.

Lemma m3_b8_shr : forall u x k w, 0 <= u < 2^64 -> 0 <= k -> k + 8 <= w -> u mod 2^w = x mod 2^w ->
  b8 (bv_unsigned (Z_to_bv 64 (Z.shiftr u k))) = b8 (x / 2^k).
Proof.
  intros u x k w Hu Hk Hw H.
  assert (P : 0 < 2^k) by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.shiftr_div_pow2 by lia.
  assert (D : 0 <= u / 2^k <= u) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; nia]).
  rewrite unsigned_lit by lia.
  rewrite <- (b8_div_mod u k w) by lia. rewrite <- (b8_div_mod x k w) by lia. rewrite H. reflexivity.
Qed.

Lemma m3_swrap16 : forall z, bv_swrap 16 z = (z + 2^15) mod 2^16 - 2^15.
Proof. reflexivity. Qed.

Lemma m3_sx32_mod : forall x, 0 <= x < 2^32 -> bv_unsigned (sx32 (Z_to_bv 64 x)) mod 2^32 = x mod 2^32.
Proof.
  intros x Hx. unfold sx32. rewrite (unsigned_lit x) by lia. rewrite unsigned_lit_wrap.
  rewrite mod_mod_pow2 by lia. rewrite bv_swrap32_eq. Z.div_mod_to_equations. lia.
Qed.

Lemma m3_sx16_mod : forall x, 0 <= x < 2^16 -> bv_unsigned (sx16 (Z_to_bv 64 x)) mod 2^16 = x mod 2^16.
Proof.
  intros x Hx. unfold sx16. rewrite (unsigned_lit x) by lia. rewrite unsigned_lit_wrap.
  rewrite mod_mod_pow2 by lia. rewrite m3_swrap16. Z.div_mod_to_equations. lia.
Qed.

Lemma m3_le1_sx32 : forall x k, 0 <= x < 2^32 -> 0 <= k <= 24 ->
  le1 (Z_to_bv 64 (Z.shiftr (bv_unsigned (sx32 (Z_to_bv 64 x))) k)) = [b8 (x / 2^k)].
Proof.
  intros x k Hx Hk. apply m3_le1_b8.
  apply (m3_b8_shr _ x k 32); [apply u64_range | lia | lia | apply m3_sx32_mod; lia].
Qed.

Lemma m3_le1_sx32_0 : forall x, 0 <= x < 2^32 -> le1 (sx32 (Z_to_bv 64 x)) = [b8 x].
Proof.
  intros x Hx. apply m3_le1_b8. rewrite <- (b8_mod_w (bv_unsigned (sx32 (Z_to_bv 64 x))) 32) by lia.
  rewrite m3_sx32_mod by lia. apply b8_mod_w. lia.
Qed.

Lemma m3_le1_sx16 : forall x k, 0 <= x < 2^16 -> 0 <= k <= 8 ->
  le1 (Z_to_bv 64 (Z.shiftr (bv_unsigned (sx16 (Z_to_bv 64 x))) k)) = [b8 (x / 2^k)].
Proof.
  intros x k Hx Hk. apply m3_le1_b8.
  apply (m3_b8_shr _ x k 16); [apply u64_range | lia | lia | apply m3_sx16_mod; lia].
Qed.

Lemma m3_le1_sx16_0 : forall x, 0 <= x < 2^16 -> le1 (sx16 (Z_to_bv 64 x)) = [b8 x].
Proof.
  intros x Hx. apply m3_le1_b8. rewrite <- (b8_mod_w (bv_unsigned (sx16 (Z_to_bv 64 x))) 16) by lia.
  rewrite m3_sx16_mod by lia. apply b8_mod_w. lia.
Qed.

Lemma m3_le1_eq : forall z z', 0 <= z < 2^64 -> z = z' -> le1 (Z_to_bv 64 z) = [b8 z'].
Proof. intros z z' Hz <-. apply m3_le1_b8. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma m3_le1_srl : forall z z' k, 0 <= z < 2^64 -> 0 <= k -> z = z' ->
  le1 (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 z)) k)) = [b8 (z' / 2^k)].
Proof.
  intros z z' k Hz Hk <-. apply m3_le1_b8. rewrite (unsigned_lit z) by lia.
  apply (m3_b8_shr z z k (k + 8)); [lia | lia | lia | reflexivity].
Qed.

(* The 18 header bytes at want + 12 and the blocks around them make the frame. *)
Lemma m3_want : forall m want b hdr z,
  hdr = put16 0x885f ++ put16 (16 + Z.of_nat (length (fr_body b))) ++ put16 0 ++ put32 (fr_send b) ++
        put32 (fr_ack b) ++ put16 (fr_retry b) ++ [b8 (fr_cmd b); b8 (fr_ncmds b)] ->
  z = b8 0 ->
  rw_cells rsegs m want [CB 6 (fr_dst b)] ->
  rw_cells rsegs m (want + 6) [CB 6 (fr_src b)] ->
  rw_cells rsegs m (want + 12) [CB 18 hdr] ->
  rw_cells rsegs m (want + 30) [CB (length (fr_body b)) (fr_body b)] ->
  rw_cells rsegs m (want + 30 + Z.of_nat (length (fr_body b)))
    [CB (30 - length (fr_body b)) (repeat z (30 - length (fr_body b)))] ->
  rw_cells rsegs m want [CB (Z.to_nat (frame_len (length (fr_body b)))) (m3_bf b)].
Proof.
  intros m want b hdr z Eh Ez H1 H2 H3 H4 H5. subst hdr z.
  pose proof (m3_join m (want + 30) (want + 30 + Z.of_nat (length (fr_body b))) (length (fr_body b)) _ _ _
    eq_refl H4 H5) as H45.
  pose proof (m3_join m (want + 12) (want + 30) 18 _ _ _ ltac:(lia) H3 H45) as H3'.
  pose proof (m3_join m (want + 6) (want + 12) 6 _ _ _ ltac:(lia) H2 H3') as H2'.
  pose proof (m3_join m want (want + 6) 6 _ _ _ ltac:(lia) H1 H2') as H1'.
  replace (Z.to_nat (frame_len (length (fr_body b))))
    with (6 + (6 + (18 + (length (fr_body b) + (30 - length (fr_body b))))))%nat by (unfold frame_len; lia).
  unfold m3_bf, build_frame. exact H1'.
Qed.

(** * diginet_frame_build when the frame is built *)

Lemma m3_build_code : forall bb, (Z.of_nat (length bb) <=? 1484) && negb (system_at bb) = true ->
  build_code bb (frame_len (length bb)) = frame_len (length bb).
Proof.
  intros bb H. apply andb_true_iff in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply negb_true_iff in H2.
  unfold build_code. replace (1484 <? Z.of_nat (length bb)) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite H2, Z.ltb_irrefl. reflexivity.
Qed.

Lemma m3_build_out : forall dmac smac send ack retry cmd ncmds bb x,
  (Z.of_nat (length bb) <=? 1484) && negb (system_at bb) = true ->
  build_out dmac smac send ack retry cmd ncmds bb 1 (repeat x (Z.to_nat (frame_len (length bb)))) =
  build_frame dmac smac send ack retry cmd ncmds bb true.
Proof.
  intros dmac smac send ack retry cmd ncmds bb x H. unfold build_out. cbv zeta. rewrite repeat_length.
  assert (F60 : 60 <= frame_len (length bb)) by (unfold frame_len; lia).
  rewrite Z2Nat.id by lia. rewrite (m3_build_code bb H).
  replace (0 <=? frame_len (length bb)) with true by (symmetry; apply Z.leb_le; lia).
  change (1 =? 1) with true.
  rewrite skipn_all2 by (rewrite repeat_length; lia). apply app_nil_r.
Qed.

Lemma m3_memcmp_self : forall l k, (k <= length l)%nat -> memcmp_model l l k = Some 0.
Proof.
  intros l k; revert l; induction k as [|k IH]; intros [|x l] H; cbn in *; try lia; try reflexivity.
  rewrite Z.eqb_refl. apply IH. lia.
Qed.
