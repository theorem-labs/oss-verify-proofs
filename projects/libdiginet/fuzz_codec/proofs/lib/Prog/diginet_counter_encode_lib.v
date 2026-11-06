From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells.
Import ListNotations.
Open Scope Z_scope.

(** ---- cells ---- *)

(** One byte of a byte list in memory. *)
Lemma cnt_byte_read : forall m a bs (k : nat) e,
  bytes_at rsegs m a bs -> (k < length bs)%nat -> e = a + Z.of_nat k ->
  ov_read_bytes rsegs m (wa e) 1 = Some [nth k bs (Z_to_bv 8 0)].
Proof.
  intros m a bs k e H Hk ->. rewrite (bytes_at_ov_read rsegs m a bs k 1 H ltac:(lia)).
  f_equal. clear H. revert bs Hk. induction k as [|k IH]; intros [|b bs] Hk; cbn in *; try lia.
  - reflexivity.
  - apply IH. lia.
Qed.

(** rw_cells of two lists of cells side by side. *)
Lemma cnt_rw_split : forall m A pre post,
  rw_cells rsegs m A (pre ++ post) ->
  rw_cells rsegs m A pre /\ rw_cells rsegs m (A + Z.of_nat (cells_size pre)) post.
Proof.
  intros m A pre post [[Hwf Hb] (Ha & Hn & Hw)].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_bytes_length in B2 by exact W1.
  rewrite cells_size_app in Hn, Hw.
  split; split; try (split; assumption).
  - split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size pre) + i) with (A + (Z.of_nat (cells_size pre) + i)) by lia.
    apply Hw. lia.
Qed.

Lemma cnt_rw_join : forall m A B pre post,
  rw_cells rsegs m A pre -> rw_cells rsegs m B post -> B = A + Z.of_nat (cells_size pre) ->
  rw_cells rsegs m A (pre ++ post).
Proof.
  intros m A B pre post [[W1 B1] (Ha & Hn1 & Hw1)] [[W2 B2] (Hb & Hn2 & Hw2)] ->.
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|].
    rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.ltb_spec i (Z.of_nat (cells_size pre))).
    + apply Hw1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size pre) + (i - Z.of_nat (cells_size pre))) by lia.
      apply Hw2. lia.
Qed.

(** The bytes of the middle cells of rw_cells. *)
Lemma cnt_rw_mid_bytes : forall m A pre mid post,
  rw_cells rsegs m A (pre ++ mid ++ post) ->
  bytes_at rsegs m (A + Z.of_nat (cells_size pre)) (cells_bytes mid).
Proof.
  intros m A pre mid post H. apply cnt_rw_split in H. destruct H as [_ H].
  apply cnt_rw_split in H. destruct H as [[[_ Hb] _] _]. exact Hb.
Qed.

Lemma cnt_rw_rebytes : forall m A cs cs',
  rw_cells rsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[Hwf Hb] Hw] Hwf' Heq. split; [split; [exact Hwf' | rewrite Heq; exact Hb] |].
  rewrite <- (cells_bytes_length cs') by assumption. rewrite Heq. rewrite cells_bytes_length by assumption.
  exact Hw.
Qed.

(** A list in three pieces. *)
Lemma cnt_split3 : forall {T} (i j : nat) (l : list T),
  l = firstn i l ++ firstn j (skipn i l) ++ skipn (i + j) l.
Proof.
  intros T i; induction i as [|i IH]; intros j l.
  - cbn. rewrite firstn_skipn. reflexivity.
  - destruct l as [|x l]; cbn.
    + destruct j; reflexivity.
    + f_equal. apply IH.
Qed.

(** The 32 bytes of out as the three areas the code writes: bytes 0..3 (stores), 4..13 (memcpy),
    14..31 (stores). *)
Lemma cnt_out_split : forall m A before,
  rw_cells rsegs m A [CB 32 before] ->
  rw_cells rsegs m A [CB 4 (firstn 4 before)] /\
  rw_cells rsegs m (A + 4) [CB 10 (firstn 10 (skipn 4 before))] /\
  rw_cells rsegs m (A + 14) [CB 18 (firstn 18 (skipn 10 (skipn 4 before)))].
Proof.
  intros m A before H.
  apply (rw_cells_split_CB rsegs m A [] 32 before [] [4; 10; 18]%nat) in H; [|reflexivity].
  cbn [mk_CB_cells app] in H.
  apply (cnt_rw_split m A [CB 4 (firstn 4 before)]) in H. destruct H as [H1 H].
  apply (cnt_rw_split m _ [CB 10 (firstn 10 (skipn 4 before))]) in H. destruct H as [H2 H3].
  cbn [cells_size csize Nat.add] in H2, H3.
  replace (A + Z.of_nat 4) with (A + 4) in H2 by lia.
  replace (A + Z.of_nat 4 + Z.of_nat 10) with (A + 14) in H3 by lia.
  auto.
Qed.

Lemma cnt_out_join : forall m A c1 c2 c3,
  rw_cells rsegs m A c1 -> rw_cells rsegs m (A + 4) c2 -> rw_cells rsegs m (A + 14) c3 ->
  cells_size c1 = 4%nat -> cells_size c2 = 10%nat -> rw_cells rsegs m A (c1 ++ c2 ++ c3).
Proof.
  intros m A c1 c2 c3 H1 H2 H3 S1 S2.
  apply (cnt_rw_join m A (A + 4)); [exact H1 | | rewrite S1; reflexivity].
  apply (cnt_rw_join m (A + 4) (A + 14)); [exact H2 | exact H3 | rewrite S2; cbn; lia].
Qed.

(** The 10 payload bytes the code builds in its frame, as memcpy's source. *)
Lemma cnt_fr_src : forall m A j (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : byte) post,
  rw_cells rsegs m A (CB 14 j :: C1 b0 :: C1 b1 :: C1 b2 :: C1 b3 :: C1 b4 :: C1 b5 :: C1 b6 :: C1 b7
                      :: C1 b8 :: C1 b9 :: post) ->
  bytes_at rsegs m (A + 14) [b0; b1; b2; b3; b4; b5; b6; b7; b8; b9].
Proof.
  intros m A j b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 post H.
  pose proof (cnt_rw_mid_bytes m A [CB 14 j] [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7; C1 b8; C1 b9]
                post H) as B.
  cbn [cells_bytes cbytes app cells_size csize Nat.add] in B.
  replace (A + Z.of_nat 14) with (A + 14) in B by lia. exact B.
Qed.

(** ---- bytes ---- *)

Lemma cnt_modulus8 : bv_modulus 8 = 256. Proof. reflexivity. Qed.
Lemma cnt_half_modulus8 : bv_half_modulus 8 = 128. Proof. reflexivity. Qed.

Lemma cnt_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. rewrite cnt_modulus8 in H. exact H. Qed.

Lemma cnt_u8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z H. rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite cnt_modulus8. lia. Qed.

Lemma cnt_b8_u64 : forall z, Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z)) = Z_to_bv 8 z.
Proof.
  intros z. apply Z_to_bv8_mod. rewrite unsigned_lit_wrap.
  change (2 ^ 8) with 256. change (2 ^ 64) with 18446744073709551616.
  Z.div_mod_to_equations. lia.
Qed.

Lemma cnt_b8_ub : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma cnt_signed_byte : forall b : byte,
  bv_signed b = if bv_unsigned b <? 128 then bv_unsigned b else bv_unsigned b - 256.
Proof.
  intros b. pose proof (cnt_byte_range b) as R.
  change (bv_signed b) with (bv_swrap 8 (bv_unsigned b)). unfold bv_swrap, bv_wrap.
  rewrite cnt_half_modulus8, cnt_modulus8.
  destruct (Z.ltb_spec (bv_unsigned b) 128); Z.div_mod_to_equations; lia.
Qed.

(** The low byte of a sign-extended byte. *)
Lemma cnt_b8_sxb : forall b : byte, Z_to_bv 8 (bv_unsigned (sxb b)) = b.
Proof.
  intros b. unfold sxb. rewrite cnt_b8_u64. apply bv_eq. rewrite Z_to_bv_unsigned.
  pose proof (cnt_byte_range b) as R. rewrite cnt_signed_byte. unfold bv_wrap. rewrite cnt_modulus8.
  destruct (Z.ltb_spec (bv_unsigned b) 128).
  - rewrite Z.mod_small by lia. reflexivity.
  - rewrite <- (Z_mod_plus_full _ 1). rewrite Z.mod_small by lia. lia.
Qed.

(** bltz on a byte loaded with lb: bit 7 of the byte. *)
Lemma cnt_sxb_neg : forall b : byte,
  9223372036854775808 <= bv_unsigned (sxb b) <-> 128 <= bv_unsigned b.
Proof.
  intros b. pose proof (cnt_byte_range b) as R. unfold sxb. rewrite unsigned_lit_wrap, cnt_signed_byte.
  change (2 ^ 64) with 18446744073709551616.
  destruct (Z.ltb_spec (bv_unsigned b) 128).
  - rewrite Z.mod_small by lia. split; intros; lia.
  - rewrite <- (Z_mod_plus_full _ 1). rewrite Z.mod_small by lia. split; intros; lia.
Qed.

Lemma cnt_sxb_pos : forall b : byte,
  bv_unsigned (sxb b) < 9223372036854775808 -> bv_unsigned b < 128.
Proof.
  intros b H. destruct (Z.lt_ge_cases (bv_unsigned b) 128) as [L|L]; [exact L|].
  apply cnt_sxb_neg in L. lia.
Qed.

Lemma cnt_leb_true : forall x, 128 <= x -> (128 <=? x) = true.
Proof. intros x H. apply Z.leb_le. exact H. Qed.
Lemma cnt_leb_false : forall x, x < 128 -> (128 <=? x) = false.
Proof. intros x H. apply Z.leb_gt. exact H. Qed.

Lemma cnt_tb7 : forall x, 0 <= x < 256 -> Z.testbit x 7 = (128 <=? x).
Proof.
  intros x H.
  replace (Z.testbit x 7) with (Z.testbit (Z.shiftr x 7) 0) by (rewrite Z.shiftr_spec by lia; reflexivity).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 7) with 128.
  destruct (Z.leb_spec 128 x) as [L|L].
  - replace (x / 128) with 1 by (symmetry; Z.div_mod_to_equations; lia). reflexivity.
  - replace (x / 128) with 0 by (symmetry; Z.div_mod_to_equations; lia). reflexivity.
Qed.

(** The key word the code stores: counter_addr | 0x60000. *)
Lemma cnt_key : forall c, 0 <= c < 256 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 8 c)) 393216) = Z_to_bv 64 (KEY 6 c).
Proof.
  intros c H. rewrite cnt_u8 by exact H. unfold KEY. f_equal.
  replace (Z.land c 65535) with c.
  - change (6 * 65536) with 393216. apply Z.lor_comm.
  - symmetry. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. apply Z.mod_small.
    change (2 ^ 16) with 65536. lia.
Qed.

(** The constant halfwords and the 0xf7 byte the code stores. *)
Lemma cnt_le2_13f0 : le2 (Z_to_bv 64 5104) = [Z_to_bv 8 240; Z_to_bv 8 19].
Proof.
  unfold le2. cbn [Z_to_le_bytes].
  apply (f_equal2 cons); [apply Z_to_bv8_mod; vm_compute; reflexivity|].
  apply (f_equal2 cons); [apply Z_to_bv8_mod; vm_compute; reflexivity|reflexivity].
Qed.
Lemma cnt_le2_010f : le2 (Z_to_bv 64 271) = [Z_to_bv 8 15; Z_to_bv 8 1].
Proof.
  unfold le2. cbn [Z_to_le_bytes].
  apply (f_equal2 cons); [apply Z_to_bv8_mod; vm_compute; reflexivity|].
  apply (f_equal2 cons); [apply Z_to_bv8_mod; vm_compute; reflexivity|reflexivity].
Qed.
Lemma cnt_f7 : Z_to_bv 8 (-9) = Z_to_bv 8 247.
Proof. apply Z_to_bv8_mod. vm_compute. reflexivity. Qed.

(** The 32 bytes of out after the success path, as cmd_out of the encoded command. *)
Lemma cnt_out_final : forall m A before (dev c dots : Z) (g0 g1 g2 g3 g4 g5 g6 g7 : byte),
  length before = 32%nat ->
  rw_cells rsegs m A
    ([C2 (Z_to_bv 64 5104); C1 (Z_to_bv 8 dev); C1 (Z_to_bv 8 48)] ++
     [CB 10 [Z_to_bv 8 c; Z_to_bv 8 dots; g7; g6; g5; g4; g3; g2; g1; g0]] ++
     [C1 (Z_to_bv 8 (-9));
      CB 9 (firstn 9 (skipn 1 (firstn 18 (skipn 10 (skipn 4 before)))));
      C2 (Z_to_bv 64 271);
      CB 2 (firstn 2 (skipn 11 (skipn 1 (firstn 18 (skipn 10 (skipn 4 before))))));
      C4 (Z_to_bv 64 (KEY 6 c))]) ->
  rw_cells rsegs m A
    [CB 32 (cmd_out before
              (Some ([240; 19; dev; 48] ++
                     [c; dots; bv_unsigned g7; bv_unsigned g6; bv_unsigned g5; bv_unsigned g4;
                      bv_unsigned g3; bv_unsigned g2; bv_unsigned g1; bv_unsigned g0] ++ [247],
                     KEY 6 c, 1)))].
Proof.
  intros m A before dev c dots g0 g1 g2 g3 g4 g5 g6 g7 HL H.
  do 32 (let y := fresh "y" in destruct before as [|y before]; [cbn in HL; lia|]).
  destruct before; [|cbn in HL; lia]. clear HL.
  eapply cnt_rw_rebytes; [exact H | |].
  - cbn [cells_wf cell_wf]. split; [|exact I].
    unfold cmd_out, bz, b8.
    cbn [map app length firstn skipn Z.of_nat Pos.of_succ_nat Pos.succ].
    rewrite length_le4. reflexivity.
  - unfold cmd_out, bz, b8.
    cbn [cells_bytes cbytes app map length firstn skipn Z.of_nat Pos.of_succ_nat Pos.succ].
    rewrite cnt_le2_13f0, cnt_le2_010f, cnt_f7. cbn [app].
    repeat (apply (f_equal2 cons); [first [reflexivity | rewrite cnt_b8_ub; reflexivity] |]).
    reflexivity.
Qed.

(** ---- the spec ---- *)

Definition cnt_pl (d : desk) (dots : Z) (g0 g1 g2 g3 g4 g5 g6 g7 : byte) : list Z :=
  [d_counter d; dots; bv_unsigned g7; bv_unsigned g6; bv_unsigned g5; bv_unsigned g4;
   bv_unsigned g3; bv_unsigned g2; bv_unsigned g1; bv_unsigned g0].

Definition cnt_bad (d : desk) (dots : Z) (g0 g1 g2 g3 g4 g5 g6 g7 : byte) : bool :=
  (128 <=? d_counter d) || (128 <=? dots) || (128 <=? bv_unsigned g7) || (128 <=? bv_unsigned g6)
  || (128 <=? bv_unsigned g5) || (128 <=? bv_unsigned g4) || (128 <=? bv_unsigned g3)
  || (128 <=? bv_unsigned g2) || (128 <=? bv_unsigned g1) || (128 <=? bv_unsigned g0).

(** counter_spec on a desk and the 8 seg bytes. *)
Lemma cnt_spec_some : forall d dots (g0 g1 g2 g3 g4 g5 g6 g7 : byte) rest,
  desk_ok d -> 0 <= dots < 256 ->
  counter_spec (Some d) (zb (g0 :: g1 :: g2 :: g3 :: g4 :: g5 :: g6 :: g7 :: rest)) dots =
  if 0x7f <? d_dev d then (E_ARG, None)
  else if cnt_bad d dots g0 g1 g2 g3 g4 g5 g6 g7 then (E_RANGE, None)
  else (0, Some ([0xf0; 0x13; d_dev d; 0x30] ++ cnt_pl d dots g0 g1 g2 g3 g4 g5 g6 g7 ++ [0xf7],
                 KEY 6 (d_counter d), 1)).
Proof.
  intros d dots g0 g1 g2 g3 g4 g5 g6 g7 rest (Hd0 & Hd1 & Hd2 & Hd3) Hdots.
  unfold counter_spec.
  replace ([d_counter d; dots] ++ rev (firstn 8 (zb (g0 :: g1 :: g2 :: g3 :: g4 :: g5 :: g6 :: g7 :: rest))))
    with (cnt_pl d dots g0 g1 g2 g3 g4 g5 g6 g7) by reflexivity.
  unfold sysex_spec.
  destruct (0x7f <? d_dev d); [reflexivity|].
  replace (existsb (fun x => Z.testbit x 7) (cnt_pl d dots g0 g1 g2 g3 g4 g5 g6 g7))
    with (cnt_bad d dots g0 g1 g2 g3 g4 g5 g6 g7).
  - destruct (cnt_bad d dots g0 g1 g2 g3 g4 g5 g6 g7); reflexivity.
  - pose proof (cnt_byte_range g0). pose proof (cnt_byte_range g1). pose proof (cnt_byte_range g2).
    pose proof (cnt_byte_range g3). pose proof (cnt_byte_range g4). pose proof (cnt_byte_range g5).
    pose proof (cnt_byte_range g6). pose proof (cnt_byte_range g7).
    unfold cnt_bad, cnt_pl. cbn [existsb].
    rewrite !cnt_tb7 by lia. rewrite orb_false_r. rewrite !orb_assoc. reflexivity.
Qed.
