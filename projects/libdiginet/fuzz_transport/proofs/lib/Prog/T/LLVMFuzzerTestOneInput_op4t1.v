(* Case 4 of the op loop of LLVMFuzzerTestOneInput in the plain image, the tagged arm's first segment:
   0x13df4 (op4_j, g_raw = 0) -> 0x1400c (op4_t1). *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb TSess0 TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import memset_c memcpy_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract
  diginet_session_submit_c check_refusal_submit_c check_latest_submit_c settle_c
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_op4k.
Import ListNotations.
Open Scope Z_scope.

(* ---- pure facts ---- *)

(* one byte of the input buffer, as bytes_at reads it (Prog/T/LLVMFuzzerTestOneInput_disp.v disp_sub1) *)
Lemma o4t1_sub1 : forall (D : list byte) k, (k < length D)%nat -> firstn 1 (skipn k D) = [nth k D (b8 0)].
Proof.
  induction D as [|d D IH]; intros k Hk; cbn in Hk; [lia|].
  destruct k as [|k]; cbn; [reflexivity|]. apply IH. lia.
Qed.

(* Copied from the ubsan twin: t4_land32 / t4_minus3 of an earlier version of it,
   libdiginet/fuzz_transport lib/U/Prog/T/LLVMFuzzerTestOneInput_op4_tag_a.v (file sha256 8b7e8455a562; donor not released), and
   lib/U/Prog/T/LLVMFuzzerTestOneInput_op4_tag_s.v t4_magic. *)
Lemma o4t1_land32 : forall x, 0 <= x -> Z.land x 4294967295 = x mod 4294967296.
Proof. intros x Hx. change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma o4t1_minus3 : forall len, 3 <= len <= 24 -> Z.land (len + 4294967293) 4294967295 = len - 3.
Proof.
  intros len H. rewrite o4t1_land32 by lia.
  replace (len + 4294967293) with (len - 3 + 1 * 4294967296) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(* the compiler's reciprocal of 22: a mulhu, no shift (the dividend is a byte) *)
Lemma o4t1_magic : forall b K, 0 <= b < 256 -> 2 ^ 64 <= 22 * K ->
  11 * (22 * K - 2 ^ 64) + 21 * K < 2 ^ 64 -> Z.shiftr (b * K) 64 = b / 22.
Proof.
  intros b K Hb HK HB. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.div_mod b 22 ltac:(lia)) as E.
  pose proof (Z.mod_pos_bound b 22 ltac:(lia)) as R.
  assert (Hq : 0 <= b / 22 <= 11).
  { split; [apply Z.div_pos; lia|].
    assert (b / 22 < 12) by (apply Z.div_lt_upper_bound; lia). lia. }
  remember (b / 22) as q eqn:Eq. remember (b mod 22) as r eqn:Er.
  assert (HKp : 0 <= K) by lia.
  assert (HB2 : b * K = q * 2 ^ 64 + ((22 * K - 2 ^ 64) * q + r * K)).
  { replace b with (22 * q + r) at 1 by lia. ring. }
  rewrite HB2, Z.div_add_l by lia.
  rewrite (Z.div_small ((22 * K - 2 ^ 64) * q + r * K) (2 ^ 64)) by nia.
  lia.
Qed.

(* 0x13e44-0x13e68 as the kit leaves it: lb % 22 + 3, with the reciprocal of 22 loaded from 0xfdf0 *)
Lemma o4t1_len_val : forall b, 0 <= b < 256 ->
  b - (Z.shiftr (b * 838488366986797801) 64 mod 18446744073709551616 * 22) mod 18446744073709551616 + 3
  = b mod 22 + 3.
Proof.
  intros b Hb. rewrite (o4t1_magic b 838488366986797801 Hb) by lia.
  assert (Hq : 0 <= b / 22 <= 11).
  { split; [apply Z.div_pos; lia|].
    assert (b / 22 < 12) by (apply Z.div_lt_upper_bound; lia). lia. }
  rewrite (Z.mod_small (b / 22) 18446744073709551616) by lia.
  rewrite (Z.mod_small (b / 22 * 22) 18446744073709551616) by lia.
  pose proof (Z.div_mod b 22 ltac:(lia)). lia.
Qed.

(* 0x13f80-0x13f84: (serial << 50) >> 57 is serial >> 7 & 0x7f for a serial < 2^14 *)
Lemma o4t1_ser_hi : forall g, 0 <= g < 16384 ->
  Z.shiftr (Z.shiftl g 50 mod 18446744073709551616) 57 = Z.land (Z.shiftr g 7) 127.
Proof.
  intros g Hg. rewrite Z.shiftl_mul_pow2 by lia. rewrite !Z.shiftr_div_pow2 by lia.
  change (2 ^ 50) with 1125899906842624. change (2 ^ 57) with 144115188075855872. change (2 ^ 7) with 128.
  rewrite (Z.mod_small (g * 1125899906842624)) by lia.
  replace 144115188075855872 with (1125899906842624 * 128) by reflexivity.
  rewrite <- Z.div_div by lia. rewrite Z.div_mul by lia.
  change 127 with (Z.ones 7). rewrite Z.land_ones by lia. change (2 ^ 7) with 128.
  rewrite Z.mod_small; [reflexivity|]. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Lemma o4t1_land127 : forall x, 0 <= x -> 0 <= Z.land x 127 < 128.
Proof.
  intros x Hx. change 127 with (Z.ones 7). rewrite Z.land_ones by lia.
  apply Z.mod_pos_bound. reflexivity.
Qed.

Lemma o4t1_skipn_repeat : forall (x : byte) k n, skipn n (repeat x k) = repeat x (k - n).
Proof. induction k as [|k IH]; intros [|n]; cbn; [reflexivity | reflexivity | reflexivity | apply IH]. Qed.

Lemma o4t1_firstn_app : forall (l1 l2 : list byte) n, (n <= length l1)%nat -> firstn n (l1 ++ l2) = firstn n l1.
Proof.
  intros l1 l2 n H. rewrite firstn_app. replace (n - length l1)%nat with 0%nat by lia.
  cbn [firstn]. apply app_nil_r.
Qed.

(* a cell list cut around one cell, and joined back *)
Lemma o4t1_cut3 : forall m A pre c post, rw_cells rsegs m A (pre ++ c :: post) ->
  rw_cells rsegs m A pre /\ rw_cells rsegs m (A + Z.of_nat (cells_size pre)) [c] /\
  rw_cells rsegs m (A + Z.of_nat (cells_size pre) + Z.of_nat (csize c)) post.
Proof.
  intros m A pre c post H. apply op4_rw_app in H. destruct H as [H1 H2].
  change (c :: post) with ([c] ++ post) in H2. apply op4_rw_app in H2. destruct H2 as [H2 H3].
  cbn [cells_size] in H3. rewrite Nat.add_0_r in H3. tauto.
Qed.

Lemma o4t1_join3 : forall m A pre c post,
  rw_cells rsegs m A pre -> rw_cells rsegs m (A + Z.of_nat (cells_size pre)) [c] ->
  rw_cells rsegs m (A + Z.of_nat (cells_size pre) + Z.of_nat (csize c)) post ->
  rw_cells rsegs m A (pre ++ c :: post).
Proof.
  intros m A pre c post H1 H2 H3. apply op4_rw_app. split; [exact H1|].
  change (c :: post) with ([c] ++ post). apply op4_rw_app. split; [exact H2|].
  cbn [cells_size]. rewrite Nat.add_0_r. exact H3.
Qed.

Lemma o4t1_u8_lit : forall z, 0 <= z < 256 -> bv_unsigned (b8 z) = z.
Proof. intros z Hz. unfold b8. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact Hz. Qed.

(* memcpy's source in.p = data + off (0x13fac): an empty copy when the address wraps to 0 *)
Lemma o4t1_src : forall m data D off n, bytes_at rsegs m data D -> 0 <= off -> 0 <= n ->
  off + n <= Z.of_nat (length D) ->
  bytes_at rsegs m (bv_unsigned (Z_to_bv 64 (data + off))) (sub D off (Z.to_nat n)) /\
  (n = 0 \/ bv_unsigned (Z_to_bv 64 (data + off)) = data + off).
Proof.
  intros m data D off n H Ho Hn Hl. pose proof (bytes_at_bound rsegs m data D H) as HB.
  destruct (Z.eq_dec n 0) as [->|Hn0].
  - split; [|left; reflexivity]. unfold sub.
    replace (firstn (Z.to_nat 0) (skipn (Z.to_nat off) D)) with (@nil byte) by reflexivity.
    pose proof (wk_word_range (Z_to_bv 64 (data + off))) as R.
    revert R. generalize (bv_unsigned (Z_to_bv 64 (data + off))). intros u R.
    unfold bytes_at. change (length (@nil byte)) with 0%nat.
    split; [lia|]. split; [lia|]. intros i Hi. lia.
  - assert (E : bv_unsigned (Z_to_bv 64 (data + off)) = data + off) by (apply unsigned_lit; lia).
    rewrite E. split; [|right; reflexivity]. apply op4_bytes_sub; [exact H | lia | lia].
Qed.

(* ---- the frame of case 4 with the struct at sp + 0x50 as any list of cells ---- *)

Definition o4t1_fr (x10 : cell) (bf : word) (j30 : list byte) (sc : list cell) (j70 : list byte)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)); x10;
   C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff); C8 bf; CB 32 j30] ++ sc ++
  [CB 8 j70; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma o4t1_fr_op4 : forall x10 bf j30 cs j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11,
  op4_fr x10 bf j30 cs j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 =
  o4t1_fr x10 bf j30 [CB 32 cs] j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.
Proof. reflexivity. Qed.

Lemma o4t1_fr_size : forall x10 bf j30 sc j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11,
  csize x10 = 8%nat -> cells_size sc = 32%nat ->
  cells_size (o4t1_fr x10 bf j30 sc j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) = 224%nat.
Proof.
  intros x10 bf j30 sc j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 H1 H2. unfold o4t1_fr.
  rewrite !cells_size_app, H2. cbn [cells_size csize]. rewrite H1. reflexivity.
Qed.

(* the same bytes at sp + 0x50 in other cells *)
Lemma o4t1_restruct : forall m Sp x10 bf j30 sc sc' j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11,
  rw_cells rsegs m Sp (o4t1_fr x10 bf j30 sc j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  cells_wf sc' -> cells_bytes sc' = cells_bytes sc ->
  rw_cells rsegs m Sp (o4t1_fr x10 bf j30 sc' j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Proof. intros. unfold o4t1_fr in *. eapply op4_rw_mid; eassumption. Qed.

(* the frame cut at the memcpy destination sp + 0x53 (0x13fa8), the cell c there, and joined back *)
Lemma o4t1_fr_cut : forall m Sp v bf j30 y0 y1 y2 c rest j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11,
  rw_cells rsegs m Sp (o4t1_fr (C8 v) bf j30 ([C1 y0; C1 y1; C1 y2; c] ++ rest) j70
                         ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  rw_cells rsegs m Sp [C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)); C8 v;
                       C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff); C8 bf; CB 32 j30; C1 y0; C1 y1; C1 y2] /\
  rw_cells rsegs m (Sp + 83) [c] /\
  rw_cells rsegs m (Sp + 83 + Z.of_nat (csize c))
    (rest ++ [CB 8 j70; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
Proof.
  intros m Sp v bf j30 y0 y1 y2 c rest j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 H.
  pose proof (o4t1_cut3 m Sp
    [C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)); C8 v;
     C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff); C8 bf; CB 32 j30; C1 y0; C1 y1; C1 y2] c
    (rest ++ [CB 8 j70; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    H) as (H1 & H2 & H3).
  cbn [cells_size csize Nat.add] in H2, H3. change (Z.of_nat 83) with 83 in H2, H3. tauto.
Qed.

Lemma o4t1_fr_join : forall m Sp v bf j30 y0 y1 y2 c rest j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11,
  rw_cells rsegs m Sp [C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)); C8 v;
                       C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff); C8 bf; CB 32 j30; C1 y0; C1 y1; C1 y2] ->
  rw_cells rsegs m (Sp + 83) [c] ->
  rw_cells rsegs m (Sp + 83 + Z.of_nat (csize c))
    (rest ++ [CB 8 j70; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) ->
  rw_cells rsegs m Sp (o4t1_fr (C8 v) bf j30 ([C1 y0; C1 y1; C1 y2; c] ++ rest) j70
                         ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Proof.
  intros m Sp v bf j30 y0 y1 y2 c rest j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 H1 H2 H3.
  exact (o4t1_join3 m Sp
    [C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)); C8 v;
     C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff); C8 bf; CB 32 j30; C1 y0; C1 y1; C1 y2] c
    (rest ++ [CB 8 j70; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    H1 H2 H3).
Qed.

(* the struct's bytes at sp + 0x50 *)
Lemma o4t1_fr_bytes : forall m Sp v bf j30 sc j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11,
  rw_cells rsegs m Sp (o4t1_fr (C8 v) bf j30 sc j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  bytes_at rsegs m (Sp + 80) (cells_bytes sc).
Proof.
  intros m Sp v bf j30 sc j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 H. unfold o4t1_fr in H.
  apply op4_rw_app in H. destruct H as [_ H]. apply op4_rw_app in H. destruct H as [H _].
  cbn [cells_size csize Nat.add] in H. change (Z.of_nat 80) with 80 in H.
  unfold rw_cells, cells_at in H. destruct H as [[_ HB] _]. exact HB.
Qed.

Section OP4T1.
Context (data : Z) (D : list byte).

(* op4_mem with another frame over the same memory *)
Lemma o4t1_mem_fr : forall Sp lo B m0 m fr fr',
  op4_mem data D Sp lo B m0 m fr -> rw_cells rsegs m Sp fr' -> cells_size fr' = 224%nat ->
  op4_mem data D Sp lo B m0 m fr'.
Proof.
  intros Sp lo B m0 m fr fr' HM HR HS. unfold op4_mem in *.
  destruct HM as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & _ & _).
  tauto.
Qed.

End OP4T1.

(* the struct as op4_j leaves it (cmd_struct (repeat 0 24) 0 0 key), in the cells the stores hit *)
Definition o4t1_s0 (key : Z) : list cell :=
  [C1 (b8 0); C1 (b8 0); C1 (b8 0); CB 21 (repeat (b8 0) 21); C1 (b8 0); C1 (b8 0); CB 6 ([b8 0; b8 0] ++ put 4 key)].

Lemma o4t1_s0_ok : forall key, cells_wf (o4t1_s0 key) /\
  cells_bytes (o4t1_s0 key) = cells_bytes [CB 32 (cmd_struct (repeat (b8 0) 24) 0 0 key)].
Proof.
  intros key. unfold o4t1_s0, cmd_struct. split.
  - cbn [cells_wf cell_wf]. rewrite repeat_length, length_app, length_put. cbn. tauto.
  - cbn [cells_bytes cbytes repeat app]. rewrite !app_nil_r. reflexivity.
Qed.

(* the struct after the display store (0x13df8) *)
Definition o4t1_s1 (display key : Z) : list cell :=
  [C1 (b8 0); C1 (b8 0); C1 (b8 0); CB 21 (repeat (b8 0) 21); C1 (b8 0); C1 (b8 display);
   CB 6 ([b8 0; b8 0] ++ put 4 key)].

(* the struct's tail after the memcpy span: the zeros left, len, display, the pad and the key *)
Definition o4t1_tl (D : list byte) (c3 : fuzz_in) (display key : Z) (n : nat) (bs : list byte) : list cell :=
  [CB (21 - n) bs; C1 (b8 (o4_len D c3)); C1 (b8 display); CB 6 ([b8 0; b8 0] ++ put 4 key)].

(* the struct after the four byte stores 0x13f8c-0x13f98 *)
Definition o4t1_s2 (D B1 : list byte) (c3 : fuzz_in) (display key : Z) : list cell :=
  [C1 (b8 TAG); C1 (b8 (Z.land (g_ncmd B1) 0x7f)); C1 (b8 (Z.land (Z.shiftr (g_ncmd B1) 7) 0x7f));
   CB 21 (repeat (b8 0) 21); C1 (b8 (o4_len D c3)); C1 (b8 display); CB 6 ([b8 0; b8 0] ++ put 4 key)].

(* the same bytes with the 21 zeros cut at n, the memcpy's span *)
Definition o4t1_s2x (D B1 : list byte) (c3 : fuzz_in) (display key : Z) (n : nat) : list cell :=
  [C1 (b8 TAG); C1 (b8 (Z.land (g_ncmd B1) 0x7f)); C1 (b8 (Z.land (Z.shiftr (g_ncmd B1) 7) 0x7f));
   CB n (firstn n (repeat (b8 0) 21))] ++ o4t1_tl D c3 display key n (skipn n (repeat (b8 0) 21)).

(* the struct after the memcpy 0x13fb4, as the join leaves it *)
Definition o4t1_s3x (D B1 : list byte) (c3 : fuzz_in) (display key : Z) : list cell :=
  [C1 (b8 TAG); C1 (b8 (Z.land (g_ncmd B1) 0x7f)); C1 (b8 (Z.land (Z.shiftr (g_ncmd B1) 7) 0x7f));
   CB (Z.to_nat (o4_n D c3)) (sub D (o4_off D c3) (Z.to_nat (o4_n D c3)))] ++
  o4t1_tl D c3 display key (Z.to_nat (o4_n D c3)) (skipn (Z.to_nat (o4_n D c3)) (repeat (b8 0) 21)).

Lemma o4t1_s2x_ok : forall D B1 c3 display key n, (n <= 21)%nat ->
  cells_wf (o4t1_s2x D B1 c3 display key n) /\
  cells_bytes (o4t1_s2x D B1 c3 display key n) = cells_bytes (o4t1_s2 D B1 c3 display key).
Proof.
  intros D B1 c3 display key n Hn. unfold o4t1_s2x, o4t1_tl, o4t1_s2. split.
  - cbn [app cells_wf cell_wf]. rewrite length_firstn, length_skipn, repeat_length.
    cbn [length]. rewrite ?length_app, ?length_put. cbn [length]. repeat split; lia.
  - cbn [app cells_bytes cbytes].
    assert (E : forall R, firstn n (repeat (b8 0) 21) ++ skipn n (repeat (b8 0) 21) ++ R = repeat (b8 0) 21 ++ R)
      by (intros R; rewrite app_assoc, firstn_skipn; reflexivity).
    rewrite E. reflexivity.
Qed.

(* the model's take after lb (fuzz_take_m (o4_c4 c3) (len - 3)) *)
Lemma o4t1_tk : forall D c3, llvm_cursor D c3 ->
  llvm_cursor D (o4_c4 D c3) /\ 3 <= o4_len D c3 <= 24 /\
  o4_off D c3 = fi_off (o4_c4 D c3) /\
  o4_n D c3 = (if o4_len D c3 - 3 <? fi_n (o4_c4 D c3) then o4_len D c3 - 3 else fi_n (o4_c4 D c3)) /\
  0 <= o4_n D c3 <= 21 /\ o4_n D c3 <= fi_n (o4_c4 D c3).
Proof.
  intros D c3 HC.
  assert (HC4 : llvm_cursor D (o4_c4 D c3)).
  { unfold o4_c4, fuzz_u8_m. unfold llvm_cursor in *.
    destruct (Z.eqb_spec (fi_n c3) 0); cbn [fst fi_off fi_n]; lia. }
  assert (HL : 3 <= o4_len D c3 <= 24).
  { unfold o4_len. pose proof (Z.mod_pos_bound (snd (fuzz_u8_m D c3)) 22 ltac:(lia)). lia. }
  pose proof HC4 as (H1 & H2 & H3 & H4).
  split; [exact HC4|]. split; [exact HL|].
  unfold o4_off, o4_n, o4_tk, fuzz_take_m. cbv beta iota zeta delta [fst snd].
  split; [reflexivity|].
  destruct (Z.ltb_spec (o4_len D c3 - 3) (fi_n (o4_c4 D c3))); repeat split; lia.
Qed.

(* the struct after the memcpy with the copied bytes and the zeros after them in one cell *)
Definition o4t1_s3 (D B1 : list byte) (c3 : fuzz_in) (display key : Z) : list cell :=
  [C1 (b8 TAG); C1 (b8 (Z.land (g_ncmd B1) 0x7f)); C1 (b8 (Z.land (Z.shiftr (g_ncmd B1) 7) 0x7f));
   CB 21 (sub D (o4_off D c3) (Z.to_nat (o4_n D c3)) ++ repeat (b8 0) (Z.to_nat (21 - o4_n D c3)));
   C1 (b8 (o4_len D c3)); C1 (b8 display); CB 6 ([b8 0; b8 0] ++ put 4 key)].

Lemma o4t1_s3x_ok : forall D B1 c3 display key, llvm_cursor D c3 ->
  cells_wf (o4t1_s3 D B1 c3 display key) /\
  cells_bytes (o4t1_s3 D B1 c3 display key) = cells_bytes (o4t1_s3x D B1 c3 display key).
Proof.
  intros D B1 c3 display key HC.
  pose proof (o4t1_tk D c3 HC) as (HC4 & HL & EO & EN & HN & HN4).
  pose proof HC4 as (H1 & H2 & H3 & H4).
  assert (LS : length (sub D (o4_off D c3) (Z.to_nat (o4_n D c3))) = Z.to_nat (o4_n D c3))
    by (apply length_sub; rewrite EO; lia).
  unfold o4t1_s3, o4t1_s3x, o4t1_tl. split.
  - cbn [app cells_wf cell_wf]. rewrite length_app, LS, repeat_length.
    cbn [length]. rewrite ?length_app, ?length_put. cbn [length]. repeat split; lia.
  - cbn [app cells_bytes cbytes]. rewrite o4t1_skipn_repeat.
    replace (21 - Z.to_nat (o4_n D c3))%nat with (Z.to_nat (21 - o4_n D c3)) by lia.
    rewrite <- !app_assoc. reflexivity.
Qed.

Lemma o4t1_s3_ok : forall D B1 c3 display key, llvm_cursor D c3 ->
  cells_wf (o4t1_s3 D B1 c3 display key) /\
  cells_bytes (o4t1_s3 D B1 c3 display key) = cells_bytes [CB 32 (o4_cs D B1 c3 display key)].
Proof.
  intros D B1 c3 display key HC.
  pose proof (o4t1_s3x_ok D B1 c3 display key HC) as [W _]. split; [exact W|].
  unfold o4t1_s3, o4_cs, o4_cb, cmd_struct.
  cbn [app cells_bytes cbytes]. rewrite <- !app_assoc. cbn [app]. rewrite ?app_nil_r. reflexivity.
Qed.

Section OP4T1S.
Context (data : Z) (D : list byte).

Ltac o4t1_cur_mem := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => mm end.

(* 0x13fb8 -> 0x1400c: len < 4, or the F0 13 xx 70 scan (TR6Op4Scan's op4_sys_scan) *)
Lemma o4t1_tail : forall Sp lo ops c3 B1 before display key m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Q
    m j30 j70 (rr t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  op4_sys_scan_stmt -> op4_sys_short_stmt ->
  o4_tok D ops c3 B1 before display key ->
  op4_mem data D Sp lo (o4_B2 B1) m0 m
    (o4t1_fr (C8 (Z_to_bv 64 (fi_n (o4_c4 D c3)))) (Z_to_bv 64 (bv_swrap 32 before)) j30
       (o4t1_s3 D B1 c3 display key) j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  (forall ms', op4_t1 data D m0 gp tp Sp lo ops c3 B1 before display key
                 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
  evt rsegs Q
    (MS (mkR rr (Z_to_bv 64 Sp) gp tp t0 t1 t2
             (Z_to_bv 64 (W_BASE_PLAIN + A_Cmd_st (g_ncmd B1))) (Z_to_bv 64 (g_ncmd B1))
             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 240) (Z_to_bv 64 (data + fi_off (o4_c4 D c3)))
             (Z_to_bv 64 226648) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
             (Z_to_bv 64 (o4_n D c3)) (Z_to_bv 64 19) (Z_to_bv 64 40)
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_M)) (Z_to_bv 64 ops) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13fb8) fc None m (seg_rom rsegs)).
Proof.
  intros Sp lo ops c3 B1 before display key m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Q
    m j30 j70 rr t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 SCAN SHORT HTOK HM HK.
  pose proof HTOK as ((HOPS & HCUR & HBEF & HDIS & HKEY) & HSER).
  pose proof (o4t1_tk D c3 HCUR) as (HC4 & HLEN & EO & EN & HN & HN4).
  pose proof HM as HMc. unfold op4_mem in HMc.
  destruct HMc as (HMU0 & HWMO0 & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HRW & HSZ).
  (* the struct as the model's cmd_struct, and op4_t1's invariant, before any step (the tail stores nothing) *)
  pose proof (o4t1_s3_ok D B1 c3 display key HCUR) as [S3W S3B].
  assert (LCS : length (o4_cs D B1 c3 display key) = 32%nat).
  { pose proof (cells_bytes_length _ S3W) as L. rewrite S3B in L. cbn [cells_bytes cbytes] in L.
    rewrite app_nil_r in L. rewrite L. reflexivity. }
  pose proof HRW as HCS. apply o4t1_fr_bytes in HCS. rewrite S3B in HCS. cbn [cells_bytes cbytes] in HCS.
  rewrite app_nil_r in HCS.
  pose proof HRW as HRWc.
  apply (o4t1_restruct _ _ _ _ _ _ [CB 32 (o4_cs D B1 c3 display key)]) in HRWc;
    [| cbn [cells_wf cell_wf]; split; [exact LCS | exact I] | symmetry; exact S3B].
  rewrite <- o4t1_fr_op4 in HRWc.
  pose proof (o4t1_mem_fr data D _ _ _ _ _ _ _ HM HRWc ltac:(reflexivity)) as HMf.
  assert (HTM : o4_tmem data D Sp lo c3 B1 before display key (o4_B2 B1) m0 m
                  ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) by (exists j30, j70; exact HMf).
  assert (LCB : length (o4_cb D B1 c3) = 24%nat).
  { unfold o4_cb. rewrite !length_app, length_sub, repeat_length; [cbn [length]; lia | |];
      rewrite EO; pose proof HC4 as (HC4a & HC4b & HC4c & HC4d); lia. }
  assert (HLO0 : 0 <= lo) by (unfold W_BASE_PLAIN, W_LEN in HOWS; lia).
  unfold LLVM_FP, LLVM_LOOP_K, LLVM_FRAME in *.
  unfold o4t1_fr, o4t1_s3 in HRW. cbn [app] in HRW.
  wk_facts.
  (* 0x13fb8 lbu a1, 0x68(sp): len; 0x13fbc li a0, 4; 0x13fc0 bltu a1, a0 *)
  zstep. cbv beta. rewrite (o4t1_u8_lit (o4_len D c3)) by lia.
  do 2 zstep.
  if_cases K; zify_cond K.
  - (* len = 3: 0x14008 mv s5, zero; sys = 0 (spec_system_at needs 4 bytes) *)
    zstep.
    assert (ES : o4_sys D B1 c3 = false) by (unfold o4_sys; apply SHORT; exact K).
    apply HK. unfold op4_t1. do 17 eexists. split; [rewrite ES; reflexivity|].
    split; [exact HTOK | exact HTM].
  - (* 0x13fc4-0x13fcc: a0 = 0, a1 = len - 3, a2 = sp + 0x51, the scan at 0x13fd0 *)
    do 3 zstep.
    replace (Z_to_bv 64 (o4_len D c3 + -3)) with (Z_to_bv 64 (o4_len D c3 - 3)) by (f_equal; lia).
    replace (Z_to_bv 64 (Sp + 81)) with (Z_to_bv 64 (Sp + 80 + 1)) by (f_equal; lia).
    assert (ES : system_at (firstn (Z.to_nat (o4_len D c3)) (o4_cs D B1 c3 display key)) = o4_sys D B1 c3).
    { unfold o4_sys, o4_cs, cmd_struct. rewrite o4t1_firstn_app; [reflexivity | rewrite LCB; lia]. }
    eapply (SCAN (o4_cs D B1 c3 display key) (Sp + 80) (o4_len D c3));
      [exact HCS | rewrite LCS; lia | lia |].
    intros a0' a2' a3' a4'.
    apply HK. unfold op4_t1. do 17 eexists. split; [rewrite ES; reflexivity|].
    split; [exact HTOK | exact HTM].
Qed.

(* 0x13fa4 -> 0x13fb8: sd n at sp+0x10, memcpy(sp + 0x53, in.p, n) (:1092-1093) *)
Lemma o4t1_cp : forall Sp lo ops c3 B1 before display key m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Q
    m j10 j30 j70 (rr t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x22 t3 t4 t5 t6 : word),
  memcpy_contract -> op4_sys_scan_stmt -> op4_sys_short_stmt ->
  o4_tok D ops c3 B1 before display key ->
  op4_mem data D Sp lo (o4_B2 B1) m0 m
    (o4t1_fr (CB 8 j10) (Z_to_bv 64 (bv_swrap 32 before)) j30 (o4t1_s2 D B1 c3 display key) j70
       ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  a4 = Z_to_bv 64 (fi_n (o4_c4 D c3)) -> x19 = Z_to_bv 64 (data + fi_off (o4_c4 D c3)) ->
  x22 = Z_to_bv 64 (o4_n D c3) ->
  (forall ms', op4_t1 data D m0 gp tp Sp lo ops c3 B1 before display key
                 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
  evt rsegs Q
    (MS (mkR rr (Z_to_bv 64 Sp) gp tp t0 t1 t2
             (Z_to_bv 64 (W_BASE_PLAIN + A_Cmd_st (g_ncmd B1))) (Z_to_bv 64 (g_ncmd B1))
             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 240) x19 (Z_to_bv 64 226648) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
             x22 (Z_to_bv 64 19) (Z_to_bv 64 40) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_M)) (Z_to_bv 64 ops) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13fa4) fc None m (seg_rom rsegs)).
Proof.
  intros Sp lo ops c3 B1 before display key m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Q
    m j10 j30 j70 rr t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x22 t3 t4 t5 t6 MCC SCAN SHORT HTOK HM -> -> -> HK.
  pose proof HTOK as ((HOPS & HCUR & HBEF & HDIS & HKEY) & HSER).
  pose proof (o4t1_tk D c3 HCUR) as (HC4 & HLEN & EO & EN & HN & HN4).
  pose proof HC4 as (HC4a & HC4b & HC4c & HC4d).
  pose proof HM as HMc. unfold op4_mem in HMc.
  destruct HMc as (HMU0 & HWMO0 & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HRW & HSZ).
  unfold off_world in HOW. unfold off_window in HOWIN.
  assert (HLO0 : 0 <= lo) by (unfold W_BASE_PLAIN, W_LEN in HOWS; lia).
  unfold LLVM_FP, LLVM_LOOP_K, LLVM_FRAME in *. rewrite unsigned_lit in HOWIN by lia.
  unfold o4t1_fr, o4t1_s2 in HRW. cbn [app] in HRW.
  wk_facts.
  pose proof (bytes_at_bound rsegs m data D HD) as HDB.
  pose proof (munch_refl [(Sp - 0, Sp + 224); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMO.
  (* 0x13fa4 sd a4, 0x10(sp); 0x13fa8-0x13fb4 a0 = sp + 0x53, a1 = in.p, a2 = n, jal memcpy *)
  do 5 zstep.
  let mm := o4t1_cur_mem in
  assert (HM1 : op4_mem data D Sp lo (o4_B2 B1) m0 mm
    (o4t1_fr (C8 (Z_to_bv 64 (fi_n (o4_c4 D c3)))) (Z_to_bv 64 (bv_swrap 32 before)) j30
       (o4t1_s2 D B1 c3 display key) j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { eapply (op4_mem_after data D Sp lo 0 (o4_B2 B1) (o4_B2 B1) m0 m);
      [ exact HM | unfold LLVM_LOOP_K; lia | exact MU | exact WMO | exact HMI | exact HSTK | exact HWM | exact HFN
      | exact HRW | reflexivity ]. }
  clear HM MU WMO HMU0 HWMO0 HRW HSZ.
  pose proof HM1 as HM1c. unfold op4_mem in HM1c.
  destruct HM1c as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRW1 & _).
  pose proof (o4t1_s2x_ok D B1 c3 display key (Z.to_nat (o4_n D c3)) ltac:(lia)) as [SW SB].
  apply (o4t1_restruct _ _ _ _ _ _ (o4t1_s2x D B1 c3 display key (Z.to_nat (o4_n D c3)))) in HRW1;
    [| exact SW | exact SB].
  unfold o4t1_s2x in HRW1.
  apply o4t1_fr_cut in HRW1. destruct HRW1 as (HP & HX & HPOST). cbn [csize] in HPOST.
  pose proof (o4t1_src _ data D (fi_off (o4_c4 D c3)) (o4_n D c3) HD ltac:(lia) ltac:(lia) ltac:(lia)) as SRC0.
  eapply evt_cut.
  { eapply MCC with (src := sub D (o4_off D c3) (Z.to_nat (o4_n D c3)))
                    (junk := firstn (Z.to_nat (o4_n D c3)) (repeat (b8 0) 21)).
    - rewrite EO. exact (proj1 SRC0).
    - rewrite (unsigned_lit (o4_n D c3)) by lia. apply length_sub; rewrite EO; lia.
    - rewrite (unsigned_lit (Sp + 83)), (unsigned_lit (o4_n D c3)) by lia. exact HX.
    - rewrite (unsigned_lit (Sp + 83)), (unsigned_lit (o4_n D c3)) by lia.
      destruct (proj2 SRC0) as [E0|E0]; [| rewrite E0; lia].
      rewrite E0. generalize (bv_unsigned (Z_to_bv 64 (data + fi_off (o4_c4 D c3)))). intros u. lia.
    - exact HMI. }
  intros ms' Hpost. unfold memcpy_post in Hpost.
  destruct Hpost as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m3 &
                     -> & MU3 & WMO3 & MI3 & DST & SRC).
  rewrite !unsigned_lit in MU3, DST by lia.
  assert (HP3 := rw_cells_transport _ _ _ _ _ _ HP MU3 WMO3
                   ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)).
  assert (HPOST3 := rw_cells_transport _ _ _ _ _ _ HPOST MU3 WMO3
                   ltac:(unfold o4t1_tl; cbn [disjoint_from cells_size csize app]; lia)).
  assert (HJ : rw_cells rsegs m3 Sp
    (o4t1_fr (C8 (Z_to_bv 64 (fi_n (o4_c4 D c3)))) (Z_to_bv 64 (bv_swrap 32 before)) j30
       (o4t1_s3x D B1 c3 display key) j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { unfold o4t1_s3x. apply o4t1_fr_join; [exact HP3 | exact DST | cbn [csize]; exact HPOST3]. }
  pose proof (o4t1_s3x_ok D B1 c3 display key HCUR) as [S3W S3B].
  apply (o4t1_restruct _ _ _ _ _ _ (o4t1_s3 D B1 c3 display key)) in HJ; [| exact S3W | exact S3B].
  lazymatch type of HM1 with op4_mem _ _ _ _ _ _ ?mm _ =>
    assert (MUw : munch [(Sp - 0, Sp + 224); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] mm m3);
    [ eapply munch_weaken; [| exact MU3];
      intros x Hx; cbn [outside] in Hx |- *; destruct Hx as (Hx1 & Hx2 & _); split; [lia | exact I]
    | ];
    assert (STK3 : stk rsegs m3 lo Sp);
    [ eapply (stk_transport_disjoint rsegs _ mm m3 lo Sp HSTK MU3 WMO3); cbn [disjoint_from]; lia | ];
    assert (WM3 : wmem rsegs m3 (o4_B2 B1));
    [ eapply (rw_cells_transport rsegs _ mm m3 W_BASE_PLAIN _ HWM MU3 WMO3);
      rewrite wm_size; cbn [disjoint_from]; unfold W_BASE_PLAIN, W_LEN in *; lia | ]
  end.
  assert (HM3 : op4_mem data D Sp lo (o4_B2 B1) m0 m3
    (o4t1_fr (C8 (Z_to_bv 64 (fi_n (o4_c4 D c3)))) (Z_to_bv 64 (bv_swrap 32 before)) j30
       (o4t1_s3 D B1 c3 display key) j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { eapply (op4_mem_after data D Sp lo 0 (o4_B2 B1) (o4_B2 B1) m0 _ m3 _ _ HM1);
      [ unfold LLVM_LOOP_K; lia | exact MUw | exact WMO3 | exact MI3 | exact STK3 | exact WM3 | exact HFN
      | exact HJ | ].
    reflexivity. }
  rewrite (ret_pc_even 0x13fb8) by (first [lia | reflexivity]).
  eapply o4t1_tail; [exact SCAN | exact SHORT | exact HTOK | exact HM3 | exact HK].
Qed.

(* 0x13f64 -> 0x1400c: the struct's stores, n, memcpy, the scan *)
Lemma o4t1_st : forall Sp lo ops c3 B1 before display key m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Q
    m j10 j30 j70 (rr t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x22 x23 t3 t4 t5 t6 : word),
  memcpy_contract -> op4_sys_scan_stmt -> op4_sys_short_stmt ->
  o4_tok D ops c3 B1 before display key ->
  op4_mem data D Sp lo (o4_B2 B1) m0 m
    (o4t1_fr (CB 8 j10) (Z_to_bv 64 (bv_swrap 32 before)) j30 (o4t1_s1 display key) j70
       ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  a0 = Z_to_bv 64 (o4_len D c3) -> a4 = Z_to_bv 64 (fi_n (o4_c4 D c3)) ->
  x19 = Z_to_bv 64 (data + fi_off (o4_c4 D c3)) ->
  (forall ms', op4_t1 data D m0 gp tp Sp lo ops c3 B1 before display key
                 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
  evt rsegs Q
    (MS (mkR rr (Z_to_bv 64 Sp) gp tp t0 t1 t2
             (Z_to_bv 64 (W_BASE_PLAIN + A_Cmd_st (g_ncmd B1))) (Z_to_bv 64 (g_ncmd B1))
             a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 (Z_to_bv 64 226648) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
             x22 x23 (Z_to_bv 64 40) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_M)) (Z_to_bv 64 ops) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13f64) fc None m (seg_rom rsegs)).
Proof.
  intros Sp lo ops c3 B1 before display key m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Q
    m j10 j30 j70 rr t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x22 x23 t3 t4 t5 t6 MCC SCAN SHORT HTOK HM
    -> -> -> HK.
  pose proof HTOK as ((HOPS & HCUR & HBEF & HDIS & HKEY) & HSER).
  pose proof HM as HMc. unfold op4_mem in HMc.
  destruct HMc as (HMU0 & HWMO0 & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HRW & HSZ).
  unfold off_world in HOW. unfold off_window in HOWIN.
  assert (HLO0 : 0 <= lo) by (unfold W_BASE_PLAIN, W_LEN in HOWS; lia).
  unfold LLVM_FP, LLVM_LOOP_K, LLVM_FRAME in *. rewrite unsigned_lit in HOWIN by lia.
  unfold o4t1_fr, o4t1_s1 in HRW. cbn [app] in HRW.
  wk_facts.
  pose proof (bytes_at_bound rsegs m data D HD) as HDB.
  assert (HLEN : 3 <= o4_len D c3 <= 24).
  { unfold o4_len. pose proof (Z.mod_pos_bound (snd (fuzz_u8_m D c3)) 22 ltac:(lia)). lia. }
  pose proof (munch_refl [(Sp - 0, Sp + 224); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMO.
  (* 0x13f64-0x13f98: s2 = 0xf0, s7 = 0x13, a1 = serial & 0x7f, s6 = (len + 2^32 - 3) & (2^32 - 1),
     a2 = (serial << 50) >> 57, the stores of TAG, a1, a2 at sp + 0x50 .. 0x52 and len at sp + 0x68 *)
  do 14 zstep.
  rewrite (unsigned_lit 160) in HRW by lia.
  rewrite (Z.mod_small (g_ncmd B1) 18446744073709551616) in HRW by (unfold CMDS_MAX in HSER; lia).
  rewrite (unsigned_lit (Z.land (g_ncmd B1) 127)) in HRW
    by (pose proof (o4t1_land127 (g_ncmd B1) ltac:(lia)); lia).
  rewrite (o4t1_ser_hi (g_ncmd B1)) in HRW by (unfold CMDS_MAX in HSER; lia).
  rewrite (unsigned_lit (Z.land (Z.shiftr (g_ncmd B1) 7) 127)) in HRW
    by (pose proof (o4t1_land127 (Z.shiftr (g_ncmd B1) 7) ltac:(apply Z.shiftr_nonneg; lia)); lia).
  rewrite (unsigned_lit (o4_len D c3)) in HRW by lia.
  rewrite (o4t1_minus3 (o4_len D c3) HLEN).
  let mm := o4t1_cur_mem in
  assert (HM2 : op4_mem data D Sp lo (o4_B2 B1) m0 mm
    (o4t1_fr (CB 8 j10) (Z_to_bv 64 (bv_swrap 32 before)) j30 (o4t1_s2 D B1 c3 display key) j70
       ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { eapply (op4_mem_after data D Sp lo 0 (o4_B2 B1) (o4_B2 B1) m0 m);
      [ exact HM | unfold LLVM_LOOP_K; lia | exact MU | exact WMO | exact HMI | exact HSTK | exact HWM | exact HFN
      | exact HRW | reflexivity ]. }
  pose proof (o4t1_tk D c3 HCUR) as (HC4 & _ & EO & EN & HN & HN4).
  pose proof HC4 as (HC4a & HC4b & HC4c & HC4d).
  (* 0x13f9c bltu s6, a4; 0x13fa0 mv s6, a4: n = min(len - 3, in.n) (fuzz_take) *)
  zstep.
  if_cases K; zify_cond K.
  - (* len - 3 < in.n: n = len - 3 *)
    eapply o4t1_cp; [exact MCC | exact SCAN | exact SHORT | exact HTOK | exact HM2 | reflexivity | reflexivity
      | | exact HK].
    f_equal. rewrite EN. destruct (Z.ltb_spec (o4_len D c3 - 3) (fi_n (o4_c4 D c3))); lia.
  - (* in.n <= len - 3: n = in.n *)
    zstep.
    eapply o4t1_cp; [exact MCC | exact SCAN | exact SHORT | exact HTOK | exact HM2 | reflexivity | reflexivity
      | | exact HK].
    f_equal. rewrite EN. destruct (Z.ltb_spec (o4_len D c3 - 3) (fi_n (o4_c4 D c3))); lia.
Qed.

(* 0x13e40 -> 0x13f64: the length byte lb, len = lb % 22 + 3 (:1088) *)
Lemma o4t1_lb : forall Sp lo ops c3 B1 before display key m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Q
    m j10 j30 j70 (rr t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 t3 t4 t5 t6 : word),
  memcpy_contract -> op4_sys_scan_stmt -> op4_sys_short_stmt ->
  o4_tok D ops c3 B1 before display key ->
  op4_mem data D Sp lo (o4_B2 B1) m0 m
    (o4t1_fr (CB 8 j10) (Z_to_bv 64 (bv_swrap 32 before)) j30 (o4t1_s1 display key) j70
       ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  (forall ms', op4_t1 data D m0 gp tp Sp lo ops c3 B1 before display key
                 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
  evt rsegs Q
    (MS (mkR rr (Z_to_bv 64 Sp) gp tp t0 t1 t2
             (Z_to_bv 64 (W_BASE_PLAIN + A_Cmd_st (g_ncmd B1))) (Z_to_bv 64 (g_ncmd B1))
             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 57) (Z_to_bv 64 (data + fi_off c3))
             (Z_to_bv 64 226648) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
             x22 (Z_to_bv 64 (fi_n c3)) (Z_to_bv 64 40) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_M)) (Z_to_bv 64 ops) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13e40) fc None m (seg_rom rsegs)).
Proof.
  intros Sp lo ops c3 B1 before display key m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Q
    m j10 j30 j70 rr t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 t3 t4 t5 t6 MCC SCAN SHORT HTOK HM HK.
  pose proof HTOK as ((HOPS & HCUR & HBEF & HDIS & HKEY) & HSER).
  pose proof HM as HMc. unfold op4_mem in HMc.
  destruct HMc as (HMU0 & HWMO0 & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HRW & HSZ).
  unfold off_world in HOW. unfold off_window in HOWIN.
  assert (HLO0 : 0 <= lo) by (unfold W_BASE_PLAIN, W_LEN in HOWS; lia).
  unfold LLVM_FP, LLVM_LOOP_K, LLVM_FRAME in *. rewrite unsigned_lit in HOWIN by lia.
  unfold o4t1_fr, o4t1_s1 in HRW. cbn [app] in HRW.
  pose proof (bytes_at_bound rsegs m data D HD) as HDB.
  unfold llvm_cursor in HCUR.
  (* 0x13e40 beqz s7: in.n = 0 *)
  zstep.
  if_cases K; zify_cond K.
  - (* fi_n c3 = 0: 0x13f5c a4 = 0, a0 = 3 *)
    do 2 zstep.
    assert (E8 : fuzz_u8_m D c3 = (c3, 0)) by (unfold fuzz_u8_m; rewrite K; reflexivity).
    eapply o4t1_st; [exact MCC | exact SCAN | exact SHORT | exact HTOK | exact HM | | | | exact HK].
    + unfold o4_len. rewrite E8. reflexivity.
    + unfold o4_c4. rewrite E8. cbn [fst]. rewrite K. reflexivity.
    + unfold o4_c4. rewrite E8. reflexivity.
  - assert (HK1 : (Z.to_nat (fi_off c3) + 1 <= length D)%nat) by lia.
    pose proof (bytes_at_read rsegs m data D (fi_off c3) 1 HD ltac:(lia) HK1) as HR.
    rewrite o4t1_sub1 in HR by lia.
    (* 0x13e44 lbu a0 = lb; 0x13e48-0x13e4c a1 = the 8 bytes at 0xfdf0 (0x13e48 - 0x4000 + 0x5a8), the
       reciprocal of 22, 838488366986797801; a4 = in.n - 1; s3 = in.p + 1; mulhu, * 22, sub, + 3; j 0x13f64 *)
    do 11 zstep.
    assert (E8 : fuzz_u8_m D c3 = (FuzzIn (fi_off c3 + 1) (fi_n c3 - 1), at8 D (Z.to_nat (fi_off c3)))).
    { unfold fuzz_u8_m. destruct (Z.eqb_spec (fi_n c3) 0); [lia | reflexivity]. }
    pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (fi_off c3)) D (b8 0))) as HBY.
    unfold bv_modulus in HBY. change (2 ^ Z.of_N 8) with 256 in HBY.
    eapply o4t1_st; [exact MCC | exact SCAN | exact SHORT | exact HTOK | exact HM | | | | exact HK].
    + unfold o4_len. rewrite E8. cbn [snd]. unfold at8, bz. f_equal. apply o4t1_len_val. exact HBY.
    + unfold o4_c4. rewrite E8. cbn [fst fi_n]. f_equal; lia.
    + unfold o4_c4. rewrite E8. cbn [fst fi_off]. f_equal; lia.
Qed.

End OP4T1S.

Lemma op4_tag1 : forall data D, op4_tag1_stmt data D.
Proof.
  intros data D. unfold op4_tag1_stmt.
  intros Sp lo ops c3 B1 before display key m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms Q
    MSC MCC SCAN SHORT HJ HRAW HNC HK.
  destruct HJ as (rr & t0 & t1 & t2 & x8 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x20 & x22 & t3 & t4 & t5 & t6 &
                  m & j10 & j30 & j70 & -> & HOK & HM).
  pose proof HM as HMc. unfold op4_mem in HMc.
  destruct HMc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRW & _).
  rewrite o4t1_fr_op4 in HRW.
  pose proof (o4t1_s0_ok key) as [S0W S0B].
  apply (o4t1_restruct _ _ _ _ _ _ (o4t1_s0 key)) in HRW; [| exact S0W | exact S0B].
  apply (o4t1_mem_fr data D _ _ _ _ _ _ _ HM) in HRW; [| apply o4t1_fr_size; reflexivity].
  clear HM. rename HRW into HM.
  pose proof HM as HMc. unfold op4_mem in HMc.
  destruct HMc as (HMU0 & HWMO0 & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HRW & HSZ).
  unfold off_world in HOW. unfold off_window in HOWIN.
  assert (HLO0 : 0 <= lo) by (unfold W_BASE_PLAIN, W_LEN in HOWS; lia).
  unfold LLVM_FP, LLVM_LOOP_K, LLVM_FRAME in *. rewrite unsigned_lit in HOWIN by lia.
  unfold o4t1_fr, o4t1_s0 in HRW. cbn [app] in HRW.
  wk_facts. wk_eq_fact OFF_g_fail_next. wk_eq_fact OFF_g_raw. wk_eq_fact OFF_g_ncmd. wk_eq_fact OFF_g_cmd.
  (* 0x13df4 lw a1, 4(s9): g_raw (OFF_g_raw = 64972 = OFF_g_fail_next + 4) *)
  zstep.
  change (s32_at B1 64972) with (g_raw B1). rewrite HRAW.
  pose proof (munch_refl [(Sp - 0, Sp + 224); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMO.
  (* 0x13df8 sb a0, 0x69(sp): c.display, byte 25 of the struct *)
  zstep.
  destruct HOK as (HOPS & HCUR & HBEF & HDIS & HKEY).
  rewrite (unsigned_lit display) in HRW by lia.
  (* 0x13dfc beqz a1: g_raw = 0, the tagged arm at 0x13e1c *)
  zstep. if_true.
  assert (HM1 : op4_mem data D Sp lo B1 m0 m1
    (o4t1_fr (CB 8 j10) (Z_to_bv 64 (bv_swrap 32 before)) j30
       [C1 (b8 0); C1 (b8 0); C1 (b8 0); CB 21 (repeat (b8 0) 21); C1 (b8 0); C1 (b8 display);
        CB 6 ([b8 0; b8 0] ++ put 4 key)] j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { eapply (op4_mem_after data D Sp lo 0 B1 B1 m0 m m1);
      [ exact HM | unfold LLVM_LOOP_K; lia | exact MU | exact WMO | exact HMI | exact HSTK | exact HWM | exact HFN
      | exact HRW | reflexivity ]. }
  clear HM.
  (* 0x13e1c lwu s1, 0x10(s9): serial = g_ncmd (OFF_g_ncmd = 64984); 0x13e20 + 0x13e2c s4 = 0x37558 = 226648 =
     W_BASE_PLAIN + OFF_g_cmd; s8 = 0x28; s0 = s4 + serial * 40 = &g_cmd[serial]; a2 = 40; a0 = s0; a1 = g_raw = 0;
     0x13e3c jal memset (:1087) *)
  do 9 zstep.
  change (u_at B1 64984 4) with (g_ncmd B1).
  pose proof (u_at_range B1 OFF_g_ncmd 4) as HNC0. change (u_at B1 OFF_g_ncmd 4) with (g_ncmd B1) in HNC0.
  cbn in HNC0.
  replace (226648 + g_ncmd B1 mod 18446744073709551616 * 40) with (W_BASE_PLAIN + A_Cmd_st (g_ncmd B1))
    by (unfold W_BASE_PLAIN, A_Cmd_st, OFF_g_cmd, CMDS_MAX in *; rewrite Z.mod_small by lia; lia).
  pose proof (wm_len _ _ _ _ HWM) as LB1.
  assert (CW : rw_cells rsegs m1 (W_BASE_PLAIN + A_Cmd_st (g_ncmd B1))
                 [CB (Z.to_nat 40) (sub B1 (A_Cmd_st (g_ncmd B1)) 40)]).
  { pose proof (wm_cell rsegs W_BASE_PLAIN m1 B1 (A_Cmd_st (g_ncmd B1)) 40 _ HWM eq_refl
                  ltac:(unfold A_Cmd_st, OFF_g_cmd, CMDS_MAX in *; lia)
                  ltac:(unfold A_Cmd_st, OFF_g_cmd, CMDS_MAX, W_LEN in *; lia)) as P.
    rewrite length_sub in P by (rewrite ?LB1; unfold A_Cmd_st, OFF_g_cmd, CMDS_MAX, W_LEN in *; lia).
    exact P. }
  eapply evt_cut.
  { eapply MSC with (junk := sub B1 (A_Cmd_st (g_ncmd B1)) 40).
    - rewrite !unsigned_lit by (unfold W_BASE_PLAIN, A_Cmd_st, OFF_g_cmd, CMDS_MAX in *; lia). exact CW.
    - exact HMI. }
  intros ms' Hpost. unfold memset_post in Hpost.
  destruct Hpost as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & z3 & z4 & z5 & z6 & m2 &
                     -> & MU1 & WMO1 & MI1 & CZ1).
  rewrite !unsigned_lit in MU1, CZ1 by (unfold W_BASE_PLAIN, A_Cmd_st, OFF_g_cmd, CMDS_MAX in *; lia).
  assert (HM2 : op4_mem data D Sp lo (o4_B2 B1) m0 m2
    (o4t1_fr (CB 8 j10) (Z_to_bv 64 (bv_swrap 32 before)) j30
       [C1 (b8 0); C1 (b8 0); C1 (b8 0); CB 21 (repeat (b8 0) 21); C1 (b8 0); C1 (b8 display);
        CB 6 ([b8 0; b8 0] ++ put 4 key)] j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { unfold o4_B2. change (Z.to_nat Cmd_ESZ) with (Z.to_nat 40). change (b8 0) with (Z_to_bv 8 (0 mod 256)).
    eapply (op4_mem_after_fill data D Sp lo B1 m0 m1 m2 (A_Cmd_st (g_ncmd B1)) 40);
      [ exact HM1 | exact MU1 | exact WMO1 | exact MI1 | exact CZ1
      | unfold A_Cmd_st, OFF_g_cmd, CMDS_MAX in *; lia | lia
      | unfold A_Cmd_st, OFF_g_cmd, CMDS_MAX, W_LEN in *; lia | ].
    unfold g_fail_next.
    rewrite u_at_upd_out by (rewrite ?repeat_length, ?LB1; unfold A_Cmd_st, OFF_g_cmd, OFF_g_fail_next, CMDS_MAX, W_LEN in *; lia).
    exact HFN. }
  rewrite (ret_pc_even 0x13e40) by (first [lia | reflexivity]).
  eapply (o4t1_lb data D); [exact MCC | exact SCAN | exact SHORT | | exact HM2 | exact HK].
  split; [exact (conj HOPS (conj HCUR (conj HBEF (conj HDIS HKEY)))) | lia].
Qed.
