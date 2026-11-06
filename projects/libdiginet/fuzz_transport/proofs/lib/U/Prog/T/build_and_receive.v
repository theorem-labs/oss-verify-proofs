(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths changed; 522 of its 775 lines of code are new or changed and 274 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/Prog/T/TSRGlue.v, with its module paths and module names changed; 794 of its 876 lines of code are new or changed and 693 lines of the source are left out. *)
(* Walk of build_and_receive (fuzz/fuzz_transport.c:1024-1030; spec_build_frame of fuzz/spec.h inlined) in the ubsan
   image: 0x161ac, 676 bytes, own frame 1616 (ra, s0-s8 saved at sp + 1536 .. sp + 1615), frame[SPEC_MAX_FRAME] at
   sp + 20, for the SR and SRcf contracts of U/Prog/T/build_and_receive_c.v.
   - bar_walk (0x161ac .. 0x16418): the prologue; s8 = max 30 len; memset (frame + 6, 0, s8 + 24); dst's six bytes
     loaded (lbu) and stored as a word and a halfword at frame[0 .. 5]; memcpy (frame + 6, src, 6); the 18 header
     bytes stored one by one (frame[12 .. 29]); the body's sum (the loop at 0x162e4, when len <> 0); memcpy
     (frame + 30, body, len) when len <> 0; then receive (frame, max 30 len + 30, 0, 0). The bytes at frame are
     fst (spec_build_frame dst src send ack retry cmd 1 body 0) (bar_frame_cells, bar_dst, bar_hdr, bar_frame_eq).
   - The UBSan checks, each a branch to the trap at 0x1644c, are pointer-overflow checks on frame + c (0x16260 bgeu
     frame + 6, 0x16278 frame + 13, 0x1628c frame + 12 = -1, 0x162a0 frame + 15, 0x162b8 frame + 14 = -1, 0x162c8
     frame + 17, 0x16320 frame + 16 = -1, 0x16330 frame + 19, 0x16340 frame + 18 = -1, 0x1634c / 0x1635c frame + 18
     against -3 / -4, 0x1636c frame + 23, 0x16380 frame + 22 = -1, 0x16390 / 0x163a0 frame + 22 against -3 / -4,
     0x163b0 frame + 27, 0x163c0 frame + 26 = -1, 0x163d0 frame + 29, 0x163dc frame + 30, 0x163f4 frame + 31),
     refuted by sp < 2^63 (h_pre's call_pre_k), and the loop's checks on body + i (0x162e4 body + i < body,
     0x162f0 body + i NULL, 0x162f4 body NULL), refuted by h_src (the body lies in a user block from 4096 up, or
     above sp, with body + len <= 2^64).
   - bar_epi (0x1641c .. 0x16448): the saved registers back, ret.
   - bar_gen: the walk, receive and the epilogue as one run, by U/Prog/T/TSRGlue.v (g_run, g_pre, sr_fr_call,
     g_above, sr_post), for SR and SRcf alike; build_and_receive_holds and build_and_receive_holds_cf. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes
  ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TNeed
  TNeedLink.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memset_c memcpy_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem.
Import ListNotations.
Open Scope Z_scope.

(* ==== the frame spec_build_frame writes ==== *)

(* fst (spec_build_frame ..) with ncmds 1 and zero_sum 0, as one list (TNeedLink.tneed_spec_build_frame). *)
Lemma bar_frame_eq : forall dst src send ack retry cmd body,
  length dst = 6%nat -> length src = 6%nat ->
  fst (spec_build_frame dst src send ack retry cmd 1 body 0) =
  dst ++ src ++ put16 0x885f ++ put16 (16 + Z.of_nat (length body)) ++ put16 (sum16 body) ++ put32 send ++
  put32 ack ++ put16 retry ++ [b8 cmd; b8 1] ++ body ++ repeat (b8 0) (30 - length body).
Proof.
  intros dst src send ack retry cmd body Hd Hs. rewrite tneed_spec_build_frame by assumption. cbn [fst].
  unfold build_frame. rewrite spec_sum_eq. reflexivity.
Qed.

Lemma bar_frame_len : forall dst src send ack retry cmd body,
  length dst = 6%nat -> length src = 6%nat ->
  Z.of_nat (length (fst (spec_build_frame dst src send ack retry cmd 1 body 0))) = Z.max 30 (Z.of_nat (length body)) + 30.
Proof.
  intros dst src send ack retry cmd body Hd Hs. rewrite tneed_spec_build_frame by assumption. cbn [fst].
  rewrite length_build_frame by assumption. unfold frame_len. lia.
Qed.

(* ==== cells of the frame ==== *)

(* Cells split in two at a cell boundary (U/Prog/T/send_control.v sc_rw_app). *)
Lemma bar_rw_app : forall m A cs1 cs2, rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf Hb] (Ha & Hl & Hw)].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_bytes_length in B2 by exact W1. rewrite cells_size_app in Hl, Hw.
  split; split; try (split; assumption).
  - split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
    apply Hw. lia.
Qed.

(* The frame after the prologue: the first 1536 bytes, then the saved registers. They are cut into the 26 bytes
   below memset's span (frame[0 .. 5] at A + 20), memset's span of k + 24 bytes at A + 26 (k = max 30 len), the rest
   of frame[] and the padding, and the saved registers at A + 1536. *)
Lemma bar_split_frame : forall m A J (c8 : list cell) k,
  rw_cells rsegs m A (CB 1536 J :: c8) -> 30 <= k <= 1484 ->
  rw_cells rsegs m A [CB 26 (firstn 26 J)] /\
  rw_cells rsegs m (A + 26) [CB (Z.to_nat (k + 24)) (firstn (Z.to_nat (k + 24)) (skipn 26 J))] /\
  rw_cells rsegs m (A + 50 + k)
    [CB (Z.to_nat (1486 - k)) (firstn (Z.to_nat (1486 - k)) (skipn (Z.to_nat (k + 24)) (skipn 26 J)))] /\
  rw_cells rsegs m (A + 1536) c8.
Proof.
  intros m A J c8 k H Hk.
  change (CB 1536 J :: c8) with ([] ++ CB 1536 J :: c8) in H.
  apply (rw_cells_split_CB rsegs m A [] 1536 J c8 [26%nat; Z.to_nat (k + 24); Z.to_nat (1486 - k)]) in H;
    [| cbn [sum_nat]; lia].
  cbn [mk_CB_cells app] in H.
  change (CB 26 (firstn 26 J) :: CB (Z.to_nat (k + 24)) (firstn (Z.to_nat (k + 24)) (skipn 26 J)) ::
          CB (Z.to_nat (1486 - k)) (firstn (Z.to_nat (1486 - k)) (skipn (Z.to_nat (k + 24)) (skipn 26 J))) :: c8)
    with ([CB 26 (firstn 26 J)] ++ [CB (Z.to_nat (k + 24)) (firstn (Z.to_nat (k + 24)) (skipn 26 J))] ++
          [CB (Z.to_nat (1486 - k)) (firstn (Z.to_nat (1486 - k)) (skipn (Z.to_nat (k + 24)) (skipn 26 J)))] ++
          c8) in H.
  apply bar_rw_app in H. destruct H as [H0 H].
  apply bar_rw_app in H. destruct H as [H1 H].
  apply bar_rw_app in H. destruct H as [H2 H3].
  cbn [cells_size csize Nat.add] in H1, H2, H3.
  split; [exact H0|]. split; [exact H1|]. split.
  - replace (A + 50 + k) with (A + Z.of_nat 26 + Z.of_nat (Z.to_nat (k + 24) + 0)) by lia. exact H2.
  - replace (A + 1536) with (A + Z.of_nat 26 + Z.of_nat (Z.to_nat (k + 24) + 0) +
                             Z.of_nat (Z.to_nat (1486 - k) + 0)) by lia. exact H3.
Qed.

Lemma bar_firstn_repeat : forall (z : byte) n k, firstn k (repeat z n) = repeat z (Nat.min k n).
Proof. intros z n. induction n as [|n IH]; intros [|k]; cbn; try reflexivity. f_equal. apply IH. Qed.

Lemma bar_skipn_repeat : forall (z : byte) n k, skipn k (repeat z n) = repeat z (n - k).
Proof. intros z n. induction n as [|n IH]; intros [|k]; cbn; try reflexivity. apply IH. Qed.

(* memset's span, zeroed, cut into src's 6 bytes (frame[6 .. 11]), the 18 header bytes (frame[12 .. 29]), the body's
   len bytes (frame[30 ..]) and the padding (k - len bytes). *)
Lemma bar_split_zero : forall m A (z : byte) k len,
  rw_cells rsegs m A [CB (Z.to_nat (k + 24)) (repeat z (Z.to_nat (k + 24)))] -> 0 <= len <= k ->
  rw_cells rsegs m A [CB 6 (repeat z 6)] /\
  rw_cells rsegs m (A + 6) [CB 18 (repeat z 18)] /\
  rw_cells rsegs m (A + 24) [CB (Z.to_nat len) (repeat z (Z.to_nat len))] /\
  rw_cells rsegs m (A + 24 + len) [CB (Z.to_nat (k - len)) (repeat z (Z.to_nat (k - len)))].
Proof.
  intros m A z k len H Hk.
  change [CB (Z.to_nat (k + 24)) (repeat z (Z.to_nat (k + 24)))]
    with ([] ++ CB (Z.to_nat (k + 24)) (repeat z (Z.to_nat (k + 24))) :: []) in H.
  apply (rw_cells_split_CB rsegs m A [] _ _ []
           [6%nat; 18%nat; Z.to_nat len; Z.to_nat (k - len)]) in H; [| cbn [sum_nat]; lia].
  cbn [mk_CB_cells app] in H. rewrite !bar_skipn_repeat, !bar_firstn_repeat in H.
  replace (Nat.min 6 (Z.to_nat (k + 24))) with 6%nat in H by lia.
  replace (Nat.min 18 (Z.to_nat (k + 24) - 6)) with 18%nat in H by lia.
  replace (Nat.min (Z.to_nat len) (Z.to_nat (k + 24) - 6 - 18)) with (Z.to_nat len) in H by lia.
  replace (Nat.min (Z.to_nat (k - len)) (Z.to_nat (k + 24) - 6 - 18 - Z.to_nat len)) with (Z.to_nat (k - len))
    in H by lia.
  change (CB 6 (repeat z 6) :: CB 18 (repeat z 18) :: CB (Z.to_nat len) (repeat z (Z.to_nat len)) ::
          CB (Z.to_nat (k - len)) (repeat z (Z.to_nat (k - len))) :: [])
    with ([CB 6 (repeat z 6)] ++ [CB 18 (repeat z 18)] ++ [CB (Z.to_nat len) (repeat z (Z.to_nat len))] ++
          [CB (Z.to_nat (k - len)) (repeat z (Z.to_nat (k - len)))]) in H.
  apply bar_rw_app in H. destruct H as [H0 H].
  apply bar_rw_app in H. destruct H as [H1 H].
  apply bar_rw_app in H. destruct H as [H2 H3].
  cbn [cells_size csize Nat.add] in H1, H2, H3.
  split; [exact H0|]. split; [replace (A + 6) with (A + Z.of_nat (6 + 0)) by lia; exact H1|]. split.
  - replace (A + 24) with (A + Z.of_nat (6 + 0) + Z.of_nat (18 + 0)) by lia. exact H2.
  - replace (A + 24 + len) with (A + Z.of_nat (6 + 0) + Z.of_nat (18 + 0) + Z.of_nat (Z.to_nat len + 0))
      by lia. exact H3.
Qed.

(* ==== the body's sum ==== *)

Lemma bar_u1_nat : forall (l : list byte) (k : nat) x, nth_error l k = Some x ->
  bytes_le_to_Z (firstn 1 (skipn k l)) = bv_unsigned x.
Proof.
  induction l as [|y l IH]; intros [|k] x H; cbn in H; try discriminate.
  - injection H as <-. cbn [skipn]. change (firstn 1 (y :: l)) with [y]. rewrite bytes_le_to_Z_le_val.
    cbn [map le_val]. lia.
  - cbn [skipn]. apply IH. exact H.
Qed.

Lemma bar_firstn_S : forall (l : list byte) n x, nth_error l n = Some x -> firstn (S n) l = firstn n l ++ [x].
Proof.
  induction l as [|y l IH]; intros [|n] x H; cbn in H; try discriminate.
  - injection H as <-. reflexivity.
  - change (firstn (S (S n)) (y :: l)) with (y :: firstn (S n) l). rewrite (IH n x H). reflexivity.
Qed.

(* The loop adds one byte of the body per turn: the byte at i is u_at body i 1. *)
Lemma bar_sum_step : forall (l : list byte) i, 0 <= i < Z.of_nat (length l) ->
  sum_bytes (firstn (Z.to_nat (i + 1)) l) = sum_bytes (firstn (Z.to_nat i) l) + u_at l i 1.
Proof.
  intros l i Hi.
  destruct (nth_error l (Z.to_nat i)) as [x|] eqn:E; [| apply nth_error_None in E; lia].
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite (bar_firstn_S l _ x E), sum_bytes_app. cbn [sum_bytes].
  unfold u_at, sub. rewrite (bar_u1_nat l _ x E). unfold bz. lia.
Qed.

Lemma bar_sum_range : forall l, 0 <= sum_bytes l <= 255 * Z.of_nat (length l).
Proof.
  induction l as [|x l IH]; cbn [sum_bytes length]; [lia|].
  pose proof (bv_unsigned_in_range 8 x) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  unfold bz. lia.
Qed.

Lemma bar_u1_range : forall (l : list byte) k, 0 <= u_at l k 1 < 256.
Proof. intros l k. pose proof (u_at_range l k 1) as R. change (2 ^ (8 * Z.of_nat 1)) with 256 in R. exact R. Qed.

Lemma bar_rd : forall m a bs k n, bytes_at rsegs m a bs -> 0 <= k -> k + Z.of_nat n <= Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (Z_to_bv 64 (a + k)) n = Some (sub bs k n).
Proof. intros m a bs k n H Hk Hn. apply (bytes_at_read rsegs m a bs k n H Hk). lia. Qed.

(* snez / seqz of a nonzero address (the UBSan pointer checks of the loop) *)
Lemma bar_snez_pos : forall t, 0 < t < 2 ^ 64 -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 t) = Z_to_bv 64 1.
Proof.
  intros t Ht. rewrite v_sltu_b2z. rewrite !unsigned_lit by lia.
  replace (0 <? t) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma bar_seqz_pos : forall t, 0 < t < 2 ^ 64 -> v_sltiu (Z_to_bv 64 t) 1 = Z_to_bv 64 0.
Proof.
  intros t Ht. rewrite v_sltiu_b2z. rewrite unsigned_lit by lia. change (bv_wrap 64 1) with 1.
  replace (t <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

(* ==== words ==== *)

Lemma bar_ltu : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by assumption. reflexivity. Qed.

Lemma bar_eqb : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit by assumption. reflexivity. Qed.


(* A branch whose condition the context decides. *)
Ltac bar_br v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; unfold_cond; fold_lit_ux; rewrite ?unsigned_lit by lia; solve_cond_rec]
  end.

Ltac cur_mem := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => mm end.

(* bv_unsigned (Z_to_bv 64 z) is z, innermost first (lia proves each range from the context). *)
Ltac bar_ul := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
  lazymatch z with context [bv_unsigned (Z_to_bv 64 _)] => fail | _ => rewrite (unsigned_lit z) by lia end end.
Ltac bar_ul_in H := repeat match type of H with context [bv_unsigned (Z_to_bv 64 ?z)] =>
  lazymatch z with context [bv_unsigned (Z_to_bv 64 _)] => fail | _ => rewrite (unsigned_lit z) in H by lia end end.

(* The kit computes an address sp + c as one literal c: fold A + c1 + c2 in a cell's base the same way. *)
Ltac bar_fold H := repeat match type of H with context [Z.add (Z.add ?X ?c1) ?c2] =>
  is_Zlit c1; is_Zlit c2; let v := eval vm_compute in (c1 + c2) in
  replace (Z.add (Z.add X c1) c2) with (Z.add X v) in H by lia end.

(* A UBSan check that branches to the trap at 0x1644c: the context refutes its condition. *)
Ltac trapf := step; bar_br false.
Ltac bar_brf tac := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota | symmetry; tac] end.

(* ==== the bytes the walk leaves in frame[] ==== *)

(* a | b is a + b when a has no bit below 2^n and b none above (U/KindBGlue.v kb_lor_low) *)
Lemma bar_lor_low : forall a b n, 0 <= n -> 0 <= a -> 0 <= b < 2 ^ n -> a mod 2 ^ n = 0 -> Z.lor a b = a + b.
Proof.
  intros a b n Hn Ha Hb Hm.
  assert (HL : Z.land a b = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i n) as [Hlt|Hge].
    - rewrite <- (Z.mod_pow2_bits_low a n i Hlt), Hm, Z.bits_0. reflexivity.
    - rewrite <- (Z.mod_small b (2 ^ n)) by lia. rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r. }
  rewrite <- Z.lxor_lor by exact HL. symmetry. apply Z.add_nocarry_lxor. exact HL.
Qed.

Lemma bar_b8u : forall z, bv_unsigned (Z_to_bv 8 z) = z mod 256.
Proof. intros z. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma bar_byte_rng : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. exact R. Qed.

Lemma bar_shl : forall x n, 0 <= n -> Z.shiftl x n = x * 2 ^ n.
Proof. intros x n Hn. apply Z.shiftl_mul_pow2. exact Hn. Qed.

(* frame[0 .. 5]: the word sw stores (dst[0 .. 3], packed by lbu / slli / or) and the halfword sh stores
   (dst[4 .. 5]) are dst's six bytes *)
Lemma bar_dst : forall d0 d1 d2 d3 d4 d5 : byte,
  le4 (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb d3)) 24)))
                                                        (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb d2)) 16))))))
                            (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb d1)) 8)))
                                                            (bv_unsigned (zxb d0))))))) ++
  le2 (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb d5)) 8))) (bv_unsigned (zxb d4)))) =
  [d0; d1; d2; d3; d4; d5].
Proof.
  intros d0 d1 d2 d3 d4 d5.
  pose proof (bar_byte_rng d0). pose proof (bar_byte_rng d1). pose proof (bar_byte_rng d2).
  pose proof (bar_byte_rng d3). pose proof (bar_byte_rng d4). pose proof (bar_byte_rng d5).
  unfold zxb. bar_ul.
  rewrite !bar_shl by lia. change (2 ^ 24) with 16777216. change (2 ^ 16) with 65536. change (2 ^ 8) with 256.
  bar_ul.
  rewrite (bar_lor_low (bv_unsigned d3 * 16777216) (bv_unsigned d2 * 65536) 24) by (try lia; Z.div_mod_to_equations; lia).
  rewrite (bar_lor_low (bv_unsigned d1 * 256) (bv_unsigned d0) 8) by (try lia; Z.div_mod_to_equations; lia).
  rewrite (bar_lor_low (bv_unsigned d5 * 256) (bv_unsigned d4) 8) by (try lia; Z.div_mod_to_equations; lia).
  bar_ul.
  rewrite (bar_lor_low (bv_unsigned d3 * 16777216 + bv_unsigned d2 * 65536) (bv_unsigned d1 * 256 + bv_unsigned d0) 16)
    by (try lia; Z.div_mod_to_equations; lia).
  unfold le4, le2. bar_ul.
  apply bytes_eq_of_zs. cbn [Z_to_le_bytes app map]. rewrite !bar_b8u. rewrite !Z.shiftr_div_pow2 by lia.
  change (2 ^ 8) with 256.
  repeat (apply (f_equal2 cons)); try reflexivity; Z.div_mod_to_equations; lia.
Qed.

Lemma bar_dst_app : forall d0 d1 d2 d3 d4 d5 : byte, forall rest,
  le4 (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb d3)) 24)))
                                                        (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb d2)) 16))))))
                            (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb d1)) 8)))
                                                            (bv_unsigned (zxb d0))))))) ++
  le2 (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb d5)) 8))) (bv_unsigned (zxb d4)))) ++ rest =
  [d0; d1; d2; d3; d4; d5] ++ rest.
Proof. intros. rewrite app_assoc, bar_dst. reflexivity. Qed.

(* frame[12 .. 29] as the 18 byte stores leave them: SPEC_ETHERTYPE, SPEC_HDR + len, the sum, send (its upper 16
   bits stored as zeros: send < 2^16), ack, retry (its upper byte stored as zero: retry < 2^8), cmd, ncmds 1 *)
Lemma bar_hdr : forall (len s : Z) (a2 a3 : word) send ack retry cmd,
  0 <= len <= 1484 -> 0 <= s < 2 ^ 62 -> bv_unsigned a2 mod 2 ^ 32 = send -> 0 <= send < 2 ^ 16 ->
  bv_unsigned a3 mod 2 ^ 32 = ack -> 0 <= retry < 2 ^ 8 -> 0 <= cmd < 2 ^ 8 ->
  cells_bytes
    [C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 136))); C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 95)));
     C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (len + 16))) 8))));
     C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (len + 16))));
     C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 s)) 8))));
     C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 s)));
     C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0))); C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0)));
     C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned a2) 8)))); C1 (Z_to_bv 8 (bv_unsigned a2));
     C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned a3) 24))));
     C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned a3) 16))));
     C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned a3) 8)))); C1 (Z_to_bv 8 (bv_unsigned a3));
     C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0))); C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 retry)));
     C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 cmd))); C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1)))] =
  put16 0x885f ++ put16 (16 + len) ++ put16 (s mod 2 ^ 16) ++ put32 send ++ put32 ack ++ put16 retry ++
  [b8 cmd; b8 1].
Proof.
  intros len s a2 a3 send ack retry cmd Hl Hs H2 Hsd H3 Hr Hc.
  pose proof (bv_unsigned_in_range 64 a2) as R2. pose proof (bv_unsigned_in_range 64 a3) as R3.
  unfold bv_modulus in R2, R3. change (2 ^ Z.of_N 64) with (2 ^ 64) in R2, R3.
  rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 24) with 16777216 in *. change (2 ^ 16) with 65536 in *.
  change (2 ^ 8) with 256 in *. change (2 ^ 32) with 4294967296 in *.
  bar_ul.
  rewrite ?(unsigned_lit (bv_unsigned a2 / 256)) by (Z.div_mod_to_equations; lia).
  rewrite ?(unsigned_lit (bv_unsigned a3 / 256)) by (Z.div_mod_to_equations; lia).
  rewrite ?(unsigned_lit (bv_unsigned a3 / 65536)) by (Z.div_mod_to_equations; lia).
  rewrite ?(unsigned_lit (bv_unsigned a3 / 16777216)) by (Z.div_mod_to_equations; lia).
  rewrite ?(unsigned_lit ((len + 16) / 256)) by (Z.div_mod_to_equations; lia).
  rewrite ?(unsigned_lit (s / 256)) by (Z.div_mod_to_equations; lia).
  apply bytes_eq_of_zs. unfold put16, put32, b8. cbn [cells_bytes cbytes app map]. rewrite !bar_b8u.
  change (2 ^ 24) with 16777216. change (2 ^ 16) with 65536. change (2 ^ 8) with 256.
  repeat (apply (f_equal2 cons)); try reflexivity; Z.div_mod_to_equations; lia.
Qed.

Lemma bar_cells_bytes : forall m A cs, rw_cells rsegs m A cs -> bytes_at rsegs m A (cells_bytes cs).
Proof. intros m A cs [[_ H] _]. exact H. Qed.

(* The frame's pieces at the call of receive, as one byte list at frame = A0 + 20: frame[0 .. 5] (the word and the
   halfword stored at A0 + 20, A0 + 24), src (A1), the header cells (A2), the body (A3), memset's zeros (A4). *)
Lemma bar_frame_cells : forall m A0 A1 A2 A3 A4 j w w' n1 src hcs nb body np pad,
  rw_cells rsegs m A0 [CB 20 j; C4 w; C2 w'] -> rw_cells rsegs m A1 [CB n1 src] ->
  rw_cells rsegs m A2 hcs -> rw_cells rsegs m A3 [CB nb body] -> rw_cells rsegs m A4 [CB np pad] ->
  A1 = A0 + 26 -> A2 = A1 + Z.of_nat n1 -> A3 = A2 + Z.of_nat (cells_size hcs) -> A4 = A3 + Z.of_nat nb ->
  bytes_at rsegs m (A0 + 20) (le4 w ++ le2 w' ++ src ++ cells_bytes hcs ++ body ++ pad).
Proof.
  intros m A0 A1 A2 A3 A4 j w w' n1 src hcs nb body np pad H0 H1 H2 H3 H4 E1 E2 E3 E4.
  pose proof H0 as [[W0 _] _]. cbn [cells_wf cell_wf] in W0. destruct W0 as [Lj _].
  pose proof H1 as [[W1 _] _]. cbn [cells_wf cell_wf] in W1. destruct W1 as [Ls _].
  pose proof H2 as [[W2 _] _].
  pose proof H3 as [[W3 _] _]. cbn [cells_wf cell_wf] in W3. destruct W3 as [Lb _].
  apply bar_cells_bytes in H0, H1, H2, H3, H4. cbn [cells_bytes cbytes] in H0, H1, H3, H4.
  rewrite app_nil_r in H1, H3, H4.
  apply bytes_at_app in H0. destruct H0 as [_ H0]. rewrite Lj in H0. rewrite app_nil_r in H0.
  assert (L6 : length (le4 w ++ le2 w') = 6%nat) by (rewrite length_app, length_le4, length_le2; reflexivity).
  assert (LH : length (cells_bytes hcs) = cells_size hcs) by (apply cells_bytes_length; exact W2).
  rewrite app_assoc. apply bytes_at_app. split; [exact H0|]. rewrite L6.
  replace (A0 + 20 + Z.of_nat 6) with A1 by lia.
  apply bytes_at_app. split; [exact H1|]. rewrite Ls. rewrite <- E2.
  apply bytes_at_app. split; [exact H2|]. rewrite LH. rewrite <- E3.
  apply bytes_at_app. split; [exact H3|]. rewrite Lb. rewrite <- E4. exact H4.
Qed.

(* ==== the walk from the entry to the call of receive ==== *)

(* The state at receive's entry (0x14d1c, ra = 0x1641c, sp - 1616): receive(frame, n, 0, 0) with frame at
   sp - 1596 holding the n bytes spec_build_frame writes, the saved registers at sp - 80, the callee-saved registers
   s0 .. s8 as the walk set them (len, body, cmd, retry, ack, send, src, frame, max 30 len), the frame's footprint. *)
Definition bar_at_recv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (Bw : list byte) (dst src body : list byte)
    (bodyp srcp send ack retry cmd : Z) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms = MS (mkR (Z_to_bv 64 0x1641c) (Z_to_bv 64 (bv_unsigned sp + -1616)) gp tp t0 t1 t2
               (Z_to_bv 64 (Z.of_nat (length body))) (Z_to_bv 64 bodyp) (Z_to_bv 64 (bv_unsigned sp + -1596))
               (Z_to_bv 64 (Z.max 30 (Z.of_nat (length body)) + 30)) (Z_to_bv 64 0) (Z_to_bv 64 0) a4 a5 a6 a7
               (Z_to_bv 64 cmd) (Z_to_bv 64 retry) a3 a2 (Z_to_bv 64 srcp) (Z_to_bv 64 (bv_unsigned sp + -1596))
               (Z_to_bv 64 (Z.max 30 (Z.of_nat (length body)))) s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x14d1c) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp + -1616, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    bytes_at rsegs m' (bv_unsigned sp + -1596) (fst (spec_build_frame dst src send ack retry cmd 1 body 0)) /\
    ro_cells rsegs m' (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
    wmem rsegs m' Bw.

(* 0x161ac .. 0x16418: the prologue, the frame build (memset, dst's bytes, memcpy of src, the header's byte stores,
   the body's sum, memcpy of the body when len <> 0) and the call of receive, every UBSan check (a branch to the
   trap at 0x1644c) refuted. dst and src are the 6 bytes below 2^20 (.rodata); bq is where the body's bytes lie
   (the body when len <> 0), off the frame [sp - 1616, sp). *)
Lemma bar_walk : memset_contract -> memcpy_contract ->
  forall (dstp srcp bodyp bq : Z) (d0 d1 d2 d3 d4 d5 : byte) (src body : list byte) (send ack retry cmd : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Bw : list byte),
  0 <= dstp -> dstp + 6 <= 2 ^ 20 -> bytes_at rsegs m dstp [d0; d1; d2; d3; d4; d5] ->
  0 <= srcp -> srcp + 6 <= 2 ^ 20 -> bytes_at rsegs m srcp src -> length src = 6%nat ->
  bv_unsigned a2 mod 2 ^ 32 = send -> 0 <= send < 2 ^ 16 ->
  bv_unsigned a3 mod 2 ^ 32 = ack ->
  0 <= retry < 2 ^ 8 -> 0 <= cmd < 2 ^ 8 ->
  Z.of_nat (length body) <= 1484 ->
  0 <= bodyp < 2 ^ 64 ->
  (length body = 0%nat \/ (bq = bodyp /\ 0 < bodyp)) ->
  bytes_at rsegs m bq body ->
  (bq + Z.of_nat (length body) <= bv_unsigned sp - 1616 \/ bv_unsigned sp <= bq) ->
  bv_unsigned sp mod 16 = 0 -> 2 ^ 20 <= bv_unsigned sp - 1616 -> bv_unsigned sp < 2 ^ 63 ->
  stk rsegs m (bv_unsigned sp - 1616) (bv_unsigned sp) ->
  W_BASE_UBSAN + W_LEN <= bv_unsigned sp - 1616 ->
  wmem rsegs m Bw ->
  mem_inv rsegs m ->
  evt rsegs (bar_at_recv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 F fc m Bw [d0; d1; d2; d3; d4; d5]
               src body bodyp srcp send ack retry cmd)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 dstp) (Z_to_bv 64 srcp) a2 a3 (Z_to_bv 64 retry)
           (Z_to_bv 64 cmd) (Z_to_bv 64 bodyp) (Z_to_bv 64 (Z.of_nat (length body))) s2 s3 s4 s5 s6 s7 s8 s9 s10
           s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x161ac) fc None m (seg_rom rsegs)).
Proof.
  intros MEMSET MEMCPY dstp srcp bodyp bq d0 d1 d2 d3 d4 d5 src body send ack retry cmd
    ra sp gp tp t0 t1 t2 s0 s1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Bw
    D0 D6 HD S0 S6 HS LS A2 RS A3 RR RC LB RB BQ HB BQD SP16 SPL SPH ST WO WM MI.
  lazymatch goal with |- evt _ ?QQ _ => set (Q := QQ) end.
  wk_facts.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 1616, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMo.
  set (len := Z.of_nat (length body)) in *.
  assert (Rl : 0 <= len <= 1484) by (unfold len in *; lia).
  set (k := Z.max 30 len).
  assert (Ek : k = Z.max 30 len) by reflexivity. clearbody k.
  assert (Rk : 30 <= k <= 1484) by lia.
  (* dst's six bytes as one-byte cells, which the loads below read *)
  assert (RD : ro_cells rsegs m dstp [C1 d0; C1 d1; C1 d2; C1 d3; C1 d4; C1 d5])
    by (split; [cbn; tauto | exact HD]).
  clear HD.
  carve_frame 1616%nat ST.
  (* 0x161ac addi sp,sp,-1616; 0x161b0 .. 0x161d4: sd ra, s0 .. s8 *)
  do 11 step.
  (* 0x161d8 .. 0x161fc: the arguments into s0 .. s7 (s0 = len, s1 = body, s2 = cmd, s3 = retry, s4 = ack,
     s5 = send, s6 = src, s7 = dst), a0 = 30, s8 = len *)
  do 10 step.
  (* 0x16200 bltu a0,a7 / 0x16204 li s8,30: s8 = max 30 len = k on both paths, joined at 0x16208 *)
  step.
  let mm := cur_mem in
  assert (J : evt rsegs Q
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -1616)) gp tp t0 t1 t2 (Z_to_bv 64 len) (Z_to_bv 64 bodyp)
           (Z_to_bv 64 30) (Z_to_bv 64 srcp) a2 a3 (Z_to_bv 64 retry) (Z_to_bv 64 cmd) (Z_to_bv 64 bodyp)
           (Z_to_bv 64 len) (Z_to_bv 64 cmd) (Z_to_bv 64 retry) a3 a2 (Z_to_bv 64 srcp) (Z_to_bv 64 dstp)
           (Z_to_bv 64 k) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16208) fc None mm (seg_rom rsegs))).
  2: { destruct (Z.ltb_spec 30 len) as [L30|L30].
       - bar_br true. replace (Z_to_bv 64 k) with (Z_to_bv 64 len) in J by (f_equal; lia). exact J.
       - bar_br false. step. replace (Z_to_bv 64 k) with (Z_to_bv 64 30) in J by (f_equal; lia).
         exact J. }
  apply (bar_split_frame _ _ _ _ k) in FR; [| exact Rk]. destruct FR as (FR0 & MSP & FR2 & SAV).
  bar_fold MSP. bar_fold FR2. bar_fold SAV.
  (* 0x16208 .. 0x16210: a2 = k + 24, a0 = sp + 26, a1 = 0; 0x16214 jal memset (sp + 26, 0, k + 24) *)
  do 4 step.
  let mm := cur_mem in
  eapply evt_cut;
  [ eapply MEMSET; [ bar_ul; exact MSP | exact MI ]
  | intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & -> & MUc & WMc & MI2 & Z0);
    bar_ul_in MUc; bar_ul_in Z0;
    transport_after_call rsegs mm m2 MUc WMc; clear MUc WMc;
    try match goal with H : mem_inv rsegs mm |- _ => clear H end; try clear mm ].
  rewrite (ret_pc_even 90648) by (first [lia | reflexivity]).
  apply (bar_split_zero _ _ _ k len) in Z0; [| lia]. destruct Z0 as (ZS & ZH & ZB & ZP).
  bar_fold ZH. bar_fold ZB. bar_fold ZP.
  (* 0x16218 .. 0x16254: dst's bytes into a1 (dst[0 .. 3]) and a0 (dst[4 .. 5]), a3 = -6, s7 = sp + 20;
     0x16258 sw a1,20(sp); 0x1625c sh a0,24(sp): frame[0 .. 5] = dst *)
  do 18 step.
  (* 0x16260 bgeu s7,a3: the pointer-overflow check of frame + 6 (sp + 20 < 2^64 - 6) *)
  trapf.
  (* 0x16264 .. 0x1626c: a0 = sp + 26, a2 = 6, a1 = src; 0x16270 jal memcpy (frame + 6, src, 6) *)
  do 4 step.
  let mm := cur_mem in
  eapply evt_cut;
  [ eapply MEMCPY; [ bar_ul; exact HS | bar_ul; exact LS | bar_ul; exact ZS | bar_ul; lia | assumption ]
  | intros ms' (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m3 & -> & MUc & WMc
      & MI3 & CS & SRC3);
    bar_ul_in MUc; bar_ul_in CS; clear SRC3;
    transport_after_call rsegs mm m3 MUc WMc; clear MUc WMc;
    try match goal with H : mem_inv rsegs mm |- _ => clear H end; try clear mm ].
  rewrite (ret_pc_even 90740) by (first [lia | reflexivity]).
  (* 0x16274 .. 0x162c8: frame[12 .. 15] = 0x88, 0x5f, (len + 16) >> 8, len + 16, each store after its UBSan
     pointer check (frame + 13, frame + 15, frame + 17 below 2^64, frame + 12, frame + 14 not 2^64 - 1) *)
  step. trapf. do 4 step. trapf. do 4 step. trapf. do 5 step. trapf. do 3 step. trapf.
  (* 0x162cc mv a0,zero; 0x162d0 beqz s0: the body's sum in a0, or 0 when len = 0, joined at 0x16310 *)
  step. step.
  let mm := cur_mem in
  assert (J2 : forall r10 r11 r12 r13 r14 r15 : word, r10 = Z_to_bv 64 (sum_bytes body) ->
    evt rsegs Q
      (MS (mkR (Z_to_bv 64 90740) (Z_to_bv 64 (bv_unsigned sp + -1616)) gp tp q5 q6 q7 (Z_to_bv 64 len)
             (Z_to_bv 64 bodyp) r10 r11 r12 r13 r14 r15 q16 q17 (Z_to_bv 64 cmd) (Z_to_bv 64 retry) a3 a2
             (Z_to_bv 64 srcp) (Z_to_bv 64 (bv_unsigned sp + -1596)) (Z_to_bv 64 k) s9 s10 s11 q28 q29 q30 q31)
          F (Z_to_bv 64 90896) fc None mm (seg_rom rsegs))).
  2: { destruct (Z.eqb_spec len 0) as [L0|L0].
    - (* len = 0: the body is empty, its sum 0 *)
      bar_br true. eapply J2. unfold len in L0. destruct body; [reflexivity | cbn in L0; lia].
    - (* 0x162d4 snez a1,s1; 0x162d8 .. 0x162e0: a2 = a3 = body, a4 = len; the loop at 0x162e4, i bytes added *)
      bar_br false. destruct BQ as [BQ | [-> BQ]]; [unfold len in L0; lia|].
      pose proof (bytes_at_bound rsegs _ _ _ HB) as HBB. fold len in HBB.
      let mm := cur_mem in
      assert (LOOP : forall (n : nat) (i : Z) (r10 r11 r12 r13 r14 r15 : word),
        Z.of_nat n = len - i -> 0 <= i < len ->
        r10 = Z_to_bv 64 (sum_bytes (firstn (Z.to_nat i) body)) -> r11 = Z_to_bv 64 1 ->
        r12 = Z_to_bv 64 (bodyp + i) -> r13 = Z_to_bv 64 (bodyp + i) -> r14 = Z_to_bv 64 (len - i) ->
        evt rsegs Q
          (MS (mkR (Z_to_bv 64 90740) (Z_to_bv 64 (bv_unsigned sp + -1616)) gp tp q5 q6 q7 (Z_to_bv 64 len)
                 (Z_to_bv 64 bodyp) r10 r11 r12 r13 r14 r15 q16 q17 (Z_to_bv 64 cmd) (Z_to_bv 64 retry) a3 a2
                 (Z_to_bv 64 srcp) (Z_to_bv 64 (bv_unsigned sp + -1596)) (Z_to_bv 64 k) s9 s10 s11 q28 q29 q30 q31)
              F (Z_to_bv 64 90852) fc None mm (seg_rom rsegs))).
      { induction n as [|n IH]; intros i r10 r11 r12 r13 r14 r15 Hn Hi -> -> -> -> ->; [lia|].
        pose proof (bar_sum_range (firstn (Z.to_nat i) body)) as SR.
        rewrite length_firstn in SR.
        pose proof (bar_u1_range body i) as UR.
        (* 0x162e4 bltu a3,s1: body + i does not wrap *)
        trapf.
        (* 0x162e8 seqz a5,a3; 0x162ec xor a5,a1,a5; 0x162f0 beqz a5: body + i is not NULL *)
        do 3 step.
        bar_brf ltac:(rewrite bar_seqz_pos by lia; reflexivity).
        (* 0x162f4 beqz s1: body is not NULL *)
        trapf.
        (* 0x162f8 lbu a5,0(a2): body[i] *)
        let mm := cur_mem in pose proof (bar_rd mm bodyp body i 1 HB ltac:(lia) ltac:(lia)) as RD1.
        step. rewrite wm_lbu. clear RD1.
        (* 0x162fc .. 0x16308: a4 = len - i - 1, a3 = body + i + 1, a0 += body[i], a2 = body + i + 1 *)
        do 4 step.
        (* 0x1630c bnez a4 *)
        step.
        rewrite bar_eqb by lia.
        destruct (Z.eqb_spec (len - i + -1) 0) as [E|E]; cbn [negb]; cbv iota.
        - (* the last byte: the sum of the whole body *)
          apply J2. f_equal. rewrite <- bar_sum_step by (unfold len in *; lia).
          replace (Z.to_nat (i + 1)) with (length body) by (unfold len in *; lia).
          rewrite firstn_all. reflexivity.
        - apply (IH (i + 1));
            [ lia | lia | f_equal; rewrite bar_sum_step by (unfold len in *; lia); reflexivity | reflexivity
            | f_equal; lia | f_equal; lia | f_equal; lia ]. }
      do 4 step.
      apply (LOOP (Z.to_nat len) 0); [lia | lia | reflexivity | rewrite bar_snez_pos by lia; reflexivity
        | f_equal; lia | f_equal; lia | f_equal; lia]. }
  intros r10 r11 r12 r13 r14 r15 ->.
  (* 0x16310 .. 0x163e4: frame[16 .. 29] = sum >> 8, sum, 0, 0, send >> 8, send, ack >> 24, ack >> 16, ack >> 8,
     ack, 0, retry, cmd, 1, each store after its UBSan pointer check (frame + c below 2^64, or not 2^64 - 1) *)
  do 4 step. trapf. do 3 step. trapf. do 3 step. trapf. do 2 step. trapf. do 3 step. trapf. do 3 step. trapf.
  do 4 step. trapf. do 3 step. trapf. do 3 step. trapf. do 3 step. trapf. do 3 step. trapf. do 3 step. trapf.
  do 2 step. trapf. do 2 step.
  (* 0x163e8 beqz s0: the body is copied only when len <> 0 *)
  step.
  destruct (Z.eqb_spec len 0) as [L0|L0].
  (* len = 0: frame[30 ..] keeps memset's zeros, none of them the body's *)
  1: (bar_br true;
      assert (EB : body = []) by (unfold len in L0; destruct body; [reflexivity | cbn in L0; lia]);
      replace (repeat _ (Z.to_nat len)) with body in ZB by (rewrite EB, L0; reflexivity)).
  (* 0x163ec .. 0x163f4: the pointer-overflow check of frame + 31 (bltu a1,a0, a1 = -31); 0x163f8 .. 0x16404:
     memcpy (frame + 30, body, len) *)
  2: (bar_br false; destruct BQ as [BQ | [-> BQ]]; [unfold len in L0; lia|];
      do 2 step; trapf; do 4 step;
      let mm := cur_mem in
      eapply evt_cut;
      [ eapply MEMCPY; [ bar_ul; exact HB | bar_ul; unfold len; lia | bar_ul; exact ZB | bar_ul; lia | assumption ]
      | intros ms' (p5 & p6 & p7 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p28 & p29 & p30 & p31 & m4 & -> & MUc
          & WMc & MI4 & CB4 & BOD4);
        bar_ul_in MUc; bar_ul_in CB4; clear BOD4;
        transport_after_call rsegs mm m4 MUc WMc; clear MUc WMc;
        try match goal with H : mem_inv rsegs mm |- _ => clear H end; try clear mm ];
      rewrite (ret_pc_even 91144) by (first [lia | reflexivity]);
      rename CB4 into ZB).
  (* 0x16408 .. 0x16414: a1 = k + 30 (the frame's length), a0 = frame, a2 = a3 = 0; 0x16418 jal receive *)
  all: do 5 step.
  all: subst k.
  all: pose proof (bar_sum_range body) as SRb.
  (* the n bytes at frame are fst (spec_build_frame dst src send ack retry cmd 1 body 0) *)
  all: let mm := cur_mem in
    assert (FRM : bytes_at rsegs mm (bv_unsigned sp + -1596)
                    (fst (spec_build_frame [d0; d1; d2; d3; d4; d5] src send ack retry cmd 1 body 0)))
      by (pose proof (bar_frame_cells _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR0 CS ZH ZB ZP ltac:(lia) ltac:(lia)
            ltac:(cbn [cells_size csize Nat.add]; lia) ltac:(unfold len; lia)) as FC;
          bar_fold FC;
          rewrite bar_dst_app in FC;
          rewrite (bar_hdr len (sum_bytes body) a2 a3 send ack retry cmd) in FC
            by (first [assumption | unfold len in *; lia]);
          eapply bytes_at_ext; [exact FC |];
          rewrite bar_frame_eq by (first [reflexivity | exact LS]);
          rewrite <- !app_assoc; unfold sum16, len; repeat f_equal; lia).
  all: apply evt_done; unfold Q, bar_at_recv.
  all: do 12 eexists; split; [reflexivity |].
  all: split; [exact MU |]; split; [exact WMo |]; split; [assumption |]; split; [exact FRM |].
  all: split; [exact (proj1 SAV) | exact WM].
Qed.

(* 0x1641c .. 0x16448: the saved registers back, the frame popped, ret. *)
Lemma bar_epi : forall (sp0 : word) (x1 gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24
    s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte),
  bv_unsigned sp0 + 1616 < 2 ^ 64 ->
  ro_cells rsegs m (bv_unsigned sp0 + 1536) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  evt rsegs (fun ms => ms = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 + 1616)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6
                                  a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (ret_pc ra) fc None m (seg_rom rsegs))
    (MS (mkR x1 sp0 gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1641c) fc None m (seg_rom rsegs)).
Proof.
  intros sp0 x1 gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 t3 t4 t5 t6
    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 F fc m Hsp SAV.
  pose proof (bv_unsigned_in_range 64 sp0) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2 ^ 64) in R.
  do 12 step.
  apply evt_done. reflexivity.
Qed.

(* ==== the SR and SRcf contracts: the walk, receive (U/Prog/T/receive_c.v) and the epilogue, composed by U/Prog/T/TSRGlue.v ==== *)
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Contract Img0 SlotAgree AgreeLift.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require RoAdapt.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TImg TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU TContract receive_c
  build_and_receive_c TSRGlue.

(* ==== memory facts the SR steps carry ==== *)

(* A read-only address lies in a segment, below SR_RES_TOP. *)
Lemma bar_ro_low : forall z, Mem.ro_addr rsegs (Z_to_bv 64 z) = true -> bv_unsigned (Z_to_bv 64 z) + 1 <= SR_RES_TOP.
Proof.
  intros z H. unfold Mem.ro_addr in H.
  destruct (find_segment rsegs (bv_unsigned (Z_to_bv 64 z)) 1) as [seg|] eqn:E; [|discriminate H].
  exact (sr_find_top _ _ _ E).
Qed.

Lemma bar_blk_bytes : forall (B : malloc_syms) m A bs, ms_segs B = rsegs -> 0 <= A ->
  A + Z.of_nat (length bs) <= 2 ^ 64 -> blk_data B m A bs -> bytes_at rsegs m A bs.
Proof.
  intros B m A bs HS H0 H1 HD. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  pose proof (HD (Z.of_nat i) ltac:(lia)) as E. rewrite Nat2Z.id in E. rewrite <- E, HS. reflexivity.
Qed.

Lemma bar_bytes_blk : forall (B : malloc_syms) m A bs, ms_segs B = rsegs -> bytes_at rsegs m A bs -> blk_data B m A bs.
Proof.
  intros B m A bs HS (H0 & H1 & Hb) i Hi. rewrite HS.
  pose proof (Hb (Z.to_nat i) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia. exact E.
Qed.

Lemma bar_bytes_frame : forall m m' A bs, bytes_at rsegs m A bs ->
  (forall a, A <= a < A + Z.of_nat (length bs) -> mbyte rsegs m' a = mbyte rsegs m a) -> bytes_at rsegs m' A bs.
Proof.
  intros m m' A bs (H0 & H1 & Hb) HE. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (Hb i Hi).
  change (Mem.mrd rsegs m' (wa (A + Z.of_nat i)) = Mem.mrd rsegs m (wa (A + Z.of_nat i))).
  exact (HE (A + Z.of_nat i) ltac:(lia)).
Qed.

(* A MAC of h_mac_at: 6 bytes below SR_RES_TOP at the unsigned address, in the normalized memory. *)
Lemma bar_mac : forall (B : malloc_syms) m p mac, ms_segs B = rsegs -> ro_agree rsegs m -> length mac = 6%nat ->
  blk_data B m p mac -> (forall i, 0 <= i < 6 -> Mem.ro_addr rsegs (Z_to_bv 64 (p + i)) = true) ->
  bv_unsigned (Z_to_bv 64 p) + 6 <= SR_RES_TOP /\
  bytes_at rsegs (normalize rsegs m) (bv_unsigned (Z_to_bv 64 p)) mac.
Proof.
  intros B m p mac HS HR HL HD HRO.
  set (p' := bv_unsigned (Z_to_bv 64 p)).
  assert (Ep : p' = p mod 2 ^ 64) by (unfold p'; apply unsigned_lit_wrap).
  pose proof (Z.mod_pos_bound p (2 ^ 64) ltac:(lia)) as Rp.
  assert (R0 := bar_ro_low _ (HRO 0 ltac:(lia))). rewrite Z.add_0_r in R0. fold p' in R0.
  assert (R5 := bar_ro_low _ (HRO 5 ltac:(lia))). rewrite unsigned_lit_wrap in R5.
  assert (E5 : (p + 5) mod 2 ^ 64 = p' + 5).
  { rewrite Ep, <- Zplus_mod_idemp_l. apply Z.mod_small. unfold SR_RES_TOP in R0. lia. }
  rewrite E5 in R5.
  split; [lia|].
  apply bytes_at_normalize; [exact HR|].
  split; [lia|]. split; [rewrite HL; unfold SR_RES_TOP in *; lia|]. intros i Hi. rewrite HL in Hi.
  pose proof (HD (Z.of_nat i) ltac:(rewrite HL; lia)) as E. rewrite Nat2Z.id in E. rewrite <- E, HS.
  unfold mbyte. change (Mem.mrd rsegs m (wa (p' + Z.of_nat i)) =
    match m (Z_to_bv 64 (p + Z.of_nat i)) with Some b => Some b | None => seg_rom rsegs (Z_to_bv 64 (p + Z.of_nat i)) end).
  replace (wa (p' + Z.of_nat i)) with (Z_to_bv 64 (p + Z.of_nat i)); [reflexivity|].
  apply bv_eq. unfold wa. rewrite !unsigned_lit_wrap. rewrite Ep, Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma bar_world_check : forallb (fun s => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? W_BASE_UBSAN)
    || (W_BASE_UBSAN + W_LEN <=? Z.of_N (seg_base s))) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

(* The world lies in a writable segment: no read-only address in it. *)
Lemma bar_world_not_ro : forall a, W_BASE_UBSAN <= a < W_BASE_UBSAN + W_LEN -> Mem.ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha. unfold Mem.ro_addr. rewrite unsigned_lit by (unfold W_BASE_UBSAN, W_LEN in *; lia).
  destruct (find_segment rsegs a 1) as [seg|] eqn:E; [|reflexivity].
  destruct (sr_find_segment_in rsegs a 1 seg E) as (Hin & H1 & H2).
  pose proof (proj1 (forallb_forall _ rsegs) bar_world_check seg Hin) as C. cbv beta in C.
  destruct (seg_writable seg); [reflexivity|]. cbn [orb] in C.
  apply orb_true_iff in C as [C|C]; apply Z.leb_le in C; unfold W_BASE_UBSAN, W_LEN in *; lia.
Qed.

Lemma bar_wmem_norm : forall m Bw, ro_agree rsegs m -> wmem rsegs m Bw -> wmem rsegs (normalize rsegs m) Bw.
Proof.
  intros m Bw HR WM. apply RoAdapt.rw_cells_norm; [exact HR | exact WM |].
  intros i Hi. cbn [cells_size csize] in Hi. unfold W_LEN in Hi. change (Z.of_nat (Z.to_nat 65616 + 0)) with 65616 in Hi.
  apply bar_world_not_ro. unfold W_BASE_UBSAN, W_LEN. lia.
Qed.

Lemma bar_relro_norm : forall m, relro_img m -> relro_img (normalize rsegs m).
Proof.
  intros m H i Hi. specialize (H i Hi). unfold Mem.mrd, normalize in *.
  destruct (Mem.ro_addr rsegs (wa (RELRO_BASE + i))); [reflexivity | exact H].
Qed.

Lemma bar_relro_rel : forall m m0, mem_rel rsegs m m0 -> relro_img m0 -> relro_img m.
Proof.
  intros m m0 HR H i Hi. specialize (H i Hi).
  change (mbyte rsegs m (RELRO_BASE + i) = seg_rom rsegs (wa (RELRO_BASE + i))).
  rewrite (mbyte_rel rsegs m m0 _ HR). exact H.
Qed.

(* ==== the run: the walk, receive, the epilogue, for SR and SRcf alike ==== *)

Section Gen.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis HGG : ms_got_guard B = H_GUARD_GOT.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis WORLD : forall a, h_world a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis RELRO : forall a, RELRO_BASE <= a < RELRO_BASE + RELRO_LEN ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis CTX_LOW : ms_ctx B + CTX_SIZE <= alloc_ceiling.   (* h_binds' ctx clause *)

(* SR rsegs or SRcf B; ROOM the matching budget *)
Variable X : config -> (config -> Prop) -> Prop.
Variable ROOM : Model -> sbound -> Z -> Prop.
Hypothesis X_bind : forall c (R Q : config -> Prop), X c R -> (forall c', R c' -> X c' Q) -> X c Q.
Hypothesis X_ret : forall c (Q : config -> Prop), Q c -> X c Q.
Hypothesis X_run : forall stk S L0 A0 mem0 md0 (fx' : FPState) regs pc mem md L A
    (Q : machine_state -> Prop) (P : config -> Prop),
  sr_fr B API stk S L0 A0 mem0 md0 L A mem md -> alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) (@fp_regs fx') pc (@fp_csr fx') None
                      (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R F pc' fc m' W, ms = MState.MS R F pc' fc None m' (seg_rom rsegs) /\
     Frame.munch W (normalize rsegs mem) m' /\ Frame.wmono rsegs (normalize rsegs mem) m' /\
     (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
        (S - stk <= x < S) \/ h_world x \/ exists y k, sr_mine L0 A0 L A y k /\ y <= x < y + k)) ->
  (forall R F pc' fc m0', Q (MState.MS R F pc' fc None m0' (seg_rom rsegs)) ->
     forall regs' m', Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m' m0' ->
     sr_fr B API stk S L0 A0 mem0 md0 L A m' md ->
     X (mkCfg (@mkst (mkFP F fc) regs' pc' m' (seg_rom rsegs)) md) P) ->
  X (mkCfg (@mkst fx' regs pc mem (seg_rom rsegs)) md) P.
Hypothesis X_recv : forall L A regs mem md b (Bw : list byte) (p : Z) (bytes : list byte) (by_poll pf : Z),
  h_pre B API receive_FRAME L A regs mem md b Bw -> frm_zero fp_csr ->
  receive_args B L A regs mem Bw p bytes by_poll pf -> ROOM md b (Z.max 1 (Z.of_nat (length bytes))) ->
  X (mkCfg (mkst regs (Z_to_bv 64 receive_ENTRY) mem (seg_rom rsegs)) md)
    (receive_ret B API L A regs mem md b Bw bytes by_poll pf).

Lemma bar_gen : memset_contract -> memcpy_contract ->
  forall L A regs mem md b (Bw : list byte) (dstp srcp bodyp : Z) (dst src body : list byte) (send ack retry cmd : Z),
    h_pre B API build_and_receive_FRAME L A regs mem md b Bw ->
    frm_zero fp_csr ->
    bar_args B L A regs mem Bw dstp srcp bodyp dst src body send ack retry cmd ->
    ROOM md b (Z.max 1 (bar_len dst src send ack retry cmd body)) ->
    X (mkCfg (mkst regs (Z_to_bv 64 build_and_receive_ENTRY) mem (seg_rom rsegs)) md)
      (bar_ret B API L A regs mem md b Bw dst src body send ack retry cmd).
Proof.
  intros MEMSET MEMCPY L A regs mem md b Bw dstp srcp bodyp dst src body send ack retry cmd HPRE FZ ARGS ROOMb.
  pose proof HPRE as (CPK & INIT & HALT & LAZY & ROA & RES & WOS & WMB & GF & RLR).
  pose proof CPK as (HM & HWF & HBD & RAOK & SP16 & SPLO & SPHI & STW & TPB & ERRW & _).
  destruct ARGS as (R10 & (LD & BD & ROD) & R11 & (LS & BS & ROS) & R12 & RS & R13 & RA & R14 & RR & R15 & RC
    & R16 & R17 & BB & HSRC & MODEL).
  rewrite SEGS in ROA.
  pose proof YM05.alloc_ceiling_value as ACV.
  unfold build_and_receive_FRAME, receive_FRAME, ALLOC_STACK, build_and_receive_ENTRY in *.
  unfold w_off_stack in WOS. unfold spZ in *.
  wk_facts.
  pose proof (wk_word_range (getr regs 2)) as RG2.
  assert (LB : Z.of_nat (length body) <= 1484).
  { specialize (MODEL 4096 ltac:(unfold h_addr_ok; lia)). unfold build_and_receive_m in MODEL.
    destruct (Z.ltb_spec SPEC_MAX_BODY (Z.of_nat (length body))) as [H|H]; [exfalso; apply MODEL; reflexivity|].
    unfold SPEC_MAX_BODY in H. lia. }
  destruct dst as [|d0 [|d1 [|d2 [|d3 [|d4 [|d5 [|? ?]]]]]]]; try (cbn in LD; discriminate LD).
  destruct (bar_mac B mem dstp _ SEGS ROA LD BD ROD) as (D6 & HD).
  destruct (bar_mac B mem srcp src SEGS ROA LS BS ROS) as (S6 & HSb).
  rewrite <- R10 in D6, HD. rewrite <- R11 in S6, HSb.
  (* where the body's bytes lie: nowhere (len = 0), a user block below the ceiling, or above sp *)
  assert (BODY : exists bq, (length body = 0%nat \/ (bq = bv_unsigned (getr regs 16) /\ 0 < bq)) /\
            bytes_at rsegs (normalize rsegs mem) bq body /\
            (bq + Z.of_nat (length body) <= bv_unsigned (getr regs 2) - 1616 \/ bv_unsigned (getr regs 2) <= bq)).
  { destruct HSRC as [H0 | (OW & [(q & k & Hin & H1 & H2) | (H1 & H2)])].
    - exists (bv_unsigned (getr regs 2)). split; [left; lia|]. split; [| right; lia].
      destruct body; [|cbn in H0; lia]. split; [lia|]. split; [cbn; lia|]. intros i Hi; cbn in Hi; lia.
    - pose proof (mr_blocks_range B _ (aa_laws API) _ _ _ _ q k HM Hin) as [Q1 Q2].
      assert (E16 : bv_unsigned (getr regs 16) = bodyp) by (rewrite R16; apply unsigned_lit; lia).
      exists bodyp. split; [right; split; [symmetry; exact E16 | lia]|]. split.
      + apply bytes_at_normalize; [exact ROA|]. apply (bar_blk_bytes B); [exact SEGS | lia | lia | exact BB].
      + left. lia.
    - assert (E16 : bv_unsigned (getr regs 16) = bodyp) by (rewrite R16; apply unsigned_lit; lia).
      exists bodyp. split; [right; split; [symmetry; exact E16 | lia]|]. split.
      + apply bytes_at_normalize; [exact ROA|]. apply (bar_blk_bytes B); [exact SEGS | lia | lia | exact BB].
      + right. lia. }
  destruct BODY as (bq & BQ & HB & BQD).
  pose proof (sr_fr_init B API SEGS _ _ _ _ _ _ _ _ HPRE) as FR0. unfold spZ in FR0.
  set (dp := bv_unsigned (getr regs 10)) in *.
  set (sq := bv_unsigned (getr regs 11)) in *.
  set (bp := bv_unsigned (getr regs 16)) in *.
  pose proof (wk_word_range (getr regs 10)) as RG10. fold dp in RG10.
  pose proof (wk_word_range (getr regs 11)) as RG11. fold sq in RG11.
  pose proof (wk_word_range (getr regs 16)) as RG16. fold bp in RG16.
  eapply (X_run 9936 (bv_unsigned (getr regs 2)) L A mem md fx regs (Z_to_bv 64 0x161ac) mem md L A
    (bar_at_recv (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 8) (getr regs 9)
       (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
       (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 12) (getr regs 13) fp_regs fp_csr
       (normalize rsegs mem) Bw [d0; d1; d2; d3; d4; d5] src body bp sq send ack retry cmd));
    [exact FR0 | lia | lia | | |].
  - (* the walk *)
    change (Regs6ss.mkR_of regs) with
      (mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
           (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
           (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
           (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
           (getr regs 29) (getr regs 30) (getr regs 31)).
    rewrite R14, R15, R17.
    replace (getr regs 10) with (Z_to_bv 64 dp) by (apply Z_to_bv_bv_unsigned).
    replace (getr regs 11) with (Z_to_bv 64 sq) by (apply Z_to_bv_bv_unsigned).
    replace (getr regs 16) with (Z_to_bv 64 bp) by (apply Z_to_bv_bv_unsigned).
    eapply (bar_walk MEMSET MEMCPY dp sq bp bq d0 d1 d2 d3 d4 d5 src body send ack retry cmd);
      try eassumption; try lia.
    + unfold SR_RES_TOP in D6. lia.
    + unfold SR_RES_TOP in S6. lia.
    + apply (norm_stk B); [exact SEGS | exact ROA | unfold SR_RES_TOP; lia | lia |].
      intros a Ha. apply STW. lia.
    + apply bar_wmem_norm; assumption.
    + apply mem_inv_normalize.
  - (* the run's footprint: the frame *)
    intros ms (t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WMo & _).
    do 6 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WMo|].
    intros x Hx NO. left.
    destruct (Z_lt_le_dec x (bv_unsigned (getr regs 2) + -1616)) as [Hl|Hl];
      [exfalso; apply NO; cbn [Frame.outside]; split; [lia | exact I] |].
    destruct (Z_lt_le_dec x (bv_unsigned (getr regs 2))) as [Hh|Hh];
      [lia | exfalso; apply NO; cbn [Frame.outside]; split; [lia | exact I]].
  - (* at receive's entry *)
    intros R F pc' fc m0' HQ regs1 mem1 HX1 REL1 FR1.
    destruct HQ as (t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & EQ & MU & WMo & MI1 & FRM
      & SAV & WM1).
    injection EQ as ER EF EP EC EM. subst R F pc' fc m0'.
    assert (G1 : getr regs1 1 = Z_to_bv 64 0x1641c) by (rewrite (sr_getr_eqv _ _ _ HX1); reflexivity).
    assert (G2 : getr regs1 2 = Z_to_bv 64 (bv_unsigned (getr regs 2) + -1616))
      by (rewrite (sr_getr_eqv _ _ _ HX1); reflexivity).
    assert (G4 : getr regs1 4 = getr regs 4) by (rewrite (sr_getr_eqv _ _ _ HX1); reflexivity).
    assert (G10 : getr regs1 10 = Z_to_bv 64 (bv_unsigned (getr regs 2) + -1596))
      by (rewrite (sr_getr_eqv _ _ _ HX1); reflexivity).
    assert (G11 : getr regs1 11 = Z_to_bv 64 (Z.max 30 (Z.of_nat (length body)) + 30))
      by (rewrite (sr_getr_eqv _ _ _ HX1); reflexivity).
    assert (G12 : getr regs1 12 = Z_to_bv 64 0) by (rewrite (sr_getr_eqv _ _ _ HX1); reflexivity).
    assert (G13 : getr regs1 13 = Z_to_bv 64 0) by (rewrite (sr_getr_eqv _ _ _ HX1); reflexivity).
    assert (SP1 : bv_unsigned (getr regs1 2) = bv_unsigned (getr regs 2) + -1616)
      by (rewrite G2; apply unsigned_lit; lia).
    assert (FLEN : Z.of_nat (length (fst (spec_build_frame [d0; d1; d2; d3; d4; d5] src send ack retry cmd 1 body 0)))
                   = Z.max 30 (Z.of_nat (length body)) + 30) by (apply bar_frame_len; [reflexivity | exact LS]).
    pose proof FR1 as (HM1 & _ & _ & _ & _ & _ & IMG1 & _ & _ & _ & _ & _ & ROA1 & _).
    (* the call of receive (frame, n, 0, 0) *)
    eapply X_bind.
    { change (@mkst (mkFP fp_regs fp_csr) regs1 (Z_to_bv 64 0x14d1c) mem1 (seg_rom rsegs))
        with (@mkst fx regs1 (Z_to_bv 64 receive_ENTRY) mem1 (seg_rom rsegs)).
      apply (X_recv L A regs1 mem1 md b Bw (bv_unsigned (getr regs 2) + -1596)
               (fst (spec_build_frame [d0; d1; d2; d3; d4; d5] src send ack retry cmd 1 body 0)) 0 0).
      - (* h_pre with receive's window 8320 = the walk's 9936 less its own frame 1616 *)
        split.
        { eapply (g_pre B API); [exact FR1 | rewrite G1; reflexivity | unfold spZ; rewrite SP1; Z.div_mod_to_equations; lia
            | unfold spZ; rewrite SP1; unfold receive_FRAME, ALLOC_STACK; lia | unfold spZ; lia
            | unfold receive_FRAME, ALLOC_STACK; lia | lia | unfold spZ; lia | rewrite G4; exact TPB]. }
        split; [exact INIT|]. split; [exact HALT|]. split; [exact LAZY|]. split; [rewrite SEGS; exact ROA1|].
        split; [exact RES|]. split; [unfold w_off_stack, receive_FRAME, ALLOC_STACK; rewrite SP1; lia|].
        split; [exact (sr_rw_cells_rel mem1 m' _ _ REL1 WM1)|]. split; [exact GF|].
        intros i Hi. specialize (RLR i Hi).
        change (mbyte rsegs mem1 (RELRO_BASE + i) = seg_rom rsegs (wa (RELRO_BASE + i))).
        change (mbyte rsegs mem (RELRO_BASE + i) = seg_rom rsegs (wa (RELRO_BASE + i))) in RLR.
        destruct (RELRO (RELRO_BASE + i) ltac:(lia)) as (Ri & Rs & Rc & Re).
        rewrite <- SEGS. rewrite (proj1 (IMG1 (RELRO_BASE + i) Ri Rs Rc Re ltac:(unfold h_world, RELRO_BASE, RELRO_LEN in *; lia))).
        rewrite SEGS. exact RLR.
      - exact FZ.
      - (* receive_args *)
        split; [exact G10|]. split; [rewrite G11, FLEN; reflexivity|]. split; [exact G12|]. split; [lia|].
        split; [rewrite G13; reflexivity|]. split; [lia|]. split; [rewrite FLEN; lia|].
        split; [apply (bar_bytes_blk B); [exact SEGS | exact (RoAdapt.bytes_at_back rsegs mem1 m' _ _ REL1 FRM)]|].
        split.
        { right. split; [unfold off_world; right; lia | right; unfold spZ; rewrite SP1, FLEN; lia]. }
        intros a0 Ha0. specialize (MODEL a0 Ha0). unfold build_and_receive_m in MODEL.
        rewrite (proj2 (Z.ltb_ge _ _)) in MODEL by (unfold SPEC_MAX_BODY; lia).
        destruct (spec_build_frame [d0; d1; d2; d3; d4; d5] src send ack retry cmd 1 body 0) as [fr nn].
        exact MODEL.
      - exact ROOMb. }
    intros c2 (a & Bw' & HAOK & ACEIL & OFFI & RM & POSTH).
    destruct POSTH as (fx2 & L2 & A2 & regs2 & mem2 & md2 & -> & FZ2 & CPK2 & INIT2 & HALT2 & LAZY2 & BLK2 & UB2
      & REG2 & RES2 & ROA2 & GK2 & WM2 & GF2 & RLR2).
    rewrite SEGS in ROA2.
    pose proof CPK2 as (_ & _ & _ & _ & _ & Hrp2 & _ & _ & KEEP2 & _).
    rewrite FLEN in ACEIL, OFFI.
    (* receive's footprint: the world, the freed frame below the ceiling off the image, ctx *)
    assert (ELOW : forall x, (h_world x \/ a <= x < a + Z.max 1 (Z.of_nat (length
                     (fst (spec_build_frame [d0; d1; d2; d3; d4; d5] src send ack retry cmd 1 body 0)))) \/
                     ms_ctx B <= x < ms_ctx B + CTX_SIZE) -> x < alloc_ceiling).
    { intros x [Hw | [Hh | Hc]].
      - destruct (WORLD x Hw) as (Hi & _). pose proof (sr_in_img_top B x SEGS Hi). pose proof sr_ceiling. lia.
      - rewrite FLEN in Hh. lia.
      - lia. }
    assert (FR2 : sr_fr B API 9936 (bv_unsigned (getr regs 2)) L A mem md L2 A2 mem2 md2).
    { eapply (sr_fr_call B API); try exact SEGS; try exact AX; try exact WORLD; try exact HGG; try exact ERRNO_LOW;
        try exact RELRO;
        [exact FR1 | lia | lia | exact CPK2 | unfold spZ; rewrite SP1; unfold receive_FRAME, ALLOC_STACK; lia
        | unfold spZ; lia | | | | exact UB2 | | exact INIT2 | exact ROA2 | exact GK2 | exact REG2].
      - intros x [Hw | [Hh | Hc]]; [right; right; left; exact Hw | | right; right; right; exact Hc].
        right; left. rewrite FLEN in Hh. split; [lia|].
        replace x with (a + (x - a)) by lia. apply OFFI. lia.
      - intros x Hx. right. intros HE. pose proof (ELOW x HE). lia.
      - intros x HE Hx. exfalso. pose proof (ELOW x HE). lia.
      - intros a0 k i Hin Hi. apply blocks_In in Hin as (p0 & <- & Hp).
        exact (KEEP2 p0 k i Hp (UB2 p0 k Hp) Hi). }
    (* receive keeps the walk's frame above its sp: the saved registers *)
    assert (GA : forall x, bv_unsigned (getr regs 2) + -1616 <= x < bv_unsigned (getr regs 2) ->
                 mbyte (ms_segs B) mem2 x = mbyte (ms_segs B) mem1 x).
    { intros x Hx. eapply proj1.
      eapply (g_above B API) with (stk := 9936) (S := bv_unsigned (getr regs 2)); try exact ERRNO_LOW; try exact SEGS;
        [exact HM1 | exact CPK2 | | | | | exact ELOW | ].
      all: try (unfold spZ; rewrite SP1); unfold receive_FRAME, ALLOC_STACK; lia. }
    (* registers receive keeps: sp, gp, tp, s0 .. s11 *)
    assert (P2 : forall r, callee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) by exact Hrp2.
    assert (H22 : getr regs2 2 = Z_to_bv 64 (bv_unsigned (getr regs 2) + -1616))
      by (rewrite <- G2; apply (P2 2); unfold callee_saved; lia).
    (* the epilogue, 0x1641c .. 0x16448 *)
    rewrite SEGS.
    eapply (X_run 9936 (bv_unsigned (getr regs 2)) L A mem md fx2 regs2 (getr regs1 1) mem2 md2 L2 A2);
      [exact FR2 | lia | lia | | |].
    + change (Regs6ss.mkR_of regs2) with
        (mkR (getr regs2 1) (getr regs2 2) (getr regs2 3) (getr regs2 4) (getr regs2 5) (getr regs2 6) (getr regs2 7)
             (getr regs2 8) (getr regs2 9) (getr regs2 10) (getr regs2 11) (getr regs2 12) (getr regs2 13)
             (getr regs2 14) (getr regs2 15) (getr regs2 16) (getr regs2 17) (getr regs2 18) (getr regs2 19)
             (getr regs2 20) (getr regs2 21) (getr regs2 22) (getr regs2 23) (getr regs2 24) (getr regs2 25)
             (getr regs2 26) (getr regs2 27) (getr regs2 28) (getr regs2 29) (getr regs2 30) (getr regs2 31)).
      rewrite G1, H22.
      eapply bar_epi; [rewrite unsigned_lit by lia; lia |].
      rewrite unsigned_lit by lia.
      replace (bv_unsigned (getr regs 2) + -1616 + 1536) with (bv_unsigned (getr regs 2) + -80) by lia.
      destruct SAV as [SWF SB]. split; [exact SWF|].
      apply bytes_at_normalize; [exact ROA2|].
      apply (bar_bytes_frame mem1); [exact (RoAdapt.bytes_at_back rsegs mem1 m' _ _ REL1 SB)|].
      intros x Hx. rewrite cells_bytes_length in Hx by exact SWF. cbn [cells_size csize Nat.add] in Hx.
      rewrite <- SEGS. apply GA. lia.
    + intros ms Hms. cbv beta in Hms. subst ms. do 5 eexists. exists []. split; [reflexivity|].
      split; [apply munch_refl|]. split; [apply wmono_refl|].
      intros x _ NO. exfalso. apply NO. exact I.
    + intros R3 F3 pc3 fc3 m03 HQ3 regs3 mem3 HX3 REL3 FR3.
      cbv beta in HQ3. injection HQ3 as ER3 EF3 EP3 EC3 EM3. subst R3 F3 pc3 fc3 m03.
      apply X_ret. unfold bar_ret. exists a, Bw'.
      split; [exact HAOK|]. split; [unfold bar_len; rewrite FLEN; exact ACEIL|].
      split; [unfold bar_len; rewrite FLEN; exact OFFI|].
      split.
      { unfold build_and_receive_m. rewrite (proj2 (Z.ltb_ge _ _)) by (unfold SPEC_MAX_BODY; lia).
        revert RM. destruct (spec_build_frame [d0; d1; d2; d3; d4; d5] src send ack retry cmd 1 body 0) as [fr nn].
        intros RM. exact RM. }
      unfold h_post. exists (mkFP (@fp_regs fx2) (@fp_csr fx2)), L2, A2, regs3, mem3, md2.
      split; [rewrite SEGS, (sr_ret_pc _ RAOK); reflexivity|].
      split; [exact FZ2|].
      split.
      { eapply (sr_post B API); try exact SEGS; try exact AX; try exact WORLD; try exact HGG; try exact ERRNO_LOW;
          try exact RELRO; [exact FR3 | | intros x Hx; left; exact Hx | intros x Hx; right; right; exact Hx].
        intros r Hr. rewrite (sr_getr_eqv _ _ _ HX3).
        unfold callee_saved in Hr.
        assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                     r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27 \/ False) by lia.
        repeat (destruct Hc as [Hc | Hc];
          [ subst r;
            first
            [ reflexivity
            | (transitivity (Z_to_bv 64 (bv_unsigned (getr regs 2)));
               [ transitivity (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned (getr regs 2) + -1616)) + 1616));
                 [reflexivity | f_equal; rewrite unsigned_lit by lia; lia]
               | apply Z_to_bv_bv_unsigned ])
            | match goal with |- getr _ (Z_to_bv 5 ?n) = _ =>
                transitivity (getr regs2 (Z_to_bv 5 n));
                [ reflexivity
                | rewrite (P2 n) by (unfold callee_saved; lia); rewrite (sr_getr_eqv _ _ _ HX1); reflexivity ]
              end ]
          | ]).
        destruct Hc. }
      split; [exact INIT2|]. split; [exact HALT2|]. split; [exact LAZY2|]. split; [exact BLK2|].
      split; [exact UB2|]. split; [exact REG2|]. split; [exact RES2|].
      split; [destruct FR3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R3 & _); rewrite SEGS; exact R3|].
      split; [destruct FR3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G3 & _); exact G3|].
      split; [exact (sr_rw_cells_rel mem3 _ _ _ REL3 (bar_wmem_norm mem2 Bw' ROA2 WM2))|].
      split; [exact GF2|].
      exact (bar_relro_rel mem3 _ REL3 (bar_relro_norm mem2 RLR2)).
Qed.

End Gen.

Section Thm.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.

Theorem build_and_receive_holds :
  receive_contract B API -> memset_contract -> memcpy_contract -> build_and_receive_contract B API.
Proof.
  intros RECV MEMSET MEMCPY HB L A regs mem md b Bw dstp srcp bodyp dst src body send ack retry cmd HPRE FZ ARGS ROOM.
  pose proof HB as (SEGS & _ & _ & HGG & _ & AX & ERRNO_LOW & CTX_LOW & WORLD & RELRO).
  rewrite SEGS.
  eapply (bar_gen B API) with (X := SR rsegs) (ROOM := fun _ b n => room_slots b n);
    try exact SEGS; try exact AX; try exact HGG; try exact ERRNO_LOW; try exact WORLD; try exact RELRO;
    try exact CTX_LOW; try eassumption.
  - intros c R Q H1 H2. exact (SR_bind rsegs c R Q H1 H2).
  - intros c Q HQ. exact (SR_ret rsegs c Q HQ).
  - intros. eapply (g_run B API); try exact SEGS; try exact AX; try exact HGG; try exact ERRNO_LOW;
      try exact WORLD; try exact RELRO; eassumption.
  - intros L0 A0 regs0 mem0 md0 b0 Bw0 p bytes bp pf HP HF HA HR. rewrite <- SEGS.
    exact (RECV HB L0 A0 regs0 mem0 md0 b0 Bw0 p bytes bp pf HP HF HA HR).
Qed.

Theorem build_and_receive_holds_cf :
  receive_contract_cf B API -> memset_contract -> memcpy_contract -> build_and_receive_contract_cf B API.
Proof.
  intros RECV MEMSET MEMCPY HB L A regs mem md b Bw dstp srcp bodyp dst src body send ack retry cmd HPRE FZ ARGS ROOM.
  pose proof HB as (SEGS & _ & _ & HGG & _ & AX & ERRNO_LOW & CTX_LOW & WORLD & RELRO).
  rewrite SEGS.
  eapply (bar_gen B API) with (X := SRcf B) (ROOM := room_cf);
    try exact SEGS; try exact AX; try exact HGG; try exact ERRNO_LOW; try exact WORLD; try exact RELRO;
    try exact CTX_LOW; try eassumption.
  - intros c R Q H1 H2. exact (SRcf_bind B c R Q H1 H2).
  - intros c Q HQ T HK. exact (HK c HQ).
  - intros. eapply (g_run_cf B API); try exact SEGS; try exact AX; try exact HGG; try exact ERRNO_LOW;
      try exact WORLD; try exact RELRO; eassumption.
  - intros L0 A0 regs0 mem0 md0 b0 Bw0 p bytes bp pf HP HF HA HR. rewrite <- SEGS.
    exact (RECV HB L0 A0 regs0 mem0 md0 b0 Bw0 p bytes bp pf HP HF HA HR).
Qed.

End Thm.
