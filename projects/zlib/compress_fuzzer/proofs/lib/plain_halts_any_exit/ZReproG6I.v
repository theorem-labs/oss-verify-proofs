(** * ZReproG6I — G6 bound-fit, part I: the room arithmetic.

    OWNER: g6-bound (zlib z-repro campaign, 2026-08-20).

    The whole-stream accounting closes on ONE integer inequality: the
    per-block stored overhead (5 bytes) summed over the block count fits
    inside [deflateBound]'s shift terms.  At memLevel 8 a Huffman block
    holds at most [lit_bufsize - 1 = 16383] symbols, each covering >= 1
    input byte, so a full block covers >= 16383 input bytes and the block
    count is at most [len / 16383 + 1].  The claim

        5 * (len / 16383 + 1)  <=  len>>12 + len>>14 + len>>25 + 7

    is EXACTLY TIGHT (equality at every [len = 16383 k]); the proof turns
    on [len/4096 >= 4*(len/16383) - 1] and [len/16384 >= len/16383 - 1],
    which hold precisely because [4 * 4096 = 16384 > 16383] and the block
    count stays below 4097 under the 64 MiB input cap.  There is no slack
    to spare — a 41st bit per block anywhere would break the face.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT. *)

From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproL0 ZRepro
  ZReproG6A.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** The Huffman block count at memLevel 8: [sym_end / 3 = 16383] symbols
    per full block, each symbol >= 1 input byte. *)
Definition zr_hnblocks (len : Z) : Z := len / 16383 + 1.

(** [q = len / 16383] stays below 4097 under the 64 MiB cap. *)
Lemma zr_q_bound : forall len, 0 <= len < 67108864 -> len / 16383 <= 4096.
Proof.
  intros len Hlen.
  assert (H : len / 16383 < 4097) by (apply Z.div_lt_upper_bound; lia).
  lia.
Qed.

(** The two tight per-shift bounds. *)
Lemma zr_a_bound : forall len, 0 <= len < 67108864 ->
  4 * (len / 16383) - 1 <= len / 4096.
Proof.
  intros len Hlen.
  pose proof (Z.div_mod len 4096 ltac:(lia)) as Ha.
  pose proof (Z.mod_pos_bound len 4096 ltac:(lia)) as Hra.
  pose proof (Z.div_mod len 16383 ltac:(lia)) as Hq.
  pose proof (Z.mod_pos_bound len 16383 ltac:(lia)) as Hrq.
  pose proof (zr_q_bound len Hlen) as Hqb.
  (* both quotients read the same [len]; integrality (not just the
     rationals) is what forces [4q-1 <= a] at the boundary *)
  lia.
Qed.

Lemma zr_b_bound : forall len, 0 <= len < 67108864 ->
  len / 16383 - 1 <= len / 16384.
Proof.
  intros len Hlen.
  pose proof (Z.div_mod len 16384 ltac:(lia)) as Hb.
  pose proof (Z.mod_pos_bound len 16384 ltac:(lia)) as Hrb.
  pose proof (Z.div_mod len 16383 ltac:(lia)) as Hq.
  pose proof (Z.mod_pos_bound len 16383 ltac:(lia)) as Hrq.
  pose proof (zr_q_bound len Hlen) as Hqb.
  lia.
Qed.

(** THE ROOM LEMMA (integer form). *)
Lemma zr_room_shifts : forall len, 0 <= len < 67108864 ->
  5 * zr_hnblocks len
  <= len / 4096 + len / 16384 + len / 33554432 + 7.
Proof.
  intros len Hlen.
  unfold zr_hnblocks.
  pose proof (zr_a_bound len Hlen) as Ha.
  pose proof (zr_b_bound len Hlen) as Hb.
  pose proof (Z.div_pos len 33554432 ltac:(lia) ltac:(lia)) as Hc.
  lia.
Qed.

(** ...and in the [Z.shiftr] spelling [zr_deflate_bound] uses. *)
Lemma zr_room_bound : forall len, 0 <= len < ZR_MAX_INPUT ->
  len + 5 * zr_hnblocks len + 6 <= zr_deflate_bound 15 len.
Proof.
  intros len Hlen.
  unfold ZR_MAX_INPUT in Hlen.
  unfold zr_deflate_bound, zr_wraplen.
  replace (15 <? 0) with false by reflexivity.
  replace (15 <? 15) with false by reflexivity.
  rewrite !Z.shiftr_div_pow2 by lia.
  replace (2 ^ 12) with 4096 by reflexivity.
  replace (2 ^ 14) with 16384 by reflexivity.
  replace (2 ^ 25) with 33554432 by reflexivity.
  pose proof (zr_room_shifts len Hlen) as Hr.
  lia.
Qed.

(** Tightness pins, as values: equality holds at block-boundary lengths
    (so the +7 constant and the 16383 granularity are both load-bearing —
    a reviewer can see the margin is zero). *)
Example zr_room_tight_1 :
  5 * zr_hnblocks 16383 = 16383 / 4096 + 16383 / 16384 + 16383 / 33554432 + 7.
Proof. vm_compute. reflexivity. Qed.

Example zr_room_tight_4 :
  5 * zr_hnblocks 65532 = 65532 / 4096 + 65532 / 16384 + 65532 / 33554432 + 7.
Proof. vm_compute. reflexivity. Qed.

(** At the largest block counts the [>>14]/[>>25] roundings add a little
    slack, so equality gives way to [<=] there — pinned as a value at the
    cap so the margin is visible to stay nonnegative but not zero. *)
Example zr_room_slack_cap :
  5 * zr_hnblocks 67104768
  <= 67104768 / 4096 + 67104768 / 16384 + 67104768 / 33554432 + 7.
Proof. vm_compute. discriminate. Qed.

Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Print Assumptions zr_room_shifts.
Print Assumptions zr_room_bound.
Unset Printing All.
