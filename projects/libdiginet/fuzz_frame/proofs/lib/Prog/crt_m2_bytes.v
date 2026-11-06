(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/mbedtls/fuzz_pkcs7/lib/Lib/Asn1Aux.v; 1278 of its 1342 lines of code are new or changed and 385 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Prog/classify_core.v, with its module paths and module names changed; 100 of its 145 lines of code are new or changed and 1297 lines of the source are left out. *)
(* Byte and memory facts for the two inlined copies of spec_build_frame (fuzz/spec.h:228) in
   check_round_trip of fuzz_frame.plain (0x131cc..0x132ec and 0x13314..0x13404): build_frame
   cut at its 18 header bytes; the byte that a store of a register writes; memcmp_model of a
   list with itself; build_out with a cap of the frame length; the split and the join of
   rw_cells blocks.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Prog Require Import diginet_frame_build_c.
Import ListNotations.
Open Scope Z_scope.

(** * Lists *)

(* memcmp_model of a list with itself, over at most its length, is 0. *)
Lemma m2_memcmp_self : forall n l, (n <= length l)%nat -> memcmp_model l l n = Some 0.
Proof.
  induction n as [|n IH]; intros l H; [reflexivity|].
  destruct l as [|a l]; cbn [length] in H; [lia|].
  cbn [memcmp_model]. rewrite Z.eqb_refl. apply IH. lia.
Qed.

(* With a cap of exactly the code it answers, diginet_frame_build leaves build_frame. *)
Lemma m2_build_out_eq : forall dmac smac send ack retry cmd ncmds bb mode oj,
  build_code bb (Z.of_nat (length oj)) = Z.of_nat (length oj) ->
  build_out dmac smac send ack retry cmd ncmds bb mode oj =
  build_frame dmac smac send ack retry cmd ncmds bb (mode =? 1).
Proof.
  intros dmac smac send ack retry cmd ncmds bb mode oj H. unfold build_out. cbv zeta. rewrite H.
  replace (0 <=? Z.of_nat (length oj)) with true by (symmetry; apply Z.leb_le; lia).
  rewrite Nat2Z.id, skipn_all. apply app_nil_r.
Qed.

(* The 18 bytes of build_frame at 12 .. 29: 0x885F, numbytes, the sum, send, ack and retry
   big-endian, cmd, ncmds. len is the body length, s the sum field. *)
Definition m2_hdr (len s send ack retry cmd ncmds : Z) : list byte :=
  [b8 0x88; b8 0x5f; b8 ((16 + len) / 2^8); b8 (16 + len); b8 (s / 2^8); b8 s;
   b8 (send / 2^24); b8 (send / 2^16); b8 (send / 2^8); b8 send;
   b8 (ack / 2^24); b8 (ack / 2^16); b8 (ack / 2^8); b8 ack;
   b8 (retry / 2^8); b8 retry; b8 cmd; b8 ncmds].

Lemma length_m2_hdr : forall len s send ack retry cmd ncmds,
  length (m2_hdr len s send ack retry cmd ncmds) = 18%nat.
Proof. reflexivity. Qed.

Lemma m2_build_frame_split : forall dst src send ack retry cmd ncmds bb z,
  build_frame dst src send ack retry cmd ncmds bb z =
  dst ++ src ++ m2_hdr (Z.of_nat (length bb)) (if z then 0 else spec_sum bb) send ack retry cmd ncmds ++
  bb ++ repeat (b8 0) (30 - length bb).
Proof.
  intros. unfold build_frame, m2_hdr, put16, put32. cbn [app].
  replace (b8 (0x885f / 2^8)) with (b8 0x88) by (vm_compute; reflexivity).
  replace (b8 0x885f) with (b8 0x5f) by (rewrite <- (b8_mod 0x885f); vm_compute; reflexivity).
  reflexivity.
Qed.

(** * The byte that a store of a register writes *)

Lemma m2_le1 : forall v : word, le1 v = [b8 (bv_unsigned v)].
Proof. intros v. reflexivity. Qed.

Lemma m2_b8_w64 : forall z, b8 (bv_unsigned (Z_to_bv 64 z)) = b8 z.
Proof. intros z. rewrite unsigned_lit_wrap. apply b8_mod_w. lia. Qed.

(* (uint8_t)(x >> k) for an x that agrees with v in its low w bits, k + 8 <= w. *)
Lemma m2_b8_shr : forall x v k w, 0 <= k -> k + 8 <= w -> x mod 2^w = v mod 2^w ->
  b8 (Z.shiftr x k) = b8 (v / 2^k).
Proof.
  intros x v k w Hk Hw H. rewrite Z.shiftr_div_pow2 by lia.
  rewrite <- (b8_div_mod x k w Hk Hw), <- (b8_div_mod v k w Hk Hw), H. reflexivity.
Qed.

Lemma m2_b8_low : forall x v w, 8 <= w -> x mod 2^w = v mod 2^w -> b8 x = b8 v.
Proof. intros x v w Hw H. rewrite <- (b8_mod_w x w Hw), <- (b8_mod_w v w Hw), H. reflexivity. Qed.

Lemma m2_w64_mod : forall z w, 0 <= w <= 64 -> bv_unsigned (Z_to_bv 64 z) mod 2^w = z mod 2^w.
Proof. intros z w Hw. rewrite unsigned_lit_wrap. apply mod_mod_pow2. lia. Qed.

(* lw sign-extends; the low 32 bits are the value's. *)
Lemma m2_sx32_mod : forall z, bv_unsigned (sx32 (Z_to_bv 64 z)) mod 2^32 = z mod 2^32.
Proof.
  intros z. unfold sx32. rewrite !unsigned_lit_wrap. rewrite mod_mod_pow2 by lia.
  unfold bv_swrap, bv_wrap.
  change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
  rewrite Zminus_mod_idemp_l.
  replace (z mod 2^64 + 2^31 - 2^31) with (z mod 2^64) by lia.
  apply mod_mod_pow2. lia.
Qed.

Lemma m2_zx16_mod : forall z, bv_unsigned (zx16 (Z_to_bv 64 z)) mod 2^16 = z mod 2^16.
Proof.
  intros z. unfold zx16. rewrite !unsigned_lit_wrap.
  rewrite (mod_mod_pow2 ((z mod 2^64) mod 2^16) 16 64) by lia.
  rewrite Z.mod_mod by lia. apply mod_mod_pow2. lia.
Qed.

(** * rw_cells blocks *)

Lemma m2_wr_split : forall m A n1 n2, wr_at rsegs m A (n1 + n2) -> 0 <= n1 -> 0 <= n2 ->
  wr_at rsegs m A n1 /\ wr_at rsegs m (A + n1) n2.
Proof.
  intros m A n1 n2 (H1 & H2 & H) P1 P2. split.
  - split; [lia|]. split; [lia|]. intros i Hi. apply H. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. replace (A + n1 + i) with (A + (n1 + i)) by lia. apply H. lia.
Qed.

Lemma m2_wr_join : forall m A n1 n2, wr_at rsegs m A n1 -> wr_at rsegs m (A + n1) n2 -> 0 <= n1 -> 0 <= n2 ->
  wr_at rsegs m A (n1 + n2).
Proof.
  intros m A n1 n2 (H1 & H2 & H) (G1 & G2 & G) P1 P2. split; [lia|]. split; [lia|].
  intros i Hi. destruct (Z.ltb_spec0 i n1); [apply H; lia|].
  replace (A + i) with (A + n1 + (i - n1)) by lia. apply G. lia.
Qed.

Lemma m2_rw_split : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_size_app, Nat2Z.inj_add in Hw.
  apply m2_wr_split in Hw; [| lia | lia]. destruct Hw as [V1 V2].
  rewrite cells_bytes_length in B2 by exact W1.
  split; (split; [split|]); assumption.
Qed.

Lemma m2_rw_app : forall m A cs1 cs2,
  rw_cells rsegs m A cs1 -> rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2 ->
  rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 [[W1 B1] V1] [[W2 B2] V2].
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|].
    rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app, Nat2Z.inj_add. apply m2_wr_join; [exact V1 | exact V2 | lia | lia].
Qed.

(* The join, with the address of the second block given. *)
Lemma m2_rw_app_at : forall m A B cs1 cs2,
  rw_cells rsegs m A cs1 -> B = A + Z.of_nat (cells_size cs1) -> rw_cells rsegs m B cs2 ->
  rw_cells rsegs m A (cs1 ++ cs2).
Proof. intros m A B cs1 cs2 H1 -> H2. apply m2_rw_app; assumption. Qed.

Lemma m2_rw_bytes : forall m A cs, rw_cells rsegs m A cs -> bytes_at rsegs m A (cells_bytes cs).
Proof. intros m A cs [[_ B] _]. exact B. Qed.

Lemma m2_rw_cb : forall m A n j, length j = n -> bytes_at rsegs m A j -> wr_at rsegs m A (Z.of_nat n) ->
  rw_cells rsegs m A [CB n j].
Proof.
  intros m A n j Hl Hb Hw. split; [split|]; cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize].
  - split; [exact Hl | exact I].
  - rewrite app_nil_r. exact Hb.
  - rewrite Nat.add_0_r. exact Hw.
Qed.

Lemma m2_cb_rw : forall m A n j, rw_cells rsegs m A [CB n j] ->
  length j = n /\ bytes_at rsegs m A j /\ wr_at rsegs m A (Z.of_nat n).
Proof.
  intros m A n j [[[Hl _] Hb] Hw]. cbn [cells_bytes cbytes cells_size csize] in Hb, Hw.
  rewrite app_nil_r in Hb. rewrite Nat.add_0_r in Hw. auto.
Qed.

(* A block of a + b bytes as a block of a bytes and a block of b bytes. *)
Lemma m2_cb_split : forall m A (a b : nat) j, rw_cells rsegs m A [CB (a + b) j] ->
  rw_cells rsegs m A [CB a (firstn a j)] /\ rw_cells rsegs m (A + Z.of_nat a) [CB b (skipn a j)].
Proof.
  intros m A a b j H. apply m2_cb_rw in H. destruct H as (Hl & Hb & Hw).
  rewrite <- (firstn_skipn a j) in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite length_firstn, Nat.min_l in B2 by lia.
  rewrite Nat2Z.inj_add in Hw. apply m2_wr_split in Hw; [| lia | lia]. destruct Hw as [V1 V2].
  split; apply m2_rw_cb; try assumption.
  - rewrite length_firstn. lia.
  - rewrite length_skipn. lia.
Qed.

(* The bytes firstn n (skipn k l) at A + k, for the bytes l at A. *)
Lemma m2_bytes_sub : forall m A l k n, bytes_at rsegs m A l -> (k <= length l)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn n (skipn k l)).
Proof.
  intros m A l k n H Hk. rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn, Nat.min_l in H by exact Hk.
  rewrite <- (firstn_skipn n (skipn k l)) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.
