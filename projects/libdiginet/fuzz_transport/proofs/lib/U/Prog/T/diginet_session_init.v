(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/varnish/esi_parse_fuzzer/lib/Yd/DA_Tac.v, with its module paths and module names changed; 635 of its 698 lines of code are new or changed and 187 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/TModel/TWorldMem.v, with its module paths and module names changed; 707 of its 787 lines of code are new or changed and 618 lines of the source are left out. *)
(* diginet_session_init at 0x169d4 (ubsan build), frame 48: the walk from the binary to diginet_session_init_m.
   It is the plain build's body plus three UBSan alignment tests (io & 7, &g_cfg & 3, &g_s & 7), none of which
   reaches the trap at 0x16af4. The body saves ra and s0..s4, rejects a NULL notify, a NULL io->send and an
   out-of-range cfg with -1, then
   memsets g_s to 0, memcpys the 60 config bytes into g_s.cfg, stores the io block, notify, ctx and state 0, and,
   when cfg.desk_mac_set is not 0, the 6 desk MAC bytes and desk_known = 1. Every world write lands in g_s
   [OFF_g_s, OFF_g_s + 18264); every world read reads g_cfg, which is never written. The world is therefore kept
   in the canonical form [upd B OFF_g_s G] with G the 18264-byte image of g_s, and the reads go through it by
   u_at_upd_out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TSess0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memset_c memcpy_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract TSessC diginet_session_init_c.
Import ListNotations.
Open Scope Z_scope.

(* ================ little-endian bytes ================ *)

Lemma put_zeros : forall n, put n 0 = repeat (Z_to_bv 8 0) n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  unfold put in *. cbn [Z_to_le_bytes repeat]. rewrite Z.shiftr_0_l, IH. reflexivity.
Qed.

Lemma le_roundtrip : forall n (L : list byte), length L = n -> Z_to_le_bytes n (bytes_le_to_Z L) = L.
Proof.
  induction n as [|n IH]; intros L HL.
  - destruct L as [|b L]; [reflexivity | cbn in HL; lia].
  - destruct L as [|b L]; [cbn in HL; lia|].
    cbn [length] in HL.
    pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
    pose proof (bytes_le_to_Z_nonneg L) as RL.
    cbn [bytes_le_to_Z Z_to_le_bytes].
    rewrite lor_shiftl8_add by lia.
    f_equal.
    + apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
      rewrite (Z.mul_comm 256 (bytes_le_to_Z L)), Z.mod_add by lia. apply Z.mod_small. lia.
    + rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
      rewrite (Z.mul_comm 256 (bytes_le_to_Z L)), Z.div_add by lia.
      rewrite (Z.div_small (bv_unsigned b) 256) by lia. rewrite Z.add_0_l. apply IH. lia.
Qed.

Lemma le2_swrap : forall X, Z_to_le_bytes 2 (bv_swrap 16 X) = Z_to_le_bytes 2 X.
Proof.
  intros X.
  rewrite <- (Z_to_le_bytes_mod 2 (bv_swrap 16 X) 16) by (cbn; lia).
  rewrite <- (Z_to_le_bytes_mod 2 X 16) by (cbn; lia).
  f_equal. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 16) with (2 ^ 15). change (bv_modulus 16) with (2 ^ 16).
  rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

Lemma put_sub2 : forall bs k, 0 <= k -> k + 2 <= Z.of_nat (length bs) ->
  put 2 (bv_swrap 16 (u_at bs k 2)) = sub bs k 2.
Proof.
  intros bs k Hk Hl.
  assert (L2 : length (sub bs k 2) = 2%nat) by (apply length_sub; lia).
  unfold put, u_at. rewrite le2_swrap. apply le_roundtrip. exact L2.
Qed.

(* ================ lengths and the algebra of upd ================ *)

Lemma Lupd : forall (bs v : list byte) k n, 0 <= k -> k + Z.of_nat (length v) <= n ->
  Z.of_nat (length bs) = n -> Z.of_nat (length (upd bs k v)) = n.
Proof. intros bs v k n Hk Hv Hb. rewrite length_upd; [exact Hb | exact Hk | lia]. Qed.

(* a write inside an already written span folds into that span *)
Lemma upd_nest : forall (bs G v : list byte) k d j, 0 <= k -> 0 <= d -> j = k + d ->
  d + Z.of_nat (length v) <= Z.of_nat (length G) -> k + Z.of_nat (length G) <= Z.of_nat (length bs) ->
  upd (upd bs k G) j v = upd bs k (upd G d v).
Proof.
  intros bs G v k d j Hk Hd -> HdG HGb.
  assert (LGv : length (upd G d v) = length G) by (apply length_upd; lia).
  assert (L1 : length (upd bs k G) = length bs) by (apply length_upd; lia).
  apply nth_error_ext. intros i.
  rewrite (ne_upd (upd bs k G) v (k + d) i) by (first [ lia | (rewrite L1; lia) ]).
  rewrite (ne_upd bs G k i) by lia.
  rewrite (ne_upd bs (upd G d v) k i) by (first [ lia | (rewrite LGv; lia) ]).
  rewrite LGv, (Z2Nat.inj_add k d) by lia.
  destruct (Nat.leb_spec (Z.to_nat k + Z.to_nat d) i);
  destruct (Nat.ltb_spec i (Z.to_nat k + Z.to_nat d + length v));
  destruct (Nat.leb_spec (Z.to_nat k) i);
  destruct (Nat.ltb_spec i (Z.to_nat k + length G));
  cbn [andb]; try reflexivity; try (exfalso; lia);
  rewrite (ne_upd G v d (i - Z.to_nat k)) by lia;
  first
    [ (replace ((Z.to_nat d <=? i - Z.to_nat k) && (i - Z.to_nat k <? Z.to_nat d + length v))%nat with true
         by (symmetry; apply andb_true_iff; split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia);
       f_equal; lia)
    | (replace ((Z.to_nat d <=? i - Z.to_nat k) && (i - Z.to_nat k <? Z.to_nat d + length v))%nat with false
         by (symmetry; apply andb_false_iff;
             first [ left; apply Nat.leb_gt; lia | right; apply Nat.ltb_ge; lia ]);
       reflexivity) ].
Qed.

Lemma sub_app2 : forall (bs : list byte) k n p, 0 <= k -> k + Z.of_nat n + Z.of_nat p <= Z.of_nat (length bs) ->
  sub bs k n ++ sub bs (k + Z.of_nat n) p = sub bs k (n + p).
Proof.
  intros bs k n p Hk Hl. apply nth_error_ext. intros i.
  assert (Ln : length (sub bs k n) = n) by (apply length_sub; lia).
  destruct (Nat.ltb_spec i n).
  - rewrite nth_error_app1 by lia. rewrite !ne_sub by lia.
    replace (i <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    replace (i <? n + p)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    reflexivity.
  - rewrite nth_error_app2 by lia. rewrite Ln. rewrite !ne_sub by lia.
    destruct (Nat.ltb_spec (i - n) p).
    + replace (i <? n + p)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
      f_equal. lia.
    + replace (i <? n + p)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
      reflexivity.
Qed.

Lemma sub_app2' : forall (bs : list byte) k j n p, 0 <= k -> j = k + Z.of_nat n ->
  k + Z.of_nat n + Z.of_nat p <= Z.of_nat (length bs) ->
  sub bs k n ++ sub bs j p = sub bs k (n + p).
Proof. intros bs k j n p Hk -> Hl. apply sub_app2; lia. Qed.

(* two adjacent writes, the lower one last (the model's order) *)
Lemma upd_merge_r : forall (bs v w : list byte) k j, 0 <= k -> j = k + Z.of_nat (length v) ->
  j + Z.of_nat (length w) <= Z.of_nat (length bs) ->
  upd (upd bs k v) j w = upd bs k (v ++ w).
Proof.
  intros bs v w k j Hk -> Hl. apply nth_error_ext. intros i.
  assert (L1 : length (upd bs k v) = length bs) by (apply length_upd; lia).
  rewrite (ne_upd (upd bs k v) w (k + Z.of_nat (length v)) i) by (first [ lia | (rewrite L1; lia) ]).
  rewrite (ne_upd bs v k i) by lia.
  rewrite (ne_upd bs (v ++ w) k i) by (first [ lia | (rewrite length_app; lia) ]).
  rewrite length_app, (Z2Nat.inj_add k (Z.of_nat (length v))) by lia. rewrite Nat2Z.id.
  destruct (Nat.leb_spec (Z.to_nat k + length v) i);
  destruct (Nat.ltb_spec i (Z.to_nat k + length v + length w));
  destruct (Nat.leb_spec (Z.to_nat k) i);
  destruct (Nat.ltb_spec i (Z.to_nat k + (length v + length w)));
  destruct (Nat.ltb_spec i (Z.to_nat k + length v));
  cbn [andb]; try reflexivity; try (exfalso; lia);
  first [ (rewrite nth_error_app1 by lia; reflexivity)
        | (rewrite nth_error_app2 by lia; f_equal; lia) ].
Qed.

(* the same two writes, the higher one first (the binary's order) *)
Lemma upd_merge_l : forall (bs v w : list byte) k j, 0 <= k -> j = k + Z.of_nat (length v) ->
  j + Z.of_nat (length w) <= Z.of_nat (length bs) ->
  upd (upd bs j w) k v = upd bs k (v ++ w).
Proof.
  intros bs v w k j Hk Hj Hl.
  rewrite (upd_upd_comm bs w v j k) by lia.
  apply upd_merge_r; lia.
Qed.

(* the io block: the binary stores now_us, recv, send, ctx; the model ctx, send, recv, now_us *)
Lemma io_reorder : forall (G c8 s8 r8 n8 : list byte),
  Z.of_nat (length c8) = 8 -> Z.of_nat (length s8) = 8 -> Z.of_nat (length r8) = 8 ->
  Z.of_nat (length n8) = 8 -> Z.of_nat (length G) = 18264 ->
  upd (upd (upd (upd G 88 n8) 80 r8) 72 s8) 64 c8 = upd (upd (upd (upd G 64 c8) 72 s8) 80 r8) 88 n8.
Proof.
  intros G c8 s8 r8 n8 Lc Ls Lr Ln LG.
  assert (L1 : Z.of_nat (length (upd G 88 n8)) = 18264) by (apply Lupd; [lia|lia|exact LG]).
  assert (L2 : Z.of_nat (length (upd (upd G 88 n8) 80 r8)) = 18264) by (apply Lupd; [lia|lia|exact L1]).
  assert (M1 : Z.of_nat (length (upd G 64 c8)) = 18264) by (apply Lupd; [lia|lia|exact LG]).
  assert (M2 : Z.of_nat (length (upd (upd G 64 c8) 72 s8)) = 18264) by (apply Lupd; [lia|lia|exact M1]).
  rewrite (upd_merge_l (upd (upd G 88 n8) 80 r8) c8 s8 64 72) by lia.
  rewrite (upd_merge_l (upd G 88 n8) (c8 ++ s8) r8 64 80) by (rewrite ?length_app; lia).
  rewrite (upd_merge_l G ((c8 ++ s8) ++ r8) n8 64 88) by (rewrite ?length_app; lia).
  rewrite (upd_merge_r G c8 s8 64 72) by lia.
  rewrite (upd_merge_r G (c8 ++ s8) r8 64 80) by (rewrite ?length_app; lia).
  rewrite (upd_merge_r G ((c8 ++ s8) ++ r8) n8 64 88) by (rewrite ?length_app; lia).
  reflexivity.
Qed.

(* the desk MAC: the binary writes 124, 122, desk_known, 120; the model the 6 bytes, then desk_known *)
Lemma desk_reorder : forall (G p1 p2 p3 o4 : list byte),
  Z.of_nat (length p1) = 2 -> Z.of_nat (length p2) = 2 -> Z.of_nat (length p3) = 2 ->
  Z.of_nat (length o4) = 4 -> Z.of_nat (length G) = 18264 ->
  upd (upd (upd (upd G 124 p3) 122 p2) 116 o4) 120 p1 = upd (upd G 120 (p1 ++ p2 ++ p3)) 116 o4.
Proof.
  intros G p1 p2 p3 o4 L1 L2 L3 L4 LG.
  assert (K1 : Z.of_nat (length (upd G 124 p3)) = 18264) by (apply Lupd; [lia|lia|exact LG]).
  assert (K2 : Z.of_nat (length (upd (upd G 124 p3) 122 p2)) = 18264) by (apply Lupd; [lia|lia|exact K1]).
  rewrite (upd_upd_comm (upd (upd G 124 p3) 122 p2) o4 p1 116 120) by lia.
  f_equal.
  rewrite (upd_merge_l (upd G 124 p3) p1 p2 120 122) by lia.
  rewrite (upd_merge_l G (p1 ++ p2) p3 120 124) by (rewrite ?length_app; lia).
  rewrite <- app_assoc. reflexivity.
Qed.

(* the common part: the binary's canonical world against the model's chain of setters *)
Lemma init_eq_ok : forall (B zs cfg c8 s8 r8 n8 nt8 cx8 z4 : list byte),
  Z.of_nat (length B) = 65616 -> Z.of_nat (length zs) = 18264 -> Z.of_nat (length cfg) = 60 ->
  Z.of_nat (length c8) = 8 -> Z.of_nat (length s8) = 8 -> Z.of_nat (length r8) = 8 ->
  Z.of_nat (length n8) = 8 -> Z.of_nat (length nt8) = 8 -> Z.of_nat (length cx8) = 8 ->
  Z.of_nat (length z4) = 4 ->
  upd B 1648 (upd (upd (upd (upd (upd (upd (upd (upd zs 0 cfg) 88 n8) 80 r8) 72 s8) 64 c8) 96 nt8) 104 cx8) 112 z4)
  = upd (upd (upd (upd (upd (upd (upd (upd (upd B 1648 zs) 1648 cfg) 1712 c8) 1720 s8) 1728 r8) 1736 n8)
                1744 nt8) 1752 cx8) 1760 z4.
Proof.
  intros B zs cfg c8 s8 r8 n8 nt8 cx8 z4 LB Lzs Lcfg Lc Ls Lr Ln Lnt Lcx Lz.
  assert (K1 : Z.of_nat (length (upd zs 0 cfg)) = 18264) by (apply Lupd; [lia|lia|exact Lzs]).
  rewrite (upd_nest B zs cfg 1648 0 1648) by lia.
  assert (K2 : Z.of_nat (length (upd (upd zs 0 cfg) 64 c8)) = 18264) by (apply Lupd; [lia|lia|exact K1]).
  rewrite (upd_nest B (upd zs 0 cfg) c8 1648 64 1712) by lia.
  assert (K3 : Z.of_nat (length (upd (upd (upd zs 0 cfg) 64 c8) 72 s8)) = 18264)
    by (apply Lupd; [lia|lia|exact K2]).
  rewrite (upd_nest B (upd (upd zs 0 cfg) 64 c8) s8 1648 72 1720) by lia.
  assert (K4 : Z.of_nat (length (upd (upd (upd (upd zs 0 cfg) 64 c8) 72 s8) 80 r8)) = 18264)
    by (apply Lupd; [lia|lia|exact K3]).
  rewrite (upd_nest B (upd (upd (upd zs 0 cfg) 64 c8) 72 s8) r8 1648 80 1728) by lia.
  assert (K5 : Z.of_nat (length (upd (upd (upd (upd (upd zs 0 cfg) 64 c8) 72 s8) 80 r8) 88 n8)) = 18264)
    by (apply Lupd; [lia|lia|exact K4]).
  rewrite (upd_nest B (upd (upd (upd (upd zs 0 cfg) 64 c8) 72 s8) 80 r8) n8 1648 88 1736) by lia.
  assert (K6 : Z.of_nat (length (upd (upd (upd (upd (upd (upd zs 0 cfg) 64 c8) 72 s8) 80 r8) 88 n8) 96 nt8))
               = 18264) by (apply Lupd; [lia|lia|exact K5]).
  rewrite (upd_nest B (upd (upd (upd (upd (upd zs 0 cfg) 64 c8) 72 s8) 80 r8) 88 n8) nt8 1648 96 1744) by lia.
  assert (K7 : Z.of_nat (length (upd (upd (upd (upd (upd (upd (upd zs 0 cfg) 64 c8) 72 s8) 80 r8) 88 n8) 96 nt8)
                                   104 cx8)) = 18264) by (apply Lupd; [lia|lia|exact K6]).
  rewrite (upd_nest B (upd (upd (upd (upd (upd (upd zs 0 cfg) 64 c8) 72 s8) 80 r8) 88 n8) 96 nt8) cx8
             1648 104 1752) by lia.
  rewrite (upd_nest B (upd (upd (upd (upd (upd (upd (upd zs 0 cfg) 64 c8) 72 s8) 80 r8) 88 n8) 96 nt8) 104 cx8) z4
             1648 112 1760) by lia.
  f_equal. f_equal. f_equal. f_equal.
  apply io_reorder; assumption.
Qed.

Lemma init_eq_desk : forall (B G p1 p2 p3 o4 : list byte),
  Z.of_nat (length B) = 65616 -> Z.of_nat (length G) = 18264 ->
  Z.of_nat (length p1) = 2 -> Z.of_nat (length p2) = 2 -> Z.of_nat (length p3) = 2 ->
  Z.of_nat (length o4) = 4 ->
  upd B 1648 (upd (upd (upd (upd G 124 p3) 122 p2) 116 o4) 120 p1)
  = upd (upd (upd B 1648 G) 1768 (p1 ++ p2 ++ p3)) 1764 o4.
Proof.
  intros B G p1 p2 p3 o4 LB LG L1 L2 L3 L4.
  assert (K1 : Z.of_nat (length (upd G 120 (p1 ++ p2 ++ p3))) = 18264)
    by (apply Lupd; [lia | rewrite ?length_app; lia | exact LG]).
  rewrite (upd_nest B G (p1 ++ p2 ++ p3) 1648 120 1768) by (rewrite ?length_app; lia).
  rewrite (upd_nest B (upd G 120 (p1 ++ p2 ++ p3)) o4 1648 116 1764) by lia.
  f_equal. apply desk_reorder; assumption.
Qed.

(* ================ the caller's 32-byte io block ================ *)

Lemma sub_app_l : forall (u v : list byte) n, length u = n -> sub (u ++ v) 0 n = u.
Proof.
  intros u v n Hu. apply nth_error_ext. intros i.
  rewrite ne_sub by lia.
  replace (Z.to_nat 0 + i)%nat with i by lia.
  destruct (Nat.ltb_spec i n).
  - rewrite nth_error_app1 by lia. reflexivity.
  - symmetry. apply nth_error_None. lia.
Qed.

Lemma sub_app_r : forall (u v : list byte) k n, 0 <= k -> length u = Z.to_nat k ->
  sub (u ++ v) k n = sub v 0 n.
Proof.
  intros u v k n Hk Hu. apply nth_error_ext. intros i.
  rewrite !ne_sub by lia.
  destruct (Nat.ltb_spec i n); [|reflexivity].
  rewrite nth_error_app2 by lia. f_equal. lia.
Qed.

Lemma io_sub0 : forall c s rc n,
  sub (put 8 c ++ put 8 s ++ put 8 rc ++ put 8 n) 0 8 = le8 (Z_to_bv 64 c).
Proof. intros. rewrite sub_app_l by apply length_put. rewrite le8_put. reflexivity. Qed.

Lemma io_sub8 : forall c s rc n,
  sub (put 8 c ++ put 8 s ++ put 8 rc ++ put 8 n) 8 8 = le8 (Z_to_bv 64 s).
Proof.
  intros. rewrite sub_app_r by (first [lia | (rewrite length_put; reflexivity)]).
  rewrite sub_app_l by apply length_put. rewrite le8_put. reflexivity.
Qed.

Lemma io_sub16 : forall c s rc n,
  sub (put 8 c ++ put 8 s ++ put 8 rc ++ put 8 n) 16 8 = le8 (Z_to_bv 64 rc).
Proof.
  intros. rewrite app_assoc.
  rewrite sub_app_r by (first [lia | (rewrite length_app, !length_put; reflexivity)]).
  rewrite sub_app_l by apply length_put. rewrite le8_put. reflexivity.
Qed.

Lemma io_sub24 : forall c s rc n,
  sub (put 8 c ++ put 8 s ++ put 8 rc ++ put 8 n) 24 8 = le8 (Z_to_bv 64 n).
Proof.
  intros. rewrite app_assoc, app_assoc.
  rewrite sub_app_r by (first [lia | (rewrite !length_app, !length_put; reflexivity)]).
  rewrite sub_all by apply length_put. rewrite le8_put. reflexivity.
Qed.

Lemma io_read : forall segs m p k c s rc n,
  bytes_at segs m p (put 8 c ++ put 8 s ++ put 8 rc ++ put 8 n) -> 0 <= k -> k + 8 <= 32 ->
  ov_read_bytes segs m (wa (p + k)) 8 = Some (sub (put 8 c ++ put 8 s ++ put 8 rc ++ put 8 n) k 8).
Proof.
  intros segs m p k c s rc n H Hk Hn.
  assert (L : length (put 8 c ++ put 8 s ++ put 8 rc ++ put 8 n) = 32%nat)
    by (rewrite !length_app, !length_put; reflexivity).
  rewrite (bytes_at_read segs m p _ k 8 H Hk ltac:(rewrite L; lia)). reflexivity.
Qed.

(* ================ the stack window across a libc call ================ *)

(* The callee wrote exactly [X, X + n), and gives that span back as a cell, so every byte of the stack window
   is still readable: outside the span by munch, inside it from the cell. *)
Lemma stk_fill : forall segs m m' lo hi X n (src : list byte),
  stk segs m lo hi -> munch [(X, X + n)] m m' -> wmono segs m m' ->
  rw_cells segs m' X [CB (Z.to_nat n) src] ->
  stk segs m' lo hi.
Proof.
  intros segs m m' lo hi X n src (H1 & H2 & H) MU WO D.
  destruct D as [[Dwf Db] _]. cbn [cells_wf cell_wf] in Dwf. destruct Dwf as [LS _].
  cbn [cells_bytes cbytes] in Db. rewrite app_nil_r in Db. destruct Db as (Ba & Bl & Dbi).
  split; [exact H1|]. split; [exact H2|].
  intros a Ha. destruct (H a Ha) as [Hw (b & Hb)].
  split; [apply WO; exact Hw|].
  destruct (Z.leb_spec X a) as [I1|I1]; destruct (Z.ltb_spec a (X + n)) as [I2|I2];
    try (exists b; unfold mrd in *; rewrite MU; [exact Hb|];
         cbn [outside]; split; [|exact I]; rewrite wa_unsigned by lia; lia).
  assert (Hi : (Z.to_nat (a - X) < length src)%nat) by (rewrite LS; lia).
  destruct (nth_error src (Z.to_nat (a - X))) as [b0|] eqn:E.
  - exists b0. rewrite <- E. replace a with (X + Z.of_nat (Z.to_nat (a - X))) at 1 by lia.
    apply Dbi. exact Hi.
  - apply nth_error_None in E. lia.
Qed.

(* ================ branch conditions ================ *)

Lemma eqb0_lit : forall z, 0 <= z < 2 ^ 64 -> bv_eqb (Z_to_bv 64 z) (Z_to_bv 64 0) = (z =? 0).
Proof. intros z Hz. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma land7 : forall z, 0 <= z -> z mod 8 = 0 -> Z.land z 7 = 0.
Proof. intros z Hz Hm. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact Hm. Qed.

Lemma s32_val : forall B k, s32_at B k = (if u_at B k 4 <? 2 ^ 31 then u_at B k 4 else u_at B k 4 - 2 ^ 32).
Proof.
  intros B k. pose proof (u_at_range B k 4) as R. change (8 * Z.of_nat 4) with 32 in R.
  unfold s32_at, bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  destruct (Z.ltb_spec (u_at B k 4) (2 ^ 31)).
  - rewrite Z.mod_small by lia. lia.
  - replace (u_at B k 4 + 2 ^ 31) with ((u_at B k 4 - 2 ^ 31) + 1 * 2 ^ 32) by lia.
    rewrite Z_mod_plus_full, Z.mod_small by lia. lia.
Qed.

Lemma s32_eqb0 : forall B k, (s32_at B k =? 0) = (u_at B k 4 =? 0).
Proof.
  intros B k. pose proof (u_at_range B k 4) as R. change (8 * Z.of_nat 4) with 32 in R.
  rewrite s32_val. destruct (Z.ltb_spec (u_at B k 4) (2 ^ 31)); [reflexivity|].
  destruct (Z.eqb_spec (u_at B k 4 - 2 ^ 32) 0); destruct (Z.eqb_spec (u_at B k 4) 0);
    first [ reflexivity | lia ].
Qed.

Lemma mod64_neg : forall x, - 2 ^ 63 <= x < 0 -> x mod 2 ^ 64 = x + 2 ^ 64.
Proof.
  intros x Hx. replace x with ((x + 2 ^ 64) + (-1) * 2 ^ 64) at 1 by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma eqb0_s32 : forall B k, bv_eqb (Z_to_bv 64 (s32_at B k)) (Z_to_bv 64 0) = (s32_at B k =? 0).
Proof.
  intros B k. pose proof (s32_range B k) as R. unfold bv_eqb.
  rewrite (unsigned_lit 0) by lia. rewrite unsigned_lit_wrap.
  destruct (Z.ltb_spec (s32_at B k) 0).
  - rewrite (mod64_neg (s32_at B k)) by lia.
    destruct (Z.eqb_spec (s32_at B k + 2 ^ 64) 0); destruct (Z.eqb_spec (s32_at B k) 0);
      first [ reflexivity | lia ].
  - rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma ltu_s32 : forall c B k, 0 <= c < 2 ^ 31 ->
  bv_ltu (Z_to_bv 64 c) (Z_to_bv 64 (s32_at B k)) = (c <? u_at B k 4).
Proof.
  intros c B k Hc. pose proof (u_at_range B k 4) as R. change (8 * Z.of_nat 4) with 32 in R.
  unfold bv_ltu. rewrite (unsigned_lit c) by lia. rewrite unsigned_lit_wrap.
  rewrite s32_val. destruct (Z.ltb_spec (u_at B k 4) (2 ^ 31)).
  - rewrite Z.mod_small by lia. reflexivity.
  - rewrite (mod64_neg (u_at B k 4 - 2 ^ 32)) by lia.
    destruct (Z.ltb_spec c (u_at B k 4 - 2 ^ 32 + 2 ^ 64)); destruct (Z.ltb_spec c (u_at B k 4));
      first [ reflexivity | lia ].
Qed.

Lemma swrap32_small : forall x, - 2 ^ 31 <= x < 2 ^ 31 -> bv_swrap 32 x = x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma swrap32_hi : forall x, 2 ^ 31 <= x < 2 ^ 31 + 2 ^ 32 -> bv_swrap 32 x = x - 2 ^ 32.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  replace (x + 2 ^ 31) with ((x + 2 ^ 31 - 2 ^ 32) + 1 * 2 ^ 32) by lia.
  rewrite Z_mod_plus_full, Z.mod_small by lia. lia.
Qed.

(* `addiw a1,a1,-1485; bltu a1,-1461` is `max_body < 24 || 1484 < max_body` on the uint32 *)
Lemma body_cond : forall B k,
  bv_ltu (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (s32_at B k)) + -1485))) (Z_to_bv 64 (-1461))
  = ((u_at B k 4 <? 24) || (1484 <? u_at B k 4)).
Proof.
  intros B k. pose proof (u_at_range B k 4) as R. change (8 * Z.of_nat 4) with 32 in R.
  unfold bv_ltu. rewrite !unsigned_lit_wrap.
  replace ((-1461) mod 2 ^ 64) with (2 ^ 64 - 1461) by (vm_compute; reflexivity).
  assert (E : bv_swrap 32 (s32_at B k mod 2 ^ 64 + -1485) = bv_swrap 32 (u_at B k 4 - 1485)).
  { rewrite s32_val. destruct (Z.ltb_spec (u_at B k 4) (2 ^ 31)).
    - rewrite Z.mod_small by lia. f_equal; try lia.
    - rewrite (mod64_neg (u_at B k 4 - 2 ^ 32)) by lia.
      unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
      f_equal.
      replace (u_at B k 4 - 2 ^ 32 + 2 ^ 64 + -1485 + 2 ^ 31)
        with ((u_at B k 4 - 1485 + 2 ^ 31) + (2 ^ 32 - 1) * 2 ^ 32) by lia.
      rewrite Z_mod_plus_full. reflexivity. }
  rewrite E.
  destruct (Z.ltb_spec (u_at B k 4) 24).
  - rewrite (swrap32_small (u_at B k 4 - 1485)) by lia.
    rewrite (mod64_neg (u_at B k 4 - 1485)) by lia.
    cbn [orb]. apply Z.ltb_lt. lia.
  - destruct (Z.ltb_spec 1484 (u_at B k 4)).
    + destruct (Z.ltb_spec (u_at B k 4) (2 ^ 31 + 1485)).
      * rewrite (swrap32_small (u_at B k 4 - 1485)) by lia.
        rewrite (Z.mod_small (u_at B k 4 - 1485)) by lia.
        cbn [orb]. apply Z.ltb_lt. lia.
      * rewrite (swrap32_hi (u_at B k 4 - 1485)) by lia.
        rewrite (mod64_neg (u_at B k 4 - 1485 - 2 ^ 32)) by lia.
        cbn [orb]. apply Z.ltb_lt. lia.
    + rewrite (swrap32_small (u_at B k 4 - 1485)) by lia.
      rewrite (mod64_neg (u_at B k 4 - 1485)) by lia.
      cbn [orb]. apply Z.ltb_ge. lia.
Qed.

(* ================ the model, case by case ================ *)

(* the model's result, read off without `injection` (which head-normalises the world term it is given) *)
Lemma some_pair_inv : forall {A C : Type} {a a' : A} {b b' : C}, Some (a, b) = Some (a', b') -> a = a' /\ b = b'.
Proof. intros A C a a' b b' H. injection H as H1 H2. split; assumption. Qed.

(* :58-59, a NULL io->send or a NULL notify *)
Lemma init_m_arg : forall B c s rc n nt cx, s = 0 \/ nt = 0 ->
  diginet_session_init_m B c s rc n nt cx = Some (B, DIGINET_E_ARG).
Proof.
  intros B c s rc n nt cx H. unfold diginet_session_init_m.
  replace ((s =? 0) || (nt =? 0))%bool with true; [reflexivity|].
  symmetry. apply Bool.orb_true_iff. destruct H as [ Hs | Hn ]; [ left; rewrite Hs | right; rewrite Hn ];
    apply Z.eqb_refl.
Qed.

(* :60-62, a config out of range *)
Lemma init_m_cfg : forall B c s rc n nt cx,
  Cfg_max_cmds B = 0 \/ 255 < Cfg_max_cmds B \/ Cfg_max_body B < 24 \/ 1484 < Cfg_max_body B ->
  diginet_session_init_m B c s rc n nt cx = Some (B, DIGINET_E_ARG).
Proof.
  intros B c s rc n nt cx H. unfold diginet_session_init_m.
  destruct ((s =? 0) || (nt =? 0))%bool; [reflexivity|].
  replace ((Cfg_max_cmds B =? 0) || (Cfg_max_body B <? DIGINET_CMD_MAX_LEN)
           || (DIGINET_MAX_BODY_LEN <? Cfg_max_body B) || (255 <? Cfg_max_cmds B))%bool with true;
    [reflexivity|].
  symmetry. unfold DIGINET_CMD_MAX_LEN, DIGINET_MAX_BODY_LEN.
  destruct H as [H|[H|[H|H]]].
  - apply Bool.orb_true_iff; left. apply Bool.orb_true_iff; left.
    apply Bool.orb_true_iff; left. apply Z.eqb_eq. exact H.
  - apply Bool.orb_true_iff; right. apply Z.ltb_lt. exact H.
  - apply Bool.orb_true_iff; left. apply Bool.orb_true_iff; left.
    apply Bool.orb_true_iff; right. apply Z.ltb_lt. exact H.
  - apply Bool.orb_true_iff; left. apply Bool.orb_true_iff; right. apply Z.ltb_lt. exact H.
Qed.

(* :63-68 and :74 with no desk MAC *)
Lemma init_m_ok0 : forall B c s rc n nt cx,
  s <> 0 -> nt <> 0 -> Cfg_max_cmds B <> 0 -> Cfg_max_cmds B <= 255 ->
  24 <= Cfg_max_body B -> Cfg_max_body B <= 1484 -> Cfg_desk_mac_set B = 0 ->
  diginet_session_init_m B c s rc n nt cx =
  Some (upd (upd (upd (upd (upd (upd (upd (upd (upd B 1648 (put (Z.to_nat 18264) 0)) 1648 (sub B 65024 60))
                  1712 (put 8 c)) 1720 (put 8 s)) 1728 (put 8 rc)) 1736 (put 8 n)) 1744 (put 8 nt))
              1752 (put 8 cx)) 1760 (put 4 0), DIGINET_OK).
Proof.
  intros B c s rc n nt cx Hs Hnt H1 H2 H3 H4 Hd. unfold diginet_session_init_m.
  replace ((s =? 0) || (nt =? 0))%bool with false
    by (symmetry; apply Bool.orb_false_iff; split; apply Z.eqb_neq; assumption).
  replace ((Cfg_max_cmds B =? 0) || (Cfg_max_body B <? DIGINET_CMD_MAX_LEN)
           || (DIGINET_MAX_BODY_LEN <? Cfg_max_body B) || (255 <? Cfg_max_cmds B))%bool with false
    by (symmetry; unfold DIGINET_CMD_MAX_LEN, DIGINET_MAX_BODY_LEN;
        apply Bool.orb_false_iff; split;
        [ apply Bool.orb_false_iff; split;
          [ apply Bool.orb_false_iff; split; [apply Z.eqb_neq; assumption | apply Z.ltb_ge; lia]
          | apply Z.ltb_ge; lia ]
        | apply Z.ltb_ge; lia ]).
  cbv zeta.
  replace (Cfg_desk_mac_set B =? 0) with true by (symmetry; apply Z.eqb_eq; exact Hd).
  cbn [negb].
  cbv beta delta [set_S_state set_S_notify_ctx set_S_notify set_S_io_now_us set_S_io_recv set_S_io_send
    set_S_io_ctx A_S_state A_S_notify_ctx A_S_notify A_S_io_now_us A_S_io_recv A_S_io_send A_S_io_ctx
    A_S_cfg_host_mac OFF_g_s OFF_g_cfg SZ_g_s SZ_g_cfg DIGINET_S_IDLE].
  reflexivity.
Qed.

(* :63-71 and :74 with a desk MAC *)
Lemma init_m_ok1 : forall B c s rc n nt cx,
  s <> 0 -> nt <> 0 -> Cfg_max_cmds B <> 0 -> Cfg_max_cmds B <= 255 ->
  24 <= Cfg_max_body B -> Cfg_max_body B <= 1484 -> Cfg_desk_mac_set B <> 0 ->
  diginet_session_init_m B c s rc n nt cx =
  Some (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd B 1648 (put (Z.to_nat 18264) 0))
                  1648 (sub B 65024 60)) 1712 (put 8 c)) 1720 (put 8 s)) 1728 (put 8 rc)) 1736 (put 8 n))
              1744 (put 8 nt)) 1752 (put 8 cx)) 1760 (put 4 0)) 1768 (sub B 65030 6)) 1764 (put 4 1),
         DIGINET_OK).
Proof.
  intros B c s rc n nt cx Hs Hnt H1 H2 H3 H4 Hd. unfold diginet_session_init_m.
  replace ((s =? 0) || (nt =? 0))%bool with false
    by (symmetry; apply Bool.orb_false_iff; split; apply Z.eqb_neq; assumption).
  replace ((Cfg_max_cmds B =? 0) || (Cfg_max_body B <? DIGINET_CMD_MAX_LEN)
           || (DIGINET_MAX_BODY_LEN <? Cfg_max_body B) || (255 <? Cfg_max_cmds B))%bool with false
    by (symmetry; unfold DIGINET_CMD_MAX_LEN, DIGINET_MAX_BODY_LEN;
        apply Bool.orb_false_iff; split;
        [ apply Bool.orb_false_iff; split;
          [ apply Bool.orb_false_iff; split; [apply Z.eqb_neq; assumption | apply Z.ltb_ge; lia]
          | apply Z.ltb_ge; lia ]
        | apply Z.ltb_ge; lia ]).
  cbv zeta.
  replace (Cfg_desk_mac_set B =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hd).
  cbn [negb].
  cbv beta delta [set_S_desk_known set_S_desk_mac set_S_state set_S_notify_ctx set_S_notify set_S_io_now_us
    set_S_io_recv set_S_io_send set_S_io_ctx A_S_desk_known A_S_desk_mac A_S_state A_S_notify_ctx A_S_notify
    A_S_io_now_us A_S_io_recv A_S_io_send A_S_io_ctx A_S_cfg_host_mac Cfg_desk_mac A_Cfg_desk_mac
    OFF_g_s OFF_g_cfg SZ_g_s SZ_g_cfg DIGINET_S_IDLE].
  reflexivity.
Qed.

(* ================ tactics ================ *)

(* a closed branch condition *)
Ltac wfalse :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false by (vm_compute; reflexivity); cbv iota
  end.

(* the destination cell of a libc call, at world offset k *)
Ltac wpiece k :=
  lazymatch goal with
  | H : rw_cells ?segs ?mm ?A [CB (Z.to_nat W_LEN) ?BB] |- rw_cells ?segs ?mm ?X [CB (Z.to_nat ?n) _] =>
      apply (wm_piece segs A mm BB k n X);
      [ exact H
      | first [ reflexivity | (vm_compute; reflexivity) ]
      | lia
      | (rewrite ?unsigned_lit by lia; lia)
      | (rewrite ?unsigned_lit by lia; unfold W_LEN; lia) ]
  end.

(* the length of a chain of writes over the 18264-byte image of g_s *)
(* the hypothesis giving the length of exactly this list, matched syntactically: `assumption` would let the
   conversion check compare other upd / sub chains and unfold Z.to_nat of world offsets *)
Ltac glen_hyp :=
  match goal with
  | |- Z.of_nat (length ?X) = _ =>
      match goal with H : Z.of_nat (length ?Y) = _ |- _ => constr_eq X Y; exact H end
  end.

Ltac glen := first [ glen_hyp
                   | (apply Lupd; [ lia | (rewrite ?length_put, ?length_app; lia) | glen ]) ].

(* fold a world store at g_s + d back into the canonical world [upd B OFF_g_s G] *)
Ltac wfold d :=
  lazymatch goal with
  | H : rw_cells _ _ _ [CB (Z.to_nat W_LEN) (upd (upd ?BB 1648 ?G) ?j ?v)] |- _ =>
      rewrite (upd_nest BB G v 1648 d j) in H;
      [ lazymatch type of H with
        | rw_cells _ _ _ [CB _ (upd _ _ ?G2)] =>
            let g := fresh "G" in let lg := fresh "LG" in
            set (g := G2) in H;
            assert (lg : Z.of_nat (length g) = 18264) by (unfold g; glen)
        end
      | lia | lia | lia
      | (rewrite ?length_put, ?length_app; lia)
      | lia ]
  end.

(* a stored `lh` value is the two config bytes it was read from *)
Ltac wmac BB k :=
  lazymatch goal with
  | H : rw_cells _ _ _ [CB (Z.to_nat W_LEN) _] |- _ => rewrite (put_sub2 BB k) in H by lia
  end.

(* the kit's post_call with the stack window carried across the callee's span *)
Ltac wcall_post segs m :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MIc" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  try destruct_ands PO;
  lazymatch type of MUc with
  | munch _ m ?m' =>
      lazymatch goal with
      | STq : stk segs m ?loq ?hiq, D : rw_cells segs m' ?X [CB (Z.to_nat ?nn) ?src] |- _ =>
          let ST2 := fresh "ST" in
          assert (ST2 : stk segs m' loq hiq)
            by (apply (stk_fill segs m m' loq hiq X nn src); [exact STq | exact MUc | exact WMc | exact D]);
          clear STq
      end;
      wk_facts;
      wk_world_after_call segs m m';
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

(* the current mem_inv, found by its syntax (eassumption would unfold other definitions to compare) *)
Ltac wmi :=
  lazymatch goal with
  | |- mem_inv ?segs ?mm => lazymatch goal with H : mem_inv segs mm |- _ => exact H end
  end.

(* jump to the shared epilogue: its frame, stack, footprint, writability, mem_inv and world facts are passed by
   name, found by their syntax; what is left is the world and the result against the model *)
Ltac wepi EPI :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with
      | FRx : rw_cells _ mm (bv_unsigned _ + -48) _ |- _ =>
      lazymatch goal with
      | STx : stk _ mm _ _ |- _ =>
      lazymatch goal with
      | MUx : munch _ _ mm |- _ =>
      lazymatch goal with
      | WOx : wmono _ _ mm |- _ =>
      lazymatch goal with
      | MIx : mem_inv _ mm |- _ =>
      lazymatch goal with
      | WMx : rw_cells _ mm _ [CB (Z.to_nat W_LEN) _] |- _ =>
          eapply (EPI mm _ _  _ _ _ _ _ _ _ _ _ _  _ _ _ _ _ _ _ _ _ _  FRx STx MUx WOx MIx WMx)
      end end end end end end
  end.

(* ================ the walk ================ *)

Theorem diginet_session_init_holds :
  memset_contract -> memcpy_contract -> diginet_session_init_contract.
Proof.
  intros MSET MCPY.
  unfold diginet_session_init_contract, diginet_session_init_ENTRY, diginet_session_init_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo iop io_ctx io_send io_recv io_now ntf ctx r B B'
         Ea0 Ea1 Ea2 Ea3 Ea4 Hioc Hios Hior Hion Hntf Hctx HIO ABLK HAL WM HM Hsp ST LO WS MI.
  subst a0 a1 a2 a3 a4.
  destruct ABLK as (Hp0 & Hp1 & HOW & HWIN).
  unfold off_world in HOW. unfold off_window in HWIN. unfold w_off_stack in WS.
  assert (EGS : OFF_g_s = 1648) by reflexivity.
  assert (EGC : OFF_g_cfg = 65024) by reflexivity.
  assert (EA0 : bv_unsigned (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) = 211312) by (vm_compute; reflexivity).
  assert (EA1 : bv_unsigned (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_cfg)) = 274688) by (vm_compute; reflexivity).
  assert (EN1 : bv_unsigned (Z_to_bv 64 18264) = 18264) by (vm_compute; reflexivity).
  assert (EN2 : bv_unsigned (Z_to_bv 64 60) = 60) by (vm_compute; reflexivity).
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof (wm_len rsegs W_BASE_UBSAN m B WM) as LBn.
  assert (LB : Z.of_nat (length B) = 65616)
    by (rewrite LBn, Z2Nat.id by (unfold W_LEN; lia); unfold W_LEN; reflexivity).
  assert (Lcfg : Z.of_nat (length (sub B 65024 60)) = 60) by (rewrite length_sub by lia; lia).
  assert (Lm0 : Z.of_nat (length (sub B 65030 2)) = 2) by (rewrite length_sub by lia; lia).
  assert (Lm1 : Z.of_nat (length (sub B 65032 2)) = 2) by (rewrite length_sub by lia; lia).
  assert (Lm2 : Z.of_nat (length (sub B 65034 2)) = 2) by (rewrite length_sub by lia; lia).
  assert (Lio0 : Z.of_nat (length (put 8 io_ctx)) = 8) by (rewrite length_put; reflexivity).
  assert (Lio1 : Z.of_nat (length (put 8 io_send)) = 8) by (rewrite length_put; reflexivity).
  assert (Lio2 : Z.of_nat (length (put 8 io_recv)) = 8) by (rewrite length_put; reflexivity).
  assert (Lio3 : Z.of_nat (length (put 8 io_now)) = 8) by (rewrite length_put; reflexivity).
  assert (Lio : Z.of_nat (length (put 8 io_ctx ++ put 8 io_send ++ put 8 io_recv ++ put 8 io_now)) = 32)
    by (rewrite !length_app, !length_put; reflexivity).
  wk_facts.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WO.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  carve_frame 48%nat ST.
  do 7 step.
  lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -48) ?cs |- _ => set (FRC := cs) in H end.
  assert (LFRC : Z.of_nat (cells_size FRC) = 48) by (unfold FRC; reflexivity).
  (* the shared epilogue at 0x16ad4 *)
  assert (EPI : forall (m2 : word -> option byte) (B2 : list byte) (v : Z)
                  (ra' u5 u6 u7 u8 u9 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u28 u29 u30 u31 : word),
    rw_cells rsegs m2 (bv_unsigned sp + -48) FRC ->
    stk rsegs m2 lo (bv_unsigned sp + -48) ->
    munch [(bv_unsigned sp + -48, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m m2 ->
    wmono rsegs m m2 -> mem_inv rsegs m2 -> wmem rsegs m2 B2 ->
    B2 = B' -> v = r ->
    evt rsegs QQ
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u5 u6 u7 u8 u9 (Z_to_bv 64 v)
                u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 s5 s6 s7 s8 s9 s10 s11 u28 u29 u30 u31)
          F (Z_to_bv 64 0x16ad4) fc None m2 (seg_rom rsegs))).
  { intros m2 B2 v ra' u5 u6 u7 u8 u9 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u28 u29 u30 u31
      FR2 ST2 MU2 WO2 MI2 WM2 EB Ev.
    subst B2 v. unfold FRC in FR2.
    do 6 step.
    release_frame FR2 ST2 (bv_unsigned sp).
    do 2 step.
    apply evt_done. unfold QQ. do 15 eexists.
    split; [reflexivity|]. split; [exact MU2|]. split; [exact WO2|]. split; [exact MI2|].
    split; [exact ST2 | exact WM2]. }
  cbv beta delta [mkR] in EPI.
  (* 0x169f0 mv s0,a0; li a0,-1; beqz s0 (s = &g_s is not NULL) *)
  do 3 step. wfalse.
  (* 0x169fc mv s1,a1; beqz a1 (cfg = &g_cfg is not NULL) *)
  do 2 step. wfalse.
  (* 0x16a04 mv s4,a2; beqz a2 (io is not NULL) *)
  do 2 step.
  rewrite (eqb0_lit iop) by lia.
  replace (iop =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  (* 0x16a0c andi a1,s4,7; bnez a1 (io is 8-aligned) *)
  do 2 step.
  rewrite (unsigned_lit iop) by lia. rewrite (land7 iop ltac:(lia) HAL). wfalse.
  (* 0x16a14 mv s3,a3; beqz a3 (notify) *)
  do 2 step.
  rewrite (eqb0_lit ntf) by lia.
  destruct (Z.eqb_spec ntf 0) as [Ent|Ent]; cbv iota.
  { rewrite (init_m_arg B io_ctx io_send io_recv io_now ntf ctx ltac:(right; exact Ent)) in HM.
    destruct (some_pair_inv HM) as [EB Er].
    wepi EPI; [ exact EB | exact Er ]. }
  (* 0x16a1c ld a1,8(s4): io->send *)
  pose proof (io_read rsegs _ iop 8 io_ctx io_send io_recv io_now HIO ltac:(lia) ltac:(lia)) as RD.
  rewrite io_sub8 in RD.
  step. clear RD.
  (* 0x16a20 beqz a1 *)
  step.
  rewrite (eqb0_lit io_send) by lia.
  destruct (Z.eqb_spec io_send 0) as [Esd|Esd]; cbv iota.
  { rewrite (init_m_arg B io_ctx io_send io_recv io_now ntf ctx ltac:(left; exact Esd)) in HM.
    destruct (some_pair_inv HM) as [EB Er].
    wepi EPI; [ exact EB | exact Er ]. }
  (* 0x16a24 andi a1,s1,3; bnez a1 (&g_cfg is 4-aligned) *)
  do 2 step. wfalse.
  (* 0x16a2c lw a1,52(s1): cfg.max_cmds; beqz a1 *)
  do 2 step.
  rewrite eqb0_s32.
  rewrite s32_eqb0.
  change (u_at B 65076 4) with (Cfg_max_cmds B).
  destruct (Z.eqb_spec (Cfg_max_cmds B) 0) as [Ecm|Ecm]; cbv iota.
  { rewrite (init_m_cfg B io_ctx io_send io_recv io_now ntf ctx ltac:(left; exact Ecm)) in HM.
    destruct (some_pair_inv HM) as [EB Er].
    wepi EPI; [ exact EB | exact Er ]. }
  (* 0x16a34 li a2,255; bltu a2,a1 *)
  do 2 step.
  rewrite (ltu_s32 255 B 65076) by lia.
  change (u_at B 65076 4) with (Cfg_max_cmds B).
  destruct (Z.ltb_spec 255 (Cfg_max_cmds B)) as [Ecm2|Ecm2]; cbv iota.
  { rewrite (init_m_cfg B io_ctx io_send io_recv io_now ntf ctx ltac:(right; left; exact Ecm2)) in HM.
    destruct (some_pair_inv HM) as [EB Er].
    wepi EPI; [ exact EB | exact Er ]. }
  (* 0x16a3c lw a1,56(s1); addiw a1,a1,-1485; li a2,-1461; bltu a1,a2 *)
  do 4 step.
  rewrite (body_cond B 65080).
  change (u_at B 65080 4) with (Cfg_max_body B).
  destruct (Z.ltb_spec (Cfg_max_body B) 24) as [Eb1|Eb1]; cbn [orb].
  { cbv iota.
    rewrite (init_m_cfg B io_ctx io_send io_recv io_now ntf ctx ltac:(right; right; left; exact Eb1)) in HM.
    destruct (some_pair_inv HM) as [EB Er].
    wepi EPI; [ exact EB | exact Er ]. }
  destruct (Z.ltb_spec 1484 (Cfg_max_body B)) as [Eb2|Eb2]; cbv iota.
  { rewrite (init_m_cfg B io_ctx io_send io_recv io_now ntf ctx ltac:(right; right; right; exact Eb2)) in HM.
    destruct (some_pair_inv HM) as [EB Er].
    wepi EPI; [ exact EB | exact Er ]. }
  (* 0x16a4c mv s2,a4; lui a0,0x4; addiw a2,a0,1880; mv a0,s0; li a1,0; jal memset *)
  do 6 step.
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut; [ eapply MSET; [ wpiece 1648 | wmi ] | wcall_post rsegs mm ]
  end.
  (* the world is now [upd B OFF_g_s zeros] *)
  lazymatch goal with
  | H : rw_cells _ _ _ [CB (Z.to_nat W_LEN) (upd B 1648 _)] |- _ =>
      rewrite (unsigned_lit 0) in H by lia; rewrite (unsigned_lit 18264) in H by lia;
      change (Z_to_bv 8 (0 mod 256)) with (Z_to_bv 8 0) in H;
      rewrite <- put_zeros in H;
      set (G := put (Z.to_nat 18264) 0) in H
  end.
  assert (LG : Z.of_nat (length G) = 18264) by (unfold G; rewrite length_put; lia).
  (* 0x16a64 andi a0,s0,7; bnez a0 (&g_s is 8-aligned) *)
  do 2 step. wfalse.
  (* 0x16a6c li a2,60; mv a0,s0; mv a1,s1; jal memcpy *)
  do 4 step.
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  eapply evt_cut;
  [ eapply MCPY with (src := sub (upd B 1648 G) 65024 60);
      [ lazymatch goal with
        | H : rw_cells ?segs ?mx ?A [CB (Z.to_nat W_LEN) ?BB] |- _ =>
            apply (wm_src segs A mx BB 65024 60);
            [ exact H | first [ reflexivity | (vm_compute; reflexivity) ] | lia | (unfold W_LEN; lia) ]
        end
      | (rewrite EN2;
         rewrite length_sub by (first [ lia | (rewrite (length_upd B G 1648) by lia; lia) ]);
         reflexivity)
      | wpiece 1648
      | (rewrite EA0, EA1, EN2; lia)
      | wmi ]
  | wcall_post rsegs mm ]
  end.
  (* the copied bytes are g_cfg's, untouched by the memset *)
  lazymatch goal with
  | H : rw_cells _ _ _ [CB (Z.to_nat W_LEN) (upd (upd B 1648 _) 1648 _)] |- _ =>
      rewrite (sub_upd_out B G 1648 65024 60) in H by (unfold G; rewrite ?length_put; lia)
  end.
  wfold 0.
  (* 0x16a7c ld a0,24(s4); sd a0,88(s0) *)
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (io_read rsegs mm iop 24 io_ctx io_send io_recv io_now HIO ltac:(lia) ltac:(lia))
        as RD
  end.
  rewrite io_sub24 in RD.
  step. clear RD. step. wfold 88.
  (* 0x16a84 ld a0,16(s4); sd a0,80(s0) *)
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (io_read rsegs mm iop 16 io_ctx io_send io_recv io_now HIO ltac:(lia) ltac:(lia))
        as RD
  end.
  rewrite io_sub16 in RD.
  step. clear RD. step. wfold 80.
  (* 0x16a8c ld a0,8(s4); sd a0,72(s0) *)
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (io_read rsegs mm iop 8 io_ctx io_send io_recv io_now HIO ltac:(lia) ltac:(lia))
        as RD
  end.
  rewrite io_sub8 in RD.
  step. clear RD. step. wfold 72.
  (* 0x16a94 ld a0,0(s4); sd a0,64(s0) *)
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (io_read rsegs mm iop 0 io_ctx io_send io_recv io_now HIO ltac:(lia) ltac:(lia))
        as RD
  end.
  rewrite io_sub0 in RD. rewrite Z.add_0_r in RD.
  step. clear RD. step. wfold 64.
  (* 0x16a9c lw a0,12(s1): cfg.desk_mac_set, read past the writes to g_s *)
  step.
  lazymatch goal with
  | LGx : Z.of_nat (length ?GG) = 18264 |- context [s32_at (upd B 1648 ?GG) 65036] =>
      rewrite (s32_at_upd_out B GG 1648 65036) by lia
  end.
  (* 0x16aa0 sd s3,96(s0); sd s2,104(s0); sw zero,112(s0) *)
  step. wfold 96.
  step. wfold 104.
  step. wfold 112.
  (* 0x16aac beqz a0 *)
  step.
  rewrite eqb0_s32.
  destruct (Z.eqb_spec (s32_at B 65036) 0) as [Edk|Edk]; cbv iota.
  { (* no desk MAC: the model's else branch, result 0 *)
    assert (Edk' : Cfg_desk_mac_set B = 0)
      by (unfold Cfg_desk_mac_set, A_Cfg_desk_mac_set, OFF_g_cfg; exact Edk).
    rewrite (init_m_ok0 B io_ctx io_send io_recv io_now ntf ctx Esd Ent Ecm ltac:(lia) ltac:(lia) ltac:(lia)
                  Edk') in HM.
    destruct (some_pair_inv HM) as [EB Er].
    wepi EPI; [ | (rewrite <- Er; unfold DIGINET_OK; exact Edk) ].
    rewrite <- EB.
    unfold G7, G6, G5, G4, G3, G2, G1, G0.
    apply init_eq_ok;
      [ exact LB | exact LG | exact Lcfg | exact Lio0 | exact Lio1 | exact Lio2 | exact Lio3
      | (rewrite length_put; reflexivity) .. ]. }
  (* 0x16ab0 li a0,0; lh a1,10(s1); sh a1,124(s0) *)
  assert (Edk' : Cfg_desk_mac_set B <> 0) by (unfold Cfg_desk_mac_set, A_Cfg_desk_mac_set, OFF_g_cfg; exact Edk).
  rewrite (init_m_ok1 B io_ctx io_send io_recv io_now ntf ctx Esd Ent Ecm ltac:(lia) ltac:(lia) ltac:(lia) Edk')
    in HM.
  destruct (some_pair_inv HM) as [EB Er].
  do 2 step.
  lazymatch goal with
  | LGx : Z.of_nat (length ?GG) = 18264 |- context [u_at (upd B 1648 ?GG) 65034 2] =>
      rewrite (u_at_upd_out B GG 1648 65034 2) by lia
  end.
  step.
  wmac B 65034.
  wfold 124.
  (* 0x16abc lh a1,8(s1); sh a1,122(s0) *)
  step.
  lazymatch goal with
  | LGx : Z.of_nat (length ?GG) = 18264 |- context [u_at (upd B 1648 ?GG) 65032 2] =>
      rewrite (u_at_upd_out B GG 1648 65032 2) by lia
  end.
  step.
  wmac B 65032.
  wfold 122.
  (* 0x16ac4 lh a1,6(s1); li a2,1; sw a2,116(s0); sh a1,120(s0) *)
  step.
  lazymatch goal with
  | LGx : Z.of_nat (length ?GG) = 18264 |- context [u_at (upd B 1648 ?GG) 65030 2] =>
      rewrite (u_at_upd_out B GG 1648 65030 2) by lia
  end.
  do 2 step. wfold 116.
  step.
  wmac B 65030.
  wfold 120.
  wepi EPI; [ | (rewrite <- Er; reflexivity) ].
  rewrite <- EB.
  replace (sub B 65030 6) with (sub B 65030 2 ++ sub B 65032 2 ++ sub B 65034 2)
    by (rewrite (sub_app2' B 65032 65034 2 2) by lia; rewrite (sub_app2' B 65030 65032 2 (2 + 2)) by lia;
        reflexivity).
  unfold G11, G10, G9, G8.
  rewrite (init_eq_desk B G7 (sub B 65030 2) (sub B 65032 2) (sub B 65034 2) (put 4 1));
    [ | exact LB | glen_hyp | exact Lm0 | exact Lm1 | exact Lm2 | (rewrite length_put; reflexivity) ].
  f_equal. f_equal.
  unfold G7, G6, G5, G4, G3, G2, G1, G0.
  apply init_eq_ok;
    [ exact LB | exact LG | exact Lcfg | exact Lio0 | exact Lio1 | exact Lio2 | exact Lio3
    | (rewrite length_put; reflexivity) .. ].
Qed.
