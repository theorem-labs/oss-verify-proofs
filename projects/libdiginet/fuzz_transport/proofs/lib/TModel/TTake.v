(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/mbedtls/fuzz_pkcs7/lib/Lib/Asn1Aux.v; 542 of its 587 lines of code are new or changed and 404 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_frame/lib/U/Prog/diginet_frame_build.v, with its module paths changed; 334 of its 395 lines of code are new or changed and 526 lines of the source are left out. *)
(* Facts of the walk of take (transport/src/diginet_session.c:353-386) that hold in both builds: the register
   arithmetic of its comparisons, the world algebra of the queue copy, one turn of take_m's loops, the cell lemmas
   of the body buffer and the frame, and the tactics both walks (Prog/T/take.v, U/Prog/T/take.v) share. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TSess0.
Import ListNotations.
Open Scope Z_scope.

(** * Arithmetic of the registers *)

Lemma tk_zext_shl5 : forall k, 0 <= k < 2 ^ 27 ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 k)) 32))) 27 = 32 * k.
Proof.
  intros k Hk. rewrite (unsigned_lit k) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (unsigned_lit (k * 2 ^ 32)) by lia. rewrite Z.shiftr_div_pow2 by lia.
  replace (k * 2 ^ 32) with (32 * k * 2 ^ 27) by lia. apply Z.div_mul. lia.
Qed.

Lemma tk_ltu_lits : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma tk_zext32 : forall k, 0 <= k < 2 ^ 31 ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 k)) 32))) 32 = k.
Proof.
  intros k Hk. rewrite (unsigned_lit k) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (unsigned_lit (k * 2 ^ 32)) by lia. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_mul. lia.
Qed.

Lemma tk_mod64_neg : forall x, - 2 ^ 64 <= x < 0 -> x mod 2 ^ 64 = x + 2 ^ 64.
Proof. intros x Hx. Z.div_mod_to_equations. lia. Qed.

Lemma tk_eqb_lits : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

(* a signed value against 0 (beqz of a register holding a C int) *)
Lemma tk_eqb0 : forall v, - 2 ^ 63 <= v < 2 ^ 63 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
  intros v Hv. unfold bv_eqb. rewrite !unsigned_lit_wrap. change (0 mod 2 ^ 64) with 0.
  destruct (Z.eqb_spec v 0) as [->|N]; [reflexivity|].
  apply Z.eqb_neq. intros E. apply Z.mod_divide in E; [|lia]. destruct E as [c Ec]. nia.
Qed.

Lemma tk_swrap32_small : forall z, - 2 ^ 31 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof. intros z Hz. apply bv_swrap_small. change (bv_half_modulus 32) with (2 ^ 31). lia. Qed.

(* the two forms of a 32-bit world field in a register: lwu gives u_at, lw gives s32_at *)
Lemma tk_s32_val : forall B k, s32_at B k = (if u_at B k 4 <? 2 ^ 31 then u_at B k 4 else u_at B k 4 - 2 ^ 32).
Proof.
  intros B k. pose proof (u_at_range B k 4) as R. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R.
  unfold s32_at, bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31).
  change (bv_modulus 32) with (2 ^ 32).
  destruct (Z.ltb_spec (u_at B k 4) (2 ^ 31)) as [S|S].
  - rewrite Z.mod_small by lia. lia.
  - replace (u_at B k 4 + 2 ^ 31) with ((u_at B k 4 - 2 ^ 31) + 1 * 2 ^ 32) by lia.
    rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. lia.
Qed.

Lemma tk_ltu_s32 : forall t B k, 0 <= t < 2 ^ 31 ->
  bv_ltu (Z_to_bv 64 t) (Z_to_bv 64 (s32_at B k)) = (t <? u_at B k 4).
Proof.
  intros t B k Ht. pose proof (u_at_range B k 4) as R. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R.
  unfold bv_ltu. rewrite (unsigned_lit t) by lia. rewrite unsigned_lit_wrap. rewrite tk_s32_val.
  destruct (Z.ltb_spec (u_at B k 4) (2 ^ 31)) as [S|S].
  - rewrite Z.mod_small by lia. reflexivity.
  - rewrite (tk_mod64_neg (u_at B k 4 - 2 ^ 32)) by lia.
    replace (t <? u_at B k 4) with true by (symmetry; apply Z.ltb_lt; lia).
    apply Z.ltb_lt. lia.
Qed.

Lemma tk_eqb_s32 : forall t B k, 0 <= t < 2 ^ 31 ->
  bv_eqb (Z_to_bv 64 t) (Z_to_bv 64 (s32_at B k)) = (t =? u_at B k 4).
Proof.
  intros t B k Ht. pose proof (u_at_range B k 4) as R. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R.
  unfold bv_eqb. rewrite (unsigned_lit t) by lia. rewrite unsigned_lit_wrap. rewrite tk_s32_val.
  destruct (Z.ltb_spec (u_at B k 4) (2 ^ 31)) as [S|S].
  - rewrite Z.mod_small by lia. reflexivity.
  - rewrite (tk_mod64_neg (u_at B k 4 - 2 ^ 32)) by lia.
    replace (t =? u_at B k 4) with false by (symmetry; apply Z.eqb_neq; lia).
    apply Z.eqb_neq. lia.
Qed.

Lemma tk_s32_eq0 : forall B k, (s32_at B k =? 0) = (u_at B k 4 =? 0).
Proof.
  intros B k. pose proof (u_at_range B k 4) as R. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R.
  rewrite tk_s32_val. destruct (Z.ltb_spec (u_at B k 4) (2 ^ 31)) as [S|S]; [reflexivity|].
  destruct (Z.eqb_spec (u_at B k 4 - 2 ^ 32) 0); destruct (Z.eqb_spec (u_at B k 4) 0); lia || reflexivity.
Qed.

(* sext.w of a register that already holds a 32-bit field *)
Lemma tk_sextw_s32 : forall B k, bv_swrap 32 (bv_unsigned (Z_to_bv 64 (s32_at B k)) + 0) = s32_at B k.
Proof.
  intros B k. rewrite Z.add_0_r. pose proof (s32_range B k) as R.
  rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31).
  change (bv_modulus 32) with (2 ^ 32).
  destruct (Z_lt_le_dec (s32_at B k) 0) as [N|N].
  - rewrite (tk_mod64_neg (s32_at B k)) by lia.
    replace (s32_at B k + 2 ^ 64 + 2 ^ 31) with ((s32_at B k + 2 ^ 31) + 2 ^ 32 * (2 ^ 32)) by lia.
    rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. lia.
  - rewrite (Z.mod_small (s32_at B k) (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma tk_sextw_u : forall B k, bv_swrap 32 (bv_unsigned (Z_to_bv 64 (u_at B k 4)) + 0) = s32_at B k.
Proof.
  intros B k. pose proof (u_at_range B k 4) as R. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R.
  rewrite Z.add_0_r. rewrite unsigned_lit by lia. reflexivity.
Qed.

Lemma tk_sx32_small : forall v, 0 <= v < 2 ^ 31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sx32. rewrite (unsigned_lit v) by lia. f_equal. apply tk_swrap32_small. lia.
Qed.

Lemma tk_lor_256 : forall x y, 0 <= x < 256 -> 0 <= y < 256 -> 0 <= Z.lor x y < 256.
Proof. intros x y Hx Hy. change 256 with (2 ^ 8) in *. apply lor_lt_pow2; assumption. Qed.

(** * Algebra of the world *)

Lemma tk_firstn_add : forall {A} (n1 n2 : nat) (l : list A), firstn (n1 + n2) l = firstn n1 l ++ firstn n2 (skipn n1 l).
Proof.
  induction n1 as [|n1 IH]; intros n2 l; [reflexivity|].
  destruct l as [|x l]; cbn [Nat.add firstn skipn app]; [destruct n2; reflexivity | f_equal; apply IH].
Qed.

Lemma tk_sub_app : forall (B : list byte) k (n1 n2 : nat), 0 <= k ->
  sub B k (n1 + n2) = sub B k n1 ++ sub B (k + Z.of_nat n1) n2.
Proof.
  intros B k n1 n2 Hk. unfold sub. rewrite tk_firstn_add. f_equal. rewrite skipn_skipn. f_equal. f_equal. lia.
Qed.

Lemma tk_upd_app : forall (B X Y : list byte) k, 0 <= k ->
  k + Z.of_nat (length X) + Z.of_nat (length Y) <= Z.of_nat (length B) ->
  upd (upd B (k + Z.of_nat (length X)) Y) k X = upd B k (X ++ Y).
Proof.
  intros B X Y k Hk Hl. apply nth_error_ext. intros i.
  assert (L1 : length (upd B (k + Z.of_nat (length X)) Y) = length B) by (apply length_upd; lia).
  rewrite (ne_upd (upd B _ Y)) by lia. rewrite (ne_upd B (X ++ Y)) by (rewrite ?length_app; lia).
  rewrite (ne_upd B Y) by lia. rewrite length_app.
  destruct (Nat.leb_spec (Z.to_nat k) i); destruct (Nat.ltb_spec i (Z.to_nat k + length X));
    destruct (Nat.leb_spec (Z.to_nat (k + Z.of_nat (length X))) i);
    destruct (Nat.ltb_spec i (Z.to_nat (k + Z.of_nat (length X)) + length Y));
    destruct (Nat.ltb_spec i (Z.to_nat k + (length X + length Y)));
    cbn [andb]; try (exfalso; lia); try reflexivity.
  - rewrite nth_error_app1 by lia. reflexivity.
  - rewrite nth_error_app2 by lia. f_equal. lia.
Qed.

Lemma tk_put_u_at : forall (B : list byte) k n, 0 <= k -> k + Z.of_nat n <= Z.of_nat (length B) ->
  put n (u_at B k n) = sub B k n.
Proof.
  intros B k n Hk Hl. pose proof (length_sub B k n Hk Hl) as L. unfold put, u_at.
  remember (sub B k n) as s eqn:Es. rewrite <- L. apply StrFun.Z_to_le_bytes_to_Z.
Qed.

(* The four ld / sd pairs of the queue-entry copy, offsets 24, 16, 8, 0: the entry at j over the entry at k.
   k = j (the entry copied onto itself, kept = j in take_tail_m) leaves the world as it was. *)
Lemma tk_copy32 : forall (B : list byte) k j, 0 <= k -> 0 <= j -> (k = j \/ k + 32 <= j \/ j + 32 <= k) ->
  k + 32 <= Z.of_nat (length B) -> j + 32 <= Z.of_nat (length B) ->
  upd (upd (upd (upd B (k + 24) (put 8 (u_at B (j + 24) 8))) (k + 16) (put 8 (u_at B (j + 16) 8)))
         (k + 8) (put 8 (u_at B (j + 8) 8))) k (put 8 (u_at B j 8))
  = upd B k (sub B j 32).
Proof.
  intros B k j Hk Hj Hd Hk2 Hj2.
  rewrite !tk_put_u_at by lia.
  destruct Hd as [->|Hd]; [rewrite !upd_sub_id by lia; reflexivity|].
  assert (L : forall x, 0 <= x -> x + 8 <= Z.of_nat (length B) -> length (sub B x 8) = 8%nat)
    by (intros; apply length_sub; lia).
  replace (k + 24) with (k + 16 + Z.of_nat (length (sub B (j + 16) 8))) by (rewrite L by lia; lia).
  rewrite tk_upd_app by (rewrite ?L by lia; lia).
  replace (k + 16) with (k + 8 + Z.of_nat (length (sub B (j + 8) 8))) by (rewrite L by lia; lia).
  rewrite tk_upd_app by (rewrite ?length_app, ?L by lia; lia).
  replace (k + 8) with (k + Z.of_nat (length (sub B j 8))) by (rewrite L by lia; lia).
  rewrite tk_upd_app by (rewrite ?length_app, ?L by lia; lia).
  f_equal.
  replace 32%nat with (8 + (8 + (8 + 8)))%nat by reflexivity.
  rewrite !tk_sub_app by lia. change (Z.of_nat 8) with 8.
  replace (j + 8 + 8) with (j + 16) by lia. replace (j + 16 + 8) with (j + 24) by lia. reflexivity.
Qed.

Lemma tk_queued_upd : forall (B v : list byte) k, 0 <= k < 512 -> length v = 32%nat ->
  Z.of_nat (length B) = W_LEN -> S_queued (upd B (OFF_g_s + 1760 + 32 * k) v) = S_queued B.
Proof.
  intros B v k Hk Lv LB. unfold S_queued. apply u_at_upd_out; rewrite ?Lv, ?LB;
    unfold A_S_queued, OFF_g_s, W_LEN; lia.
Qed.

Lemma tk_fail_upd : forall (B v : list byte) k, 0 <= k < 512 -> length v = 32%nat ->
  Z.of_nat (length B) = W_LEN -> g_fail_next (upd B (OFF_g_s + 1760 + 32 * k) v) = g_fail_next B.
Proof.
  intros B v k Hk Lv LB. unfold g_fail_next. apply u_at_upd_out; rewrite ?Lv, ?LB;
    unfold OFF_g_fail_next, OFF_g_s, W_LEN; lia.
Qed.


Lemma tk_fail_queued : forall (B : list byte) v, Z.of_nat (length B) = W_LEN ->
  g_fail_next (upd B 19792 (put 4 v)) = g_fail_next B.
Proof.
  intros B v LB. unfold g_fail_next. apply u_at_upd_out; rewrite ?length_put, ?LB;
    unfold A_S_queued, OFF_g_fail_next, OFF_g_s, W_LEN; lia.
Qed.
(* the world after s->queue[k] = (32 bytes of the entry j): its length, s->queued and g_fail_next are kept *)
Ltac tk_upd_facts :=
  rewrite ?tk_queued_upd, ?tk_fail_upd by first [ (apply length_sub; lia) | lia ].

(* one turn of the model's loops *)
Lemma tk_tail_S : forall B kept j n, take_tail_m B kept j (S n) =
  if (S_queue_N <=? j) || (S_queue_N <=? kept) then None
  else take_tail_m (upd B (A_S_queue_bytes kept) (sub B (A_S_queue_bytes j) 32)) (kept + 1) (j + 1) n.
Proof. reflexivity. Qed.

Lemma tk_loop_S : forall B allow i taken kept len hd body n,
  take_loop_m B allow i taken kept len hd body (S n) =
  if S_queue_N <=? i then None
  else
  let clen := S_queue_len B i in
  let fits0 := (taken <? S_cfg_max_cmds B) && (len + clen <=? S_cfg_max_body B) &&
               (negb (allow =? 0) || (S_queue_display B i =? 0)) in
  if fits0 && (DIGINET_MAX_BODY_LEN <? len + clen) then None
  else
  let cand := body ++ sub B (A_S_queue_bytes i) (Z.to_nat clen) in
  let fits := fits0 && (body_check cand =? DIGINET_OK) in
  let '(B1, body1, len1, taken1, hd1, kept1) :=
    if fits then (B, cand, len + clen, taken + 1, Z.lor hd (S_queue_display B i), kept)
    else ((if kept =? i then B else upd B (A_S_queue_bytes kept) (sub B (A_S_queue_bytes i) 32)),
          body, len, taken, hd, kept + 1) in
  if (taken1 =? S_cfg_max_cmds B1) || (len1 =? S_cfg_max_body B1) then
    match take_tail_m B1 kept1 (i + 1) (Z.to_nat (S_queued B1 - (i + 1))) with
    | None => None
    | Some (B3, kept2) => Some (B3, (body1, len1, hd1, taken1, kept2))
    end
  else take_loop_m B1 allow (i + 1) taken1 kept1 len1 hd1 body1 n.
Proof. reflexivity. Qed.

(** * Cells (the shape of the lemmas is diginet_frame_build.v's rw_cells_split2 .. rw_cb_split) *)

Section Cells.
Context {segs : list Segment}.

Lemma tk_split2 : forall m A A2 cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) -> A2 = A + Z.of_nat (cells_size cs1) ->
  rw_cells segs m A cs1 /\ rw_cells segs m A2 cs2.
Proof.
  intros m A A2 cs1 cs2 [[Hwf Hb] (Ha & Hn & Hw)] ->.
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

Lemma tk_join2 : forall m A A2 cs1 cs2,
  rw_cells segs m A cs1 -> A2 = A + Z.of_nat (cells_size cs1) -> rw_cells segs m A2 cs2 ->
  rw_cells segs m A (cs1 ++ cs2).
Proof.
  intros m A A2 cs1 cs2 [[W1 B1] (Ha & Hn & Hw1)] -> [[W2 B2] (Hb & Hn2 & Hw2)].
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

Lemma tk_rebytes : forall m A cs cs',
  rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells segs m A cs'.
Proof.
  intros m A cs cs' [[Hwf Hb] Hw] Hwf' Heq. split; [split; [exact Hwf' | rewrite Heq; exact Hb] |].
  rewrite <- (cells_bytes_length cs') by assumption. rewrite Heq. rewrite cells_bytes_length by assumption. exact Hw.
Qed.

Lemma tk_cb_split : forall m A (k r : nat) l,
  rw_cells segs m A [CB (k + r) l] ->
  rw_cells segs m A [CB k (firstn k l)] /\ rw_cells segs m (A + Z.of_nat k) [CB r (skipn k l)].
Proof.
  intros m A k r l H.
  assert (Hl : length l = (k + r)%nat) by (destruct H as [[[Hl _] _] _]; exact Hl).
  apply (tk_split2 m A (A + Z.of_nat k) [CB k (firstn k l)] [CB r (skipn k l)]); [|cbn; lia].
  eapply tk_rebytes; [exact H| |].
  - cbn. rewrite length_firstn, length_skipn. repeat split; lia.
  - cbn. rewrite !app_nil_r. apply firstn_skipn.
Qed.

Lemma tk_cb_join : forall m A (n1 n2 : nat) l1 l2, length l1 = n1 -> length l2 = n2 ->
  rw_cells segs m A [CB n1 l1] -> rw_cells segs m (A + Z.of_nat n1) [CB n2 l2] ->
  rw_cells segs m A [CB (n1 + n2) (l1 ++ l2)].
Proof.
  intros m A n1 n2 l1 l2 L1 L2 R1 R2.
  pose proof (tk_join2 m A (A + Z.of_nat n1) [CB n1 l1] [CB n2 l2] R1 ltac:(cbn [cells_size csize]; lia) R2) as J.
  eapply tk_rebytes; [exact J| |].
  - cbn [cells_wf cell_wf]. rewrite length_app. split; [lia | exact I].
  - cbn [app cells_bytes cbytes]. rewrite !app_nil_r. reflexivity.
Qed.

(* the body buffer split at [len, len + c->len): the destination cell of the memcpy of :365 *)
Lemma tk_cb_split3 : forall m A (L C R : nat) l,
  rw_cells segs m A [CB (L + C + R) l] ->
  rw_cells segs m A [CB L (firstn L l)] /\
  rw_cells segs m (A + Z.of_nat L) [CB C (firstn C (skipn L l))] /\
  rw_cells segs m (A + Z.of_nat L + Z.of_nat C) [CB R (skipn C (skipn L l))].
Proof.
  intros m A L C R l H.
  replace (L + C + R)%nat with (L + (C + R))%nat in H by lia.
  apply tk_cb_split in H. destruct H as [H1 H].
  apply tk_cb_split in H. destruct H as [H2 H3].
  split; [exact H1|]. split; [exact H2 | exact H3].
Qed.

Lemma tk_firstn_app1 : forall (p q r : list byte) (L : nat), length p = L -> firstn L (p ++ q ++ r) = p.
Proof.
  intros p q r L Hp. rewrite firstn_app, Hp, Nat.sub_diag, firstn_O, app_nil_r.
  apply firstn_all2. lia.
Qed.

Lemma tk_firstn_app2 : forall (p q r : list byte) (L C : nat), length p = L -> length q = C ->
  firstn (L + C) (p ++ q ++ r) = p ++ q.
Proof.
  intros p q r L C Hp Hq. rewrite firstn_app, Hp.
  rewrite (firstn_all2 p) by lia. replace (L + C - L)%nat with C by lia.
  rewrite firstn_app, Hq, Nat.sub_diag, firstn_O, app_nil_r. rewrite (firstn_all2 q) by lia. reflexivity.
Qed.

Lemma tk_bytes_of_cb : forall m A n l, rw_cells segs m A [CB n l] -> bytes_at segs m A l.
Proof. intros m A n l [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

(* the stack after a call that wrote the span [A, A + n), which may lie inside it: outside the span the bytes
   are those of the entry, inside it they are the bytes of the cell the callee gives back (frame_build.v
   stk_rebuild, for one span) *)
Lemma tk_stk_rebuild : forall m1 m2 lo' hi A n cs,
  stk segs m1 lo' hi -> munch [(A, A + n)] m1 m2 -> wmono segs m1 m2 ->
  rw_cells segs m2 A cs -> Z.of_nat (cells_size cs) = n ->
  stk segs m2 lo' hi.
Proof.
  intros m1 m2 lo' hi A n cs (H1 & H2 & H) Hm Hw [[Hwf Hb] _] Hn.
  destruct Hb as (HA & HAl & Hbi). rewrite cells_bytes_length in HAl by exact Hwf.
  split; [lia|]. split; [lia|]. intros x Hx.
  destruct (H x Hx) as [Hwx (b0 & Hb0)]. split; [apply Hw; exact Hwx|].
  destruct (Z_lt_le_dec x A) as [Lt|Ge]; [| destruct (Z_lt_le_dec x (A + n)) as [Lt2|Ge2]].
  - exists b0. unfold mrd in *. rewrite Hm; [exact Hb0|]. rewrite wa_unsigned by lia.
    cbn [outside]. repeat split; lia.
  - specialize (Hbi (Z.to_nat (x - A))). rewrite cells_bytes_length in Hbi by exact Hwf.
    replace (A + Z.of_nat (Z.to_nat (x - A))) with x in Hbi by lia.
    destruct (nth_error (cells_bytes cs) (Z.to_nat (x - A))) as [b1|] eqn:E.
    + exists b1. apply Hbi. lia.
    + apply nth_error_None in E. rewrite cells_bytes_length in E by exact Hwf. lia.
  - exists b0. unfold mrd in *. rewrite Hm; [exact Hb0|]. rewrite wa_unsigned by lia.
    cbn [outside]. repeat split; lia.
Qed.

End Cells.

(** * Tactics *)

(* ---- world accesses at an open offset ---- *)

(* A register A + k (k the offset of a queue entry, open in its index) plus an immediate c: the world offset k + c.
   The walks install these hooks BEFORE the kit's (TModel/TWorldMem.v), and [tk_open] makes them fire only for an
   offset open in a variable, so a closed offset keeps the kit's literal form (s32_at B 1700) and an open one keeps
   the form OFF_g_s + 1760 + 32 * i + c, which the walks name themselves (the kit's indexed hook would fold it into
   a field of the queue entry by its literal offset alone). *)
Ltac tk_offset A a :=
  let E := addr_expr a in
  lazymatch E with
  | Z.add (Z.add A ?k) ?c => constr:(Z.add k c)
  | Z.add A ?k => k
  end.
Ltac tk_open k := match k with context [?x] => is_var x end.

(* side goals of the hooks: a word equation by wk_addr_eq, an arithmetic goal by lia (never vm_compute: the
   bytes stored are Z_to_bv 64 of an open value) *)
Ltac tk_hside :=
  lazymatch goal with
  | |- @eq (bv _) _ _ => wk_addr_eq
  | |- _ => rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?length_put; lia
  end.

Ltac tk_solve_load_world :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
      match goal with
      | H : rw_cells segs m ?A [CB (Z.to_nat W_LEN) ?B] |- _ =>
          let k := tk_offset A a in
          tk_open k;
          rewrite (wm_read segs A m B k n a H) by tk_hside;
          wk_load_post
      end
  end.

Ltac tk_solve_store_world :=
  match goal with
  | |- context [store_ok ?segs ?m ?a ?n] =>
      match goal with
      | H : rw_cells segs m ?A [CB (Z.to_nat W_LEN) ?B] |- _ =>
          let k := tk_offset A a in
          tk_open k;
          rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
          rewrite (wm_store_ok segs A m B k n a H) by tk_hside;
          cbv beta iota
      end
  end.

Ltac tk_world_after_store :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m ?a ?bs) ?ro) =>
      match goal with
      | H : rw_cells segs m ?A [CB (Z.to_nat W_LEN) ?B] |- _ =>
          let k := tk_offset A a in
          tk_open k;
          let E := addr_expr a in
          let HS := fresh "HSw" in
          assert (HS : store_ok segs m (wa E) (length bs) = true)
            by (apply (wm_store_ok segs A m B k); [exact H | tk_hside | tk_hside | tk_hside]);
          let H' := fresh "WMw" in
          assert (H' : rw_cells segs (write_to_mem m (wa E) bs) A [CB (Z.to_nat W_LEN) (upd B k bs)])
            by (apply (wm_write_at segs A m B k bs E); [ exact H | tk_hside | tk_hside | lia ]);
          clear H;
          store_done;
          rewrite ?le8_put, ?le4_put, ?le2_put, ?le1_put in H'
      end
  end.


(* the premises of an [eapply] of one of the walk lemmas: a fact of the context, a register equation, an
   arithmetic side goal. [lia] runs ONLY on an arithmetic goal: on any other it searches the context for a
   contradiction, which with the disjunctions of the contract costs seconds per call. *)
Ltac tk_prem :=
  try eassumption; try reflexivity;
  try (lazymatch goal with
       | |- ?G =>
           tryif has_evar G then fail else
           lazymatch G with
           | (_ <= _)%Z => lia
           | (_ < _)%Z => lia
           | @eq Z _ _ => lia
           | @eq nat _ _ => lia
           | _ /\ _ => lia
           end
       end);
  try (lazymatch goal with |- @eq (bv _) _ _ => f_equal; lia end).

(* A fact under [tk_keep] is out of lia's reach: the disjointness disjunctions of the contract, whose case
   split costs seconds per lia call in a walk that calls lia hundreds of times (frame_build.v's [keep]). *)
Definition tk_keep (P : Prop) : Prop := P.
Ltac tk_hide H := let T := type of H in change (tk_keep T) in H.

(* reads of a world under writes elsewhere; the length facts in Z (a Z.to_nat in the context costs lia a case
   split per fact) *)
Ltac tk_lens :=
  repeat match goal with
  | H : rw_cells _ _ _ [CB (Z.to_nat W_LEN) ?B0] |- _ =>
      lazymatch goal with
      | _ : Z.of_nat (length B0) = W_LEN |- _ => fail
      | _ => let L := fresh "LW" in pose proof (wm_len _ _ _ _ H) as L;
             apply (f_equal Z.of_nat) in L; rewrite Z2Nat.id in L by (unfold W_LEN; lia)
      end
  end.

Ltac tk_rd :=
  tk_lens;
  repeat match goal with
  | |- context [u_at (upd ?B0 ?k ?v) ?k' ?n] =>
      rewrite (u_at_upd_out B0 v k k' n) by (rewrite ?length_put; lia)
  end.

(* decide the branch of the goal to b *)
Ltac tk_cond b :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b; [cbv iota | symmetry; unfold_cond; rewrite ?unsigned_lit by lia; solve_cond_rec]
  end.
