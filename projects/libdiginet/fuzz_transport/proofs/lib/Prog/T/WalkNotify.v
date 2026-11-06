(* Pieces the plain walks of the session functions that call s->notify share (session_lost, maybe_online,
   on_ack): the current heap frame and the RELRO tables carried from the entry memory to a callee, the world
   carried across a callee that writes only above it, and the struct diginet_notice the walk builds on its stack,
   read as TContract's ntc_at. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem TContract.
Import ListNotations.
Open Scope Z_scope.

(* the footprint of a walk contract: its stack window and the world *)
Definition wk_fp (sp : word) (K : Z) : list ivl :=
  [(bv_unsigned sp - K, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)].

(* ---- the heap frame and the RELRO tables, from the entry memory to a callee ---- *)

Lemma tframe_at_move : forall m m' (sp sp' : word) K K' TF,
  tframe_at m sp K TF -> munch (wk_fp sp K) m m' ->
  bv_unsigned sp - K <= bv_unsigned sp' - K' -> bv_unsigned sp' <= bv_unsigned sp ->
  tframe_at m' sp' K' TF.
Proof.
  intros m m' sp sp' K K' TF T MU H1 H2. destruct TF as [fr|]; [|exact I].
  unfold tframe_at in *. destruct T as (P & BA & OW & OWin). unfold off_world, off_window in *.
  refine (conj P (conj _ (conj OW _))); [| lia].
  eapply bytes_at_transport; [exact BA | exact MU |]. unfold wk_fp. cbn [disjoint_from].
  refine (conj _ (conj _ I)); lia.
Qed.

Lemma relro_img_move : forall m m' (sp : word) K, relro_img m -> munch (wk_fp sp K) m m' ->
  W_BASE_PLAIN + W_LEN <= bv_unsigned sp - K -> relro_img m'.
Proof.
  intros m m' sp K R MU H i Hi. unfold mrd. rewrite (MU (wa (RELRO_BASE + i))); [exact (R i Hi) |].
  unfold wk_fp, RELRO_BASE, RELRO_LEN in *. cbn [outside]. rewrite wa_unsigned by lia.
  unfold W_BASE_PLAIN, W_LEN in *. refine (conj _ (conj _ I)); lia.
Qed.

(* ---- the world across a callee whose footprint misses it ---- *)

Lemma wmem_transport : forall m m' B W, wmem rsegs m B -> munch W m m' -> wmono rsegs m m' ->
  disjoint_from W W_BASE_PLAIN W_LEN -> wmem rsegs m' B.
Proof.
  intros m m' B W H MU WM D. eapply rw_cells_transport; [exact H | exact MU | exact WM |].
  rewrite wm_size. exact D.
Qed.

(* the bytes of a cell list *)
Lemma rw_cells_bytes_at : forall m A cs, rw_cells rsegs m A cs -> bytes_at rsegs m A (cells_bytes cs).
Proof. intros m A cs [[_ Hb] _]. exact Hb. Qed.

Lemma bytes_at_join : forall m a b bs1 bs2, bytes_at rsegs m a bs1 -> bytes_at rsegs m b bs2 ->
  b = a + Z.of_nat (length bs1) -> bytes_at rsegs m a (bs1 ++ bs2).
Proof. intros m a b bs1 bs2 H1 H2 ->. apply bytes_at_app. split; assumption. Qed.

(* a branch on a register that holds a nonzero int *)
Lemma bv_unsigned_nz : forall v, - 2 ^ 63 <= v < 2 ^ 63 -> v <> 0 -> bv_unsigned (Z_to_bv 64 v) <> 0.
Proof.
  intros v Hv N E. rewrite unsigned_lit_wrap in E. apply Z.mod_divide in E; [| lia].
  destruct E as [c Ec]. nia.
Qed.

Lemma bv_unsigned_ne : forall v w, - 2 ^ 63 <= v < 2 ^ 63 -> - 2 ^ 63 <= w < 2 ^ 63 -> v <> w ->
  bv_unsigned (Z_to_bv 64 v) <> bv_unsigned (Z_to_bv 64 w).
Proof. intros v w Hv Hw N E. rewrite !unsigned_lit_wrap in E. apply N. Z.div_mod_to_equations. lia. Qed.

(* a 64-bit store: put 8 of two values equal mod 2^64 *)
Lemma put8_mod_eq : forall x y, x mod 2 ^ 64 = y mod 2 ^ 64 -> put 8 x = put 8 y.
Proof. intros x y H. rewrite <- (put_mod64 8 x), <- (put_mod64 8 y) by lia. rewrite H. reflexivity. Qed.

(* the stack pointer is 16-aligned: an offset from it is as aligned as the offset *)
Lemma sp_mod8 : forall x k, x mod 16 = 0 -> (x + k) mod 8 = k mod 8.
Proof. intros x k H. Z.div_mod_to_equations. lia. Qed.

Lemma sp_mod16 : forall x k, x mod 16 = 0 -> (x + k) mod 16 = k mod 16.
Proof. intros x k H. Z.div_mod_to_equations. lia. Qed.

(* ---- reading a struct diginet_notice built field by field ---- *)

Lemma u_at_app_l : forall (l1 l2 : list byte) k n, 0 <= k -> k + Z.of_nat n <= Z.of_nat (length l1) ->
  u_at (l1 ++ l2) k n = u_at l1 k n.
Proof.
  intros l1 l2 k n Hk Hn. unfold u_at, sub. f_equal.
  rewrite skipn_app. replace (Z.to_nat k - length l1)%nat with 0%nat by lia. cbn [skipn].
  rewrite firstn_app. rewrite length_skipn. replace (n - (length l1 - Z.to_nat k))%nat with 0%nat by lia.
  cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.

Lemma u_at_app_r : forall (l1 l2 : list byte) k n, Z.of_nat (length l1) <= k ->
  u_at (l1 ++ l2) k n = u_at l2 (k - Z.of_nat (length l1)) n.
Proof.
  intros l1 l2 k n Hk. unfold u_at, sub. f_equal.
  rewrite skipn_app. rewrite skipn_all2 by lia. cbn [app].
  f_equal. f_equal. lia.
Qed.

Lemma u_at_put4 : forall v k, k = 0 -> u_at (put 4 v) k 4 = v mod 2 ^ 32.
Proof. intros v k ->. rewrite u_at_put. reflexivity. Qed.

Lemma u_at_put_n : forall n v k, k = 0 -> u_at (put n v) k n = v mod 2 ^ (8 * Z.of_nat n).
Proof. intros n v k ->. apply u_at_put. Qed.

Lemma swrap32_mod : forall v, - 2 ^ 31 <= v < 2 ^ 31 -> bv_swrap 32 (v mod 2 ^ 32) = v.
Proof.
  intros v Hv. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  Z.div_mod_to_equations. lia.
Qed.

Lemma firstn_repeat_le : forall (x : byte) j n, (j <= n)%nat -> firstn j (repeat x n) = repeat x j.
Proof. induction j as [|j IH]; intros n H; [reflexivity |]. destruct n as [|n]; [lia |]. cbn. f_equal. apply IH. lia. Qed.

Lemma skipn_repeat_sub : forall (x : byte) k n, skipn k (repeat x n) = repeat x (n - k).
Proof.
  induction k as [|k IH]; intros n; [cbn [skipn]; rewrite Nat.sub_0_r; reflexivity |].
  destruct n as [|n]; [reflexivity |]. cbn. apply IH.
Qed.

Lemma ble_zeros : forall j, bytes_le_to_Z (repeat (b8 0) j) = 0.
Proof.
  intros j. rewrite bytes_le_to_Z_le_val. induction j as [|j IH]; [reflexivity |].
  cbn [repeat map le_val]. rewrite IH. reflexivity.
Qed.

Lemma u_at_zeros : forall n k j, 0 <= k -> k + Z.of_nat j <= Z.of_nat n -> u_at (repeat (b8 0) n) k j = 0.
Proof.
  intros n k j Hk Hj. unfold u_at, sub. rewrite skipn_repeat_sub, firstn_repeat_le by lia. apply ble_zeros.
Qed.

Ltac ntc_norm := rewrite ?app_length, ?length_put, ?repeat_length.
Ltac ntc_field :=
  repeat (rewrite u_at_app_r by (ntc_norm; cbn; lia); ntc_norm);
  first [ rewrite u_at_zeros by (ntc_norm; cbn; lia)
        | rewrite u_at_app_l by (ntc_norm; cbn; lia); ntc_norm;
          first [ rewrite u_at_zeros by (cbn; lia) | rewrite u_at_put4 by (cbn; lia)
                | rewrite u_at_put_n by (cbn; lia) | idtac ]
        | rewrite u_at_put4 by (cbn; lia)
        | rewrite u_at_put_n by (cbn; lia)
        | idtac ];
  try reflexivity.

(* a STATE notice (diginet_session.c:83-84): kind, state, old_state, reason, every other field zero *)
Definition ntc_state_bytes (st old why : Z) : list byte :=
  put 4 2 ++ put 4 st ++ put 4 old ++ put 4 why ++ repeat (b8 0) 56.

Lemma ntc_state_at : forall m p (sp : word) K st old why,
  bytes_at rsegs m p (ntc_state_bytes st old why) ->
  0 < p -> p mod 8 = 0 -> off_world p 72 -> off_window sp K p 72 -> 0 <= bv_unsigned sp - K ->
  - 2 ^ 31 <= st < 2 ^ 31 -> - 2 ^ 31 <= old < 2 ^ 31 -> - 2 ^ 31 <= why < 2 ^ 31 ->
  ntc_at m p (Ntc 2 st old why 0 0 0 0 None [] 0) sp K.
Proof.
  intros m p sp K st old why BA P0 P8 OW OWin SK Hst Hold Hwhy.
  unfold ntc_at. refine (conj P0 (conj P8 (conj OW (conj OWin _)))).
  exists (ntc_state_bytes st old why). unfold ntc_state_bytes, s32_at. cbn [n_kind n_state n_old n_reason n_pers
    n_mac_offset n_body_len n_counter n_retry n_body n_ann length].
  assert (Z0 : u_at (put 4 2 ++ put 4 st ++ put 4 old ++ put 4 why ++ repeat (b8 0) 56) 48 8 = 0) by ntc_field.
  rewrite Z0.
  split; [exact BA |].
  split; [ntc_norm; reflexivity |].
  split; [ntc_field |].
  split; [ntc_field; apply swrap32_mod; exact Hst |].
  split; [ntc_field; apply swrap32_mod; exact Hold |].
  split; [ntc_field; apply swrap32_mod; exact Hwhy |].
  split; [ntc_field |].
  split; [ntc_field |].
  split; [ntc_field |].
  split; [ntc_field |].
  split; [ntc_field |].
  split; [apply bytes_at_nil; lia |].
  split; [unfold off_world, W_BASE_PLAIN; lia |].
  split; [unfold off_window; lia |].
  ntc_field.
Qed.

(* an ACKED notice (diginet_session.c:230-231): kind, state, the frame pointer (not read by notice), counter,
   retry, every other field zero *)
Definition ntc_acked_bytes (st fpz cnt rt : Z) : list byte :=
  put 4 4 ++ put 4 st ++ put 8 0 ++ put 8 fpz ++ repeat (b8 0) 40 ++ put 4 cnt ++ put 2 rt ++ put 2 0.

Lemma ntc_acked_at : forall m p (sp : word) K st fpz cnt rt,
  bytes_at rsegs m p (ntc_acked_bytes st fpz cnt rt) ->
  0 < p -> p mod 8 = 0 -> off_world p 72 -> off_window sp K p 72 -> 0 <= bv_unsigned sp - K ->
  - 2 ^ 31 <= st < 2 ^ 31 -> 0 <= cnt < 2 ^ 32 -> 0 <= rt < 2 ^ 16 ->
  ntc_at m p (Ntc 4 st 0 0 cnt rt 0 0 None [] 0) sp K.
Proof.
  intros m p sp K st fpz cnt rt BA P0 P8 OW OWin SK Hst Hc Hr.
  unfold ntc_at. refine (conj P0 (conj P8 (conj OW (conj OWin _)))).
  exists (ntc_acked_bytes st fpz cnt rt). unfold ntc_acked_bytes, s32_at. cbn [n_kind n_state n_old n_reason n_pers
    n_mac_offset n_body_len n_counter n_retry n_body n_ann length].
  assert (Z0 : u_at (put 4 4 ++ put 4 st ++ put 8 0 ++ put 8 fpz ++ repeat (b8 0) 40 ++ put 4 cnt ++ put 2 rt
                     ++ put 2 0) 48 8 = 0) by ntc_field.
  rewrite Z0.
  split; [exact BA |].
  split; [ntc_norm; reflexivity |].
  split; [ntc_field |].
  split; [ntc_field; apply swrap32_mod; exact Hst |].
  split; [ntc_field |].
  split; [ntc_field |].
  split; [ntc_field |].
  split; [ntc_field |].
  split; [ntc_field |].
  split; [ntc_field; apply Z.mod_small; exact Hc |].
  split; [ntc_field; apply Z.mod_small; cbn; lia |].
  split; [apply bytes_at_nil; lia |].
  split; [unfold off_world, W_BASE_PLAIN; lia |].
  split; [unfold off_window; lia |].
  ntc_field.
Qed.
