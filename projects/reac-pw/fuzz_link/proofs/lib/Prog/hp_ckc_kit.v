(* reac-pw/fuzz_link, PLAIN build: small facts the walks of check_marks and check_requests share
   (lib/Prog/check_marks.v, lib/Prog/check_requests.v): reads of a field out of a `u8arr` view as the
   `le4` / `le8` word a load sees, a sub-range of a byte view, the C string inside a mark slot, and
   memcmp_model of a list against itself. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
Local Open Scope Z_scope.

(* a 4-byte field of a byte view, as the word a `lw` / `lwu` reads *)
Lemma ck_rd4 : forall m A bs off,
  u8arr rsegs m A bs -> 0 <= off -> off + 4 <= Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (wa (A + off)) 4 = Some (le4 (Z_to_bv 64 (rdn bs off 4))).
Proof.
  intros m A bs off [HB _] H0 H1.
  rewrite (bytes_at_read rsegs m A bs off 4 HB H0) by lia.
  f_equal. unfold rdn, slice. change (Z.to_nat 4) with 4%nat.
  set (l := firstn 4 (skipn (Z.to_nat off) bs)).
  assert (L : length l = 4%nat) by (unfold l; rewrite length_firstn, length_skipn; lia).
  pose proof (bytes_le_to_Z_bound l) as HB2. pose proof (bytes_le_to_Z_nonneg l) as HN.
  rewrite L in HB2. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in HB2.
  rewrite <- le4_lit by lia. rewrite <- L at 1. symmetry. apply Z_to_le_bytes_to_Z.
Qed.

(* an 8-byte field of a byte view, as the word an `ld` reads *)
Lemma ck_rd8 : forall m A bs off,
  u8arr rsegs m A bs -> 0 <= off -> off + 8 <= Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (wa (A + off)) 8 = Some (le8 (Z_to_bv 64 (rdn bs off 8))).
Proof.
  intros m A bs off [HB _] H0 H1.
  rewrite (bytes_at_read rsegs m A bs off 8 HB H0) by lia.
  f_equal. unfold rdn, slice. change (Z.to_nat 8) with 8%nat.
  set (l := firstn 8 (skipn (Z.to_nat off) bs)).
  assert (L : length l = 8%nat) by (unfold l; rewrite length_firstn, length_skipn; lia).
  pose proof (bytes_le_to_Z_bound l) as HB2. pose proof (bytes_le_to_Z_nonneg l) as HN.
  rewrite L in HB2. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in HB2.
  rewrite <- le8_lit by lia. rewrite <- L at 1. symmetry. apply Z_to_le_bytes_to_Z.
Qed.

Lemma ck_rdn_range : forall bs off n, 0 <= n -> 0 <= rdn bs off n < 2 ^ (8 * n).
Proof.
  intros bs off n Hn. unfold rdn, slice. split; [apply bytes_le_to_Z_nonneg|].
  eapply Z.lt_le_trans; [apply bytes_le_to_Z_bound|].
  apply Z.pow_le_mono_r; [lia|]. rewrite length_firstn. lia.
Qed.

Lemma ck_sx32 : forall z, 0 <= z < 2 ^ 31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit by lia.
  apply bv_swrap_small. change (bv_half_modulus 32) with 2147483648. change (2 ^ 31) with 2147483648 in Hz. lia.
Qed.

(* a sub-range of a byte view *)
Lemma ck_bytes_sub : forall m A bs off k,
  bytes_at rsegs m A bs -> 0 <= off -> 0 <= k -> off + k <= Z.of_nat (length bs) ->
  bytes_at rsegs m (A + off) (slice bs off k).
Proof.
  intros m A bs off k HB H0 Hk H1. unfold slice.
  rewrite <- (firstn_skipn (Z.to_nat off) bs) in HB.
  apply bytes_at_app in HB. destruct HB as [_ HB].
  rewrite length_firstn in HB.
  replace (Z.of_nat (Nat.min (Z.to_nat off) (length bs))) with off in HB by lia.
  rewrite <- (firstn_skipn (Z.to_nat k) (skipn (Z.to_nat off) bs)) in HB.
  apply bytes_at_app in HB. exact (proj1 HB).
Qed.

Lemma ck_bytes_prefix : forall m A bs k,
  bytes_at rsegs m A bs -> (k <= length bs)%nat -> bytes_at rsegs m A (firstn k bs).
Proof.
  intros m A bs k HB Hk. rewrite <- (firstn_skipn k bs) in HB.
  apply bytes_at_app in HB. exact (proj1 HB).
Qed.

(* the C string of a slot that holds a NUL: its bytes, then that NUL *)
Lemma ck_cstr_split : forall l : list byte, (nul_at l < length l)%nat ->
  firstn (S (nul_at l)) l = cstr l ++ [Z_to_bv 8 0] /\ ~ In (Z_to_bv 8 0) (cstr l).
Proof.
  induction l as [|b l IH]; intros H; [cbn in H; lia|].
  unfold cstr. cbn [nul_at] in *.
  destruct (bz b =? 0) eqn:E.
  - apply Z.eqb_eq in E. cbn [firstn app]. split.
    + f_equal. apply bv_eq. unfold bz in E. rewrite E. reflexivity.
    + intros [].
  - apply Z.eqb_neq in E. cbn [length] in H.
    destruct (IH ltac:(lia)) as [IH1 IH2]. unfold cstr in IH1, IH2.
    cbn [firstn app]. split.
    + f_equal. exact IH1.
    + intros [Hb|Hin]; [|exact (IH2 Hin)].
      apply E. unfold bz. rewrite Hb. reflexivity.
Qed.

Lemma ck_memcmp_self : forall n (l : list byte), (n <= length l)%nat -> memcmp_model l l n = Some 0.
Proof.
  induction n as [|n IH]; intros [|b l] H; cbn [length memcmp_model] in *; try lia; try reflexivity.
  rewrite Z.eqb_refl. apply IH. lia.
Qed.

(* two maps over `seq 0 len` that agree agree at each index *)
Lemma ck_map_seq_eq : forall {A} (f g : nat -> A) len n,
  map f (seq 0 len) = map g (seq 0 len) -> (n < len)%nat -> f n = g n.
Proof.
  intros A f g len n H Hn.
  pose proof (f_equal (fun l => nth_error l n) H) as H'. cbv beta in H'.
  assert (Ex : nth_error (seq 0 len) n = Some n).
  { rewrite nth_error_nth' with (d := 0%nat) by (rewrite length_seq; exact Hn).
    rewrite seq_nth by exact Hn. reflexivity. }
  rewrite !nth_error_map, Ex in H'. cbn in H'. injection H' as H'. exact H'.
Qed.
