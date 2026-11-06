(* talk (fuzz_link.c:333-384), PLAIN build: byte-list facts of the stores talk and owe make into
   the model block (struct model, link_spec.v section 7). Pure: no machine state.

   md_owe is the three stores of owe (fuzz_link.c:296-303) into a model with n requests:
   the request bytes into slot n, n+1 into n_req, the length into req_len[n].
   md_same says the marks part of the block is the same. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem talk_defs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac.
Local Open Scope Z_scope.

Definition md_owe (mb req : list byte) (n len : Z) : list byte :=
  upd_bytes (upd_bytes (upd_bytes mb (Z.to_nat (MD_REQ + NL_SENT_LEN * n)) req)
             (Z.to_nat MD_N_REQ) (le4 (Z_to_bv 64 (n + 1))))
            (Z.to_nat (MD_REQ_LEN + 8 * n)) (le8 (Z_to_bv 64 len)).

Definition md_same (a b : list byte) : Prop :=
  md_n_mark a = md_n_mark b /\ md_marks a = md_marks b.

(* --------------------------------------------------------------------------
   1. arithmetic over the offsets of struct model
   -------------------------------------------------------------------------- *)

Ltac tm_lia :=
  rewrite ?length_le4, ?length_le8 in *;
  unfold MD_SOCKET_ERRNO, MD_SEND_ERRNO, MD_NEXT, MD_REQ, MD_REQ_LEN, MD_N_REQ, MD_MARK,
    MD_N_MARK, MD_SIZE, MARK_LEN, NL_SENT_LEN, NL_SENT_MAX, MARKS_MAX in *;
  lia.

(* --------------------------------------------------------------------------
   2. a slice of a list after upd_bytes
   -------------------------------------------------------------------------- *)

(* a slice apart from the written range reads the old bytes *)
Lemma tm_slice_upd_out : forall (l xs : list byte) p o n,
  (p + length xs <= length l)%nat -> 0 <= o ->
  o + n <= Z.of_nat p \/ Z.of_nat p + Z.of_nat (length xs) <= o ->
  slice (upd_bytes l p xs) o n = slice l o n.
Proof.
  intros l xs p o n Hl Ho Hd. unfold slice. apply nth_error_ext. intros i.
  rewrite !nth_error_firstn, !nth_error_skipn.
  destruct (Nat.ltb_spec i (Z.to_nat n)) as [Hi|Hi]; [|reflexivity].
  destruct (Nat.ltb_spec (Z.to_nat o + i)%nat (length l)) as [Hk|Hk].
  - rewrite upd_bytes_nth by lia.
    destruct (Nat.leb_spec p (Z.to_nat o + i)%nat);
      destruct (Nat.ltb_spec (Z.to_nat o + i)%nat (p + length xs)%nat);
      cbn [andb]; first [reflexivity | exfalso; lia].
  - assert (L : length (upd_bytes l p xs) = length l) by (apply upd_bytes_length; exact Hl).
    rewrite (proj2 (nth_error_None (upd_bytes l p xs) _)) by lia.
    rewrite (proj2 (nth_error_None l _)) by lia. reflexivity.
Qed.

(* the slice of exactly the written range reads the new bytes *)
Lemma tm_slice_upd_same : forall (l xs : list byte) p o n, (p + length xs <= length l)%nat ->
  o = Z.of_nat p -> n = Z.of_nat (length xs) -> slice (upd_bytes l p xs) o n = xs.
Proof.
  intros l xs p o n Hl -> ->. unfold slice. rewrite !Nat2Z.id.
  apply nth_error_ext. intros i. rewrite nth_error_firstn, nth_error_skipn.
  destruct (Nat.ltb_spec i (length xs)) as [Hi|Hi].
  - rewrite upd_bytes_nth by lia.
    destruct (Nat.leb_spec p (p + i)%nat); destruct (Nat.ltb_spec (p + i)%nat (p + length xs)%nat);
      cbn [andb]; try (exfalso; lia).
    replace (p + i - p)%nat with i by lia. reflexivity.
  - rewrite (proj2 (nth_error_None xs i)) by lia. reflexivity.
Qed.

(* two writes of the same width at the same place: the second wins *)
Lemma tm_upd_upd : forall (l xs ys : list byte) p, length xs = length ys ->
  (p + length xs <= length l)%nat -> upd_bytes (upd_bytes l p xs) p ys = upd_bytes l p ys.
Proof.
  intros l xs ys p E Hl. apply nth_error_ext. intros i.
  assert (L1 : length (upd_bytes l p xs) = length l) by (apply upd_bytes_length; exact Hl).
  destruct (Nat.ltb_spec i (length l)) as [Hi|Hi].
  - rewrite (upd_bytes_nth (upd_bytes l p xs) p ys i) by (rewrite L1; lia).
    rewrite (upd_bytes_nth l p ys i) by lia.
    rewrite (upd_bytes_nth l p xs i) by lia. rewrite E.
    destruct (Nat.leb_spec p i); destruct (Nat.ltb_spec i (p + length ys)%nat); cbn [andb]; reflexivity.
  - assert (L2 : length (upd_bytes (upd_bytes l p xs) p ys) = length l)
      by (rewrite upd_bytes_length; [exact L1 | rewrite L1; lia]).
    assert (L3 : length (upd_bytes l p ys) = length l) by (apply upd_bytes_length; lia).
    rewrite (proj2 (nth_error_None (upd_bytes (upd_bytes l p xs) p ys) i)) by lia.
    rewrite (proj2 (nth_error_None (upd_bytes l p ys) i)) by lia. reflexivity.
Qed.

(* --------------------------------------------------------------------------
   3. the little-endian fields
   -------------------------------------------------------------------------- *)

Lemma tm_ulit : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact Hz. Qed.

Lemma tm_le4_val : forall v, 0 <= v < 2 ^ 32 -> bytes_le_to_Z (le4 (Z_to_bv 64 v)) = v.
Proof. intros v Hv. rewrite bytes_le_to_Z_le4, tm_ulit by lia. apply Z.mod_small. exact Hv. Qed.

Lemma tm_le8_val : forall v, 0 <= v < 2 ^ 64 -> bytes_le_to_Z (le8 (Z_to_bv 64 v)) = v.
Proof.
  intros v Hv. rewrite <- store_bytes_8. change (width_bytes 64) with 8%nat.
  rewrite tm_ulit by exact Hv. rewrite bytes_le_to_Z_to_le_bytes by lia.
  apply Z.mod_small. change (8 * Z.of_nat 8) with 64. exact Hv.
Qed.

Lemma tm_u32_out : forall (l xs : list byte) p o, (p + length xs <= length l)%nat -> 0 <= o ->
  o + 4 <= Z.of_nat p \/ Z.of_nat p + Z.of_nat (length xs) <= o ->
  fld_u32 (upd_bytes l p xs) o = fld_u32 l o.
Proof. intros l xs p o H1 H2 H3. unfold fld_u32, link_spec.rdn. rewrite tm_slice_upd_out by assumption. reflexivity. Qed.

Lemma tm_u64_out : forall (l xs : list byte) p o, (p + length xs <= length l)%nat -> 0 <= o ->
  o + 8 <= Z.of_nat p \/ Z.of_nat p + Z.of_nat (length xs) <= o ->
  fld_u64 (upd_bytes l p xs) o = fld_u64 l o.
Proof. intros l xs p o H1 H2 H3. unfold fld_u64, link_spec.rdn. rewrite tm_slice_upd_out by assumption. reflexivity. Qed.

Lemma tm_u32_same : forall (l : list byte) p o v, (p + 4 <= length l)%nat -> o = Z.of_nat p ->
  0 <= v < 2 ^ 32 -> fld_u32 (upd_bytes l p (le4 (Z_to_bv 64 v))) o = v.
Proof.
  intros l p o v Hl Ho Hv. unfold fld_u32, link_spec.rdn.
  assert (E : slice (upd_bytes l p (le4 (Z_to_bv 64 v))) o 4 = le4 (Z_to_bv 64 v))
    by (apply tm_slice_upd_same; rewrite ?length_le4; lia).
  rewrite E. apply tm_le4_val. exact Hv.
Qed.

Lemma tm_u64_same : forall (l : list byte) p o v, (p + 8 <= length l)%nat -> o = Z.of_nat p ->
  0 <= v < 2 ^ 64 -> fld_u64 (upd_bytes l p (le8 (Z_to_bv 64 v))) o = v.
Proof.
  intros l p o v Hl Ho Hv. unfold fld_u64, link_spec.rdn.
  assert (E : slice (upd_bytes l p (le8 (Z_to_bv 64 v))) o 8 = le8 (Z_to_bv 64 v))
    by (apply tm_slice_upd_same; rewrite ?length_le8; lia).
  rewrite E. apply tm_le8_val. exact Hv.
Qed.

(* --------------------------------------------------------------------------
   4. the parts of the model a write leaves alone
   -------------------------------------------------------------------------- *)

Lemma tm_same_trans : forall a b c, md_same a b -> md_same b c -> md_same a c.
Proof. unfold md_same. intros a b c [H1 H2] [H3 H4]. split; congruence. Qed.

(* a write below the marks keeps them *)
Lemma tm_same_upd : forall (l xs : list byte) p, (p + length xs <= length l)%nat ->
  Z.of_nat p + Z.of_nat (length xs) <= MD_MARK -> md_same (upd_bytes l p xs) l.
Proof.
  intros l xs p Hl Hp.
  assert (Hn : md_n_mark (upd_bytes l p xs) = md_n_mark l) by (unfold md_n_mark; apply tm_u32_out; tm_lia).
  split; [exact Hn|]. unfold md_marks. rewrite Hn. apply map_ext. intros i. cbv beta. f_equal.
  apply tm_slice_upd_out; tm_lia.
Qed.

Lemma tm_marks_wf_upd : forall (l xs : list byte) p, (p + length xs <= length l)%nat ->
  Z.of_nat p + Z.of_nat (length xs) <= MD_MARK -> model_marks_wf l -> model_marks_wf (upd_bytes l p xs).
Proof.
  intros l xs p Hl Hp [H1 H2]. destruct (tm_same_upd l xs p Hl Hp) as [Hn _].
  unfold model_marks_wf, slots_terminated in *. rewrite Hn. split; [exact H1|].
  intros i Hi. rewrite tm_slice_upd_out by tm_lia. apply H2. exact Hi.
Qed.

(* a write into the three header words keeps the requests *)
Lemma tm_reqs_hdr : forall (l xs : list byte) p, (p + length xs <= length l)%nat ->
  Z.of_nat p + Z.of_nat (length xs) <= MD_REQ ->
  md_n_req (upd_bytes l p xs) = md_n_req l /\ md_reqs (upd_bytes l p xs) = md_reqs l.
Proof.
  intros l xs p Hl Hp.
  assert (Hn : md_n_req (upd_bytes l p xs) = md_n_req l) by (unfold md_n_req; apply tm_u32_out; tm_lia).
  split; [exact Hn|]. unfold md_reqs. rewrite Hn. apply map_ext. intros i. cbv beta. unfold md_req_one.
  rewrite tm_u64_out by tm_lia. apply tm_slice_upd_out; tm_lia.
Qed.

Lemma tm_wf_hdr : forall (l xs : list byte) p, (p + length xs <= length l)%nat ->
  Z.of_nat p + Z.of_nat (length xs) <= MD_REQ -> model_wf l ->
  0 <= md_next (upd_bytes l p xs) < 2 ^ 31 -> 0 <= md_socket_errno (upd_bytes l p xs) < 2 ^ 31 ->
  0 <= md_send_errno (upd_bytes l p xs) < 2 ^ 31 -> model_wf (upd_bytes l p xs).
Proof.
  intros l xs p Hl Hp (W1 & W2 & W3 & W4 & W5 & W6) N1 N2 N3.
  destruct (tm_reqs_hdr l xs p Hl Hp) as [Hn _].
  unfold model_wf. rewrite Hn. split; [exact W1|]. split; [exact N1|]. split; [exact N2|]. split; [exact N3|].
  split.
  - intros i Hi. rewrite tm_u64_out by tm_lia. apply W5. exact Hi.
  - apply tm_marks_wf_upd; [exact Hl | tm_lia | exact W6].
Qed.

(* --------------------------------------------------------------------------
   5. the lemmas the walk applies
   -------------------------------------------------------------------------- *)

Lemma md_reqs_length : forall mb, length (md_reqs mb) = Z.to_nat (md_n_req mb).
Proof. intros mb. unfold md_reqs. rewrite length_map, length_seq. reflexivity. Qed.

Lemma md_zero_sock : forall mbs, Z.of_nat (length mbs) = MD_SIZE -> model_wf mbs ->
  let mb' := upd_bytes mbs 0 (le4 (Z_to_bv 64 0)) in
  Z.of_nat (length mb') = MD_SIZE /\ model_wf mb' /\ md_socket_errno mb' = 0 /\
  md_send_errno mb' = md_send_errno mbs /\ md_next mb' = md_next mbs /\
  md_reqs mb' = md_reqs mbs /\ md_n_req mb' = md_n_req mbs /\ md_same mb' mbs.
Proof.
  intros mbs HL HW. cbv zeta.
  pose proof HW as (W1 & W2 & W3 & W4 & _).
  assert (Hlen : (0 + length (le4 (Z_to_bv 64 0)) <= length mbs)%nat) by tm_lia.
  assert (S0 : md_socket_errno (upd_bytes mbs 0 (le4 (Z_to_bv 64 0))) = 0)
    by (unfold md_socket_errno; apply tm_u32_same; tm_lia).
  assert (S1 : md_send_errno (upd_bytes mbs 0 (le4 (Z_to_bv 64 0))) = md_send_errno mbs)
    by (unfold md_send_errno; apply tm_u32_out; tm_lia).
  assert (S2 : md_next (upd_bytes mbs 0 (le4 (Z_to_bv 64 0))) = md_next mbs)
    by (unfold md_next; apply tm_u32_out; tm_lia).
  assert (R : md_n_req (upd_bytes mbs 0 (le4 (Z_to_bv 64 0))) = md_n_req mbs /\
              md_reqs (upd_bytes mbs 0 (le4 (Z_to_bv 64 0))) = md_reqs mbs)
    by (apply tm_reqs_hdr; tm_lia).
  destruct R as [S3 S4].
  split; [rewrite upd_bytes_length by exact Hlen; exact HL|].
  split; [apply tm_wf_hdr; [exact Hlen | tm_lia | exact HW | rewrite S2; exact W2 | rewrite S0; lia
                            | rewrite S1; exact W4]|].
  split; [exact S0|]. split; [exact S1|]. split; [exact S2|]. split; [exact S4|]. split; [exact S3|].
  apply tm_same_upd; tm_lia.
Qed.

Lemma md_zero_send : forall mbs, Z.of_nat (length mbs) = MD_SIZE -> model_wf mbs ->
  let mb' := upd_bytes mbs 4 (le4 (Z_to_bv 64 0)) in
  Z.of_nat (length mb') = MD_SIZE /\ model_wf mb' /\ md_send_errno mb' = 0 /\
  md_socket_errno mb' = md_socket_errno mbs /\ md_next mb' = md_next mbs /\
  md_reqs mb' = md_reqs mbs /\ md_n_req mb' = md_n_req mbs /\ md_same mb' mbs.
Proof.
  intros mbs HL HW. cbv zeta.
  pose proof HW as (W1 & W2 & W3 & W4 & _).
  assert (Hlen : (4 + length (le4 (Z_to_bv 64 0)) <= length mbs)%nat) by tm_lia.
  assert (S0 : md_send_errno (upd_bytes mbs 4 (le4 (Z_to_bv 64 0))) = 0)
    by (unfold md_send_errno; apply tm_u32_same; tm_lia).
  assert (S1 : md_socket_errno (upd_bytes mbs 4 (le4 (Z_to_bv 64 0))) = md_socket_errno mbs)
    by (unfold md_socket_errno; apply tm_u32_out; tm_lia).
  assert (S2 : md_next (upd_bytes mbs 4 (le4 (Z_to_bv 64 0))) = md_next mbs)
    by (unfold md_next; apply tm_u32_out; tm_lia).
  assert (R : md_n_req (upd_bytes mbs 4 (le4 (Z_to_bv 64 0))) = md_n_req mbs /\
              md_reqs (upd_bytes mbs 4 (le4 (Z_to_bv 64 0))) = md_reqs mbs)
    by (apply tm_reqs_hdr; tm_lia).
  destruct R as [S3 S4].
  split; [rewrite upd_bytes_length by exact Hlen; exact HL|].
  split; [apply tm_wf_hdr; [exact Hlen | tm_lia | exact HW | rewrite S2; exact W2 | rewrite S1; exact W3
                            | rewrite S0; lia]|].
  split; [exact S0|]. split; [exact S1|]. split; [exact S2|]. split; [exact S4|]. split; [exact S3|].
  apply tm_same_upd; tm_lia.
Qed.

Lemma md_set_next_ok : forall mbs j, Z.of_nat (length mbs) = MD_SIZE -> model_wf mbs -> 0 <= j < 2 ^ 31 ->
  let mb' := md_set_next mbs j in
  Z.of_nat (length mb') = MD_SIZE /\ model_wf mb' /\ md_next mb' = j /\
  md_socket_errno mb' = md_socket_errno mbs /\ md_send_errno mb' = md_send_errno mbs /\
  md_reqs mb' = md_reqs mbs /\ md_n_req mb' = md_n_req mbs /\ md_same mb' mbs.
Proof.
  intros mbs j HL HW Hj. cbv zeta. unfold md_set_next.
  pose proof HW as (W1 & W2 & W3 & W4 & _).
  assert (Hlen : (8 + length (le4 (Z_to_bv 64 j)) <= length mbs)%nat) by tm_lia.
  assert (S0 : md_next (upd_bytes mbs 8 (le4 (Z_to_bv 64 j))) = j)
    by (unfold md_next; apply tm_u32_same; tm_lia).
  assert (S1 : md_socket_errno (upd_bytes mbs 8 (le4 (Z_to_bv 64 j))) = md_socket_errno mbs)
    by (unfold md_socket_errno; apply tm_u32_out; tm_lia).
  assert (S2 : md_send_errno (upd_bytes mbs 8 (le4 (Z_to_bv 64 j))) = md_send_errno mbs)
    by (unfold md_send_errno; apply tm_u32_out; tm_lia).
  assert (R : md_n_req (upd_bytes mbs 8 (le4 (Z_to_bv 64 j))) = md_n_req mbs /\
              md_reqs (upd_bytes mbs 8 (le4 (Z_to_bv 64 j))) = md_reqs mbs)
    by (apply tm_reqs_hdr; tm_lia).
  destruct R as [S3 S4].
  split; [rewrite upd_bytes_length by exact Hlen; exact HL|].
  split; [apply tm_wf_hdr; [exact Hlen | tm_lia | exact HW | rewrite S0; lia | rewrite S1; exact W3
                            | rewrite S2; exact W4]|].
  split; [exact S0|]. split; [exact S1|]. split; [exact S2|]. split; [exact S4|]. split; [exact S3|].
  apply tm_same_upd; tm_lia.
Qed.

Lemma md_set_next_twice : forall mbs x y, Z.of_nat (length mbs) = MD_SIZE ->
  md_set_next (md_set_next mbs x) y = md_set_next mbs y.
Proof. intros mbs x y HL. unfold md_set_next. apply tm_upd_upd; tm_lia. Qed.

Lemma md_owe_ok : forall mbs req, Z.of_nat (length mbs) = MD_SIZE -> model_wf mbs ->
  md_n_req mbs < NL_SENT_MAX -> Z.of_nat (length req) <= NL_SENT_LEN ->
  let mb' := md_owe mbs req (md_n_req mbs) (Z.of_nat (length req)) in
  Z.of_nat (length mb') = MD_SIZE /\ model_wf mb' /\
  md_reqs mb' = md_reqs mbs ++ [req] /\ md_n_req mb' = md_n_req mbs + 1 /\
  md_socket_errno mb' = md_socket_errno mbs /\ md_send_errno mb' = md_send_errno mbs /\
  md_next mb' = md_next mbs /\ md_same mb' mbs.
Proof.
  intros mbs req HL HW Hn Hr. cbv zeta. unfold md_owe.
  pose proof HW as (W1 & W2 & W3 & W4 & W5 & W6).
  remember (upd_bytes mbs (Z.to_nat (MD_REQ + NL_SENT_LEN * md_n_req mbs)) req) as mb1 eqn:E1.
  remember (upd_bytes mb1 (Z.to_nat MD_N_REQ) (le4 (Z_to_bv 64 (md_n_req mbs + 1)))) as mb2 eqn:E2.
  remember (upd_bytes mb2 (Z.to_nat (MD_REQ_LEN + 8 * md_n_req mbs)) (le8 (Z_to_bv 64 (Z.of_nat (length req)))))
    as mb3 eqn:E3.
  assert (L1 : length mb1 = length mbs) by (rewrite E1; apply upd_bytes_length; tm_lia).
  assert (L2 : length mb2 = length mbs) by (rewrite E2, <- L1; apply upd_bytes_length; tm_lia).
  assert (L3 : length mb3 = length mbs) by (rewrite E3, <- L2; apply upd_bytes_length; tm_lia).
  (* the three header words *)
  assert (O32 : forall o, 0 <= o -> o + 4 <= MD_REQ -> fld_u32 mb3 o = fld_u32 mbs o).
  { intros o Ho1 Ho2. rewrite E3, tm_u32_out by tm_lia. rewrite E2, tm_u32_out by tm_lia.
    rewrite E1. apply tm_u32_out; tm_lia. }
  assert (X0 : md_socket_errno mb3 = md_socket_errno mbs) by (unfold md_socket_errno; apply O32; tm_lia).
  assert (X1 : md_send_errno mb3 = md_send_errno mbs) by (unfold md_send_errno; apply O32; tm_lia).
  assert (X2 : md_next mb3 = md_next mbs) by (unfold md_next; apply O32; tm_lia).
  (* the count *)
  assert (N3 : md_n_req mb3 = md_n_req mbs + 1).
  { unfold md_n_req at 1. rewrite E3, tm_u32_out by tm_lia. rewrite E2. apply tm_u32_same; tm_lia. }
  (* the lengths: the old ones, and the new one at n *)
  assert (O64 : forall i, 0 <= i < md_n_req mbs ->
            fld_u64 mb3 (MD_REQ_LEN + 8 * i) = fld_u64 mbs (MD_REQ_LEN + 8 * i)).
  { intros i Hi. rewrite E3, tm_u64_out by tm_lia. rewrite E2, tm_u64_out by tm_lia.
    rewrite E1. apply tm_u64_out; tm_lia. }
  assert (F3 : fld_u64 mb3 (MD_REQ_LEN + 8 * md_n_req mbs) = Z.of_nat (length req))
    by (rewrite E3; apply tm_u64_same; tm_lia).
  (* the slots: the old ones, and the new one at n *)
  assert (SL : forall i, 0 <= i < md_n_req mbs ->
            slice mb3 (MD_REQ + NL_SENT_LEN * i) (fld_u64 mbs (MD_REQ_LEN + 8 * i)) =
            slice mbs (MD_REQ + NL_SENT_LEN * i) (fld_u64 mbs (MD_REQ_LEN + 8 * i))).
  { intros i Hi. pose proof (W5 i Hi) as Wi.
    rewrite E3, tm_slice_upd_out by tm_lia. rewrite E2, tm_slice_upd_out by tm_lia.
    rewrite E1. apply tm_slice_upd_out; tm_lia. }
  assert (SN : slice mb3 (MD_REQ + NL_SENT_LEN * md_n_req mbs) (Z.of_nat (length req)) = req).
  { rewrite E3, tm_slice_upd_out by tm_lia. rewrite E2, tm_slice_upd_out by tm_lia.
    rewrite E1. apply tm_slice_upd_same; tm_lia. }
  (* the marks *)
  assert (SM : md_same mb3 mbs).
  { apply (tm_same_trans _ mb2); [rewrite E3; apply tm_same_upd; tm_lia|].
    apply (tm_same_trans _ mb1); [rewrite E2; apply tm_same_upd; tm_lia|].
    rewrite E1. apply tm_same_upd; tm_lia. }
  assert (MW : model_marks_wf mb3).
  { rewrite E3. apply tm_marks_wf_upd; [tm_lia | tm_lia |].
    rewrite E2. apply tm_marks_wf_upd; [tm_lia | tm_lia |].
    rewrite E1. apply tm_marks_wf_upd; [tm_lia | tm_lia | exact W6]. }
  split; [rewrite L3; exact HL|].
  split.
  { unfold model_wf. rewrite N3, X0, X1, X2.
    split; [tm_lia|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. split; [|exact MW].
    intros i Hi. destruct (Z.eq_dec i (md_n_req mbs)) as [->|Hne].
    - rewrite F3. tm_lia.
    - rewrite O64 by tm_lia. apply W5. tm_lia. }
  split.
  { unfold md_reqs at 1. rewrite N3.
    replace (Z.to_nat (md_n_req mbs + 1)) with (S (Z.to_nat (md_n_req mbs))) by lia.
    rewrite seq_S, map_app. unfold md_reqs. f_equal.
    - apply map_ext_in. intros k Hk. apply in_seq in Hk. cbv beta. unfold md_req_one.
      rewrite O64 by lia. apply SL. lia.
    - transitivity [md_req_one mb3 (Z.of_nat (0 + Z.to_nat (md_n_req mbs))%nat)]; [reflexivity|].
      f_equal. unfold md_req_one. rewrite Nat.add_0_l, Z2Nat.id by lia.
      rewrite F3. exact SN. }
  split; [exact N3|]. split; [exact X0|]. split; [exact X1|]. split; [exact X2|]. exact SM.
Qed.

Print Assumptions md_reqs_length.
Print Assumptions md_zero_sock.
Print Assumptions md_zero_send.
Print Assumptions md_set_next_ok.
Print Assumptions md_set_next_twice.
Print Assumptions md_owe_ok.
