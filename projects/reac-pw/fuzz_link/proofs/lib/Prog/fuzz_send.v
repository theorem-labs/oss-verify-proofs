(* fuzz_send (netlink.h:89-105), PLAIN build: the walk of its contract (lib/Prog/fuzz_send_c.v) on the plain
   image, 0x13528-0x1360f (58 instructions, a 48-byte frame), the three instructions of ___errno_location
   (0x16e04: `mv a0, tp; addi a0, a0, -0xa4; ret`) on the failing path, and memcpy (0x1ec5c, memcpy_holds) on
   the recording path. Each instruction is fetched from the image and decoded by computation (lib/Lib/Step.v
   `step`).
   The g_nl bytes stay one `bytes_at` over all 271992 bytes: a load reads its field through them (gnl_rd4), a
   store turns them into `upd_bytes` of the stored bytes (gnl_store), and memcpy's destination g_nl.sent[n] is
   cut out as a cell and joined back after the call (gnl_cut, gnl_join3).
   The index n = n_sent stays symbolic (no case split): the `slli` shifts become 512 * n and 8 * n (fix_shl),
   so lia handles the addresses of sent[n] and sent_len[n] as they are.
   The three ways into 0x1356c (misuse set by fd, set by a closed socket, or left) and the two into 0x135b4
   (len < 512, len = 512) are joined with evt_cut, so the rest of the walk is written once. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf kn_nlk memcpy_c memcpy fuzz_send_c.
Local Open Scope Z_scope.

(* the misuse flag fuzz_send leaves (netlink.h:92-93), as the Post states it *)
Definition snd_mis (fd : Z) (bs : list byte) : Z :=
  if (fd =? NL_FD) && negb (nk_open bs =? 0) then nk_misuse bs else 1.

Lemma upd_bytes_self4 : forall bs k, 0 <= k -> k + 4 <= Z.of_nat (length bs) ->
  upd_bytes bs (Z.to_nat k) (le4 (wz (rdn bs k 4))) = bs.
Proof.
  intros bs k H0 H1. rewrite <- rdn_le4_slice by lia.
  unfold upd_bytes. rewrite slice_length by lia. unfold slice.
  change (Z.to_nat 4) with 4%nat. apply CB3_bytes. lia.
Qed.

Lemma signed_wz : forall v, 0 <= v < 2 ^ 63 -> bv_signed (wz v) = v.
Proof.
  intros v H. unfold bv_signed, wz. rewrite unsigned_lit by lia.
  unfold bv_swrap. change (bv_half_modulus 64) with (2 ^ 63).
  change (bv_wrap 64 (v + 2 ^ 63)) with ((v + 2 ^ 63) mod 2 ^ 64).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma gnl_rd4 : forall m cur a k v, bytes_at rsegs m 203648 cur -> a = 203648 + k -> 0 <= k ->
  k + 4 <= Z.of_nat (length cur) -> rdn cur k 4 = v ->
  ov_read_bytes rsegs m (wa a) 4 = Some (le4 (wz v)).
Proof.
  intros m cur a k v G -> H0 H1 <-.
  rewrite (bytes_at_read rsegs m 203648 cur k 4 G H0) by lia.
  rewrite <- rdn_le4_slice by lia. reflexivity.
Qed.

Lemma gnl_store_ok : forall m a k j, wr_at rsegs m 203648 271992 -> a = 203648 + k -> 0 <= k ->
  k + Z.of_nat j <= 271992 -> store_ok rsegs m (wa a) j = true.
Proof. intros m a k j W -> H0 H1. exact (wr_at_store_ok rsegs m 203648 271992 k j W H0 H1). Qed.

Lemma gnl_wr : forall m cur a k l, bytes_at rsegs m 203648 cur -> a = 203648 + k -> 0 <= k ->
  k + Z.of_nat (length l) <= Z.of_nat (length cur) ->
  bytes_at rsegs (write_to_mem m (wa a) l) 203648 (upd_bytes cur (Z.to_nat k) l).
Proof. intros m cur a k l G -> H0 H1. apply bytes_at_write_inside; [exact G | lia | lia]. Qed.

(* g_nl.sent[n], the memcpy destination, cut out of the g_nl bytes, and the bytes joined back after the copy *)
Lemma gnl_cut : forall m cur K L, bytes_at rsegs m 203648 cur -> wr_at rsegs m 203648 (Z.of_nat (length cur)) ->
  (K + L <= length cur)%nat ->
  bytes_at rsegs m 203648 (firstn K cur) /\
  rw_cells rsegs m (203648 + Z.of_nat K) [CB L (firstn L (skipn K cur))] /\
  bytes_at rsegs m (203648 + Z.of_nat K + Z.of_nat L) (skipn (K + L) cur).
Proof.
  intros m cur K L G W H.
  pose proof (CB3_bytes K L cur H) as E.
  rewrite <- E in G. apply bytes_at_app in G. destruct G as [B1 G]. apply bytes_at_app in G. destruct G as [B2 B3].
  rewrite firstn_length_le in B2, B3 by lia.
  rewrite firstn_length_le in B3 by (rewrite length_skipn; lia).
  split; [exact B1|]. split; [|exact B3].
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [|exact I]. rewrite firstn_length_le by (rewrite length_skipn; lia). reflexivity.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B2.
  - cbn [cells_size csize]. rewrite Nat.add_0_r.
    apply wr_at_sub with (n := Z.of_nat (length cur)); [exact W | lia | lia | lia].
Qed.

Lemma gnl_join3 : forall m cur K L l, length l = L -> (K + L <= length cur)%nat ->
  bytes_at rsegs m 203648 (firstn K cur) -> bytes_at rsegs m (203648 + Z.of_nat K) l ->
  bytes_at rsegs m (203648 + Z.of_nat K + Z.of_nat L) (skipn (K + L) cur) ->
  bytes_at rsegs m 203648 (upd_bytes cur K l).
Proof.
  intros m cur K L l HlL H B1 B2 B3. subst L. unfold upd_bytes. apply bytes_at_app. split; [exact B1|].
  rewrite firstn_length_le by lia. apply bytes_at_app. split; [exact B2 | exact B3].
Qed.

(* a field of the g_nl bytes after stores into them *)
Lemma rdn_le4_0 : forall w, rdn (le4 w) 0 4 = bv_unsigned w mod 2 ^ 32.
Proof. intros w. rewrite <- (app_nil_r (le4 w)). apply rdn_le4_head. reflexivity. Qed.
Lemma rdn_le8_0 : forall w, rdn (le8 w) 0 8 = bv_unsigned w.
Proof. intros w. rewrite <- (app_nil_r (le8 w)). apply rdn_le8_head. reflexivity. Qed.
Lemma slice_all0 : forall (l : list byte) n, n = Z.of_nat (length l) -> slice l 0 n = l.
Proof.
  intros l n ->. unfold slice. rewrite Nat2Z.id. change (Z.to_nat 0) with 0%nat. cbn [skipn]. apply firstn_all.
Qed.

Ltac len_upd :=
  repeat match goal with |- context [length (upd_bytes ?b ?k ?l)] =>
    rewrite (upd_bytes_length b k l) by (len_upd; rewrite ?length_le4, ?length_le8; lia) end.
Ltac upd_side := len_upd; rewrite ?length_le4, ?length_le8; lia.
Ltac upd_rw :=
  repeat first [ rewrite rdn_upd_out by upd_side | rewrite rdn_upd_in by upd_side
               | rewrite slice_upd_out by upd_side | rewrite slice_upd_in by upd_side ];
  rewrite ?Z2Nat.id by lia; rewrite ?Z.sub_diag, ?rdn_le4_0, ?rdn_le8_0.

(* x << k of a small value, as a product *)
Ltac fix_shl :=
  repeat match goal with |- context [Z.shiftl (bv_unsigned (wz ?v)) ?k] =>
    let c := eval vm_compute in (2 ^ k) in
    replace (Z.shiftl (bv_unsigned (wz v)) k) with (c * v)
      by (unfold wz; rewrite unsigned_lit by lia; rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ k) with c; lia)
  end.

(* a store into g_nl at offset k, after its step: the g_nl bytes take the stored bytes *)
Ltac gnl_store k :=
  lazymatch goal with
  | G : bytes_at rsegs ?mm 203648 ?cur |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?a ?l) _) =>
      let E := addr_expr a in
      change (write_to_mem mm a l) with (write_to_mem mm (wa E) l);
      let G' := fresh "G" in
      assert (G' : bytes_at rsegs (write_to_mem mm (wa E) l) 203648 (upd_bytes cur (Z.to_nat k) l))
        by (apply gnl_wr; [exact G | lia | lia | upd_side]);
      clear G; rename G' into G
  end;
  store_done.

Lemma snd_mis_range : forall fd bs, nlk_wf bs -> 0 <= snd_mis fd bs <= 1.
Proof.
  intros fd bs (_ & _ & _ & _ & _ & _ & _ & W8 & _). unfold snd_mis.
  destruct ((fd =? NL_FD) && negb (nk_open bs =? 0)); lia.
Qed.

Lemma nk_sent_len : forall bs, 0 <= nk_n_sent bs -> Z.of_nat (length (nk_sent bs)) = nk_n_sent bs.
Proof. intros bs H. unfold nk_sent. rewrite length_map, length_seq. lia. Qed.

Lemma nk_sent_same : forall bs bs', nk_n_sent bs' = nk_n_sent bs ->
  (forall i, 0 <= i < nk_n_sent bs -> nk_sent_one bs' i = nk_sent_one bs i) -> nk_sent bs' = nk_sent bs.
Proof.
  intros bs bs' E H. unfold nk_sent. rewrite E. apply map_ext_in. intros i Hi. apply in_seq in Hi. apply H. lia.
Qed.

Lemma nk_sent_snoc : forall bs bs' r, 0 <= nk_n_sent bs -> nk_n_sent bs' = nk_n_sent bs + 1 ->
  (forall i, 0 <= i < nk_n_sent bs -> nk_sent_one bs' i = nk_sent_one bs i) ->
  nk_sent_one bs' (nk_n_sent bs) = r -> nk_sent bs' = nk_sent bs ++ [r].
Proof.
  intros bs bs' r H0 E H Hr. unfold nk_sent. rewrite E.
  replace (Z.to_nat (nk_n_sent bs + 1)) with (S (Z.to_nat (nk_n_sent bs))) by lia.
  rewrite seq_S, map_app. cbn [map]. f_equal.
  - apply map_ext_in. intros i Hi. apply in_seq in Hi. apply H. lia.
  - rewrite Nat.add_0_l, Z2Nat.id by lia. rewrite Hr. reflexivity.
Qed.

(* the Post of the contract, for the final g_nl bytes bs' *)
Local Abbreviation snd_q m' bs bs' req fd ea r10 r12 :=
  (nlk_at m' bs'
   /\ nlk_wf bs'
   /\ nk_socket_errno bs' = nk_socket_errno bs /\ nk_end_errno bs' = nk_end_errno bs
   /\ nk_open bs' = nk_open bs /\ nk_opened bs' = nk_opened bs
   /\ nk_closed bs' = nk_closed bs
   /\ nk_misuse bs' = (if (fd =? NL_FD) && negb (nk_open bs =? 0) then nk_misuse bs else 1)
   /\ (nk_send_errno bs <> 0 ->
         r10 = wz (-1) /\ nk_send_errno bs' = 0
         /\ u32_at m' ea (nk_send_errno bs)
         /\ nk_n_sent bs' = nk_n_sent bs /\ nk_sent bs' = nk_sent bs)
   /\ (nk_send_errno bs = 0 ->
         r10 = r12 /\ nk_send_errno bs' = 0
         /\ nk_sent bs' = owe (nk_sent bs) req
         /\ nk_n_sent bs' = Z.of_nat (length (owe (nk_sent bs) req)))).

Ltac nk_unf := unfold nk_n_chunks, nk_next, nk_n_sent, nk_n_if, nk_open, nk_opened, nk_closed, nk_misuse,
  nk_end_errno, nk_socket_errno, nk_send_errno, fld_u32, fld_u64.
Ltac nk_unf_in H := unfold nk_n_chunks, nk_next, nk_n_sent, nk_n_if, nk_open, nk_opened, nk_closed, nk_misuse,
  nk_end_errno, nk_socket_errno, nk_send_errno, fld_u32, fld_u64 in H.

(* the path where a pending send_errno fails the call: misuse, then send_errno := 0 *)
Lemma post_err : forall m' bs req fd ea (r10 r12 z : word),
  Z.of_nat (length bs) = 271992 -> nlk_wf bs -> nk_send_errno bs <> 0 -> bv_unsigned z = 0 ->
  bytes_at rsegs m' 203648
    (upd_bytes (upd_bytes bs (Z.to_nat 262688) (le4 (wz (snd_mis fd bs)))) (Z.to_nat 262672) (le4 z)) ->
  wr_at rsegs m' 203648 271992 ->
  u32_at m' ea (nk_send_errno bs) -> r10 = wz (-1) ->
  snd_q m' bs (upd_bytes (upd_bytes bs (Z.to_nat 262688) (le4 (wz (snd_mis fd bs)))) (Z.to_nat 262672) (le4 z))
    req fd ea r10 r12.
Proof.
  intros m' bs req fd ea r10 r12 z HL WF SE Z0 B W EU R10.
  pose proof (snd_mis_range fd bs WF) as Mb.
  pose proof WF as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13).
  nk_unf_in W1. nk_unf_in W2. nk_unf_in W3. nk_unf_in W4. nk_unf_in W5. nk_unf_in W6. nk_unf_in W7.
  nk_unf_in W8. nk_unf_in W9. nk_unf_in W10. nk_unf_in W11. nk_unf_in W12. nk_unf_in W13. nk_nums.
  remember (snd_mis fd bs) as mis eqn:Emis.
  set (bs' := upd_bytes (upd_bytes bs (Z.to_nat 262688) (le4 (wz mis))) (Z.to_nat 262672) (le4 z)).
  assert (HLb : Z.of_nat (length bs') = 271992) by (unfold bs'; len_upd; lia).
  assert (OUTr : forall a n, 0 <= a -> 0 <= n -> a + n <= 262672 \/ (262676 <= a /\ a + n <= 262688) \/ 262692 <= a ->
                 rdn bs' a n = rdn bs a n) by (intros a n Ha Hn Hd; unfold bs'; upd_rw; reflexivity).
  assert (OUTs : forall a n, 0 <= a -> 0 <= n -> a + n <= 262672 \/ (262676 <= a /\ a + n <= 262688) \/ 262692 <= a ->
                 slice bs' a n = slice bs a n) by (intros a n Ha Hn Hd; unfold bs'; upd_rw; reflexivity).
  assert (MIS : rdn bs' 262688 4 = mis)
    by (unfold bs'; upd_rw; unfold wz; rewrite unsigned_lit by lia; apply Z.mod_small; lia).
  assert (SE' : rdn bs' 262672 4 = 0) by (unfold bs'; upd_rw; rewrite Z0; reflexivity).
  assert (SENT : nk_sent bs' = nk_sent bs).
  { apply nk_sent_same.
    - nk_unf. nk_nums. apply OUTr; lia.
    - intros i Hi. pose proof (W13 i) as L13. unfold nk_n_sent, fld_u32, NK_N_SENT in Hi.
      specialize (L13 Hi). unfold nk_sent_one, fld_u64. nk_nums.
      rewrite (OUTr (270888 + 8 * i) 8) by lia. apply OUTs; lia. }
  refine (conj (conj (conj B _) HLb) _); [rewrite HLb; exact W|].
  split.
  { apply (nlk_wf_same_queues bs bs' WF).
    all: nk_unf; nk_nums.
    all: try (intros i Hi); first [ apply OUTr; lia | rewrite MIS; lia | rewrite SE'; lia | rewrite OUTr by lia; lia ]. }
  split; [nk_unf; nk_nums; apply OUTr; lia|]. split; [nk_unf; nk_nums; apply OUTr; lia|].
  split; [nk_unf; nk_nums; apply OUTr; lia|]. split; [nk_unf; nk_nums; apply OUTr; lia|].
  split; [nk_unf; nk_nums; apply OUTr; lia|].
  split; [unfold nk_misuse, fld_u32, NK_MISUSE; rewrite MIS, Emis; reflexivity|].
  split.
  - intros _. refine (conj R10 (conj SE' (conj EU (conj _ SENT)))). nk_unf. nk_nums. apply OUTr; lia.
  - intros H. exfalso. exact (SE H).
Qed.

(* the path where the ring is full (n_sent = 16): only the misuse flag changes *)
Lemma post_full : forall m' bs req fd ea (r10 r12 : word),
  Z.of_nat (length bs) = 271992 -> nlk_wf bs -> nk_send_errno bs = 0 -> nk_n_sent bs = 16 ->
  bytes_at rsegs m' 203648 (upd_bytes bs (Z.to_nat 262688) (le4 (wz (snd_mis fd bs)))) ->
  wr_at rsegs m' 203648 271992 -> r10 = r12 ->
  snd_q m' bs (upd_bytes bs (Z.to_nat 262688) (le4 (wz (snd_mis fd bs)))) req fd ea r10 r12.
Proof.
  intros m' bs req fd ea r10 r12 HL WF SE N16 B W R10.
  pose proof (snd_mis_range fd bs WF) as Mb.
  pose proof WF as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13).
  nk_unf_in W1. nk_unf_in W2. nk_unf_in W3. nk_unf_in W4. nk_unf_in W5. nk_unf_in W6. nk_unf_in W7.
  nk_unf_in W8. nk_unf_in W9. nk_unf_in W10. nk_unf_in W11. nk_unf_in W12. nk_unf_in W13. nk_nums.
  remember (snd_mis fd bs) as mis eqn:Emis.
  set (bs' := upd_bytes bs (Z.to_nat 262688) (le4 (wz mis))).
  assert (HLb : Z.of_nat (length bs') = 271992) by (unfold bs'; len_upd; lia).
  assert (OUTr : forall a n, 0 <= a -> 0 <= n -> a + n <= 262688 \/ 262692 <= a ->
                 rdn bs' a n = rdn bs a n) by (intros a n Ha Hn Hd; unfold bs'; upd_rw; reflexivity).
  assert (OUTs : forall a n, 0 <= a -> 0 <= n -> a + n <= 262688 \/ 262692 <= a ->
                 slice bs' a n = slice bs a n) by (intros a n Ha Hn Hd; unfold bs'; upd_rw; reflexivity).
  assert (MIS : rdn bs' 262688 4 = mis)
    by (unfold bs'; upd_rw; unfold wz; rewrite unsigned_lit by lia; apply Z.mod_small; lia).
  assert (SENT : nk_sent bs' = nk_sent bs).
  { apply nk_sent_same.
    - nk_unf. nk_nums. apply OUTr; lia.
    - intros i Hi. pose proof (W13 i) as L13. unfold nk_n_sent, fld_u32, NK_N_SENT in Hi.
      specialize (L13 Hi). unfold nk_sent_one, fld_u64. nk_nums.
      rewrite (OUTr (270888 + 8 * i) 8) by lia. apply OUTs; lia. }
  assert (NS : nk_n_sent bs' = nk_n_sent bs) by (nk_unf; nk_nums; apply OUTr; lia).
  refine (conj (conj (conj B _) HLb) _); [rewrite HLb; exact W|].
  split.
  { apply (nlk_wf_same_queues bs bs' WF).
    all: nk_unf; nk_nums.
    all: try (intros i Hi); first [ apply OUTr; lia | rewrite MIS; lia | rewrite OUTr by lia; lia ]. }
  split; [nk_unf; nk_nums; apply OUTr; lia|]. split; [nk_unf; nk_nums; apply OUTr; lia|].
  split; [nk_unf; nk_nums; apply OUTr; lia|]. split; [nk_unf; nk_nums; apply OUTr; lia|].
  split; [nk_unf; nk_nums; apply OUTr; lia|].
  split; [unfold nk_misuse, fld_u32, NK_MISUSE; rewrite MIS, Emis; reflexivity|].
  split.
  - intros H. exfalso. exact (H SE).
  - intros _. assert (LS : Z.of_nat (length (nk_sent bs)) = 16) by (rewrite nk_sent_len; lia).
    assert (OW : owe (nk_sent bs) req = nk_sent bs)
      by (unfold owe, NL_SENT_MAX; destruct (Z.ltb_spec (Z.of_nat (length (nk_sent bs))) 16); [lia | reflexivity]).
    rewrite OW, SENT, NS, LS, N16.
    refine (conj R10 (conj _ (conj eq_refl eq_refl))). nk_unf. nk_nums. rewrite OUTr by lia. exact SE.
Qed.

(* the recording path: misuse, then sent[n] := req, n_sent := n + 1, sent_len[n] := len *)
Lemma post_copy : forall m' bs req fd ea (r10 r12 v a2w : word),
  Z.of_nat (length bs) = 271992 -> nlk_wf bs -> nk_send_errno bs = 0 -> rdn bs 271016 4 <= 15 ->
  Z.of_nat (length req) = bv_unsigned a2w -> bv_unsigned a2w <= 512 ->
  bv_unsigned v mod 2 ^ 32 = rdn bs 271016 4 + 1 ->
  bytes_at rsegs m' 203648
    (upd_bytes (upd_bytes (upd_bytes (upd_bytes bs (Z.to_nat 262688) (le4 (wz (snd_mis fd bs))))
       (Z.to_nat (262692 + 512 * rdn bs 271016 4)) req) (Z.to_nat 271016) (le4 v))
       (Z.to_nat (270888 + 8 * rdn bs 271016 4)) (le8 a2w)) ->
  wr_at rsegs m' 203648 271992 -> r10 = r12 ->
  snd_q m' bs
    (upd_bytes (upd_bytes (upd_bytes (upd_bytes bs (Z.to_nat 262688) (le4 (wz (snd_mis fd bs))))
       (Z.to_nat (262692 + 512 * rdn bs 271016 4)) req) (Z.to_nat 271016) (le4 v))
       (Z.to_nat (270888 + 8 * rdn bs 271016 4)) (le8 a2w))
    req fd ea r10 r12.
Proof.
  intros m' bs req fd ea r10 r12 v a2w HL WF SE N15 LR L5 V B W R10.
  pose proof (snd_mis_range fd bs WF) as Mb.
  pose proof WF as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13).
  nk_unf_in W1. nk_unf_in W2. nk_unf_in W3. nk_unf_in W4. nk_unf_in W5. nk_unf_in W6. nk_unf_in W7.
  nk_unf_in W8. nk_unf_in W9. nk_unf_in W10. nk_unf_in W11. nk_unf_in W12. nk_unf_in W13. nk_nums.
  remember (snd_mis fd bs) as mis eqn:Emis.
  remember (rdn bs 271016 4) as n eqn:En.
  set (bs' := upd_bytes (upd_bytes (upd_bytes (upd_bytes bs (Z.to_nat 262688) (le4 (wz mis)))
       (Z.to_nat (262692 + 512 * n)) req) (Z.to_nat 271016) (le4 v)) (Z.to_nat (270888 + 8 * n)) (le8 a2w)).
  assert (HLb : Z.of_nat (length bs') = 271992) by (unfold bs'; len_upd; lia).
  assert (OUTr : forall a k, 0 <= a -> 0 <= k ->
                 a + k <= 262688 \/ (262692 <= a /\ a + k <= 262692 + 512 * n)
                 \/ (262692 + 512 * n + bv_unsigned a2w <= a /\ a + k <= 270888 + 8 * n)
                 \/ (270896 + 8 * n <= a /\ a + k <= 271016) \/ 271020 <= a ->
                 rdn bs' a k = rdn bs a k) by (intros a k Ha Hk Hd; unfold bs'; upd_rw; reflexivity).
  assert (OUTs : forall a k, 0 <= a -> 0 <= k ->
                 a + k <= 262688 \/ (262692 <= a /\ a + k <= 262692 + 512 * n)
                 \/ (262692 + 512 * n + bv_unsigned a2w <= a /\ a + k <= 270888 + 8 * n)
                 \/ (270896 + 8 * n <= a /\ a + k <= 271016) \/ 271020 <= a ->
                 slice bs' a k = slice bs a k) by (intros a k Ha Hk Hd; unfold bs'; upd_rw; reflexivity).
  assert (MIS : rdn bs' 262688 4 = mis)
    by (unfold bs'; upd_rw; unfold wz; rewrite unsigned_lit by lia; apply Z.mod_small; lia).
  assert (NS : rdn bs' 271016 4 = n + 1) by (unfold bs'; upd_rw; exact V).
  assert (SL : rdn bs' (270888 + 8 * n) 8 = bv_unsigned a2w) by (unfold bs'; upd_rw; reflexivity).
  assert (SR : slice bs' (262692 + 512 * n) (bv_unsigned a2w) = req)
    by (unfold bs'; upd_rw; apply slice_all0; lia).
  assert (SENT : nk_sent bs' = nk_sent bs ++ [req]).
  { apply nk_sent_snoc.
    - nk_unf. nk_nums. lia.
    - nk_unf. nk_nums. rewrite NS, En. reflexivity.
    - intros i Hi. nk_unf_in Hi. nk_nums. rewrite <- En in Hi.
      pose proof (W13 i ltac:(lia)) as L13. unfold nk_sent_one, fld_u64. nk_nums.
      rewrite (OUTr (270888 + 8 * i) 8) by lia. apply OUTs; lia.
    - unfold nk_sent_one, fld_u64, nk_n_sent, fld_u32. nk_nums. rewrite <- En, SL. exact SR. }
  refine (conj (conj (conj B _) HLb) _); [rewrite HLb; exact W|].
  split.
  { unfold nlk_wf. nk_unf. nk_nums.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
      (conj _ _)))))))))))).
    - rewrite OUTr by lia. lia.
    - rewrite !OUTr by lia. lia.
    - rewrite NS. lia.
    - rewrite OUTr by lia. lia.
    - rewrite OUTr by lia. lia.
    - rewrite OUTr by lia. lia.
    - rewrite OUTr by lia. lia.
    - rewrite MIS. lia.
    - rewrite OUTr by lia. lia.
    - rewrite OUTr by lia. lia.
    - rewrite OUTr by lia. lia.
    - intros i Hi. rewrite OUTr in Hi by lia. rewrite OUTr by lia. apply W12. lia.
    - intros i Hi. rewrite NS in Hi. destruct (Z.eq_dec i n) as [->|Ni].
      + rewrite SL. lia.
      + rewrite OUTr by lia. apply W13. lia. }
  split; [nk_unf; nk_nums; apply OUTr; lia|]. split; [nk_unf; nk_nums; apply OUTr; lia|].
  split; [nk_unf; nk_nums; apply OUTr; lia|]. split; [nk_unf; nk_nums; apply OUTr; lia|].
  split; [nk_unf; nk_nums; apply OUTr; lia|].
  split; [unfold nk_misuse, fld_u32, NK_MISUSE; rewrite MIS, Emis; reflexivity|].
  split.
  - intros H. exfalso. exact (H SE).
  - intros _. assert (LS : Z.of_nat (length (nk_sent bs)) = n)
      by (rewrite nk_sent_len; [unfold nk_n_sent, fld_u32, NK_N_SENT; lia | unfold nk_n_sent, fld_u32, NK_N_SENT; lia]).
    assert (OW : owe (nk_sent bs) req = nk_sent bs ++ [req])
      by (unfold owe, NL_SENT_MAX; destruct (Z.ltb_spec (Z.of_nat (length (nk_sent bs))) 16); [reflexivity | lia]).
    rewrite OW, SENT. refine (conj R10 (conj _ (conj eq_refl _))).
    + nk_unf. nk_nums. rewrite OUTr by lia. exact SE.
    + nk_unf. nk_nums. rewrite NS, length_app. cbn [length]. lia.
Qed.

(* the end of every path: the epilogue's frame release, the return, and the Post's two uniqueness steps *)
Ltac snd_end sp :=
  lazymatch goal with FR : rw_cells _ _ (bv_unsigned sp + -48) _, ST : stk _ _ _ (bv_unsigned sp + -48) |- _ =>
    release_frame FR ST (bv_unsigned sp) end;
  apply evt_done; eexists _, _; split; [reflexivity|];
  split; [solve_rp|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
  split; [eassumption|];
  let bs0 := fresh "bs0" in let req0 := fresh "req0" in
  let N0 := fresh "N0" in let R0 := fresh "R0" in let L0 := fresh "L0" in
  intros bs0 req0 N0 R0 L0;
  (* the Post's bs0 and req0 are the entry's bs and req: nlk_at and bytes_at fix them *)
  match goal with
  | UB : forall b1 b2, nlk_at _ b1 -> nlk_at _ b2 -> b1 = b2, NK : nlk_at _ ?bs |- _ =>
      first [ constr_eq bs bs0; fail 1 | pose proof (UB bs0 bs N0 NK) as Ebs; subst bs0 ]
  end;
  lazymatch goal with
  | UR : forall r, bytes_at _ _ _ r -> _ -> r = ?req |- _ =>
      pose proof (UR req0 R0 L0) as Ereq; subst req0
  end.

(* The stack below the frame after memcpy: the contract does not place [lo, sp - 48) apart from g_nl, so the
   copy may write there; every byte it writes is the copied text, so each stays readable. *)
Lemma stk_after_copy : forall m m' lo hi d len (l : list byte),
  stk rsegs m lo hi -> munch [(d, d + len)] m m' -> wmono rsegs m m' ->
  bytes_at rsegs m' d l -> Z.of_nat (length l) = len ->
  stk rsegs m' lo hi.
Proof.
  intros m m' lo hi d len l (H1 & H2 & H) Hm Hw (Hd0 & Hdl & Hb) Hl.
  split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hwa (b & Hb0)]. split; [apply Hw; exact Hwa|].
  destruct (Z.ltb_spec0 a d) as [Lt|Ge]; [|destruct (Z.ltb_spec0 a (d + len)) as [Lt2|Ge2]].
  - exists b. unfold mrd in *. rewrite Hm; [exact Hb0|]. cbn [outside]. rewrite wa_unsigned by lia.
    split; [lia | exact I].
  - specialize (Hb (Z.to_nat (a - d)) ltac:(lia)).
    replace (d + Z.of_nat (Z.to_nat (a - d))) with a in Hb by lia.
    destruct (nth_error l (Z.to_nat (a - d))) as [b'|] eqn:E.
    + exists b'. exact Hb.
    + apply nth_error_None in E. lia.
  - exists b. unfold mrd in *. rewrite Hm; [exact Hb0|]. cbn [outside]. rewrite wa_unsigned by lia.
    split; [lia | exact I].
Qed.

(* post_call (lib/Lib/Tac.v) for the memcpy call, with the stack below the frame carried by stk_after_copy *)
Ltac copy_post mm :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO; destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  let DC := fresh "DC" in let SC := fresh "SC" in let BR := fresh "BR" in
  destruct PO as [E [MUc [WMc [MIc [DC SC]]]]]; subst ms';
  pose proof DC as [[_ BR] _]; cbn [cells_bytes cbytes] in BR; rewrite app_nil_r in BR; clear DC;
  lazymatch type of MUc with munch _ mm ?m' =>
    lazymatch goal with ST : stk _ mm ?lo ?hi |- _ =>
      let ST' := fresh "ST" in
      pose proof (stk_after_copy mm m' lo hi _ _ _ ST MUc WMc BR ltac:(lia)) as ST';
      clear ST
    end;
    transport_after_call rsegs mm m' MUc WMc; clear MUc WMc;
    try match goal with H : mem_inv rsegs mm |- _ => clear H end
  end;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

Theorem fuzz_send_holds : fuzz_send_contract.
Proof.
  unfold fuzz_send_contract. apply leaf_intro.
  - intros r1 r2 m E H. cbv beta in H |- *.
    unfold frame_apart_gnl, apart_frame, apart_gnl, errno_at, spZ, arg in *. rewrite <- ?E. exact H.
  - intros r1 r2 m E. cbv beta. unfold errno_at. rewrite <- ?E. reflexivity.
  - intros r1 r2 m q1 q2 m' E E' H. cbv beta in H |- *. unfold errno_at, arg in *. rewrite <- ?E, <- ?E'. exact H.
  - unfold leaf_walk, FUZZ_SEND.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
    cbv zeta. intros (bs & req & NK & FA & WF & WE & EF & EG & RQ & LR & L5 & RG & RF) MI ST LO SP.
    rewrite ?mkR_sp, ?mkR_errno, ?mkR_a1, ?mkR_a2 in *.
    unfold frame_apart_gnl, apart_frame, apart_gnl, A_G_NL, NK_SIZE, ERRNO_TP_OFF, NL_SENT_LEN in FA, EF, EG, RG, RF, WE, L5.
    rewrite ?mkR_sp in FA, EF, RF.
    pose proof (nlk_at_unique m) as UB.
    assert (UR : forall r, bytes_at rsegs m (bv_unsigned a1) r -> Z.of_nat (length r) = bv_unsigned a2 -> r = req)
      by (intros r Hr Lr; apply (bytes_at_unique m (bv_unsigned a1)); [exact Hr | exact RQ | lia]).
    pose proof NK as [[G WRA] HL].
    rewrite HL in WRA. change A_G_NL with 203648 in G, WRA. change NK_SIZE with 271992 in WRA, HL.
    pose proof WF as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13).
    unfold nk_n_chunks, nk_next, nk_n_sent, nk_n_if, nk_open, nk_opened, nk_closed, nk_misuse,
      nk_end_errno, nk_socket_errno, nk_send_errno, fld_u32, fld_u64 in W1, W2, W3, W4, W5, W6, W7, W8, W9, W10,
      W11, W12, W13.
    unfold NK_N_CHUNKS, NK_NEXT, NK_N_SENT, NK_N_IF, NK_OPEN, NK_OPENED, NK_CLOSED, NK_MISUSE, NK_END_ERRNO,
      NK_SOCKET_ERRNO, NK_SEND_ERRNO, NK_CHUNK_LEN, NK_SENT_LEN, NL_CHUNKS, NL_SENT_MAX, NL_CHUNK_MAX, NL_SENT_LEN
      in W1, W2, W3, W4, W5, W6, W7, W8, W9, W10, W11, W12, W13.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (466320, 474668);
                            (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof (zr_word tp) as Rtp. unfold inr64 in Rtp.
    pose proof (zr_word a1) as Ra1. unfold inr64 in Ra1.
    pose proof WE as [WE0 [WE1 _]].
    carve_frame 48%nat ST.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. zstep. zstep. zstep. zstep.
    lazymatch type of FR with context [CB 8 ?l] => set (jk := l) in FR; clearbody jk end.
    eapply (evt_cut rsegs (fun ms' => exists (x10 : word) (m1 : word -> option byte),
      ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 a2 (Z_to_bv 64 203648) x10 a1
                  (Z_to_bv 64 465792) (Z_to_bv 64 7) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 79212) fc None m1 (seg_rom rsegs) /\
      bytes_at rsegs m1 203648 (upd_bytes bs (Z.to_nat 262688) (le4 (wz (snd_mis (bv_unsigned a0) bs)))) /\
      wr_at rsegs m1 203648 271992 /\
      rw_cells rsegs m1 (bv_unsigned sp + -48) [CB 8 jk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
      stk rsegs m1 lo (bv_unsigned sp + -48) /\
      munch [(bv_unsigned sp + -48, bv_unsigned sp); (466320, 474668);
             (bv_unsigned tp + ERRNO_TP_OFF, bv_unsigned tp + ERRNO_TP_OFF + 4)] m m1 /\
      wmono rsegs m m1 /\ mem_inv rsegs m1 /\
      bytes_at rsegs m1 (bv_unsigned a1) req /\ wr_at rsegs m1 (bv_unsigned tp + -164) 4)).
    { zstep. if_cases K.
      + (* fd <> 7: misuse *)
        zify_cond K.
        zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          pose proof (gnl_store_ok mm 466336 262688 4 WRA eq_refl ltac:(lia) ltac:(lia)) as HS end.
        zstep. gnl_store 262688.
        assert (M1 : snd_mis (bv_unsigned a0) bs = 1)
          by (unfold snd_mis, NL_FD; destruct (Z.eqb_spec (bv_unsigned a0) 7); [lia | reflexivity]).
        apply evt_done. eexists _, _. split; [reflexivity|]. rewrite M1.
        refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))); eassumption.
      + zify_cond K.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          pose proof (gnl_rd4 mm bs 466324 262676 (rdn bs 262676 4) G eq_refl ltac:(lia) ltac:(lia) eq_refl) as HR end.
        zstep. rewrite sx32_wz by lia.
        zstep. if_cases K2.
        * (* open <> 0: no misuse *)
          zify_cond K2. try (unfold wz in K2; rewrite unsigned_lit in K2 by lia).
          assert (M1 : snd_mis (bv_unsigned a0) bs = rdn bs 262688 4)
            by (unfold snd_mis, NL_FD, nk_open, nk_misuse, fld_u32, NK_OPEN, NK_MISUSE;
                destruct (Z.eqb_spec (bv_unsigned a0) 7); [|lia];
                destruct (Z.eqb_spec (rdn bs 262676 4) 0); [lia|reflexivity]).
          apply evt_done. eexists _, _. split; [reflexivity|]. rewrite M1, upd_bytes_self4 by lia.
          refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))); eassumption.
        * (* open = 0: misuse *)
          zify_cond K2. try (unfold wz in K2; rewrite unsigned_lit in K2 by lia).
          zstep.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            pose proof (gnl_store_ok mm 466336 262688 4 WRA eq_refl ltac:(lia) ltac:(lia)) as HS end.
          zstep. gnl_store 262688.
          assert (M1 : snd_mis (bv_unsigned a0) bs = 1)
            by (unfold snd_mis, NL_FD, nk_open, nk_misuse, fld_u32, NK_OPEN, NK_MISUSE;
                destruct (Z.eqb_spec (bv_unsigned a0) 7); [|reflexivity];
                destruct (Z.eqb_spec (rdn bs 262676 4) 0); [reflexivity|lia]).
          apply evt_done. eexists _, _. split; [reflexivity|]. rewrite M1.
          refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))); eassumption. }
    clear G WRA FR ST MU WM MI RQ WE.
    intros ms' (x10 & m1 & -> & G & WRA & FR & ST & MU & WM & MI & RQ & WE).
    unfold ERRNO_TP_OFF in MU.
    pose proof (snd_mis_range (bv_unsigned a0) bs WF) as Mb.
    remember (snd_mis (bv_unsigned a0) bs) as mis eqn:Emis.
    remember (upd_bytes bs (Z.to_nat 262688) (le4 (wz mis))) as cur eqn:Ecur.
    assert (HLc : Z.of_nat (length cur) = 271992)
      by (subst cur; rewrite upd_bytes_length; rewrite ?length_le4; lia).
    zstep. zstep.
    pose proof (gnl_rd4 m1 cur 466320 262672 (rdn bs 262672 4) G eq_refl ltac:(lia) ltac:(lia)
                  ltac:(subst cur; apply rdn_upd_out; rewrite ?length_le4; lia)) as HR.
    zstep. rewrite sx32_wz by lia.
    zstep. if_cases K.
    + (* send_errno = 0 *)
      zify_cond K. try (unfold wz in K; rewrite unsigned_lit in K by lia).
      zstep. zstep.
      pose proof (gnl_rd4 m1 cur 474664 271016 (rdn bs 271016 4) G eq_refl ltac:(lia) ltac:(lia)
                    ltac:(subst cur; apply rdn_upd_out; rewrite ?length_le4; lia)) as HR2.
      zstep. rewrite sx32_wz by lia.
      zstep. zstep. if_cases K2.
      * (* the ring is full: n_sent = 16 *)
        zify_cond K2. rewrite signed_wz in K2 by lia.
        zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
        snd_end sp.
        eexists. subst cur mis.
        eapply post_full; [exact HL | exact WF | exact K | unfold nk_n_sent, fld_u32, NK_N_SENT; lia
                          | exact G | exact WRA | reflexivity].
      * zify_cond K2. rewrite signed_wz in K2 by lia.
        zstep. zstep.
        eapply (evt_cut rsegs (fun ms' => ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 a2
                  (Z_to_bv 64 203648) (wz (rdn bs 271016 4)) a1 a2 (Z_to_bv 64 512) a4 a5 a6 a7
                  (Z_to_bv 64 465792) (wz (rdn bs 262672 4)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 79284) fc None m1 (seg_rom rsegs))).
        { zstep. if_cases K3.
          - apply evt_done. reflexivity.
          - zify_cond K3. zstep.
            assert (A2 : a2 = Z_to_bv 64 512) by (apply bv_eq; rewrite unsigned_lit by lia; lia).
            subst a2. apply evt_done. reflexivity. }
        intros ms' ->.
        zstep. zstep. zstep. zstep. zstep.
        fix_shl.
        remember (Z_to_bv 64 (466340 + 512 * rdn bs 271016 4)) as d eqn:Ed.
        assert (Hd : bv_unsigned d = 466340 + 512 * rdn bs 271016 4) by (subst d; apply unsigned_lit; lia).
        clear Ed.
        assert (KL : (Z.to_nat (262692 + 512 * rdn bs 271016 4) + Z.to_nat (bv_unsigned a2) <= length cur)%nat)
          by lia.
        destruct (gnl_cut m1 cur (Z.to_nat (262692 + 512 * rdn bs 271016 4)) (Z.to_nat (bv_unsigned a2)) G
                    ltac:(rewrite HLc; exact WRA) KL) as (B1 & DST & B3).
        clear G.
        remember (firstn (Z.to_nat (262692 + 512 * rdn bs 271016 4)) cur) as p1 eqn:Ep1.
        remember (skipn (Z.to_nat (262692 + 512 * rdn bs 271016 4) + Z.to_nat (bv_unsigned a2)) cur) as p3 eqn:Ep3.
        remember (firstn (Z.to_nat (bv_unsigned a2)) (skipn (Z.to_nat (262692 + 512 * rdn bs 271016 4)) cur))
          as slot eqn:Eslot.
        assert (HL1 : Z.of_nat (length p1) = 262692 + 512 * rdn bs 271016 4)
          by (subst p1; rewrite length_firstn; lia).
        assert (HL3 : Z.of_nat (length p3) = 271992 - (262692 + 512 * rdn bs 271016 4 + bv_unsigned a2))
          by (subst p3; rewrite length_skipn; lia).
        replace (203648 + Z.of_nat (Z.to_nat (262692 + 512 * rdn bs 271016 4))) with (bv_unsigned d) in DST by lia.
        replace (203648 + Z.of_nat (Z.to_nat (262692 + 512 * rdn bs 271016 4)) + Z.of_nat (Z.to_nat (bv_unsigned a2)))
          with (bv_unsigned d + bv_unsigned a2) in B3 by lia.
        zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          eapply evt_cut;
          [ eapply memcpy_holds with (src := req) (junk := slot);
            [ exact RQ | lia | exact DST | lia | exact MI ]
          | copy_post mm ] end.
        lazymatch goal with BR : bytes_at _ ?mm (bv_unsigned d) req |- _ =>
          assert (G : bytes_at rsegs mm 203648 (upd_bytes cur (Z.to_nat (262692 + 512 * rdn bs 271016 4)) req))
            by (apply (gnl_join3 mm cur (Z.to_nat (262692 + 512 * rdn bs 271016 4)) (Z.to_nat (bv_unsigned a2)) req);
                [ lia | exact KL | subst p1; exact B1 | eapply bytes_at_at; [exact BR | lia]
                | subst p3; eapply bytes_at_at; [exact B3 | lia] ])
        end.
        clear B1 B3 BR.
        zstep. zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          pose proof (gnl_rd4 mm _ 474664 271016 (rdn bs 271016 4) G eq_refl ltac:(lia) ltac:(len_upd; lia)
                        ltac:(subst cur; upd_rw; reflexivity)) as HR3 end.
        zstep. rewrite sx32_wz by lia.
        zstep. zstep. zstep.
        fix_shl.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          pose proof (gnl_store_ok mm 474664 271016 4 WRA eq_refl ltac:(lia) ltac:(lia)) as HS end.
        zstep. gnl_store 271016.
        zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          pose proof (gnl_store_ok mm (474536 + 8 * rdn bs 271016 4) (270888 + 8 * rdn bs 271016 4) 8 WRA
                        ltac:(lia) ltac:(lia) ltac:(lia)) as HS end.
        zstep. gnl_store (270888 + 8 * rdn bs 271016 4).
        zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
        snd_end sp.
        eexists. subst cur mis.
        eapply post_copy; [exact HL | exact WF | exact K | lia | exact LR | lia | | exact G | exact WRA | reflexivity].
        unfold wz; rewrite ?unsigned_lit by lia; rewrite ?Z.mod_small by lia; lia.
    + (* a pending send_errno: errno := send_errno, send_errno := 0, answer -1 *)
      zify_cond K. try (unfold wz in K; rewrite unsigned_lit in K by lia).
      zstep. zstep. zstep. zstep.
      match goal with WE : wr_at _ ?mm (bv_unsigned tp + -164) 4 |- _ =>
        pose proof (wr_at_store_ok rsegs mm (bv_unsigned tp + -164) 4 0 4 WE ltac:(lia) ltac:(lia)) as HSe end.
      rewrite Z.add_0_r in HSe.
      zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?a ?bs) _) =>
        let E := addr_expr a in
        change (write_to_mem mm a bs) with (write_to_mem mm (wa E) bs);
        assert (ERB : bytes_at rsegs (write_to_mem mm (wa E) bs) E bs)
          by (apply bytes_at_write_same; rewrite ?length_le4; lia)
      end.
      store_done.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (gnl_store_ok mm 466320 262672 4 WRA eq_refl ltac:(lia) ltac:(lia)) as HS end.
      zstep. gnl_store 262672.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      snd_end sp.
      eexists. subst cur mis.
      eapply post_err; [exact HL | exact WF | exact K | | exact G | exact WRA | exact ERB | reflexivity].
      first [reflexivity | apply unsigned_lit; lia].
Qed.
