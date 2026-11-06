(* reac-pw/fuzz_link, PLAIN build: the byte facts the walks of the fake kernel (fuzz_socket, fuzz_send, fuzz_recv,
   fuzz_close, fuzz_if_nametoindex / index_of, kernel) use over g_nl.

   - a little-endian field read back from its bytes (`slice` and `rdn` of link_spec.v);
   - a slice or a field after an update inside or outside it (`upd_bytes` of lib/Lib/Mem.v);
   - `nlk_at` cut into the bytes before a run of fields, the fields as cells the walk tactics read and write, and
     the bytes after them, and joined back after the walk. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Bytes.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Lists
   ========================================================================== *)

Lemma Z_to_le_bytes_of_bytes : forall l : list byte, Z_to_le_bytes (length l) (bytes_le_to_Z l) = l.
Proof.
  induction l as [|b l IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
  pose proof (bytes_le_to_Z_nonneg l) as Nl.
  rewrite lor_shiftl8_add by lia.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned.
    change (bv_wrap 8 (bv_unsigned b + 256 * bytes_le_to_Z l))
      with ((bv_unsigned b + 256 * bytes_le_to_Z l) mod 2 ^ 8).
    change (2 ^ 8) with 256. rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace ((bv_unsigned b + 256 * bytes_le_to_Z l) / 256) with (bytes_le_to_Z l); [exact IH|].
    rewrite Z.mul_comm, Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma firstn_plus : forall {A} k1 k2 (l : list A), firstn (k1 + k2) l = firstn k1 l ++ firstn k2 (skipn k1 l).
Proof.
  intros A k1. induction k1 as [|k1 IH]; intros k2 l; [reflexivity|].
  destruct l as [|x l]; [destruct k2; reflexivity|].
  cbn. f_equal. apply IH.
Qed.

Lemma list_eq_nth : forall {A} (l1 l2 : list A), (forall i, nth_error l1 i = nth_error l2 i) -> l1 = l2.
Proof.
  intros A l1. induction l1 as [|x l1 IH]; intros [|y l2] H.
  - reflexivity.
  - specialize (H 0%nat). discriminate.
  - specialize (H 0%nat). discriminate.
  - pose proof (H 0%nat) as H0. cbn in H0. inversion H0; subst. f_equal. apply IH. intros i. exact (H (S i)).
Qed.

Lemma slice_length : forall bs a n, 0 <= a -> 0 <= n -> a + n <= Z.of_nat (length bs) ->
  length (slice bs a n) = Z.to_nat n.
Proof. intros bs a n H0 H1 H2. unfold slice. rewrite length_firstn, length_skipn. lia. Qed.

Lemma slice_split : forall bs a n1 n2, 0 <= a -> 0 <= n1 -> 0 <= n2 ->
  slice bs a (n1 + n2) = slice bs a n1 ++ slice bs (a + n1) n2.
Proof.
  intros bs a n1 n2 Ha H1 H2. unfold slice. rewrite Z2Nat.inj_add by lia. rewrite firstn_plus.
  f_equal. rewrite skipn_skipn. f_equal. f_equal. lia.
Qed.

Lemma slice_app_l : forall l r a n, 0 <= a -> 0 <= n -> a + n <= Z.of_nat (length l) ->
  slice (l ++ r) a n = slice l a n.
Proof.
  intros l r a n Ha Hn H. unfold slice.
  rewrite skipn_app. replace (Z.to_nat a - length l)%nat with 0%nat by lia. cbn [skipn].
  rewrite firstn_app, length_skipn. replace (Z.to_nat n - (length l - Z.to_nat a))%nat with 0%nat by lia.
  cbn [firstn]. apply app_nil_r.
Qed.

Lemma slice_app_r : forall l r a n, Z.of_nat (length l) <= a ->
  slice (l ++ r) a n = slice r (a - Z.of_nat (length l)) n.
Proof.
  intros l r a n H. unfold slice.
  rewrite skipn_app, skipn_all2 by lia. cbn [app]. f_equal. f_equal. lia.
Qed.

Lemma slice_firstn : forall bs k a n, 0 <= a -> 0 <= n -> a + n <= Z.of_nat k ->
  slice (firstn k bs) a n = slice bs a n.
Proof.
  intros bs k a n Ha Hn H. unfold slice. rewrite skipn_firstn_comm, firstn_firstn. f_equal. lia.
Qed.

Lemma slice_skipn : forall bs k a n, Z.of_nat k <= a ->
  slice (skipn k bs) (a - Z.of_nat k) n = slice bs a n.
Proof. intros bs k a n H. unfold slice. rewrite skipn_skipn. f_equal. f_equal. lia. Qed.

(* an update outside a slice leaves it; inside, the slice reads the new bytes *)
Lemma slice_upd_out : forall bs k l a n, 0 <= a -> 0 <= n ->
  (k + length l <= length bs)%nat ->
  a + n <= Z.of_nat k \/ Z.of_nat k + Z.of_nat (length l) <= a ->
  slice (upd_bytes bs k l) a n = slice bs a n.
Proof.
  intros bs k l a n Ha Hn Hk [H|H]; unfold upd_bytes.
  - rewrite slice_app_l by (rewrite ?length_firstn; lia). apply slice_firstn; lia.
  - rewrite app_assoc. rewrite slice_app_r by (rewrite ?length_app, ?length_firstn; lia).
    rewrite length_app, length_firstn.
    replace (Z.of_nat (Nat.min k (length bs) + length l)) with (Z.of_nat (k + length l)) by lia.
    apply slice_skipn. lia.
Qed.

Lemma slice_upd_in : forall bs k l a n, 0 <= n ->
  (k + length l <= length bs)%nat -> Z.of_nat k <= a -> a + n <= Z.of_nat k + Z.of_nat (length l) ->
  slice (upd_bytes bs k l) a n = slice l (a - Z.of_nat k) n.
Proof.
  intros bs k l a n Hn Hk H1 H2. unfold upd_bytes.
  rewrite slice_app_r by (rewrite ?length_firstn; lia).
  rewrite length_firstn. replace (Z.of_nat (Nat.min k (length bs))) with (Z.of_nat k) by lia.
  apply slice_app_l; lia.
Qed.

Lemma rdn_upd_out : forall bs k l a n, 0 <= a -> 0 <= n ->
  (k + length l <= length bs)%nat ->
  a + n <= Z.of_nat k \/ Z.of_nat k + Z.of_nat (length l) <= a ->
  rdn (upd_bytes bs k l) a n = rdn bs a n.
Proof. intros. unfold rdn. f_equal. apply slice_upd_out; assumption. Qed.

Lemma rdn_upd_in : forall bs k l a n, 0 <= n ->
  (k + length l <= length bs)%nat -> Z.of_nat k <= a -> a + n <= Z.of_nat k + Z.of_nat (length l) ->
  rdn (upd_bytes bs k l) a n = rdn l (a - Z.of_nat k) n.
Proof. intros. unfold rdn. f_equal. apply slice_upd_in; assumption. Qed.

Lemma upd_bytes_len : forall bs k l, (k + length l <= length bs)%nat -> length (upd_bytes bs k l) = length bs.
Proof. intros. apply upd_bytes_length. assumption. Qed.

(* ==========================================================================
   2. Fields
   ========================================================================== *)

Lemma rdn_le4_slice : forall bs a, 0 <= a -> a + 4 <= Z.of_nat (length bs) ->
  slice bs a 4 = le4 (wz (rdn bs a 4)).
Proof.
  intros bs a H0 H1. unfold le4, wz, rdn.
  pose proof (slice_length bs a 4 H0 ltac:(lia) H1) as L. change (Z.to_nat 4) with 4%nat in L.
  pose proof (bytes_le_to_Z_nonneg (slice bs a 4)) as N.
  pose proof (bytes_le_to_Z_bound (slice bs a 4)) as B. rewrite L in B. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in B.
  rewrite unsigned_lit by lia.
  transitivity (Z_to_le_bytes (length (slice bs a 4)) (bytes_le_to_Z (slice bs a 4))).
  - symmetry. apply Z_to_le_bytes_of_bytes.
  - rewrite L. reflexivity.
Qed.

Lemma rdn_le8_slice : forall bs a, 0 <= a -> a + 8 <= Z.of_nat (length bs) ->
  slice bs a 8 = le8 (wz (rdn bs a 8)).
Proof.
  intros bs a H0 H1. unfold wz, rdn.
  change (le8 (Z_to_bv 64 (bytes_le_to_Z (slice bs a 8))))
    with (Z_to_le_bytes 8 (bv_unsigned (Z_to_bv 64 (bytes_le_to_Z (slice bs a 8))))).
  pose proof (slice_length bs a 8 H0 ltac:(lia) H1) as L. change (Z.to_nat 8) with 8%nat in L.
  pose proof (bytes_le_to_Z_nonneg (slice bs a 8)) as N.
  pose proof (bytes_le_to_Z_bound (slice bs a 8)) as B. rewrite L in B. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in B.
  rewrite unsigned_lit by lia.
  transitivity (Z_to_le_bytes (length (slice bs a 8)) (bytes_le_to_Z (slice bs a 8))).
  - symmetry. apply Z_to_le_bytes_of_bytes.
  - rewrite L. reflexivity.
Qed.

Lemma rdn_le4_head : forall w r a, a = 0 -> rdn (le4 w ++ r) a 4 = bv_unsigned w mod 2 ^ 32.
Proof.
  intros w r a ->. unfold rdn. rewrite slice_app_l by (rewrite ?length_le4; lia).
  unfold slice. change (Z.to_nat 0) with 0%nat. change (Z.to_nat 4) with 4%nat. cbn [skipn].
  rewrite <- (length_le4 w) at 1. rewrite firstn_all. apply bytes_le_to_Z_le4.
Qed.

Lemma rdn_le8_head : forall w r a, a = 0 -> rdn (le8 w ++ r) a 8 = bv_unsigned w.
Proof.
  intros w r a ->. unfold rdn. rewrite slice_app_l by (rewrite ?length_le8; lia).
  unfold slice. change (Z.to_nat 0) with 0%nat. change (Z.to_nat 8) with 8%nat. cbn [skipn].
  rewrite <- (length_le8 w) at 1. rewrite firstn_all.
  unfold le8, word_to_le_bytes.
  lazymatch goal with |- context [skipn 0 ?l] => change (skipn 0 l) with l end.
  rewrite bytes_le_to_Z_to_le_bytes by apply bv_unsigned_in_range.
  pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R.
  change (8 * Z.of_nat 8) with 64. apply Z.mod_small. lia.
Qed.

Lemma rdn_le4_cons : forall w r a n, 4 <= a -> rdn (le4 w ++ r) a n = rdn r (a - 4) n.
Proof. intros. unfold rdn. rewrite slice_app_r by (rewrite ?length_le4; lia). rewrite length_le4. reflexivity. Qed.

Lemma rdn_le8_cons : forall w r a n, 8 <= a -> rdn (le8 w ++ r) a n = rdn r (a - 8) n.
Proof. intros. unfold rdn. rewrite slice_app_r by (rewrite ?length_le8; lia). rewrite length_le8. reflexivity. Qed.

(* reading a field of a run of cells *)
Ltac rdn_cells :=
  repeat first [ rewrite rdn_le4_head by lia | rewrite rdn_le8_head by lia
               | rewrite rdn_le4_cons by lia | rewrite rdn_le8_cons by lia ].

Lemma rdn_range : forall bs a n, 0 <= a -> 0 <= n -> a + n <= Z.of_nat (length bs) ->
  0 <= rdn bs a n < 2 ^ (8 * n).
Proof.
  intros bs a n H0 H1 H2. unfold rdn. pose proof (slice_length bs a n H0 H1 H2) as L.
  pose proof (bytes_le_to_Z_nonneg (slice bs a n)). pose proof (bytes_le_to_Z_bound (slice bs a n)) as B.
  rewrite L, Z2Nat.id in B by lia. lia.
Qed.

Lemma sx32_wz : forall v, 0 <= v < 2 ^ 31 -> sx32 (wz v) = wz v.
Proof.
  intros v H. unfold sx32, wz. rewrite unsigned_lit by lia. f_equal.
  unfold bv_swrap. change (bv_half_modulus 32) with (2 ^ 31).
  change (bv_wrap 32 (v + 2 ^ 31)) with ((v + 2 ^ 31) mod 2 ^ 32).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma wz_unsigned : forall v, 0 <= v < 2 ^ 64 -> bv_unsigned (wz v) = v.
Proof. intros. apply unsigned_lit. assumption. Qed.

(* ==========================================================================
   3. Memory
   ========================================================================== *)

Lemma bytes_at_unique : forall m a l1 l2,
  bytes_at rsegs m a l1 -> bytes_at rsegs m a l2 -> length l1 = length l2 -> l1 = l2.
Proof.
  intros m a l1 l2 (_ & _ & H1) (_ & _ & H2) L. apply list_eq_nth. intros i.
  destruct (Nat.lt_ge_cases i (length l1)) as [Hi|Hi].
  - rewrite <- H1, <- H2 by lia. reflexivity.
  - rewrite (proj2 (nth_error_None l1 i)), (proj2 (nth_error_None l2 i)) by lia. reflexivity.
Qed.

Lemma nlk_at_unique : forall m b1 b2, nlk_at m b1 -> nlk_at m b2 -> b1 = b2.
Proof.
  intros m b1 b2 [[H1 _] L1] [[H2 _] L2]. apply (bytes_at_unique m A_G_NL); [exact H1 | exact H2 | lia].
Qed.

Lemma bytes_at_at : forall m a b l, bytes_at rsegs m a l -> a = b -> bytes_at rsegs m b l.
Proof. intros; subst; assumption. Qed.

Lemma wr_at_sub : forall m a n k j, wr_at rsegs m a n -> 0 <= k -> 0 <= j -> k + j <= n -> wr_at rsegs m (a + k) j.
Proof.
  intros m a n k j (H0 & H1 & H) Hk Hj Hkj. split; [lia|]. split; [lia|].
  intros i Hi. replace (a + k + i) with (a + (k + i)) by lia. apply H. lia.
Qed.

(* the run of `n` 4-byte fields from `off` *)
Fixpoint u32_cells (bs : list byte) (off : Z) (n : nat) : list cell :=
  match n with
  | O => []
  | S n' => C4 (wz (fld_u32 bs off)) :: u32_cells bs (off + 4) n'
  end.

Lemma u32_cells_wf : forall n bs off, cells_wf (u32_cells bs off n).
Proof. induction n as [|n IH]; intros; cbn; [exact I | split; [exact I | apply IH]]. Qed.

Lemma u32_cells_size : forall n bs off, cells_size (u32_cells bs off n) = (4 * n)%nat.
Proof. induction n as [|n IH]; intros; cbn [u32_cells cells_size csize]; [reflexivity|]. rewrite IH. lia. Qed.

Lemma u32_cells_bytes : forall n bs off, 0 <= off -> off + 4 * Z.of_nat n <= Z.of_nat (length bs) ->
  cells_bytes (u32_cells bs off n) = slice bs off (4 * Z.of_nat n).
Proof.
  induction n as [|n IH]; intros bs off H0 H1.
  - cbn [u32_cells cells_bytes]. unfold slice. change (4 * Z.of_nat 0) with 0. reflexivity.
  - cbn [u32_cells cells_bytes cbytes]. rewrite IH by lia.
    replace (4 * Z.of_nat (S n)) with (4 + 4 * Z.of_nat n) by lia.
    rewrite slice_split by lia. f_equal. symmetry. apply rdn_le4_slice; lia.
Qed.

(* `nlk_at` cut at the cells `cs`, which hold the bytes of g_nl from `off` *)
Lemma nlk_split : forall m bs off cs,
  nlk_at m bs -> 0 <= off -> cells_wf cs -> off + Z.of_nat (cells_size cs) <= NK_SIZE ->
  cells_bytes cs = slice bs off (Z.of_nat (cells_size cs)) ->
  bytes_at rsegs m A_G_NL (firstn (Z.to_nat off) bs) /\
  rw_cells rsegs m (A_G_NL + off) cs /\
  bytes_at rsegs m (A_G_NL + off + Z.of_nat (cells_size cs)) (skipn (Z.to_nat off + cells_size cs) bs) /\
  wr_at rsegs m A_G_NL NK_SIZE.
Proof.
  intros m bs off cs [[HB HW] HL] H0 Hwf Hsz HC.
  rewrite HL in HW.
  pose proof (CB3_bytes (Z.to_nat off) (cells_size cs) bs ltac:(lia)) as E.
  rewrite <- E in HB.
  apply bytes_at_app in HB. destruct HB as [B1 HB]. apply bytes_at_app in HB. destruct HB as [B2 B3].
  rewrite firstn_length_le in B2, B3 by lia.
  rewrite firstn_length_le in B3 by (rewrite ?length_skipn; lia).
  split; [exact B1|]. split; [|split; [|exact HW]].
  - split; [split; [exact Hwf|]|].
    + rewrite HC. unfold slice. rewrite Nat2Z.id.
      eapply bytes_at_at; [exact B2 | lia].
    + apply wr_at_sub with (n := NK_SIZE); [exact HW | lia | lia | lia].
  - eapply bytes_at_at; [exact B3 | lia].
Qed.

Lemma nlk_split_u32 : forall m bs off n,
  nlk_at m bs -> 0 <= off -> off + 4 * Z.of_nat n <= NK_SIZE ->
  bytes_at rsegs m A_G_NL (firstn (Z.to_nat off) bs) /\
  rw_cells rsegs m (A_G_NL + off) (u32_cells bs off n) /\
  bytes_at rsegs m (A_G_NL + off + 4 * Z.of_nat n) (skipn (Z.to_nat off + 4 * n) bs) /\
  wr_at rsegs m A_G_NL NK_SIZE.
Proof.
  intros m bs off n NK H0 H1.
  pose proof NK as [_ HL].
  destruct (nlk_split m bs off (u32_cells bs off n) NK H0 (u32_cells_wf n bs off)) as (B1 & C & B3 & W).
  - rewrite u32_cells_size. lia.
  - rewrite u32_cells_size, u32_cells_bytes by lia. f_equal. lia.
  - rewrite u32_cells_size in B3. split; [exact B1|]. split; [exact C|]. split; [|exact W].
    eapply bytes_at_at; [exact B3 | lia].
Qed.

(* ... and joined back after the walk wrote new cells there *)
Lemma nlk_join : forall m bs off cs,
  Z.of_nat (length bs) = NK_SIZE -> 0 <= off -> off + Z.of_nat (cells_size cs) <= NK_SIZE ->
  bytes_at rsegs m A_G_NL (firstn (Z.to_nat off) bs) ->
  rw_cells rsegs m (A_G_NL + off) cs ->
  bytes_at rsegs m (A_G_NL + off + Z.of_nat (cells_size cs)) (skipn (Z.to_nat off + cells_size cs) bs) ->
  wr_at rsegs m A_G_NL NK_SIZE ->
  nlk_at m (upd_bytes bs (Z.to_nat off) (cells_bytes cs)) /\
  length (upd_bytes bs (Z.to_nat off) (cells_bytes cs)) = length bs.
Proof.
  intros m bs off cs HL H0 Hsz B1 [[Hwf B2] _] B3 W.
  pose proof (cells_bytes_length cs Hwf) as Lc.
  assert (LU : length (upd_bytes bs (Z.to_nat off) (cells_bytes cs)) = length bs)
    by (apply upd_bytes_length; lia).
  split; [|exact LU].
  split; [split|].
  - unfold upd_bytes. apply bytes_at_app. split; [exact B1|].
    rewrite firstn_length_le by lia. apply bytes_at_app. split.
    + eapply bytes_at_at; [exact B2 | lia].
    + rewrite Lc. eapply bytes_at_at; [exact B3 | lia].
  - rewrite LU, HL. exact W.
  - rewrite LU. exact HL.
Qed.

(* the cells' fields after the join, and every byte outside them *)
Lemma rdn_join_in : forall bs off cs a n,
  Z.of_nat (length bs) = NK_SIZE -> cells_wf cs -> 0 <= off -> off + Z.of_nat (cells_size cs) <= NK_SIZE ->
  0 <= n -> off <= a -> a + n <= off + Z.of_nat (cells_size cs) ->
  rdn (upd_bytes bs (Z.to_nat off) (cells_bytes cs)) a n = rdn (cells_bytes cs) (a - off) n.
Proof.
  intros bs off cs a n HL Hwf H0 Hsz Hn H1 H2. pose proof (cells_bytes_length cs Hwf) as Lc.
  rewrite rdn_upd_in by lia. f_equal. lia.
Qed.

Lemma rdn_join_out : forall bs off cs a n,
  Z.of_nat (length bs) = NK_SIZE -> cells_wf cs -> 0 <= off -> off + Z.of_nat (cells_size cs) <= NK_SIZE ->
  0 <= a -> 0 <= n -> a + n <= off \/ off + Z.of_nat (cells_size cs) <= a ->
  rdn (upd_bytes bs (Z.to_nat off) (cells_bytes cs)) a n = rdn bs a n.
Proof.
  intros bs off cs a n HL Hwf H0 Hsz Ha Hn H. pose proof (cells_bytes_length cs Hwf) as Lc.
  apply rdn_upd_out; lia.
Qed.

Lemma slice_join_out : forall bs off cs a n,
  Z.of_nat (length bs) = NK_SIZE -> cells_wf cs -> 0 <= off -> off + Z.of_nat (cells_size cs) <= NK_SIZE ->
  0 <= a -> 0 <= n -> a + n <= off \/ off + Z.of_nat (cells_size cs) <= a ->
  slice (upd_bytes bs (Z.to_nat off) (cells_bytes cs)) a n = slice bs a n.
Proof.
  intros bs off cs a n HL Hwf H0 Hsz Ha Hn H. pose proof (cells_bytes_length cs Hwf) as Lc.
  apply slice_upd_out; lia.
Qed.

(* the names of the fake kernel's layout, as numbers *)
Ltac nk_nums := unfold NK_CHUNK, NK_CHUNK_LEN, NK_N_CHUNKS, NK_NEXT, NK_END_ERRNO, NK_SOCKET_ERRNO, NK_SEND_ERRNO,
  NK_OPEN, NK_OPENED, NK_CLOSED, NK_MISUSE, NK_SENT, NK_SENT_LEN, NK_N_SENT, NK_IF_NAME, NK_IF_INDEX, NK_N_IF, NK_SIZE,
  NL_CHUNK_MAX, NL_SENT_LEN, NL_CHUNKS, NL_SENT_MAX, A_G_NL in *.

(* the join, with the two ways a field of the joined bytes reads *)
Lemma nlk_join_rd : forall m bs off cs,
  Z.of_nat (length bs) = NK_SIZE -> 0 <= off -> cells_wf cs -> off + Z.of_nat (cells_size cs) <= NK_SIZE ->
  bytes_at rsegs m A_G_NL (firstn (Z.to_nat off) bs) ->
  rw_cells rsegs m (A_G_NL + off) cs ->
  bytes_at rsegs m (A_G_NL + off + Z.of_nat (cells_size cs)) (skipn (Z.to_nat off + cells_size cs) bs) ->
  wr_at rsegs m A_G_NL NK_SIZE ->
  exists bs', nlk_at m bs' /\ Z.of_nat (length bs') = NK_SIZE /\
    (forall a n, 0 <= a -> 0 <= n -> a + n <= off \/ off + Z.of_nat (cells_size cs) <= a ->
       rdn bs' a n = rdn bs a n /\ slice bs' a n = slice bs a n) /\
    (forall a n, off <= a -> a + n <= off + Z.of_nat (cells_size cs) -> 0 <= n ->
       rdn bs' a n = rdn (cells_bytes cs) (a - off) n).
Proof.
  intros m bs off cs HL H0 Hwf Hsz B1 C B3 W.
  destruct (nlk_join m bs off cs HL H0 Hsz B1 C B3 W) as [NK LU].
  exists (upd_bytes bs (Z.to_nat off) (cells_bytes cs)). split; [exact NK|]. split; [rewrite LU; exact HL|].
  split.
  - intros a n Ha Hn H. split; [apply rdn_join_out | apply slice_join_out]; assumption.
  - intros a n H1 H2 Hn. apply rdn_join_in; assumption.
Qed.

(* well-formedness when the chunk queue, the request ring and the interface count are untouched *)
Lemma nlk_wf_same_queues : forall bs bs',
  nlk_wf bs ->
  nk_n_chunks bs' = nk_n_chunks bs -> nk_n_sent bs' = nk_n_sent bs -> nk_n_if bs' = nk_n_if bs ->
  (forall i, 0 <= i < nk_n_chunks bs -> fld_u64 bs' (NK_CHUNK_LEN + 8 * i) = fld_u64 bs (NK_CHUNK_LEN + 8 * i)) ->
  (forall i, 0 <= i < nk_n_sent bs -> fld_u64 bs' (NK_SENT_LEN + 8 * i) = fld_u64 bs (NK_SENT_LEN + 8 * i)) ->
  0 <= nk_next bs' <= nk_n_chunks bs ->
  0 <= nk_open bs' <= 1 -> 0 <= nk_opened bs' < 2 ^ 31 -> 0 <= nk_closed bs' < 2 ^ 31 -> 0 <= nk_misuse bs' <= 1 ->
  0 <= nk_end_errno bs' < 2 ^ 31 -> 0 <= nk_socket_errno bs' < 2 ^ 31 -> 0 <= nk_send_errno bs' < 2 ^ 31 ->
  nlk_wf bs'.
Proof.
  intros bs bs' (W1 & W2 & W3 & W4 & _ & _ & _ & _ & _ & _ & _ & W12 & W13) E1 E2 E3 C1 C2 N O1 O2 O3 O4 O5 O6 O7.
  unfold nlk_wf. rewrite E1, E2, E3.
  refine (conj W1 (conj N (conj W3 (conj W4 (conj O1 (conj O2 (conj O3 (conj O4 (conj O5 (conj O6 (conj O7
    (conj _ _)))))))))))).
  - intros i Hi. rewrite C1 by exact Hi. apply W12. exact Hi.
  - intros i Hi. rewrite C2 by exact Hi. apply W13. exact Hi.
Qed.

(* the side conditions of the cut and the join *)
Ltac kn_side :=
  first [ assumption | reflexivity
        | solve [cbn [cells_wf cell_wf]; repeat split]
        | solve [cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; nk_nums; lia] ].

(* the callee-saved registers of a concrete register map against the entry map *)
Ltac solve_rp :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; unfold callee_saved in Hr;
  destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; [reflexivity..|];
  assert (r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
    as Hc by lia;
  destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; reflexivity.
