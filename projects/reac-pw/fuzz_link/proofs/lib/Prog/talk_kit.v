(* talk, PLAIN build: small facts the fragments of the walk share (lib/Prog/talk_defs.v).
   Words as Z (`Z_to_bv 64`), reads of byte lists, comparisons, and the memory steps a
   memcpy or a byte store makes. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem talk_defs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Spec Require StrFun.
Local Open Scope Z_scope.

(* --------------------------------------------------------------------------
   1. words
   -------------------------------------------------------------------------- *)

Lemma tk_signed_lit : forall z, - 2 ^ 63 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. unfold bv_signed. rewrite Z_to_bv_unsigned. rewrite bv_swrap_wrap'.
  apply bv_swrap_small. change (bv_half_modulus 64) with (2 ^ 63). lia.
Qed.

Lemma tk_lts : forall x y, - 2 ^ 63 <= x < 2 ^ 63 -> - 2 ^ 63 <= y < 2 ^ 63 ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_lts. rewrite !tk_signed_lit by lia. reflexivity. Qed.

Lemma tk_ltu : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma tk_eqb : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma tk_sx32_small : forall v, 0 <= v < 2 ^ 31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sx32. f_equal. rewrite unsigned_lit by lia. apply bv_swrap_small.
  change (bv_half_modulus 32) with (2 ^ 31). lia.
Qed.

Lemma tk_zx32_small : forall v, 0 <= v < 2 ^ 32 -> zx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma tk_zx16_small : forall v, 0 <= v < 2 ^ 16 -> zx16 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold zx16. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma tk_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. exact R. Qed.

(* two bytes read with lbu and joined with slli 8 / or *)
Lemma tk_lor_shl8 : forall x y, 0 <= x -> 0 <= y < 256 -> Z.lor (Z.shiftl x 8) y = y + 256 * x.
Proof. intros x y Hx Hy. rewrite Z.lor_comm. apply lor_shiftl8_add; lia. Qed.

(* --------------------------------------------------------------------------
   2. byte lists
   -------------------------------------------------------------------------- *)

Lemma tk_slice_length : forall c off n, 0 <= off -> 0 <= n -> off + n <= Z.of_nat (length c) ->
  length (slice c off n) = Z.to_nat n.
Proof. intros c off n H1 H2 H3. unfold slice. rewrite length_firstn, length_skipn. lia. Qed.

Lemma tk_bytes_le : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof. exact StrFun.Z_to_le_bytes_to_Z. Qed.

Lemma tk_le4 : forall bs : list byte, length bs = 4%nat -> bs = le4 (Z_to_bv 64 (bytes_le_to_Z bs)).
Proof.
  intros bs H. unfold le4. pose proof (bytes_le_to_Z_nonneg bs) as N. pose proof (bytes_le_to_Z_bound bs) as B.
  rewrite H in B. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in B.
  rewrite unsigned_lit by lia. rewrite <- H at 1. symmetry. apply tk_bytes_le.
Qed.

Lemma tk_le2 : forall bs : list byte, length bs = 2%nat -> bs = le2 (Z_to_bv 64 (bytes_le_to_Z bs)).
Proof.
  intros bs H. unfold le2. pose proof (bytes_le_to_Z_nonneg bs) as N. pose proof (bytes_le_to_Z_bound bs) as B.
  rewrite H in B. change (2 ^ (8 * Z.of_nat 2)) with (2 ^ 16) in B.
  rewrite unsigned_lit by lia. rewrite <- H at 1. symmetry. apply tk_bytes_le.
Qed.

Lemma tk_le8 : forall bs : list byte, length bs = 8%nat -> bs = le8 (Z_to_bv 64 (bytes_le_to_Z bs)).
Proof.
  intros bs H. rewrite <- store_bytes_8. pose proof (bytes_le_to_Z_nonneg bs) as N.
  pose proof (bytes_le_to_Z_bound bs) as B. rewrite H in B. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in B.
  change (width_bytes 64) with 8%nat. rewrite unsigned_lit by lia. rewrite <- H at 1. symmetry. apply tk_bytes_le.
Qed.

Lemma tk_rdn_range : forall c off n, 0 <= link_spec.rdn c off n.
Proof. intros. apply bytes_le_to_Z_nonneg. Qed.

Lemma tk_rdn_bound : forall c off n, 0 <= off -> 0 <= n -> off + n <= Z.of_nat (length c) ->
  link_spec.rdn c off n < 2 ^ (8 * n).
Proof.
  intros c off n H1 H2 H3. unfold link_spec.rdn. pose proof (bytes_le_to_Z_bound (slice c off n)) as B.
  rewrite tk_slice_length in B by lia. rewrite Z2Nat.id in B by lia. exact B.
Qed.

Lemma tk_nth_slice : forall c off n k, 0 <= off -> 0 <= k < n -> off + n <= Z.of_nat (length c) ->
  nth_error (slice c off n) (Z.to_nat k) = nth_error c (Z.to_nat (off + k)).
Proof.
  intros c off n k H1 H2 H3. unfold slice. rewrite nth_error_firstn.
  destruct (Nat.ltb_spec (Z.to_nat k) (Z.to_nat n)) as [L|L]; [|lia].
  rewrite nth_error_skipn. f_equal. lia.
Qed.

Lemma tk_rd16 : forall c off b0 b1, 0 <= off -> off + 2 <= Z.of_nat (length c) ->
  nth_error c (Z.to_nat off) = Some b0 -> nth_error c (Z.to_nat (off + 1)) = Some b1 ->
  rd16 c off = bv_unsigned b0 + 256 * bv_unsigned b1.
Proof.
  intros c off b0 b1 H1 H2 E0 E1. unfold rd16, link_spec.rdn, slice. change (Z.to_nat 2) with 2%nat.
  destruct (skipn (Z.to_nat off) c) as [|x [|y rest]] eqn:S.
  - apply (f_equal (@length byte)) in S. rewrite length_skipn in S. cbn in S. lia.
  - apply (f_equal (@length byte)) in S. rewrite length_skipn in S. cbn in S. lia.
  - assert (Ex : nth_error (skipn (Z.to_nat off) c) 0 = Some x) by (rewrite S; reflexivity).
    assert (Ey : nth_error (skipn (Z.to_nat off) c) 1 = Some y) by (rewrite S; reflexivity).
    rewrite nth_error_skipn, Nat.add_0_r, E0 in Ex. injection Ex as <-.
    rewrite nth_error_skipn in Ey. replace (Z.to_nat off + 1)%nat with (Z.to_nat (off + 1)) in Ey by lia.
    rewrite E1 in Ey. injection Ey as <-.
    cbn [firstn bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r.
    pose proof (tk_byte_range b0). pose proof (tk_byte_range b1).
    rewrite lor_shiftl8_add by lia. lia.
Qed.

(* --------------------------------------------------------------------------
   3. reads
   -------------------------------------------------------------------------- *)

Lemma tk_read : forall m A c (off : Z) (n : nat),
  bytes_at rsegs m A c -> 0 <= off -> off + Z.of_nat n <= Z.of_nat (length c) ->
  ov_read_bytes rsegs m (Z_to_bv 64 (A + off)) n = Some (slice c off (Z.of_nat n)).
Proof.
  intros m A c off n HB H1 H2. unfold slice. rewrite Nat2Z.id.
  change (Z_to_bv 64 (A + off)) with (wa (A + off)). apply bytes_at_read; [exact HB | lia | lia].
Qed.

Lemma tk_read1 : forall m A c (off : Z) b,
  bytes_at rsegs m A c -> 0 <= off -> nth_error c (Z.to_nat off) = Some b ->
  ov_read_bytes rsegs m (Z_to_bv 64 (A + off)) 1 = Some [b].
Proof.
  intros m A c off b HB H1 E.
  assert (L : (Z.to_nat off < length c)%nat) by (apply nth_error_Some; rewrite E; discriminate).
  rewrite (tk_read m A c off 1 HB H1) by lia. unfold slice. change (Z.to_nat (Z.of_nat 1)) with 1%nat.
  destruct (skipn (Z.to_nat off) c) as [|x rest] eqn:S.
  - apply (f_equal (@length byte)) in S. rewrite length_skipn in S. cbn in S. lia.
  - assert (Ex : nth_error (skipn (Z.to_nat off) c) 0 = Some x) by (rewrite S; reflexivity).
    rewrite nth_error_skipn, Nat.add_0_r, E in Ex. injection Ex as <-. reflexivity.
Qed.

Lemma tk_bytes_slice : forall m A (bs : list byte) off n, bytes_at rsegs m A bs ->
  0 <= off -> 0 <= n -> off + n <= Z.of_nat (length bs) -> bytes_at rsegs m (A + off) (slice bs off n).
Proof.
  intros m A bs off n HB H1 H2 H3. unfold slice.
  rewrite <- (firstn_skipn (Z.to_nat off) bs) in HB. apply bytes_at_app in HB. destruct HB as [_ HB].
  rewrite length_firstn in HB. replace (Z.of_nat (Nat.min (Z.to_nat off) (length bs))) with off in HB by lia.
  rewrite <- (firstn_skipn (Z.to_nat n) (skipn (Z.to_nat off) bs)) in HB. apply bytes_at_app in HB. exact (proj1 HB).
Qed.

Lemma tk_nth_some : forall (c : list byte) k, (k < length c)%nat -> exists b, nth_error c k = Some b.
Proof. intros c k H. destruct (nth_error c k) as [b|] eqn:E; [eauto|]. apply nth_error_None in E. lia. Qed.

(* one memory, one list: two lists of the same length at the same address are equal *)
Lemma tk_bytes_at_uniq : forall m a (l1 l2 : list byte),
  bytes_at rsegs m a l1 -> bytes_at rsegs m a l2 -> length l1 = length l2 -> l1 = l2.
Proof.
  intros m a l1 l2 (_ & _ & H1) (_ & _ & H2) L. apply nth_error_ext. intros i.
  destruct (Nat.ltb_spec i (length l1)) as [Hi|Hi].
  - rewrite <- H1 by exact Hi. apply H2. lia.
  - rewrite !(proj2 (nth_error_None _ _)) by lia. reflexivity.
Qed.

(* --------------------------------------------------------------------------
   4. memory after a write
   -------------------------------------------------------------------------- *)

Lemma tk_rw_split : forall m A n k (j : list byte), (k <= n)%nat ->
  rw_cells rsegs m A [CB n j] ->
  rw_cells rsegs m A [CB k (firstn k j)] /\ rw_cells rsegs m (A + Z.of_nat k) [CB (n - k) (skipn k j)].
Proof.
  intros m A n k j Hk [[Hwf Hb] Hw]. cbn in Hwf. destruct Hwf as [Hl _].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw.
  rewrite <- (firstn_skipn k j) in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite length_firstn in B2. replace (Nat.min k (length j)) with k in B2 by lia.
  destruct Hw as (W1 & W2 & W3). split.
  - split; [split|].
    + cbn. split; [rewrite length_firstn; lia | exact I].
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B1.
    + cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|].
      intros i Hi. apply W3. lia.
  - split; [split|].
    + cbn. split; [rewrite length_skipn; lia | exact I].
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B2.
    + cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|].
      intros i Hi. replace (A + Z.of_nat k + i) with (A + (Z.of_nat k + i)) by lia. apply W3. lia.
Qed.

Lemma tk_rw_merge : forall m A k l (x y : list byte),
  rw_cells rsegs m A [CB k x] -> rw_cells rsegs m (A + Z.of_nat k) [CB l y] ->
  rw_cells rsegs m A [CB (k + l) (x ++ y)].
Proof.
  intros m A k l x y [[Hwf1 Hb1] Hw1] [[Hwf2 Hb2] Hw2].
  cbn in Hwf1, Hwf2. destruct Hwf1 as [L1 _]. destruct Hwf2 as [L2 _].
  cbn [cells_bytes cbytes] in Hb1, Hb2. rewrite app_nil_r in Hb1, Hb2.
  cbn [cells_size csize] in Hw1, Hw2. rewrite Nat.add_0_r in Hw1, Hw2.
  destruct Hw1 as (W1 & W1' & W1''). destruct Hw2 as (W2 & W2' & W2'').
  split; [split|].
  - cbn. split; [rewrite length_app; lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. rewrite L1. split; assumption.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|].
    intros i Hi. destruct (Z.ltb_spec i (Z.of_nat k)) as [Lt|Ge].
    + apply W1''. lia.
    + replace (A + i) with (A + Z.of_nat k + (i - Z.of_nat k)) by lia. apply W2''. lia.
Qed.

Lemma tk_rw_bytes : forall m A n (j : list byte), rw_cells rsegs m A [CB n j] -> bytes_at rsegs m A j.
Proof. intros m A n j [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

Lemma tk_rw_len : forall m A n (j : list byte), rw_cells rsegs m A [CB n j] -> length j = n.
Proof. intros m A n j [[Hwf _] _]. cbn in Hwf. tauto. Qed.

(* a region a callee rewrote in place: the u8arr view of the block takes the new bytes *)
Lemma tk_u8arr_upd : forall W m m' A (bs xs : list byte) (off : nat),
  u8arr rsegs m A bs -> munch W m m' -> wmono rsegs m m' ->
  (forall x, A <= x < A + Z.of_nat (length bs) -> outside W x \/
     (A + Z.of_nat off <= x < A + Z.of_nat off + Z.of_nat (length xs))) ->
  bytes_at rsegs m' (A + Z.of_nat off) xs -> (off + length xs <= length bs)%nat ->
  u8arr rsegs m' A (upd_bytes bs off xs).
Proof.
  intros W m m' A bs xs off [(Ha & Hl & Hb) Hw] MU WM HW (Hx1 & Hx2 & Hx) Hle. split.
  - split; [lia|]. rewrite upd_bytes_length by exact Hle. split; [lia|].
    intros i Hi. rewrite upd_bytes_nth by assumption.
    destruct (Nat.leb_spec off i); destruct (Nat.ltb_spec i (off + length xs)); cbn [andb].
    + replace (A + Z.of_nat i) with (A + Z.of_nat off + Z.of_nat (i - off)) by lia. apply Hx. lia.
    + rewrite <- Hb by exact Hi. unfold mrd. rewrite MU; [reflexivity|].
      rewrite wa_unsigned by lia. destruct (HW (A + Z.of_nat i) ltac:(lia)) as [O|O]; [exact O|lia].
    + rewrite <- Hb by exact Hi. unfold mrd. rewrite MU; [reflexivity|].
      rewrite wa_unsigned by lia. destruct (HW (A + Z.of_nat i) ltac:(lia)) as [O|O]; [exact O|lia].
    + rewrite <- Hb by exact Hi. unfold mrd. rewrite MU; [reflexivity|].
      rewrite wa_unsigned by lia. destruct (HW (A + Z.of_nat i) ltac:(lia)) as [O|O]; [exact O|lia].
  - rewrite upd_bytes_length by exact Hle. eapply wr_at_transport; eauto.
Qed.

(* the stack view survives a callee that wrote only where it left readable bytes *)
Lemma tk_stk_transport : forall W m m' lo hi,
  stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> outside W x \/ exists b, mrd rsegs m' (wa x) = Some b) ->
  stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) Hm Hw Hcase. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hwa (b & Hb)]. split; [apply Hw; exact Hwa|].
  destruct (Hcase a Ha) as [Ho | (b' & Hb')].
  - exists b. unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
  - exists b'. exact Hb'.
Qed.

Lemma tk_bytes_mrd : forall m A (bs : list byte) x, bytes_at rsegs m A bs ->
  A <= x < A + Z.of_nat (length bs) -> exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m A bs x (H1 & H2 & H) Hx. replace x with (A + Z.of_nat (Z.to_nat (x - A))) by lia.
  rewrite H by lia. apply tk_nth_some. lia.
Qed.

(* --------------------------------------------------------------------------
   5. the chunks of the fake kernel
   -------------------------------------------------------------------------- *)

Lemma tk_fld_u64_bound : forall bs off, 0 <= off -> off + 8 <= Z.of_nat (length bs) ->
  0 <= fld_u64 bs off < 2 ^ 64.
Proof.
  intros bs off H1 H2. unfold fld_u64. split; [apply tk_rdn_range|].
  apply (tk_rdn_bound bs off 8); lia.
Qed.

Lemma tk_chunk_len : forall kbs c, nlk_wf kbs -> Z.of_nat (length kbs) = NK_SIZE ->
  0 <= c < nk_n_chunks kbs ->
  Z.of_nat (length (nk_chunk kbs c)) = fld_u64 kbs (NK_CHUNK_LEN + 8 * c) /\
  fld_u64 kbs (NK_CHUNK_LEN + 8 * c) <= NL_CHUNK_MAX.
Proof.
  intros kbs c W L Hc. destruct W as (W1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W12 & _).
  specialize (W12 c Hc). unfold nk_chunk. unfold NK_CHUNK, NL_CHUNK_MAX, NK_CHUNK_LEN, NL_CHUNKS, NK_SIZE in *.
  split; [|lia]. rewrite tk_slice_length by lia. lia.
Qed.

Lemma tk_chunk_at : forall m kbs c, nlk_at m kbs -> nlk_wf kbs -> 0 <= c < nk_n_chunks kbs ->
  bytes_at rsegs m (tG + 4096 * c) (nk_chunk kbs c).
Proof.
  intros m kbs c [[HB _] L] W Hc. pose proof (tk_chunk_len kbs c W L Hc) as [E1 E2].
  destruct W as (W1 & _). unfold nk_chunk. unfold tG.
  replace (A_G_NL + 4096 * c) with (A_G_NL + (NK_CHUNK + NL_CHUNK_MAX * c)) by (unfold NK_CHUNK, NL_CHUNK_MAX; lia).
  pose proof (tk_fld_u64_bound kbs (NK_CHUNK_LEN + 8 * c)) as B.
  unfold NK_CHUNK_LEN, NL_CHUNKS, NK_SIZE, NK_CHUNK, NL_CHUNK_MAX in *.
  apply tk_bytes_slice; [exact HB | lia | lia | lia].
Qed.

Lemma tk_nth_chunks : forall kbs c, 0 <= c < nk_n_chunks kbs ->
  nth_error (nk_chunks kbs) (Z.to_nat c) = Some (nk_chunk kbs c).
Proof.
  intros kbs c Hc. unfold nk_chunks. rewrite nth_error_map, nth_error_seq.
  destruct (Nat.ltb_spec (Z.to_nat c) (Z.to_nat (nk_n_chunks kbs))) as [L|L]; [|lia].
  cbn. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma tk_nth_chunks_none : forall kbs c, 0 <= nk_n_chunks kbs <= c ->
  nth_error (nk_chunks kbs) (Z.to_nat c) = None.
Proof.
  intros kbs c Hc. apply nth_error_None. unfold nk_chunks. rewrite length_map, length_seq. lia.
Qed.

Lemma tk_chunks_length : forall kbs, length (nk_chunks kbs) = Z.to_nat (nk_n_chunks kbs).
Proof. intros kbs. unfold nk_chunks. rewrite length_map, length_seq. reflexivity. Qed.
