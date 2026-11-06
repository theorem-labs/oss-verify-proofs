(* reac-pw/fuzz_link, PLAIN build: pure and memory facts the walk of nl_talk (lib/Prog/nl_talk.v)
   uses. Nothing here mentions an instruction: the byte encodings of the loads the walk makes, the
   field views of g_nl that a callee's footprint leaves alone, and the unfolding of link_spec's
   exchange (talk_core, chunk_loop, msg_scan, attr_scan, kind_scan). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_str mk_marks.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Bytes.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Little-endian loads out of a chunk
   ========================================================================== *)

Lemma le_roundtrip : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (byte_range b) as Rb. pose proof (bytes_le_to_Z_nonneg bs) as Nn.
  rewrite lor_shiftl8_add by lia.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by ring.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace ((bv_unsigned b + 256 * bytes_le_to_Z bs) / 256) with (bytes_le_to_Z bs); [exact IH|].
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bytes_le_to_Z bs * 256 + bv_unsigned b) by ring.
    rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma slice_app_l : forall (c rest : list byte) off n, 0 <= off -> 0 <= n ->
  off + n <= Z.of_nat (length c) -> slice (c ++ rest) off n = slice c off n.
Proof.
  intros c rest off n H0 H1 H2. unfold slice.
  rewrite skipn_app. replace (Z.to_nat off - length c)%nat with 0%nat by lia. cbn [skipn].
  rewrite firstn_app. rewrite length_skipn.
  replace (Z.to_nat n - (length c - Z.to_nat off))%nat with 0%nat by lia. cbn [firstn]. apply app_nil_r.
Qed.

Lemma slice_len : forall (c : list byte) off n, 0 <= off -> 0 <= n ->
  off + n <= Z.of_nat (length c) -> length (slice c off n) = Z.to_nat n.
Proof. exact slice_length. Qed.

Lemma bytes_range : forall bs : list byte, 0 <= bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)).
Proof. intros bs. split; [apply bytes_le_to_Z_nonneg | apply bytes_le_to_Z_bound]. Qed.

Lemma rd32_range : forall c off, 0 <= off -> off + 4 <= Z.of_nat (length c) -> 0 <= rd32 c off < 2 ^ 32.
Proof.
  intros c off H0 H1. unfold rd32, rdn. pose proof (bytes_range (slice c off 4)) as R.
  rewrite slice_len in R by lia. exact R.
Qed.

Lemma rd16_range : forall c off, 0 <= off -> off + 2 <= Z.of_nat (length c) -> 0 <= rd16 c off < 2 ^ 16.
Proof.
  intros c off H0 H1. unfold rd16, rdn. pose proof (bytes_range (slice c off 2)) as R.
  rewrite slice_len in R by lia. exact R.
Qed.

Lemma slice_le4 : forall c off, 0 <= off -> off + 4 <= Z.of_nat (length c) ->
  slice c off 4 = le4 (wz (rd32 c off)).
Proof.
  intros c off H0 H1. pose proof (rd32_range c off H0 H1) as R.
  unfold le4, wz. rewrite unsigned_lit by lia. unfold rd32, rdn.
  rewrite <- (le_roundtrip (slice c off 4)) at 1. rewrite slice_len by lia. reflexivity.
Qed.

Lemma slice_le2 : forall c off, 0 <= off -> off + 2 <= Z.of_nat (length c) ->
  slice c off 2 = le2 (wz (rd16 c off)).
Proof.
  intros c off H0 H1. pose proof (rd16_range c off H0 H1) as R.
  unfold le2, wz. rewrite unsigned_lit by lia. unfold rd16, rdn.
  rewrite <- (le_roundtrip (slice c off 2)) at 1. rewrite slice_len by lia. reflexivity.
Qed.

(* the read fact the step tactic consumes, for a load of 4 or 2 bytes inside the chunk at the front
   of the receive buffer *)
Lemma read4_chunk : forall m buf c rest off, bytes_at rsegs m buf (c ++ rest) -> 0 <= off ->
  off + 4 <= Z.of_nat (length c) ->
  ov_read_bytes rsegs m (wa (buf + off)) 4 = Some (le4 (wz (rd32 c off))).
Proof.
  intros m buf c rest off B H0 H1.
  rewrite (bytes_at_read rsegs m buf (c ++ rest) off 4 B H0) by (rewrite length_app; lia).
  f_equal. rewrite <- slice_le4 by lia. rewrite <- (slice_app_l c rest off 4) by lia. reflexivity.
Qed.

Lemma read2_chunk : forall m buf c rest off, bytes_at rsegs m buf (c ++ rest) -> 0 <= off ->
  off + 2 <= Z.of_nat (length c) ->
  ov_read_bytes rsegs m (wa (buf + off)) 2 = Some (le2 (wz (rd16 c off))).
Proof.
  intros m buf c rest off B H0 H1.
  rewrite (bytes_at_read rsegs m buf (c ++ rest) off 2 B H0) by (rewrite length_app; lia).
  f_equal. rewrite <- slice_le2 by lia. rewrite <- (slice_app_l c rest off 2) by lia. reflexivity.
Qed.

(* an attribute payload is the slice after its 4-byte header *)
Lemma bytes_at_chunk_slice : forall m buf c rest off n, bytes_at rsegs m buf (c ++ rest) ->
  0 <= off -> 0 <= n -> off + n <= Z.of_nat (length c) ->
  bytes_at rsegs m (buf + off) (slice c off n).
Proof.
  intros m buf c rest off n B H0 H1 H2.
  rewrite <- (slice_app_l c rest off n) by lia.
  apply bytes_at_slice; [exact B | lia | lia | rewrite length_app; lia].
Qed.

(* the sign-extended 32-bit load of an NLMSG_ERROR code *)
Lemma sx32_rd32 : forall c off, 0 <= off -> off + 4 <= Z.of_nat (length c) ->
  sx32 (wz (rd32 c off)) = wz (rd32s c off).
Proof.
  intros c off H0 H1. pose proof (rd32_range c off H0 H1) as R.
  unfold sx32, wz, rd32s. rewrite unsigned_lit by lia. f_equal.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31).
  change (bv_modulus 32) with (2 ^ 32).
  destruct (Z.ltb_spec (rd32 c off) (2 ^ 31)) as [L|L].
  - rewrite Z.mod_small by lia. lia.
  - replace (rd32 c off + 2 ^ 31) with ((rd32 c off - 2 ^ 31) + 1 * 2 ^ 32) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* RTA_ALIGN of a 16-bit length, as `and a0, a0, s9` with s9 = 0x1fffc computes it *)
Lemma nl_align_land : forall l, 0 <= l <= 65535 -> Z.land (l + 3) 131068 = nl_align l.
Proof.
  intros l Hl. unfold nl_align.
  replace 131068 with (Z.land (Z.ones 17) (Z.lnot (Z.ones 2))) by reflexivity.
  rewrite Z.land_assoc, Z.land_ones by lia.
  rewrite Z.mod_small by (change (2 ^ 17) with 131072; lia).
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4. lia.
Qed.

Lemma nl_align_ge : forall l, 0 <= l -> l <= nl_align l <= l + 3.
Proof. intros l Hl. unfold nl_align. pose proof (Z.div_mod (l + 3) 4). pose proof (Z.mod_pos_bound (l+3) 4). lia. Qed.

(* ==========================================================================
   2. The fields of g_nl that a callee's footprint leaves alone
   ========================================================================== *)

Lemma nlk_slice_keep : forall W m m' bs bs' o n,
  nlk_at m bs -> nlk_at m' bs' -> munch W m m' ->
  disjoint_from W (A_G_NL + o) n -> 0 <= o -> 0 <= n -> o + n <= NK_SIZE ->
  slice bs' o n = slice bs o n.
Proof.
  intros W m m' bs bs' o n [[B _] L] [[B' _] L'] MU D H0 H1 H2.
  pose proof (bytes_at_slice m A_G_NL bs o n B H0 H1 ltac:(lia)) as S.
  pose proof (bytes_at_slice m' A_G_NL bs' o n B' H0 H1 ltac:(lia)) as S'.
  apply (bytes_at_transport rsegs W m m') in S;
    [| exact MU | rewrite slice_length by lia; rewrite Z2Nat.id by lia; exact D].
  symmetry. apply (bytes_at_unique m' (A_G_NL + o)); [exact S | exact S' |].
  rewrite !slice_length by lia. reflexivity.
Qed.

Lemma fld_keep : forall W m m' bs bs' off k,
  nlk_at m bs -> nlk_at m' bs' -> munch W m m' ->
  disjoint_from W (A_G_NL + off) k -> 0 <= off -> 0 <= k -> off + k <= NK_SIZE ->
  rdn bs' off k = rdn bs off k.
Proof.
  intros W m m' bs bs' off k H1 H2 MU D H3 H4 H5. unfold rdn.
  rewrite (nlk_slice_keep W m m' bs bs' off k H1 H2 MU D H3 H4 H5). reflexivity.
Qed.

Lemma slice_slice : forall (bs : list byte) a k o n, 0 <= a -> 0 <= k -> 0 <= o -> 0 <= n ->
  a <= o -> o + n <= a + k -> slice bs o n = slice (slice bs a k) (o - a) n.
Proof.
  intros bs a k o n Ha Hk Ho Hn H1 H2. unfold slice.
  rewrite skipn_firstn_comm, skipn_skipn, firstn_firstn.
  replace (Z.to_nat (o - a) + Z.to_nat a)%nat with (Z.to_nat o) by lia.
  replace (Nat.min (Z.to_nat n) (Z.to_nat k - Z.to_nat (o - a))) with (Z.to_nat n) by lia.
  reflexivity.
Qed.

(* two byte lists that agree on [a, a+k) agree on every slice inside it *)
Lemma slice_sub_eq : forall (bs bs' : list byte) a k o n, 0 <= a -> 0 <= k -> 0 <= o -> 0 <= n ->
  a <= o -> o + n <= a + k -> slice bs' a k = slice bs a k -> slice bs' o n = slice bs o n.
Proof.
  intros bs bs' a k o n Ha Hk Ho Hn H1 H2 E.
  rewrite (slice_slice bs' a k o n), (slice_slice bs a k o n) by lia. rewrite E. reflexivity.
Qed.

Lemma rdn_sub_eq : forall (bs bs' : list byte) a k o n, 0 <= a -> 0 <= k -> 0 <= o -> 0 <= n ->
  a <= o -> o + n <= a + k -> slice bs' a k = slice bs a k -> rdn bs' o n = rdn bs o n.
Proof.
  intros bs bs' a k o n Ha Hk Ho Hn H1 H2 E. unfold rdn.
  rewrite (slice_sub_eq bs bs' a k o n Ha Hk Ho Hn H1 H2 E). reflexivity.
Qed.

(* the chunk queue depends only on [0, NK_NEXT) *)
Lemma nk_chunks_keep : forall bs bs', nlk_wf bs ->
  slice bs' 0 NK_NEXT = slice bs 0 NK_NEXT -> nk_chunks bs' = nk_chunks bs.
Proof.
  intros bs bs' WF E. destruct WF as (Hn & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL & _).
  unfold NL_CHUNKS, NL_CHUNK_MAX in *.
  assert (EN : nk_n_chunks bs' = nk_n_chunks bs).
  { unfold nk_n_chunks, fld_u32. apply (rdn_sub_eq bs bs' 0 NK_NEXT); unfold NK_N_CHUNKS, NK_NEXT; lia || exact E. }
  unfold nk_chunks. rewrite EN. apply map_ext_in. intros i Hi. apply in_seq in Hi.
  assert (Hi' : 0 <= Z.of_nat i < nk_n_chunks bs) by lia.
  assert (EL : fld_u64 bs' (NK_CHUNK_LEN + 8 * Z.of_nat i) = fld_u64 bs (NK_CHUNK_LEN + 8 * Z.of_nat i)).
  { unfold fld_u64. apply (rdn_sub_eq bs bs' 0 NK_NEXT); unfold NK_CHUNK_LEN, NK_NEXT; lia || exact E. }
  specialize (HL (Z.of_nat i) Hi').
  unfold nk_chunk. rewrite EL.
  apply (slice_sub_eq bs bs' 0 NK_NEXT); unfold NK_CHUNK, NK_NEXT, NL_CHUNK_MAX in *; lia || exact E.
Qed.

(* the request ring depends only on [NK_SENT, NK_N_SENT + 4) *)
Lemma nk_sent_keep : forall bs bs', nlk_wf bs ->
  slice bs' NK_SENT (NK_N_SENT + 4 - NK_SENT) = slice bs NK_SENT (NK_N_SENT + 4 - NK_SENT) ->
  nk_sent bs' = nk_sent bs.
Proof.
  intros bs bs' WF E. destruct WF as (_ & _ & Hn & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL).
  unfold NL_SENT_MAX, NL_SENT_LEN in *.
  assert (EN : nk_n_sent bs' = nk_n_sent bs).
  { unfold nk_n_sent, fld_u32.
    apply (rdn_sub_eq bs bs' NK_SENT (NK_N_SENT + 4 - NK_SENT)); unfold NK_SENT, NK_N_SENT; lia || exact E. }
  unfold nk_sent. rewrite EN. apply map_ext_in. intros i Hi. apply in_seq in Hi.
  assert (Hi' : 0 <= Z.of_nat i < nk_n_sent bs) by lia.
  assert (EL : fld_u64 bs' (NK_SENT_LEN + 8 * Z.of_nat i) = fld_u64 bs (NK_SENT_LEN + 8 * Z.of_nat i)).
  { unfold fld_u64.
    apply (rdn_sub_eq bs bs' NK_SENT (NK_N_SENT + 4 - NK_SENT)); unfold NK_SENT_LEN, NK_SENT, NK_N_SENT; lia || exact E. }
  specialize (HL (Z.of_nat i) Hi').
  unfold nk_sent_one. rewrite EL.
  apply (slice_sub_eq bs bs' NK_SENT (NK_N_SENT + 4 - NK_SENT));
    unfold NK_SENT, NK_N_SENT, NL_SENT_LEN in *; lia || exact E.
Qed.

Lemma nk_sent_len : forall bs, nlk_wf bs -> nk_n_sent bs = Z.of_nat (length (nk_sent bs)).
Proof.
  intros bs WF. destruct WF as (_ & _ & Hn & _). unfold nk_sent. rewrite length_map, length_seq. lia.
Qed.

Lemma nk_chunks_length : forall bs, nlk_wf bs -> Z.of_nat (length (nk_chunks bs)) = nk_n_chunks bs.
Proof.
  intros bs WF. destruct WF as (Hn & _). unfold nk_chunks. rewrite length_map, length_seq. lia.
Qed.

Lemma nk_chunks_nth : forall bs i, 0 <= i < nk_n_chunks bs ->
  nth_error (nk_chunks bs) (Z.to_nat i) = Some (nk_chunk bs i).
Proof.
  intros bs i Hi. unfold nk_chunks. rewrite nth_error_map, nth_error_seq.
  replace (Z.to_nat i <? Z.to_nat (nk_n_chunks bs))%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  cbn. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma nk_chunks_none : forall bs i, 0 <= nk_n_chunks bs -> nk_n_chunks bs <= i ->
  nth_error (nk_chunks bs) (Z.to_nat i) = None.
Proof.
  intros bs i H0 Hi. apply nth_error_None. unfold nk_chunks. rewrite length_map, length_seq. lia.
Qed.

Lemma nk_chunk_len : forall bs i, nlk_wf bs -> 0 <= i < nk_n_chunks bs ->
  (length (nk_chunk bs i) <= 4096)%nat.
Proof.
  intros bs i WF Hi. destruct WF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL & _).
  specialize (HL i Hi). unfold NL_CHUNK_MAX in HL. unfold nk_chunk, slice. rewrite length_firstn. lia.
Qed.

(* ==========================================================================
   3. The exchange, one case at a time
   ========================================================================== *)

Lemma talk_sock : forall K, k_sock K <> 0 ->
  talk_rc_lib K = - k_sock K /\ talk_attrs K = no_attrs /\
  talk_after K = Kst (k_chunks K) (k_next K) (k_end K) 0 (k_send K) /\ talk_owes K = false.
Proof.
  intros K H. unfold talk_rc_lib, talk_attrs, talk_after, talk_core, talk_owes.
  replace (k_sock K =? 0) with false by (symmetry; apply Z.eqb_neq; exact H). cbn. repeat split.
Qed.

Lemma talk_send : forall K, k_sock K = 0 -> k_send K <> 0 ->
  talk_rc_lib K = - k_send K /\ talk_attrs K = no_attrs /\
  talk_after K = Kst (k_chunks K) (k_next K) (k_end K) 0 0 /\ talk_owes K = false.
Proof.
  intros K H1 H2. unfold talk_rc_lib, talk_attrs, talk_after, talk_core, talk_owes.
  rewrite H1. replace (k_send K =? 0) with false by (symmetry; apply Z.eqb_neq; exact H2). cbn. repeat split.
Qed.

(* the answer of a chunk walk, as the exchange turns it into a code and attributes *)
Definition nlv_rc (v : nlv) (e : Z) : Z :=
  match v with NlNone => - e | NlShort => - E_IO | NlErr code => code | NlLink _ => 0 end.
Definition nlv_attrs (v : nlv) : attrs :=
  match v with NlLink a => a | _ => no_attrs end.

Lemma talk_loop : forall K, k_sock K = 0 -> k_send K = 0 ->
  let r := chunk_loop (S (length (k_chunks K))) (k_chunks K) (k_next K) in
  talk_rc_lib K = nlv_rc (fst r) (k_end K) /\ talk_attrs K = nlv_attrs (fst r) /\
  talk_after K = Kst (k_chunks K) (snd r) (k_end K) 0 0 /\ talk_owes K = true.
Proof.
  intros K H1 H2 r. unfold talk_rc_lib, talk_attrs, talk_after, talk_core, talk_owes.
  rewrite H1, H2. cbn [Z.eqb negb andb]. fold r. destruct r as [v j]. cbn [fst snd].
  destruct v; cbn; repeat split.
Qed.

Lemma chunk_loop_step : forall f cs i c, nth_error cs i = Some c -> chunk_walk c = NlNone ->
  chunk_loop (S f) cs i = chunk_loop f cs (S i).
Proof. intros f cs i c E W. cbn [chunk_loop]. rewrite E, W. reflexivity. Qed.

Lemma chunk_loop_hit : forall f cs i c, nth_error cs i = Some c -> chunk_walk c <> NlNone ->
  chunk_loop (S f) cs i = (chunk_walk c, S i).
Proof. intros f cs i c E W. cbn [chunk_loop]. rewrite E. destruct (chunk_walk c); [contradiction|reflexivity..]. Qed.

Lemma chunk_loop_end : forall f cs i, nth_error cs i = None -> chunk_loop f cs i = (NlNone, i).
Proof. intros [|f] cs i E; cbn [chunk_loop]; [reflexivity|]. rewrite E. reflexivity. Qed.
