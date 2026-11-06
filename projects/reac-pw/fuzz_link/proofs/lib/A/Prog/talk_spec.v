(* talk on image A (lib/A/Prog/talk_c.v, fuzz_link.asan 0x8763c): the facts of link_spec.v that the pieces of its
   walk use. No instruction runs here and no image is named: the memory lemmas (sections 3, 7, 8) take the segment
   list as a variable and speak only of mbyte, val_mem, writable_at and link_amem's views.
   1. talk_core's three arms: the socket errno (+0x6c), the send errno (+0x9c), the chunk loop (+0x16c); tw_rc, tw_at,
      msg_ret; the fields of md_kstate.
   2. the Post's arithmetic: norm_rc of a code, -E_IO, RC_FAILS = 0xf4240, the negw of an errno below 2 ^ 31.
   3. the chunks of g_nl: chunk c is the bytes [4096 c, 4096 c + chunk_len[c]) of the g_nl list, chunk_len[c] <= 4096,
      c < n_chunks <= 64; a read of the chunk is a read of the g_nl list, and a val_mem at its address.
   4. reads as the little-endian value of the bytes (the lbu / lb joins of the code), the align-4 steps.
   5. one step of chunk_loop, msg_scan, attr_scan and kind_scan at a position.
   6. fuel: the code loops while the spec counts fuel; with more fuel than bytes left (chunks left) the result does
      not depend on the fuel.
   7. take_text: the NUL scan (+0x3b4 / +0x490), the clamp to cap - 1 (+0x55c / +0x4c8), the payload as g_nl bytes,
      and the C string the copy and the NUL store leave (acstr_cut).
   8. the model block: bput (the list after a store), the fields after each store talk makes (+0x7c, +0xac, +0x1bc,
      checked_memcpy +0x12c, +0x150, +0x168), model_wf kept, owe; amodel_put / amodel_store (the list of the memory
      after a store).
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK04 YP0e YP09 YI04 YG0f YG0n YA0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_amem LinkWalk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ==========================================================================
   1. talk_core's three arms
   ========================================================================== *)

(* the raw code and the attributes of a chunk loop answer v, with end errno e *)
Definition tw_rc (v : nlv) (e : Z) : Z :=
  match v with NlNone => - e | NlShort => - E_IO | NlErr c => c | NlLink _ => 0 end.
Definition tw_at (v : nlv) : attrs := match v with NlLink a => a | _ => no_attrs end.

(* the code a chunk answers when it stops the exchange without filling the buffers: an NLMSG_ERROR too short for
   its code (+0x2b0), an NLMSG_ERROR (+0x63c), an RTM_NEWLINK too short for an attribute (+0x2a0) *)
Definition msg_ret (v : nlv) (rc : Z) : Prop :=
  (v = NlShort /\ rc = - E_IO) \/ (exists code, v = NlErr code /\ rc = norm_rc code) \/
  (v = NlLink no_attrs /\ rc = 0).

Lemma msg_ret_some : forall v rc, msg_ret v rc -> v <> NlNone.
Proof. unfold msg_ret. intros v rc [[-> _] | [[code [-> _]] | [-> _]]]; discriminate. Qed.

Lemma tw_kstate : forall mbs kbs,
  k_chunks (md_kstate mbs kbs) = nk_chunks kbs /\ k_next (md_kstate mbs kbs) = Z.to_nat (md_next mbs) /\
  k_end (md_kstate mbs kbs) = nk_end_errno kbs /\ k_sock (md_kstate mbs kbs) = md_socket_errno mbs /\
  k_send (md_kstate mbs kbs) = md_send_errno mbs.
Proof. intros mbs kbs. exact (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))). Qed.

(* the socket arm: +0x6c socket_errno <> 0 *)
Lemma tw_core_sock : forall K, k_sock K <> 0 ->
  talk_rc_model K = norm_rc (- k_sock K) /\ talk_attrs K = no_attrs /\
  talk_after K = Kst (k_chunks K) (k_next K) (k_end K) 0 (k_send K) /\ talk_owes K = false.
Proof.
  intros K H. unfold talk_rc_model, talk_rc_lib, talk_attrs, talk_after, talk_owes, talk_core.
  destruct (Z.eqb_spec (k_sock K) 0); [contradiction|]. cbn. repeat split.
Qed.

(* the send arm: +0x9c send_errno <> 0 after socket_errno = 0 *)
Lemma tw_core_send : forall K, k_sock K = 0 -> k_send K <> 0 ->
  talk_rc_model K = norm_rc (- k_send K) /\ talk_attrs K = no_attrs /\
  talk_after K = Kst (k_chunks K) (k_next K) (k_end K) 0 0 /\ talk_owes K = false.
Proof.
  intros K H1 H2. unfold talk_rc_model, talk_rc_lib, talk_attrs, talk_after, talk_owes, talk_core.
  rewrite H1. destruct (Z.eqb_spec (k_send K) 0); [contradiction|]. cbn. repeat split.
Qed.

(* the chunk arm: both errnos 0 *)
Lemma tw_core_main : forall K v j, k_sock K = 0 -> k_send K = 0 ->
  chunk_loop (S (length (k_chunks K))) (k_chunks K) (k_next K) = (v, j) ->
  talk_after K = Kst (k_chunks K) j (k_end K) 0 0 /\ talk_owes K = true /\
  talk_attrs K = tw_at v /\ talk_rc_model K = norm_rc (tw_rc v (k_end K)).
Proof.
  intros K v j H1 H2 H3. unfold talk_rc_model, talk_rc_lib, talk_attrs, talk_after, talk_owes, talk_core.
  rewrite H1, H2. cbn [negb Z.eqb andb]. rewrite H3. destruct v; cbn; repeat split.
Qed.

(* the cursor the chunk loop leaves is at most the number of chunks (or where it started) *)
Lemma tw_cl_bound : forall f cs i v j, chunk_loop f cs i = (v, j) -> (j <= Nat.max i (length cs))%nat.
Proof.
  induction f as [|f IH]; intros cs i v j H; cbn [chunk_loop] in H.
  - inversion H; subst; lia.
  - destruct (nth_error cs i) as [c|] eqn:E.
    + assert (L : (i < length cs)%nat) by (apply nth_error_Some; rewrite E; discriminate).
      destruct (chunk_walk c); try (inversion H; subst; lia).
      specialize (IH cs (S i) v j H). lia.
    + inversion H; subst; lia.
Qed.

(* ==========================================================================
   2. the Post's arithmetic
   ========================================================================== *)

Lemma tw_rc_fails : RC_FAILS = 0xf4240.
Proof. reflexivity. Qed.

Lemma tw_eio : - E_IO = -5.
Proof. reflexivity. Qed.

(* +0x63c..+0x644: a positive NLMSG_ERROR code answers 0xf4240 *)
Lemma tw_norm_pos : forall rc, 0 < rc -> norm_rc rc = 0xf4240.
Proof. intros rc H. unfold norm_rc. destruct (Z.ltb_spec 0 rc); [reflexivity | lia]. Qed.

Lemma tw_norm_nonpos : forall rc, rc <= 0 -> norm_rc rc = rc.
Proof. intros rc H. unfold norm_rc. destruct (Z.ltb_spec 0 rc); [lia | reflexivity]. Qed.

(* the socket, send and end errnos: -e with e >= 0 is its own norm_rc *)
Lemma tw_norm_neg : forall e, 0 <= e -> norm_rc (- e) = - e.
Proof. intros e H. apply tw_norm_nonpos. lia. Qed.

Lemma tw_norm_eio : norm_rc (- E_IO) = -5.
Proof. reflexivity. Qed.

(* negw on an errno e, 0 <= e < 2 ^ 31 (the lw that loaded it sign-extends to e): the 32-bit signed value of 0 - e *)
Lemma tw_negw : forall e, 0 <= e < 2 ^ 31 -> bv_swrap 32 (0 - e) = - e.
Proof. intros e He. rewrite swrap32_id by lia. lia. Qed.

(* the norm_rc of an NLMSG_ERROR code, by the sign the +0x63c blez tests *)
Lemma tw_norm_code : forall code, norm_rc code = if code <=? 0 then code else 0xf4240.
Proof.
  intros code. unfold norm_rc. destruct (Z.leb_spec code 0); destruct (Z.ltb_spec 0 code); first [reflexivity | lia].
Qed.

(* ==========================================================================
   3. the chunks of g_nl
   ========================================================================== *)

Lemma tw_nth_map_seq : forall {A : Type} (f : nat -> A) n s i, (i < n)%nat ->
  nth_error (map f (seq s n)) i = Some (f (s + i)%nat).
Proof.
  intros A f. induction n as [|n IH]; intros s i Hi; [lia|].
  destruct i as [|i]; cbn [seq map nth_error].
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite (IH (S s) i ltac:(lia)). f_equal. f_equal. lia.
Qed.

Lemma tw_nth_map_seq_none : forall {A : Type} (f : nat -> A) n s i, (n <= i)%nat ->
  nth_error (map f (seq s n)) i = None.
Proof. intros A f n s i H. apply nth_error_None. rewrite length_map, length_seq. exact H. Qed.

Lemma tw_nth_firstn_ge : forall (l : list byte) n k, (n <= k)%nat -> nth_error (firstn n l) k = None.
Proof. intros l n k H. apply nth_error_None. rewrite length_firstn. lia. Qed.

Lemma nk_chunks_length : forall kbs, length (nk_chunks kbs) = Z.to_nat (nk_n_chunks kbs).
Proof. intros kbs. unfold nk_chunks. rewrite length_map, length_seq. reflexivity. Qed.

Lemma nk_chunks_nth : forall kbs c, 0 <= c < nk_n_chunks kbs ->
  nth_error (nk_chunks kbs) (Z.to_nat c) = Some (nk_chunk kbs c).
Proof.
  intros kbs c Hc. unfold nk_chunks. rewrite tw_nth_map_seq by lia.
  rewrite Nat.add_0_l, Z2Nat.id by lia. reflexivity.
Qed.

Lemma nk_chunks_none : forall kbs c, 0 <= nk_n_chunks kbs <= c ->
  nth_error (nk_chunks kbs) (Z.to_nat c) = None.
Proof. intros kbs c Hc. unfold nk_chunks. apply tw_nth_map_seq_none. lia. Qed.

(* chunk c's length is chunk_len[c] <= 4096, and n_chunks <= 64 (nlk_wf) *)
Lemma nk_chunk_len : forall kbs c, nlk_wf kbs -> Z.of_nat (length kbs) = NK_SIZE -> 0 <= c < nk_n_chunks kbs ->
  Z.of_nat (length (nk_chunk kbs c)) = fld_u64 kbs (NK_CHUNK_LEN + 8 * c) /\
  0 <= fld_u64 kbs (NK_CHUNK_LEN + 8 * c) <= NL_CHUNK_MAX /\ 0 <= nk_n_chunks kbs <= NL_CHUNKS.
Proof.
  intros kbs c W L Hc. destruct W as (W1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W12 & _).
  pose proof (W12 c Hc) as Wc. unfold nk_chunk.
  unfold NK_CHUNK, NL_CHUNK_MAX, NL_CHUNKS, NK_SIZE in *.
  rewrite lw_slice_length by lia. split; [lia|]. split; [exact Wc | exact W1].
Qed.

(* byte i of chunk c is byte 4096 c + i of the g_nl list *)
Lemma nk_chunk_nth : forall kbs c i, 0 <= c -> 0 <= i < fld_u64 kbs (NK_CHUNK_LEN + 8 * c) ->
  nth_error (nk_chunk kbs c) (Z.to_nat i) = nth_error kbs (Z.to_nat (4096 * c + i)).
Proof.
  intros kbs c i Hc Hi. unfold nk_chunk. rewrite lw_slice_nth by (unfold NK_CHUNK, NL_CHUNK_MAX; lia).
  f_equal. unfold NK_CHUNK, NL_CHUNK_MAX. lia.
Qed.

Lemma tw_slice_slice : forall (bs : list byte) s L off n, 0 <= s -> 0 <= off -> 0 <= n -> off + n <= L ->
  slice (slice bs s L) off n = slice bs (s + off) n.
Proof.
  intros bs s L off n Hs Ho Hn HL. apply nth_error_ext. intros k.
  destruct (Nat.ltb_spec k (Z.to_nat n)) as [H|H].
  - rewrite (lw_slice_nth (slice bs s L) off n k Ho H), (lw_slice_nth bs (s + off) n k ltac:(lia) H).
    rewrite (lw_slice_nth bs s L (Z.to_nat off + k) Hs ltac:(lia)). f_equal. lia.
  - unfold slice. rewrite !tw_nth_firstn_ge by lia. reflexivity.
Qed.

(* a read of chunk c is a read of the g_nl list *)
Lemma nk_chunk_rdn : forall kbs c off n, 0 <= c -> 0 <= off -> 0 <= n ->
  off + n <= fld_u64 kbs (NK_CHUNK_LEN + 8 * c) ->
  rdn (nk_chunk kbs c) off n = rdn kbs (4096 * c + off) n.
Proof.
  intros kbs c off n Hc Ho Hn H. unfold rdn, nk_chunk.
  rewrite tw_slice_slice by (unfold NK_CHUNK, NL_CHUNK_MAX; lia).
  replace (NK_CHUNK + NL_CHUNK_MAX * c + off) with (4096 * c + off) by (unfold NK_CHUNK, NL_CHUNK_MAX; lia).
  reflexivity.
Qed.

Lemma nk_chunk_rd32 : forall kbs c off, 0 <= c -> 0 <= off -> off + 4 <= fld_u64 kbs (NK_CHUNK_LEN + 8 * c) ->
  rd32 (nk_chunk kbs c) off = rdn kbs (4096 * c + off) 4.
Proof. intros kbs c off Hc Ho H. unfold rd32. apply nk_chunk_rdn; lia. Qed.

Lemma nk_chunk_rd16 : forall kbs c off, 0 <= c -> 0 <= off -> off + 2 <= fld_u64 kbs (NK_CHUNK_LEN + 8 * c) ->
  rd16 (nk_chunk kbs c) off = rdn kbs (4096 * c + off) 2.
Proof. intros kbs c off Hc Ho H. unfold rd16. apply nk_chunk_rdn; lia. Qed.

Lemma nk_chunk_rd32s : forall kbs c off, 0 <= c -> 0 <= off -> off + 4 <= fld_u64 kbs (NK_CHUNK_LEN + 8 * c) ->
  rd32s (nk_chunk kbs c) off =
  (let v := rdn kbs (4096 * c + off) 4 in if v <? 2 ^ 31 then v else v - 2 ^ 32).
Proof. intros kbs c off Hc Ho H. unfold rd32s. rewrite nk_chunk_rd32 by lia. reflexivity. Qed.

Section g.
Variable segs : list Segment.

(* a read of chunk c as the val_mem at g + 4096 c + off the symbolic state takes *)
Lemma anlk_chunk_val : forall m g kbs c off (n : nat),
  anlk_at segs m g kbs -> nlk_wf kbs -> 0 <= c < nk_n_chunks kbs -> 0 <= off ->
  off + Z.of_nat n <= fld_u64 kbs (NK_CHUNK_LEN + 8 * c) ->
  val_mem segs m (g + 4096 * c + off) n (rdn (nk_chunk kbs c) off (Z.of_nat n)).
Proof.
  intros m g kbs c off n [[Hab Hw] HL] W Hc Ho Hn.
  pose proof (nk_chunk_len kbs c W HL Hc) as (_ & Hl & Hnc).
  rewrite nk_chunk_rdn by lia.
  replace (g + 4096 * c + off) with (g + (4096 * c + off)) by lia.
  apply val_mem_of_abytes; [exact Hab | lia |].
  unfold NL_CHUNK_MAX, NL_CHUNKS, NK_SIZE in *. lia.
Qed.

(* byte i of chunk c in memory *)
Lemma anlk_chunk_byte : forall m g kbs c i,
  anlk_at segs m g kbs -> nlk_wf kbs -> 0 <= c < nk_n_chunks kbs ->
  0 <= i < fld_u64 kbs (NK_CHUNK_LEN + 8 * c) ->
  mbyte segs m (g + 4096 * c + i) = nth_error (nk_chunk kbs c) (Z.to_nat i).
Proof.
  intros m g kbs c i [[(_ & _ & Hb) Hw] HL] W Hc Hi.
  pose proof (nk_chunk_len kbs c W HL Hc) as (_ & Hl & Hnc).
  rewrite nk_chunk_nth by lia.
  replace (g + 4096 * c + i) with (g + Z.of_nat (Z.to_nat (4096 * c + i))) by lia.
  apply Hb. unfold NL_CHUNK_MAX, NL_CHUNKS, NK_SIZE in *. lia.
Qed.
End g.

(* ==========================================================================
   4. reads as the little-endian value of bytes
   ========================================================================== *)

Lemma tw_byte_range : forall b : byte, 0 <= bz b < 256.
Proof. intros b. unfold bz. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. exact R. Qed.

Lemma tw_rdn_range : forall c off n, 0 <= off -> 0 <= n -> off + n <= Z.of_nat (length c) ->
  0 <= rdn c off n < 2 ^ (8 * n).
Proof.
  intros c off n H1 H2 H3. unfold rdn. split; [apply bytes_le_to_Z_nonneg|].
  pose proof (bytes_le_to_Z_bound (slice c off n)) as B.
  rewrite lw_slice_length in B by lia. rewrite Z2Nat.id in B by lia. exact B.
Qed.

Lemma tw_rd16_range : forall c off, 0 <= off -> off + 2 <= Z.of_nat (length c) -> 0 <= rd16 c off < 2 ^ 16.
Proof. intros c off H1 H2. unfold rd16. exact (tw_rdn_range c off 2 H1 ltac:(lia) H2). Qed.

Lemma tw_rd32_range : forall c off, 0 <= off -> off + 4 <= Z.of_nat (length c) -> 0 <= rd32 c off < 2 ^ 32.
Proof. intros c off H1 H2. unfold rd32. exact (tw_rdn_range c off 4 H1 ltac:(lia) H2). Qed.

Lemma tw_rd32s_range : forall c off, 0 <= off -> off + 4 <= Z.of_nat (length c) ->
  - 2 ^ 31 <= rd32s c off < 2 ^ 31.
Proof.
  intros c off H1 H2. pose proof (tw_rd32_range c off H1 H2) as R.
  unfold rd32s. cbv zeta. destruct (Z.ltb_spec (rd32 c off) (2 ^ 31)); lia.
Qed.

(* the n bytes of c from off, named *)
Lemma tw_skipn_nth : forall (c : list byte) off k b, 0 <= off ->
  nth_error c (Z.to_nat (off + Z.of_nat k)) = Some b -> nth_error (skipn (Z.to_nat off) c) k = Some b.
Proof.
  intros c off k b Ho H. rewrite lw_nth_error_skipn.
  replace (Z.to_nat off + k)%nat with (Z.to_nat (off + Z.of_nat k)) by lia. exact H.
Qed.

Lemma tw_slice2 : forall (c : list byte) off b0 b1, 0 <= off ->
  nth_error c (Z.to_nat off) = Some b0 -> nth_error c (Z.to_nat (off + 1)) = Some b1 ->
  slice c off 2 = [b0; b1].
Proof.
  intros c off b0 b1 Ho E0 E1.
  pose proof (tw_skipn_nth c off 0 b0 Ho ltac:(rewrite Z.add_0_r; exact E0)) as F0.
  pose proof (tw_skipn_nth c off 1 b1 Ho E1) as F1.
  unfold slice. change (Z.to_nat 2) with 2%nat.
  remember (skipn (Z.to_nat off) c) as sk eqn:Esk. clear Esk.
  destruct sk as [|x0 [|x1 r]]; cbn [nth_error] in F0, F1; try discriminate.
  injection F0 as <-. injection F1 as <-. reflexivity.
Qed.

Lemma tw_slice4 : forall (c : list byte) off b0 b1 b2 b3, 0 <= off ->
  nth_error c (Z.to_nat off) = Some b0 -> nth_error c (Z.to_nat (off + 1)) = Some b1 ->
  nth_error c (Z.to_nat (off + 2)) = Some b2 -> nth_error c (Z.to_nat (off + 3)) = Some b3 ->
  slice c off 4 = [b0; b1; b2; b3].
Proof.
  intros c off b0 b1 b2 b3 Ho E0 E1 E2 E3.
  pose proof (tw_skipn_nth c off 0 b0 Ho ltac:(rewrite Z.add_0_r; exact E0)) as F0.
  pose proof (tw_skipn_nth c off 1 b1 Ho E1) as F1.
  pose proof (tw_skipn_nth c off 2 b2 Ho E2) as F2.
  pose proof (tw_skipn_nth c off 3 b3 Ho E3) as F3.
  unfold slice. change (Z.to_nat 4) with 4%nat.
  remember (skipn (Z.to_nat off) c) as sk eqn:Esk. clear Esk.
  destruct sk as [|x0 [|x1 [|x2 [|x3 r]]]]; cbn [nth_error] in F0, F1, F2, F3; try discriminate.
  injection F0 as <-. injection F1 as <-. injection F2 as <-. injection F3 as <-. reflexivity.
Qed.

(* two bytes joined (lbu, lbu, slli 8, or; or one lhu) *)
Lemma tw_rd16_bytes : forall c off b0 b1, 0 <= off ->
  nth_error c (Z.to_nat off) = Some b0 -> nth_error c (Z.to_nat (off + 1)) = Some b1 ->
  rd16 c off = bz b0 + 256 * bz b1.
Proof.
  intros c off b0 b1 Ho E0 E1. unfold rd16, rdn. rewrite (tw_slice2 c off b0 b1 Ho E0 E1).
  rewrite !bytes_le_to_Z_cons. cbn [bytes_le_to_Z]. unfold bz. lia.
Qed.

(* four bytes joined (one lwu) *)
Lemma tw_rd32_bytes : forall c off b0 b1 b2 b3, 0 <= off ->
  nth_error c (Z.to_nat off) = Some b0 -> nth_error c (Z.to_nat (off + 1)) = Some b1 ->
  nth_error c (Z.to_nat (off + 2)) = Some b2 -> nth_error c (Z.to_nat (off + 3)) = Some b3 ->
  rd32 c off = bz b0 + 256 * bz b1 + 65536 * bz b2 + 16777216 * bz b3.
Proof.
  intros c off b0 b1 b2 b3 Ho E0 E1 E2 E3. unfold rd32, rdn.
  rewrite (tw_slice4 c off b0 b1 b2 b3 Ho E0 E1 E2 E3).
  rewrite !bytes_le_to_Z_cons. cbn [bytes_le_to_Z]. unfold bz. lia.
Qed.

(* the value of a byte loaded by lb *)
Definition sbz (b : byte) : Z := if bz b <? 128 then bz b else bz b - 256.

Lemma sbz_signed : forall b : byte, bv_signed b = sbz b.
Proof.
  intros b. pose proof (tw_byte_range b) as R. unfold sbz, bz in *.
  unfold bv_signed, bv_swrap, bv_wrap.
  replace (bv_half_modulus 8) with 128 by reflexivity. replace (bv_modulus 8) with 256 by reflexivity.
  destruct (Z.ltb_spec (bv_unsigned b) 128) as [H|H].
  - rewrite Z.mod_small by lia. lia.
  - rewrite <- (Z.mod_add (bv_unsigned b + 128) (-1) 256) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma sbz_range : forall b : byte, -128 <= sbz b < 128.
Proof. intros b. pose proof (tw_byte_range b). unfold sbz. destruct (Z.ltb_spec (bz b) 128); lia. Qed.

(* the int32 NLMSG_ERROR code (+0x614..+0x638: lbu, lbu, lbu, lb) *)
Lemma tw_rd32s_bytes : forall c off b0 b1 b2 b3, 0 <= off ->
  nth_error c (Z.to_nat off) = Some b0 -> nth_error c (Z.to_nat (off + 1)) = Some b1 ->
  nth_error c (Z.to_nat (off + 2)) = Some b2 -> nth_error c (Z.to_nat (off + 3)) = Some b3 ->
  rd32s c off = bz b0 + 256 * bz b1 + 65536 * bz b2 + 16777216 * sbz b3.
Proof.
  intros c off b0 b1 b2 b3 Ho E0 E1 E2 E3. unfold rd32s. cbv zeta.
  rewrite (tw_rd32_bytes c off b0 b1 b2 b3 Ho E0 E1 E2 E3).
  pose proof (tw_byte_range b0). pose proof (tw_byte_range b1).
  pose proof (tw_byte_range b2). pose proof (tw_byte_range b3).
  unfold sbz. destruct (Z.ltb_spec (bz b3) 128) as [Hs|Hs].
  - rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
  - rewrite (proj2 (Z.ltb_ge _ _)) by lia. lia.
Qed.

(* `or` of two values whose bits do not meet *)
Lemma tw_lor_add : forall a b k, 0 <= k -> 0 <= a -> 0 <= b < 2 ^ k -> a mod 2 ^ k = 0 -> Z.lor a b = a + b.
Proof.
  intros a b k Hk Ha Hb Hm.
  assert (L : Z.land a b = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i k) as [Lt|Ge].
    - rewrite <- (Z.mod_pow2_bits_low a k i Lt). rewrite Hm, Z.bits_0. reflexivity.
    - rewrite <- (Z.mod_small b (2 ^ k)) by lia. rewrite (Z.mod_pow2_bits_high b k i) by lia.
      apply andb_false_r. }
  rewrite <- Z.lxor_lor by exact L. symmetry. apply Z.add_nocarry_lxor. exact L.
Qed.

(* lbu x, lbu y, slli x 8, or *)
Lemma tw_join2 : forall x y, 0 <= x < 256 -> 0 <= y < 256 -> Z.lor (Z.shiftl x 8) y = y + 256 * x.
Proof.
  intros x y Hx Hy. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  rewrite (tw_lor_add (x * 256) y 8) by (first [lia | change (2 ^ 8) with 256; lia | apply Z.mod_mul; lia]).
  lia.
Qed.

(* the code's join of the int32 at +0x620..+0x638, every value as its unsigned 64-bit word:
   ((s3 << 24) | (b2 << 16)) | ((b1 << 8) | b0), s3 the lb-loaded top byte *)
Lemma tw_join4 : forall b0 b1 b2 s3, 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> -128 <= s3 < 128 ->
  Z.lor (Z.lor ((s3 * 2 ^ 24) mod 2 ^ 64) (b2 * 2 ^ 16)) (Z.lor (b1 * 2 ^ 8) b0) =
  (b0 + 256 * b1 + 65536 * b2 + 16777216 * s3) mod 2 ^ 64.
Proof.
  intros b0 b1 b2 s3 H0 H1 H2 H3.
  change (2 ^ 8) with 256. change (2 ^ 16) with 65536. change (2 ^ 24) with 16777216.
  rewrite (tw_lor_add (b1 * 256) b0 8) by (first [lia | change (2 ^ 8) with 256; lia | apply Z.mod_mul; lia]).
  assert (EA : exists q, (s3 * 16777216) mod 2 ^ 64 = q * 16777216 /\ 0 <= q * 16777216 /\
                         (b0 + 256 * b1 + 65536 * b2 + 16777216 * s3) mod 2 ^ 64 =
                         q * 16777216 + (b0 + 256 * b1 + 65536 * b2)).
  { destruct (Z_lt_le_dec s3 0) as [N|P].
    - exists (s3 + 2 ^ 40). split; [|split; [lia|]].
      + rewrite <- (Z.mod_add (s3 * 16777216) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
      + rewrite <- (Z.mod_add (b0 + 256 * b1 + 65536 * b2 + 16777216 * s3) 1 (2 ^ 64)) by lia.
        rewrite Z.mod_small by lia. lia.
    - exists s3. split; [|split; [lia|]].
      + rewrite Z.mod_small by lia. reflexivity.
      + rewrite Z.mod_small by lia. lia. }
  destruct EA as (q & E1 & E2 & E4). rewrite E1, E4.
  rewrite (tw_lor_add (q * 16777216) (b2 * 65536) 24).
  2: lia.
  2: lia.
  2: (change (2 ^ 24) with 16777216; lia).
  2: (change (2 ^ 24) with 16777216; apply Z.mod_mul; lia).
  rewrite (tw_lor_add (q * 16777216 + b2 * 65536) (b1 * 256 + b0) 16).
  2: lia.
  2: lia.
  2: (change (2 ^ 16) with 65536; lia).
  2: (change (2 ^ 16) with 65536;
      replace (q * 16777216 + b2 * 65536) with ((q * 256 + b2) * 65536) by lia; apply Z.mod_mul; lia).
  lia.
Qed.

(* +0x248..+0x24c: srliw 2 of ml + 3, then slli 2 *)
Lemma tw_srliw : forall e, 0 <= e < 2 ^ 31 -> bv_swrap 32 (Z.shiftr (e mod 2 ^ 32) 2) = e / 4.
Proof.
  intros e He. rewrite (Z.mod_small e (2 ^ 32)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4.
  apply swrap32_id. split; [Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia].
Qed.

Lemma tw_align_eq : forall ml, Z.shiftl ((ml + 3) / 4) 2 = nl_align ml.
Proof. intros ml. unfold nl_align. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. lia. Qed.

(* +0x598..+0x59c / +0x504..+0x508: `(x + 3) & 0x1fffc` is NL_ALIGN(x) for a 16-bit x *)
Lemma tw_land_align : forall x, 0 <= x < 2 ^ 16 -> Z.land (x + 3) 131068 = nl_align x.
Proof.
  intros x Hx. unfold nl_align.
  change 131068 with (Z.ldiff (Z.ones 17) (Z.ones 2)).
  assert (E : Z.land (x + 3) (Z.ldiff (Z.ones 17) (Z.ones 2))
              = Z.ldiff (Z.land (x + 3) (Z.ones 17)) (Z.ones 2)).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec.
    destruct (Z.testbit (x + 3) n), (Z.testbit (Z.ones 17) n), (Z.testbit (Z.ones 2) n); reflexivity. }
  rewrite E. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 2) with 4. lia.
Qed.

Lemma tw_align_range : forall n, 0 <= n -> n <= nl_align n <= n + 3 /\ nl_align n mod 4 = 0.
Proof.
  intros n Hn. split; [apply nl_align_le; exact Hn|]. unfold nl_align.
  rewrite Z.mul_comm. apply Z.mod_mul. lia.
Qed.

(* ==========================================================================
   5. one step of the four walks
   ========================================================================== *)

(* the chunk loop: +0x198 / +0x1f0 next < n_chunks, then chunk next *)
Lemma cl_none : forall f cs i, nth_error cs i = None -> chunk_loop f cs i = (NlNone, i).
Proof. intros [|f] cs i H; [reflexivity|]. cbn [chunk_loop]. rewrite H. reflexivity. Qed.

Lemma cl_end : forall f kbs c, 0 <= nk_n_chunks kbs <= c ->
  chunk_loop f (nk_chunks kbs) (Z.to_nat c) = (NlNone, Z.to_nat c).
Proof. intros f kbs c Hc. apply cl_none. apply nk_chunks_none. exact Hc. Qed.

Lemma cl_hit : forall f kbs c, 0 <= c < nk_n_chunks kbs -> chunk_walk (nk_chunk kbs c) <> NlNone ->
  chunk_loop (S f) (nk_chunks kbs) (Z.to_nat c) = (chunk_walk (nk_chunk kbs c), Z.to_nat (c + 1)).
Proof.
  intros f kbs c Hc Hw. cbn [chunk_loop]. rewrite (nk_chunks_nth kbs c Hc). cbv beta iota.
  destruct (chunk_walk (nk_chunk kbs c)); [congruence | | |]; f_equal; lia.
Qed.

Lemma cl_miss : forall f kbs c, 0 <= c < nk_n_chunks kbs -> chunk_walk (nk_chunk kbs c) = NlNone ->
  chunk_loop (S f) (nk_chunks kbs) (Z.to_nat c) = chunk_loop f (nk_chunks kbs) (Z.to_nat (c + 1)).
Proof.
  intros f kbs c Hc Hw. cbn [chunk_loop]. rewrite (nk_chunks_nth kbs c Hc). cbv beta iota. rewrite Hw.
  f_equal. lia.
Qed.

(* one turn of the chunk loop at chunk c < n_chunks, both outcomes *)
Lemma cl_step : forall f kbs c, 0 <= c < nk_n_chunks kbs ->
  chunk_loop (S f) (nk_chunks kbs) (Z.to_nat c) =
  match chunk_walk (nk_chunk kbs c) with
  | NlNone => chunk_loop f (nk_chunks kbs) (Z.to_nat (c + 1))
  | v => (v, Z.to_nat (c + 1))
  end.
Proof.
  intros f kbs c Hc. destruct (chunk_walk (nk_chunk kbs c)) eqn:E;
    [apply cl_miss; assumption | ..];
    rewrite (cl_hit f kbs c Hc) by (rewrite E; discriminate); rewrite E; reflexivity.
Qed.

(* the message walk of chunk ck from the start *)
Lemma chunk_walk_eq : forall ck, chunk_walk ck = msg_scan (S (length ck)) ck 0 (Z.of_nat (length ck)).
Proof. reflexivity. Qed.

(* the message loop at (off, left): +0x204..+0x258 *)
Lemma ms_short : forall f c off left, left < 16 -> msg_scan f c off left = NlNone.
Proof.
  intros [|f] c off left H; [reflexivity|]. cbn [msg_scan]. unfold NL_HDR.
  destruct (Z.ltb_spec left 16); [reflexivity | lia].
Qed.

Lemma ms_bad : forall f c off left, 16 <= left -> (rd32 c off < 16 \/ left < rd32 c off) ->
  msg_scan (S f) c off left = NlNone.
Proof.
  intros f c off left H1 H2. cbn [msg_scan]. unfold NL_HDR.
  destruct (Z.ltb_spec left 16); [lia|].
  destruct (Z.ltb_spec (rd32 c off) 16); [reflexivity|].
  destruct (Z.ltb_spec left (rd32 c off)); [reflexivity | lia].
Qed.

(* NLMSG_ERROR, ml < 36: -EIO (+0x2a8..+0x2b0) *)
Lemma ms_short_err : forall f c off left, 16 <= left -> 16 <= rd32 c off <= left -> rd16 c (off + 4) = 2 ->
  rd32 c off < 36 -> msg_scan (S f) c off left = NlShort.
Proof.
  intros f c off left H1 H2 H3 H4. cbn [msg_scan]. unfold NL_HDR, NL_ERR_BODY, NL_ERROR.
  destruct (Z.ltb_spec left 16); [lia|].
  destruct (Z.ltb_spec (rd32 c off) 16); [lia|].
  destruct (Z.ltb_spec left (rd32 c off)); [lia|].
  rewrite H3. destruct (Z.ltb_spec (rd32 c off) (16 + 20)); [reflexivity | lia].
Qed.

(* NLMSG_ERROR, ml >= 36: the int32 code at off + 16 (+0x5ec..+0x638) *)
Lemma ms_err : forall f c off left, 16 <= left -> 16 <= rd32 c off <= left -> rd16 c (off + 4) = 2 ->
  36 <= rd32 c off -> msg_scan (S f) c off left = NlErr (rd32s c (off + 16)).
Proof.
  intros f c off left H1 H2 H3 H4. cbn [msg_scan]. unfold NL_HDR, NL_ERR_BODY, NL_ERROR.
  destruct (Z.ltb_spec left 16); [lia|].
  destruct (Z.ltb_spec (rd32 c off) 16); [lia|].
  destruct (Z.ltb_spec left (rd32 c off)); [lia|].
  rewrite H3. destruct (Z.ltb_spec (rd32 c off) (16 + 20)); [lia | reflexivity].
Qed.

(* RTM_NEWLINK: the attributes at off + 32, al = ml - 32 (+0x298..+0x2c8) *)
Lemma ms_link : forall f c off left, 16 <= left -> 16 <= rd32 c off <= left -> rd16 c (off + 4) = 16 ->
  msg_scan (S f) c off left = NlLink (attr_scan f c (off + 32) (rd32 c off - 32) no_attrs).
Proof.
  intros f c off left H1 H2 H3. cbn [msg_scan]. unfold NL_HDR, NL_ERROR, RTM_NEWLINK, IFI_LEN.
  destruct (Z.ltb_spec left 16); [lia|].
  destruct (Z.ltb_spec (rd32 c off) 16); [lia|].
  destruct (Z.ltb_spec left (rd32 c off)); [lia|].
  rewrite H3. replace (off + 16 + 16) with (off + 32) by lia.
  replace (rd32 c off - 16 - 16) with (rd32 c off - 32) by lia. reflexivity.
Qed.

(* any other type: off += align4(ml), left -= align4(ml) (+0x244..+0x258) *)
Lemma ms_other : forall f c off left, 16 <= left -> 16 <= rd32 c off <= left ->
  rd16 c (off + 4) <> 2 -> rd16 c (off + 4) <> 16 ->
  msg_scan (S f) c off left = msg_scan f c (off + nl_align (rd32 c off)) (left - nl_align (rd32 c off)).
Proof.
  intros f c off left H1 H2 H3 H4. cbn [msg_scan]. unfold NL_HDR, NL_ERROR, RTM_NEWLINK.
  destruct (Z.ltb_spec left 16); [lia|].
  destruct (Z.ltb_spec (rd32 c off) 16); [lia|].
  destruct (Z.ltb_spec left (rd32 c off)); [lia|].
  rewrite (proj2 (Z.eqb_neq _ _) H3), (proj2 (Z.eqb_neq _ _) H4). reflexivity.
Qed.

(* the attribute loop at (a, al): +0x30c..+0x5ac *)
Lemma as_short : forall f c off left acc, left < 4 -> attr_scan f c off left acc = acc.
Proof.
  intros f c off left acc H. destruct f as [|f]; [reflexivity|].
  cbn [attr_scan]. unfold RTA_HDR. destruct (Z.ltb_spec left 4); [reflexivity | lia].
Qed.

Lemma as_stop : forall f c off left acc, 4 <= left -> (rd16 c off < 4 \/ left < rd16 c off) ->
  attr_scan (S f) c off left acc = acc.
Proof.
  intros f c off left acc H1 H2. cbn [attr_scan]. unfold RTA_HDR.
  destruct (Z.ltb_spec left 4); [lia|].
  destruct (Z.ltb_spec (rd16 c off) 4); [reflexivity|].
  destruct (Z.ltb_spec left (rd16 c off)); [reflexivity | lia].
Qed.

(* IFLA_IFALIAS (type 20) *)
Lemma as_alias : forall f c off left ak aa, 4 <= left -> 4 <= rd16 c off <= left -> rd16 c (off + 2) = 20 ->
  attr_scan (S f) c off left (Attrs ak aa)
  = attr_scan f c (off + nl_align (rd16 c off)) (left - nl_align (rd16 c off))
      (Attrs ak (Some (slice c (off + RTA_HDR) (rd16 c off - RTA_HDR)))).
Proof.
  intros f c off left ak aa H1 H2 H3. cbn [attr_scan]. unfold RTA_HDR, IFLA_IFALIAS, IFLA_LINKINFO.
  destruct (Z.ltb_spec left 4); [lia|].
  destruct (Z.ltb_spec (rd16 c off) 4); [lia|].
  destruct (Z.ltb_spec left (rd16 c off)); [lia|].
  rewrite H3. reflexivity.
Qed.

(* IFLA_LINKINFO (type 18): the inner walk over [off + 4, off + l) *)
Lemma as_link : forall f c off left ak aa, 4 <= left -> 4 <= rd16 c off <= left -> rd16 c (off + 2) = 18 ->
  attr_scan (S f) c off left (Attrs ak aa)
  = attr_scan f c (off + nl_align (rd16 c off)) (left - nl_align (rd16 c off))
      (Attrs (kind_scan f c (off + 4) (rd16 c off - 4) ak) aa).
Proof.
  intros f c off left ak aa H1 H2 H3. cbn [attr_scan]. unfold RTA_HDR, IFLA_IFALIAS, IFLA_LINKINFO.
  destruct (Z.ltb_spec left 4); [lia|].
  destruct (Z.ltb_spec (rd16 c off) 4); [lia|].
  destruct (Z.ltb_spec left (rd16 c off)); [lia|].
  rewrite H3. reflexivity.
Qed.

Lemma as_other : forall f c off left acc, 4 <= left -> 4 <= rd16 c off <= left ->
  rd16 c (off + 2) <> 18 -> rd16 c (off + 2) <> 20 ->
  attr_scan (S f) c off left acc
  = attr_scan f c (off + nl_align (rd16 c off)) (left - nl_align (rd16 c off)) acc.
Proof.
  intros f c off left acc H1 H2 H3 H4. cbn [attr_scan]. unfold RTA_HDR, IFLA_IFALIAS, IFLA_LINKINFO.
  destruct (Z.ltb_spec left 4); [lia|].
  destruct (Z.ltb_spec (rd16 c off) 4); [lia|].
  destruct (Z.ltb_spec left (rd16 c off)); [lia|].
  rewrite (proj2 (Z.eqb_neq _ _) H4), (proj2 (Z.eqb_neq _ _) H3). reflexivity.
Qed.

(* the inner loop at (i, il): +0x3f8..+0x514 *)
Lemma ks_short : forall f c off left k, left < 4 -> kind_scan f c off left k = k.
Proof.
  intros f c off left k H. destruct f as [|f]; [reflexivity|].
  cbn [kind_scan]. unfold RTA_HDR. destruct (Z.ltb_spec left 4); [reflexivity | lia].
Qed.

Lemma ks_stop : forall f c off left k, 4 <= left -> (rd16 c off < 4 \/ left < rd16 c off) ->
  kind_scan (S f) c off left k = k.
Proof.
  intros f c off left k H1 H2. cbn [kind_scan]. unfold RTA_HDR.
  destruct (Z.ltb_spec left 4); [lia|].
  destruct (Z.ltb_spec (rd16 c off) 4); [reflexivity|].
  destruct (Z.ltb_spec left (rd16 c off)); [reflexivity | lia].
Qed.

(* IFLA_INFO_KIND (type 1) *)
Lemma ks_kind : forall f c off left k, 4 <= left -> 4 <= rd16 c off <= left -> rd16 c (off + 2) = 1 ->
  kind_scan (S f) c off left k
  = kind_scan f c (off + nl_align (rd16 c off)) (left - nl_align (rd16 c off))
      (Some (slice c (off + RTA_HDR) (rd16 c off - RTA_HDR))).
Proof.
  intros f c off left k H1 H2 H3. cbn [kind_scan]. unfold RTA_HDR, INFO_KIND.
  destruct (Z.ltb_spec left 4); [lia|].
  destruct (Z.ltb_spec (rd16 c off) 4); [lia|].
  destruct (Z.ltb_spec left (rd16 c off)); [lia|].
  rewrite H3. reflexivity.
Qed.

Lemma ks_other : forall f c off left k, 4 <= left -> 4 <= rd16 c off <= left -> rd16 c (off + 2) <> 1 ->
  kind_scan (S f) c off left k
  = kind_scan f c (off + nl_align (rd16 c off)) (left - nl_align (rd16 c off)) k.
Proof.
  intros f c off left k H1 H2 H3. cbn [kind_scan]. unfold RTA_HDR, INFO_KIND.
  destruct (Z.ltb_spec left 4); [lia|].
  destruct (Z.ltb_spec (rd16 c off) 4); [lia|].
  destruct (Z.ltb_spec left (rd16 c off)); [lia|].
  rewrite (proj2 (Z.eqb_neq _ _) H3). reflexivity.
Qed.

(* a text once found stays found *)
Lemma ks_some : forall f c off left x, kind_scan f c off left (Some x) <> None.
Proof.
  induction f as [|f IH]; intros c off left x; [discriminate|].
  cbn [kind_scan].
  destruct (left <? RTA_HDR); [discriminate|].
  destruct ((rd16 c off <? RTA_HDR) || (left <? rd16 c off)); [discriminate|].
  destruct (rd16 c (off + 2) =? INFO_KIND); apply IH.
Qed.

Lemma as_kind_some : forall f c off left acc,
  a_kind acc <> None -> a_kind (attr_scan f c off left acc) <> None.
Proof.
  induction f as [|f IH]; intros c off left acc H; [exact H|]. cbn [attr_scan].
  destruct (left <? RTA_HDR); [exact H|].
  destruct ((rd16 c off <? RTA_HDR) || (left <? rd16 c off)); [exact H|].
  apply IH.
  destruct (rd16 c (off + 2) =? IFLA_IFALIAS); [exact H|].
  destruct (rd16 c (off + 2) =? IFLA_LINKINFO); [|exact H].
  cbn [a_kind]. destruct (a_kind acc) as [x|]; [apply ks_some | exfalso; apply H; reflexivity].
Qed.

Lemma as_alias_some : forall f c off left acc,
  a_alias acc <> None -> a_alias (attr_scan f c off left acc) <> None.
Proof.
  induction f as [|f IH]; intros c off left acc H; [exact H|]. cbn [attr_scan].
  destruct (left <? RTA_HDR); [exact H|].
  destruct ((rd16 c off <? RTA_HDR) || (left <? rd16 c off)); [exact H|].
  apply IH.
  destruct (rd16 c (off + 2) =? IFLA_IFALIAS); [cbn [a_alias]; discriminate|].
  destruct (rd16 c (off + 2) =? IFLA_LINKINFO); exact H.
Qed.

(* a buffer the whole walk names nothing for was named nothing before *)
Lemma as_kind_none : forall f c off left acc,
  a_kind (attr_scan f c off left acc) = None -> a_kind acc = None.
Proof.
  intros f c off left acc H. destruct (a_kind acc) as [x|] eqn:E; [|reflexivity].
  exfalso. apply (as_kind_some f c off left acc); [rewrite E; discriminate | exact H].
Qed.

Lemma as_alias_none : forall f c off left acc,
  a_alias (attr_scan f c off left acc) = None -> a_alias acc = None.
Proof.
  intros f c off left acc H. destruct (a_alias acc) as [x|] eqn:E; [|reflexivity].
  exfalso. apply (as_alias_some f c off left acc); [rewrite E; discriminate | exact H].
Qed.

(* ==========================================================================
   6. fuel
   ========================================================================== *)

Lemma kind_scan_fuel : forall f1 f2 c off left k, left < Z.of_nat f1 -> left < Z.of_nat f2 ->
  kind_scan f1 c off left k = kind_scan f2 c off left k.
Proof.
  induction f1 as [|f1 IH]; intros f2 c off left k H1 H2.
  - rewrite (ks_short f2) by lia. reflexivity.
  - destruct f2 as [|f2]; [rewrite (ks_short (S f1)) by lia; reflexivity|].
    cbn [kind_scan].
    destruct (left <? RTA_HDR) eqn:E1; [reflexivity|].
    destruct ((rd16 c off <? RTA_HDR) || (left <? rd16 c off)) eqn:E2; [reflexivity|].
    apply Z.ltb_ge in E1. apply orb_false_iff in E2 as [E2 E3]. apply Z.ltb_ge in E2. apply Z.ltb_ge in E3.
    unfold RTA_HDR in *. pose proof (nl_align_le (rd16 c off) ltac:(lia)) as NA.
    apply IH; lia.
Qed.

Lemma attr_scan_fuel : forall f1 f2 c off left a, left < Z.of_nat f1 -> left < Z.of_nat f2 ->
  attr_scan f1 c off left a = attr_scan f2 c off left a.
Proof.
  induction f1 as [|f1 IH]; intros f2 c off left a H1 H2.
  - rewrite (as_short f2) by lia. reflexivity.
  - destruct f2 as [|f2]; [rewrite (as_short (S f1)) by lia; reflexivity|].
    cbn [attr_scan].
    destruct (left <? RTA_HDR) eqn:E1; [reflexivity|].
    destruct ((rd16 c off <? RTA_HDR) || (left <? rd16 c off)) eqn:E2; [reflexivity|].
    apply Z.ltb_ge in E1. apply orb_false_iff in E2 as [E2 E3]. apply Z.ltb_ge in E2. apply Z.ltb_ge in E3.
    unfold RTA_HDR in *. pose proof (nl_align_le (rd16 c off) ltac:(lia)) as NA.
    destruct (rd16 c (off + 2) =? IFLA_IFALIAS); [apply IH; lia|].
    destruct (rd16 c (off + 2) =? IFLA_LINKINFO); [|apply IH; lia].
    rewrite (kind_scan_fuel f1 f2) by lia. apply IH; lia.
Qed.

Lemma msg_scan_fuel : forall f1 f2 c off left, left < Z.of_nat f1 -> left < Z.of_nat f2 ->
  msg_scan f1 c off left = msg_scan f2 c off left.
Proof.
  induction f1 as [|f1 IH]; intros f2 c off left H1 H2.
  - rewrite (ms_short f2) by lia. reflexivity.
  - destruct f2 as [|f2]; [rewrite (ms_short (S f1)) by lia; reflexivity|].
    cbn [msg_scan].
    destruct (left <? NL_HDR) eqn:E1; [reflexivity|].
    destruct ((rd32 c off <? NL_HDR) || (left <? rd32 c off)) eqn:E2; [reflexivity|].
    apply Z.ltb_ge in E1. apply orb_false_iff in E2 as [E2 E3]. apply Z.ltb_ge in E2. apply Z.ltb_ge in E3.
    unfold NL_HDR, IFI_LEN in *. pose proof (nl_align_le (rd32 c off) ltac:(lia)) as NA.
    destruct (rd16 c (off + 4) =? NL_ERROR); [reflexivity|].
    destruct (rd16 c (off + 4) =? RTM_NEWLINK).
    + f_equal. apply attr_scan_fuel; lia.
    + apply IH; lia.
Qed.

Lemma chunk_loop_fuel : forall f1 f2 cs i, (length cs < i + f1)%nat -> (length cs < i + f2)%nat ->
  chunk_loop f1 cs i = chunk_loop f2 cs i.
Proof.
  induction f1 as [|f1 IH]; intros f2 cs i H1 H2.
  - rewrite (cl_none f2 cs i) by (apply nth_error_None; lia). reflexivity.
  - destruct f2 as [|f2]; [rewrite (cl_none (S f1) cs i) by (apply nth_error_None; lia); reflexivity|].
    cbn [chunk_loop]. destruct (nth_error cs i) as [ck|] eqn:E; [|reflexivity].
    destruct (chunk_walk ck); try reflexivity. apply IH; lia.
Qed.

(* the message walk of a chunk, with any fuel above its length *)
Lemma chunk_walk_fuel : forall ck f, Z.of_nat (length ck) < Z.of_nat f ->
  chunk_walk ck = msg_scan f ck 0 (Z.of_nat (length ck)).
Proof. intros ck f H. unfold chunk_walk. apply msg_scan_fuel; lia. Qed.

(* the chunk arm of talk_core at md_kstate, with the fuel of a loop on next *)
Lemma tw_core_md : forall mbs kbs f v j,
  md_socket_errno mbs = 0 -> md_send_errno mbs = 0 -> 0 <= md_next mbs -> 0 <= nk_n_chunks kbs ->
  nk_n_chunks kbs < md_next mbs + Z.of_nat f ->
  chunk_loop f (nk_chunks kbs) (Z.to_nat (md_next mbs)) = (v, j) ->
  talk_after (md_kstate mbs kbs) = Kst (nk_chunks kbs) j (nk_end_errno kbs) 0 0 /\
  talk_owes (md_kstate mbs kbs) = true /\ talk_attrs (md_kstate mbs kbs) = tw_at v /\
  talk_rc_model (md_kstate mbs kbs) = norm_rc (tw_rc v (nk_end_errno kbs)).
Proof.
  intros mbs kbs f v j H1 H2 H3 H4 H5 H6.
  apply (tw_core_main (md_kstate mbs kbs) v j H1 H2).
  cbn [k_chunks k_next md_kstate]. rewrite <- H6. apply chunk_loop_fuel; rewrite nk_chunks_length; lia.
Qed.

(* ==========================================================================
   7. take_text
   ========================================================================== *)

Lemma tt_nul_step : forall (pay : list byte) (i : nat) b,
  (i <= nul_at pay)%nat -> nth_error pay i = Some b ->
  (bz b = 0 -> nul_at pay = i) /\ (bz b <> 0 -> (S i <= nul_at pay)%nat).
Proof.
  induction pay as [|x pay IH]; intros i b Hi Hn; [destruct i; discriminate|].
  destruct i as [|i]; cbn [nul_at nth_error] in Hi, Hn |- *.
  - injection Hn as ->. destruct (Z.eqb_spec (bz b) 0) as [E|E]; cbv beta iota in *; split; intros H; lia.
  - destruct (Z.eqb_spec (bz x) 0) as [E|E]; cbv beta iota in *; [lia|].
    destruct (IH i b ltac:(lia) Hn) as [H1 H2]. split; intros H.
    + rewrite (H1 H). reflexivity.
    + specialize (H2 H). lia.
Qed.

(* the scan's three exits, with the counter k of s2: byte k is a NUL; byte k is not (k + 1 next); k = l - 4 *)
Lemma tt_scan_hit : forall (pay : list byte) k b, 0 <= k -> (Z.to_nat k <= nul_at pay)%nat ->
  nth_error pay (Z.to_nat k) = Some b -> bz b = 0 -> Z.of_nat (nul_at pay) = k.
Proof.
  intros pay k b Hk Hn Hb Hz. destruct (tt_nul_step pay (Z.to_nat k) b Hn Hb) as [A _]. rewrite (A Hz). lia.
Qed.

Lemma tt_scan_go : forall (pay : list byte) k b, 0 <= k -> (Z.to_nat k <= nul_at pay)%nat ->
  nth_error pay (Z.to_nat k) = Some b -> bz b <> 0 -> (Z.to_nat (k + 1) <= nul_at pay)%nat.
Proof.
  intros pay k b Hk Hn Hb Hz. destruct (tt_nul_step pay (Z.to_nat k) b Hn Hb) as [_ A]. specialize (A Hz). lia.
Qed.

Lemma tt_scan_end : forall (pay : list byte) n, Z.of_nat (length pay) = n -> (Z.to_nat n <= nul_at pay)%nat ->
  Z.of_nat (nul_at pay) = n.
Proof. intros pay n Hl Hn. pose proof (nul_at_le pay). lia. Qed.

(* the payload of the attribute at a (length l) of chunk ck: bytes [a + 4, a + l) *)
Lemma tt_pay_len : forall ck a l, 0 <= a -> 4 <= l -> a + l <= Z.of_nat (length ck) ->
  length (slice ck (a + RTA_HDR) (l - RTA_HDR)) = Z.to_nat (l - 4).
Proof. intros ck a l H1 H2 H3. unfold RTA_HDR. apply lw_slice_length; lia. Qed.

Lemma tt_pay_nth : forall ck a l i, 0 <= a -> 0 <= i < l - 4 ->
  nth_error (slice ck (a + RTA_HDR) (l - RTA_HDR)) (Z.to_nat i) = nth_error ck (Z.to_nat (a + 4 + i)).
Proof.
  intros ck a l i H1 H2. unfold RTA_HDR. rewrite lw_slice_nth by lia. f_equal. lia.
Qed.

(* the payload byte the code loads at b + 4 + a + k (frame slot 0x10 = b + 4) is a g_nl byte *)
Lemma tt_pay_kbs : forall kbs c a l i, 0 <= c -> 0 <= a -> 0 <= i < l - 4 ->
  a + l <= fld_u64 kbs (NK_CHUNK_LEN + 8 * c) ->
  nth_error (slice (nk_chunk kbs c) (a + RTA_HDR) (l - RTA_HDR)) (Z.to_nat i) =
  nth_error kbs (Z.to_nat (4096 * c + a + 4 + i)).
Proof.
  intros kbs c a l i Hc Ha Hi Hl. rewrite tt_pay_nth by lia.
  rewrite nk_chunk_nth by lia. f_equal. lia.
Qed.

(* +0x55c..+0x564: k := k if k < cap - 1 (unsigned), else cap - 1 *)
Lemma tt_clamp : forall k cap, (if k <? cap - 1 then k else cap - 1) = Z.min k (cap - 1).
Proof. intros k cap. destruct (Z.ltb_spec k (cap - 1)); lia. Qed.

Lemma tt_cut_len : forall pay cap, 1 <= cap ->
  Z.of_nat (length (cut_text pay cap)) = Z.min (Z.of_nat (nul_at pay)) (cap - 1).
Proof.
  intros pay cap Hc. unfold cut_text. rewrite length_firstn. pose proof (nul_at_le pay). lia.
Qed.

Lemma tt_cut_nth : forall pay cap i, (i < length (cut_text pay cap))%nat ->
  nth_error (cut_text pay cap) i = nth_error pay i.
Proof.
  intros pay cap i Hi. unfold cut_text in *. rewrite length_firstn in Hi.
  apply lw_nth_error_firstn. lia.
Qed.

Lemma tt_cut_nonul : forall pay cap, ~ In (zb 0) (cut_text pay cap).
Proof. intros pay cap H. apply (cut_text_nonul pay cap (zb 0) H). reflexivity. Qed.

Section t.
Variable segs : list Segment.

(* a stored NUL byte (sb zero, +0x588 / +0x4f4) *)
Lemma val_mem_nul : forall m a, val_mem segs m a 1 0 -> mbyte segs m a = Some (zb 0).
Proof.
  intros m a H. pose proof (H 0%nat ltac:(lia)) as H0. change (Z.of_nat 0) with 0 in H0.
  rewrite Z.add_0_r in H0. rewrite H0. reflexivity.
Qed.

(* two equal views are two equal bytes (checked_memcpy's post speaks of aview) *)
Lemma aview_mbyte_eq : forall (H H' : word -> bool) (m m' : word -> option byte) a a',
  aview segs H' m' a' = aview segs H m a -> mbyte segs (mrestrict H' m') a' = mbyte segs (mrestrict H m) a.
Proof.
  intros H H' m m' a a' E. unfold aview in E.
  destruct (mbyte segs (mrestrict H' m') a') as [b'|], (mbyte segs (mrestrict H m) a) as [b|];
    cbn in E; try discriminate; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* THE C STRING take_text LEAVES: the k = min(first NUL, cap - 1) bytes the copy put at buf (each the payload's),
   then the NUL at buf + k *)
Lemma acstr_cut : forall m buf pay cap,
  1 <= cap -> 0 <= buf -> buf + cap <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.min (Z.of_nat (nul_at pay)) (cap - 1) ->
     mbyte segs m (buf + i) = nth_error pay (Z.to_nat i)) ->
  mbyte segs m (buf + Z.min (Z.of_nat (nul_at pay)) (cap - 1)) = Some (zb 0) ->
  acstr_at segs m buf (cut_text pay cap).
Proof.
  intros m buf pay cap Hc Hb Hbc Hin Hnul.
  pose proof (tt_cut_len pay cap Hc) as HL.
  pose proof (nul_at_le pay) as Hn.
  split; [|apply tt_cut_nonul].
  split; [exact Hb|]. rewrite length_app. cbn [length]. split; [lia|].
  intros i Hi.
  destruct (Nat.ltb_spec i (length (cut_text pay cap))) as [Lt|Ge].
  - rewrite nth_error_app1 by exact Lt. rewrite tt_cut_nth by exact Lt.
    rewrite Hin by lia. rewrite Nat2Z.id. reflexivity.
  - assert (Ei : i = length (cut_text pay cap)) by lia. subst i.
    rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. cbn [nth_error].
    rewrite HL. exact Hnul.
Qed.

(* the same from what the take_text arm knows: checked_memcpy (+0x570 / +0x4dc) copied the k bytes from the payload
   at g + 4096 c + a + 4 (aview, as its post states it), the code stored the NUL at buf + k, and g_nl holds kbs *)
Lemma acstr_take : forall (H : word -> bool) mem mem3 g kbs c a l buf cap,
  anlk_at segs (mrestrict H mem) g kbs -> nlk_wf kbs -> 0 <= c < nk_n_chunks kbs ->
  0 <= a -> 4 <= l -> a + l <= fld_u64 kbs (NK_CHUNK_LEN + 8 * c) ->
  1 <= cap -> 0 <= buf -> buf + cap <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.min (Z.of_nat (nul_at (slice (nk_chunk kbs c) (a + RTA_HDR) (l - RTA_HDR)))) (cap - 1) ->
     aview segs H mem3 (buf + i) = aview segs H mem (g + 4096 * c + a + 4 + i)) ->
  mbyte segs (mrestrict H mem3)
    (buf + Z.min (Z.of_nat (nul_at (slice (nk_chunk kbs c) (a + RTA_HDR) (l - RTA_HDR)))) (cap - 1)) = Some (zb 0) ->
  acstr_at segs (mrestrict H mem3) buf (cut_text (slice (nk_chunk kbs c) (a + RTA_HDR) (l - RTA_HDR)) cap).
Proof.
  intros H mem mem3 g kbs c a l buf cap HN W Hc Ha Hl4 Hal Hcap Hb Hbc Hv Hnul.
  pose proof HN as [[(_ & _ & Hkb) _] HL].
  pose proof (nk_chunk_len kbs c W HL Hc) as (Hlen & Hcl & Hnc).
  pose proof (tt_pay_len (nk_chunk kbs c) a l Ha Hl4 ltac:(lia)) as Hpl.
  pose proof (nul_at_le (slice (nk_chunk kbs c) (a + RTA_HDR) (l - RTA_HDR))) as Hnl.
  apply acstr_cut; [exact Hcap | exact Hb | exact Hbc | | exact Hnul].
  intros i Hi.
  rewrite (aview_mbyte_eq H H mem mem3 _ _ (Hv i Hi)).
  rewrite tt_pay_kbs by lia.
  replace (g + 4096 * c + a + 4 + i) with (g + Z.of_nat (Z.to_nat (4096 * c + a + 4 + i))) by lia.
  apply Hkb. unfold NL_CHUNK_MAX, NL_CHUNKS, NK_SIZE in *. lia.
Qed.

(* the bytes of a list kept *)
Lemma abytes_kept : forall m m' a bs, abytes segs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte segs m' (a + i) = mbyte segs m (a + i)) ->
  abytes segs m' a bs.
Proof.
  intros m m' a bs (H1 & H2 & H) K. split; [exact H1|]. split; [exact H2|].
  intros i Hi. rewrite K by lia. apply H. exact Hi.
Qed.

(* a buffer whose bytes are all present and writable at the end (a part kept, a part written) *)
Lemma abuf_after : forall m m' a n, abuf segs m a n ->
  (forall i, 0 <= i < n -> mbyte segs m' (a + i) = mbyte segs m (a + i) \/ exists b, mbyte segs m' (a + i) = Some b) ->
  (forall i, 0 <= i < n -> writable_at segs m' (a + i)) ->
  abuf segs m' a n.
Proof.
  intros m m' a n (junk & Hl & (Ha & Hal & Hb) & _) Hd Hw.
  exists (abytes_of segs m' a (Z.to_nat n)). rewrite abytes_of_length. split; [lia|]. split.
  - apply abytes_of_abytes; [exact Ha | lia |]. intros i Hi.
    destruct (Hd (Z.of_nat i) ltac:(lia)) as [E|E]; [|exact E].
    rewrite E. rewrite (Hb i ltac:(lia)).
    destruct (nth_error junk i) as [b|] eqn:Eb; [exists b; reflexivity|].
    apply nth_error_None in Eb. lia.
  - intros i Hi. rewrite abytes_of_length in Hi. apply Hw. lia.
Qed.
End t.

(* ==========================================================================
   8. the model block
   ========================================================================== *)

(* the list bs with xs written from off, and the n little-endian bytes of v (val_mem's bytes) *)
Definition bput (bs : list byte) (off : Z) (xs : list byte) : list byte :=
  firstn (Z.to_nat off) bs ++ xs ++ skipn (Z.to_nat off + length xs) bs.
Definition lev (n : nat) (v : Z) : list byte := map (fun k => Z_to_bv 8 (le_byte v n k)) (seq 0 n).

Lemma lev_length : forall n v, length (lev n v) = n.
Proof. intros n v. unfold lev. rewrite length_map, length_seq. reflexivity. Qed.

Lemma lev_nth : forall n v k, (k < n)%nat -> nth_error (lev n v) k = Some (Z_to_bv 8 (le_byte v n k)).
Proof. intros n v k Hk. unfold lev. rewrite (lw_nth_error_map_seq _ n 0%nat k Hk). reflexivity. Qed.

Lemma lev_val : forall n v, 0 <= v < 2 ^ (8 * Z.of_nat n) -> bytes_le_to_Z (lev n v) = v.
Proof. intros n v Hv. apply (lw_bytes_of_vals n); [apply lev_length | exact Hv | apply lev_nth]. Qed.

Lemma bput_length : forall bs off xs, 0 <= off -> off + Z.of_nat (length xs) <= Z.of_nat (length bs) ->
  length (bput bs off xs) = length bs.
Proof. intros bs off xs H1 H2. unfold bput. rewrite !length_app, length_firstn, length_skipn. lia. Qed.

Lemma bput_nth_in : forall bs off xs k, 0 <= off -> off + Z.of_nat (length xs) <= Z.of_nat (length bs) ->
  (k < length xs)%nat -> nth_error (bput bs off xs) (Z.to_nat off + k) = nth_error xs k.
Proof.
  intros bs off xs k H1 H2 Hk. unfold bput.
  rewrite nth_error_app2 by (rewrite length_firstn; lia). rewrite length_firstn.
  replace (Z.to_nat off + k - Nat.min (Z.to_nat off) (length bs))%nat with k by lia.
  rewrite nth_error_app1 by lia. reflexivity.
Qed.

Lemma bput_nth_out : forall bs off xs i, 0 <= off -> off + Z.of_nat (length xs) <= Z.of_nat (length bs) ->
  (i < Z.to_nat off \/ Z.to_nat off + length xs <= i)%nat -> nth_error (bput bs off xs) i = nth_error bs i.
Proof.
  intros bs off xs i H1 H2 [Lt|Ge]; unfold bput.
  - rewrite nth_error_app1 by (rewrite length_firstn; lia). apply lw_nth_error_firstn. exact Lt.
  - rewrite nth_error_app2 by (rewrite length_firstn; lia). rewrite length_firstn.
    rewrite nth_error_app2 by lia. rewrite lw_nth_error_skipn. f_equal. lia.
Qed.

(* the n bytes of a list from o, when those bytes agree *)
Lemma tw_slice_agree : forall (l l' : list byte) o n, 0 <= o ->
  (forall k, (k < Z.to_nat n)%nat -> nth_error l' (Z.to_nat o + k) = nth_error l (Z.to_nat o + k)) ->
  slice l' o n = slice l o n.
Proof.
  intros l l' o n Ho H. apply nth_error_ext. intros k.
  destruct (Nat.ltb_spec k (Z.to_nat n)) as [Lt|Ge].
  - rewrite !lw_slice_nth by lia. apply H. exact Lt.
  - unfold slice. rewrite !tw_nth_firstn_ge by lia. reflexivity.
Qed.

Lemma slice_bput_out : forall bs off xs o n, 0 <= off -> off + Z.of_nat (length xs) <= Z.of_nat (length bs) ->
  0 <= o -> (o + n <= off \/ off + Z.of_nat (length xs) <= o) -> slice (bput bs off xs) o n = slice bs o n.
Proof.
  intros bs off xs o n H1 H2 Ho Hd. apply tw_slice_agree; [exact Ho|].
  intros k Hk. apply bput_nth_out; lia.
Qed.

Lemma rdn_bput_out : forall bs off xs o n, 0 <= off -> off + Z.of_nat (length xs) <= Z.of_nat (length bs) ->
  0 <= o -> (o + n <= off \/ off + Z.of_nat (length xs) <= o) -> rdn (bput bs off xs) o n = rdn bs o n.
Proof. intros bs off xs o n H1 H2 Ho Hd. unfold rdn. rewrite slice_bput_out by assumption. reflexivity. Qed.

Lemma slice_bput_same : forall bs off xs, 0 <= off -> off + Z.of_nat (length xs) <= Z.of_nat (length bs) ->
  slice (bput bs off xs) off (Z.of_nat (length xs)) = xs.
Proof.
  intros bs off xs H1 H2. apply lw_list_ext.
  - rewrite lw_slice_length; [lia | lia | lia | rewrite bput_length; lia].
  - intros k Hk. rewrite lw_slice_length in Hk by (rewrite ?bput_length; lia).
    rewrite lw_slice_nth by lia. apply bput_nth_in; lia.
Qed.

Lemma rdn_bput_same : forall bs off (n : nat) v, 0 <= off -> off + Z.of_nat n <= Z.of_nat (length bs) ->
  0 <= v < 2 ^ (8 * Z.of_nat n) -> rdn (bput bs off (lev n v)) off (Z.of_nat n) = v.
Proof.
  intros bs off n v H1 H2 Hv.
  assert (L : length (bput bs off (lev n v)) = length bs) by (apply bput_length; rewrite ?lev_length; lia).
  apply rdn_of_vals; [lia | rewrite L; lia | exact Hv |].
  intros k Hk. rewrite bput_nth_in by (rewrite ?lev_length; lia). apply lev_nth. exact Hk.
Qed.

Lemma rdn_bput_same4 : forall bs off v, 0 <= off -> off + 4 <= Z.of_nat (length bs) -> 0 <= v < 2 ^ 32 ->
  rdn (bput bs off (lev 4 v)) off 4 = v.
Proof. intros bs off v H1 H2 Hv. exact (rdn_bput_same bs off 4 v H1 H2 Hv). Qed.

Lemma rdn_bput_same8 : forall bs off v, 0 <= off -> off + 8 <= Z.of_nat (length bs) -> 0 <= v < 2 ^ 64 ->
  rdn (bput bs off (lev 8 v)) off 8 = v.
Proof. intros bs off v H1 H2 Hv. exact (rdn_bput_same bs off 8 v H1 H2 Hv). Qed.

(* two writes of the same width at the same place: the second wins *)
Lemma bput_bput_same : forall bs off xs ys, length xs = length ys -> 0 <= off ->
  off + Z.of_nat (length xs) <= Z.of_nat (length bs) -> bput (bput bs off xs) off ys = bput bs off ys.
Proof.
  intros bs off xs ys E H1 H2.
  assert (L1 : length (bput bs off xs) = length bs) by (apply bput_length; lia).
  apply lw_list_ext.
  - rewrite !bput_length; rewrite ?L1; lia.
  - intros k Hk. rewrite bput_length in Hk by (rewrite ?L1; lia). rewrite L1 in Hk.
    destruct (Nat.ltb_spec k (Z.to_nat off)) as [Lt|Ge];
      [|destruct (Nat.ltb_spec k (Z.to_nat off + length ys)) as [Lt2|Ge2]].
    + rewrite !bput_nth_out by (rewrite ?L1; lia). reflexivity.
    + replace k with (Z.to_nat off + (k - Z.to_nat off))%nat by lia.
      rewrite !bput_nth_in by (rewrite ?L1; lia). reflexivity.
    + rewrite !bput_nth_out by (rewrite ?L1; lia). reflexivity.
Qed.

(* the stores talk makes into the model block *)
Definition md_zero_sock (mb : list byte) : list byte := bput mb MD_SOCKET_ERRNO (lev 4 0).
Definition md_zero_send (mb : list byte) : list byte := bput mb MD_SEND_ERRNO (lev 4 0).
Definition md_set_next (mb : list byte) (j : Z) : list byte := bput mb MD_NEXT (lev 4 j).
(* owe (+0xf4..+0x168): when n_req < 16, checked_memcpy of the request into slot n_req, n_req := n_req + 1,
   req_len[n_req] := len; else nothing *)
Definition md_owe (mb req : list byte) : list byte :=
  if md_n_req mb <? NL_SENT_MAX
  then bput (bput (bput mb (MD_REQ + NL_SENT_LEN * md_n_req mb) req) MD_N_REQ (lev 4 (md_n_req mb + 1)))
            (MD_REQ_LEN + 8 * md_n_req mb) (lev 8 (Z.of_nat (length req)))
  else mb.

Ltac md_lia :=
  rewrite ?lev_length in *;
  unfold MD_SOCKET_ERRNO, MD_SEND_ERRNO, MD_NEXT, MD_REQ, MD_REQ_LEN, MD_N_REQ, MD_MARK,
    MD_N_MARK, MD_SIZE, MARK_LEN, NL_SENT_LEN, NL_SENT_MAX, MARKS_MAX in *;
  lia.

Lemma md_reqs_length : forall mb, length (md_reqs mb) = Z.to_nat (md_n_req mb).
Proof. intros mb. unfold md_reqs. rewrite length_map, length_seq. reflexivity. Qed.

(* the Post's last model conjunct *)
Lemma md_n_req_len : forall mb, model_wf mb -> md_n_req mb = Z.of_nat (length (md_reqs mb)).
Proof. intros mb (W1 & _). rewrite md_reqs_length. lia. Qed.

(* the Post's cursor on the two errno arms (k_next of talk_after is Z.to_nat (md_next mbs)) *)
Lemma md_next_nat : forall mb, model_wf mb -> Z.of_nat (Z.to_nat (md_next mb)) = md_next mb.
Proof. intros mb (_ & W2 & _). lia. Qed.

(* a write below the marks keeps them *)
Lemma md_marks_put : forall mb off xs, Z.of_nat (length mb) = MD_SIZE -> 0 <= off ->
  off + Z.of_nat (length xs) <= MD_MARK ->
  md_n_mark (bput mb off xs) = md_n_mark mb /\ md_marks (bput mb off xs) = md_marks mb /\
  (model_marks_wf mb -> model_marks_wf (bput mb off xs)).
Proof.
  intros mb off xs HL Ho Hx.
  assert (Hn : md_n_mark (bput mb off xs) = md_n_mark mb)
    by (unfold md_n_mark, fld_u32; apply rdn_bput_out; md_lia).
  assert (Hs : forall i, 0 <= i -> slice (bput mb off xs) (MD_MARK + MARK_LEN * i) MARK_LEN =
                                   slice mb (MD_MARK + MARK_LEN * i) MARK_LEN)
    by (intros i Hi; apply slice_bput_out; md_lia).
  split; [exact Hn|]. split.
  - unfold md_marks. rewrite Hn. apply map_ext. intros i. rewrite Hs by lia. reflexivity.
  - intros [H1 H2]. unfold model_marks_wf, slots_terminated in *. rewrite Hn. split; [exact H1|].
    intros i Hi. rewrite Hs by lia. apply H2. exact Hi.
Qed.

(* a write into the three header words keeps the requests *)
Lemma md_hdr_put : forall mb off xs, Z.of_nat (length mb) = MD_SIZE -> 0 <= off ->
  off + Z.of_nat (length xs) <= MD_REQ ->
  Z.of_nat (length (bput mb off xs)) = MD_SIZE /\
  md_n_req (bput mb off xs) = md_n_req mb /\ md_reqs (bput mb off xs) = md_reqs mb /\
  (forall i, 0 <= i -> fld_u64 (bput mb off xs) (MD_REQ_LEN + 8 * i) = fld_u64 mb (MD_REQ_LEN + 8 * i)) /\
  md_n_mark (bput mb off xs) = md_n_mark mb /\ md_marks (bput mb off xs) = md_marks mb /\
  (model_marks_wf mb -> model_marks_wf (bput mb off xs)).
Proof.
  intros mb off xs HL Ho Hx.
  assert (L : length (bput mb off xs) = length mb) by (apply bput_length; md_lia).
  assert (Hn : md_n_req (bput mb off xs) = md_n_req mb)
    by (unfold md_n_req, fld_u32; apply rdn_bput_out; md_lia).
  assert (H8 : forall i, 0 <= i -> fld_u64 (bput mb off xs) (MD_REQ_LEN + 8 * i) = fld_u64 mb (MD_REQ_LEN + 8 * i))
    by (intros i Hi; unfold fld_u64; apply rdn_bput_out; md_lia).
  destruct (md_marks_put mb off xs HL Ho ltac:(md_lia)) as (M1 & M2 & M3).
  split; [rewrite L; exact HL|]. split; [exact Hn|]. split; [|split; [exact H8|split; [exact M1|split; [exact M2|exact M3]]]].
  unfold md_reqs. rewrite Hn. apply map_ext. intros i. unfold md_req_one.
  rewrite H8 by lia. apply slice_bput_out; md_lia.
Qed.

(* +0x7c: socket_errno := 0 *)
Lemma md_zero_sock_ok : forall mb, Z.of_nat (length mb) = MD_SIZE -> model_wf mb ->
  Z.of_nat (length (md_zero_sock mb)) = MD_SIZE /\ model_wf (md_zero_sock mb) /\
  md_socket_errno (md_zero_sock mb) = 0 /\ md_send_errno (md_zero_sock mb) = md_send_errno mb /\
  md_next (md_zero_sock mb) = md_next mb /\ md_n_req (md_zero_sock mb) = md_n_req mb /\
  md_reqs (md_zero_sock mb) = md_reqs mb /\ md_n_mark (md_zero_sock mb) = md_n_mark mb /\
  md_marks (md_zero_sock mb) = md_marks mb.
Proof.
  intros mb HL (W1 & W2 & W3 & W4 & W5 & W6). unfold md_zero_sock.
  destruct (md_hdr_put mb MD_SOCKET_ERRNO (lev 4 0) HL ltac:(md_lia) ltac:(md_lia))
    as (L & N & R & F & M1 & M2 & M3).
  assert (S0 : md_socket_errno (bput mb MD_SOCKET_ERRNO (lev 4 0)) = 0)
    by (unfold md_socket_errno, fld_u32; apply rdn_bput_same4; md_lia).
  assert (S1 : md_send_errno (bput mb MD_SOCKET_ERRNO (lev 4 0)) = md_send_errno mb)
    by (unfold md_send_errno, fld_u32; apply rdn_bput_out; md_lia).
  assert (S2 : md_next (bput mb MD_SOCKET_ERRNO (lev 4 0)) = md_next mb)
    by (unfold md_next, fld_u32; apply rdn_bput_out; md_lia).
  split; [exact L|]. split.
  - unfold model_wf. rewrite N, S0, S1, S2. split; [exact W1|]. split; [exact W2|]. split; [lia|].
    split; [exact W4|]. split; [|exact (M3 W6)]. intros i Hi. rewrite F by lia. apply W5. exact Hi.
  - split; [exact S0|]. split; [exact S1|]. split; [exact S2|]. split; [exact N|]. split; [exact R|].
    split; [exact M1 | exact M2].
Qed.

(* +0xac: send_errno := 0 *)
Lemma md_zero_send_ok : forall mb, Z.of_nat (length mb) = MD_SIZE -> model_wf mb ->
  Z.of_nat (length (md_zero_send mb)) = MD_SIZE /\ model_wf (md_zero_send mb) /\
  md_send_errno (md_zero_send mb) = 0 /\ md_socket_errno (md_zero_send mb) = md_socket_errno mb /\
  md_next (md_zero_send mb) = md_next mb /\ md_n_req (md_zero_send mb) = md_n_req mb /\
  md_reqs (md_zero_send mb) = md_reqs mb /\ md_n_mark (md_zero_send mb) = md_n_mark mb /\
  md_marks (md_zero_send mb) = md_marks mb.
Proof.
  intros mb HL (W1 & W2 & W3 & W4 & W5 & W6). unfold md_zero_send.
  destruct (md_hdr_put mb MD_SEND_ERRNO (lev 4 0) HL ltac:(md_lia) ltac:(md_lia))
    as (L & N & R & F & M1 & M2 & M3).
  assert (S0 : md_send_errno (bput mb MD_SEND_ERRNO (lev 4 0)) = 0)
    by (unfold md_send_errno, fld_u32; apply rdn_bput_same4; md_lia).
  assert (S1 : md_socket_errno (bput mb MD_SEND_ERRNO (lev 4 0)) = md_socket_errno mb)
    by (unfold md_socket_errno, fld_u32; apply rdn_bput_out; md_lia).
  assert (S2 : md_next (bput mb MD_SEND_ERRNO (lev 4 0)) = md_next mb)
    by (unfold md_next, fld_u32; apply rdn_bput_out; md_lia).
  split; [exact L|]. split.
  - unfold model_wf. rewrite N, S0, S1, S2. split; [exact W1|]. split; [exact W2|]. split; [exact W3|].
    split; [lia|]. split; [|exact (M3 W6)]. intros i Hi. rewrite F by lia. apply W5. exact Hi.
  - split; [exact S0|]. split; [exact S1|]. split; [exact S2|]. split; [exact N|]. split; [exact R|].
    split; [exact M1 | exact M2].
Qed.

(* +0x1bc: next := j *)
Lemma md_set_next_ok : forall mb j, Z.of_nat (length mb) = MD_SIZE -> model_wf mb -> 0 <= j < 2 ^ 31 ->
  Z.of_nat (length (md_set_next mb j)) = MD_SIZE /\ model_wf (md_set_next mb j) /\
  md_next (md_set_next mb j) = j /\ md_socket_errno (md_set_next mb j) = md_socket_errno mb /\
  md_send_errno (md_set_next mb j) = md_send_errno mb /\ md_n_req (md_set_next mb j) = md_n_req mb /\
  md_reqs (md_set_next mb j) = md_reqs mb /\ md_n_mark (md_set_next mb j) = md_n_mark mb /\
  md_marks (md_set_next mb j) = md_marks mb.
Proof.
  intros mb j HL (W1 & W2 & W3 & W4 & W5 & W6) Hj. unfold md_set_next.
  destruct (md_hdr_put mb MD_NEXT (lev 4 j) HL ltac:(md_lia) ltac:(md_lia))
    as (L & N & R & F & M1 & M2 & M3).
  assert (S0 : md_next (bput mb MD_NEXT (lev 4 j)) = j)
    by (unfold md_next, fld_u32; apply rdn_bput_same4; md_lia).
  assert (S1 : md_socket_errno (bput mb MD_NEXT (lev 4 j)) = md_socket_errno mb)
    by (unfold md_socket_errno, fld_u32; apply rdn_bput_out; md_lia).
  assert (S2 : md_send_errno (bput mb MD_NEXT (lev 4 j)) = md_send_errno mb)
    by (unfold md_send_errno, fld_u32; apply rdn_bput_out; md_lia).
  split; [exact L|]. split.
  - unfold model_wf. rewrite N, S0, S1, S2. split; [exact W1|]. split; [lia|]. split; [exact W3|].
    split; [exact W4|]. split; [|exact (M3 W6)]. intros i Hi. rewrite F by lia. apply W5. exact Hi.
  - split; [exact S0|]. split; [exact S1|]. split; [exact S2|]. split; [exact N|]. split; [exact R|].
    split; [exact M1 | exact M2].
Qed.

(* the chunk loop stores the cursor at every turn: the last store wins *)
Lemma md_set_next_twice : forall mb x y, Z.of_nat (length mb) = MD_SIZE ->
  md_set_next (md_set_next mb x) y = md_set_next mb y.
Proof. intros mb x y HL. unfold md_set_next. apply bput_bput_same; [rewrite !lev_length; reflexivity | md_lia | md_lia]. Qed.

(* +0x118 ring full: owe does nothing *)
Lemma md_owe_full : forall mb req, NL_SENT_MAX <= md_n_req mb -> md_owe mb req = mb.
Proof. intros mb req H. unfold md_owe. destruct (Z.ltb_spec (md_n_req mb) NL_SENT_MAX); [lia | reflexivity]. Qed.

(* the three stores of owe, in the order of the code *)
Lemma md_owe_lt : forall mb req, md_n_req mb < NL_SENT_MAX ->
  md_owe mb req =
  bput (bput (bput mb (MD_REQ + NL_SENT_LEN * md_n_req mb) req) MD_N_REQ (lev 4 (md_n_req mb + 1)))
       (MD_REQ_LEN + 8 * md_n_req mb) (lev 8 (Z.of_nat (length req))).
Proof. intros mb req H. unfold md_owe. destruct (Z.ltb_spec (md_n_req mb) NL_SENT_MAX); [reflexivity | lia]. Qed.

Lemma md_owe_ok : forall mb req, Z.of_nat (length mb) = MD_SIZE -> model_wf mb ->
  Z.of_nat (length req) <= NL_SENT_LEN ->
  Z.of_nat (length (md_owe mb req)) = MD_SIZE /\ model_wf (md_owe mb req) /\
  md_reqs (md_owe mb req) = owe (md_reqs mb) req /\
  md_n_req (md_owe mb req) = Z.of_nat (length (md_reqs (md_owe mb req))) /\
  md_socket_errno (md_owe mb req) = md_socket_errno mb /\ md_send_errno (md_owe mb req) = md_send_errno mb /\
  md_next (md_owe mb req) = md_next mb /\
  md_n_mark (md_owe mb req) = md_n_mark mb /\ md_marks (md_owe mb req) = md_marks mb.
Proof.
  intros mb req HL HW Hr. pose proof HW as (W1 & W2 & W3 & W4 & W5 & W6).
  assert (Hlen : length (md_reqs mb) = Z.to_nat (md_n_req mb)) by apply md_reqs_length.
  destruct (Z_lt_le_dec (md_n_req mb) NL_SENT_MAX) as [Hn|Hn].
  2:{ rewrite md_owe_full by exact Hn.
      assert (Ow : owe (md_reqs mb) req = md_reqs mb).
      { unfold owe. rewrite Hlen. destruct (Z.ltb_spec (Z.of_nat (Z.to_nat (md_n_req mb))) NL_SENT_MAX);
          [md_lia | reflexivity]. }
      rewrite Ow. split; [exact HL|]. split; [exact HW|]. split; [reflexivity|].
      split; [apply md_n_req_len; exact HW|]. repeat split. }
  rewrite md_owe_lt by exact Hn.
  remember (md_n_req mb) as n eqn:En.
  remember (Z.of_nat (length req)) as len eqn:Elen.
  remember (bput mb (MD_REQ + NL_SENT_LEN * n) req) as mb1 eqn:E1.
  remember (bput mb1 MD_N_REQ (lev 4 (n + 1))) as mb2 eqn:E2.
  remember (bput mb2 (MD_REQ_LEN + 8 * n) (lev 8 len)) as mb3 eqn:E3.
  assert (L1 : length mb1 = length mb) by (rewrite E1; apply bput_length; md_lia).
  assert (L2 : length mb2 = length mb) by (rewrite E2, <- L1; apply bput_length; md_lia).
  assert (L3 : length mb3 = length mb) by (rewrite E3, <- L2; apply bput_length; md_lia).
  (* the three header words *)
  assert (O32 : forall o, 0 <= o -> o + 4 <= MD_REQ -> fld_u32 mb3 o = fld_u32 mb o).
  { intros o Ho1 Ho2. unfold fld_u32. rewrite E3, rdn_bput_out by md_lia. rewrite E2, rdn_bput_out by md_lia.
    rewrite E1. apply rdn_bput_out; md_lia. }
  assert (X0 : md_socket_errno mb3 = md_socket_errno mb) by (unfold md_socket_errno; apply O32; md_lia).
  assert (X1 : md_send_errno mb3 = md_send_errno mb) by (unfold md_send_errno; apply O32; md_lia).
  assert (X2 : md_next mb3 = md_next mb) by (unfold md_next; apply O32; md_lia).
  (* the count *)
  assert (N3 : md_n_req mb3 = n + 1).
  { unfold md_n_req, fld_u32. rewrite E3, rdn_bput_out by md_lia. rewrite E2. apply rdn_bput_same4; md_lia. }
  (* the lengths: the old ones, and the new one at n *)
  assert (O64 : forall i, 0 <= i < n -> fld_u64 mb3 (MD_REQ_LEN + 8 * i) = fld_u64 mb (MD_REQ_LEN + 8 * i)).
  { intros i Hi. unfold fld_u64. rewrite E3, rdn_bput_out by md_lia. rewrite E2, rdn_bput_out by md_lia.
    rewrite E1. apply rdn_bput_out; md_lia. }
  assert (F3 : fld_u64 mb3 (MD_REQ_LEN + 8 * n) = len).
  { unfold fld_u64. rewrite E3. apply rdn_bput_same8; md_lia. }
  (* the slots: the old ones, and the new one at n *)
  assert (SL : forall i, 0 <= i < n ->
            slice mb3 (MD_REQ + NL_SENT_LEN * i) (fld_u64 mb (MD_REQ_LEN + 8 * i)) =
            slice mb (MD_REQ + NL_SENT_LEN * i) (fld_u64 mb (MD_REQ_LEN + 8 * i))).
  { intros i Hi. pose proof (W5 i ltac:(lia)) as Wi.
    rewrite E3, slice_bput_out by md_lia. rewrite E2, slice_bput_out by md_lia.
    rewrite E1. apply slice_bput_out; md_lia. }
  assert (SN : slice mb3 (MD_REQ + NL_SENT_LEN * n) len = req).
  { rewrite E3, slice_bput_out by md_lia. rewrite E2, slice_bput_out by md_lia.
    rewrite E1, Elen. apply slice_bput_same; md_lia. }
  (* the marks *)
  assert (SM : md_n_mark mb3 = md_n_mark mb /\ md_marks mb3 = md_marks mb /\ model_marks_wf mb3).
  { destruct (md_marks_put mb2 (MD_REQ_LEN + 8 * n) (lev 8 len) ltac:(rewrite L2; exact HL) ltac:(md_lia)
                ltac:(md_lia)) as (A1 & A2 & A3).
    destruct (md_marks_put mb1 MD_N_REQ (lev 4 (n + 1)) ltac:(rewrite L1; exact HL) ltac:(md_lia)
                ltac:(md_lia)) as (B1 & B2 & B3).
    destruct (md_marks_put mb (MD_REQ + NL_SENT_LEN * n) req HL ltac:(md_lia) ltac:(md_lia)) as (C1 & C2 & C3).
    rewrite <- E3 in A1, A2, A3. rewrite <- E2 in B1, B2, B3. rewrite <- E1 in C1, C2, C3.
    split; [congruence|]. split; [congruence|]. apply A3, B3, C3, W6. }
  destruct SM as (SM1 & SM2 & SM3).
  assert (R3 : md_reqs mb3 = md_reqs mb ++ [req]).
  { unfold md_reqs at 1. rewrite N3.
    replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
    rewrite seq_S, map_app. unfold md_reqs. rewrite <- En. f_equal.
    - apply map_ext_in. intros k Hk. apply in_seq in Hk. unfold md_req_one.
      rewrite O64 by lia. apply SL. lia.
    - cbn [map]. f_equal. unfold md_req_one. rewrite Nat.add_0_l, Z2Nat.id by lia.
      rewrite F3. exact SN. }
  assert (WF3 : model_wf mb3).
  { unfold model_wf. rewrite N3, X0, X1, X2.
    split; [md_lia|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. split; [|exact SM3].
    intros i Hi. destruct (Z.eq_dec i n) as [->|Hne].
    - rewrite F3. md_lia.
    - rewrite O64 by lia. apply W5. lia. }
  split; [rewrite L3; exact HL|]. split; [exact WF3|]. split.
  { rewrite R3. unfold owe. rewrite Hlen. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
  split; [apply md_n_req_len; exact WF3|].
  split; [exact X0|]. split; [exact X1|]. split; [exact X2|]. split; [exact SM1 | exact SM2].
Qed.

(* THE CHUNK STAGE in the raw forms of talk_defs.v (tk_clr / tk_mo / tk_mres), cs := nk_chunks kbs,
   n := nk_n_chunks kbs, K0 := md_kstate mbs kbs *)
Lemma cls_start : forall mbs kbs,
  chunk_loop (S (length (nk_chunks kbs))) (nk_chunks kbs) (Z.to_nat (md_next mbs)) =
  chunk_loop (S (Z.to_nat (nk_n_chunks kbs - md_next mbs))) (nk_chunks kbs) (Z.to_nat (md_next mbs)).
Proof. intros mbs kbs. apply chunk_loop_fuel; rewrite nk_chunks_length; lia. Qed.

Lemma cls_miss : forall mbs kbs j,
  chunk_loop (S (length (nk_chunks kbs))) (nk_chunks kbs) (Z.to_nat (md_next mbs)) =
  chunk_loop (S (Z.to_nat (nk_n_chunks kbs - j))) (nk_chunks kbs) (Z.to_nat j) ->
  0 <= j < nk_n_chunks kbs -> chunk_walk (nk_chunk kbs j) = NlNone ->
  chunk_loop (S (length (nk_chunks kbs))) (nk_chunks kbs) (Z.to_nat (md_next mbs)) =
  chunk_loop (S (Z.to_nat (nk_n_chunks kbs - (j + 1)))) (nk_chunks kbs) (Z.to_nat (j + 1)).
Proof.
  intros mbs kbs j H Hj Hw. rewrite H. rewrite (cl_miss (Z.to_nat (nk_n_chunks kbs - j)) kbs j Hj Hw).
  replace (Z.to_nat (nk_n_chunks kbs - j)) with (S (Z.to_nat (nk_n_chunks kbs - (j + 1)))) by lia.
  reflexivity.
Qed.

Lemma cls_hit : forall mbs kbs j,
  chunk_loop (S (length (nk_chunks kbs))) (nk_chunks kbs) (Z.to_nat (md_next mbs)) =
  chunk_loop (S (Z.to_nat (nk_n_chunks kbs - j))) (nk_chunks kbs) (Z.to_nat j) ->
  0 <= j < nk_n_chunks kbs -> chunk_walk (nk_chunk kbs j) <> NlNone ->
  chunk_loop (S (length (nk_chunks kbs))) (nk_chunks kbs) (Z.to_nat (md_next mbs)) =
  (chunk_walk (nk_chunk kbs j), S (Z.to_nat j)).
Proof.
  intros mbs kbs j H Hj Hw. rewrite H. rewrite (cl_hit (Z.to_nat (nk_n_chunks kbs - j)) kbs j Hj Hw).
  replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia. reflexivity.
Qed.

Lemma cls_end : forall mbs kbs j,
  chunk_loop (S (length (nk_chunks kbs))) (nk_chunks kbs) (Z.to_nat (md_next mbs)) =
  chunk_loop (S (Z.to_nat (nk_n_chunks kbs - j))) (nk_chunks kbs) (Z.to_nat j) ->
  nk_n_chunks kbs <= j ->
  chunk_loop (S (length (nk_chunks kbs))) (nk_chunks kbs) (Z.to_nat (md_next mbs)) = (NlNone, Z.to_nat j).
Proof.
  intros mbs kbs j H Hj. rewrite H. apply cl_none. unfold nk_chunks. apply tw_nth_map_seq_none. lia.
Qed.

(* the model block of the chunk stage (tk_mo) after owe, and kept by a store of the cursor *)
Lemma mo_owe : forall mbs req, Z.of_nat (length mbs) = MD_SIZE -> model_wf mbs ->
  Z.of_nat (length req) <= NL_SENT_LEN -> md_socket_errno mbs = 0 -> md_send_errno mbs = 0 ->
  Z.of_nat (length (md_owe mbs req)) = MD_SIZE /\ md_next (md_owe mbs req) = md_next mbs /\
  (model_wf (md_owe mbs req) /\ md_socket_errno (md_owe mbs req) = 0 /\ md_send_errno (md_owe mbs req) = 0 /\
   md_n_mark (md_owe mbs req) = md_n_mark mbs /\ md_marks (md_owe mbs req) = md_marks mbs /\
   md_reqs (md_owe mbs req) = owe (md_reqs mbs) req /\
   md_n_req (md_owe mbs req) = Z.of_nat (length (md_reqs (md_owe mbs req)))).
Proof.
  intros mbs req HL HW Hr H1 H2.
  destruct (md_owe_ok mbs req HL HW Hr) as (L & W & R & N & S0 & S1 & S2 & M1 & M2).
  rewrite S0, S1. refine (conj L (conj S2 (conj W (conj H1 (conj H2 (conj M1 (conj M2 (conj R N)))))))).
Qed.

Lemma mo_set_next : forall mbs req mb j, Z.of_nat (length mb) = MD_SIZE -> 0 <= j < 2 ^ 31 ->
  model_wf mb /\ md_socket_errno mb = 0 /\ md_send_errno mb = 0 /\ md_n_mark mb = md_n_mark mbs /\
  md_marks mb = md_marks mbs /\ md_reqs mb = owe (md_reqs mbs) req /\ md_n_req mb = Z.of_nat (length (md_reqs mb)) ->
  Z.of_nat (length (md_set_next mb j)) = MD_SIZE /\ md_next (md_set_next mb j) = j /\
  (model_wf (md_set_next mb j) /\ md_socket_errno (md_set_next mb j) = 0 /\ md_send_errno (md_set_next mb j) = 0 /\
   md_n_mark (md_set_next mb j) = md_n_mark mbs /\ md_marks (md_set_next mb j) = md_marks mbs /\
   md_reqs (md_set_next mb j) = owe (md_reqs mbs) req /\
   md_n_req (md_set_next mb j) = Z.of_nat (length (md_reqs (md_set_next mb j)))).
Proof.
  intros mbs req mb j HL Hj (HW & H1 & H2 & H3 & H4 & H5 & H6).
  destruct (md_set_next_ok mb j HL HW Hj) as (L & W & S0 & S1 & S2 & N & R & M1 & M2).
  rewrite S1, S2, M1, M2, N, R.
  refine (conj L (conj S0 (conj W (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 H6)))))))).
Qed.

(* the chunk arm's exit (tk_mres from tk_mo and the chunk loop's answer) *)
Lemma mres_main : forall mbs kbs req mb v j,
  md_socket_errno mbs = 0 -> md_send_errno mbs = 0 ->
  chunk_loop (S (length (nk_chunks kbs))) (nk_chunks kbs) (Z.to_nat (md_next mbs)) = (v, j) ->
  model_wf mb /\ md_socket_errno mb = 0 /\ md_send_errno mb = 0 /\ md_n_mark mb = md_n_mark mbs /\
  md_marks mb = md_marks mbs /\ md_reqs mb = owe (md_reqs mbs) req /\ md_n_req mb = Z.of_nat (length (md_reqs mb)) ->
  md_next mb = Z.of_nat j ->
  (model_wf mb /\ md_next mb = Z.of_nat (k_next (talk_after (md_kstate mbs kbs))) /\ md_socket_errno mb = 0 /\
   md_send_errno mb = k_send (talk_after (md_kstate mbs kbs)) /\ md_n_mark mb = md_n_mark mbs /\
   md_marks mb = md_marks mbs /\
   md_reqs mb = (if talk_owes (md_kstate mbs kbs) then owe (md_reqs mbs) req else md_reqs mbs) /\
   md_n_req mb = Z.of_nat (length (md_reqs mb))) /\
  talk_rc_model (md_kstate mbs kbs) = norm_rc (tw_rc v (nk_end_errno kbs)) /\
  talk_attrs (md_kstate mbs kbs) = tw_at v.
Proof.
  intros mbs kbs req mb v j H1 H2 HC (HW & S0 & S1 & M1 & M2 & R & N) Hn.
  destruct (tw_core_main (md_kstate mbs kbs) v j H1 H2 HC) as (TA & TO & TT & TR).
  rewrite TA, TO. cbn [k_next k_send].
  split; [|split; [exact TR | exact TT]].
  refine (conj HW (conj Hn (conj S0 (conj S1 (conj M1 (conj M2 (conj R N))))))).
Qed.

(* the two errno arms' exits (tk_mres at md_zero_sock mbs / md_zero_send mbs) *)
Lemma mres_sock : forall mbs kbs req, Z.of_nat (length mbs) = MD_SIZE -> model_wf mbs -> md_socket_errno mbs <> 0 ->
  Z.of_nat (length (md_zero_sock mbs)) = MD_SIZE /\
  (model_wf (md_zero_sock mbs) /\
   md_next (md_zero_sock mbs) = Z.of_nat (k_next (talk_after (md_kstate mbs kbs))) /\
   md_socket_errno (md_zero_sock mbs) = 0 /\
   md_send_errno (md_zero_sock mbs) = k_send (talk_after (md_kstate mbs kbs)) /\
   md_n_mark (md_zero_sock mbs) = md_n_mark mbs /\ md_marks (md_zero_sock mbs) = md_marks mbs /\
   md_reqs (md_zero_sock mbs) = (if talk_owes (md_kstate mbs kbs) then owe (md_reqs mbs) req else md_reqs mbs) /\
   md_n_req (md_zero_sock mbs) = Z.of_nat (length (md_reqs (md_zero_sock mbs)))) /\
  talk_rc_model (md_kstate mbs kbs) = - md_socket_errno mbs /\ talk_attrs (md_kstate mbs kbs) = no_attrs.
Proof.
  intros mbs kbs req HL HW Hs. pose proof HW as (_ & W2 & W3 & _).
  destruct (md_zero_sock_ok mbs HL HW) as (L & W & S0 & S1 & S2 & N & R & M1 & M2).
  destruct (tw_core_sock (md_kstate mbs kbs) Hs) as (TR & TT & TA & TO).
  rewrite TA, TO. cbn [k_next k_send k_sock md_kstate]. cbn [k_sock md_kstate] in TR.
  split; [exact L|]. split; [|split; [rewrite TR; apply tw_norm_neg; lia | exact TT]].
  rewrite S1, S2, M1, M2, R, N. split; [exact W|]. split; [lia|]. split; [exact S0|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  apply md_n_req_len. exact HW.
Qed.

Lemma mres_send : forall mbs kbs req, Z.of_nat (length mbs) = MD_SIZE -> model_wf mbs ->
  md_socket_errno mbs = 0 -> md_send_errno mbs <> 0 ->
  Z.of_nat (length (md_zero_send mbs)) = MD_SIZE /\
  (model_wf (md_zero_send mbs) /\
   md_next (md_zero_send mbs) = Z.of_nat (k_next (talk_after (md_kstate mbs kbs))) /\
   md_socket_errno (md_zero_send mbs) = 0 /\
   md_send_errno (md_zero_send mbs) = k_send (talk_after (md_kstate mbs kbs)) /\
   md_n_mark (md_zero_send mbs) = md_n_mark mbs /\ md_marks (md_zero_send mbs) = md_marks mbs /\
   md_reqs (md_zero_send mbs) = (if talk_owes (md_kstate mbs kbs) then owe (md_reqs mbs) req else md_reqs mbs) /\
   md_n_req (md_zero_send mbs) = Z.of_nat (length (md_reqs (md_zero_send mbs)))) /\
  talk_rc_model (md_kstate mbs kbs) = - md_send_errno mbs /\ talk_attrs (md_kstate mbs kbs) = no_attrs.
Proof.
  intros mbs kbs req HL HW Hs Hd. pose proof HW as (_ & W2 & W3 & W4 & _).
  destruct (md_zero_send_ok mbs HL HW) as (L & W & S0 & S1 & S2 & N & R & M1 & M2).
  destruct (tw_core_send (md_kstate mbs kbs) Hs Hd) as (TR & TT & TA & TO).
  rewrite TA, TO. cbn [k_next k_send k_sock md_kstate]. cbn [k_send md_kstate] in TR.
  split; [exact L|]. split; [|split; [rewrite TR; apply tw_norm_neg; lia | exact TT]].
  rewrite S1, S2, M1, M2, R, N. split; [exact W|]. split; [lia|]. split; [rewrite Hs; reflexivity|].
  split; [exact S0|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  apply md_n_req_len. exact HW.
Qed.

Section mm.
Variable segs : list Segment.

Lemma amodel_at_unique : forall m p b1 b2, amodel_at segs m p b1 -> amodel_at segs m p b2 -> b1 = b2.
Proof.
  intros m p b1 b2 [[(_ & _ & H1) _] L1] [[(_ & _ & H2) _] L2].
  apply lw_list_ext; [lia|].
  intros k Hk. rewrite <- (H1 k Hk). apply H2. lia.
Qed.

(* THE MODEL LIST OF THE MEMORY AFTER A WRITE of xs at p + off: the bytes outside the write as before, the written
   bytes those of xs, every byte of the block still writable *)
Lemma amodel_put : forall m m' p mb off xs,
  amodel_at segs m p mb -> 0 <= off -> off + Z.of_nat (length xs) <= MD_SIZE ->
  (forall i, 0 <= i < MD_SIZE -> ~ (off <= i < off + Z.of_nat (length xs)) ->
     mbyte segs m' (p + i) = mbyte segs m (p + i)) ->
  (forall k, (k < length xs)%nat -> mbyte segs m' (p + off + Z.of_nat k) = nth_error xs k) ->
  (forall i, 0 <= i < MD_SIZE -> writable_at segs m' (p + i)) ->
  amodel_at segs m' p (bput mb off xs).
Proof.
  intros m m' p mb off xs [[(Hp & Hpl & Hb) _] HL] Ho Hox Hout Hin Hw.
  assert (L' : length (bput mb off xs) = length mb) by (apply bput_length; lia).
  split; [|rewrite L'; exact HL].
  split; [split; [exact Hp|]; split; [rewrite L'; exact Hpl|]|].
  - intros i Hi. rewrite L' in Hi.
    destruct (Z_lt_le_dec (Z.of_nat i) off) as [H1|H1];
      [|destruct (Z_lt_le_dec (Z.of_nat i) (off + Z.of_nat (length xs))) as [H2|H2]].
    + rewrite bput_nth_out by lia. rewrite Hout by lia. apply Hb. exact Hi.
    + replace i with (Z.to_nat off + (i - Z.to_nat off))%nat by lia.
      rewrite bput_nth_in by lia.
      replace (p + Z.of_nat (Z.to_nat off + (i - Z.to_nat off))) with (p + off + Z.of_nat (i - Z.to_nat off))
        by lia.
      apply Hin. lia.
    + rewrite bput_nth_out by lia. rewrite Hout by lia. apply Hb. exact Hi.
  - intros i Hi. rewrite L' in Hi. apply Hw. lia.
Qed.

(* the same for a store of the n-byte value v (sw / sd): its val_mem at p + off *)
Lemma amodel_store : forall m m' p mb off (n : nat) v,
  amodel_at segs m p mb -> 0 <= off -> off + Z.of_nat n <= MD_SIZE ->
  (forall i, 0 <= i < MD_SIZE -> ~ (off <= i < off + Z.of_nat n) -> mbyte segs m' (p + i) = mbyte segs m (p + i)) ->
  val_mem segs m' (p + off) n v ->
  (forall i, 0 <= i < MD_SIZE -> writable_at segs m' (p + i)) ->
  amodel_at segs m' p (bput mb off (lev n v)).
Proof.
  intros m m' p mb off n v HA Ho Hon Hout HV Hw.
  apply (amodel_put m m' p mb off (lev n v) HA Ho); rewrite ?lev_length; [exact Hon | exact Hout | | exact Hw].
  intros k Hk. rewrite lev_nth by exact Hk. apply HV. exact Hk.
Qed.

(* a write elsewhere keeps the model list *)
Lemma amodel_kept : forall m m' p mb, amodel_at segs m p mb ->
  (forall i, 0 <= i < MD_SIZE -> mbyte segs m' (p + i) = mbyte segs m (p + i)) ->
  (forall i, 0 <= i < MD_SIZE -> writable_at segs m' (p + i)) ->
  amodel_at segs m' p mb.
Proof.
  intros m m' p mb [[Hab _] HL] K Hw. split; [|exact HL]. split.
  - apply (abytes_kept segs m m' p mb Hab). intros i Hi. apply K. lia.
  - intros i Hi. apply Hw. lia.
Qed.
End mm.
