(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/bzip2/bzip2_compress_target/lib/K/A/L_hkit.v, with its module paths and module names changed; 801 of its 858 lines of code are new or changed and 196 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/Prog/reac_served_unmark_all.v, with its module paths and module names changed; 208 of its 301 lines of code are new or changed and 765 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A, the op_unmark arm (+0x6e8): the pure facts its walk needs over
   lib/Prog/link_spec.v, and the C-string view of a mark slot of the model block.
   The pure lemmas are the plain walk's (lib/Prog/Slot/LC3LoopLib.v, the c3l_* lemmas), restated here over
   link_spec only so that this closure holds no plain-image module.

   Proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ==========================================================================
   1. The exchange keeps the chunk queue and the end errno
   ========================================================================== *)

Lemma u_talk_after_ce : forall K, k_chunks (talk_after K) = k_chunks K /\ k_end (talk_after K) = k_end K.
Proof.
  intros K. unfold talk_after, talk_core.
  destruct (negb (k_sock K =? 0)); [split; reflexivity|].
  destruct (negb (k_send K =? 0)); [split; reflexivity|].
  destruct (chunk_loop (S (length (k_chunks K))) (k_chunks K) (k_next K)) as [v j].
  destruct v; split; reflexivity.
Qed.

Lemma u_read_ce : forall tab nm kc ac reqs K,
  k_chunks (r_state (read_core tab nm kc ac reqs K)) = k_chunks K /\
  k_end (r_state (read_core tab nm kc ac reqs K)) = k_end K.
Proof.
  intros. unfold read_core. destruct nm as [s|]; [|split; reflexivity]. cbv zeta.
  destruct (Nat.eqb (length s) 0); [split; reflexivity|].
  destruct (index_of tab s =? 0); [split; reflexivity|]. apply u_talk_after_ce.
Qed.

Lemma u_write_ce : forall tab nm al reqs K,
  k_chunks (w_state (write_core tab nm al reqs K)) = k_chunks K /\
  k_end (w_state (write_core tab nm al reqs K)) = k_end K.
Proof.
  intros. unfold write_core. destruct nm as [s|]; [|split; reflexivity].
  destruct al as [a|]; [|split; reflexivity]. cbv zeta.
  destruct (Nat.eqb (length s) 0); [split; reflexivity|].
  destruct (ALIAS_MAX <=? Z.of_nat (length a)); [split; reflexivity|].
  destruct (index_of tab s =? 0); [split; reflexivity|]. apply u_talk_after_ce.
Qed.

Lemma u_kst_eta : forall K, Kst (k_chunks K) (k_next K) (k_end K) (k_sock K) (k_send K) = K.
Proof. intros [a b c d e]. reflexivity. Qed.

(* the model's state after a step whose post gives its three own fields from the step's state K', when K' keeps
   the chunk queue and the end errno of g_nl *)
Lemma u_md_kstate_of : forall mbs' kbs K',
  md_next mbs' = Z.of_nat (k_next K') -> md_socket_errno mbs' = k_sock K' -> md_send_errno mbs' = k_send K' ->
  k_chunks K' = nk_chunks kbs -> k_end K' = nk_end_errno kbs ->
  md_kstate mbs' kbs = K'.
Proof.
  intros mbs' kbs K' Hn Hs Hd Hc He. unfold md_kstate. rewrite Hn, Hs, Hd, Nat2Z.id, <- Hc, <- He.
  apply u_kst_eta.
Qed.

(* ==========================================================================
   2. The answer codes
   ========================================================================== *)

Lemma u_byte_zero : forall b : byte, bv_unsigned b = 0 -> b = Z_to_bv 8 0.
Proof. intros b H. apply bv_eq. rewrite H. reflexivity. Qed.

Lemma u_byte_eq : forall a b : byte, bv_unsigned a = bv_unsigned b -> a = b.
Proof. intros a b H. apply bv_eq. exact H. Qed.

Lemma u_rd32_range : forall c off, 0 <= rd32 c off < 2 ^ 32.
Proof.
  intros c off. unfold rd32, rdn. pose proof (bytes_le_to_Z_nonneg (slice c off 4)) as H0.
  pose proof (bytes_le_to_Z_bound (slice c off 4)) as H1.
  assert (L : (length (slice c off 4) <= 4)%nat) by (unfold slice; rewrite length_firstn; lia).
  assert (P : 2 ^ (8 * Z.of_nat (length (slice c off 4))) <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
  set (q := 2 ^ (8 * Z.of_nat (length (slice c off 4)))) in *. lia.
Qed.

Lemma u_rd32s_range : forall c off, - 2 ^ 31 <= rd32s c off < 2 ^ 31.
Proof.
  intros c off. unfold rd32s. cbv zeta. pose proof (u_rd32_range c off) as R.
  destruct (Z.ltb_spec (rd32 c off) (2 ^ 31)); lia.
Qed.

Lemma u_msg_scan_err : forall fuel c off left code, msg_scan fuel c off left = NlErr code ->
  - 2 ^ 31 <= code < 2 ^ 31.
Proof.
  induction fuel as [|f IH]; intros c off left code H; cbn [msg_scan] in H; [discriminate|].
  destruct (left <? NL_HDR); [discriminate|].
  destruct ((rd32 c off <? NL_HDR) || (left <? rd32 c off)); [discriminate|].
  destruct (rd16 c (off + 4) =? NL_ERROR).
  - destruct (rd32 c off <? NL_HDR + NL_ERR_BODY); [discriminate|]. injection H as <-. apply u_rd32s_range.
  - destruct (rd16 c (off + 4) =? RTM_NEWLINK); [discriminate|]. exact (IH _ _ _ _ H).
Qed.

Lemma u_chunk_loop_err : forall fuel cs i code j, chunk_loop fuel cs i = (NlErr code, j) ->
  - 2 ^ 31 <= code < 2 ^ 31.
Proof.
  induction fuel as [|f IH]; intros cs i code j H; cbn [chunk_loop] in H; [discriminate|].
  destruct (nth_error cs i) as [c|]; [|discriminate].
  destruct (chunk_walk c) as [| |code'|a] eqn:E.
  - exact (IH _ _ _ _ H).
  - discriminate.
  - injection H as <- _. exact (u_msg_scan_err _ _ _ _ _ E).
  - discriminate.
Qed.

Lemma u_talk_rc_range : forall K, 0 <= k_sock K < 2 ^ 31 -> 0 <= k_send K < 2 ^ 31 -> 0 <= k_end K < 2 ^ 31 ->
  - 2 ^ 32 < talk_rc_lib K < 2 ^ 32.
Proof.
  intros K Hs Hd He. unfold talk_rc_lib, talk_core.
  destruct (negb (k_sock K =? 0)); [cbn [fst]; lia|].
  destruct (negb (k_send K =? 0)); [cbn [fst]; lia|].
  destruct (chunk_loop (S (length (k_chunks K))) (k_chunks K) (k_next K)) as [v j] eqn:E.
  destruct v as [| |code|a]; simpl.
  - lia.
  - unfold E_IO. lia.
  - pose proof (u_chunk_loop_err _ _ _ _ _ E). lia.
  - lia.
Qed.

Lemma u_read_rc_range : forall tab nm kc ac reqs K,
  0 <= k_sock K < 2 ^ 31 -> 0 <= k_send K < 2 ^ 31 -> 0 <= k_end K < 2 ^ 31 ->
  - 2 ^ 32 < r_rc (read_core tab nm kc ac reqs K) < 2 ^ 32.
Proof.
  intros tab nm kc ac reqs K Hs Hd He. unfold read_core.
  destruct nm as [s|]; [|cbn [r_rc]; unfold E_INVAL; lia]. cbv zeta.
  destruct (Nat.eqb (length s) 0); [cbn [r_rc]; unfold E_INVAL; lia|].
  destruct (index_of tab s =? 0); [cbn [r_rc]; unfold E_NODEV; lia|].
  cbn [r_rc]. apply u_talk_rc_range; assumption.
Qed.

Lemma u_norm_rc_range : forall x, - 2 ^ 32 < x < 2 ^ 32 -> - 2 ^ 32 < norm_rc x < 2 ^ 32.
Proof. intros x H. unfold norm_rc, RC_FAILS. destruct (Z.ltb_spec 0 x); lia. Qed.

Lemma u_norm_rc_zero : forall x, norm_rc x = 0 <-> x = 0.
Proof. intros x. unfold norm_rc, RC_FAILS. destruct (Z.ltb_spec 0 x); lia. Qed.

(* a small signed value is 0 as a 64-bit word exactly when it is 0 *)
Lemma u_w64_zero : forall x, - 2 ^ 63 <= x < 2 ^ 63 -> (Z_to_bv 64 x = Z_to_bv 64 0 <-> x = 0).
Proof.
  intros x Hx. split; [|intros ->; reflexivity].
  intros H. apply (f_equal (@bv_unsigned 64)) in H. rewrite !Z_to_bv_unsigned in H.
  unfold bv_wrap in H. change (bv_modulus 64) with (2 ^ 64) in H. rewrite Z.mod_0_l in H by lia.
  destruct (Z_lt_le_dec x 0).
  - assert (Hm : x mod 2 ^ 64 = x + 2 ^ 64) by (symmetry; apply (Z.mod_unique x (2 ^ 64) (-1)); lia). lia.
  - rewrite Z.mod_small in H by lia. exact H.
Qed.

(* ==========================================================================
   3. One round of the unmark walk
   ========================================================================== *)

Lemma u_uw_cons : forall tab nm rest reqs K, unmark_walk tab (nm :: rest) reqs K =
  if negb (r_rc (read_core tab (Some nm) 0 ALIAS_MAX reqs K) =? 0)
  then unmark_walk tab rest (r_reqs (read_core tab (Some nm) 0 ALIAS_MAX reqs K))
                   (r_state (read_core tab (Some nm) 0 ALIAS_MAX reqs K))
  else if negb (bl_eqb (r_alias (read_core tab (Some nm) 0 ALIAS_MAX reqs K)) S_SERVED)
  then unmark_walk tab rest (r_reqs (read_core tab (Some nm) 0 ALIAS_MAX reqs K))
                   (r_state (read_core tab (Some nm) 0 ALIAS_MAX reqs K))
  else unmark_walk tab rest
         (w_reqs (write_core tab (Some nm) (Some []) (r_reqs (read_core tab (Some nm) 0 ALIAS_MAX reqs K))
                    (r_state (read_core tab (Some nm) 0 ALIAS_MAX reqs K))))
         (w_state (write_core tab (Some nm) (Some []) (r_reqs (read_core tab (Some nm) 0 ALIAS_MAX reqs K))
                    (r_state (read_core tab (Some nm) 0 ALIAS_MAX reqs K)))).
Proof. reflexivity. Qed.

Lemma u_skipn_nth : forall {X} (l : list X) i x, nth_error l i = Some x -> skipn i l = x :: skipn (S i) l.
Proof.
  intros X l. induction l as [|y l IH]; intros [|i] x H; cbn in H |- *; try discriminate.
  - injection H as ->. reflexivity.
  - exact (IH i x H).
Qed.

(* the round that skips the write: the read failed, or the alias is not ours *)
Lemma u_step_skip : forall tab names j nm reqs K U, 0 <= j -> nth_error names (Z.to_nat j) = Some nm ->
  unmark_walk tab (skipn (Z.to_nat j) names) reqs K = U ->
  (r_rc (read_core tab (Some nm) 0 ALIAS_MAX reqs K) <> 0 \/
   bl_eqb (r_alias (read_core tab (Some nm) 0 ALIAS_MAX reqs K)) S_SERVED = false) ->
  unmark_walk tab (skipn (Z.to_nat (j + 1)) names) (r_reqs (read_core tab (Some nm) 0 ALIAS_MAX reqs K))
    (r_state (read_core tab (Some nm) 0 ALIAS_MAX reqs K)) = U.
Proof.
  intros tab names j nm reqs K U Hj Hn UW Hc.
  rewrite (u_skipn_nth _ _ _ Hn), u_uw_cons in UW.
  replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia.
  destruct (r_rc (read_core tab (Some nm) 0 ALIAS_MAX reqs K) =? 0) eqn:E.
  - destruct Hc as [Hc|Hc]; [apply Z.eqb_eq in E; contradiction|].
    rewrite Hc in UW. cbn [negb] in UW. exact UW.
  - cbn [negb] in UW. exact UW.
Qed.

(* the round that writes the empty alias *)
Lemma u_step_write : forall tab names j nm reqs K U, 0 <= j -> nth_error names (Z.to_nat j) = Some nm ->
  unmark_walk tab (skipn (Z.to_nat j) names) reqs K = U ->
  r_rc (read_core tab (Some nm) 0 ALIAS_MAX reqs K) = 0 ->
  bl_eqb (r_alias (read_core tab (Some nm) 0 ALIAS_MAX reqs K)) S_SERVED = true ->
  unmark_walk tab (skipn (Z.to_nat (j + 1)) names)
    (w_reqs (write_core tab (Some nm) (Some []) (r_reqs (read_core tab (Some nm) 0 ALIAS_MAX reqs K))
               (r_state (read_core tab (Some nm) 0 ALIAS_MAX reqs K))))
    (w_state (write_core tab (Some nm) (Some []) (r_reqs (read_core tab (Some nm) 0 ALIAS_MAX reqs K))
               (r_state (read_core tab (Some nm) 0 ALIAS_MAX reqs K)))) = U.
Proof.
  intros tab names j nm reqs K U Hj Hn UW Hr Ha.
  rewrite (u_skipn_nth _ _ _ Hn), u_uw_cons, Hr, Ha in UW. cbn [negb Z.eqb] in UW.
  replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia. exact UW.
Qed.

(* ==========================================================================
   4. The bcmp of the alias buffer against "reac-pw:served" (15 bytes, .str.11)
   ========================================================================== *)

Lemma u_served_len : length S_SERVED = 14%nat.
Proof. reflexivity. Qed.

Lemma u_served_nonul : ~ In (Z_to_bv 8 0) S_SERVED.
Proof.
  intros Hin. assert (H : forallb (fun b : byte => negb (bv_unsigned b =? 0)) S_SERVED = true) by reflexivity.
  rewrite forallb_forall in H. specialize (H _ Hin). discriminate H.
Qed.

Lemma u_bl_eqb_true : forall l1 l2, bl_eqb l1 l2 = true <-> l1 = l2.
Proof.
  induction l1 as [|a l1 IH]; intros [|b l2]; cbn [bl_eqb]; split; intros H; try discriminate; try reflexivity.
  - apply andb_prop in H as [H1 H2]. unfold byte_eqb, bz in H1. apply Z.eqb_eq in H1.
    apply u_byte_eq in H1. subst b. f_equal. apply IH. exact H2.
  - injection H as -> ->. apply andb_true_intro. split; [unfold byte_eqb, bz; apply Z.eqb_refl | apply IH; reflexivity].
Qed.

(* the 15 bytes at the buffer (the alias, its NUL, then any bytes) equal S_SERVED and its NUL exactly when the alias
   is S_SERVED *)
Lemma u_bcmp15 : forall (al rest : list byte), ~ In (Z_to_bv 8 0) al -> (15 <= length al + 1 + length rest)%nat ->
  (forall i, (i < 15)%nat -> nth_error (al ++ Z_to_bv 8 0 :: rest) i = nth_error (S_SERVED ++ [Z_to_bv 8 0]) i) <->
  al = S_SERVED.
Proof.
  intros al rest Hnz Hlen. split.
  - intros H.
    assert (Hl : length al = 14%nat).
    { destruct (Nat.lt_trichotomy (length al) 14) as [Hlt | [Heq | Hgt]]; [exfalso | exact Heq | exfalso].
      - specialize (H (length al) ltac:(lia)).
        rewrite nth_error_app2 in H by lia. rewrite Nat.sub_diag in H. cbn [nth_error] in H.
        rewrite nth_error_app1 in H by (rewrite u_served_len; lia). symmetry in H.
        apply nth_error_In in H. exact (u_served_nonul H).
      - specialize (H 14%nat ltac:(lia)).
        assert (Hr : nth_error (S_SERVED ++ [Z_to_bv 8 0]) 14 = Some (Z_to_bv 8 0)) by reflexivity.
        rewrite Hr in H. rewrite nth_error_app1 in H by lia.
        apply nth_error_In in H. exact (Hnz H). }
    apply nth_error_ext. intros i.
    destruct (Nat.lt_ge_cases i 14) as [Hi | Hi].
    + specialize (H i ltac:(lia)). rewrite nth_error_app1 in H by lia.
      rewrite nth_error_app1 in H by (rewrite u_served_len; lia). exact H.
    + rewrite (proj2 (nth_error_None al i)) by lia. rewrite (proj2 (nth_error_None S_SERVED i)) by
        (rewrite u_served_len; lia). reflexivity.
  - intros -> i Hi. destruct (Nat.lt_ge_cases i 14) as [Hi14 | Hi14].
    + rewrite !nth_error_app1 by (rewrite u_served_len; lia). reflexivity.
    + assert (i = 14%nat) by lia. subst i. rewrite !nth_error_app2 by (rewrite u_served_len; lia).
      rewrite u_served_len. reflexivity.
Qed.

(* ==========================================================================
   5. check_requests' comparison, from the two request lists being one list
   ========================================================================== *)

Lemma u_nth_map_seq : forall {A : Type} (f : nat -> A) n k d, (k < n)%nat -> nth k (map f (seq 0 n)) d = f k.
Proof.
  intros A f n k d Hk. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. reflexivity.
Qed.

Lemma u_slice_len : forall (bs : list byte) a n, 0 <= a -> 0 <= n -> a + n <= Z.of_nat (length bs) ->
  length (slice bs a n) = Z.to_nat n.
Proof. intros bs a n H0 H1 H2. unfold slice. rewrite length_firstn, length_skipn. lia. Qed.

Lemma u_rdn_nonneg : forall bs a n, 0 <= rdn bs a n.
Proof. intros bs a n. unfold rdn. apply bytes_le_to_Z_nonneg. Qed.

Lemma u_requests_are : forall kbs mbs,
  Z.of_nat (length kbs) = NK_SIZE -> Z.of_nat (length mbs) = MD_SIZE ->
  nlk_wf kbs -> model_wf mbs ->
  nk_sent kbs = md_reqs mbs -> requests_are kbs mbs.
Proof.
  intros kbs mbs Lk Lm Wk Wm E.
  pose proof Wk as (_ & _ & Hns & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hslk).
  pose proof Wm as (Hnr & _ & _ & _ & Hslm & _).
  assert (EL : Z.to_nat (nk_n_sent kbs) = Z.to_nat (md_n_req mbs)).
  { apply (f_equal (@length (list byte))) in E. unfold nk_sent, md_reqs in E.
    rewrite !length_map, !length_seq in E. exact E. }
  unfold NL_SENT_MAX in *.
  assert (EN : nk_n_sent kbs = md_n_req mbs) by lia.
  split; [exact EN|]. intros i Hi.
  assert (Ei : nk_sent_one kbs i = md_req_one mbs i).
  { apply (f_equal (fun l => nth (Z.to_nat i) l [])) in E. unfold nk_sent, md_reqs in E.
    rewrite (u_nth_map_seq (fun i => nk_sent_one kbs (Z.of_nat i))) in E by lia.
    rewrite (u_nth_map_seq (fun i => md_req_one mbs (Z.of_nat i))) in E by lia.
    rewrite Z2Nat.id in E by lia. exact E. }
  split; [|exact Ei].
  pose proof (Hslk i Hi) as Lki. pose proof (Hslm i ltac:(lia)) as Lmi.
  unfold nk_sent_one, md_req_one in Ei. apply (f_equal (@length byte)) in Ei.
  unfold NL_SENT_LEN, NK_SENT, MD_REQ, NK_SIZE, MD_SIZE in *.
  rewrite !u_slice_len in Ei by (try lia; try (apply u_rdn_nonneg)).
  apply Z2Nat.inj; [apply u_rdn_nonneg | apply u_rdn_nonneg | exact Ei].
Qed.

(* ==========================================================================
   6. A mark slot of the model block as a C string
   ========================================================================== *)

Section slot.
Variable segs : list Segment.

Lemma u_nul_split : forall l, (nul_at l < length l)%nat ->
  exists rest, l = cstr l ++ [Z_to_bv 8 0] ++ rest /\ ~ In (Z_to_bv 8 0) (cstr l).
Proof.
  induction l as [|b l IH]; intros H; [cbn in H; lia|].
  unfold cstr in *. cbn [nul_at firstn] in *. unfold bz in *.
  destruct (Z.eqb_spec (bv_unsigned b) 0) as [E|E].
  - exists l. cbn [firstn app]. rewrite (u_byte_zero b E). split; [reflexivity | intros []].
  - cbn [length] in H. destruct (IH ltac:(lia)) as (rest & Hl & Hn). exists rest.
    cbn [firstn app]. split; [f_equal; exact Hl|].
    intros [Hb|Hin]; [apply E; rewrite Hb; reflexivity | exact (Hn Hin)].
Qed.

Lemma u_nth_slice : forall (bs : list byte) a n k, 0 <= a -> 0 <= n -> (k < Z.to_nat n)%nat ->
  nth_error (slice bs a n) k = nth_error bs (Z.to_nat a + k).
Proof.
  intros bs a n k Ha Hn Hk. unfold slice. rewrite nth_error_firstn.
  destruct (Nat.ltb_spec k (Z.to_nat n)) as [_|]; [|lia]. rewrite nth_error_skipn. reflexivity.
Qed.

Lemma u_mark_slot : forall m md mbs j, amodel_at segs m md mbs -> model_wf mbs -> 0 <= j < md_n_mark mbs ->
  nth_error (md_marks mbs) (Z.to_nat j) = Some (cstr (slice mbs (MD_MARK + MARK_LEN * j) MARK_LEN)) /\
  acstr_at segs m (md + MD_MARK + MARK_LEN * j) (cstr (slice mbs (MD_MARK + MARK_LEN * j) MARK_LEN)) /\
  (length (cstr (slice mbs (MD_MARK + MARK_LEN * j) MARK_LEN)) < 16)%nat.
Proof.
  intros m md mbs j (((H0 & H1 & HB) & _) & L) MW Hj.
  destruct MW as (_ & _ & _ & _ & _ & R & T). unfold MARKS_MAX in R.
  specialize (T j Hj). unfold MARK_LEN in *. change (Z.to_nat 16) with 16%nat in T.
  unfold MD_SIZE, MD_MARK in *.
  assert (LS : length (slice mbs (8340 + 16 * j) 16) = 16%nat) by (rewrite u_slice_len; lia).
  split; [|split].
  - unfold md_marks. rewrite nth_error_map, nth_error_seq.
    replace (Z.to_nat j <? Z.to_nat (md_n_mark mbs))%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    cbn [option_map Nat.add]. rewrite Z2Nat.id by lia. reflexivity.
  - destruct (u_nul_split (slice mbs (8340 + 16 * j) 16) ltac:(rewrite LS; lia)) as (rest & E & Nn).
    split; [|exact Nn].
    assert (Lc : (length (cstr (slice mbs (8340 + 16 * j) 16)) + 1 <= 16)%nat).
    { apply (f_equal (@length byte)) in E. rewrite LS, !length_app in E. cbn [length] in E. lia. }
    split; [lia|]. rewrite length_app. cbn [length]. split; [lia|].
    intros i Hi. try rewrite length_app in Hi. cbn [length] in Hi.
    assert (Hs : nth_error (cstr (slice mbs (8340 + 16 * j) 16) ++ [Z_to_bv 8 0]) i =
                 nth_error (slice mbs (8340 + 16 * j) 16) i).
    { set (s := slice mbs (8340 + 16 * j) 16) in *. set (c := cstr s) in *.
      rewrite E. rewrite app_assoc.
      rewrite (nth_error_app1 (c ++ [Z_to_bv 8 0]) rest) by (rewrite length_app; cbn [length]; lia).
      reflexivity. }
    change (zb 0) with (Z_to_bv 8 0). rewrite Hs, u_nth_slice by lia.
    replace (md + 8340 + 16 * j + Z.of_nat i) with (md + Z.of_nat (Z.to_nat (8340 + 16 * j) + i)) by lia.
    apply HB. lia.
  - unfold cstr. rewrite length_firstn. lia.
Qed.
End slot.
