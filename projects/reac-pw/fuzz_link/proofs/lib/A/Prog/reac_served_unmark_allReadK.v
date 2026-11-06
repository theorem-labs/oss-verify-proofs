(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/bzip2/bzip2_compress_target/lib/K/A/L_hkit.v, with its module paths and module names changed; 801 of its 858 lines of code are new or changed and 196 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/Prog/reac_served_unmark_all.v, with its module paths and module names changed; 980 of its 1095 lines of code are new or changed and 743 lines of the source are left out. *)
(* reac_served_unmark_all (fuzz_link.asan 0x89ed4) on image A, THE READ PIECE (HEAD c -> MID c / JOIN c), its
   kit: the byte algebra and the model facts the two read files use (reac_served_unmark_allReadA.v,
   reac_served_unmark_allReadB.v), with no symbolic engine.
   - the C string of a mark slot (the plain build's lib/Prog/mk_marks.v slot_cstr, over link_amem.v's abytes),
   - uniqueness and transport of the A views (adapted from reac_link_alias_writeSendA.v),
   - the reader's answer is small and its state keeps the chunks and the end errno (the plain walk
     lib/Prog/reac_served_unmark_all.v: read_rc_range, read_state_ce),
   - the 15-byte compare of a C string against "reac-pw:served" and its NUL (the plain walk's bcmp_served,
     over the bytes a reader sees).

   Proves no function (kind: segment lemma of reac_served_unmark_all's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 PcapImgEnd YK0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit PcapRelro YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
model_decide_c remember_c reac_code_emit_c reac_served_mark_c reac_served_unmark_all_c reac_link_alias_read_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkSide LinkWalkPi LinkWalkCall LinkWalkShadow LinkWalkZsh.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_served_unmark_allDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AF0m AB1v.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   1. Lists of bytes
   ========================================================================== *)

Lemma rk_byte_zero : forall b : byte, bv_unsigned b = 0 -> b = zb 0.
Proof. intros b E. apply bv_eq. rewrite E. reflexivity. Qed.

Lemma rk_no_nul_b : forall l : list byte, existsb (fun b : byte => bv_unsigned b =? 0) l = false -> ~ In (zb 0) l.
Proof.
  intros l H Hin.
  assert (E : existsb (fun b : byte => bv_unsigned b =? 0) l = true)
    by (apply existsb_exists; exists (zb 0); split; [exact Hin | reflexivity]).
  congruence.
Qed.

Lemma rk_S_SERVED_no_nul : ~ In (zb 0) S_SERVED.
Proof. apply rk_no_nul_b. vm_compute. reflexivity. Qed.

Lemma rk_S_SERVED_len : length S_SERVED = 14%nat.
Proof. reflexivity. Qed.

Lemma rk_nth_firstn_gen : forall {A} (l : list A) n i,
  nth_error (firstn n l) i = if (i <? n)%nat then nth_error l i else None.
Proof.
  intros A l. induction l as [|x l IH]; intros [|n] [|i]; cbn; try reflexivity;
    try (rewrite IH; reflexivity);
    repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Qed.

Lemma rk_nth_skipn_gen : forall {A} (l : list A) n i, nth_error (skipn n l) i = nth_error l (n + i).
Proof.
  intros A l. induction l as [|x l IH]; intros n i; destruct n as [|n]; cbn; try reflexivity.
  - destruct i; reflexivity.
  - apply IH.
Qed.

Lemma rk_slice_nth : forall (c : list byte) off len i, 0 <= off -> 0 <= len ->
  nth_error (slice c off len) i =
    if (i <? Z.to_nat len)%nat then nth_error c (Z.to_nat off + i) else None.
Proof. intros c off len i H0 H1. unfold slice. rewrite rk_nth_firstn_gen, rk_nth_skipn_gen. reflexivity. Qed.

Lemma rk_slice_length : forall (c : list byte) off len, 0 <= off -> 0 <= len -> off + len <= Z.of_nat (length c) ->
  length (slice c off len) = Z.to_nat len.
Proof. intros c off len H0 H1 H2. unfold slice. rewrite length_firstn, length_skipn. lia. Qed.

(* a byte list with a NUL holds its C string, then the NUL *)
Lemma rk_cstr_split : forall l, (nul_at l < length l)%nat ->
  exists rest, l = cstr l ++ [zb 0] ++ rest /\ ~ In (zb 0) (cstr l).
Proof.
  induction l as [|b l IH]; intros H; [cbn in H; lia|].
  unfold cstr in *. cbn [nul_at firstn] in *. unfold bz in *.
  destruct (Z.eqb_spec (bv_unsigned b) 0) as [E|E].
  - exists l. cbn [firstn app]. rewrite (rk_byte_zero b E). split; [reflexivity | intros []].
  - cbn [length] in H. destruct (IH ltac:(lia)) as (rest & Hl & Hn). exists rest.
    cbn [firstn app]. split; [f_equal; exact Hl|].
    intros [Hb|Hin]; [apply E; rewrite Hb; reflexivity | exact (Hn Hin)].
Qed.

Lemma rk_skipn_nth : forall {X} (l : list X) i x, nth_error l i = Some x -> skipn i l = x :: skipn (S i) l.
Proof.
  intros X l. induction l as [|y l IH]; intros [|i] x H; cbn in H; try discriminate.
  - injection H as ->. reflexivity.
  - cbn [skipn]. apply IH. exact H.
Qed.

Lemma rk_mk_names_nth : forall gbs i, (i < Z.to_nat (mk_n gbs))%nat ->
  nth_error (mk_names gbs) i = Some (cstr (slice gbs (4 + 16 * Z.of_nat i) 16)).
Proof.
  intros gbs i Hi. unfold mk_names. rewrite nth_error_map, nth_error_seq.
  replace (i <? Z.to_nat (mk_n gbs))%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi). reflexivity.
Qed.

(* the 15-byte compare of a C string with "reac-pw:served" and its NUL, as a reader sees both *)
Lemma rk_served_cmp : forall (rd : Z -> option Z) x y (al : list byte),
  (forall i, (i < length al + 1)%nat -> rd (x + Z.of_nat i) = option_map (fun b : byte => bv_unsigned b) (nth_error (al ++ [zb 0]) i)) ->
  (forall i, (i < 15)%nat -> rd (y + Z.of_nat i) = option_map (fun b : byte => bv_unsigned b) (nth_error (S_SERVED ++ [zb 0]) i)) ->
  ~ In (zb 0) al ->
  ((forall i, 0 <= i < 15 -> rd (x + i) = rd (y + i)) <-> al = S_SERVED).
Proof.
  intros rd x y al HX HY HN. split.
  - intros HE.
    assert (HE' : forall i, (i < 15)%nat -> rd (x + Z.of_nat i) = rd (y + Z.of_nat i)) by (intros i Hi; apply HE; lia).
    destruct (lt_eq_lt_dec (length al) 14) as [[Hlt|Heq]|Hgt].
    + exfalso. specialize (HE' (length al) ltac:(lia)).
      rewrite (HX (length al) ltac:(lia)), (HY (length al) ltac:(lia)) in HE'.
      rewrite (nth_error_app2 al [zb 0]) in HE' by lia. rewrite Nat.sub_diag in HE'. cbn [nth_error] in HE'.
      rewrite (nth_error_app1 S_SERVED [zb 0]) in HE' by (rewrite rk_S_SERVED_len; lia).
      destruct (nth_error S_SERVED (length al)) as [b|] eqn:Eb; cbn [option_map] in HE'; [|discriminate].
      injection HE' as HE'. apply rk_S_SERVED_no_nul.
      assert (b = zb 0) by (apply rk_byte_zero; rewrite <- HE'; reflexivity). subst b.
      exact (nth_error_In _ _ Eb).
    + apply nth_error_ext. intros i.
      destruct (Nat.lt_ge_cases i 14) as [Hi|Hi].
      * specialize (HE' i ltac:(lia)). rewrite (HX i ltac:(lia)), (HY i ltac:(lia)) in HE'.
        rewrite (nth_error_app1 al [zb 0]) in HE' by lia.
        rewrite (nth_error_app1 S_SERVED [zb 0]) in HE' by (rewrite rk_S_SERVED_len; lia).
        destruct (nth_error al i) as [a|] eqn:Ea; destruct (nth_error S_SERVED i) as [b|] eqn:Eb;
          cbn [option_map] in HE'; try discriminate; [|reflexivity].
        injection HE' as HE'. f_equal. apply bv_eq. exact HE'.
      * rewrite (proj2 (nth_error_None al i)) by lia.
        rewrite (proj2 (nth_error_None S_SERVED i)) by (rewrite rk_S_SERVED_len; lia). reflexivity.
    + exfalso. specialize (HE' 14%nat ltac:(lia)).
      rewrite (HX 14%nat ltac:(lia)), (HY 14%nat ltac:(lia)) in HE'.
      rewrite (nth_error_app1 al [zb 0]) in HE' by lia.
      change (nth_error (S_SERVED ++ [zb 0]) 14) with (Some (zb 0)) in HE'.
      destruct (nth_error al 14) as [a|] eqn:Ea; cbn [option_map] in HE'; [|discriminate].
      injection HE' as HE'. apply HN.
      assert (a = zb 0) by (apply rk_byte_zero; rewrite HE'; reflexivity). subst a.
      exact (nth_error_In _ _ Ea).
  - intros -> i Hi.
    pose proof (HX (Z.to_nat i) ltac:(rewrite rk_S_SERVED_len; lia)) as A.
    pose proof (HY (Z.to_nat i) ltac:(lia)) as C.
    rewrite Z2Nat.id in A, C by lia. rewrite A, C. reflexivity.
Qed.

(* ==========================================================================
   2. The reader's answer and state (the plain walk's lemmas)
   ========================================================================== *)

Lemma rk_nk_kstate_eq : forall kbs K, nk_chunks kbs = k_chunks K -> nk_next kbs = Z.of_nat (k_next K) ->
  nk_end_errno kbs = k_end K -> nk_socket_errno kbs = k_sock K -> nk_send_errno kbs = k_send K ->
  nk_kstate kbs = K.
Proof.
  intros kbs [c n e s d] H1 H2 H3 H4 H5. cbn [k_chunks k_next k_end k_sock k_send] in *. unfold nk_kstate.
  rewrite H1, H2, H3, H4, H5, Nat2Z.id. reflexivity.
Qed.

Lemma rk_talk_after_ce : forall K, k_chunks (talk_after K) = k_chunks K /\ k_end (talk_after K) = k_end K.
Proof.
  intros K. unfold talk_after, talk_core.
  destruct (negb (k_sock K =? 0)); [split; reflexivity|].
  destruct (negb (k_send K =? 0)); [split; reflexivity|].
  destruct (chunk_loop (S (length (k_chunks K))) (k_chunks K) (k_next K)) as [v j].
  destruct v; split; reflexivity.
Qed.

Lemma rk_read_state_ce : forall tab nm kc ac reqs K,
  k_chunks (r_state (read_core tab nm kc ac reqs K)) = k_chunks K /\
  k_end (r_state (read_core tab nm kc ac reqs K)) = k_end K.
Proof.
  intros. unfold read_core. destruct nm as [s|]; [|split; reflexivity]. cbv zeta.
  destruct (Nat.eqb (length s) 0); [split; reflexivity|].
  destruct (index_of tab s =? 0); [split; reflexivity|]. apply rk_talk_after_ce.
Qed.

Lemma rk_rd32_range : forall c off, 0 <= rd32 c off < 2 ^ 32.
Proof.
  intros c off. unfold rd32, rdn. pose proof (bytes_le_to_Z_nonneg (slice c off 4)) as H0.
  pose proof (bytes_le_to_Z_bound (slice c off 4)) as H1.
  assert (L : (length (slice c off 4) <= 4)%nat) by (unfold slice; rewrite length_firstn; lia).
  assert (P : 2 ^ (8 * Z.of_nat (length (slice c off 4))) <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
  set (q := 2 ^ (8 * Z.of_nat (length (slice c off 4)))) in *. lia.
Qed.

Lemma rk_rd32s_range : forall c off, - 2 ^ 31 <= rd32s c off < 2 ^ 31.
Proof.
  intros c off. unfold rd32s. cbv zeta. pose proof (rk_rd32_range c off) as R.
  destruct (Z.ltb_spec (rd32 c off) (2 ^ 31)); lia.
Qed.

Lemma rk_msg_scan_err : forall fuel c off left code, msg_scan fuel c off left = NlErr code ->
  - 2 ^ 31 <= code < 2 ^ 31.
Proof.
  induction fuel as [|f IH]; intros c off left code H; cbn [msg_scan] in H; [discriminate|].
  destruct (left <? NL_HDR); [discriminate|].
  destruct ((rd32 c off <? NL_HDR) || (left <? rd32 c off)); [discriminate|].
  destruct (rd16 c (off + 4) =? NL_ERROR).
  - destruct (rd32 c off <? NL_HDR + NL_ERR_BODY); [discriminate|]. injection H as <-. apply rk_rd32s_range.
  - destruct (rd16 c (off + 4) =? RTM_NEWLINK); [discriminate|]. exact (IH _ _ _ _ H).
Qed.

Lemma rk_chunk_loop_err : forall fuel cs i code j, chunk_loop fuel cs i = (NlErr code, j) ->
  - 2 ^ 31 <= code < 2 ^ 31.
Proof.
  induction fuel as [|f IH]; intros cs i code j H; cbn [chunk_loop] in H; [discriminate|].
  destruct (nth_error cs i) as [c|]; [|discriminate].
  destruct (chunk_walk c) as [| |code'|a] eqn:E.
  - exact (IH _ _ _ _ H).
  - discriminate.
  - injection H as <- _. unfold chunk_walk in E. exact (rk_msg_scan_err _ _ _ _ _ E).
  - discriminate.
Qed.

Lemma rk_talk_rc_range : forall K, 0 <= k_sock K < 2 ^ 31 -> 0 <= k_send K < 2 ^ 31 -> 0 <= k_end K < 2 ^ 31 ->
  - 2 ^ 32 < talk_rc_lib K < 2 ^ 32.
Proof.
  intros K Hs Hd He. unfold talk_rc_lib, talk_core.
  destruct (negb (k_sock K =? 0)); [cbn [fst]; lia|].
  destruct (negb (k_send K =? 0)); [cbn [fst]; lia|].
  destruct (chunk_loop (S (length (k_chunks K))) (k_chunks K) (k_next K)) as [v j] eqn:E.
  destruct v as [| |code|a]; cbn [fst].
  - lia.
  - unfold E_IO. lia.
  - pose proof (rk_chunk_loop_err _ _ _ _ _ E). lia.
  - lia.
Qed.

Lemma rk_read_rc_range : forall tab nm kc ac reqs K,
  0 <= k_sock K < 2 ^ 31 -> 0 <= k_send K < 2 ^ 31 -> 0 <= k_end K < 2 ^ 31 ->
  - 2 ^ 32 < r_rc (read_core tab nm kc ac reqs K) < 2 ^ 32.
Proof.
  intros tab nm kc ac reqs K Hs Hd He. unfold read_core.
  destruct nm as [s|]; [|cbn [r_rc]; unfold E_INVAL; lia]. cbv zeta.
  destruct (Nat.eqb (length s) 0); [cbn [r_rc]; unfold E_INVAL; lia|].
  destruct (index_of tab s =? 0); [cbn [r_rc]; unfold E_NODEV; lia|].
  cbn [r_rc]. apply rk_talk_rc_range; assumption.
Qed.

(* the answer word is 0 exactly when the answer is *)
Lemma rk_w64_small_zero : forall z, - 2 ^ 32 < z < 2 ^ 32 -> w64 z = w64 0 -> z = 0.
Proof.
  intros z Hz E. apply (f_equal (@bv_unsigned 64)) in E. unfold w64 in E.
  rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 64) with (2 ^ 64) in E.
  change (0 mod 2 ^ 64) with 0 in E. lia.
Qed.

(* ==========================================================================
   3. The A views: uniqueness, transport, the C string of a mark slot
   ========================================================================== *)
Section s.
Variable segs : list Segment.

Lemma rk_lb_inj : forall (n : nat) (p1 p2 : Z),
  (forall k, (k < n)%nat ->
     Z_to_bv 8 (Z.shiftr (p1 mod 2 ^ (8 * Z.of_nat n)) (8 * Z.of_nat k) mod 256) =
     Z_to_bv 8 (Z.shiftr (p2 mod 2 ^ (8 * Z.of_nat n)) (8 * Z.of_nat k) mod 256)) ->
  p1 mod 2 ^ (8 * Z.of_nat n) = p2 mod 2 ^ (8 * Z.of_nat n).
Proof.
  intros n p1 p2 H. apply Z.bits_inj'. intros i Hi.
  destruct (Z_lt_le_dec i (8 * Z.of_nat n)) as [Hl|Hl].
  - pose proof (Z.div_mod i 8 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound i 8 ltac:(lia)) as Hr.
    set (q := i / 8) in *. set (r := i mod 8) in *. clearbody q r.
    assert (Hq : 0 <= q) by lia.
    assert (Hk : (Z.to_nat q < n)%nat) by lia.
    specialize (H (Z.to_nat q) Hk).
    apply (f_equal bv_unsigned) in H. rewrite !Z_to_bv_unsigned in H. unfold bv_wrap in H.
    change (bv_modulus 8) with 256 in H. rewrite !Z.mod_mod in H by lia.
    rewrite Z2Nat.id in H by exact Hq.
    apply (f_equal (fun z => Z.testbit z r)) in H. cbv beta in H.
    change 256 with (2 ^ 8) in H. rewrite !Z.mod_pow2_bits_low in H by lia.
    rewrite !Z.shiftr_spec in H by lia.
    replace (r + 8 * q) with i in H by lia. exact H.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma rk_vm_unique : forall m a (n : nat) v1 v2, val_mem segs m a n v1 -> val_mem segs m a n v2 ->
  v1 mod 2 ^ (8 * Z.of_nat n) = v2 mod 2 ^ (8 * Z.of_nat n).
Proof.
  intros m a n v1 v2 H1 H2. apply rk_lb_inj. intros k Hk.
  pose proof (eq_trans (eq_sym (H1 k Hk)) (H2 k Hk)) as E.
  exact (f_equal (fun o : option byte => match o with Some b => b | None => Z_to_bv 8 0 end) E).
Qed.

Lemma rk_abytes_unique : forall m a l1 l2,
  abytes segs m a l1 -> abytes segs m a l2 -> length l1 = length l2 -> l1 = l2.
Proof.
  intros m a l1 l2 (_ & _ & H1) (_ & _ & H2) L. apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length l1)) as [Hi|Hi].
  - rewrite <- (H1 i Hi), <- (H2 i ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None l1 i) Hi), (proj2 (nth_error_None l2 i) ltac:(lia)). reflexivity.
Qed.

Lemma rk_acstr_short : forall m a s1 s2, acstr_at segs m a s1 -> acstr_at segs m a s2 ->
  (length s1 < length s2)%nat -> False.
Proof.
  intros m a s1 s2 [(_ & _ & B1) _] [(_ & _ & B2) N2] L.
  assert (E1 : mbyte segs m (a + Z.of_nat (length s1)) = Some (zb 0)).
  { rewrite (B1 (length s1)) by (rewrite length_app; cbn [length]; lia).
    rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
  assert (E2 : mbyte segs m (a + Z.of_nat (length s1)) = nth_error s2 (length s1)).
  { rewrite (B2 (length s1)) by (rewrite length_app; cbn [length]; lia).
    apply nth_error_app1. exact L. }
  apply N2. apply (nth_error_In s2 (length s1)). rewrite <- E2. exact E1.
Qed.

Lemma rk_acstr_unique : forall m a s1 s2, acstr_at segs m a s1 -> acstr_at segs m a s2 -> s1 = s2.
Proof.
  intros m a s1 s2 H1 H2.
  destruct (Nat.lt_trichotomy (length s1) (length s2)) as [L|[L|L]].
  - exfalso. exact (rk_acstr_short m a s1 s2 H1 H2 L).
  - destruct H1 as [B1 _]. destruct H2 as [B2 _].
    apply (app_inv_tail [zb 0]). apply (rk_abytes_unique m a); [exact B1 | exact B2 |].
    rewrite !length_app, L. reflexivity.
  - exfalso. exact (rk_acstr_short m a s2 s1 H2 H1 L).
Qed.

Lemma rk_anlk_unique : forall m g b1 b2, anlk_at segs m g b1 -> anlk_at segs m g b2 -> b1 = b2.
Proof.
  intros m g b1 b2 [[B1 _] L1] [[B2 _] L2]. apply (rk_abytes_unique m g); [exact B1 | exact B2 | lia].
Qed.

Lemma rk_au64_unique : forall m a p1 p2, au64_at segs m a p1 -> au64_at segs m a p2 ->
  p1 mod 2 ^ 64 = p2 mod 2 ^ 64.
Proof.
  intros m a p1 p2 H1 H2. pose proof (rk_vm_unique m a 8 p1 p2 H1 H2) as E.
  change (8 * Z.of_nat 8) with 64 in E. exact E.
Qed.

Lemma rk_au32_small_unique : forall m a x1 x2, au32_at segs m a x1 -> au32_at segs m a x2 ->
  0 <= x1 < 2 ^ 31 -> 0 <= x2 < 2 ^ 31 -> x1 = x2.
Proof.
  intros m a x1 x2 H1 H2 R1 R2. pose proof (rk_vm_unique m a 4 x1 x2 H1 H2) as E.
  change (8 * Z.of_nat 4) with 32 in E. rewrite !Z.mod_small in E by lia. exact E.
Qed.

Lemma rk_acstr_range : forall m p s, acstr_at segs m p s -> 0 <= p /\ p + Z.of_nat (length s) + 1 <= 2 ^ 64.
Proof.
  intros m p s [(Ha & Hl & _) _]. rewrite length_app in Hl. cbn [length] in Hl. lia.
Qed.

Lemma rk_aiftab_unique : forall m bs tab1 tab2,
  aiftab_at segs m LA_G_NL bs tab1 -> aiftab_at segs m LA_G_NL bs tab2 -> tab1 = tab2.
Proof.
  intros m bs tab1 tab2 (L1 & _ & E1) (L2 & _ & E2).
  assert (L : length tab1 = length tab2) by lia.
  apply nth_error_ext. intros i.
  destruct (nth_error tab1 i) as [[n1 x1]|] eqn:H1; destruct (nth_error tab2 i) as [[n2 x2]|] eqn:H2.
  - destruct (E1 i n1 x1 H1) as (R1 & p1 & P1 & _ & C1 & I1).
    destruct (E2 i n2 x2 H2) as (R2 & p2 & P2 & _ & C2 & I2).
    pose proof (rk_au64_unique _ _ _ _ P1 P2) as Ep.
    pose proof (rk_acstr_range _ _ _ C1). pose proof (rk_acstr_range _ _ _ C2).
    rewrite !Z.mod_small in Ep by lia. subst p2.
    rewrite (rk_acstr_unique _ _ _ _ C1 C2).
    rewrite (rk_au32_small_unique _ _ _ _ I1 I2 R1 R2). reflexivity.
  - exfalso. apply nth_error_None in H2. assert (i < length tab1)%nat by (apply nth_error_Some; congruence). lia.
  - exfalso. apply nth_error_None in H1. assert (i < length tab2)%nat by (apply nth_error_Some; congruence). lia.
  - reflexivity.
Qed.

Lemma rk_abytes_move : forall (m m' : word -> option byte) a bs,
  abytes segs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> mbyte segs m' x = mbyte segs m x) ->
  abytes segs m' a bs.
Proof.
  intros m m' a bs (Ha & Hl & H) Hk. split; [exact Ha|]. split; [exact Hl|].
  intros i Hi. rewrite (Hk (a + Z.of_nat i)) by lia. exact (H i Hi).
Qed.

Lemma rk_acstr_move : forall m m' p s, acstr_at segs m p s ->
  (forall x, p <= x <= p + Z.of_nat (length s) -> mbyte segs m' x = mbyte segs m x) -> acstr_at segs m' p s.
Proof.
  intros m m' p s [Bs N] Hk. split; [|exact N]. apply (rk_abytes_move m m' p _ Bs).
  intros x Hx. apply Hk. rewrite length_app in Hx. cbn [length] in Hx. lia.
Qed.

Lemma rk_anlk_move : forall m m' bs, anlk_at segs m LA_G_NL bs ->
  (forall x, LA_G_NL <= x < LA_G_NL + NK_SIZE -> mbyte segs m' x = mbyte segs m x) ->
  (forall x, LA_G_NL <= x < LA_G_NL + NK_SIZE -> writable_at segs m' x) -> anlk_at segs m' LA_G_NL bs.
Proof.
  intros m m' bs [[U R] L] Hk Hw. split; [|exact L]. split.
  - apply (rk_abytes_move m m' LA_G_NL bs U). intros x Hx. apply Hk. lia.
  - intros i Hi. apply Hw. lia.
Qed.

(* the table at m', when its cells are m's and the string each cell names at m is kept *)
Lemma rk_aiftab_keep : forall m m' bs bs' tab,
  aiftab_at segs m LA_G_NL bs tab -> nk_n_if bs' = nk_n_if bs ->
  (forall x, LA_G_NL + NK_IF_NAME <= x < LA_G_NL + NK_IF_NAME + 8 * Z.of_nat (length tab) ->
     mbyte segs m' x = mbyte segs m x) ->
  (forall x, LA_G_NL + NK_IF_INDEX <= x < LA_G_NL + NK_IF_INDEX + 4 * Z.of_nat (length tab) ->
     mbyte segs m' x = mbyte segs m x) ->
  (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
     au64_at segs m (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> 0 <= p < 2 ^ 64 ->
     forall x, p <= x <= p + Z.of_nat (length n2) -> mbyte segs m' x = mbyte segs m x) ->
  aiftab_at segs m' LA_G_NL bs' tab.
Proof.
  intros m m' bs bs' tab (L & L80 & E) Hn DN DI DS.
  split; [rewrite Hn; exact L|]. split; [exact L80|]. intros i n2 ix Hi.
  destruct (E i n2 ix Hi) as (R & p & P & Pz & C & I). split; [exact R|].
  assert (Li : (i < length tab)%nat) by (apply nth_error_Some; congruence).
  exists p. split; [|split; [exact Pz|split]].
  - unfold au64_at, val_mem in *. intros k Hk.
    rewrite (DN (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i + Z.of_nat k)) by lia. exact (P k Hk).
  - pose proof (rk_acstr_range m p n2 C) as Rp.
    apply (rk_acstr_move m m' p n2 C). exact (DS i n2 ix p Hi P ltac:(lia)).
  - unfold au32_at, val_mem in *. intros k Hk.
    rewrite (DI (LA_G_NL + NK_IF_INDEX + 4 * Z.of_nat i + Z.of_nat k)) by lia. exact (I k Hk).
Qed.

Lemma rk_abytes_slice : forall m a (c : list byte) off len, abytes segs m a c -> 0 <= off -> 0 <= len ->
  off + len <= Z.of_nat (length c) -> abytes segs m (a + off) (slice c off len).
Proof.
  intros m a c off len (Ha & Hl & H) H0 H1 H2. pose proof (rk_slice_length c off len H0 H1 H2) as LS.
  split; [lia|]. split; [rewrite LS; lia|]. intros i Hi. rewrite LS in Hi. rewrite rk_slice_nth by lia.
  replace (i <? Z.to_nat len)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  rewrite <- H by lia. f_equal. lia.
Qed.

Lemma rk_abytes_prefix : forall m a l1 l2, abytes segs m a (l1 ++ l2) -> abytes segs m a l1.
Proof.
  intros m a l1 l2 (Ha & Hl & H). rewrite length_app in Hl. split; [exact Ha|]. split; [lia|].
  intros i Hi. rewrite (H i) by (rewrite length_app; lia). apply nth_error_app1. exact Hi.
Qed.

(* THE C STRING OF A MARK SLOT: name i of a well-formed block, then its NUL *)
Lemma rk_slot_cstr : forall m a gbs i, abytes segs m a gbs -> Z.of_nat (length gbs) = 516 -> marks_wf gbs ->
  0 <= i < mk_n gbs ->
  acstr_at segs m (a + (4 + 16 * i)) (cstr (slice gbs (4 + 16 * i) 16))
  /\ (length (cstr (slice gbs (4 + 16 * i) 16)) <= 15)%nat.
Proof.
  intros m a gbs i Bk L [R T] Hi. unfold MARKS_MAX in R.
  specialize (T i Hi). unfold MK_NAME, MARK_LEN in T. change (Z.to_nat 16) with 16%nat in T.
  pose proof (rk_abytes_slice m a gbs (4 + 16 * i) 16 Bk ltac:(lia) ltac:(lia) ltac:(lia)) as BS.
  assert (LS : length (slice gbs (4 + 16 * i) 16) = 16%nat) by (rewrite rk_slice_length by lia; reflexivity).
  destruct (rk_cstr_split (slice gbs (4 + 16 * i) 16) ltac:(rewrite LS; lia)) as (rest & E & N).
  split.
  - split; [|exact N]. rewrite E in BS. rewrite app_assoc in BS. exact (rk_abytes_prefix _ _ _ _ BS).
  - unfold cstr. rewrite length_firstn. lia.
Qed.

(* the bytes a C string covers, as a reader sees them *)
Lemma rk_acstr_rd : forall (H : word -> bool) (m : word -> option byte) p s,
  acstr_at segs (mrestrict H m) p s ->
  forall i, (i < length s + 1)%nat ->
    aview segs H m (p + Z.of_nat i) = option_map (fun b : byte => bv_unsigned b) (nth_error (s ++ [zb 0]) i).
Proof.
  intros H m p s [(_ & _ & Bs) _] i Hi. unfold aview. rewrite (Bs i) by (rewrite length_app; cbn [length]; lia).
  reflexivity.
Qed.

(* a word read is the read it was when its eight bytes did not change *)
Lemma rk_rdword_eq : forall (rd rd' : reader) a,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = rdword rd a.
Proof.
  intros rd rd' a H.
  assert (E0 : rd' a = rd a) by (specialize (H 0 ltac:(lia)); rewrite Z.add_0_r in H; exact H).
  unfold rdword. rewrite E0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

(* the read-only image facts are the facts they were when every read-only byte did not change *)
Lemma rk_arodata_eq : forall rlo rhi B (rd rd' : reader),
  YC20.arodata_okP segs rlo rhi B rd -> (forall a, YC20.in_roP segs rlo rhi a -> rd' a = rd a) ->
  YC20.arodata_okP segs rlo rhi B rd'.
Proof. intros rlo rhi B rd rd' H Hk a Hro Ho He. rewrite (Hk a Hro). exact (H a Hro Ho He). Qed.

(* a present byte is seen *)
Lemma rk_aview_present : forall (H : word -> bool) (m : word -> option byte) a,
  apresent H m a -> aview segs H m a <> None.
Proof.
  intros H m a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
Qed.

(* two intervals one of which has no point in the other are apart *)
Lemma rk_apart_of_pts : forall a n b k, 0 < n -> 0 < k ->
  (forall x, a <= x < a + n -> ~ (b <= x < b + k)) -> apart a n b k.
Proof.
  intros a n b k Hn Hk H. unfold apart.
  destruct (Z_le_gt_dec (a + n) b) as [H1|H1]; [left; exact H1|].
  destruct (Z_le_gt_dec (b + k) a) as [H2|H2]; [right; exact H2|].
  exfalso. apply (H (Z.max a b)); lia.
Qed.
End s.

(* addressability and a visible shadow hull of a range hold of every sub-range *)
Lemma rk_ra_sub : forall (rd : reader) p n p' n', range_addressable rd SHADOW_OFF p n -> p <= p' -> p' + n' <= p + n ->
  range_addressable rd SHADOW_OFF p' n'.
Proof. intros rd p n p' n' H H1 H2 x Hx. apply H. lia. Qed.

Lemma rk_hull_sub : forall (rd : reader) p n p' n', shadow_hull_vis rd p n -> p <= p' -> p' + n' <= p + n -> 0 < n' ->
  shadow_hull_vis rd p' n'.
Proof.
  intros rd p n p' n' H H1 H2 H3 s Hs. apply H.
  unfold shadow_addr, SHADOW_OFF in *. lia.
Qed.

(* an interval of a non-writable segment, as one boolean *)
Definition rk_ro_b (segs : list Segment) (lo hi : Z) : bool :=
  existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? lo) &&
                    (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) segs.

Lemma rk_ro_of_b : forall segs rlo rhi lo hi a, rk_ro_b segs lo hi = true -> lo <= a < hi ->
  YC20.in_roP segs rlo rhi a.
Proof.
  intros segs rlo rhi lo hi a H Ha. unfold rk_ro_b in H. apply existsb_exists in H as (s & Hs & Hb).
  apply andb_true_iff in Hb as [Hb H2]. apply andb_true_iff in Hb as [H0 H1].
  apply negb_true_iff in H0. apply Z.leb_le in H1. apply Z.leb_le in H2.
  left. exists s. split; [exact Hs|]. split; [exact H0 | lia].
Qed.

Ltac rk_consts :=
  let C := fresh "C" in
  pose proof asan_consts as C; destruct C as ((?C & ?C) & ?C & ?C & ?C & ?C);
  unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd in *.

(* ==========================================================================
   4. The walk's state at the read piece's cuts
   ========================================================================== *)
(* every section lemma below takes every section variable, in declaration order: the read files apply them by
   position *)
(* ---- machine-state shape, the model's descriptors, presence, words; the two run tactics ---- *)
Lemma urd_ms_eta `{fx : YK11.FPState} : forall ms : machine_state,
  ms_fregs ms = fp_regs -> ms_svc_pending ms = None -> ms_resv ms = None -> ms_fcsr ms = fp_csr ->
  ms = mkst (ms_regs ms) (ms_pc_val ms) (ms_mem ms) (ms_rom ms).
Proof. intros [] H1 H2 H3 H4; cbn in *; subst; reflexivity. Qed.

Lemma urd_wvb_fds_fs : forall l X m, m_fds (with_vm_backing l X m) = m_fds m /\ m_fs (with_vm_backing l X m) = m_fs m.
Proof. intros l X []. split; reflexivity. Qed.

Lemma urd_apresent_grows : forall (H : word -> bool) (m m' : word -> option byte) a,
  mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a HG [Hh [b Hb]]. split; [exact Hh|].
specialize (HG (Z_to_bv 64 a)). unfold mrestrict in HG. rewrite Hh in HG. rewrite Hb in HG.
destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; apply HG; [discriminate | reflexivity]].
Qed.

(* a word that is w64 v, for v a 64-bit value, reads back as v *)
Lemma urd_bvu : forall (x : word) v, x = w64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned x = v.
Proof. intros x v -> Hv. unfold w64. apply unsigned_lit_small. exact Hv. Qed.

(* ---- the run tactic (reac_link_alias_writeExit.v aw_run_call) ---- *)
Ltac urd_run_call RUNC HS HJ :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
    lazymatch type of RUNC with
    | forall W n E ss ss' s ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q, _ -> _ -> sym_runN_pi ?tpi n ss = _ -> _ =>
      let r := eval vm_compute in (sym_runN_pi tpi FUEL ss) in
      lazymatch r with
      | (?ss', PRS_call ?s) =>
        let Hrun := fresh "Hrun" in
        assert (Hrun : sym_runN_pi tpi FUEL ss = (ss', PRS_call s)) by (vm_compute; reflexivity);
        let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI end in
        eapply (RUNC W FUEL E ss ss' s ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun HJ);
        [ clear Hrun | clear Hrun ]
      | ?other => fail "urd_run_call: the run does not stop at a call:" other
      end
    end
  end.

Definition urb_ss (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).

(* a run to a listing offset that stops at no call (urd_run_call for paj_run_to_plain_x) *)
Ltac urb_run_to RUNTO HS HJ stop :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
    lazymatch type of RUNTO with
    | forall W n stop E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q, _ -> _ -> sym_run_toN_pi ?tpi n stop ss = _ -> _ =>
      let r := eval vm_compute in (sym_run_toN_pi tpi FUEL stop ss) in
      lazymatch r with
      | (?ss', ?st) =>
        let Hrun := fresh "Hrun" in
        assert (Hrun : sym_run_toN_pi tpi FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
        let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI end in
        eapply (RUNTO W FUEL stop E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun I HJ);
        [ clear Hrun | clear Hrun ]
      end
    end
  end.

(* the callee-saved registers of a symbolic state are the entry atoms *)
Ltac urb_cs_tac :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; unfold acallee_saved in Hr;
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
     r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  clear Hr;
  repeat (destruct Hr' as [Hr0 | Hr']; [subst r; vm_compute; reflexivity|]);
  subst r; vm_compute; reflexivity.

Local Set Default Proof Using "All".
Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).

Lemma urb_ew : forall (regs : bvmap 5 word) n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (Eimg (Ereg regs [])) n = getr regs r.
Proof.
  intros regs n r Hr. rewrite Eimg_low; [exact (ew_Ereg_nat _ _ n r Hr)|].
  pose proof (u5_range r) as Hu. unfold A_TEXT. lia.
Qed.

(* `bnez a0` at a register-only state *)
Lemma urb_bt : forall (regs : bvmap 5 word),
  branch_taken BC_NE (sv_denot (Eimg (Ereg regs [])) (SOff 10 0)) (sv_denot (Eimg (Ereg regs [])) (SLit 0)) =
  negb (bv_unsigned (getr regs 10) =? 0).
Proof.
  intros regs. cbn [sv_denot]. rewrite branch_ne_lit by lia.
  rewrite (urb_ew regs 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma urb_bt_true : forall (regs : bvmap 5 word),
  branch_taken BC_NE (sv_denot (Eimg (Ereg regs [])) (SOff 10 0)) (sv_denot (Eimg (Ereg regs [])) (SLit 0)) = true ->
  getr regs 10 <> w64 0.
Proof.
  intros regs H E. rewrite urb_bt, E in H. unfold w64 in H. rewrite unsigned_lit_small in H by lia. discriminate H.
Qed.

Lemma urb_bt_false : forall (regs : bvmap 5 word),
  branch_taken BC_NE (sv_denot (Eimg (Ereg regs [])) (SOff 10 0)) (sv_denot (Eimg (Ereg regs [])) (SLit 0)) = false ->
  getr regs 10 = w64 0.
Proof.
  intros regs H. rewrite urb_bt in H. apply negb_false_iff, Z.eqb_eq in H.
  apply bv_eq. unfold w64. rewrite H, unsigned_lit_small by lia. reflexivity.
Qed.

(* the register-only state at a listing offset *)
Lemma urb_entry : forall (H : word -> bool) regs pc mem,
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (urb_ss pc) (restrict H (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
  intros H regs pc mem. rewrite restrict_mkst_fx. unfold urb_ss. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. exact I.
  - cbn. repeat split.
Qed.

(* a run that keeps every callee-saved register's entry atom keeps the register *)
Lemma urb_cs_pi : forall (H : word -> bool) regs ss ms,
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) ss (restrict H ms) ->
  (forall r, acallee_saved r -> sr_get (ss_regs ss) (Z_to_bv 5 r) = SOff (Z.to_nat r) 0) ->
  aregs_preserved regs (ms_regs ms).
Proof.
  intros H regs ss ms HS Hsr r Hr. rewrite (st_ok_pi_restrict_reg H _ ss ms _ HS), (Hsr r Hr). cbn [sv_denot].
  assert (Hr5 : 0 <= r < 32) by (unfold acallee_saved in Hr; lia).
  rewrite (urb_ew regs (Z.to_nat r) (Z_to_bv 5 r))
    by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 5) with 32; rewrite Z.mod_small by lia; lia).
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma urb_cs_abs : forall (H : word -> bool) regs ss ms,
  st_ok SEGS (Eimg (Ereg regs [])) ss (restrict H ms) ->
  (forall r, acallee_saved r -> sr_get (ss_regs ss) (Z_to_bv 5 r) = SOff (Z.to_nat r) 0) ->
  aregs_preserved regs (ms_regs ms).
Proof.
  intros H regs ss ms HS Hsr r Hr. rewrite (st_ok_restrict_reg SEGS H _ ss ms _ HS), (Hsr r Hr). cbn [sv_denot].
  assert (Hr5 : 0 <= r < 32) by (unfold acallee_saved in Hr; lia).
  rewrite (urb_ew regs (Z.to_nat r) (Z_to_bv 5 r))
    by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 5) with 32; rewrite Z.mod_small by lia; lia).
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma urb_cs_trans : forall r1 r2 r3, aregs_preserved r1 r2 -> aregs_preserved r2 r3 -> aregs_preserved r1 r3.
Proof. intros r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.

(* every byte of a C string and its NUL is seen *)
Lemma urb_cstr_vis : forall (H : word -> bool) (m : word -> option byte) p s,
  acstr_at SEGS (mrestrict H m) p s -> forall a, p <= a <= p + Z.of_nat (length s) -> aview SEGS H m a <> None.
Proof.
  intros H m p s HC a Ha. replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia.
  rewrite (rk_acstr_rd SEGS H m p s HC (Z.to_nat (a - p)) ltac:(lia)).
  destruct (nth_error (s ++ [zb 0]) (Z.to_nat (a - p))) eqn:E; [discriminate|].
  apply nth_error_None in E. rewrite length_app in E. cbn [length] in E. lia.
Qed.

Lemma urb_acstr_eq : forall (H : word -> bool) (m m' : word -> option byte) p s,
  (forall a, aview SEGS H m' a = aview SEGS H m a) -> acstr_at SEGS (mrestrict H m) p s -> acstr_at SEGS (mrestrict H m') p s.
Proof.
  intros H m m' p s Heq HC. apply (rk_acstr_move SEGS (mrestrict H m) (mrestrict H m') p s HC).
  intros a _. apply (YCbq.mbyte_of_aview SEGS H H m m' a). apply Heq.
Qed.
End p.


Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
(* AR's laws (the frame); the start-up symbols (AF0m.v PcapSyms: errno's address and the runtime's statics,
   instance lib/A AD2l.PcapB_syms); the segments for the computations over the image (g_nl writable and in the
   image, the policy literal in a read-only segment), discharged at the link instance (LinkImgInst.v
   pi_link_segs); the relro window in the image (the top file). *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : SEGS = tfibsegs.
Hypothesis RELRO_IMG : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img SEGS a.

Lemma rk_jAR : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k -> AR SEGS B ly' S' W' mem' md'.
Proof. intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k (_ & _ & (memS & HJi & _) & _). exact (proj1 HJi). Qed.

(* ---- g_nl, errno and the policy literal: computations over the image ---- *)
Lemma rk_gnl_img : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> in_img SEGS a.
Proof.
  intros a Ha. rewrite HSEGS.
  destruct (find_segment tfibsegs LA_G_NL NK_SIZE) as [sg|] eqn:Hf; [|vm_compute in Hf; discriminate Hf].
  destruct (find_segment_hit _ _ _ _ Hf) as (Hin & H1 & H2). exists sg. split; [exact Hin | lia].
Qed.

Lemma rk_gnl_not_owned : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> ~ Exists (in_zr a) (as_owned_static B).
Proof.
  intros a Ha Hex. rewrite (ts_owned _ TB) in Hex.
  assert (C : forallb (fun r : Z * Z => (fst r + snd r <=? LA_G_NL) || (LA_G_NL + NK_SIZE <=? fst r))%bool
    Tfib_owned_static = true) by (vm_compute; reflexivity).
  apply Exists_exists in Hex as (r & Hr & Hz). rewrite forallb_forall in C. specialize (C r Hr).
  unfold in_zr in Hz. apply Bool.orb_true_iff in C as [C|C]; apply Z.leb_le in C; lia.
Qed.

Lemma rk_gnl_writable : forall m a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> writable_at SEGS m a.
Proof. intros m a Ha. rewrite HSEGS. apply LA_G_NL_writable. unfold NK_SIZE in Ha. exact Ha. Qed.

Lemma rk_errno_val : as_errno B = TFIB_ERRNO.
Proof. exact (ts_errno _ TB). Qed.

(* errno's four bytes lie in a writable segment (a computation over the image) *)
Lemma rk_errno_writable : forall m a, as_errno B <= a < as_errno B + 4 -> writable_at SEGS m a.
Proof.
  intros m a Ha. rewrite rk_errno_val in Ha. rewrite HSEGS.
  apply (writable_at_of_wseg tfibsegs m TFIB_ERRNO 4); [unfold TFIB_ERRNO; lia | unfold TFIB_ERRNO; lia
    | vm_compute; reflexivity | exact Ha].
Qed.

Lemma rk_served_ro : forall a, LA_S_SERVED <= a < LA_S_SERVED + 15 ->
  YC20.in_roP SEGS PCAP_RLO PCAP_RHI a /\ ~ Exists (in_zr a) (as_owned_static B) /\
  ~ (as_errno B <= a < as_errno B + 4).
Proof.
  intros a Ha. split; [|split].
  - rewrite HSEGS. apply (rk_ro_of_b tfibsegs PCAP_RLO PCAP_RHI LA_S_SERVED (LA_S_SERVED + 15));
      [vm_compute; reflexivity | exact Ha].
  - intros Hex. rewrite (ts_owned _ TB) in Hex.
    assert (C : forallb (fun r : Z * Z => (fst r + snd r <=? LA_S_SERVED) || (LA_S_SERVED + 15 <=? fst r))%bool
      Tfib_owned_static = true) by (vm_compute; reflexivity).
    apply Exists_exists in Hex as (r & Hr & Hz). rewrite forallb_forall in C. specialize (C r Hr).
    unfold in_zr in Hz. apply Bool.orb_true_iff in C as [C|C]; apply Z.leb_le in C; lia.
  - rewrite rk_errno_val. unfold TFIB_ERRNO, LA_S_SERVED in *. lia.
Qed.

(* an image byte is below the shadow and the stack *)
Lemma rk_img_low : forall a, in_img SEGS a -> 0x10000 <= a < 0x654000.
Proof. intros a Ha. pose proof (pa_img_range a Ha) as H. unfold pcap_img_end in H. exact H. Qed.

Lemma rk_ro_img : forall a, YC20.in_roP SEGS PCAP_RLO PCAP_RHI a -> in_img SEGS a.
Proof.
  intros a [(s & Hs & _ & Hb) | Hr]; [exists s; split; [exact Hs | exact Hb] | exact (RELRO_IMG a Hr)].
Qed.

(* ==========================================================================
   5. Facts of the call (um_pre) and of the side frame
   ========================================================================== *)
Section c.
Variable cx : umcx.
Variable fpos : Z.
#[local] Notation F := (um_F cx fpos).
#[local] Notation SH := (um_SH cx fpos).
#[local] Notation Eacc := (fun a => um_E cx a \/ aside_rng (um_lyc cx) UM_CID fpos a).
#[local] Notation AJ ly S W m md :=
  (ajournal_gx SEGS B (um_G cx) (um_XO cx) (um_OUT cx) (um_STK cx) (um_sp0 cx) (um_FP cx)
     (um_ly cx) (um_S cx) (um_W0 cx) (um_mem0 cx) (um_md0 cx) ((UM_CID, fpos) :: um_own cx) ly S W m md (um_k cx)).

Hypothesis HPRE : um_pre SK B cx.
Hypothesis HNIN : ~ In (UM_CID, fpos) (frames (um_Sc cx)).
Hypothesis HS1W : exists S1 W1 mem1 md1, AR SEGS B (um_lyc cx) S1 W1 mem1 md1 /\
  frames S1 = (UM_CID, fpos) :: frames (um_Sc cx) /\ ablocks B (um_lyc cx) S1 = ablocks B (um_lyc cx) (um_Sc cx).

Lemma rk_pre_j : ajournal_gx SEGS B (um_G cx) (um_XO cx) (um_OUT cx) (um_STK cx) (um_sp0 cx) (um_FP cx)
  (um_ly cx) (um_S cx) (um_W0 cx) (um_mem0 cx) (um_md0 cx) (um_own cx)
  (um_lyc cx) (um_Sc cx) (um_W cx) (um_memc cx) (um_mdc cx) (um_k cx).
Proof. exact (proj1 (proj1 HPRE)). Qed.

Lemma rk_pre_g : gx_ok SEGS B (um_G cx).
Proof. exact (proj1 (proj2 (proj1 HPRE))). Qed.

Lemma rk_pre_ar : AR SEGS B (um_lyc cx) (um_Sc cx) (um_W cx) (um_memc cx) (um_mdc cx).
Proof. exact (rk_jAR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rk_pre_j). Qed.

Lemma rk_win : um_sp cx mod 16 = 0 /\ alloc_ceiling <= um_sp0 cx - um_STK cx /\
  um_sp0 cx - um_STK cx <= um_sp cx - 8768 /\ um_sp cx <= um_sp0 cx /\ um_sp0 cx <= 2 ^ 47 /\
  um_sp cx - 176 <= um_sp1 cx <= um_sp cx - 160 /\ um_sp1 cx mod 32 = 0 /\ um_sp1 cx mod 16 = 0.
Proof.
  destruct HPRE as ((HJ & _ & _ & _ & _ & _ & _ & H16 & Hlo & Hhi & _) & _).
  pose proof HJ as HW. eapply aj_window_bounds in HW. destruct HW as (W1 & W2 & W3 & W4).
  pose proof asan_consts as ((C1 & C2) & _).
  unfold REAC_SERVED_UNMARK_ALL_AK, REAC_SERVED_UNMARK_ALL_AFRAME, REAC_SERVED_UNMARK_ALL_ASLACK,
    AUN_ALIAS_READ_STK in Hlo.
  fold (um_sp cx) in H16, Hlo, Hhi.
  destruct (sp1_facts (um_sp cx - 160) ltac:(lia) ltac:(rewrite Zminus_mod, H16; reflexivity)) as (S1 & S2 & S3).
  unfold um_sp1, UM_FRAME. repeat split; lia.
Qed.

Lemma rk_F : 4096 <= F /\ F + 512 <= alloc_ceiling /\ F mod 64 = 0 /\ in_app F 512 /\
  (F + 512 <= YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= F) /\ 0 <= fpos < fs_frames UM_CID.
Proof.
  destruct HS1W as (S1 & W1 & mem1 & md1 & HAR & Hfr & _).
  assert (Hin : In (UM_CID, fpos) (frames S1)) by (rewrite Hfr; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS _ S1 W1 mem1 md1 _ _ HAR Hin) as (H1 & H2 & H3).
  destruct (frame_al64 SEGS B _ S1 W1 mem1 md1 _ _ HAR Hin) as (H4 & _).
  pose proof (frm_off_imgP B _ S1 W1 mem1 md1 _ _ HAR Hin) as H5.
  destruct HAR as [M _]. destruct (frame_facts B _ S1 _ _ _ M Hin) as (_ & H6 & _).
  change (fs_frame_bytes UM_CID) with 512 in *. unfold um_F.
  split; [exact H1|]. split; [exact H2|]. split; [exact H4|]. split; [exact H3|]. split; [|exact H6].
  destruct H5 as [H5|H5]; [left | right]; exact H5.
Qed.

Lemma rk_SH : SH = SHADOW_OFF + F / 8 /\ SH mod 8 = 0 /\ kLowMemEnd + 512 <= SH /\ SH + 64 <= kHighMemBeg.
Proof.
  destruct rk_F as (F1 & F2 & F3 & _). unfold um_SH. rk_consts. repeat split; lia.
Qed.

(* the side frame's bytes are low application bytes or high ones, never shadow ones *)
Lemma rk_F_app : F + 512 <= kLowShadowBeg \/ kHighMemBeg <= F.
Proof.
  destruct rk_F as (_ & _ & _ & (_ & H) & _). unfold ASAN_CEIL in H.
  destruct H as [H|[H _]]; [left | right]; exact H.
Qed.

Lemma rk_side_unfold : forall a, aside_rng (um_lyc cx) UM_CID fpos a <->
  (F <= a < F + 512) \/ (SH <= a < SH + 64) \/ a = um_FL cx fpos.
Proof.
  intros a. unfold aside_rng, in_zr, frame_rng, shadow_addr, um_SH, um_FL, um_F. cbn [fst snd].
  change (fs_frame_bytes UM_CID) with 512. change (512 / 8) with 64. tauto.
Qed.

(* the marks block, when a0 <> 0 *)
Lemma rk_mk : um_mk cx <> 0 ->
  0 < um_mk cx /\ amem_range (um_mk cx) (MK_SIZE + 8) /\
  range_addressable (ard SEGS (um_m0 cx)) SHADOW_OFF (um_mk cx) MK_SIZE /\
  shadow_hull_vis (ard SEGS (um_m0 cx)) (um_mk cx) MK_SIZE /\
  apart_frame (um_regs cx) REAC_SERVED_UNMARK_ALL_AK (um_mk cx) MK_SIZE /\
  apart_gnl LA_G_NL (um_mk cx) MK_SIZE /\ apart (as_errno B) 4 (um_mk cx) MK_SIZE /\
  amarks_at SEGS (um_m0 cx) (um_mk cx) (um_gbs cx) /\ marks_wf (um_gbs cx).
Proof.
  intros Hm. destruct HPRE as (_ & _ & _ & _ & _ & HB & _ & _ & _ & _ & HMK).
  destruct (HB Hm) as ((P0 & P1 & P2 & P3 & _ & P5) & G1 & G2 & _ & _).
  destruct (HMK Hm) as (M1 & M2).
  exact (conj P0 (conj P1 (conj P2 (conj P3 (conj P5 (conj G1 (conj G2 (conj M1 M2)))))))).
Qed.

(* errno, and its separations *)
Lemma rk_errno : as_errno B = as_tp B - 164 /\
  apart_frame (um_regs cx) REAC_SERVED_UNMARK_ALL_AK (as_errno B) 4 /\ apart_gnl LA_G_NL (as_errno B) 4 /\
  awrange SEGS (um_m0 cx) (as_errno B) 4.
Proof.
  destruct HPRE as (_ & _ & _ & HE & _). destruct HE as (E1 & E2 & _ & E4 & E5 & _).
  exact (conj E1 (conj E4 (conj E5 E2))).
Qed.

(* ---- the invariant the walk's memory keeps at the read piece's states ---- *)
Definition rk_inv (ly : alayout) (S : astate) (W : world SEGS) (m : word -> option byte) (md : Model) : Prop :=
  AJ ly S W m md /\
  frames S = (UM_CID, fpos) :: frames (um_Sc cx) /\
  (exists fs, S = set_fs fs (um_Sc cx)) /\
  Permutation (ablocks B ly S) (ablocks B (um_lyc cx) (um_Sc cx)) /\
  (forall c q, frame_addr ly c q = frame_addr (um_lyc cx) c q) /\
  rdword (aview SEGS (w_H W) m) (um_sp cx - 8) = Some (raZ (um_regs cx)) /\
  (forall j, 0 <= j < 12 -> rdword (aview SEGS (w_H W) m) (um_sp cx - 16 - 8 * j) =
     Some (bv_unsigned (getr (um_regs cx) (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))))) /\
  rdword (aview SEGS (w_H W) m) (F + UM_FLAGPTR) = Some (um_FL cx fpos) /\
  akept SEGS B (um_lyc cx) (um_Sc cx) (um_W cx) (um_memc cx) W m
    (um_sp cx - REAC_SERVED_UNMARK_ALL_AK) (um_sp cx) Eacc /\
  m_fds md = m_fds (um_mdc cx) /\ m_fs md = m_fs (um_mdc cx) /\
  YC20.arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) m) /\
  um_mk cx <> 0 /\
  rdword (aview SEGS (w_H W) m) (um_sp1 cx + UM_SLOT_EMPTY) = Some LA_S_EMPTY /\
  rdword (aview SEGS (w_H W) m) (um_sp1 cx + UM_SLOT_LIM) = Some (Z.land (um_mk cx) 7 + 3) /\
  um_marks_kept cx W m.

Lemma rk_inv_of_base : forall c ly S W ms md,
  um_base SK B cx fpos ly S W ms md -> um_loop cx c fpos W ms -> rk_inv ly S W (ms_mem ms) md.
Proof.
  intros c ly S W ms md (_ & _ & _ & _ & _ & HJ & Hfr & _ & Hfs & Hperm & _ & Hfa & _ & _ & _ & _ & _ & _ & _ & _ & _
    & Hra & Hsv & Hfl & _ & _ & HK & Hfds & Hfs' & Hro) (Hm & _ & _ & _ & _ & _ & _ & _ & Hs1 & Hs2 & Hmk).
  unfold rk_inv. repeat (split; [assumption|]); assumption.
Qed.

(* the frame and its shadow are present at every AR state where the frame is live *)
Lemma rk_frame_present : forall ly S (W : world SEGS) m md,
  AR SEGS B ly S W m md -> In (UM_CID, fpos) (frames S) -> frame_addr ly UM_CID fpos = F ->
  (forall a, F <= a < F + UM_FB -> apresent (w_H W) m a) /\
  (forall a, SH <= a < SH + UM_SHN -> apresent (w_H W) m a).
Proof.
  intros ly S W m md HAR Hin Hfa.
  destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & _ & HF & HS).
  rewrite Hfa in HF, HS. change (fs_frame_bytes UM_CID) with 512 in HF, HS. change (512 / 8) with 64 in HS.
  split.
  - intros a Ha. exact (proj1 (HF a Ha)).
  - intros a Ha. unfold um_SH, UM_SHN in Ha. fold (um_F cx fpos) in Ha.
    replace a with (shadow_addr F + (a - shadow_addr F)) by ring.
    apply (proj1 (HS (a - shadow_addr F) ltac:(unfold shadow_addr; lia))).
Qed.

Lemma rk_base_of_inv : forall ly S W ms md,
  ms_resv ms = None -> ms_svc_pending ms = None -> ms_rom ms = seg_rom SEGS -> ms_fregs ms = fp_regs ->
  ms_fcsr ms = fp_csr ->
  getr (ms_regs ms) 2 = w64 (um_sp1 cx) -> getr (ms_regs ms) 9 = w64 (um_sp1 cx) ->
  getr (ms_regs ms) 8 = w64 (um_sp cx) ->
  getr (ms_regs ms) 18 = w64 SH -> getr (ms_regs ms) 19 = w64 F -> getr (ms_regs ms) 25 = w64 F ->
  getr (ms_regs ms) 20 = getr (um_regs cx) 10 ->
  getr (ms_regs ms) 3 = getr (um_regs cx) 3 -> getr (ms_regs ms) 4 = getr (um_regs cx) 4 ->
  rk_inv ly S W (ms_mem ms) md -> um_base SK B cx fpos ly S W ms md.
Proof.
  intros ly S W ms md Hr Hs Hrom Hf Hc R2 R9 R8 R18 R19 R25 R20 R3 R4
    (HJ & Hfr & Hfs & Hperm & Hfa & Hra & Hsv & Hfl & HK & Hfds & Hfs' & Hro & _ & _ & _ & _).
  pose proof (rk_jAR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  assert (Hin : In (UM_CID, fpos) (frames S)) by (rewrite Hfr; left; reflexivity).
  destruct (rk_frame_present ly S W (ms_mem ms) md HAR Hin (Hfa UM_CID fpos)) as [HFp HSp].
  cbv zeta. repeat (split; [assumption|]); assumption.
Qed.

Lemma rk_loop_of_inv : forall c ly S W ms md,
  Z.of_nat c < um_n cx ->
  getr (ms_regs ms) 21 = w64 (F + UM_ALIAS) ->
  getr (ms_regs ms) 22 = w64 (um_mk cx + MK_NAME + MARK_LEN * Z.of_nat c) ->
  getr (ms_regs ms) 23 = w64 LA_S_SERVED -> getr (ms_regs ms) 24 = w64 (-8) ->
  getr (ms_regs ms) 26 = w64 (SHADOW_OFF + um_mk cx / 8) -> getr (ms_regs ms) 27 = w64 (Z.of_nat c) ->
  rk_inv ly S W (ms_mem ms) md -> um_loop cx c fpos W ms.
Proof.
  intros c ly S W ms md Hc R21 R22 R23 R24 R26 R27 (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hm & Hs1 & Hs2 & Hmk).
  unfold um_loop. repeat (split; [assumption|]); assumption.
Qed.

(* ---- a step of the walk's own code or of a runtime call below s1: the invariant at the new memory ---- *)
Lemma rk_step : forall ly S W m md m' md' (X : Z -> Prop),
  rk_inv ly S W m md ->
  AJ ly S W m' md' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall a, X a -> (um_sp cx - REAC_SERVED_UNMARK_ALL_AK <= a < um_sp1 cx) \/ (SH <= a < SH + 64)) ->
  (forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) ->
  m_fds md' = m_fds md -> m_fs md' = m_fs md ->
  rk_inv ly S W m' md'.
Proof.
  intros ly S W m md m' md' X (HJ & Hfr & Hfs & Hperm & Hfa & Hra & Hsv & Hfl & HK & Hfds & Hfs' & Hro & Hm & Hs1 & Hs2 & Hmk)
    HJ' UN HX Hpres Efds Efs.
  destruct rk_win as (W16 & Wc & Wlo & Whi & W47 & S1lo & S1al & _).
  destruct rk_F as (F1 & F2 & F3 & F4 & F5 & F6).
  destruct rk_SH as (SH1 & SH2 & SH3 & SH4).
  pose proof rk_F_app as FA.
  destruct (rk_mk Hm) as (M0 & M1 & _ & _ & M4 & M5 & M6 & _ & _).
  unfold REAC_SERVED_UNMARK_ALL_AK, REAC_SERVED_UNMARK_ALL_AFRAME, REAC_SERVED_UNMARK_ALL_ASLACK,
    AUN_ALIAS_READ_STK in HX |- *.
  unfold apart_frame, REAC_SERVED_UNMARK_ALL_AK, REAC_SERVED_UNMARK_ALL_AFRAME, REAC_SERVED_UNMARK_ALL_ASLACK,
    AUN_ALIAS_READ_STK in M4.
  fold (um_sp cx) in M4. unfold amem_range, MK_SIZE in M1. unfold MK_SIZE in M4.
  rk_consts.
  (* the bytes above s1 and the side frame's own bytes are not X *)
  assert (Hstk : forall a, um_sp1 cx <= a < um_sp cx -> ~ X a).
  { intros a Ha HXa. destruct (HX a HXa) as [H|H]; lia. }
  assert (Hflag : forall a, F <= a < F + 512 -> ~ X a).
  { intros a Ha HXa. destruct (HX a HXa) as [H|H]; lia. }
  split; [exact HJ'|]. split; [exact Hfr|]. split; [exact Hfs|]. split; [exact Hperm|]. split; [exact Hfa|].
  split.
  { rewrite <- Hra. apply rk_rdword_eq. intros i Hi. apply UN; [lia | apply Hstk; lia]. }
  split.
  { intros j Hj. rewrite <- (Hsv j Hj). apply rk_rdword_eq. intros i Hi. apply UN; [lia | apply Hstk; lia]. }
  split.
  { rewrite <- Hfl. apply rk_rdword_eq. intros i Hi. unfold UM_FLAGPTR in *. apply UN; [lia | apply Hflag; lia]. }
  split.
  { apply (akept_step SK SEGS B LAWS pa_segs_low (um_lyc cx) (um_Sc cx) (um_W cx) (um_memc cx) (um_mdc cx) W m W m'
      (um_sp cx - REAC_SERVED_UNMARK_ALL_AK) (um_sp cx) Eacc Eacc X rk_pre_ar).
    - unfold REAC_SERVED_UNMARK_ALL_AK, REAC_SERVED_UNMARK_ALL_AFRAME, REAC_SERVED_UNMARK_ALL_ASLACK,
        AUN_ALIAS_READ_STK. lia.
    - lia.
    - exact HK.
    - exact UN.
    - intros a _ Ha. exact (Hpres a Ha).
    - intros a Ha. exact Ha.
    - intros a HXa. destruct (HX a HXa) as [H|H].
      + right. unfold REAC_SERVED_UNMARK_ALL_AK, REAC_SERVED_UNMARK_ALL_AFRAME, REAC_SERVED_UNMARK_ALL_ASLACK,
          AUN_ALIAS_READ_STK. lia.
      + left. right. apply (proj2 (rk_side_unfold a)). right. left. exact H. }
  split; [rewrite Efds; exact Hfds|]. split; [rewrite Efs; exact Hfs'|].
  split.
  { apply (rk_arodata_eq SEGS PCAP_RLO PCAP_RHI B _ _ Hro). intros a Hro_a.
    pose proof (rk_img_low a (rk_ro_img a Hro_a)) as Hir.
    apply UN; [lia|]. intros HXa. destruct (HX a HXa) as [H|H]; lia. }
  split; [exact Hm|].
  split.
  { rewrite <- Hs1. apply rk_rdword_eq. intros i Hi. unfold UM_SLOT_EMPTY. apply UN; [lia | apply Hstk; lia]. }
  split.
  { rewrite <- Hs2. apply rk_rdword_eq. intros i Hi. unfold UM_SLOT_LIM. apply UN; [lia | apply Hstk; lia]. }
  intros a Ha. rewrite <- (Hmk a Ha). unfold MK_SIZE in Ha. apply UN; [lia|].
  intros HXa. destruct (HX a HXa) as [H|H]; lia.
Qed.

(* ---- g_nl's interface-table cells at an invariant state are the call's ---- *)
Lemma rk_cell_kept : forall ly S W m md, rk_inv ly S W m md ->
  forall x, LA_G_NL + NK_IF_NAME <= x < LA_G_NL + NK_SIZE ->
  aview SEGS (w_H W) m x = aview SEGS (w_H (um_W cx)) (um_memc cx) x.
Proof.
  intros ly S W m md (_ & _ & _ & _ & _ & _ & _ & _ & HK & _ & _ & _ & Hm & _ & _ & _) x Hx.
  destruct HK as (_ & _ & K3 & _).
  assert (Hx' : LA_G_NL <= x < LA_G_NL + NK_SIZE) by (unfold NK_IF_NAME, NK_SIZE in *; lia).
  destruct rk_errno as (_ & _ & Herr & _).
  destruct (rk_mk Hm) as (_ & _ & _ & _ & _ & Mg & _ & _ & _).
  apply K3.
  - exact (rk_gnl_img x Hx').
  - exact (rk_gnl_not_owned x Hx').
  - unfold apart_gnl in Herr. lia.
  - intros [HE | Hs].
    + unfold um_E, um_wr, reac_served_unmark_all_awr, inFP in HE. destruct HE as (r & Hr & Hra).
      destruct Hr as [<- | [<- | []]].
      * cbn [fst snd] in Hra. unfold NK_IF_NAME, NK_N_SENT in *. lia.
      * unfold aivl in Hra. cbn [fst snd] in Hra. fold (um_mk cx) in Hra.
        rewrite (proj2 (Z.eqb_neq (um_mk cx) 0) Hm) in Hra. unfold apart_gnl in Mg. unfold MK_SIZE in *. lia.
    + destruct HS1W as (S1 & W1 & mem1 & md1 & HAR1 & Hfrs1 & _).
      assert (HinF : In (UM_CID, fpos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
      apply (proj2 (aside_rng_low SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ x HAR1 HinF Hs)).
      exact (rk_gnl_img x Hx').
Qed.

(* ---- a table pointer read at an invariant state is the call's, with what the call's Pre says of it ---- *)
Lemma rk_tab_ptr : forall ly S W m md, rk_inv ly S W m md ->
  forall i n2 ix p, nth_error (um_tab cx) i = Some (n2, ix) ->
  au64_at SEGS (rdW W m) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> 0 <= p < 2 ^ 64 ->
  au64_at SEGS (um_m0 cx) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p /\ acstr_at SEGS (um_m0 cx) p n2 /\
  astr_rt_ok SEGS (um_regs cx) REAC_SERVED_UNMARK_ALL_AK (um_m0 cx) p n2 /\
  apart_gnl LA_G_NL p (Z.of_nat (length n2) + 1) /\ apart (as_errno B) 4 p (Z.of_nat (length n2) + 1) /\
  apart (um_mk cx) MK_SIZE p (Z.of_nat (length n2) + 1) /\
  (forall a, p <= a <= p + Z.of_nat (length n2) ->
     akb SEGS B (um_lyc cx) (um_Sc cx) (um_sp cx - REAC_SERVED_UNMARK_ALL_AK) (um_sp cx) a).
Proof.
  intros ly S W m md HI i n2 ix p Hi Hp Hpr.
  pose proof HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hm & _ & _ & _).
  pose proof HPRE as (_ & HRDp & (NK0 & _ & _ & _ & _ & IT0 & _ & _) & _ & HTB & _).
  pose proof IT0 as (_ & L80 & IT0').
  assert (Li : (i < length (um_tab cx))%nat) by (apply nth_error_Some; congruence).
  destruct (IT0' i n2 ix Hi) as (_ & p0 & P0 & Pz & C0 & _).
  assert (Hp0 : au64_at SEGS (um_m0 cx) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p).
  { unfold um_m0. apply (val_mem_moved SEGS (w_H W) (w_H (um_W cx)) m (um_memc cx)
      (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) 8 p); [|exact Hp].
    intros k Hk. symmetry. apply (rk_cell_kept ly S W m md HI). unfold NK_IF_NAME, NK_SIZE. lia. }
  pose proof (rk_acstr_range SEGS _ p0 n2 C0) as Rp0.
  pose proof (rk_au64_unique SEGS _ _ _ _ Hp0 P0) as Ep. rewrite !Z.mod_small in Ep by lia. subst p0.
  destruct (HTB i n2 ix p Hi P0 Hpr) as (RT & AG & AE & _ & AM).
  split; [exact P0|]. split; [exact C0|]. split; [exact RT|]. split; [exact AG|]. split; [exact AE|].
  split; [exact (AM Hm)|].
  intros a Ha. apply HRDp. right. exists (um_kbs cx), (um_tab cx), i, n2, ix, p.
  split; [exact NK0|]. split; [exact IT0|]. split; [exact Hi|]. split; [exact P0|].
  split; [exact C0 | exact Ha].
Qed.

(* ---- the fake kernel's bytes and table across a step below s1 or into the side frame's shadow ---- *)
Lemma rk_gnl_move : forall (W : world SEGS) m m' (X : Z -> Prop) kbs,
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall a, X a -> (um_sp cx - REAC_SERVED_UNMARK_ALL_AK <= a < um_sp1 cx) \/ (SH <= a < SH + 64)) ->
  anlk_at SEGS (rdW W m) LA_G_NL kbs -> anlk_at SEGS (rdW W m') LA_G_NL kbs.
Proof.
  intros W m m' X kbs UN HX NK.
  destruct rk_win as (_ & Wc & Wlo & _ & _ & S1lo & _). destruct rk_SH as (_ & _ & SH3 & _).
  unfold REAC_SERVED_UNMARK_ALL_AK, REAC_SERVED_UNMARK_ALL_AFRAME, REAC_SERVED_UNMARK_ALL_ASLACK,
    AUN_ALIAS_READ_STK in HX.
  apply (rk_anlk_move SEGS (rdW W m) (rdW W m') kbs NK).
  - intros x Hx. apply (YCbq.mbyte_of_aview SEGS). apply UN; [unfold LA_G_NL, NK_SIZE in Hx; lia|].
    intros HXx. destruct (HX x HXx) as [H|H]; rk_consts; unfold LA_G_NL, NK_SIZE in Hx; lia.
  - intros x Hx. apply rk_gnl_writable. exact Hx.
Qed.

Lemma rk_tab_move : forall ly S W m md m' (X : Z -> Prop) kbs,
  rk_inv ly S W m md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall a, X a -> (um_sp cx - REAC_SERVED_UNMARK_ALL_AK <= a < um_sp1 cx) \/ (SH <= a < SH + 64)) ->
  aiftab_at SEGS (rdW W m) LA_G_NL kbs (um_tab cx) -> aiftab_at SEGS (rdW W m') LA_G_NL kbs (um_tab cx).
Proof.
  intros ly S W m md m' X kbs HI UN HX IT.
  destruct rk_win as (_ & Wc & Wlo & _ & _ & S1lo & _). destruct rk_SH as (_ & _ & SH3 & SH4).
  unfold REAC_SERVED_UNMARK_ALL_AK, REAC_SERVED_UNMARK_ALL_AFRAME, REAC_SERVED_UNMARK_ALL_ASLACK,
    AUN_ALIAS_READ_STK in HX.
  pose proof IT as (_ & L80 & _).
  assert (Hcell : forall x, LA_G_NL <= x < LA_G_NL + NK_SIZE -> mbyte SEGS (rdW W m') x = mbyte SEGS (rdW W m) x).
  { intros x Hx. apply (YCbq.mbyte_of_aview SEGS). apply UN; [unfold LA_G_NL, NK_SIZE in Hx; lia|].
    intros HXx. destruct (HX x HXx) as [H|H]; rk_consts; unfold LA_G_NL, NK_SIZE in Hx; lia. }
  apply (rk_aiftab_keep SEGS (rdW W m) (rdW W m') kbs kbs (um_tab cx) IT eq_refl).
  - intros x Hx. apply Hcell. unfold NK_IF_NAME, NK_SIZE in *. lia.
  - intros x Hx. apply Hcell. unfold NK_IF_INDEX, NK_SIZE in *. lia.
  - intros i n2 ix p Hi Hp Hpr x Hx.
    destruct (rk_tab_ptr ly S W m md HI i n2 ix p Hi Hp Hpr) as (_ & _ & RT & _).
    destruct RT as (_ & _ & AMR & _ & _ & _ & AF).
    unfold apart_frame, REAC_SERVED_UNMARK_ALL_AK, REAC_SERVED_UNMARK_ALL_AFRAME, REAC_SERVED_UNMARK_ALL_ASLACK,
      AUN_ALIAS_READ_STK in AF.
    change (spZ (um_regs cx)) with (um_sp cx) in AF. unfold amem_range in AMR.
    apply (YCbq.mbyte_of_aview SEGS). rk_consts. apply UN; [lia|].
    intros HXx. destruct (HX x HXx) as [H|H]; lia.
Qed.

Lemma rk_kinv_step : forall ly S W m md m' (X : Z -> Prop) kbs c,
  rk_inv ly S W m md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall a, X a -> (um_sp cx - REAC_SERVED_UNMARK_ALL_AK <= a < um_sp1 cx) \/ (SH <= a < SH + 64)) ->
  um_kinv cx (rdW W m) kbs c -> um_kinv cx (rdW W m') kbs c.
Proof.
  intros ly S W m md m' X kbs c HI UN HX (NK & WF & IT & REST).
  split; [exact (rk_gnl_move W m m' X kbs UN HX NK)|]. split; [exact WF|].
  split; [exact (rk_tab_move ly S W m md m' X kbs HI UN HX IT) | exact REST].
Qed.

Lemma rk_kinv_mid_step : forall ly S W m md m' (X : Z -> Prop) kbs c,
  rk_inv ly S W m md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall a, X a -> (um_sp cx - REAC_SERVED_UNMARK_ALL_AK <= a < um_sp1 cx) \/ (SH <= a < SH + 64)) ->
  um_kinv_mid cx (rdW W m) kbs c -> um_kinv_mid cx (rdW W m') kbs c.
Proof.
  intros ly S W m md m' X kbs c HI UN HX (NK & WF & IT & REST).
  split; [exact (rk_gnl_move W m m' X kbs UN HX NK)|]. split; [exact WF|].
  split; [exact (rk_tab_move ly S W m md m' X kbs HI UN HX IT) | exact REST].
Qed.

(* ---- name c, the C string of the marks block's slot c, at an invariant state ---- *)
Lemma rk_name : forall c ly S W m md, rk_inv ly S W m md -> Z.of_nat c < um_n cx ->
  acstr_at SEGS (rdW W m) (um_mk cx + MK_NAME + MARK_LEN * Z.of_nat c) (nth c (um_names cx) []) /\
  (length (nth c (um_names cx) []) <= 15)%nat /\
  nth_error (um_names cx) c = Some (nth c (um_names cx) []) /\
  um_mk cx + MK_NAME + MARK_LEN * Z.of_nat c + 16 <= um_mk cx + MK_SIZE.
Proof.
  intros c ly S W m md HI Hc.
  pose proof HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hm & _ & _ & Hmk).
  destruct (rk_mk Hm) as (_ & _ & _ & _ & _ & _ & _ & MA & MW).
  pose proof MW as (MR & _). unfold MARKS_MAX in MR.
  unfold um_n in Hc.
  assert (Hn : (c < Z.to_nat (mk_n (um_gbs cx)))%nat) by lia.
  pose proof (rk_mk_names_nth (um_gbs cx) c Hn) as En. fold (um_names cx) in En.
  assert (Eq : nth c (um_names cx) [] = cstr (slice (um_gbs cx) (4 + 16 * Z.of_nat c) 16))
    by (apply nth_error_nth; exact En).
  destruct MA as [[MB MR'] ML].
  destruct (rk_slot_cstr SEGS (um_m0 cx) (um_mk cx) (um_gbs cx) (Z.of_nat c) MB
    ltac:(unfold MK_SIZE in ML; lia) MW ltac:(lia)) as (AC & AL).
  rewrite Eq. unfold MK_NAME, MARK_LEN, MK_SIZE.
  split; [|split; [exact AL | split; [exact En | lia]]].
  replace (um_mk cx + 4 + 16 * Z.of_nat c) with (um_mk cx + (4 + 16 * Z.of_nat c)) by ring.
  apply (rk_acstr_move SEGS (um_m0 cx) (rdW W m) _ _ AC).
  intros x Hx. apply (YCbq.mbyte_of_aview SEGS (w_H (um_W cx)) (w_H W) (um_memc cx) m x).
  apply Hmk. unfold MK_SIZE. lia.
Qed.

(* ---- the side frame's exception set misses every frame shadow of the call ---- *)
Lemma rk_fmiss : fmiss (um_lyc cx) (um_Sc cx) Eacc.
Proof.
  apply fmiss_or.
  - apply (fmiss_app SEGS B LAWS (um_lyc cx) (um_Sc cx) (um_W cx) (um_memc cx) (um_mdc cx) _ rk_pre_ar).
    intros a HE. unfold um_E, um_wr, reac_served_unmark_all_awr, inFP in HE. destruct HE as (r & Hr & Hra).
    destruct Hr as [<- | [<- | []]].
    + cbn [fst snd] in Hra. left. rk_consts. unfold LA_G_NL, NK_N_SENT in Hra. lia.
    + unfold aivl in Hra. cbn [fst snd] in Hra. fold (um_mk cx) in Hra.
      destruct (Z.eq_dec (um_mk cx) 0) as [E0|E0].
      * rewrite E0, Z.eqb_refl in Hra. lia.
      * rewrite (proj2 (Z.eqb_neq (um_mk cx) 0) E0) in Hra.
        destruct (rk_mk E0) as (_ & M1 & _). unfold amem_range, MK_SIZE in *. rk_consts. lia.
  - destruct rk_F as (_ & _ & _ & _ & _ & F6).
    apply (fmiss_side SEGS B (um_lyc cx) (um_Sc cx) (um_W cx) (um_memc cx) (um_mdc cx) UM_CID fpos rk_pre_ar).
    + unfold UM_CID. lia.
    + exact F6.
    + exact HNIN.
Qed.

(* ---- "reac-pw:served" and its NUL at an invariant state: its bytes and its shadow ---- *)
Lemma rk_served_at : forall ly S W m md, rk_inv ly S W m md ->
  acstr_at SEGS (rdW W m) LA_S_SERVED S_SERVED /\
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF LA_S_SERVED 15 /\
  shadow_hull_vis (aview SEGS (w_H W) m) LA_S_SERVED 15 /\ amem_range LA_S_SERVED 15.
Proof.
  intros ly S W m md HI. pose proof HI as (HJ & _ & _ & Hperm & _ & _ & _ & _ & HK & _ & _ & Hro & _).
  pose proof HPRE as ((_ & _ & HRO0 & _) & _ & _ & _ & _ & _ & HSV & HSR & _).
  assert (HEQ : forall x, LA_S_SERVED <= x < LA_S_SERVED + 15 ->
    aview SEGS (w_H W) m x = aview SEGS (w_H (um_W cx)) (um_memc cx) x).
  { intros x Hx. destruct (rk_served_ro x Hx) as (R1 & R2 & R3).
    rewrite (Hro x R1 R2 R3), (HRO0 x R1 R2 R3). reflexivity. }
  destruct HSR as (_ & _ & AMR & RA & HV & _ & _).
  rewrite rk_S_SERVED_len in AMR, RA, HV. change (Z.of_nat 14 + 1) with 15 in RA, HV.
  pose proof (aj_stk_row_eq SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (L1 & H1).
  pose proof (aj_stk_row_eq SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rk_pre_j) as (L2 & H2).
  destruct (shadow_transport SEGS B LAWS TB pa_img_range (um_lyc cx) (um_Sc cx) (um_W cx) (um_memc cx) (um_mdc cx)
    ly S W m md (um_sp cx - REAC_SERVED_UNMARK_ALL_AK) (um_sp cx) Eacc LA_S_SERVED 15
    rk_pre_ar (rk_jAR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) ltac:(congruence) ltac:(congruence)
    ltac:(intros b mm Hb; exact (Permutation_in _ (Permutation_sym Hperm) Hb)) HK rk_fmiss ltac:(lia)
    ltac:(intros x Hx; right; right; left; exact (rk_ro_img x (proj1 (rk_served_ro x Hx)))) RA HV) as (RA' & HV').
  split; [|split; [exact RA' | split; [exact HV' | unfold amem_range in *; lia]]].
  apply (rk_acstr_move SEGS (um_m0 cx) (rdW W m) _ _ HSV). intros x Hx. rewrite rk_S_SERVED_len in Hx.
  apply (YCbq.mbyte_of_aview SEGS (w_H (um_W cx)) (w_H W) (um_memc cx) m x). apply HEQ. lia.
Qed.
(* ---- the marks block's bytes are bytes of the call's write set, and none is a byte of the side frame ---- *)
Lemma rk_mk_ajw : forall a, um_mk cx <> 0 -> um_mk cx <= a < um_mk cx + MK_SIZE ->
  ajw B (um_G cx) (um_XO cx) (um_OUT cx) (um_STK cx) (um_sp0 cx) (um_FP cx) (um_ly cx) (um_S cx)
    (um_lyc cx) (um_Sc cx) (um_own cx) a.
Proof.
  intros a Hm Ha. pose proof HPRE as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hajw & _) & _).
  apply Hajw. exists (aivl (aarg (um_regs cx) 0) MK_SIZE). split; [right; left; reflexivity|].
  unfold aivl. fold (um_mk cx). rewrite (proj2 (Z.eqb_neq (um_mk cx) 0) Hm). cbn [fst snd]. exact Ha.
Qed.

Lemma rk_mk_not_side : forall a, um_mk cx <> 0 -> um_mk cx <= a < um_mk cx + MK_SIZE ->
  ~ aside_rng (um_lyc cx) UM_CID fpos a.
Proof.
  intros a Hm Ha. pose proof HPRE as ((HJ & HGX & _) & _).
  destruct (rk_mk Hm) as (_ & M1 & _).
  destruct (rk_F) as (_ & _ & _ & _ & _ & F6).
  apply (ajw_not_side SK SEGS B LAWS pa_img_range (um_G cx) (um_XO cx) (um_OUT cx) (um_STK cx) (um_sp0 cx)
    (um_FP cx) (um_ly cx) (um_S cx) (um_W0 cx) (um_mem0 cx) (um_md0 cx) (um_own cx) (um_lyc cx) (um_Sc cx)
    (um_W cx) (um_memc cx) (um_mdc cx) (um_k cx) UM_CID fpos a HGX HJ ltac:(unfold UM_CID; lia) F6 HNIN
    (rk_mk_ajw a Hm Ha)).
  unfold amem_range, MK_SIZE in *. rk_consts. lia.
Qed.

(* the walk's registers at a cut of round c *)
Definition urb_R (c : nat) (regs : bvmap 5 word) : Prop :=
  getr regs 2 = w64 (um_sp1 cx) /\ getr regs 9 = w64 (um_sp1 cx) /\ getr regs 8 = w64 (um_sp cx) /\
  getr regs 18 = w64 SH /\ getr regs 19 = w64 F /\ getr regs 25 = w64 F /\
  getr regs 20 = getr (um_regs cx) 10 /\ getr regs 3 = getr (um_regs cx) 3 /\ getr regs 4 = getr (um_regs cx) 4 /\
  getr regs 21 = w64 (F + UM_ALIAS) /\ getr regs 22 = w64 (um_mk cx + MK_NAME + MARK_LEN * Z.of_nat c) /\
  getr regs 23 = w64 LA_S_SERVED /\ getr regs 24 = w64 (-8) /\
  getr regs 26 = w64 (SHADOW_OFF + um_mk cx / 8) /\ getr regs 27 = w64 (Z.of_nat c).

Lemma urb_R_of : forall c ly S W ms md, um_loop cx c fpos W ms -> um_base SK B cx fpos ly S W ms md ->
  urb_R c (ms_regs ms).
Proof.
  intros c ly S W ms md (Hm & Hc & R21 & R22 & R23 & R24 & R26 & R27 & _)
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R2 & R9 & R8 & R18 & R19 & R25 & R20 & R3 & R4 & _).
  unfold urb_R. repeat (split; [assumption|]); assumption.
Qed.

Lemma urb_R_keep : forall c regs regs', urb_R c regs -> aregs_preserved regs regs' -> urb_R c regs'.
Proof.
  intros c regs regs' (R2 & R9 & R8 & R18 & R19 & R25 & R20 & R3 & R4 & R21 & R22 & R23 & R24 & R26 & R27) HP.
  assert (CS : forall r, acallee_saved r -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) by exact HP.
  unfold urb_R.
  split; [exact (eq_trans (CS 2 ltac:(unfold acallee_saved; lia)) R2)|].
  split; [exact (eq_trans (CS 9 ltac:(unfold acallee_saved; lia)) R9)|].
  split; [exact (eq_trans (CS 8 ltac:(unfold acallee_saved; lia)) R8)|].
  split; [exact (eq_trans (CS 18 ltac:(unfold acallee_saved; lia)) R18)|].
  split; [exact (eq_trans (CS 19 ltac:(unfold acallee_saved; lia)) R19)|].
  split; [exact (eq_trans (CS 25 ltac:(unfold acallee_saved; lia)) R25)|].
  split; [exact (eq_trans (CS 20 ltac:(unfold acallee_saved; lia)) R20)|].
  split; [exact (eq_trans (CS 3 ltac:(unfold acallee_saved; lia)) R3)|].
  split; [exact (eq_trans (CS 4 ltac:(unfold acallee_saved; lia)) R4)|].
  split; [exact (eq_trans (CS 21 ltac:(unfold acallee_saved; lia)) R21)|].
  split; [exact (eq_trans (CS 22 ltac:(unfold acallee_saved; lia)) R22)|].
  split; [exact (eq_trans (CS 23 ltac:(unfold acallee_saved; lia)) R23)|].
  split; [exact (eq_trans (CS 24 ltac:(unfold acallee_saved; lia)) R24)|].
  split; [exact (eq_trans (CS 26 ltac:(unfold acallee_saved; lia)) R26)|].
  exact (eq_trans (CS 27 ltac:(unfold acallee_saved; lia)) R27).
Qed.

(* the loop and the base at a cut, from the registers and the invariant *)
Lemma urb_close : forall c ly S W regs pc mem md, Z.of_nat c < um_n cx -> urb_R c regs ->
  rk_inv ly S W mem md ->
  um_loop cx c fpos W (mkst regs pc mem (seg_rom SEGS)) /\ um_base SK B cx fpos ly S W (mkst regs pc mem (seg_rom SEGS)) md.
Proof.
  intros c ly S W regs pc mem md Hc (R2 & R9 & R8 & R18 & R19 & R25 & R20 & R3 & R4 & R21 & R22 & R23 & R24 & R26 & R27) HI.
  split.
  - apply (rk_loop_of_inv c ly S W _ md Hc); assumption.
  - apply (rk_base_of_inv ly S W _ md);
      cbn [ms_regs ms_mem ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst]; first [reflexivity | assumption].
Qed.

End c.
End b.
End a.
