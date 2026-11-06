(* op_read (fuzz_link.c:677-700), plain image: the memory and pointer lemmas the five segment walks of
   the arm share (a Theorem Labs lane). Nothing here is a walk.

   1. Regions a write set misses (`c0_out`, `c0_in`), and every memory view the cuts carry kept across
      a `munch W m m'` that misses its region (`c0_*_keep`, `c0_base_keep`).
   2. From a writable byte to a readable one (`c0_wview_mrd`), and the buffers and stacks built on it.
   3. `MemNorm.task_mem` across a call (`c0_task_mem_munch`).
   4. A heap block outside the image (`pf_img_free`) is apart from every named object of the image
      (`c0_img_free`, `c0_img_named`).
   5. Where the interface names, the selector's name and the texts strings live (`c0_fixed`: in
      .rodata or in g_names), and what that gives every callee (`c0_fixed_ctx`, `c0_ifname`,
      `c0_ifname_ctx`, `c0_sel_str`, `c0_sel_fixed`, `c0_texts_img`).
   6. `requests_are` from the two request lists (`c0_requests_are`), and the range of a reader's
      answer (`c0_read_rc_range`, `c0_rkind_len`, `c0_ralias_len`).

   Every address and every image byte is read from the plain image (the unstripped twin of the pin
   ebe34b259b9f): the reserved segments and the .rodata bytes by `vm_compute` over `rsegs`. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem printf_facts_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC0Defs.
Local Open Scope Z_scope.

Ltac c0_unf := unfold A_RO_LO, A_RO_END, A_G_NAMES, G_NAMES_SIZE, A_G_NL, NK_SIZE, A_ERRNO, A_TP,
  ERRNO_TP_OFF, A_LONG_ALIAS, LONG_ALIAS_SIZE, SLOT_FRAME, SLOT_STACK_Z, FO_P, FO_N, FO_B40, FO_B256,
  FO_SAVED, A_TEXTS, TEXTS_N, A_ODD, ODD_N, A_GOT_GUARD_S, A_GUARD_S, MD_SIZE, MK_SIZE, NK_IF_NAME,
  NK_IF_INDEX in *.

(* ==========================================================================
   1. Small facts over lists, words and byte views
   ========================================================================== *)

Lemma c0_wz_u : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (wz a) = a.
Proof. intros a H. exact (wa_unsigned a H). Qed.

Lemma c0_wz_pin : forall p q, wz p = wz q -> 0 <= q < 2 ^ 64 -> exists k, p = q + k * 2 ^ 64.
Proof.
  intros p q E Hq. apply (f_equal (@bv_unsigned 64)) in E. unfold wz in E.
  rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 64) with (2 ^ 64) in E.
  rewrite (Z.mod_small q) in E by exact Hq. exists (p / 2 ^ 64). rewrite <- E.
  rewrite Z.mod_eq by lia. ring.
Qed.

Lemma c0_apart_sym : forall a n b k, apart a n b k -> apart b k a n.
Proof. unfold apart. intros; lia. Qed.

Lemma c0_apart_le : forall a n b k n' k', apart a n b k -> n' <= n -> k' <= k -> apart a n' b k'.
Proof. unfold apart. intros; lia. Qed.

Lemma c0_no_nul : forall s, existsb (fun b => bz b =? 0) s = false -> ~ In (zb 0) s.
Proof.
  intros s H Hin.
  assert (T : existsb (fun b => bz b =? 0) s = true)
    by (apply existsb_exists; exists (zb 0); split; [exact Hin | reflexivity]).
  congruence.
Qed.

Lemma c0_bytes_at0 : forall m a b l, bytes_at rsegs m a (b :: l) -> mrd rsegs m (wa a) = Some b.
Proof.
  intros m a b l (_ & _ & H). specialize (H 0%nat ltac:(cbn; lia)). rewrite Z.add_0_r in H. exact H.
Qed.

Lemma c0_bytes_tl : forall m a b l, bytes_at rsegs m a (b :: l) -> bytes_at rsegs m (a + 1) l.
Proof.
  intros m a b l H. change (b :: l) with ([b] ++ l) in H. apply bytes_at_app in H as [_ H]. exact H.
Qed.

Lemma c0_bytes_skip : forall m a bs k, bytes_at rsegs m a bs -> (k <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (skipn k bs).
Proof.
  intros m a bs k H Hk. rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn in H. replace (Nat.min k (length bs)) with k in H by lia. exact H.
Qed.

Lemma c0_wr_sub : forall m a n k j, wr_at rsegs m a n -> 0 <= k -> 0 <= j -> k + j <= n ->
  wr_at rsegs m (a + k) j.
Proof.
  intros m a n k j (H0 & H1 & H) Hk Hj Hkj. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a + k + i) with (a + (k + i)) by lia. apply H. lia.
Qed.

Lemma c0_wr_prefix : forall m a n j, wr_at rsegs m a n -> 0 <= j <= n -> wr_at rsegs m a j.
Proof.
  intros m a n j H Hj. pose proof (c0_wr_sub m a n 0 j H ltac:(lia) ltac:(lia) ltac:(lia)) as H'.
  rewrite Z.add_0_r in H'. exact H'.
Qed.

(* a cell list cut in two, and put back together *)
Lemma c0_rw_app : forall m a cs1 cs2, rw_cells rsegs m a (cs1 ++ cs2) ->
  rw_cells rsegs m a cs1 /\ rw_cells rsegs m (a + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m a cs1 cs2 ((Hwf & Hb) & Hw). apply cells_wf_app in Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb as [B1 B2].
  rewrite cells_size_app, Nat2Z.inj_add in Hw. rewrite cells_bytes_length in B2 by exact W1.
  split; split; [split; assumption | | split; assumption | ].
  - apply (c0_wr_prefix m a _ _ Hw). lia.
  - apply (c0_wr_sub m a _ _ _ Hw); lia.
Qed.

Lemma c0_rw_join : forall m a cs1 cs2, rw_cells rsegs m a cs1 ->
  rw_cells rsegs m (a + Z.of_nat (cells_size cs1)) cs2 -> rw_cells rsegs m a (cs1 ++ cs2).
Proof.
  intros m a cs1 cs2 ((W1 & B1) & H1) ((W2 & B2) & H2).
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|].
    rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app, Nat2Z.inj_add. destruct H1 as (H10 & H11 & H1). destruct H2 as (H20 & H21 & H2).
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))) as [L|L]; [apply H1; lia|].
    replace (a + i) with (a + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
    apply H2. lia.
Qed.

Lemma c0_cb_prefix : forall m a n bs k, rw_cells rsegs m a [CB n bs] -> (k <= n)%nat ->
  rw_cells rsegs m a [CB k (firstn k bs)].
Proof.
  intros m a n bs k ((Hwf & Hb) & Hw) Hk. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. cbn [cells_size csize] in Hw.
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [rewrite length_firstn; lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. rewrite <- (firstn_skipn k bs) in Hb.
    apply bytes_at_app in Hb as [B _]. exact B.
  - cbn [cells_size csize]. apply (c0_wr_prefix m a _ _ Hw). lia.
Qed.

(* a C string inside a buffer puts its NUL inside the buffer *)
Lemma c0_cstr_in_cb : forall m a s n bs, cstr_at m a s -> rw_cells rsegs m a [CB n bs] ->
  (length s < n)%nat -> In (zb 0) bs.
Proof.
  intros m a s n bs (Bs & _) ((Hwf & Hb) & _) Hn. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  destruct Bs as (_ & _ & Hs). destruct Hb as (_ & _ & Hb).
  specialize (Hs (length s) ltac:(rewrite length_app; cbn [length]; lia)).
  specialize (Hb (length s) ltac:(lia)). rewrite Hs in Hb.
  rewrite nth_error_app2 in Hb by lia. rewrite Nat.sub_diag in Hb. cbn in Hb.
  symmetry in Hb. exact (nth_error_In _ _ Hb).
Qed.

(* two C strings at one address are one string *)
Lemma c0_cstr_same : forall m s1 p s2, cstr_at m p s1 -> cstr_at m p s2 -> s1 = s2.
Proof.
  intros m s1. induction s1 as [|a s1 IH]; intros p [|b s2] (B1 & N1) (B2 & N2).
  - reflexivity.
  - exfalso. apply N2. left. cbn in B1, B2.
    pose proof (c0_bytes_at0 _ _ _ _ B1) as E1. pose proof (c0_bytes_at0 _ _ _ _ B2) as E2. congruence.
  - exfalso. apply N1. left. cbn in B1, B2.
    pose proof (c0_bytes_at0 _ _ _ _ B1) as E1. pose proof (c0_bytes_at0 _ _ _ _ B2) as E2. congruence.
  - cbn in B1, B2.
    pose proof (c0_bytes_at0 _ _ _ _ B1) as E1. pose proof (c0_bytes_at0 _ _ _ _ B2) as E2.
    assert (a = b) as <- by congruence. f_equal.
    apply (IH (p + 1)); split.
    + exact (c0_bytes_tl _ _ _ _ B1).
    + intros H. apply N1. right. exact H.
    + exact (c0_bytes_tl _ _ _ _ B2).
    + intros H. apply N2. right. exact H.
Qed.

(* `u64_at` pins the 8 bytes: two values with the same bytes agree mod 2^64 *)
Lemma c0_u64_same : forall m a p q, u64_at m a p -> u64_at m a q -> wz p = wz q.
Proof.
  unfold u64_at. intros m a p q (_ & _ & Hp) (_ & _ & Hq).
  assert (E : le8 (wz p) = le8 (wz q)).
  { apply nth_error_ext. intros i. destruct (Nat.lt_ge_cases i 8) as [Hi|Hi].
    - rewrite <- (Hp i ltac:(rewrite length_le8; lia)), <- (Hq i ltac:(rewrite length_le8; lia)).
      reflexivity.
    - rewrite (proj2 (nth_error_None (le8 (wz p)) i)) by (rewrite length_le8; lia).
      rewrite (proj2 (nth_error_None (le8 (wz q)) i)) by (rewrite length_le8; lia). reflexivity. }
  rewrite <- (le_bytes_to_word_le8 (wz p)), <- (le_bytes_to_word_le8 (wz q)), E. reflexivity.
Qed.

Lemma c0_u64_pin : forall m a p q, u64_at m a p -> u64_at m a q -> 0 <= q < 2 ^ 64 ->
  exists k, p = q + k * 2 ^ 64.
Proof. intros m a p q Hp Hq R. exact (c0_wz_pin p q (c0_u64_same m a p q Hp Hq) R). Qed.

Lemma c0_u64_eq : forall m a p q, u64_at m a p -> u64_at m a q ->
  0 <= p < 2 ^ 64 -> 0 <= q < 2 ^ 64 -> p = q.
Proof.
  intros m a p q Hp Hq Rp Rq. destruct (c0_u64_pin m a p q Hp Hq Rq) as [k ->].
  assert (k = 0) as -> by lia. lia.
Qed.

(* ==========================================================================
   2. Regions a write set misses, and the views kept across it
   ========================================================================== *)

(* every byte of [a, a+n) is outside W *)
Definition c0_out (W : list ivl) (a n : Z) : Prop := forall x, a <= x < a + n -> outside W x.
(* W writes only inside [lo, hi) *)
Definition c0_in (W : list ivl) (lo hi : Z) : Prop :=
  forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> lo <= x < hi.
(* W misses .rodata and g_names, where every name a callee reads lives *)
Definition c0_wfix (W : list ivl) : Prop :=
  c0_out W A_RO_LO (A_RO_END - A_RO_LO) /\ c0_out W A_G_NAMES G_NAMES_SIZE.

Lemma c0_outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; intros [_ H']; contradiction].
  destruct (Z.le_gt_cases lo x) as [A|A]; destruct (Z.lt_ge_cases x hi) as [B|B];
    [right; intros [H' _]; exact (H' (conj A B)) | left; split; [intros [? ?]; lia | exact H] ..].
Qed.

Lemma c0_out_in : forall W lo hi a n, c0_in W lo hi -> 0 <= a -> a + n <= 2 ^ 64 ->
  (a + n <= lo \/ hi <= a) -> c0_out W a n.
Proof.
  intros W lo hi a n HW Ha Hn D x Hx.
  destruct (c0_outside_dec W x) as [H|H]; [exact H|].
  exfalso. pose proof (HW x ltac:(lia) H). lia.
Qed.

Lemma c0_out_disj : forall W a n, disjoint_from W a n -> c0_out W a n.
Proof. intros W a n D x Hx. exact (disjoint_outside W a n x D Hx). Qed.

Lemma c0_out_sub : forall W a n b k, c0_out W a n -> a <= b -> b + k <= a + n -> c0_out W b k.
Proof. intros W a n b k H H1 H2 x Hx. apply H. lia. Qed.

Lemma c0_in_one : forall lo hi, c0_in [(lo, hi)] lo hi.
Proof.
  intros lo hi x _ H. cbn in H.
  destruct (Z.le_gt_cases lo x), (Z.lt_ge_cases x hi); try (split; assumption);
    exfalso; apply H; (split; [intros [? ?]; lia | exact I]).
Qed.

Lemma c0_in_weaken : forall W lo hi lo' hi', c0_in W lo hi -> lo' <= lo -> hi <= hi' -> c0_in W lo' hi'.
Proof. intros W lo hi lo' hi' H H1 H2 x Hx Ho. pose proof (H x Hx Ho). lia. Qed.

Lemma c0_fixed_wfix : forall W lo hi, c0_in W lo hi -> A_RO_END <= lo \/ hi <= A_RO_LO ->
  A_G_NAMES + G_NAMES_SIZE <= lo \/ hi <= A_G_NAMES -> c0_wfix W.
Proof.
  intros W lo hi H H1 H2. split; (eapply c0_out_in; [exact H| c0_unf; lia | c0_unf; lia | c0_unf; lia]).
Qed.

Lemma c0_bytes_keep : forall W m m' a bs, bytes_at rsegs m a bs -> munch W m m' ->
  c0_out W a (Z.of_nat (length bs)) -> bytes_at rsegs m' a bs.
Proof.
  intros W m m' a bs (H0 & H1 & H) MU O. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (H i Hi). unfold mrd. rewrite (MU (wa (a + Z.of_nat i))); [reflexivity|].
  rewrite wa_unsigned by lia. apply O. lia.
Qed.

Lemma c0_rw_keep : forall W m m' a cs, rw_cells rsegs m a cs -> munch W m m' -> wmono rsegs m m' ->
  c0_out W a (Z.of_nat (cells_size cs)) -> rw_cells rsegs m' a cs.
Proof.
  intros W m m' a cs ((Hwf & Hb) & Hw) MU WM O. split; [split; [exact Hwf|]|].
  - apply (c0_bytes_keep W m); [exact Hb|exact MU|]. rewrite cells_bytes_length by exact Hwf. exact O.
  - exact (wr_at_transport rsegs m m' a _ Hw WM).
Qed.

Lemma c0_u8arr_keep : forall W m m' a bs, u8arr rsegs m a bs -> munch W m m' -> wmono rsegs m m' ->
  c0_out W a (Z.of_nat (length bs)) -> u8arr rsegs m' a bs.
Proof.
  intros W m m' a bs (B & Hw) MU WM O. split.
  - exact (c0_bytes_keep W m m' a bs B MU O).
  - exact (wr_at_transport rsegs m m' a _ Hw WM).
Qed.

Lemma c0_cstr_keep : forall W m m' a s, cstr_at m a s -> munch W m m' ->
  c0_out W a (Z.of_nat (length s) + 1) -> cstr_at m' a s.
Proof.
  intros W m m' a s (B & N) MU O. split; [|exact N].
  apply (c0_bytes_keep W m m' a _ B MU). rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. exact O.
Qed.

Lemma c0_u64_keep : forall W m m' a v, u64_at m a v -> munch W m m' -> c0_out W a 8 -> u64_at m' a v.
Proof.
  intros W m m' a v B MU O. apply (c0_bytes_keep W m m' a _ B MU). rewrite length_le8. exact O.
Qed.

Lemma c0_u32_keep : forall W m m' a v, u32_at m a v -> munch W m m' -> c0_out W a 4 -> u32_at m' a v.
Proof.
  intros W m m' a v B MU O. apply (c0_bytes_keep W m m' a _ B MU). rewrite length_le4. exact O.
Qed.

Lemma c0_tbuf_keep : forall W m m' a cap bs, tbuf_at m a cap bs -> munch W m m' -> wmono rsegs m m' ->
  0 <= cap -> c0_out W a (cap + 1) -> tbuf_at m' a cap bs.
Proof.
  intros W m m' a cap bs T MU WM Hc O. apply (c0_rw_keep W m m' a _ T MU WM).
  eapply c0_out_sub; [exact O| lia | cbn [cells_size csize]; lia].
Qed.

Lemma c0_nlk_keep : forall W m m' kbs, nlk_at m kbs -> munch W m m' -> wmono rsegs m m' ->
  c0_out W A_G_NL NK_SIZE -> nlk_at m' kbs.
Proof.
  intros W m m' kbs (U & L) MU WM O. split; [|exact L].
  apply (c0_u8arr_keep W m m' _ _ U MU WM). rewrite L. exact O.
Qed.

Lemma c0_model_keep : forall W m m' p bs, model_at m p bs -> munch W m m' -> wmono rsegs m m' ->
  c0_out W p MD_SIZE -> model_at m' p bs.
Proof.
  intros W m m' p bs (U & L) MU WM O. split; [|exact L].
  apply (c0_u8arr_keep W m m' _ _ U MU WM). rewrite L. exact O.
Qed.

Lemma c0_marks_keep : forall W m m' p bs, marks_at m p bs -> munch W m m' -> wmono rsegs m m' ->
  c0_out W p MK_SIZE -> marks_at m' p bs.
Proof.
  intros W m m' p bs (U & L) MU WM O. split; [|exact L].
  apply (c0_u8arr_keep W m m' _ _ U MU WM). rewrite L. exact O.
Qed.

Lemma c0_cursor_keep : forall W m m' p0 pl P N, cursor_ok m p0 pl P N -> munch W m m' ->
  c0_out W p0 (Z.of_nat (length pl)) -> cursor_ok m' p0 pl P N.
Proof.
  intros W m m' p0 pl P N (B & K) MU O. split; [exact (c0_bytes_keep W m m' p0 pl B MU O)|exact K].
Qed.

Lemma c0_gnames_keep : forall W m m', gnames_at m -> munch W m m' ->
  c0_out W A_G_NAMES G_NAMES_SIZE -> gnames_at m'.
Proof.
  intros W m m' G MU O k Hk. destruct (G k Hk) as (rest & B & L). exists rest. split; [|exact L].
  apply (c0_bytes_keep W m m' _ _ B MU). rewrite L.
  eapply c0_out_sub; [exact O| c0_unf; lia | c0_unf; lia].
Qed.

Lemma c0_texts_keep : forall W m m', texts_at m -> munch W m m' -> c0_out W A_TEXTS (8 * TEXTS_N) ->
  texts_at m'.
Proof.
  intros W m m' T MU O i Hi. apply (c0_u64_keep W m m' _ _ (T i Hi) MU).
  eapply c0_out_sub; [exact O| c0_unf; lia | c0_unf; lia].
Qed.

Lemma c0_ifptrs_keep : forall W m m', ifptrs_at m -> munch W m m' ->
  c0_out W (A_G_NL + NK_IF_NAME) 512 -> ifptrs_at m'.
Proof.
  intros W m m' T MU O i Hi. apply (c0_u64_keep W m m' _ _ (T i Hi) MU).
  eapply c0_out_sub; [exact O| lia | lia].
Qed.

Lemma c0_la_keep : forall W m m', la_ok m -> munch W m m' -> wmono rsegs m m' ->
  c0_out W A_LONG_ALIAS (LONG_ALIAS_SIZE + 3) -> la_ok m'.
Proof.
  intros W m m' (la & sl & R & B & L) MU WM O. exists la, sl. split; [|split; [|exact L]].
  - apply (c0_rw_keep W m m' _ _ R MU WM). eapply c0_out_sub; [exact O| lia | cbn [cells_size csize]; c0_unf; lia].
  - apply (c0_bytes_keep W m m' _ _ B MU). rewrite L. eapply c0_out_sub; [exact O| c0_unf; lia | c0_unf; lia].
Qed.

Lemma c0_guard_keep : forall W m m', guard_m m -> munch W m m' ->
  c0_out W A_GOT_GUARD_S 8 -> c0_out W A_GUARD_S 8 -> guard_m m'.
Proof.
  intros W m m' (G1 & c & G2) MU O1 O2. split.
  - apply (c0_bytes_keep W m m' _ _ G1 MU). rewrite length_le8. exact O1.
  - exists c. apply (c0_bytes_keep W m m' _ _ G2 MU). rewrite length_le8. exact O2.
Qed.

Lemma c0_frame_keep : forall W m m' E P N wa wk, c0_frame E P N wa wk m -> munch W m m' ->
  wmono rsegs m m' -> c0_out W (e_S E - SLOT_FRAME) FO_SAVED -> c0_frame E P N wa wk m'.
Proof.
  intros W m m' E P N wa wk (j0 & j2 & R) MU WM O. exists j0, j2.
  apply (c0_rw_keep W m m' _ _ R MU WM). exact O.
Qed.

(* the two 40-byte frame buffers of the arm: wa at sp + 0x50, wk at sp + 0x78 *)
Lemma c0_frame_bufs : forall E P N wa wk m, c0_frame E P N wa wk m ->
  rw_cells rsegs m (e_S E - SLOT_FRAME + FO_B40) [CB 40 wa] /\
  rw_cells rsegs m (e_S E - SLOT_FRAME + FO_B256) [CB 40 wk].
Proof.
  intros E P N wa wk m (j0 & j2 & H). unfold c0_cells in H.
  match type of H with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10
                                       :: ?c11 :: ?c12 :: ?c13 :: []) =>
    change (c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: []) with
      ([c1; c2; c3; c4; c5; c6; c7; c8; c9; c10] ++ [c11] ++ [c12] ++ [c13]) in H end.
  apply c0_rw_app in H as [_ H]. apply c0_rw_app in H as [H1 H]. apply c0_rw_app in H as [H2 _].
  cbn [cells_size csize Nat.add] in H1, H2.
  replace (e_S E - SLOT_FRAME + Z.of_nat 80) with (e_S E - SLOT_FRAME + FO_B40) in H1, H2 by (unfold FO_B40; lia).
  replace (e_S E - SLOT_FRAME + FO_B40 + Z.of_nat 40) with (e_S E - SLOT_FRAME + FO_B256) in H2
    by (unfold FO_B40, FO_B256; lia).
  split; assumption.
Qed.

Lemma c0_buf_keep : forall W m m' E cap a, c0_buf E cap a m -> munch W m m' -> wmono rsegs m m' ->
  0 <= cap -> (cap <> 0 -> c0_out W a (cap + 1)) -> c0_buf E cap a m'.
Proof.
  intros W m m' E cap a (Z0 & NZ) MU WM Hc O. split; [exact Z0|]. intros Hn.
  destruct (NZ Hn) as (A0 & B & T). split; [exact A0|]. split; [exact B|].
  exact (c0_tbuf_keep W m m' a cap _ T MU WM Hc (O Hn)).
Qed.

(* ==========================================================================
   3. From a writable byte to a readable one
   ========================================================================== *)

Lemma c0_find_segment_in : forall segs a n s, find_segment segs a n = Some s -> In s segs.
Proof.
  induction segs as [|s0 segs IH]; intros a n s H; cbn in H; [discriminate|].
  destruct ((Z.of_N (seg_base s0) <=? a) && (a + n <=? Z.of_N (seg_base s0) + Z.of_N (seg_size s0)))%bool.
  - injection H as <-. left. reflexivity.
  - right. exact (IH a n s H).
Qed.

Lemma c0_rw_readable : forallb (fun s => implb (seg_writable s) (seg_readable s)) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma c0_wview_mrd : forall m x, wview rsegs m x <> None -> exists b, mrd rsegs m x = Some b.
Proof.
  intros m x H. unfold mrd. destruct (m x) as [b|] eqn:E; [exists b; reflexivity|].
  unfold wview in H. rewrite E in H. unfold seg_rom, memory_read.
  replace (Z.of_N 1) with 1 by reflexivity.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [sg|] eqn:F; [|congruence].
  assert (RW : seg_writable sg = true -> seg_readable sg = true).
  { intros Hw. pose proof c0_rw_readable as C. rewrite forallb_forall in C.
    specialize (C sg (c0_find_segment_in _ _ _ _ F)). rewrite Hw in C. exact C. }
  destruct (seg_writable sg) eqn:Wr; [|congruence]. rewrite (RW eq_refl).
  change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
  destruct (segment_byte_at (seg_bytes sg) (Z.to_N (bv_unsigned x - Z.of_N (seg_base sg)))) as [b|];
    [exists b; reflexivity | congruence].
Qed.

Lemma c0_wr_bytes : forall m a k, wr_at rsegs m a (Z.of_nat k) ->
  exists bs, length bs = k /\ forall i, (i < k)%nat -> mrd rsegs m (wa (a + Z.of_nat i)) = nth_error bs i.
Proof.
  intros m a k. induction k as [|k IH]; intros H.
  - exists []. split; [reflexivity|]. intros i Hi. lia.
  - destruct IH as (bs & L & B).
    { apply (c0_wr_prefix m a _ _ H). lia. }
    destruct H as (H0 & H1 & H).
    destruct (c0_wview_mrd m (wa (a + Z.of_nat k)) (H (Z.of_nat k) ltac:(lia))) as [b Hb].
    exists (bs ++ [b]). split; [rewrite length_app, L; cbn; lia|].
    intros i Hi. destruct (Nat.lt_ge_cases i k) as [Lt|Ge].
    + rewrite nth_error_app1 by lia. exact (B i Lt).
    + assert (i = k) as -> by lia. rewrite nth_error_app2 by lia. rewrite L, Nat.sub_diag. exact Hb.
Qed.

(* a writable range holds bytes: the buffer as one CB cell *)
Lemma c0_wr_rw : forall m a n, wr_at rsegs m a n -> 0 <= n -> exists bs, rw_cells rsegs m a [CB (Z.to_nat n) bs].
Proof.
  intros m a n H Hn.
  destruct (c0_wr_bytes m a (Z.to_nat n) ltac:(rewrite Z2Nat.id by lia; exact H)) as (bs & L & B).
  exists bs. destruct H as (H0 & H1 & H). split; [split|].
  - cbn [cells_wf cell_wf]. split; [exact L | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. split; [rewrite L; lia|].
    intros i Hi. apply B. lia.
  - cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi. apply H. lia.
Qed.

Lemma c0_wr_stk : forall m lo hi, wr_at rsegs m lo (hi - lo) -> lo <= hi -> stk rsegs m lo hi.
Proof.
  intros m lo hi (H0 & H1 & H) Hle. split; [lia|]. split; [lia|]. intros a Ha.
  specialize (H (a - lo) ltac:(lia)). replace (lo + (a - lo)) with a in H by lia.
  split; [exact H | exact (c0_wview_mrd m _ H)].
Qed.

(* ==========================================================================
   4. MemNorm.task_mem across a call
   ========================================================================== *)

Lemma c0_task_mem_munch : forall W m m', MemNorm.task_mem rsegs m -> munch W m m' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> x < TASK_SIZE) -> MemNorm.task_mem rsegs m'.
Proof.
  intros W m m' T MU H a b E. destruct (c0_outside_dec W (bv_unsigned a)) as [O|O].
  - rewrite (MU a O) in E. exact (T a b E).
  - right. apply H; [|exact O]. pose proof (bv_unsigned_in_range 64 a) as R.
    change (bv_modulus 64) with (2 ^ 64) in R. exact R.
Qed.

Lemma c0_task_mem_in : forall W m m' lo hi, MemNorm.task_mem rsegs m -> munch W m m' ->
  c0_in W lo hi -> hi <= 2 ^ 47 -> MemNorm.task_mem rsegs m'.
Proof.
  intros W m m' lo hi T MU H Hh. apply (c0_task_mem_munch W m m' T MU). intros x Hx Ho.
  pose proof (H x Hx Ho). change TASK_SIZE with (2 ^ 47). lia.
Qed.

(* ==========================================================================
   5. A heap block outside the image
   ========================================================================== *)

(* the image's reserved segments are [0x10000, 0x97000) with no hole *)
Lemma c0_resv : map (fun s => (bv_unsigned (fst s), bv_unsigned (snd s))) (segments_reserved rsegs)
  = [(65536, 8192); (73728, 57344); (131072, 4096); (135168, 483328)].
Proof. vm_compute. reflexivity. Qed.

Lemma c0_img_free : forall a n, pf_img_free a n -> 0 < n -> a + n <= 0x10000 \/ 0x97000 <= a.
Proof.
  intros a n F Hn.
  assert (G : forall lo sz, In (lo, sz) [(65536, 8192); (73728, 57344); (131072, 4096); (135168, 483328)] ->
    forall i, 0 <= i < n -> ~ (lo <= a + i < lo + sz)).
  { intros lo sz Hin i Hi. rewrite <- c0_resv in Hin. apply in_map_iff in Hin as (s & Es & Hs).
    injection Es as E1 E2. subst lo sz. exact (F i Hi s Hs). }
  destruct (Z.le_gt_cases (a + n) 0x10000) as [L|L]; [left; exact L|].
  destruct (Z.le_gt_cases 0x97000 a) as [R|R]; [right; exact R|]. exfalso.
  set (x := Z.max a 0x10000).
  assert (Hx : 0 <= x - a < n) by (unfold x; lia).
  destruct (Z.lt_ge_cases x 73728).
  { apply (G 65536 8192 ltac:(cbn; auto) (x - a) Hx). unfold x in *; lia. }
  destruct (Z.lt_ge_cases x 131072).
  { apply (G 73728 57344 ltac:(cbn; auto) (x - a) Hx). unfold x in *; lia. }
  destruct (Z.lt_ge_cases x 135168).
  { apply (G 131072 4096 ltac:(cbn; auto) (x - a) Hx). unfold x in *; lia. }
  apply (G 135168 483328 ltac:(cbn; auto 6) (x - a) Hx). unfold x in *; lia.
Qed.

Lemma c0_img_apart : forall a n b k, pf_img_free a n -> 0 < n -> 0x10000 <= b -> b + k <= 0x97000 ->
  apart a n b k /\ apart b k a n.
Proof. intros a n b k F Hn Hb Hk. destruct (c0_img_free a n F Hn); unfold apart; lia. Qed.

(* every named object the arm reads or writes lies inside the image *)
Lemma c0_img_named : forall a n, pf_img_free a n -> 0 < n ->
  apart_gnl a n /\ apart a n A_G_NAMES G_NAMES_SIZE /\ apart a n A_LONG_ALIAS (LONG_ALIAS_SIZE + 3) /\
  apart a n A_TEXTS (8 * TEXTS_N) /\ apart a n A_ODD (8 * ODD_N) /\ apart a n A_ERRNO 4 /\
  apart a n A_GOT_GUARD_S 8 /\ apart a n A_GUARD_S 8 /\ apart a n A_RO_LO (A_RO_END - A_RO_LO).
Proof.
  intros a n F Hn. destruct (c0_img_free a n F Hn); unfold apart_gnl, apart; c0_unf; lia.
Qed.

(* ==========================================================================
   6. Where the names live: .rodata or g_names
   ========================================================================== *)

Definition c0_fixed (p n : Z) : Prop :=
  0 <= n /\ ((A_RO_LO <= p /\ p + n <= A_RO_END) \/ (A_G_NAMES <= p /\ p + n <= A_G_NAMES + G_NAMES_SIZE)).
(* the same, for a value only known mod 2^64 (a `u64_at` of an unbounded Z) *)
Definition c0_fixed_w (p n : Z) : Prop := exists q k, p = q + k * 2 ^ 64 /\ c0_fixed q n.

Definition c0_fixed_b (p n : Z) : bool :=
  (0 <=? n) && (((A_RO_LO <=? p) && (p + n <=? A_RO_END)) ||
                ((A_G_NAMES <=? p) && (p + n <=? A_G_NAMES + G_NAMES_SIZE))).

Lemma c0_fixed_b_ok : forall p n, c0_fixed_b p n = true -> c0_fixed p n.
Proof.
  intros p n H. unfold c0_fixed_b in H. apply andb_prop in H as [H1 H].
  apply Z.leb_le in H1. split; [exact H1|].
  apply orb_prop in H as [H|H]; apply andb_prop in H as [H2 H3]; apply Z.leb_le in H2, H3; [left|right]; lia.
Qed.

Lemma c0_fixed_w_of : forall p n, c0_fixed p n -> c0_fixed_w p n.
Proof. intros p n H. exists p, 0. split; [lia | exact H]. Qed.

Lemma c0_fixed_out : forall W p n, c0_wfix W -> c0_fixed p n -> c0_out W p n.
Proof.
  intros W p n (O1 & O2) (Hn & [H|H]); [eapply c0_out_sub; [exact O1|..] | eapply c0_out_sub; [exact O2|..]];
    c0_unf; lia.
Qed.

Lemma c0_fixed_apart : forall p n b k, c0_fixed_w p n -> 0 <= b -> b + k <= 2 ^ 64 -> 0 <= k ->
  (b + k <= A_RO_LO \/ A_RO_END <= b) -> (b + k <= A_G_NAMES \/ A_G_NAMES + G_NAMES_SIZE <= b) ->
  apart p n b k /\ apart b k p n.
Proof.
  intros p n b k (q & j & -> & Hn & HR) Hb Hbk Hk H1 H2.
  unfold apart. c0_unf. destruct (Z.lt_total j 0) as [Hj|[Hj|Hj]]; [| subst j |]; lia.
Qed.

(* what a name in .rodata or g_names gives each callee whose frame is below sp = S - 480 *)
Lemma c0_fixed_ctx : forall E regs K p n, lenv_ok E -> spZ regs = e_S E - SLOT_FRAME -> 0 <= K <= 65056 ->
  c0_fixed_w p n ->
  apart_frame regs K p n /\ apart_gnl p n /\ apart A_ERRNO 4 p n /\ apart p n A_ERRNO 4 /\
  (p + n <= A_LONG_ALIAS \/ A_LONG_ALIAS + LONG_ALIAS_SIZE + 3 <= p) /\
  (forall a k, blk_out (e_S E) a k -> 0 < k -> apart a k p n /\ apart p n a k) /\
  (forall off k, 0 <= off -> 0 <= k -> off + k <= SLOT_FRAME ->
     apart (e_S E - SLOT_FRAME + off) k p n /\ apart p n (e_S E - SLOT_FRAME + off) k).
Proof.
  intros E regs K p n HE SP HK F. destruct HE as (HS1 & HS2 & _).
  assert (G : forall b k, 0 <= b -> b + k <= 2 ^ 64 -> 0 <= k -> (b + k <= A_RO_LO \/ A_RO_END <= b) ->
     (b + k <= A_G_NAMES \/ A_G_NAMES + G_NAMES_SIZE <= b) -> apart p n b k /\ apart b k p n)
    by (intros; apply c0_fixed_apart; assumption).
  unfold apart_frame, apart_gnl. rewrite SP. split; [|split; [|split; [|split; [|split; [|split]]]]].
  - destruct (G (e_S E - SLOT_FRAME - K) K) as [A _]; c0_unf; try lia. unfold apart in A. lia.
  - destruct (G A_G_NL NK_SIZE) as [A _]; c0_unf; try lia. unfold apart in A. lia.
  - destruct (G A_ERRNO 4) as [_ A]; c0_unf; try lia. exact A.
  - destruct (G A_ERRNO 4) as [A _]; c0_unf; try lia. exact A.
  - destruct (G A_LONG_ALIAS (LONG_ALIAS_SIZE + 3)) as [A _]; c0_unf; try lia. unfold apart in A. lia.
  - intros a k (B1 & B2 & B3) Hk. destruct (c0_img_free a k B3 Hk) as [Ha|Ha];
      destruct (G a k) as [A1 A2]; c0_unf; try lia; split; assumption.
  - intros off k H1 H2 H3. destruct (G (e_S E - SLOT_FRAME + off) k) as [A1 A2]; c0_unf; try lia.
    split; assumption.
Qed.

(* -------- the interface table -------- *)

Lemma c0_link_len : length link_tab = 64%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma c0_link_chk :
  forallb (fun i => match nth_error link_tab i with
                    | Some (nm, _) => c0_fixed_b (nth i link_ptrs 0) (Z.of_nat (length nm) + 1)
                                      && Nat.leb (length nm) 11
                    | None => true end) (seq 0 64) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma c0_link_fixed : forall i nm ix, nth_error link_tab i = Some (nm, ix) ->
  c0_fixed (nth i link_ptrs 0) (Z.of_nat (length nm) + 1) /\ (length nm <= 11)%nat.
Proof.
  intros i nm ix H.
  assert (Hi : (i < 64)%nat) by (rewrite <- c0_link_len; apply nth_error_Some; congruence).
  pose proof c0_link_chk as C. rewrite forallb_forall in C.
  specialize (C i ltac:(apply in_seq; lia)). rewrite H in C. apply andb_prop in C as [C1 C2].
  split; [exact (c0_fixed_b_ok _ _ C1) | exact (proj1 (Nat.leb_le _ _) C2)].
Qed.

Lemma c0_link_ptr_range : forall i, (i < 64)%nat -> A_RO_LO <= nth i link_ptrs 0 < A_G_NAMES + G_NAMES_SIZE.
Proof.
  intros i Hi. destruct (nth_error link_tab i) as [[nm ix]|] eqn:E.
  - destruct (c0_link_fixed i nm ix E) as [(Hn & [H|H]) _]; c0_unf; lia.
  - apply nth_error_None in E. rewrite c0_link_len in E. lia.
Qed.

(* the brief's form: a slot of g_nl.if_name holds exactly link_ptrs' entry *)
Lemma c0_ifptr_eq : forall m i p, ifptrs_at m -> (i < 64)%nat ->
  u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> 0 <= p < 2 ^ 64 -> p = nth i link_ptrs 0.
Proof.
  intros m i p IP Hi U R. apply (c0_u64_eq m _ p _ U (IP i Hi) R).
  pose proof (c0_link_ptr_range i Hi). c0_unf; lia.
Qed.

(* the name a `u64_at` of slot i points at, for any table iftab_at accepts *)
Lemma c0_ifname : forall m kbs tab i nm ix p,
  iftab_at m kbs link_tab -> ifptrs_at m -> iftab_at m kbs tab -> nth_error tab i = Some (nm, ix) ->
  u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
  c0_fixed_w p (Z.of_nat (length nm) + 1) /\ (length nm <= 11)%nat.
Proof.
  intros m kbs tab i nm ix p (NL & _ & L) IP (NT & _ & T) Hi Hp.
  assert (Lt : length tab = 64%nat) by (rewrite c0_link_len in NL; lia).
  assert (I64 : (i < 64)%nat) by (rewrite <- Lt; apply nth_error_Some; congruence).
  destruct (nth_error link_tab i) as [[nm0 ix0]|] eqn:E0;
    [| exfalso; apply nth_error_None in E0; rewrite c0_link_len in E0; lia].
  destruct (c0_link_fixed i nm0 ix0 E0) as [F0 L0].
  destruct (T i nm ix Hi) as (_ & p1 & U1 & _ & C1 & _).
  destruct (L i nm0 ix0 E0) as (_ & p2 & U2 & _ & C2 & _).
  pose proof (c0_link_ptr_range i I64) as Q.
  assert (R1 : 0 <= p1 < 2 ^ 64)
    by (destruct C1 as (B & _); apply bytes_at_bound in B; rewrite length_app in B; cbn [length] in B; lia).
  assert (R2 : 0 <= p2 < 2 ^ 64)
    by (destruct C2 as (B & _); apply bytes_at_bound in B; rewrite length_app in B; cbn [length] in B; lia).
  pose proof (c0_ifptr_eq m i p1 IP I64 U1 R1) as E1. pose proof (c0_ifptr_eq m i p2 IP I64 U2 R2) as E2.
  subst p1 p2. pose proof (c0_cstr_same m _ _ _ C1 C2) as <-.
  destruct (c0_u64_pin m _ p _ Hp (IP i I64) ltac:(c0_unf; lia)) as [k Ek].
  split; [exists (nth i link_ptrs 0), k; split; [exact Ek | exact F0] | exact L0].
Qed.

(* item 4 as one lemma a walk applies: every interface name, against every region a callee of the
   arm reads or writes *)
Lemma c0_ifname_ctx : forall E regs K m kbs, lenv_ok E -> spZ regs = e_S E - SLOT_FRAME -> 0 <= K <= 65056 ->
  iftab_at m kbs link_tab -> ifptrs_at m ->
  forall tab i nm ix p, iftab_at m kbs tab -> nth_error tab i = Some (nm, ix) ->
  u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
  let n := Z.of_nat (length nm) + 1 in
  (length nm <= 11)%nat /\
  apart_frame regs K p n /\ apart_gnl p n /\ apart A_ERRNO 4 p n /\ apart p n A_ERRNO 4 /\
  (p + n <= A_LONG_ALIAS \/ A_LONG_ALIAS + LONG_ALIAS_SIZE + 3 <= p) /\
  (forall a k, blk_out (e_S E) a k -> 0 < k -> apart a k p n /\ apart p n a k) /\
  (forall off k, 0 <= off -> 0 <= k -> off + k <= SLOT_FRAME ->
     apart (e_S E - SLOT_FRAME + off) k p n /\ apart p n (e_S E - SLOT_FRAME + off) k).
Proof.
  intros E regs K m kbs HE SP HK IL IP tab i nm ix p IT Hi Hp n.
  destruct (c0_ifname m kbs tab i nm ix p IL IP IT Hi Hp) as [F L]. split; [exact L|].
  exact (c0_fixed_ctx E regs K p n HE SP HK F).
Qed.

(* the interface table across a write set that misses g_nl.if_name / if_index and the names *)
Lemma c0_iftab_keep : forall W m m' kbs, iftab_at m kbs link_tab -> ifptrs_at m -> munch W m m' ->
  c0_out W (A_G_NL + NK_IF_NAME) 512 -> c0_out W (A_G_NL + NK_IF_INDEX) 256 -> c0_wfix W ->
  iftab_at m' kbs link_tab.
Proof.
  intros W m m' kbs (NI & LN & T) IP MU O1 O2 OF. split; [exact NI|]. split; [exact LN|].
  intros i nm ix Hi. destruct (T i nm ix Hi) as (Hix & p & U & NZ & C & U32). split; [exact Hix|].
  assert (I64 : (i < 64)%nat) by (rewrite <- c0_link_len; apply nth_error_Some; congruence).
  destruct (c0_link_fixed i nm ix Hi) as [F _].
  assert (Ep : p = nth i link_ptrs 0).
  { apply (c0_ifptr_eq m i p IP I64 U). destruct C as (B & _). apply bytes_at_bound in B.
    rewrite length_app in B. cbn [length] in B. lia. }
  exists p. split; [|split; [exact NZ|split]].
  - apply (c0_u64_keep W m m' _ _ U MU). eapply c0_out_sub; [exact O1| lia | lia].
  - rewrite Ep in C |- *. apply (c0_cstr_keep W m m' _ _ C MU). exact (c0_fixed_out W _ _ OF F).
  - apply (c0_u32_keep W m m' _ _ U32 MU). eapply c0_out_sub; [exact O2 | lia | lia].
Qed.

Lemma c0_policy_keep : forall W m m', policy_ro m -> munch W m m' -> c0_out W A_RO_LO (A_RO_END - A_RO_LO) ->
  policy_ro m'.
Proof.
  intros W m m' (C1 & C2 & C3 & C4) MU O.
  assert (L1 : length S_PREFIX = 8%nat) by reflexivity.
  assert (L2 : length S_SERVED = 14%nat) by reflexivity.
  assert (L3 : length S_VLAN = 4%nat) by reflexivity.
  split; [|split; [|split]].
  - apply (c0_cstr_keep W m m' _ _ C1 MU). rewrite L1.
    eapply c0_out_sub; [exact O | unfold A_PREFIX; c0_unf; lia | unfold A_PREFIX; c0_unf; lia].
  - apply (c0_cstr_keep W m m' _ _ C2 MU). rewrite L2.
    eapply c0_out_sub; [exact O | unfold A_SERVED; c0_unf; lia | unfold A_SERVED; c0_unf; lia].
  - apply (c0_cstr_keep W m m' _ _ C3 MU). rewrite L3.
    eapply c0_out_sub; [exact O | unfold A_VLAN; c0_unf; lia | unfold A_VLAN; c0_unf; lia].
  - apply (c0_cstr_keep W m m' _ _ C4 MU). cbn [length].
    eapply c0_out_sub; [exact O | unfold A_EMPTY; c0_unf; lia | unfold A_EMPTY; c0_unf; lia].
Qed.

(* -------- the selector's name (name_of, inlined) -------- *)

Lemma c0_gname_chk :
  forallb (fun k => negb (existsb (fun b => bz b =? 0) (gname (Z.of_nat k)))
                    && Nat.leb (length (gname (Z.of_nat k))) 4) (seq 0 64) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma c0_gname_ok : forall k, 0 <= k < 64 -> ~ In (zb 0) (gname k) /\ (length (gname k) <= 4)%nat.
Proof.
  intros k Hk. pose proof c0_gname_chk as C. rewrite forallb_forall in C.
  specialize (C (Z.to_nat k) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in C by lia.
  apply andb_prop in C as [C1 C2]. apply negb_true_iff in C1.
  split; [exact (c0_no_nul _ C1) | exact (proj1 (Nat.leb_le _ _) C2)].
Qed.

Lemma c0_odd_chk :
  forallb (fun j => c0_fixed_b (nth j odd_ptrs 0) (Z.of_nat (length (nth j odd_strs [])) + 1)
                    && Nat.leb (length (nth j odd_strs [])) 11 && negb (nth j odd_ptrs 0 =? 0))
          (seq 0 6) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma c0_odd_ok : forall j, (j < 6)%nat ->
  c0_fixed (nth j odd_ptrs 0) (Z.of_nat (length (nth j odd_strs [])) + 1) /\
  (length (nth j odd_strs []) <= 11)%nat /\ nth j odd_ptrs 0 <> 0.
Proof.
  intros j Hj. pose proof c0_odd_chk as C. rewrite forallb_forall in C.
  specialize (C j ltac:(apply in_seq; lia)).
  apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2]. apply negb_true_iff, Z.eqb_neq in C3.
  split; [exact (c0_fixed_b_ok _ _ C1)|]. split; [exact (proj1 (Nat.leb_le _ _) C2) | exact C3].
Qed.

Lemma c0_odd_keep : forall W m m', odd_at m -> munch W m m' -> c0_out W A_ODD (8 * ODD_N) -> c0_wfix W ->
  odd_at m'.
Proof.
  intros W m m' O MU O1 OF i Hi. destruct (O i Hi) as [U C]. split.
  - apply (c0_u64_keep W m m' _ _ U MU). eapply c0_out_sub; [exact O1| c0_unf; lia | c0_unf; lia].
  - apply (c0_cstr_keep W m m' _ _ C MU). apply (c0_fixed_out W _ _ OF). exact (proj1 (c0_odd_ok i Hi)).
Qed.

Lemma c0_sel_str : forall m s, 0 <= s < 256 -> gnames_at m -> odd_at m -> str_arg m (sel_ptr s) (sel_name s).
Proof.
  intros m s Hs G O. unfold str_arg, sel_name, sel_ptr.
  destruct (Z.eqb_spec s 255) as [->|N]; [reflexivity|].
  destruct (Z.ltb_spec s 64) as [L|L].
  - split; [unfold A_G_NAMES; lia|]. destruct (G s ltac:(lia)) as (rest & B & _).
    destruct (c0_gname_ok s ltac:(lia)) as [NZ _]. split; [|exact NZ].
    apply bytes_at_app in B as [B1 B2]. apply bytes_at_app. split; [exact B1|].
    change (zb 0 :: rest) with ([zb 0] ++ rest) in B2. apply bytes_at_app in B2 as [B3 _]. exact B3.
  - assert (Hj : (Z.to_nat (s mod 6) < 6)%nat) by (pose proof (Z.mod_pos_bound s 6); lia).
    destruct (O _ Hj) as [_ C]. destruct (c0_odd_ok _ Hj) as (_ & _ & NZ). split; [exact NZ | exact C].
Qed.

Lemma c0_sel_fixed : forall s t, 0 <= s < 256 -> sel_name s = Some t ->
  (length t <= 11)%nat /\ c0_fixed (sel_ptr s) (Z.of_nat (length t) + 1).
Proof.
  intros s t Hs. unfold sel_name, sel_ptr.
  destruct (Z.eqb_spec s 255) as [_|N]; [discriminate|].
  destruct (Z.ltb_spec s 64) as [L|L]; intros H; injection H as <-.
  - destruct (c0_gname_ok s ltac:(lia)) as [_ Len]. split; [lia|]. unfold c0_fixed. c0_unf. lia.
  - assert (Hj : (Z.to_nat (s mod 6) < 6)%nat) by (pose proof (Z.mod_pos_bound s 6); lia).
    destruct (c0_odd_ok _ Hj) as (F & Len & _). split; [exact Len | exact F].
Qed.

(* -------- the texts table: the eleven strings and the slack strlen reads, from the image -------- *)

Definition c0_texts_strs : list (list byte) := map (map zb)
  [[]; [114; 101; 97; 99; 45; 112; 119; 58; 115; 101; 114; 118; 101; 100];
   [114; 101; 97; 99; 45; 112; 119; 58; 109; 105; 110; 116; 101; 100];
   [104; 111; 115; 116; 45; 97; 108; 105; 97; 115]; [114; 101; 97; 99; 45; 112; 119; 58];
   [114; 101; 97; 99; 45; 112; 119; 58; 115; 101; 114; 118; 101; 100; 50];
   [114; 101; 97; 99; 45; 112; 119]; [118; 108; 97; 110]; [118; 101; 116; 104];
   [118; 108; 97; 110; 120]; [118; 108; 97]].

(* the image bytes at [a, a + n) *)
Definition c0_ro_take (a n : Z) : list byte :=
  map (fun j => match seg_rom rsegs (wa (a + Z.of_nat j)) with Some b => b | None => zb 0 end)
      (seq 0 (Z.to_nat n)).
(* the bytes after the NUL up to the next 8-byte boundary (strlen's word reads) *)
Definition c0_slack (p : Z) (s : list byte) : list byte :=
  c0_ro_take (p + Z.of_nat (length s) + 1) ((- (p + Z.of_nat (length s) + 1)) mod 8).

Fixpoint c0_ro_chk (a : Z) (bs : list byte) : bool :=
  match bs with
  | [] => true
  | b :: bs' => match seg_rom rsegs (wa a) with
                | Some b' => (bz b' =? bz b) && ro_addr rsegs (wa a) && c0_ro_chk (a + 1) bs'
                | None => false end
  end.

Lemma c0_ro_chk_ok : forall bs a, c0_ro_chk a bs = true -> ro_bytes rsegs a bs.
Proof.
  induction bs as [|b bs IH]; intros a H; cbn [c0_ro_chk] in H; cbn [ro_bytes]; [exact I|].
  destruct (seg_rom rsegs (wa a)) as [b'|] eqn:E; [|discriminate].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1.
  split; [split; [rewrite E; f_equal; apply bv_eq; exact H1 | exact H2] | exact (IH _ H3)].
Qed.

Lemma c0_texts_chk :
  forallb (fun i => let p := nth i texts_ptrs 0 in let s := nth i c0_texts_strs [] in
                    let sl := c0_slack p s in
                    c0_ro_chk p (s ++ zb 0 :: sl) && negb (existsb (fun b => bz b =? 0) s)
                    && ((- (p + Z.of_nat (length s) + 1)) mod 8 <=? Z.of_nat (length sl))
                    && (Z.of_nat (length s) <? NL_CHUNK_MAX)
                    && c0_fixed_b p (Z.of_nat (length s) + 1 + Z.of_nat (length sl))) (seq 0 11) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma c0_texts_img : forall m, mem_inv rsegs m -> forall i, (i < 11)%nat ->
  exists s slack, bytes_at rsegs m (nth i texts_ptrs 0) (s ++ zb 0 :: slack) /\ ~ In (zb 0) s /\
    (- (nth i texts_ptrs 0 + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack) /\
    Z.of_nat (length s) < NL_CHUNK_MAX /\
    c0_fixed (nth i texts_ptrs 0) (Z.of_nat (length s) + 1 + Z.of_nat (length slack)).
Proof.
  intros m MI i Hi. pose proof c0_texts_chk as C. rewrite forallb_forall in C.
  specialize (C i ltac:(apply in_seq; lia)). cbv zeta in C.
  apply andb_prop in C as [C C5]. apply andb_prop in C as [C C4].
  apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2].
  apply c0_fixed_b_ok in C5. apply negb_true_iff in C2. apply Z.leb_le in C3. apply Z.ltb_lt in C4.
  eexists; eexists. split; [|split; [exact (c0_no_nul _ C2)|split; [exact C3|split; [exact C4|exact C5]]]].
  apply (ro_bytes_at rsegs m); [exact MI | | | exact (c0_ro_chk_ok _ _ C1)];
    destruct C5 as (Hn & [H|H]); rewrite ?length_app; cbn [length]; c0_unf; lia.
Qed.

(* ==========================================================================
   7. The whole of c0_base across a write set inside the stack window
   ========================================================================== *)

(* the image-side views of c0_base that no callee of the arm writes, across any write set that misses
   g_names, the two pointer tables, .rodata, g_nl.if_name and the guard cells *)
Lemma c0_ro_keep : forall W m m', gnames_at m -> odd_at m -> policy_ro m -> texts_at m -> ifptrs_at m ->
  guard_m m -> munch W m m' ->
  c0_out W A_G_NAMES G_NAMES_SIZE -> c0_out W A_ODD (8 * ODD_N) -> c0_out W A_TEXTS (8 * TEXTS_N) ->
  c0_out W A_RO_LO (A_RO_END - A_RO_LO) -> c0_out W (A_G_NL + NK_IF_NAME) 512 ->
  c0_out W A_GOT_GUARD_S 8 -> c0_out W A_GUARD_S 8 ->
  gnames_at m' /\ odd_at m' /\ policy_ro m' /\ texts_at m' /\ ifptrs_at m' /\ guard_m m'.
Proof.
  intros W m m' GN OD PO TX IP GU MU O1 O2 O3 O4 O5 O6 O7.
  assert (OF : c0_wfix W) by (split; assumption).
  split; [exact (c0_gnames_keep W m m' GN MU O1)|].
  split; [exact (c0_odd_keep W m m' OD MU O2 OF)|].
  split; [exact (c0_policy_keep W m m' PO MU O4)|].
  split; [exact (c0_texts_keep W m m' TX MU O3)|].
  split; [exact (c0_ifptrs_keep W m m' IP MU O5)|].
  exact (c0_guard_keep W m m' GU MU O6 O7).
Qed.

Lemma c0_base_keep : forall E P N kbs mbs gbs m m' W, lenv_ok E ->
  c0_base E P N kbs mbs gbs m -> munch W m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  stk rsegs m' (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME) ->
  c0_in W (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME) ->
  c0_base E P N kbs mbs gbs m'.
Proof.
  intros E P N kbs mbs gbs m m' W HE
    (SV & NL & NW & IT & NO & NM & GN & OD & PO & LA & TX & IP & MD & MW & MK & KW & MA & CU & ER & GU & MI & TM & ST)
    MU WM MI' ST' HW.
  destruct HE as (HS1 & HS2 & _ & (D1 & D2 & _) & (K1 & K2 & _) & _ & _ & _ & HPL & (P1 & P2 & _) & _ & _ & HSV).
  assert (Img : c0_out W 0x10000 (0x960e0 - 0x10000))
    by (apply (c0_out_in W _ _ _ _ HW); c0_unf; lia).
  assert (OF : c0_wfix W) by (split; eapply c0_out_sub; [exact Img|c0_unf; lia|c0_unf; lia|exact Img|c0_unf; lia|c0_unf; lia]).
  unfold c0_base. repeat match goal with |- _ /\ _ => split end.
  - apply (c0_bytes_keep W m m' _ _ SV MU). apply (c0_out_in W _ _ _ _ HW); rewrite ?HSV; c0_unf; lia.
  - apply (c0_nlk_keep W m m' _ NL MU WM). eapply c0_out_sub; [exact Img|c0_unf; lia|c0_unf; lia].
  - exact NW.
  - apply (c0_iftab_keep W m m' kbs IT IP MU); [eapply c0_out_sub; [exact Img|c0_unf; lia|c0_unf; lia] ..
      | exact OF].
  - exact NO.
  - exact NM.
  - apply (c0_gnames_keep W m m' GN MU). eapply c0_out_sub; [exact Img|c0_unf; lia|c0_unf; lia].
  - apply (c0_odd_keep W m m' OD MU); [eapply c0_out_sub; [exact Img|c0_unf; lia|c0_unf; lia] | exact OF].
  - apply (c0_policy_keep W m m' PO MU). exact (proj1 OF).
  - apply (c0_la_keep W m m' LA MU WM). eapply c0_out_sub; [exact Img|c0_unf; lia|c0_unf; lia].
  - apply (c0_texts_keep W m m' TX MU). eapply c0_out_sub; [exact Img|c0_unf; lia|c0_unf; lia].
  - apply (c0_ifptrs_keep W m m' IP MU). eapply c0_out_sub; [exact Img|c0_unf; lia|c0_unf; lia].
  - apply (c0_model_keep W m m' _ _ MD MU WM). apply (c0_out_in W _ _ _ _ HW); c0_unf; lia.
  - exact MW.
  - apply (c0_marks_keep W m m' _ _ MK MU WM). apply (c0_out_in W _ _ _ _ HW); c0_unf; lia.
  - exact KW.
  - exact MA.
  - apply (c0_cursor_keep W m m' _ _ _ _ CU MU). apply (c0_out_in W _ _ _ _ HW); c0_unf; lia.
  - exact (wr_at_transport rsegs m m' _ _ ER WM).
  - apply (c0_guard_keep W m m' GU MU); (eapply c0_out_sub; [exact Img|c0_unf; lia|c0_unf; lia]).
  - exact MI'.
  - apply (c0_task_mem_in W m m' _ _ TM MU HW). c0_unf; lia.
  - exact ST'.
Qed.

(* ==========================================================================
   8. The two request lists, and the range of a reader's answer
   ========================================================================== *)

Lemma c0_requests_are : forall kbs mbs, nk_sent kbs = md_reqs mbs -> nk_n_sent kbs = md_n_req mbs ->
  nlk_wf kbs -> model_wf mbs -> Z.of_nat (length kbs) = NK_SIZE -> Z.of_nat (length mbs) = MD_SIZE ->
  requests_are kbs mbs.
Proof.
  intros kbs mbs ES EN WK WM LK LM. split; [exact EN|]. intros i Hi.
  destruct WK as (_ & _ & (S0 & S1) & _ & _ & _ & _ & _ & _ & _ & _ & _ & WKs).
  destruct WM as ((R0 & R1) & _ & _ & _ & WMs & _).
  assert (E : nk_sent_one kbs i = md_req_one mbs i).
  { apply (f_equal (fun l => nth_error l (Z.to_nat i))) in ES. unfold nk_sent, md_reqs in ES.
    rewrite !nth_error_map, !nth_error_seq in ES.
    destruct (Z.to_nat i <? Z.to_nat (nk_n_sent kbs))%nat eqn:B1; [|apply Nat.ltb_ge in B1; lia].
    destruct (Z.to_nat i <? Z.to_nat (md_n_req mbs))%nat eqn:B2; [|apply Nat.ltb_ge in B2; lia].
    cbn in ES. injection ES as ES. rewrite Z2Nat.id in ES by lia. exact ES. }
  split; [|exact E].
  pose proof (WKs i Hi) as HK. pose proof (WMs i ltac:(lia)) as HM.
  unfold nk_sent_one, md_req_one, slice in E. apply (f_equal (@length byte)) in E.
  rewrite !length_firstn, !length_skipn in E.
  unfold NK_SENT, NL_SENT_LEN, MD_REQ, NL_SENT_MAX, NK_SIZE, MD_SIZE, NK_SENT_LEN, MD_REQ_LEN in *. lia.
Qed.

Lemma c0_rd32s_range : forall c off, - 2 ^ 31 <= rd32s c off < 2 ^ 31.
Proof.
  intros c off. unfold rd32s. cbv zeta. unfold rd32, rdn.
  set (l := slice c off 4).
  assert (L : (length l <= 4)%nat)
    by (unfold l, slice; rewrite length_firstn; change (Z.to_nat 4) with 4%nat; lia).
  pose proof (bytes_le_to_Z_nonneg l) as H0. pose proof (bytes_le_to_Z_bound l) as H1.
  assert (H2 : 2 ^ (8 * Z.of_nat (length l)) <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
  destruct (Z.ltb_spec (bytes_le_to_Z l) (2 ^ 31)); lia.
Qed.

Lemma c0_msg_scan_err : forall fuel c off left code, msg_scan fuel c off left = NlErr code ->
  - 2 ^ 31 <= code < 2 ^ 31.
Proof.
  induction fuel as [|f IH]; intros c off left code H; cbn [msg_scan] in H; [discriminate|].
  cbv zeta in H.
  destruct (left <? NL_HDR); [discriminate|].
  destruct ((rd32 c off <? NL_HDR) || (left <? rd32 c off))%bool; [discriminate|].
  destruct (rd16 c (off + 4) =? NL_ERROR).
  - destruct (rd32 c off <? NL_HDR + NL_ERR_BODY); [discriminate|]. injection H as <-. apply c0_rd32s_range.
  - destruct (rd16 c (off + 4) =? RTM_NEWLINK); [discriminate|]. exact (IH _ _ _ _ H).
Qed.

Lemma c0_chunk_loop_err : forall fuel cs i code j, chunk_loop fuel cs i = (NlErr code, j) ->
  - 2 ^ 31 <= code < 2 ^ 31.
Proof.
  induction fuel as [|f IH]; intros cs i code j H; cbn [chunk_loop] in H; [discriminate|].
  destruct (nth_error cs i) as [c|]; [|discriminate].
  destruct (chunk_walk c) eqn:W; try discriminate.
  - exact (IH _ _ _ _ H).
  - injection H as <- _. exact (c0_msg_scan_err _ _ _ _ _ W).
Qed.

(* the answer of either reader on a well-formed kernel is an int32 *)
Lemma c0_read_rc_range : forall tab nm kc ac reqs K,
  0 <= k_sock K < 2 ^ 31 -> 0 <= k_send K < 2 ^ 31 -> 0 <= k_end K < 2 ^ 31 ->
  - 2 ^ 31 <= r_rc (read_core tab nm kc ac reqs K) < 2 ^ 31.
Proof.
  intros tab nm kc ac reqs K HS HD HE. unfold read_core.
  destruct nm as [s|]; [|cbn; unfold E_INVAL; lia].
  destruct (Nat.eqb (length s) 0); [cbn; unfold E_INVAL; lia|].
  destruct (index_of tab s =? 0); [cbn; unfold E_NODEV; lia|].
  cbn [r_rc]. unfold talk_rc_lib, talk_core.
  destruct (negb (k_sock K =? 0)); [cbn; lia|].
  destruct (negb (k_send K =? 0)); [cbn; lia|].
  destruct (chunk_loop _ _ _) as [v j] eqn:CL.
  destruct v as [| |code|a]; cbn; [lia | unfold E_IO; lia | exact (c0_chunk_loop_err _ _ _ _ _ CL) | lia].
Qed.

Lemma c0_read_rc_wf : forall tab nm kc ac reqs kbs, nlk_wf kbs ->
  - 2 ^ 31 <= r_rc (read_core tab nm kc ac reqs (nk_kstate kbs)) < 2 ^ 31.
Proof.
  intros tab nm kc ac reqs kbs (_ & _ & _ & _ & _ & _ & _ & _ & E1 & E2 & E3 & _).
  apply c0_read_rc_range; cbn [k_sock k_send k_end nk_kstate]; assumption.
Qed.

(* the texts a reader leaves fit in the cap *)
Lemma c0_rkind_len : forall tab nm kc ac reqs K, 0 <= kc ->
  Z.of_nat (length (r_kind (read_core tab nm kc ac reqs K))) <= Z.max 0 (kc - 1).
Proof.
  intros tab nm kc ac reqs K Hk. unfold read_core.
  destruct nm as [s|]; [|cbn; lia].
  destruct (Nat.eqb (length s) 0); [cbn; lia|].
  destruct (index_of tab s =? 0); [cbn; lia|]. cbn [r_kind].
  destruct (Z.ltb_spec kc 1); [cbn; lia|]. unfold text_of_attr.
  destruct (a_kind (talk_attrs K)) as [pay|]; [pose proof (cut_text_len pay kc ltac:(lia)); lia | cbn; lia].
Qed.

Lemma c0_ralias_len : forall tab nm kc ac reqs K, 0 <= ac ->
  Z.of_nat (length (r_alias (read_core tab nm kc ac reqs K))) <= Z.max 0 (ac - 1).
Proof.
  intros tab nm kc ac reqs K Hk. unfold read_core.
  destruct nm as [s|]; [|cbn; lia].
  destruct (Nat.eqb (length s) 0); [cbn; lia|].
  destruct (index_of tab s =? 0); [cbn; lia|]. cbn [r_alias].
  destruct (Z.ltb_spec ac 1); [cbn; lia|]. unfold text_of_attr.
  destruct (a_alias (talk_attrs K)) as [pay|]; [pose proof (cut_text_len pay ac ltac:(lia)); lia | cbn; lia].
Qed.
