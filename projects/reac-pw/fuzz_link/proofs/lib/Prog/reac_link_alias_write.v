(* reac_link_alias_write (reac_link_alias.c:121-149), PLAIN build: the walk of its contract
   (lib/Prog/reac_link_alias_write_c.v) on the plain image, 0x16290 .. 0x16378.

   Frame: 336 bytes, sp1 = sp - 336. ra s0 s1 s2 at sp1+0x148 .. sp1+0x130; the request at
   [sp1+0xc, sp1+0x130): memset zeroes [sp1+0x18, sp1+0x130), then the header words, the IFLA_IFALIAS
   header, memcpy of the alias at sp1+0x30, and the length word at sp1+0xc. The callees are taken
   by their contracts: strlen (0x1f2ac), fuzz_if_nametoindex (0x137c0), memset (0x1f060),
   memcpy (0x1ec5c), nl_talk (0x16008). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf mk_call mk_str mk_marks
  reac_link_alias_write_c index_of_c strlen_c memset_c memcpy_c nl_talk_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Memory facts
   ========================================================================== *)

Lemma munch_sym : forall W m m', munch W m m' -> munch W m' m.
Proof. intros W m m' H x Hx. symmetry. apply H, Hx. Qed.

Lemma disjoint_from_sub : forall W a n b k,
  disjoint_from W a n -> a <= b -> b + k <= a + n -> disjoint_from W b k.
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros a n b k H Hb Hk; [exact I|].
  destruct H as [H1 H2]. split; [lia|]. exact (IH a n b k H2 Hb Hk).
Qed.

Lemma wr_at_app : forall m A n1 n2, 0 <= n1 -> 0 <= n2 ->
  wr_at rsegs m A (n1 + n2) <-> wr_at rsegs m A n1 /\ wr_at rsegs m (A + n1) n2.
Proof.
  intros m A n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hl & H). split; (split; [lia|split; [lia|]]).
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (A + n1 + i) with (A + (n1 + i)) by lia. apply H. lia.
  - intros [(Ha & Hl & H) (Ha2 & Hl2 & H2')]. split; [lia|split; [lia|]].
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply H. lia.
    + replace (A + i) with (A + n1 + (i - n1)) by lia. apply H2'. lia.
Qed.

Lemma rw_cells_app2 : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) <->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add. split.
  - intros [[[W1 W2] B] Wr]. apply bytes_at_app in B. destruct B as [B1 B2].
    rewrite cells_bytes_length in B2 by exact W1.
    destruct (proj1 (wr_at_app m A (Z.of_nat (cells_size cs1)) (Z.of_nat (cells_size cs2)) ltac:(lia) ltac:(lia)) Wr)
      as [Wr1 Wr2].
    exact (conj (conj (conj W1 B1) Wr1) (conj (conj W2 B2) Wr2)).
  - intros [[[W1 B1] Wr1] [[W2 B2] Wr2]].
    rewrite <- (cells_bytes_length cs1 W1) in B2.
    split; [split; [split; assumption|]|].
    + apply bytes_at_app. split; assumption.
    + apply (proj2 (wr_at_app m A (Z.of_nat (cells_size cs1)) (Z.of_nat (cells_size cs2)) ltac:(lia) ltac:(lia))).
      split; assumption.
Qed.

(* one CB cell cut in two *)
Lemma rw_cells_CB_cut : forall m A (n k : nat) junk, (k <= n)%nat ->
  rw_cells rsegs m A [CB n junk] ->
  rw_cells rsegs m A [CB k (firstn k junk)] /\
  rw_cells rsegs m (A + Z.of_nat k) [CB (n - k) (skipn k junk)].
Proof.
  intros m A n k junk Hk H.
  pose proof (rw_cells_split_CB rsegs m A [] n junk [] [k; (n - k)%nat] H ltac:(cbn; lia)) as S.
  cbn [app mk_CB_cells] in S.
  change [CB k (firstn k junk); CB (n - k) (firstn (n - k) (skipn k junk))]
    with ([CB k (firstn k junk)] ++ [CB (n - k) (firstn (n - k) (skipn k junk))]) in S.
  apply rw_cells_app2 in S. destruct S as [S1 S2]. cbn [cells_size csize] in S2.
  rewrite Nat.add_0_r in S2. split; [exact S1|].
  destruct H as [[[Hw _] _] _]. cbn [cell_wf] in Hw.
  rewrite firstn_all2 in S2 by (rewrite length_skipn; lia). exact S2.
Qed.

Lemma rw_cells_bytes : forall m A cs, rw_cells rsegs m A cs -> bytes_at rsegs m A (cells_bytes cs).
Proof. intros m A cs [[_ B] _]. exact B. Qed.

Lemma stk_release_at : forall m lo A cs A', stk rsegs m lo A -> rw_cells rsegs m A cs -> lo <= A ->
  A' = A + Z.of_nat (cells_size cs) -> stk rsegs m lo A'.
Proof. intros m lo A cs A' S C L ->. eapply stk_release; eassumption. Qed.

(* ==========================================================================
   2. The fake kernel and the interface table
   ========================================================================== *)

Lemma nlk_at_unique : forall m k1 k2, nlk_at m k1 -> nlk_at m k2 -> k1 = k2.
Proof.
  intros m k1 k2 [[B1 _] L1] [[B2 _] L2].
  apply (bytes_at_unique m A_G_NL); [exact B1 | exact B2 | lia].
Qed.

Lemma wz_inj : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> wz a = wz b -> a = b.
Proof.
  intros a b Ha Hb E. rewrite <- (unsigned_lit a Ha), <- (unsigned_lit b Hb). unfold wz in E.
  rewrite E. reflexivity.
Qed.

Lemma u64_at_inj : forall m a p1 p2, u64_at m a p1 -> u64_at m a p2 -> wz p1 = wz p2.
Proof.
  intros m a p1 p2 H1 H2. unfold u64_at in *.
  pose proof (bytes_at_unique m a _ _ H1 H2 ltac:(rewrite !length_le8; reflexivity)) as E.
  apply (f_equal le_bytes_to_word) in E. rewrite !le_bytes_to_word_le8 in E. exact E.
Qed.

Lemma u32_at_inj : forall m a v1 v2, u32_at m a v1 -> u32_at m a v2 ->
  0 <= v1 < 2 ^ 31 -> 0 <= v2 < 2 ^ 31 -> v1 = v2.
Proof.
  intros m a v1 v2 H1 H2 R1 R2. unfold u32_at in *.
  pose proof (bytes_at_unique m a _ _ H1 H2 ltac:(rewrite !length_le4; reflexivity)) as E.
  apply (f_equal bytes_le_to_Z) in E. rewrite !bytes_le_to_Z_le4 in E. unfold wz in E.
  rewrite !unsigned_lit in E by lia. rewrite !Z.mod_small in E by lia. exact E.
Qed.

Lemma cstr_at_range : forall m p s, cstr_at m p s -> 0 <= p /\ p + Z.of_nat (length s) + 1 <= 2 ^ 64.
Proof.
  intros m p s [B _]. apply bytes_at_bound in B. rewrite length_app in B. cbn [length] in B. lia.
Qed.

Lemma iftab_at_unique : forall m k t1 t2, iftab_at m k t1 -> iftab_at m k t2 -> t1 = t2.
Proof.
  intros m k t1 t2 (L1 & _ & H1) (L2 & _ & H2).
  apply nth_error_ext. intros i.
  destruct (nth_error t1 i) as [[n1 x1]|] eqn:E1; destruct (nth_error t2 i) as [[n2 x2]|] eqn:E2.
  - destruct (H1 i n1 x1 E1) as (R1 & p1 & U1 & _ & C1 & I1).
    destruct (H2 i n2 x2 E2) as (R2 & p2 & U2 & _ & C2 & I2).
    pose proof (cstr_at_range _ _ _ C1). pose proof (cstr_at_range _ _ _ C2).
    assert (p1 = p2) by (apply wz_inj; [lia | lia | exact (u64_at_inj _ _ _ _ U1 U2)]). subst p2.
    rewrite (cstr_at_unique m n1 p1 n2 C1 C2), (u32_at_inj _ _ _ _ I1 I2 R1 R2). reflexivity.
  - apply nth_error_lt in E1. apply nth_error_None in E2. lia.
  - apply nth_error_None in E1. apply nth_error_lt in E2. lia.
  - reflexivity.
Qed.

Lemma nlk_move : forall W m m' k, nlk_at m k -> munch W m m' -> wmono rsegs m m' ->
  disjoint_from W A_G_NL NK_SIZE -> nlk_at m' k.
Proof.
  intros W m m' k [U L] MU WM D. split; [|exact L].
  eapply u8arr_transport; [exact U | exact MU | exact WM | rewrite L; exact D].
Qed.

Lemma cstr_move : forall W m m' a s, cstr_at m a s -> munch W m m' ->
  disjoint_from W a (Z.of_nat (length s) + 1) -> cstr_at m' a s.
Proof.
  intros W m m' a s [B N] MU D. split; [|exact N]. eapply bytes_at_transport; [exact B | exact MU |].
  rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. exact D.
Qed.

(* the C string, its NUL, then the first k readable bytes after it (strlen's slack) *)
Lemma str_slack_at : forall m a s sl k, cstr_at m a s -> bytes_at rsegs m (a + Z.of_nat (length s) + 1) sl ->
  bytes_at rsegs m a (s ++ Z_to_bv 8 0 :: firstn k sl).
Proof.
  intros m a s sl k [B _] SL.
  rewrite <- (firstn_skipn k sl) in SL. apply bytes_at_app in SL. destruct SL as [SL _].
  replace (s ++ Z_to_bv 8 0 :: firstn k sl) with ((s ++ [zb 0]) ++ firstn k sl)
    by (rewrite <- app_assoc; reflexivity).
  apply bytes_at_app. split; [exact B|]. rewrite length_app. cbn [length].
  replace (a + Z.of_nat (length s + 1)) with (a + Z.of_nat (length s) + 1) by lia. exact SL.
Qed.

Lemma dg_of : forall W, disjoint_from W A_G_NL NK_SIZE ->
  forall a n, A_G_NL + NK_IF_NAME <= a -> a + n <= A_G_NL + NK_SIZE -> disjoint_from W a n.
Proof. intros W D a n Ha Hn. eapply disjoint_from_sub; [exact D| |]; unfold NK_IF_NAME, NK_SIZE in *; lia. Qed.

Lemma rw_cells_cons : forall m A c cs, rw_cells rsegs m A (c :: cs) ->
  rw_cells rsegs m A [c] /\ rw_cells rsegs m (A + Z.of_nat (csize c)) cs.
Proof.
  intros m A c cs H. apply (rw_cells_app2 m A [c] cs) in H. cbn [cells_size] in H.
  rewrite Nat.add_0_r in H. exact H.
Qed.

Lemma iftab_at_move : forall W m m' k k' tab,
  iftab_at m k tab -> munch W m m' -> nk_n_if k' = nk_n_if k ->
  (forall a n, A_G_NL + NK_IF_NAME <= a -> a + n <= A_G_NL + NK_SIZE -> disjoint_from W a n) ->
  (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
     u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> disjoint_from W p (Z.of_nat (length n2) + 1)) ->
  iftab_at m' k' tab.
Proof.
  intros W m m' k k' tab (L & LB & H) MU Hn DG DN.
  split; [lia|]. split; [exact LB|].
  intros i nm ix E. destruct (H i nm ix E) as (R & p & U & Pn & C & I).
  pose proof (nth_error_lt _ _ _ E) as Hi.
  split; [exact R|]. exists p. split; [|split; [exact Pn|split]].
  - unfold u64_at in *. eapply bytes_at_transport; [exact U | exact MU |].
    rewrite length_le8. apply DG; unfold NK_IF_NAME, NK_SIZE; lia.
  - exact (cstr_move W m m' p nm C MU (DN i nm ix p E U)).
  - unfold u32_at in *. eapply bytes_at_transport; [exact I | exact MU |].
    rewrite length_le4. apply DG; unfold NK_IF_NAME, NK_IF_INDEX, NK_SIZE; lia.
Qed.

Lemma index_of_range : forall tab s,
  (forall i n ix, nth_error tab i = Some (n, ix) -> 0 <= ix < 2 ^ 31) -> 0 <= index_of tab s < 2 ^ 31.
Proof.
  induction tab as [|[n ix] tab IH]; intros s H; cbn [index_of]; [lia|].
  destruct (bl_eqb n s).
  - exact (H 0%nat n ix eq_refl).
  - apply IH. intros i n2 ix2 E. exact (H (S i) n2 ix2 E).
Qed.

Lemma talk_after_sock : forall K, k_sock (talk_after K) = 0.
Proof.
  intros K. unfold talk_after, talk_core.
  destruct (negb (k_sock K =? 0)); [reflexivity|].
  destruct (negb (k_send K =? 0)); [reflexivity|].
  destruct (chunk_loop _ _ _) as [v j]. destruct v; reflexivity.
Qed.

Lemma nk_n_sent_length : forall kbs, nlk_wf kbs -> nk_n_sent kbs = Z.of_nat (length (nk_sent kbs)).
Proof.
  intros kbs WF. unfold nk_sent. rewrite length_map, length_seq.
  destruct WF as (_ & _ & H & _). lia.
Qed.

Lemma nk_next_kstate : forall kbs, nlk_wf kbs -> nk_next kbs = Z.of_nat (k_next (nk_kstate kbs)).
Proof. intros kbs WF. cbn [nk_kstate k_next]. destruct WF as (_ & H & _). lia. Qed.

(* ==========================================================================
   3. The request
   ========================================================================== *)

Lemma land_508 : forall x, 0 <= x < 512 -> Z.land x 508 = 4 * (x / 4).
Proof.
  intros x Hx.
  assert (H : forallb (fun k => Z.eqb (Z.land (Z.of_nat k) 508) (4 * (Z.of_nat k / 4))) (seq 0 512) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H (Z.to_nat x)).
  rewrite in_seq, Z2Nat.id in H by lia. apply Z.eqb_eq, H. lia.
Qed.

Lemma skipn_repeat' : forall {X} (x : X) n k, skipn n (repeat x k) = repeat x (k - n).
Proof. intros X x n. induction n as [|n IH]; intros [|k]; cbn; try reflexivity. apply IH. Qed.

Lemma bytes_at_cat : forall m a l1 l2 b, bytes_at rsegs m a l1 -> b = a + Z.of_nat (length l1) ->
  bytes_at rsegs m b l2 -> bytes_at rsegs m a (l1 ++ l2).
Proof. intros m a l1 l2 b H1 E H2. subst b. apply bytes_at_app. split; assumption. Qed.

(* two byte lists with the same values are equal (a byte's range proof is not compared) *)
Lemma bl_ext : forall l1 l2 : list byte, map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

(* the word 0x50010 the walk stores at sp+0x10: type RTM_NEWLINK, flags NLM_F_REQUEST | NLM_F_ACK *)
Lemma hdr_split : Z_to_le_bytes 4 327696 = Z_to_le_bytes 2 RTM_NEWLINK ++ Z_to_le_bytes 2 (F_REQUEST + F_ACK).
Proof. apply bl_ext. vm_compute. reflexivity. Qed.

Lemma zeros8 : forall r : list byte, zeros 8 ++ r = zeros 4 ++ zeros 4 ++ r.
Proof. intros r. vm_compute. reflexivity. Qed.

(* The request as the walk leaves it: [A0+12, A0+24) the length, type/flags and seq words,
   [A0+24, A0+48) pid/family/type, the index, flags/change, the IFLA_IFALIAS header, then the
   alias and the zeros memset left. Its first `32 + nl_align (4 + len)` bytes are `req_write`. *)
Lemma req_bytes : forall m A0 A1 A2 A3 j L idx al z1 z2 z3,
  rw_cells rsegs m A0 [CB 12 j; C4 (Z_to_bv 64 L); C4 (Z_to_bv 64 327696); C4 (Z_to_bv 64 1)] ->
  rw_cells rsegs m A1 [CB 8 z1; C4 (Z_to_bv 64 idx); CB 8 z2; C2 (Z_to_bv 64 (Z.of_nat (length al) + 4));
                       C2 (Z_to_bv 64 20)] ->
  rw_cells rsegs m A2 [CB (length al) al] ->
  rw_cells rsegs m A3 [CB (256 - length al) z3] ->
  A1 = A0 + 24 -> A2 = A0 + 48 -> A3 = A0 + 48 + Z.of_nat (length al) ->
  z1 = zeros 8 -> z2 = zeros 8 -> z3 = repeat (zb 0) (256 - length al) ->
  Z.of_nat (length al) < 256 -> 0 <= idx < 2 ^ 31 -> L = 32 + nl_align (4 + Z.of_nat (length al)) ->
  bytes_at rsegs m (A0 + 12) (req_write idx al).
Proof.
  intros m A0 A1 A2 A3 j L idx al z1 z2 z3 H0 H1 H2 H3 E1 E2 E3 Z1 Z2 Z3 HL HI EL.
  subst A1 A2 A3 z1 z2 z3 L.
  pose proof (nl_align_le (4 + Z.of_nat (length al)) ltac:(lia)) as NA.
  pose proof H0 as [[[Wj _] _] _]. cbn [cell_wf] in Wj.
  apply rw_cells_bytes in H0, H1, H2, H3. cbn [cells_bytes cbytes] in H0, H1, H2, H3.
  rewrite ?app_nil_r in H0, H1, H2, H3.
  apply bytes_at_app in H0. destruct H0 as [_ H0]. rewrite Wj in H0. change (Z.of_nat 12) with 12 in H0.
  assert (BIG : bytes_at rsegs m (A0 + 12)
     ((le4 (Z_to_bv 64 (32 + nl_align (4 + Z.of_nat (length al)))) ++ le4 (Z_to_bv 64 327696)
         ++ le4 (Z_to_bv 64 1))
      ++ (zeros 8 ++ le4 (Z_to_bv 64 idx) ++ zeros 8 ++ le2 (Z_to_bv 64 (Z.of_nat (length al) + 4))
          ++ le2 (Z_to_bv 64 20))
      ++ al ++ repeat (zb 0) (256 - length al))).
  { apply (bytes_at_cat _ _ _ _ (A0 + 24)); [exact H0 | rewrite !length_app, !length_le4; lia |].
    apply (bytes_at_cat _ _ _ _ (A0 + 48));
      [exact H1 | unfold zeros; rewrite !length_app, !repeat_length, !length_le4, !length_le2; lia |].
    apply (bytes_at_cat _ _ _ _ (A0 + 48 + Z.of_nat (length al))); [exact H2 | reflexivity | exact H3]. }
  assert (TAIL : repeat (zb 0) (256 - length al)
      = zeros (nl_align (4 + Z.of_nat (length al)) - 4 - Z.of_nat (length al))
        ++ repeat (zb 0) (256 - length al
                          - Z.to_nat (nl_align (4 + Z.of_nat (length al)) - 4 - Z.of_nat (length al)))).
  { unfold zeros. rewrite <- repeat_app. f_equal. unfold nl_align in *. Z.div_mod_to_equations. lia. }
  apply (bytes_at_prefix _ _ _ (repeat (zb 0) (256 - length al
                          - Z.to_nat (nl_align (4 + Z.of_nat (length al)) - 4 - Z.of_nat (length al))))).
  eapply bytes_at_ext; [exact BIG|].
  rewrite TAIL. unfold le4, le2. rewrite !unsigned_lit by (unfold nl_align in *; Z.div_mod_to_equations; lia).
  rewrite (Z.add_comm (Z.of_nat (length al)) 4), hdr_split, (zeros8 (Z_to_le_bytes 4 idx ++ _)).
  unfold req_write, zeros. cbv zeta. rewrite <- !app_assoc. reflexivity.
Qed.

(* ==========================================================================
   4. The Post
   ========================================================================== *)

Definition rlaw_post (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop :=
  forall kbs tab nm al,
       nlk_at m kbs -> iftab_at m kbs tab ->
       str_arg m (arg regs 0) nm -> str_arg m (arg regs 1) al ->
       let W := write_lib tab nm al (nk_sent kbs) (nk_kstate kbs) in
       getr regs' 10 = wz (w_rc W)
       /\ (exists kbs', nlk_at m' kbs' /\ nlk_wf kbs'
             /\ nk_chunks kbs' = nk_chunks kbs /\ nk_end_errno kbs' = nk_end_errno kbs
             /\ nk_n_if kbs' = nk_n_if kbs /\ iftab_at m' kbs' tab
             /\ nk_next kbs' = Z.of_nat (k_next (w_state W))
             /\ nk_socket_errno kbs' = k_sock (w_state W)
             /\ nk_send_errno kbs' = k_send (w_state W)
             /\ nk_sent kbs' = w_reqs W /\ nk_n_sent kbs' = Z.of_nat (length (w_reqs W))
       /\ nk_open kbs' = 0 /\ nk_misuse kbs' = nk_misuse kbs
       /\ nk_opened kbs' - nk_closed kbs' = nk_opened kbs - nk_closed kbs
       /\ nk_opened kbs <= nk_opened kbs' <= nk_opened kbs + 1
             /\ ((nm = None \/ al = None \/ nm = Some []
                  \/ (forall s, al = Some s -> ALIAS_MAX <= Z.of_nat (length s))
                  \/ (forall s, nm = Some s -> index_of tab s = 0)) ->
                   nk_opened kbs' = nk_opened kbs)).

Lemma post_of : forall W (R R' : bvmap 5 word) m m' kbs tab nm al kbs' Wr,
  nlk_at m kbs -> iftab_at m kbs tab -> str_arg m (arg R 0) nm -> str_arg m (arg R 1) al ->
  munch W m m' ->
  (forall a n, A_G_NL + NK_IF_NAME <= a -> a + n <= A_G_NL + NK_SIZE -> disjoint_from W a n) ->
  (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
     u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> disjoint_from W p (Z.of_nat (length n2) + 1)) ->
  Wr = write_lib tab nm al (nk_sent kbs) (nk_kstate kbs) ->
  getr R' 10 = wz (w_rc Wr) ->
  nlk_at m' kbs' -> nlk_wf kbs' -> nk_chunks kbs' = nk_chunks kbs -> nk_end_errno kbs' = nk_end_errno kbs ->
  nk_n_if kbs' = nk_n_if kbs ->
  nk_next kbs' = Z.of_nat (k_next (w_state Wr)) ->
  nk_socket_errno kbs' = k_sock (w_state Wr) -> nk_send_errno kbs' = k_send (w_state Wr) ->
  nk_sent kbs' = w_reqs Wr -> nk_n_sent kbs' = Z.of_nat (length (w_reqs Wr)) ->
  nk_open kbs' = 0 -> nk_misuse kbs' = nk_misuse kbs ->
  nk_opened kbs' - nk_closed kbs' = nk_opened kbs - nk_closed kbs ->
  nk_opened kbs <= nk_opened kbs' <= nk_opened kbs + 1 ->
  ((nm = None \/ al = None \/ nm = Some []
    \/ (forall s, al = Some s -> ALIAS_MAX <= Z.of_nat (length s))
    \/ (forall s, nm = Some s -> index_of tab s = 0)) -> nk_opened kbs' = nk_opened kbs) ->
  rlaw_post R m R' m'.
Proof.
  intros W R R' m m' kbs tab nm al kbs' Wr N T S A MU DG DN EW RC N' WF' CH EE NI NX SK SD ST NS OP MS OC OB OR.
  intros kbs1 tab1 nm1 al1 N1 T1 S1 A1.
  assert (kbs1 = kbs) by (eapply nlk_at_unique; eassumption). subst kbs1.
  assert (tab1 = tab) by (eapply iftab_at_unique; eassumption). subst tab1.
  assert (nm1 = nm) by (eapply str_arg_unique; eassumption). subst nm1.
  assert (al1 = al) by (eapply str_arg_unique; eassumption). subst al1.
  cbv zeta. rewrite <- EW. split; [exact RC|]. exists kbs'.
  exact (conj N' (conj WF' (conj CH (conj EE (conj NI (conj (iftab_at_move W m m' kbs kbs' tab T MU NI DG DN)
          (conj NX (conj SK (conj SD (conj ST (conj NS (conj OP (conj MS (conj OC (conj OB OR))))))))))))))).
Qed.

(* a refusal: nothing of the fake kernel moves *)
Lemma post_refuse : forall W (R R' : bvmap 5 word) m m' kbs tab nm al rc,
  nlk_at m kbs -> nlk_wf kbs -> nk_open kbs = 0 -> iftab_at m kbs tab ->
  str_arg m (arg R 0) nm -> str_arg m (arg R 1) al ->
  munch W m m' -> wmono rsegs m m' -> disjoint_from W A_G_NL NK_SIZE ->
  (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
     u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> disjoint_from W p (Z.of_nat (length n2) + 1)) ->
  write_lib tab nm al (nk_sent kbs) (nk_kstate kbs) = Wres rc (nk_sent kbs) (nk_kstate kbs) ->
  getr R' 10 = wz rc ->
  rlaw_post R m R' m'.
Proof.
  intros W R R' m m' kbs tab nm al rc N WF OP T S A MU WM D DN EW RC.
  refine (post_of W R R' m m' kbs tab nm al kbs (Wres rc (nk_sent kbs) (nk_kstate kbs)) N T S A MU _ DN
            (eq_sym EW) RC _ WF eq_refl eq_refl eq_refl _ eq_refl eq_refl eq_refl _ OP eq_refl eq_refl _ _).
  - intros a n Ha Hn. eapply disjoint_from_sub; [exact D| |]; unfold NK_IF_NAME, NK_SIZE in *; lia.
  - exact (nlk_move W m m' kbs N MU WM D).
  - cbn [w_state]. apply nk_next_kstate. exact WF.
  - cbn [w_reqs]. apply nk_n_sent_length. exact WF.
  - lia.
  - intros _. reflexivity.
Qed.

(* ==========================================================================
   5. The walk
   ========================================================================== *)

Ltac ul := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end.
Ltac ul_in H :=
  repeat match type of H with context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) in H by lia end.
Ltac dj := cbn [disjoint_from]; repeat split; lia.

(* `call` of Tac.v, with the callee's `bv_unsigned (Z_to_bv 64 e)` read back before the transport *)
Ltac my_post_call segs m :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO; destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  ul_in MUc; try ul_in PO;
  lazymatch type of MUc with
  | munch _ m ?m' =>
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

(* the readings of an `mkR` map, stated without the `Let` of mk_leaf.v's Section Get *)
Section R.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Lemma rR_sp : spZ (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
  = bv_unsigned sp. Proof. reflexivity. Qed.
Lemma rR_a0 : arg (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) 0
  = bv_unsigned a0. Proof. reflexivity. Qed.
Lemma rR_a1 : arg (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) 1
  = bv_unsigned a1. Proof. reflexivity. Qed.
Lemma rR_a2 : arg (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) 2
  = bv_unsigned a2. Proof. reflexivity. Qed.
Lemma rR_a3 : arg (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) 3
  = bv_unsigned a3. Proof. reflexivity. Qed.
Lemma rR_a4 : arg (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) 4
  = bv_unsigned a4. Proof. reflexivity. Qed.
Lemma rR_a5 : arg (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) 5
  = bv_unsigned a5. Proof. reflexivity. Qed.
Lemma rR_errno : errno_at (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
  = bv_unsigned tp + ERRNO_TP_OFF. Proof. reflexivity. Qed.
Lemma rR_r10 : getr (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) 10
  = a0. Proof. reflexivity. Qed.
End R.
Ltac rR := rewrite ?rR_sp, ?rR_a0, ?rR_a1, ?rR_a2, ?rR_a3, ?rR_a4, ?rR_a5, ?rR_errno, ?rR_r10.
Ltac rR_in H := rewrite ?rR_sp, ?rR_a0, ?rR_a1, ?rR_a2, ?rR_a3, ?rR_a4, ?rR_a5, ?rR_errno, ?rR_r10 in H.

(* the step tactics leave the register file as the tree `mkR` unfolds to; the call lemmas want `mkR` *)
Ltac refold_mkR :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    lazymatch R with
    | TNode
        (TNode (TNode (TNode (TNode (TNode TEmpty (Some ?x31) TEmpty) (Some ?x15) TEmpty) (Some ?x7) (TNode TEmpty (Some ?x23) TEmpty)) (Some ?x3) (TNode (TNode TEmpty (Some ?x19) TEmpty) (Some ?x11) (TNode TEmpty (Some ?x27) TEmpty)))
           (Some ?x1) (TNode (TNode (TNode TEmpty (Some ?x17) TEmpty) (Some ?x9) (TNode TEmpty (Some ?x25) TEmpty)) (Some ?x5) (TNode (TNode TEmpty (Some ?x21) TEmpty) (Some ?x13) (TNode TEmpty (Some ?x29) TEmpty))))
        None
        (TNode (TNode (TNode (TNode TEmpty (Some ?x16) TEmpty) (Some ?x8) (TNode TEmpty (Some ?x24) TEmpty)) (Some ?x4) (TNode (TNode TEmpty (Some ?x20) TEmpty) (Some ?x12) (TNode TEmpty (Some ?x28) TEmpty))) (Some ?x2)
           (TNode (TNode (TNode TEmpty (Some ?x18) TEmpty) (Some ?x10) (TNode TEmpty (Some ?x26) TEmpty)) (Some ?x6) (TNode (TNode TEmpty (Some ?x22) TEmpty) (Some ?x14) (TNode TEmpty (Some ?x30) TEmpty))))
      => change R with (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                           x24 x25 x26 x27 x28 x29 x30 x31)
    | mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac
    end
  end.

(* a branch whose condition the context decides *)
Ltac my_solve_cond := unfold_cond; ul; fold_lit_ux; solve_cond_rec.
Ltac br :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      first [ replace c with true; [cbv iota | symmetry; my_solve_cond]
            | replace c with false; [cbv iota | symmetry; my_solve_cond] ]
  end.

Lemma ret_lit : forall n, 0 <= n < 2 ^ 64 -> n mod 2 = 0 -> ret_pc (Z_to_bv 64 n) = Z_to_bv 64 n.
Proof. intros n H1 H2. apply ret_pc_even; assumption. Qed.
Ltac fix_ret :=
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      rewrite (ret_lit n) by (first [lia | reflexivity])
  end).

Theorem reac_link_alias_write_holds :
  fuzz_if_nametoindex_contract -> strlen_contract -> memset_contract -> memcpy_contract -> nl_talk_contract ->
  reac_link_alias_write_contract.
Proof.
  intros HIX HSL HMS HMC HNT. unfold reac_link_alias_write_contract. apply leaf_intro.
  - intros r1 r2 m E H. cbv beta in H |- *.
    assert (E0 : arg r1 0 = arg r2 0) by (unfold arg; rewrite E; reflexivity).
    assert (E1 : arg r1 1 = arg r2 1) by (unfold arg; rewrite E; reflexivity).
    assert (EE : errno_at r1 = errno_at r2) by (unfold errno_at; rewrite E; reflexivity).
    assert (ES : spZ r1 = spZ r2) by (unfold spZ; rewrite E; reflexivity).
    unfold frame_apart_gnl, apart_frame in H |- *. rewrite E0, E1, EE, ES in H. exact H.
  - intros r1 r2 m E. cbv beta. unfold errno_at. rewrite E. reflexivity.
  - intros r1 r2 m q1 q2 m' E Eq H. cbv beta in H |- *.
    assert (E0 : arg r1 0 = arg r2 0) by (unfold arg; rewrite E; reflexivity).
    assert (E1 : arg r1 1 = arg r2 1) by (unfold arg; rewrite E; reflexivity).
    rewrite E0, E1, (Eq _) in H. exact H.
  - unfold leaf_walk, REAC_LINK_ALIAS_WRITE.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
    cbv zeta. intros HPre MI ST LO SP. cbv beta in HPre.
    lazymatch goal with |- evt _ ?q _ => set (Q := q) end.
    assert (HQ : q_ext Q).
    { unfold Q. apply leaf_q_ext. intros q1 q2 m' E H. cbv beta in H |- *.
      intros kbs1 tab1 nm1 al1 N1 T1 S1 A1. specialize (H kbs1 tab1 nm1 al1 N1 T1 S1 A1).
      cbv zeta in H |- *. rewrite <- (E _). exact H. }
    destruct HPre as (kbs & tab & nm & al & NL & FG & WF & OPEN & OPC & CLC & TAB & ERRW & ERRF & ERRG
                      & SNM & SAL & TABA & NMA & ALA & SLK).
    unfold frame_apart_gnl, apart_frame, apart_gnl, apart in FG, ERRF, ERRG, TABA, NMA, ALA.
    rR_in SNM. rR_in SAL. rR_in NMA. rR_in ALA. rR_in SLK. rR_in ERRW. rR_in ERRF. rR_in ERRG. rR_in TABA.
    rR_in FG.
    pose (R0 := mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof (zr_word a0) as Ra0. unfold inr64 in Ra0.
    pose proof (zr_word a1) as Ra1. unfold inr64 in Ra1.
    assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
    assert (TABL : Z.of_nat (length tab) <= 80) by (destruct TAB as (_ & H & _); exact H).
    assert (NKS : NK_SIZE = 271992) by reflexivity.
    assert (NKN : NK_N_SENT = 271016) by reflexivity.
    assert (NKI : NK_IF_NAME = 271024) by reflexivity.
    assert (DN0 : forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
        u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
        disjoint_from [(bv_unsigned sp - 384, bv_unsigned sp)] p (Z.of_nat (length n2) + 1)).
    { intros i n2 ix p E U. destruct (TABA i n2 ix p E U) as (T1 & _ & _). dj. }
    assert (DG0 : disjoint_from [(bv_unsigned sp - 384, bv_unsigned sp)] A_G_NL NK_SIZE) by dj.
    pose proof (munch_refl ((bv_unsigned sp - 16928, bv_unsigned sp)
      :: [(A_G_NL, A_G_NL + NK_N_SENT + 4); (bv_unsigned tp + ERRNO_TP_OFF, bv_unsigned tp + ERRNO_TP_OFF + 4)]) m)
      as MU.
    pose proof (munch_refl [(bv_unsigned sp - 384, bv_unsigned sp)] m) as MF.
    pose proof (wmono_refl rsegs m) as WM.
    carve_frame 336%nat ST.
    zstep. zstep. zstep. zstep. zstep.          (* the prologue *)
    zstep. zstep. zstep.                        (* mv s2, a0; li a0, -22; beqz s2 *)
    destruct nm as [s|].
    2:{ (* name NULL *)
      cbn [str_arg] in SNM. br.
      zstep. zstep. zstep. zstep. zstep.
      release_frame FR ST (bv_unsigned sp).
      zstep.
      apply evt_done. unfold Q. do 2 eexists. split; [reflexivity|].
      split; [apply regs_preserved_mkR|].
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      refine (post_refuse _ R0 _ m _ kbs tab None al (-22) NL WF OPEN TAB SNM SAL MF WM DG0 DN0 _ _);
        reflexivity. }
    destruct SNM as [NNZ NC]. br.
    zstep. zstep.                               (* mv s0, a1; beqz a1 *)
    destruct al as [a|].
    2:{ (* alias NULL *)
      cbn [str_arg] in SAL. br.
      zstep. zstep. zstep. zstep. zstep.
      release_frame FR ST (bv_unsigned sp).
      zstep.
      apply evt_done. unfold Q. do 2 eexists. split; [reflexivity|].
      split; [apply regs_preserved_mkR|].
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      refine (post_refuse _ R0 _ m _ kbs tab (Some s) None (-22) NL WF OPEN TAB (conj NNZ NC) SAL MF WM DG0 DN0
               _ _); reflexivity. }
    destruct SAL as [ANZ AC]. br.
    pose proof (cstr_at_range _ _ _ NC) as NCR. pose proof (cstr_at_range _ _ _ AC) as ACR.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (NC1 : cstr_at mc (bv_unsigned a0) s) end.
    { apply (cstr_move _ m _ _ _ NC MF). destruct (NMA s eq_refl) as [N1 _]. dj. }
    destruct s as [|b s'].
    { (* name empty *)
      match goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        assert (HR : ov_read_bytes rsegs mc a0 1 = Some [Z_to_bv 8 0]) end.
      { destruct NC1 as [B _]. exact (bytes_at_read1 _ a0 _ [] B). }
      zstep. zstep. br.                         (* lbu a1, 0(s2); beqz a1 *)
      zstep. zstep. zstep. zstep. zstep.
      release_frame FR ST (bv_unsigned sp).
      zstep.
      apply evt_done. unfold Q. do 2 eexists. split; [reflexivity|].
      split; [apply regs_preserved_mkR|].
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      refine (post_refuse _ R0 _ m _ kbs tab (Some []) (Some a) (-22) NL WF OPEN TAB (conj NNZ NC) (conj ANZ AC)
               MF WM DG0 DN0 _ _); reflexivity. }
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (HR : ov_read_bytes rsegs mc a0 1 = Some [b]) end.
    { destruct NC1 as [B _]. exact (bytes_at_read1 _ a0 _ _ B). }
    assert (HB : bv_unsigned b <> 0).
    { intros E. pose proof NC as [_ NN]. apply NN. left. apply byte_zero. exact E. }
    pose proof (byte_range b) as RB.
    zstep. zstep. br.                           (* lbu a1, 0(s2); beqz a1 *)
    zstep. zstep.                               (* mv a0, s0; jal strlen *)
    destruct (SLK a eq_refl) as (sl & SLB & SLL).
    destruct (ALA a eq_refl) as [AF _].
    destruct AC as [ACB ACN].
    pose proof (Z.mod_pos_bound (- (bv_unsigned a1 + Z.of_nat (length a) + 1)) 8 ltac:(lia)) as KB.
    assert (FK : Z.of_nat (length (firstn (Z.to_nat ((- (bv_unsigned a1 + Z.of_nat (length a) + 1)) mod 8)) sl))
                 = (- (bv_unsigned a1 + Z.of_nat (length a) + 1)) mod 8).
    { rewrite length_firstn. lia. }
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (ASL : bytes_at rsegs mc (bv_unsigned a1)
                (a ++ Z_to_bv 8 0 :: firstn (Z.to_nat ((- (bv_unsigned a1 + Z.of_nat (length a) + 1)) mod 8)) sl))
    end.
    { eapply bytes_at_transport; [ apply str_slack_at; [exact (conj ACB ACN) | exact SLB] | exact MF | ].
      rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add, Nat2Z.inj_succ, FK. dj. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evt_cut; [ eapply HSL; [exact ASL | exact ACN | rewrite FK; lia | assumption] | my_post_call rsegs mc ]
    end.
    zstep. zstep.                               (* li a1, 255; bgeu a1, a0 *)
    destruct (Z_lt_le_dec (Z.of_nat (length a)) 256) as [LT|GE].
    2:{ (* alias too long *)
      br. zstep. zstep.
      zstep. zstep. zstep. zstep. zstep.
      release_frame FR ST (bv_unsigned sp).
      zstep.
      apply evt_done. unfold Q. do 2 eexists. split; [reflexivity|].
      split; [apply regs_preserved_mkR|].
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      refine (post_refuse _ R0 _ m _ kbs tab (Some (b :: s')) (Some a) (-36) NL WF OPEN TAB (conj NNZ NC)
               (conj ANZ (conj ACB ACN)) MF WM DG0 DN0 _ _); [|reflexivity].
      unfold write_lib, write_core. cbn [length Nat.eqb].
      replace (ALIAS_MAX <=? Z.of_nat (length a)) with true by (symmetry; apply Z.leb_le; unfold ALIAS_MAX; lia).
      reflexivity. }
    br. zstep. zstep. zstep.                    (* mv s1, a0; mv a0, s2; jal fuzz_if_nametoindex *)
    refold_mkR.
    (* fuzz_if_nametoindex (0x137c0): its frame is [sp-384, sp-336) *)
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (NL1 : nlk_at mc kbs) by exact (nlk_move _ m mc kbs NL MF WM DG0);
      assert (TAB1 : iftab_at mc kbs tab) by exact (iftab_at_move _ m mc kbs kbs tab TAB MF eq_refl (dg_of _ DG0) DN0);
      assert (NC2 : cstr_at mc (bv_unsigned a0) (b :: s'))
        by (apply (cstr_move _ m _ _ _ NC MF); destruct (NMA _ eq_refl) as [N1 _]; dj)
    end.
    pose proof HIX as HIX'. unfold fuzz_if_nametoindex_contract, index_of_contract, FUZZ_IF_NAMETOINDEX in HIX'.
    eapply (leaf_call _ _ _ _ _ HIX').
    { intros r1 r2 mm q1 q2 mm' E Eq H. cbv beta in H |- *.
      intros bs tb nmm N T C. rewrite <- (Eq _). apply (H bs tb nmm N T). unfold arg in C |- *. rewrite E. exact C. }
    { exact HQ. }
    { cbv beta. exists kbs, tab, (b :: s'). unfold frame_apart_gnl, apart_frame, apart_gnl. rR. ul.
      refine (conj NL1 (conj _ (conj TAB1 (conj NNZ (conj NC2 (conj _ _)))))).
      - lia.
      - destruct (NMA _ eq_refl) as [N1 _]. lia.
      - intros i n2 ix p E U. pose proof (nth_error_lt _ _ _ E) as Hi.
        assert (U0 : u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p).
        { unfold u64_at in *. eapply bytes_at_transport; [exact U | exact (munch_sym _ _ _ MF) |].
          rewrite length_le8. apply (dg_of _ DG0); unfold NK_IF_NAME, NK_SIZE; lia. }
        destruct (TABA i n2 ix p E U0) as (T1 & _ & _). lia. }
    { assumption. }
    { rR. ul. exact ST. }
    { rR. ul. lia. }
    { ul. lia. }
    intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 MUc WMc MIc STc POc.
    cbv [writes_nothing] in MUc. ul_in MUc. ul_in STc.
    cbv beta in POc. specialize (POc kbs tab (b :: s') NL1 TAB1 NC2). rR_in POc. subst a0'.
    lazymatch type of MUc with munch _ ?mc _ => transport_after_call rsegs mc m2 MUc WMc end.
    clear MUc WMc. try clear ST. rename STc into ST.
    fix_ret.
    pose proof (index_of_range tab (b :: s')
      (fun i n ix E => proj1 (proj2 (proj2 TAB) i n ix E))) as IXR.
    remember (index_of tab (b :: s')) as idx eqn:EIDX. unfold wz.
    zstep.                                      (* beqz a0 *)
    destruct (Z.eq_dec idx 0) as [I0|INZ].
    { (* no such interface *)
      br. zstep.
      zstep. zstep. zstep. zstep. zstep.
      release_frame FR ST (bv_unsigned sp).
      zstep.
      apply evt_done. unfold Q. do 2 eexists. split; [reflexivity|].
      split; [apply regs_preserved_mkR|].
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      refine (post_refuse _ R0 _ m _ kbs tab (Some (b :: s')) (Some a) (-19) NL WF OPEN TAB (conj NNZ NC)
               (conj ANZ (conj ACB ACN)) MF WM DG0 DN0 _ _); [|reflexivity].
      unfold write_lib, write_core. cbn [length Nat.eqb].
      replace (ALIAS_MAX <=? Z.of_nat (length a)) with false by (symmetry; apply Z.leb_gt; unfold ALIAS_MAX; lia).
      rewrite <- EIDX, I0. reflexivity. }
    br.
    (* the frame in three: [sp-336, sp-312), the memset window [sp-312, sp-32), the saved registers *)
    destruct (rw_cells_cons _ _ _ _ FR) as [F01 F2]. clear FR. cbn [csize] in F2.
    replace (bv_unsigned sp + -336 + Z.of_nat 304) with (bv_unsigned sp + -32) in F2 by lia.
    destruct (rw_cells_CB_cut _ _ 304 24 _ ltac:(lia) F01) as [F0 F1]. clear F01.
    replace (bv_unsigned sp + -336 + Z.of_nat 24) with (bv_unsigned sp + -312) in F1 by lia.
    change (304 - 24)%nat with 280%nat in F1.
    zstep. zstep. zstep. zstep. zstep.          (* mv s2, a0; addi a0, sp, 0x18; li a2, 0x118; mv a1, zero; jal *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evt_cut; [ eapply HMS; [ ul; exact F1 | assumption ] | my_post_call rsegs mc ]
    end.
    (* the zeroed window in three: the header tail [sp-312, sp-288), the alias, the padding *)
    lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -312) [CB (Z.to_nat 280) _] |- _ =>
      change (Z.to_nat 280) with 280%nat in H;
      destruct (rw_cells_CB_cut _ _ 280 24 _ ltac:(lia) H) as [G1 G23]; clear H
    end.
    replace (bv_unsigned sp + -312 + Z.of_nat 24) with (bv_unsigned sp + -288) in G23 by lia.
    change (280 - 24)%nat with 256%nat in G23.
    destruct (rw_cells_CB_cut _ _ 256 (length a) _ ltac:(lia) G23) as [G2 G3]. clear G23.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.  (* the header stores *)
    zstep. zstep. zstep. zstep.                 (* addi a0, sp, 0x30; mv a1, s0; mv a2, s1; jal memcpy *)
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (CM : cstr_at mc (bv_unsigned a1) a) by (apply (cstr_move _ m _ _ _ (conj ACB ACN) MF); dj)
    end.
    pose proof (bytes_at_prefix _ _ _ _ (proj1 CM)) as AB.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evt_cut;
      [ eapply HMC; [ exact AB | ul; rewrite Nat2Z.id; reflexivity | ul; rewrite Nat2Z.id; exact G2 | ul; lia
                    | assumption ]
      | my_post_call rsegs mc ]
    end.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -288) _ /\ _ |- _ => destruct H as [G2 _] end.
    rewrite Nat2Z.id in G2.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.  (* the length word; jal nl_talk *)
    refold_mkR.
    (* nl_talk (0x16008) on the request [sp-324, sp-324+len'); its frame is [sp-16928, sp-336) *)
    assert (LB : 0 <= Z.land (Z.of_nat (length a) + 7) 508 /\ Z.land (Z.of_nat (length a) + 7) 508 + 32 <= 292).
    { rewrite land_508 by lia. Z.div_mod_to_equations. lia. }
    assert (RL : Z.of_nat (length (req_write idx a)) = Z.land (Z.of_nat (length a) + 7) 508 + 32).
    { rewrite req_write_len by (unfold ALIAS_MAX; lia). rewrite land_508 by lia. unfold nl_align, RTA_HDR.
      replace (4 + Z.of_nat (length a) + 3) with (Z.of_nat (length a) + 7) by lia. lia. }
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (NL2 : nlk_at mc kbs) by exact (nlk_move _ m mc kbs NL MF WM DG0);
      assert (REQ : bytes_at rsegs mc (bv_unsigned sp + -324) (req_write idx a))
    end.
    { replace (bv_unsigned sp + -324) with (bv_unsigned sp + -336 + 12) by lia.
      eapply req_bytes;
        [exact F0 | exact G1 | exact G2 | exact G3 | lia | lia | lia | reflexivity | reflexivity | | lia | lia | ].
      - rewrite !skipn_repeat'. reflexivity.
      - rewrite land_508 by lia. unfold nl_align.
        replace (4 + Z.of_nat (length a) + 3) with (Z.of_nat (length a) + 7) by lia. lia. }
    pose proof HNT as HNT'. unfold nl_talk_contract, NL_TALK in HNT'.
    eapply (leaf_call _ _ _ _ _ HNT').
    { intros r1 r2 mm q1 q2 mm' E Eq H. cbv beta in H |- *. unfold arg in *. unfold getr_same in E, Eq.
      rewrite !E, !Eq in H. exact H. }
    { exact HQ. }
    { cbv beta. exists kbs, (req_write idx a).
      unfold frame_apart_gnl, apart_frame, apart_gnl, apart, buf_arg, NL_SENT_LEN. rR. ul.
      refine (conj NL2 (conj _ (conj WF (conj OPEN (conj ERRW (conj _ (conj _ (conj REQ (conj RL (conj _ (conj _
               (conj _ (conj _ (conj _ (conj _ (conj _ (conj OPC (conj CLC (conj _ (conj _ (conj _ _)))))))))))))))))))));
        first [ lia | (intros; lia) | (intros H; exfalso; lia) ]. }
    { assumption. }
    { ul. exact ST. }
    { ul. lia. }
    { ul. lia. }
    intros ra3 t03 t13 t23 a03 a13 a23 a33 a43 a53 a63 a73 t33 t43 t53 t63 m3 MUc WMc MIc STc POc.
    cbv beta in MUc. rR_in MUc. ul_in MUc. cbn [Z.eqb] in MUc. ul_in STc.
    cbv beta in POc. rR_in POc. ul_in POc.
    specialize (POc kbs (req_write idx a) NL2 REQ RL). cbv zeta in POc.
    destruct POc as (RC & (kbs' & NL' & WF' & CH' & EE' & NI' & SOCK' & SEND' & NX' & SENT' & NS' & OP' & MS'
                           & OC' & OSE & OSZ) & _).
    subst a03.
    clear MF.
    lazymatch type of MUc with munch _ ?mc _ => transport_after_call rsegs mc m3 MUc WMc end.
    clear MUc WMc. try clear ST. rename STc into ST.
    fix_ret.
    zstep.                                      (* j 0x16364 *)
    zstep. zstep. zstep. zstep. zstep.          (* the epilogue *)
    pose proof (stk_release_at _ _ _ _ (bv_unsigned sp + -312) ST F0 ltac:(lia)
                  ltac:(cbn [cells_size csize]; lia)) as S1.
    pose proof (stk_release_at _ _ _ _ (bv_unsigned sp + -288) S1 G1 ltac:(lia)
                  ltac:(cbn [cells_size csize]; lia)) as S2.
    pose proof (stk_release_at _ _ _ _ (bv_unsigned sp + -288 + Z.of_nat (length a)) S2 G2 ltac:(lia)
                  ltac:(cbn [cells_size csize]; lia)) as S3.
    pose proof (stk_release_at _ _ _ _ (bv_unsigned sp + -32) S3 G3 ltac:(lia)
                  ltac:(cbn [cells_size csize]; lia)) as S4.
    pose proof (stk_release_at _ _ _ _ (bv_unsigned sp) S4 F2 ltac:(lia)
                  ltac:(cbn [cells_size csize]; lia)) as S5.
    zstep.                                      (* ret *)
    apply evt_done. unfold Q. do 2 eexists. split; [reflexivity|].
    split; [apply regs_preserved_mkR|].
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact S5|].
    refine (post_of _ R0 _ m _ kbs tab (Some (b :: s')) (Some a) kbs'
              (Wres (talk_rc_lib (nk_kstate kbs))
                    (if talk_owes (nk_kstate kbs) then owe (nk_sent kbs) (req_write idx a) else nk_sent kbs)
                    (talk_after (nk_kstate kbs)))
              NL TAB (conj NNZ NC) (conj ANZ (conj ACB ACN)) MU _ _ _ _ NL' WF' CH' EE' NI' NX' _ SEND' SENT' _
              OP' MS' OC' _ _).
    + intros aa nn Ha Hn. cbn [disjoint_from]. repeat split; lia.
    + intros i n2 ix p E U. destruct (TABA i n2 ix p E U) as (T1 & T2 & T3).
      cbn [disjoint_from]. repeat split; lia.
    + unfold write_lib, write_core. cbn [length Nat.eqb].
      replace (ALIAS_MAX <=? Z.of_nat (length a)) with false by (symmetry; apply Z.leb_gt; unfold ALIAS_MAX; lia).
      rewrite <- EIDX. cbv zeta.
      replace (idx =? 0) with false by (symmetry; apply Z.eqb_neq; exact INZ). reflexivity.
    + reflexivity.
    + rewrite SOCK'. symmetry. exact (talk_after_sock _).
    + rewrite NS', SENT'. reflexivity.
    + destruct (Z.eq_dec (nk_socket_errno kbs) 0) as [Z0|Z0];
        [specialize (OSZ Z0) | specialize (OSE Z0)]; lia.
    + intros [H|[H|[H|[H|H]]]]; try discriminate.
      * specialize (H a eq_refl). unfold ALIAS_MAX in H. lia.
      * specialize (H _ eq_refl). rewrite <- EIDX in H. exact (False_ind _ (INZ H)).
Qed.

Print Assumptions reac_link_alias_write_holds.
