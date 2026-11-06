(* Arm c2 (op_mark) of the slot LLVMFuzzerTestOneInput, plain image, piece HEAD (lh_ms with op 2 ->
   c2_13d70): the lemmas its two segments share. No machine step is taken here.
   1. the Z arithmetic of the dispatch (b mod 6) and of name_of (s mod 6, the g_names slot);
   2. byte lists in memory: uniqueness of what one address holds (le8 words, C strings), suffixes;
   3. the frame cells: lh_cells split into the 64 bytes below the cursor, the cursor, the buffers;
   4. 32-bit fields of a byte block (u8arr), read and written in place;
   5. what a footprint W that misses a region keeps: the image's tables and strings, g_names, the
      interface table of g_nl, the marks block, the payload, the saved registers (c2h_keep);
   6. the internal cut of the piece at 0x13d48 (the call of kernel), c2h_13d48. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Spec Require StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC2Defs.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Z arithmetic
   ========================================================================== *)

(* an equation between Z terms built by the step tactics from bytes: wraps, shifts, swrap 32, & 255 *)
Ltac c2h_zsolve :=
  rewrite ?unsigned_lit_wrap;
  rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia;
  try (unfold bv_swrap; change (bv_half_modulus 32) with 2147483648);
  try (unfold bv_wrap; change (bv_modulus 32) with 4294967296);
  try (change 255 with (Z.ones 8); rewrite Z.land_ones by lia);
  Z.div_mod_to_equations; lia.

Lemma c2h_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. exact R. Qed.

Lemma c2h_zxb : forall b : byte, bv_unsigned (zxb b) = bz b.
Proof. intros b. unfold zxb, bz. apply unsigned_lit. pose proof (c2h_byte_range b). lia. Qed.

(* 0x13a2c - 0x13a44: a3 = b - 6 * ((b * 0xab) >> 10), & 0xff *)
Lemma c2h_disp_mod6 : forall b : byte, bz b mod 6 = 2 ->
  Z.land
    (bv_unsigned
       (Z_to_bv 64
          (bv_unsigned (zxb b) +
           bv_swrap 32
             (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (bv_unsigned (zxb b) * 171))) 10))) 1)) -
              bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (bv_unsigned (zxb b) * 171))) 10))) 3))))))
    255 = 2.
Proof.
  intros b H6. rewrite c2h_zxb. pose proof (c2h_byte_range b) as Rb. unfold bz in *.
  remember (bv_unsigned b) as x eqn:Ex. clear Ex.
  rewrite !unsigned_lit_wrap.
  rewrite !Z.shiftr_div_pow2, !Z.shiftl_mul_pow2 by lia.
  unfold bv_swrap. change (bv_half_modulus 32) with 2147483648. unfold bv_wrap. change (bv_modulus 32) with 4294967296.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  Z.div_mod_to_equations. lia.
Qed.

(* name_of's three arms (LDefs.sel_ptr) *)
Lemma c2h_sel_ptr_lo : forall s, 0 <= s < 64 -> sel_ptr s = A_G_NAMES + 8 * s.
Proof.
  intros s Hs. unfold sel_ptr. rewrite (proj2 (Z.eqb_neq s 255)) by lia.
  rewrite (proj2 (Z.ltb_lt s 64)) by lia. reflexivity.
Qed.

Lemma c2h_sel_ptr_hi : forall s, 64 <= s -> s <> 255 -> sel_ptr s = nth (Z.to_nat (s mod 6)) odd_ptrs 0.
Proof.
  intros s H1 H2. unfold sel_ptr. rewrite (proj2 (Z.eqb_neq s 255)) by lia.
  rewrite (proj2 (Z.ltb_ge s 64)) by lia. reflexivity.
Qed.

Lemma c2h_sel_name_hi : forall s, 64 <= s -> s <> 255 -> sel_name s = Some (nth (Z.to_nat (s mod 6)) odd_strs []).
Proof.
  intros s H1 H2. unfold sel_name. rewrite (proj2 (Z.eqb_neq s 255)) by lia.
  rewrite (proj2 (Z.ltb_ge s 64)) by lia. reflexivity.
Qed.

Lemma c2h_sel_name_lo : forall s, 0 <= s < 64 -> sel_name s = Some (gname s).
Proof.
  intros s Hs. unfold sel_name. rewrite (proj2 (Z.eqb_neq s 255)) by lia.
  rewrite (proj2 (Z.ltb_lt s 64)) by lia. reflexivity.
Qed.

(* ==========================================================================
   2. Byte lists in memory
   ========================================================================== *)

Lemma c2h_le8_inj : forall v w : word, le8 v = le8 w -> v = w.
Proof. intros v w H. rewrite <- (load_u64 v), <- (load_u64 w), H. reflexivity. Qed.

Lemma c2h_bytes_at_unique : forall m a l1 l2,
  bytes_at rsegs m a l1 -> bytes_at rsegs m a l2 -> length l1 = length l2 -> l1 = l2.
Proof.
  intros m a l1 l2 (_ & _ & H1) (_ & _ & H2) HL. apply nth_error_ext. intros n.
  destruct (Nat.lt_ge_cases n (length l1)) as [Hn|Hn].
  - rewrite <- (H1 n Hn), <- (H2 n ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None l1 n) Hn), (proj2 (nth_error_None l2 n) ltac:(lia)). reflexivity.
Qed.

Lemma c2h_u64_unique : forall m a p q, u64_at m a p -> u64_at m a q -> p mod 2 ^ 64 = q mod 2 ^ 64.
Proof.
  intros m a p q Hp Hq. unfold u64_at in *.
  assert (E : wz p = wz q).
  { apply c2h_le8_inj. eapply c2h_bytes_at_unique; [exact Hp | exact Hq |]. rewrite !length_le8. reflexivity. }
  apply (f_equal bv_unsigned) in E. unfold wz in E. rewrite !unsigned_lit_wrap in E. exact E.
Qed.

Lemma c2h_cstr_unique : forall m a s t, cstr_at m a s -> cstr_at m a t -> s = t.
Proof.
  intros m a s t [(_ & _ & Hs) Ns] [(_ & _ & Ht) Nt].
  rewrite length_app in Hs, Ht. cbn [length] in Hs, Ht.
  assert (EQ : forall i, (i <= length s)%nat -> (i <= length t)%nat ->
                 nth_error (s ++ [zb 0]) i = nth_error (t ++ [zb 0]) i).
  { intros i Hi1 Hi2. rewrite <- (Hs i ltac:(lia)), <- (Ht i ltac:(lia)). reflexivity. }
  assert (L : length s = length t).
  { destruct (Nat.lt_trichotomy (length s) (length t)) as [H|[H|H]]; [exfalso | exact H | exfalso].
    - specialize (EQ (length s) ltac:(lia) ltac:(lia)).
      rewrite (nth_error_app2 s), Nat.sub_diag in EQ by lia. cbn in EQ.
      rewrite (nth_error_app1 t) in EQ by lia. apply Nt. symmetry in EQ. eapply nth_error_In. exact EQ.
    - specialize (EQ (length t) ltac:(lia) ltac:(lia)).
      rewrite (nth_error_app2 t), Nat.sub_diag in EQ by lia. cbn in EQ.
      rewrite (nth_error_app1 s) in EQ by lia. apply Ns. eapply nth_error_In. exact EQ. }
  apply (app_inv_tail [zb 0]). apply nth_error_ext. intros i.
  destruct (Nat.le_gt_cases i (length s)) as [Hi|Hi].
  - apply EQ; lia.
  - rewrite (proj2 (nth_error_None (s ++ [zb 0]) i)) by (rewrite length_app; cbn [length]; lia).
    rewrite (proj2 (nth_error_None (t ++ [zb 0]) i)) by (rewrite length_app; cbn [length]; lia).
    reflexivity.
Qed.

Lemma c2h_bytes_at_skipn : forall m a l k, bytes_at rsegs m a l -> (k <= length l)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (skipn k l).
Proof.
  intros m a l k H Hk. rewrite <- (firstn_skipn k l) in H.
  apply (proj1 (bytes_at_app rsegs _ _ _ _)) in H. destruct H as [_ H].
  rewrite length_firstn in H. replace (Nat.min k (length l)) with k in H by lia. exact H.
Qed.

Lemma c2h_bytes_at_prefix : forall m a l1 l2, bytes_at rsegs m a (l1 ++ l2) -> bytes_at rsegs m a l1.
Proof. intros m a l1 l2 H. apply (proj1 (bytes_at_app rsegs _ _ _ _)) in H. exact (proj1 H). Qed.

Lemma c2h_bytes_at_suffix : forall m a l1 l2, bytes_at rsegs m a (l1 ++ l2) ->
  bytes_at rsegs m (a + Z.of_nat (length l1)) l2.
Proof. intros m a l1 l2 H. apply (proj1 (bytes_at_app rsegs _ _ _ _)) in H. exact (proj2 H). Qed.

Lemma c2h_firstn1_skipn : forall {A} (l : list A) k x, nth_error l k = Some x -> firstn 1 (skipn k l) = [x].
Proof.
  intros A l. induction l as [|y l IH]; intros [|k] x H; cbn in *; try discriminate.
  - inversion H. reflexivity.
  - apply IH. exact H.
Qed.

Lemma c2h_read_byte : forall m a l k (b : byte), bytes_at rsegs m a l -> nth_error l k = Some b ->
  ov_read_bytes rsegs m (Z_to_bv 64 (a + Z.of_nat k)) 1 = Some [b].
Proof.
  intros m a l k b H E.
  assert (Hk : (k < length l)%nat) by (apply nth_error_Some; congruence).
  pose proof (bytes_at_ov_read rsegs m a l k 1 H ltac:(lia)) as R. unfold wa in R. rewrite R.
  rewrite (c2h_firstn1_skipn l k b E). reflexivity.
Qed.

(* ==========================================================================
   3. The frame cells
   ========================================================================== *)

Lemma c2h_wr_at_app : forall m A n1 n2, 0 <= n1 -> 0 <= n2 ->
  wr_at rsegs m A (n1 + n2) <-> wr_at rsegs m A n1 /\ wr_at rsegs m (A + n1) n2.
Proof.
  intros m A n1 n2 H1 H2. split.
  - intros (Ha & Hn & H). split; (split; [lia|]; split; [lia|]); intros i Hi.
    + apply H. lia.
    + replace (A + n1 + i) with (A + (n1 + i)) by lia. apply H. lia.
  - intros [(Ha & Hn & H) (Hb & Hm & H')]. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_dec i n1); [apply H; lia|].
    replace (A + i) with (A + n1 + (i - n1)) by lia. apply H'. lia.
Qed.

Lemma c2h_rw_cells_app : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) <->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  pose proof (cells_wf_app cs1 cs2) as WA.
  split.
  - intros [[W12 HB] HW]. apply WA in W12. destruct W12 as [W1 W2].
    apply (proj1 (bytes_at_app rsegs _ _ _ _)) in HB. destruct HB as [B1 B2].
    rewrite cells_bytes_length in B2 by exact W1.
    apply (proj1 (c2h_wr_at_app m A _ _ (Nat2Z.is_nonneg (cells_size cs1)) (Nat2Z.is_nonneg (cells_size cs2)))) in HW.
    destruct HW as [H1 H2].
    exact (conj (conj (conj W1 B1) H1) (conj (conj W2 B2) H2)).
  - intros [[[W1 B1] H1] [[W2 B2] H2]].
    split; [split; [apply WA; split; assumption|]|].
    + apply (proj2 (bytes_at_app rsegs _ _ _ _)). split; [exact B1|].
      rewrite cells_bytes_length by exact W1. exact B2.
    + apply (proj2 (c2h_wr_at_app m A _ _ (Nat2Z.is_nonneg (cells_size cs1)) (Nat2Z.is_nonneg (cells_size cs2)))).
      split; assumption.
Qed.

(* the 64 bytes of the frame below the cursor cells *)
Definition c2h_fhead (md mk : Z) (j0 : list byte) : list cell :=
  [CB 8 j0; C8 (wz A_ODD); C8 (wz (md + MD_MARK)); C8 (wz A_EMPTY); C8 (wz mk); C8 (wz A_G_NAMES);
   C8 (wz A_JT); C8 (wz GNL42)].

Lemma c2h_frame_split : forall m A md mk P N j0 j1 j2,
  rw_cells rsegs m A (lh_cells md mk P N j0 j1 j2) ->
  rw_cells rsegs m A (c2h_fhead md mk j0) /\ rw_cells rsegs m (A + 64) [C8 (wz P); C8 (wz N)] /\
  rw_cells rsegs m (A + 80) [CB 40 j1; CB 256 j2].
Proof.
  intros m A md mk P N j0 j1 j2 H.
  change (lh_cells md mk P N j0 j1 j2)
    with (c2h_fhead md mk j0 ++ [C8 (wz P); C8 (wz N)] ++ [CB 40 j1; CB 256 j2]) in H.
  apply (proj1 (c2h_rw_cells_app _ _ _ _)) in H. destruct H as [H1 H2].
  apply (proj1 (c2h_rw_cells_app _ _ _ _)) in H2. destruct H2 as [H2 H3].
  change (Z.of_nat (cells_size (c2h_fhead md mk j0))) with 64 in H2, H3.
  change (Z.of_nat (cells_size [C8 (wz P); C8 (wz N)])) with 16 in H3.
  replace (A + 64 + 16) with (A + 80) in H3 by lia.
  split; [exact H1 | split; [exact H2 | exact H3]].
Qed.

Lemma c2h_frame_join : forall m A md mk P N j0 j1 j2,
  rw_cells rsegs m A (c2h_fhead md mk j0) -> rw_cells rsegs m (A + 64) [C8 (wz P); C8 (wz N)] ->
  rw_cells rsegs m (A + 80) [CB 40 j1; CB 256 j2] ->
  rw_cells rsegs m A (lh_cells md mk P N j0 j1 j2).
Proof.
  intros m A md mk P N j0 j1 j2 H1 H2 H3.
  change (lh_cells md mk P N j0 j1 j2)
    with (c2h_fhead md mk j0 ++ [C8 (wz P); C8 (wz N)] ++ [CB 40 j1; CB 256 j2]).
  apply (proj2 (c2h_rw_cells_app _ _ _ _)). split; [exact H1|].
  apply (proj2 (c2h_rw_cells_app _ _ _ _)).
  change (Z.of_nat (cells_size (c2h_fhead md mk j0))) with 64.
  change (Z.of_nat (cells_size [C8 (wz P); C8 (wz N)])) with 16.
  replace (A + 64 + 16) with (A + 80) by lia.
  split; [exact H2 | exact H3].
Qed.

Lemma c2h_cells2_bytes : forall m A (v w : word), rw_cells rsegs m A [C8 v; C8 w] ->
  bytes_at rsegs m A (le8 v) /\ bytes_at rsegs m (A + 8) (le8 w).
Proof.
  intros m A v w [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  apply (proj1 (bytes_at_app rsegs _ _ _ _)) in HB. rewrite length_le8 in HB. exact HB.
Qed.

(* ==========================================================================
   4. 32-bit fields of a byte block
   ========================================================================== *)

Lemma c2h_le4_slice : forall bs off, 0 <= off -> off + 4 <= Z.of_nat (length bs) ->
  le4 (wz (fld_u32 bs off)) = firstn 4 (skipn (Z.to_nat off) bs).
Proof.
  intros bs off H0 H4. unfold fld_u32, rdn, slice, le4, wz.
  change (Z.to_nat 4) with 4%nat.
  assert (Hl : length (firstn 4 (skipn (Z.to_nat off) bs)) = 4%nat)
    by (rewrite length_firstn, length_skipn; lia).
  rewrite unsigned_lit_wrap.
  rewrite (Z_to_le_bytes_mod 4 _ 64) by lia.
  rewrite <- Hl at 1. apply StrFun.Z_to_le_bytes_to_Z.
Qed.

Lemma c2h_u8arr_rd32 : forall m A bs off a, u8arr rsegs m A bs -> 0 <= off -> off + 4 <= Z.of_nat (length bs) ->
  a = A + off -> ov_read_bytes rsegs m (Z_to_bv 64 a) 4 = Some (le4 (wz (fld_u32 bs off))).
Proof.
  intros m A bs off a [HB _] H0 H4 ->. rewrite c2h_le4_slice by lia.
  exact (bytes_at_read rsegs m A bs off 4 HB H0 ltac:(lia)).
Qed.

Lemma c2h_u8arr_store_ok : forall m A bs off a (n : nat), u8arr rsegs m A bs -> 0 <= off ->
  off + Z.of_nat n <= Z.of_nat (length bs) -> a = A + off -> store_ok rsegs m (Z_to_bv 64 a) n = true.
Proof. intros m A bs off a n [_ HW] H0 H4 ->. exact (wr_at_store_ok rsegs m A _ off n HW H0 H4). Qed.

Lemma c2h_u8arr_write : forall m A bs off a xs, u8arr rsegs m A bs -> 0 <= off ->
  off + Z.of_nat (length xs) <= Z.of_nat (length bs) -> a = A + off ->
  u8arr rsegs (write_to_mem m (Z_to_bv 64 a) xs) A (upd_bytes bs (Z.to_nat off) xs).
Proof.
  intros m A bs off a xs [HB HW] H0 H4 ->. split.
  - exact (bytes_at_write_inside rsegs m A bs off xs HB H0 ltac:(lia)).
  - rewrite upd_bytes_length by lia. exact (wr_at_write rsegs m A _ _ xs HW).
Qed.

Lemma c2h_slice_upd_same : forall bs k xs, (k + length xs <= length bs)%nat ->
  slice (upd_bytes bs k xs) (Z.of_nat k) (Z.of_nat (length xs)) = xs.
Proof.
  intros bs k xs H. unfold slice, upd_bytes. rewrite !Nat2Z.id.
  rewrite skipn_app, length_firstn, (Nat.min_l k (length bs)) by lia.
  rewrite skipn_all2 by (rewrite length_firstn; lia). rewrite Nat.sub_diag. cbn [app skipn].
  change (skipn 0 (xs ++ skipn (k + length xs) bs)) with (xs ++ skipn (k + length xs) bs).
  rewrite firstn_app, Nat.sub_diag, firstn_all. cbn [firstn]. apply app_nil_r.
Qed.

Lemma c2h_slice_upd_other : forall bs k xs off n, (k + length xs <= length bs)%nat -> 0 <= off -> 0 <= n ->
  (off + n <= Z.of_nat k \/ Z.of_nat k + Z.of_nat (length xs) <= off) ->
  slice (upd_bytes bs k xs) off n = slice bs off n.
Proof.
  intros bs k xs off n H H0 H1 [Hb|Ha]; unfold slice, upd_bytes.
  - rewrite skipn_app, length_firstn, (Nat.min_l k (length bs)) by lia.
    rewrite firstn_app, length_skipn, length_firstn, (Nat.min_l k (length bs)) by lia.
    replace (Z.to_nat n - (k - Z.to_nat off))%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r.
    rewrite skipn_firstn_comm, firstn_firstn. f_equal. lia.
  - rewrite skipn_app, length_firstn, (Nat.min_l k (length bs)) by lia.
    rewrite skipn_all2 by (rewrite length_firstn; lia). cbn [app].
    rewrite skipn_app. rewrite skipn_all2 by lia. cbn [app].
    rewrite skipn_skipn. f_equal. f_equal. lia.
Qed.

Lemma c2h_fld_u32_upd_same : forall bs k v, (k + 4 <= length bs)%nat ->
  fld_u32 (upd_bytes bs k (le4 v)) (Z.of_nat k) = bv_unsigned v mod 2 ^ 32.
Proof.
  intros bs k v H. unfold fld_u32, link_spec.rdn.
  pose proof (c2h_slice_upd_same bs k (le4 v) ltac:(rewrite length_le4; lia)) as HS.
  rewrite length_le4 in HS.
  transitivity (bytes_le_to_Z (le4 v)); [f_equal; exact HS | apply bytes_le_to_Z_le4].
Qed.

Lemma c2h_rdn_upd_other : forall bs k xs off n, (k + length xs <= length bs)%nat -> 0 <= off -> 0 <= n ->
  (off + n <= Z.of_nat k \/ Z.of_nat k + Z.of_nat (length xs) <= off) ->
  link_spec.rdn (upd_bytes bs k xs) off n = link_spec.rdn bs off n.
Proof. intros. unfold link_spec.rdn. rewrite c2h_slice_upd_other by assumption. reflexivity. Qed.

Lemma c2h_upd_length : forall bs k xs, (k + length xs <= length bs)%nat -> length (upd_bytes bs k xs) = length bs.
Proof. intros. apply upd_bytes_length. exact H. Qed.

(* ==========================================================================
   5. What a footprint keeps
   ========================================================================== *)

Lemma c2h_disjoint_sub : forall W a n b k, disjoint_from W a n -> a <= b -> b + k <= a + n -> disjoint_from W b k.
Proof.
  induction W as [|[lo hi] W IH]; intros a n b k H H1 H2; cbn in *; [exact I|].
  destruct H as [H3 H4]. split; [lia|]. exact (IH a n b k H4 H1 H2).
Qed.

Lemma c2h_cstr_keep : forall W m m' a s, cstr_at m a s -> munch W m m' ->
  disjoint_from W a (Z.of_nat (length s) + 1) -> cstr_at m' a s.
Proof.
  intros W m m' a s [B N] MU D. split; [|exact N]. eapply bytes_at_transport; [exact B | exact MU |].
  rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. exact D.
Qed.

Lemma c2h_u64_keep : forall W m m' a v, u64_at m a v -> munch W m m' -> disjoint_from W a 8 -> u64_at m' a v.
Proof. intros W m m' a v H MU D. unfold u64_at in *. eapply bytes_at_transport; [exact H | exact MU |]. rewrite length_le8. exact D. Qed.

Lemma c2h_u32_keep : forall W m m' a v, u32_at m a v -> munch W m m' -> disjoint_from W a 4 -> u32_at m' a v.
Proof. intros W m m' a v H MU D. unfold u32_at in *. eapply bytes_at_transport; [exact H | exact MU |]. rewrite length_le4. exact D. Qed.

Lemma c2h_forallb_seq : forall (f : nat -> bool) n i, forallb f (seq 0 n) = true -> (i < n)%nat -> f i = true.
Proof. intros f n i H Hi. rewrite forallb_forall in H. apply H. apply in_seq. lia. Qed.

(* the image's low region [0x10000, g_nl): .rodata, .data.rel.ro (odd, texts), the GOT *)
Definition c2h_img_lo : Z := 0x10000.

Definition c2h_odd_ok (i : nat) : bool :=
  (0x10000 <=? nth i odd_ptrs 0) && (nth i odd_ptrs 0 + Z.of_nat (length (nth i odd_strs [])) + 1 <=? A_RO_END).
Lemma c2h_odd_all : forallb c2h_odd_ok (seq 0 6) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma c2h_odd_where : forall i, (i < 6)%nat ->
  0x10000 <= nth i odd_ptrs 0 /\ nth i odd_ptrs 0 + Z.of_nat (length (nth i odd_strs [])) + 1 <= A_RO_END.
Proof.
  intros i Hi. pose proof (c2h_forallb_seq _ _ _ c2h_odd_all Hi) as H. unfold c2h_odd_ok in H.
  apply andb_true_iff in H. destruct H as [H1 H2]. apply Z.leb_le in H1, H2. split; assumption.
Qed.

Lemma c2h_gnames_keep : forall W m m', gnames_at m -> munch W m m' -> disjoint_from W A_G_NAMES 512 -> gnames_at m'.
Proof.
  intros W m m' H MU D k Hk. destruct (H k Hk) as (rest & B & L). exists rest. split; [|exact L].
  eapply bytes_at_transport; [exact B | exact MU |]. rewrite L.
  eapply c2h_disjoint_sub; [exact D | lia | lia].
Qed.

Lemma c2h_odd_keep : forall W m m', odd_at m -> munch W m m' ->
  disjoint_from W c2h_img_lo (A_G_NL - c2h_img_lo) -> odd_at m'.
Proof.
  intros W m m' H MU D i Hi. destruct (H i Hi) as [U C]. destruct (c2h_odd_where i Hi) as [R1 R2].
  split.
  - eapply c2h_u64_keep; [exact U | exact MU |].
    eapply c2h_disjoint_sub; [exact D | unfold c2h_img_lo, A_ODD; lia | unfold c2h_img_lo, A_ODD, A_G_NL; lia].
  - eapply c2h_cstr_keep; [exact C | exact MU |].
    eapply c2h_disjoint_sub; [exact D | unfold c2h_img_lo; lia | unfold c2h_img_lo, A_G_NL, A_RO_END in *; lia].
Qed.

Lemma c2h_policy_keep : forall W m m', policy_ro m -> munch W m m' ->
  disjoint_from W c2h_img_lo (A_G_NL - c2h_img_lo) -> policy_ro m'.
Proof.
  intros W m m' (H1 & H2 & H3 & H4) MU D.
  split; [|split; [|split]]; (eapply c2h_cstr_keep; [eassumption | exact MU |]);
    (eapply c2h_disjoint_sub; [exact D | |]);
    unfold c2h_img_lo, A_G_NL, A_PREFIX, A_SERVED, A_VLAN, A_EMPTY, S_PREFIX, S_SERVED, S_VLAN;
    cbn [length map]; lia.
Qed.

Lemma c2h_texts_keep : forall W m m', texts_at m -> munch W m m' ->
  disjoint_from W c2h_img_lo (A_G_NL - c2h_img_lo) -> texts_at m'.
Proof.
  intros W m m' H MU D i Hi. eapply c2h_u64_keep; [exact (H i Hi) | exact MU |].
  eapply c2h_disjoint_sub; [exact D | unfold c2h_img_lo, A_TEXTS; lia | unfold c2h_img_lo, A_TEXTS, A_G_NL; lia].
Qed.

Definition c2h_if_lo : Z := A_G_NL + NK_IF_NAME.
Definition c2h_if_n : Z := NK_N_IF - NK_IF_NAME.

Lemma c2h_ifptrs_keep : forall W m m', ifptrs_at m -> munch W m m' -> disjoint_from W c2h_if_lo c2h_if_n -> ifptrs_at m'.
Proof.
  intros W m m' H MU D i Hi. eapply c2h_u64_keep; [exact (H i Hi) | exact MU |].
  eapply c2h_disjoint_sub; [exact D | unfold c2h_if_lo; lia | unfold c2h_if_lo, c2h_if_n, NK_IF_NAME, NK_N_IF; lia].
Qed.

Lemma c2h_guard_keep : forall W m m', guard_m m -> munch W m m' ->
  disjoint_from W c2h_img_lo (A_G_NL - c2h_img_lo) -> disjoint_from W A_GUARD_S 8 -> guard_m m'.
Proof.
  intros W m m' [H1 (c & H2)] MU D Dg. split.
  - eapply bytes_at_transport; [exact H1 | exact MU |]. rewrite length_le8.
    eapply c2h_disjoint_sub; [exact D | unfold c2h_img_lo, A_GOT_GUARD_S; lia | unfold c2h_img_lo, A_GOT_GUARD_S, A_G_NL; lia].
  - exists c. eapply bytes_at_transport; [exact H2 | exact MU |]. rewrite length_le8. exact Dg.
Qed.

(* where interfaces() points g_nl.if_name[i], with the name link_tab gives it *)
Definition c2h_lw_ok (i : nat) : bool :=
  match nth_error link_tab i with
  | Some (nm, _) =>
      let a := nth i link_ptrs 0 in
      let e := a + Z.of_nat (length nm) + 1 in
      ((0x10000 <=? a) && (e <=? A_RO_END)) || ((A_G_NAMES <=? a) && (e <=? A_G_NAMES + 8 * 63 + 5))
  | None => false
  end.
Lemma c2h_lw_all : forallb c2h_lw_ok (seq 0 64) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma c2h_link_tab_len : length link_tab = 64%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma c2h_link_where : forall i nm ix, nth_error link_tab i = Some (nm, ix) ->
  (i < 64)%nat /\
  ((0x10000 <= nth i link_ptrs 0 /\ nth i link_ptrs 0 + Z.of_nat (length nm) + 1 <= A_RO_END) \/
   (A_G_NAMES <= nth i link_ptrs 0 /\ nth i link_ptrs 0 + Z.of_nat (length nm) + 1 <= A_G_NAMES + 8 * 63 + 5)).
Proof.
  intros i nm ix H.
  assert (Hi : (i < 64)%nat).
  { rewrite <- c2h_link_tab_len. apply nth_error_Some. congruence. }
  split; [exact Hi|].
  pose proof (c2h_forallb_seq _ _ _ c2h_lw_all Hi) as A. unfold c2h_lw_ok in A. rewrite H in A.
  apply orb_true_iff in A. destruct A as [A|A]; apply andb_true_iff in A; destruct A as [A1 A2];
    apply Z.leb_le in A1, A2; [left | right]; split; assumption.
Qed.

Lemma c2h_ifname_at : forall m i p, ifptrs_at m -> (i < 64)%nat ->
  u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> 0 <= p < 2 ^ 64 ->
  forall nm ix, nth_error link_tab i = Some (nm, ix) -> p = nth i link_ptrs 0.
Proof.
  intros m i p HP Hi U Rp nm ix Hnth.
  pose proof (c2h_u64_unique _ _ _ _ U (HP i Hi)) as E.
  destruct (c2h_link_where i nm ix Hnth) as (_ & R).
  rewrite (Z.mod_small p) in E by lia.
  rewrite (Z.mod_small (nth i link_ptrs 0)) in E by (unfold A_RO_END, A_G_NAMES in R; lia).
  exact E.
Qed.

Lemma c2h_iftab_keep : forall W m m' kbs kbs', iftab_at m kbs link_tab -> ifptrs_at m ->
  nk_n_if kbs' = nk_n_if kbs -> munch W m m' ->
  disjoint_from W c2h_img_lo (A_G_NL - c2h_img_lo) -> disjoint_from W A_G_NAMES 512 ->
  disjoint_from W c2h_if_lo c2h_if_n ->
  iftab_at m' kbs' link_tab.
Proof.
  intros W m m' kbs kbs' (Hn & Hl & H) HP E MU D0 D2 D3.
  split; [rewrite E; exact Hn|]. split; [exact Hl|].
  intros i nm ix Hnth. destruct (H i nm ix Hnth) as (Hix & p & U & Np & C & U32).
  destruct (c2h_link_where i nm ix Hnth) as (Hi & R).
  assert (Ep : p = nth i link_ptrs 0).
  { eapply (c2h_ifname_at m i p HP Hi U); [|exact Hnth].
    destruct C as [B _]. pose proof (bytes_at_bound _ _ _ _ B) as BB. rewrite length_app in BB.
    cbn [length] in BB. lia. }
  split; [exact Hix|]. exists p. split; [|split; [exact Np|split]].
  - eapply c2h_u64_keep; [exact U | exact MU |].
    eapply c2h_disjoint_sub; [exact D3 | unfold c2h_if_lo; lia | unfold c2h_if_lo, c2h_if_n, NK_IF_NAME, NK_N_IF; lia].
  - eapply c2h_cstr_keep; [exact C | exact MU |]. rewrite Ep.
    destruct R as [[R1 R2]|[R1 R2]].
    + eapply c2h_disjoint_sub; [exact D0 | unfold c2h_img_lo; lia | unfold c2h_img_lo, A_G_NL, A_RO_END in *; lia].
    + eapply c2h_disjoint_sub; [exact D2 | lia | lia].
  - eapply c2h_u32_keep; [exact U32 | exact MU |].
    eapply c2h_disjoint_sub; [exact D3 | unfold c2h_if_lo, NK_IF_NAME, NK_IF_INDEX; lia
                             | unfold c2h_if_lo, c2h_if_n, NK_IF_NAME, NK_IF_INDEX, NK_N_IF; lia].
Qed.

(* the facts of a cut that no write of this piece touches *)
Definition c2h_keep (E : lenv) (gbs : list byte) (m : word -> option byte) : Prop :=
  bytes_at rsegs m (e_S E - 104) (e_saved E) /\
  gnames_at m /\ odd_at m /\ policy_ro m /\ texts_at m /\ ifptrs_at m /\ guard_m m /\
  wr_at rsegs m A_ERRNO 4 /\ marks_at m (e_mk E) gbs /\ bytes_at rsegs m (e_p0 E) (e_pl E) /\
  (exists sl, bytes_at rsegs m (A_LONG_ALIAS + LONG_ALIAS_SIZE) sl /\ length sl = 3%nat).

Lemma c2h_keep_munch : forall E gbs W m m', length (e_saved E) = 104%nat ->
  c2h_keep E gbs m -> munch W m m' -> wmono rsegs m m' ->
  disjoint_from W (e_S E - 104) 104 ->
  disjoint_from W c2h_img_lo (A_G_NL - c2h_img_lo) ->
  disjoint_from W c2h_if_lo c2h_if_n ->
  disjoint_from W A_G_NAMES 512 ->
  disjoint_from W A_GUARD_S 8 ->
  disjoint_from W (e_mk E) MK_SIZE ->
  disjoint_from W (e_p0 E) (Z.of_nat (length (e_pl E))) ->
  disjoint_from W (A_LONG_ALIAS + LONG_ALIAS_SIZE) 3 ->
  c2h_keep E gbs m'.
Proof.
  intros E gbs W m m' Hsv (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & sl & K11 & K12) MU WM
    Dsv D0 D3 D2 Dg Dmk Dpl Dsl.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
  - eapply bytes_at_transport; [exact K1 | exact MU |]. rewrite Hsv. exact Dsv.
  - exact (c2h_gnames_keep W m m' K2 MU D2).
  - exact (c2h_odd_keep W m m' K3 MU D0).
  - exact (c2h_policy_keep W m m' K4 MU D0).
  - exact (c2h_texts_keep W m m' K5 MU D0).
  - exact (c2h_ifptrs_keep W m m' K6 MU D3).
  - exact (c2h_guard_keep W m m' K7 MU D0 Dg).
  - exact (wr_at_transport rsegs m m' _ _ K8 WM).
  - destruct K9 as [U L]. split; [|exact L]. eapply u8arr_transport; [exact U | exact MU | exact WM |]. rewrite L. exact Dmk.
  - eapply bytes_at_transport; [exact K10 | exact MU | exact Dpl].
  - exists sl. split; [|exact K12]. eapply bytes_at_transport; [exact K11 | exact MU |]. rewrite K12. exact Dsl.
Qed.

Lemma c2h_la_keep : forall W m m', la_ok m -> munch W m m' -> wmono rsegs m m' ->
  disjoint_from W A_LONG_ALIAS (LONG_ALIAS_SIZE + 3) -> la_ok m'.
Proof.
  intros W m m' (la & sl & H1 & H2 & H3) MU WM D. exists la, sl. split; [|split; [|exact H3]].
  - eapply rw_cells_transport; [exact H1 | exact MU | exact WM |].
    eapply c2h_disjoint_sub; [exact D | lia | cbn [cells_size csize]; unfold LONG_ALIAS_SIZE; lia].
  - eapply bytes_at_transport; [exact H2 | exact MU |]. rewrite H3.
    eapply c2h_disjoint_sub; [exact D | unfold LONG_ALIAS_SIZE; lia | unfold LONG_ALIAS_SIZE; lia].
Qed.

Lemma c2h_blk_keep : forall W m m' A bs, u8arr rsegs m A bs -> munch W m m' -> wmono rsegs m m' ->
  disjoint_from W A (Z.of_nat (length bs)) -> u8arr rsegs m' A bs.
Proof. intros. eapply u8arr_transport; eassumption. Qed.

(* ==========================================================================
   6. The internal cut at 0x13d48: `addi a0, sp, 0x40; jal kernel`, name_of done (s2 = its answer)
   ========================================================================== *)

Definition c2h_cur (E : lenv) (P N : Z) : Prop :=
  exists k, 0 <= k <= Z.of_nat (length (e_pl E)) /\ P = e_p0 E + k /\ N = Z.of_nat (length (e_pl E)) - k.

Definition c2h_kfacts (i : Z) (kbs : list byte) : Prop :=
  nlk_wf kbs /\ nk_open kbs = 0 /\ nk_misuse kbs = 0 /\ nk_opened kbs = nk_closed kbs /\ nk_opened kbs <= 64 * i.

Definition c2h_13d48 (E : lenv) (i : Z) (gp : word) (s : Z) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (P N : Z) (j0 j1 j2 kbs mbs gbs : list byte),
    ms = MS (mkR ra (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (wz (sel_ptr s)) s3 s4 (wz 46) (wz A_JT) (wz (e_mk E)) (wz 0xab) (wz 4)
                 (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6)
            F (wz 0x13d48) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\ 0 <= s <= 255 /\
    c2_frame E P N j0 j1 j2 m /\ c2h_keep E gbs m /\ c2h_cur E P N /\
    nlk_at m kbs /\ c2h_kfacts i kbs /\ iftab_at m kbs link_tab /\ la_ok m /\
    model_at m (e_md E) mbs /\ model_wf mbs /\ marks_wf gbs /\ marks_are gbs mbs /\
    mem_inv rsegs m /\ MemNorm.task_mem rsegs m /\ stk rsegs m (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME).
