(* remember, PLAIN build: memory facts the walk (lib/Prog/remember.v) uses. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_str mk_marks printf_facts_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemNorm.
Local Open Scope Z_scope.

Lemma rw_cells_of_u8arr : forall m a l, u8arr rsegs m a l -> rw_cells rsegs m a [CB (length l) l].
Proof.
  intros m a l [B W]. split; [split; [cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact B]|].
  cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact W.
Qed.

Lemma rw_cells_bytes : forall m A cs, rw_cells rsegs m A cs ->
  bytes_at rsegs m A (cells_bytes cs) /\ wr_at rsegs m A (Z.of_nat (cells_size cs)).
Proof. intros m A cs [[_ B] W]. split; assumption. Qed.

Lemma bv_lts_lit : forall a b, 0 <= a < 2 ^ 63 -> 0 <= b < 2 ^ 63 ->
  bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof.
  intros a b Ha Hb. unfold bv_lts, bv_signed. rewrite !unsigned_lit by lia.
  rewrite !bv_swrap_small by (change (bv_half_modulus 64) with (2 ^ 63); lia). reflexivity.
Qed.

Lemma wr_at_sub : forall m a n off k, wr_at rsegs m a n -> 0 <= off -> 0 <= k -> off + k <= n ->
  wr_at rsegs m (a + off) k.
Proof.
  intros m a n off k (H0 & H1 & H) Ho Hk Hl. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a + off + i) with (a + (off + i)) by lia. apply H. lia.
Qed.

Lemma rw_cells_slice : forall m a l off k, bytes_at rsegs m a l -> wr_at rsegs m a (Z.of_nat (length l)) ->
  0 <= off -> 0 <= k -> off + k <= Z.of_nat (length l) ->
  rw_cells rsegs m (a + off) [CB (Z.to_nat k) (slice l off k)].
Proof.
  intros m a l off k B W Ho Hk Hl. split.
  - split; [cbn [cells_wf cell_wf]; rewrite slice_length by lia; tauto|].
    cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_slice; assumption.
  - cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. apply (wr_at_sub _ _ _ _ _ W); lia.
Qed.

Lemma outside_dec : forall W x, {outside W x} + {~ outside W x}.
Proof.
  induction W as [|[l h] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [Ho|Hn]; [|right; tauto].
  destruct (Z_le_gt_dec l x); [destruct (Z_lt_ge_dec x h)|].
  - right. intros [N _]. apply N. lia.
  - left. split; [lia | exact Ho].
  - left. split; [lia | exact Ho].
Qed.

Lemma task_of_mrd : forall m x b, MemNorm.task_mem rsegs m -> mrd rsegs m x = Some b ->
  find_segment rsegs (bv_unsigned x) 1 <> None \/ bv_unsigned x < TASK_SIZE.
Proof.
  intros m x b TM H. unfold mrd in H. destruct (m x) as [b'|] eqn:E; [exact (TM x b' E)|].
  left. unfold seg_rom, memory_read in H. change (Z.of_N 1) with 1 in H.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [sg|] eqn:Ef; [discriminate | discriminate H].
Qed.

Lemma task_mem_frame : forall m m' W, MemNorm.task_mem rsegs m -> munch W m m' ->
  (forall x : word, ~ outside W (bv_unsigned x) -> exists b, mrd rsegs m x = Some b) ->
  MemNorm.task_mem rsegs m'.
Proof.
  intros m m' W TM MU R a b E. destruct (outside_dec W (bv_unsigned a)) as [Ho|Hn].
  - rewrite (MU a Ho) in E. exact (TM a b E).
  - destruct (R a Hn) as (b' & Hb). exact (task_of_mrd m a b' TM Hb).
Qed.

Lemma stk_rebuild : forall m m' W lo hi, stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> outside W x \/ exists b, mrd rsegs m' (wa x) = Some b) -> stk rsegs m' lo hi.
Proof.
  intros m m' W lo hi (H0 & H1 & H) MU WM C. split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as [Hw [b Hb]]. split; [exact (WM _ Hw)|].
  destruct (C a Ha) as [Ho | Hm]; [|exact Hm].
  exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

Lemma bytes_at_patch : forall m0 m2 A g W k p,
  bytes_at rsegs m0 A g -> munch W m0 m2 -> bytes_at rsegs m2 (A + Z.of_nat k) p ->
  (k + length p <= length g)%nat ->
  (forall x, A <= x < A + Z.of_nat (length g) ->
     ~ (A + Z.of_nat k <= x < A + Z.of_nat k + Z.of_nat (length p)) -> outside W x) ->
  bytes_at rsegs m2 A (upd_bytes g k p).
Proof.
  intros m0 m2 A g W k p (Ha & Hl & Hg) MU (_ & _ & Hp) L O.
  split; [lia|]. rewrite upd_bytes_length by exact L. split; [lia|].
  intros i Hi. rewrite upd_bytes_nth_gen by exact L.
  destruct (Nat.leb_spec k i), (Nat.ltb_spec i (k + length p)); cbn [andb].
  - rewrite <- (Hp (i - k)%nat) by lia. f_equal. f_equal. lia.
  - unfold mrd. rewrite (MU (wa (A + Z.of_nat i))); [exact (Hg i Hi)|].
    rewrite wa_unsigned by lia. apply O; lia.
  - unfold mrd. rewrite (MU (wa (A + Z.of_nat i))); [exact (Hg i Hi)|].
    rewrite wa_unsigned by lia. apply O; lia.
  - lia.
Qed.

Lemma map_Z_to_bv_unsigned : forall l : list byte, map (Z_to_bv 8) (map bv_unsigned l) = l.
Proof.
  induction l as [|b l IH]; cbn; [reflexivity|]. rewrite IH. f_equal.
  apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma pf_bytes_name : forall nm : list byte, pf_bytes (map bv_unsigned nm ++ [0]) = nm ++ [zb 0].
Proof. intros nm. unfold pf_bytes. rewrite map_app, map_Z_to_bv_unsigned. reflexivity. Qed.

Lemma name_bytes_ok : forall nm : list byte, ~ In (zb 0) nm -> Forall (fun c => 0 < c < 256) (map bv_unsigned nm).
Proof.
  intros nm H. apply Forall_forall. intros c Hc. apply in_map_iff in Hc. destruct Hc as (b & <- & Hb).
  pose proof (byte_range b) as R.
  assert (bv_unsigned b <> 0) by (intros E; apply H; rewrite <- (byte_zero b E); exact Hb). lia.
Qed.

Lemma pf_img_free_sub : forall D N off n, pf_img_free D N -> 0 <= off -> off + n <= N -> pf_img_free (D + off) n.
Proof.
  unfold pf_img_free. intros D N off n H Ho Hn i Hi s Hs.
  replace (D + off + i) with (D + (off + i)) by lia. apply H; [lia | exact Hs].
Qed.

(* ---- the block after remember's two stores ---- *)

Lemma slice_le4 : forall (v : word) (l : list byte) off len, 4 <= off -> 0 <= len ->
  slice (le4 v ++ l) off len = slice l (off - 4) len.
Proof.
  intros v l off len Ho Hl. unfold slice.
  replace (Z.to_nat off) with (4 + Z.to_nat (off - 4))%nat by lia.
  rewrite skipn_app, length_le4. replace (4 + Z.to_nat (off - 4) - 4)%nat with (Z.to_nat (off - 4)) by lia.
  rewrite skipn_all2 by (rewrite length_le4; lia). reflexivity.
Qed.

Lemma slice_skipn4 : forall (gbs : list byte) off len, length gbs = 516%nat -> 4 <= off -> 0 <= len -> off + len <= 516 ->
  slice (firstn 512 (skipn 4 gbs)) (off - 4) len = slice gbs off len.
Proof.
  intros gbs off len L Ho Hl Hb. apply nth_error_ext. intros i.
  rewrite !slice_nth by lia. destruct (Nat.ltb_spec i (Z.to_nat len)); [|reflexivity].
  rewrite nth_firstn_gen, nth_skipn_gen.
  destruct (Nat.ltb_spec (Z.to_nat (off - 4) + i) 512).
  - f_equal. lia.
  - exfalso. lia.
Qed.

Lemma rem_marks_after : forall gbs nm n,
  length gbs = 516%nat -> marks_wf gbs -> n = mk_n gbs -> 0 <= n <= 31 -> ~ In (zb 0) nm ->
  (length nm <= 15)%nat -> existsb (fun y => bl_eqb y nm) (mk_names gbs) = false ->
  let gbs' := upd_bytes (le4 (Z_to_bv 64 (n + 1)) ++ firstn 512 (skipn 4 gbs)) (Z.to_nat (4 + 16 * n))
                (nm ++ [zb 0]) in
  length gbs' = 516%nat /\ marks_wf gbs' /\ mk_names gbs' = remember (mk_names gbs) nm
  /\ mk_n gbs' = Z.of_nat (length (remember (mk_names gbs) nm)).
Proof.
  intros gbs nm n L Hwf En Hn Nn Ln Ex gbs'.
  set (g1 := le4 (Z_to_bv 64 (n + 1)) ++ firstn 512 (skipn 4 gbs)).
  assert (L1 : length g1 = 516%nat) by (unfold g1; rewrite length_app, length_le4, length_firstn, length_skipn; lia).
  assert (Lp : (Z.to_nat (4 + 16 * n) + length (nm ++ [zb 0]) <= length g1)%nat)
    by (rewrite length_app; cbn [length]; lia).
  assert (L' : length gbs' = 516%nat) by (unfold gbs'; rewrite upd_bytes_length by exact Lp; exact L1).
  (* n + 1 at [0, 4) *)
  assert (N' : mk_n gbs' = n + 1).
  { unfold mk_n, fld_u32, link_spec.rdn, MK_N.
    replace (slice gbs' 0 4) with (slice g1 0 4).
    2:{ unfold gbs'. symmetry. apply slice_upd_other; [lia | lia | exact Lp | left; lia]. }
    change (slice g1 0 4) with (firstn 4 g1). unfold g1. rewrite firstn_app, length_le4.
    rewrite firstn_all2 by (rewrite length_le4; lia). replace (4 - 4)%nat with 0%nat by lia.
    cbn [firstn]. rewrite app_nil_r. rewrite bytes_le_to_Z_le4. rewrite unsigned_lit by lia.
    apply Z.mod_small. lia. }
  (* the old slots *)
  assert (OLD : forall i, 0 <= i < n -> slice gbs' (4 + 16 * i) 16 = slice gbs (4 + 16 * i) 16).
  { intros i Hi. unfold gbs'. rewrite slice_upd_other; [| lia | lia | exact Lp | left; lia].
    unfold g1. rewrite slice_le4 by lia. apply slice_skipn4; [exact L | lia..]. }
  (* the new slot *)
  assert (NEW : cstr (slice gbs' (4 + 16 * n) 16) = nm /\ (nul_at (slice gbs' (4 + 16 * n) 16) < 16)%nat).
  { pose proof (slice_upd_same g1 (nm ++ [zb 0]) (Z.to_nat (4 + 16 * n)) 16 Lp
                  ltac:(rewrite length_app; cbn [length]; lia) ltac:(lia) ltac:(rewrite L1; lia)) as SU.
    rewrite Z2Nat.id in SU by lia. unfold g1 in SU. unfold gbs'. rewrite SU.
    rewrite <- app_assoc. split.
    - apply cstr_app_nul. exact Nn.
    - rewrite nul_at_app_nul by exact Nn. lia. }
  assert (LN : length (mk_names gbs) = Z.to_nat n) by (rewrite mk_names_length, <- En; reflexivity).
  assert (REM : remember (mk_names gbs) nm = mk_names gbs ++ [nm]).
  { unfold remember. rewrite Ex. rewrite LN. replace (Z.of_nat (Z.to_nat n) <? MARKS_MAX) with true
      by (symmetry; apply Z.ltb_lt; unfold MARKS_MAX; lia).
    rewrite firstn_all2 by lia. reflexivity. }
  assert (NAMES : mk_names gbs' = mk_names gbs ++ [nm]).
  { unfold mk_names. rewrite N'. replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
    rewrite seq_S, map_app. cbn [map plus]. f_equal.
    - rewrite <- En. apply map_ext_in. intros i Hi. apply in_seq in Hi. unfold MK_NAME, MARK_LEN.
      rewrite OLD by lia. reflexivity.
    - unfold MK_NAME, MARK_LEN. rewrite Z2Nat.id by lia. f_equal. exact (proj1 NEW). }
  split; [exact L'|].
  split.
  - split; [rewrite N'; unfold MARKS_MAX; lia|].
    intros i Hi. rewrite N' in Hi. unfold MK_NAME, MARK_LEN.
    destruct (Z.eq_dec i n) as [->|Hne]; [exact (proj2 NEW)|].
    rewrite OLD by lia. destruct Hwf as [_ T]. rewrite <- En in T. apply T. lia.
  - rewrite REM. split; [exact NAMES|]. rewrite N', length_app, LN. cbn [length]. lia.
Qed.
