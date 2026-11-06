(* reac-pw/fuzz_link, PLAIN build: memory facts the model_read and model_write walks share.

   - `clear_of W a n`: no byte of [a, a+n) is in the write set W. It is stated byte by byte with
     `outside`, so an interval of W that is empty (a buffer the code did not write) costs nothing.
   - the views of link_mem.v (cstr_at, model_at, nlk_at, iftab_at, u64_at) keep their bytes across
     a `munch` whose write set they are clear of.
   - splitting and joining `rw_cells` lists, and one byte stored at the head of a buffer.
   - uniqueness of the views (a model block, the fake kernel, a C string argument, the interface
     table), so a Post that quantifies over every view of the entry memory is about the Pre's
     witnesses; and the facts both walks use of index_of and talk. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
Local Open Scope Z_scope.

Definition clear_of (W : list ivl) (a n : Z) : Prop := forall x, a <= x < a + n -> outside W x.

Lemma munch_sym : forall W m m', munch W m m' -> munch W m' m.
Proof. intros W m m' H x Hx. symmetry. apply H, Hx. Qed.

Lemma bytes_at_munch : forall W m m' a bs,
  bytes_at rsegs m a bs -> munch W m m' -> clear_of W a (Z.of_nat (length bs)) ->
  bytes_at rsegs m' a bs.
Proof.
  intros W m m' a bs (Ha & Hl & H) Hm Hd. split; [lia|]. split; [lia|].
  intros i Hi. unfold mrd. rewrite Hm.
  - apply H. exact Hi.
  - rewrite wa_unsigned by lia. apply Hd. lia.
Qed.

Lemma u8arr_munch : forall W m m' a bs,
  u8arr rsegs m a bs -> munch W m m' -> wmono rsegs m m' -> clear_of W a (Z.of_nat (length bs)) ->
  u8arr rsegs m' a bs.
Proof.
  intros W m m' a bs [Hb Hw] Hm Hmo Hd. split.
  - exact (bytes_at_munch W m m' a bs Hb Hm Hd).
  - exact (wr_at_transport rsegs m m' a _ Hw Hmo).
Qed.

Lemma cstr_at_munch : forall W m m' a s,
  cstr_at m a s -> munch W m m' -> clear_of W a (Z.of_nat (length s) + 1) -> cstr_at m' a s.
Proof.
  intros W m m' a s [Hb Hn] Hm Hd. split; [|exact Hn].
  apply (bytes_at_munch W m m' a _ Hb Hm). rewrite length_app. cbn [length].
  intros x Hx. apply Hd. lia.
Qed.

Lemma model_at_munch : forall W m m' p bs,
  model_at m p bs -> munch W m m' -> wmono rsegs m m' -> clear_of W p MD_SIZE -> model_at m' p bs.
Proof.
  intros W m m' p bs [Hu Hl] Hm Hmo Hd. split; [|exact Hl].
  apply (u8arr_munch W m m' p bs Hu Hm Hmo). rewrite Hl. exact Hd.
Qed.

Lemma nlk_at_munch : forall W m m' bs,
  nlk_at m bs -> munch W m m' -> wmono rsegs m m' -> clear_of W A_G_NL NK_SIZE -> nlk_at m' bs.
Proof.
  intros W m m' bs [Hu Hl] Hm Hmo Hd. split; [|exact Hl].
  apply (u8arr_munch W m m' A_G_NL bs Hu Hm Hmo). rewrite Hl. exact Hd.
Qed.

Lemma u64_at_munch : forall W m m' a v,
  u64_at m a v -> munch W m m' -> clear_of W a 8 -> u64_at m' a v.
Proof.
  intros W m m' a v H Hm Hd. unfold u64_at in *.
  apply (bytes_at_munch W m m' a _ H Hm). rewrite length_le8. exact Hd.
Qed.

Lemma u32_at_munch : forall W m m' a v,
  u32_at m a v -> munch W m m' -> clear_of W a 4 -> u32_at m' a v.
Proof.
  intros W m m' a v H Hm Hd. unfold u32_at in *.
  apply (bytes_at_munch W m m' a _ H Hm). rewrite length_le4. exact Hd.
Qed.

Lemma iftab_at_munch : forall W m m' bs tab,
  iftab_at m bs tab -> munch W m m' -> clear_of W A_G_NL NK_SIZE ->
  (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
     u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> clear_of W p (Z.of_nat (length n2) + 1)) ->
  iftab_at m' bs tab.
Proof.
  intros W m m' bs tab (Hn & Hl & H) Hm Hg Hp. split; [exact Hn|]. split; [exact Hl|].
  intros i n2 ix Hi. destruct (H i n2 ix Hi) as (Hix & p & Hu & Hp0 & Hc & Hx).
  assert (Hlen : (i < length tab)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  split; [exact Hix|]. exists p. split; [|split; [exact Hp0|split]].
  - apply (u64_at_munch W m m' _ p Hu Hm). intros x Hx'. apply Hg.
    unfold NK_IF_NAME, NK_SIZE in *. lia.
  - exact (cstr_at_munch W m m' p n2 Hc Hm (Hp i n2 ix p Hi Hu)).
  - apply (u32_at_munch W m m' _ ix Hx Hm). intros x Hx'. apply Hg.
    unfold NK_IF_INDEX, NK_SIZE in *. lia.
Qed.

(* a table slot read in the current memory is the slot the entry memory held *)
Lemma u64_slot_back : forall W m m' i p,
  munch W m m' -> clear_of W A_G_NL NK_SIZE -> 0 <= i < 80 ->
  u64_at m' (A_G_NL + NK_IF_NAME + 8 * i) p -> u64_at m (A_G_NL + NK_IF_NAME + 8 * i) p.
Proof.
  intros W m m' i p Hm Hg Hi H. apply (u64_at_munch W m' m _ p H (munch_sym W m m' Hm)).
  intros x Hx. apply Hg. unfold NK_IF_NAME, NK_SIZE in *. lia.
Qed.

(* ---- rw_cells lists ---- *)

Lemma rw_cells_app : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf Hb] (Ha & Hl & Hw)].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_bytes_length in B2 by exact W1.
  rewrite cells_size_app in Hl, Hw.
  split.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
    apply Hw. lia.
Qed.

Lemma rw_cells_join : forall m A cs1 cs2,
  rw_cells rsegs m A cs1 -> rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2 ->
  rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 [[W1 B1] (Ha1 & Hl1 & H1)] [[W2 B2] (Ha2 & Hl2 & H2)].
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|].
    rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.ltb_spec i (Z.of_nat (cells_size cs1))) as [Hlt|Hge].
    + apply H1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
      apply H2. lia.
Qed.

(* one CB cell cut in two at k *)
Lemma rw_cells_cb_cut : forall m A n j k, (k <= n)%nat ->
  rw_cells rsegs m A [CB n j] ->
  rw_cells rsegs m A [CB k (firstn k j); CB (n - k) (skipn k j)].
Proof.
  intros m A n j k Hk [[Hwf Hb] Hw]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hj _].
  split; [split|].
  - cbn [cells_wf cell_wf]. rewrite length_firstn, length_skipn. split; [lia|]. split; [lia|exact I].
  - cbn [cells_bytes cbytes] in *. rewrite app_nil_r in *. rewrite firstn_skipn. exact Hb.
  - cbn [cells_size csize] in *. replace (k + (n - k + 0))%nat with (n + 0)%nat by lia. exact Hw.
Qed.

Lemma rw_cells_cb_merge : forall m A n1 j1 n2 j2,
  rw_cells rsegs m A [CB n1 j1; CB n2 j2] -> rw_cells rsegs m A [CB (n1 + n2) (j1 ++ j2)].
Proof.
  intros m A n1 j1 n2 j2 [[Hwf Hb] Hw]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as (H1 & H2 & _).
  split; [split|].
  - cbn [cells_wf cell_wf]. rewrite length_app. split; [lia|exact I].
  - cbn [cells_bytes cbytes] in *. rewrite app_nil_r in *. exact Hb.
  - cbn [cells_size csize] in *. replace (n1 + n2 + 0)%nat with (n1 + (n2 + 0))%nat by lia. exact Hw.
Qed.

(* the byte a C1 cell at the head holds *)
Lemma rw_cells_head_byte : forall m A b cs, rw_cells rsegs m A (C1 b :: cs) -> bytes_at rsegs m A [b].
Proof.
  intros m A b cs [[_ Hb] _].
  assert (Hb' : bytes_at rsegs m A ([b] ++ cells_bytes cs)) by exact Hb.
  apply bytes_at_app in Hb'. exact (proj1 Hb').
Qed.

(* a buffer whose first byte the walk stored is still a buffer of the same size *)
Lemma rw_cells_C1_forget : forall m A b n j, rw_cells rsegs m A [C1 b; CB n j] ->
  exists junk, rw_cells rsegs m A [CB (S n) junk].
Proof.
  intros m A b n j [[Hwf Hb] Hw]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as (_ & Hj & _).
  exists (b :: j). split; [split|].
  - cbn [cells_wf cell_wf]. cbn [length]. split; [lia|exact I].
  - cbn [cells_bytes cbytes] in *. exact Hb.
  - cbn [cells_size csize] in *. exact Hw.
Qed.

Lemma cstr_nil_of_byte : forall m a, bytes_at rsegs m a [zb 0] -> cstr_at m a [].
Proof. intros m a H. split; [exact H | intros []]. Qed.

Lemma byte_ne0 : forall b : byte, b <> zb 0 -> bv_unsigned b <> 0.
Proof.
  intros b Hb E. apply Hb. apply bv_eq. rewrite E. reflexivity.
Qed.

(* ---- uniqueness of the views, so a Post's universally quantified views are the Pre's ---- *)

Lemma list_eq_nth : forall {A : Type} (l1 l2 : list A), (forall i, nth_error l1 i = nth_error l2 i) -> l1 = l2.
Proof.
  intros A. induction l1 as [|x l1 IH]; intros [|y l2] H.
  - reflexivity.
  - specialize (H 0%nat). cbn in H. discriminate.
  - specialize (H 0%nat). cbn in H. discriminate.
  - pose proof (H 0%nat) as H0. cbn in H0. injection H0 as E. subst y. f_equal.
    apply IH. intros i. exact (H (S i)).
Qed.

Lemma bytes_at_uniq : forall m a l1 l2, bytes_at rsegs m a l1 -> bytes_at rsegs m a l2 ->
  length l1 = length l2 -> l1 = l2.
Proof.
  intros m a l1 l2 (_ & _ & H1) (_ & _ & H2) HL. apply list_eq_nth. intros i.
  destruct (Nat.ltb_spec i (length l1)) as [Hi|Hi].
  - rewrite <- (H1 i Hi), <- (H2 i ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None l1 i) Hi), (proj2 (nth_error_None l2 i) ltac:(lia)). reflexivity.
Qed.

Lemma cstr_at_uniq : forall m a s1 s2, cstr_at m a s1 -> cstr_at m a s2 -> s1 = s2.
Proof.
  assert (K : forall m a s1 s2, cstr_at m a s1 -> cstr_at m a s2 -> ~ (length s1 < length s2)%nat).
  { intros m a s1 s2 [B1 N1] [B2 N2] Hl.
    destruct B1 as (_ & _ & H1). destruct B2 as (_ & _ & H2).
    assert (L1 : (length s1 < length (s1 ++ [zb 0]))%nat) by (rewrite length_app; cbn; lia).
    assert (L2 : (length s1 < length (s2 ++ [zb 0]))%nat) by (rewrite length_app; cbn; lia).
    pose proof (H1 _ L1) as E1. pose proof (H2 _ L2) as E2. rewrite E1 in E2.
    rewrite nth_error_app2 in E2 by lia. rewrite Nat.sub_diag in E2. cbn in E2.
    rewrite nth_error_app1 in E2 by lia. symmetry in E2. apply nth_error_In in E2. exact (N2 E2). }
  intros m a s1 s2 C1 C2.
  assert (E : length s1 = length s2).
  { destruct (Nat.lt_trichotomy (length s1) (length s2)) as [Hl|[Hl|Hl]].
    - exfalso. exact (K m a s1 s2 C1 C2 Hl).
    - exact Hl.
    - exfalso. exact (K m a s2 s1 C2 C1 Hl). }
  destruct C1 as [B1 _]. destruct C2 as [B2 _].
  apply (app_inv_tail [zb 0]). apply (bytes_at_uniq m a); [exact B1 | exact B2 |].
  rewrite !length_app, E. reflexivity.
Qed.

Lemma model_at_uniq : forall m p b1 b2, model_at m p b1 -> model_at m p b2 -> b1 = b2.
Proof. intros m p b1 b2 [[B1 _] L1] [[B2 _] L2]. apply (bytes_at_uniq m p); [exact B1 | exact B2 | lia]. Qed.

Lemma nlk_at_uniq : forall m b1 b2, nlk_at m b1 -> nlk_at m b2 -> b1 = b2.
Proof. intros m b1 b2 [[B1 _] L1] [[B2 _] L2]. apply (bytes_at_uniq m A_G_NL); [exact B1 | exact B2 | lia]. Qed.

Lemma str_arg_uniq : forall m a o1 o2, str_arg m a o1 -> str_arg m a o2 -> o1 = o2.
Proof.
  intros m a [s1|] [s2|] H1 H2; cbn in H1, H2.
  - f_equal. exact (cstr_at_uniq m a s1 s2 (proj2 H1) (proj2 H2)).
  - exfalso. destruct H1 as [H1 _]. contradiction.
  - exfalso. destruct H2 as [H2 _]. contradiction.
  - reflexivity.
Qed.

Lemma iftab_uniq : forall m bs t1 t2, iftab_at m bs t1 -> iftab_at m bs t2 -> t1 = t2.
Proof.
  intros m bs t1 t2 (N1 & _ & H1) (N2 & _ & H2). apply list_eq_nth. intros i.
  destruct (nth_error t1 i) as [[n1 x1]|] eqn:E1; destruct (nth_error t2 i) as [[n2 x2]|] eqn:E2.
  - destruct (H1 i n1 x1 E1) as (R1 & p1 & U1 & _ & C1 & X1).
    destruct (H2 i n2 x2 E2) as (R2 & p2 & U2 & _ & C2 & X2).
    unfold u64_at, u32_at in *.
    assert (EP : le8 (wz p1) = le8 (wz p2))
      by (apply (bytes_at_uniq m _ _ _ U1 U2); rewrite !length_le8; reflexivity).
    apply (f_equal le_bytes_to_word) in EP. rewrite !le_bytes_to_word_le8 in EP.
    pose proof (bytes_at_bound _ _ _ _ (proj1 C1)) as Bp1. pose proof (bytes_at_bound _ _ _ _ (proj1 C2)) as Bp2.
    rewrite length_app in Bp1, Bp2. cbn [length] in Bp1, Bp2.
    assert (Ep : p1 = p2).
    { apply (f_equal (@bv_unsigned 64)) in EP. unfold wz in EP.
      rewrite !unsigned_lit in EP by lia. exact EP. }
    subst p2. rewrite (cstr_at_uniq m p1 n1 n2 C1 C2).
    assert (EX : le4 (wz x1) = le4 (wz x2))
      by (apply (bytes_at_uniq m _ _ _ X1 X2); rewrite !length_le4; reflexivity).
    apply (f_equal bytes_le_to_Z) in EX. rewrite !bytes_le_to_Z_le4 in EX. unfold wz in EX.
    rewrite !unsigned_lit in EX by lia. rewrite !Z.mod_small in EX by lia. subst x2. reflexivity.
  - exfalso. assert (L1 : (i < length t1)%nat) by (apply nth_error_Some; rewrite E1; discriminate).
    apply nth_error_None in E2. lia.
  - exfalso. assert (L2 : (i < length t2)%nat) by (apply nth_error_Some; rewrite E2; discriminate).
    apply nth_error_None in E1. lia.
  - reflexivity.
Qed.

Lemma clear1 : forall l h v n, (v + n <= l \/ h <= v) -> clear_of [(l, h)] v n.
Proof. intros. intros x Hx. cbn [outside]. split; [lia | exact I]. Qed.

Lemma index_of_range : forall tab nm,
  (forall i n ix, nth_error tab i = Some (n, ix) -> 0 <= ix < 2 ^ 31) -> 0 <= index_of tab nm < 2 ^ 31.
Proof.
  induction tab as [|[n ix] tab IH]; intros nm H; cbn [index_of].
  - lia.
  - destruct (bl_eqb n nm).
    + exact (H 0%nat n ix eq_refl).
    + apply IH. intros i n' ix' Hi. exact (H (S i) n' ix' Hi).
Qed.

Lemma iftab_range : forall m bs tab, iftab_at m bs tab ->
  forall i n ix, nth_error tab i = Some (n, ix) -> 0 <= ix < 2 ^ 31.
Proof. intros m bs tab (_ & _ & H) i n ix Hi. exact (proj1 (H i n ix Hi)). Qed.

Lemma talk_after_sock : forall K, k_sock (talk_after K) = 0.
Proof.
  intros K. unfold talk_after, talk_core.
  destruct (negb (k_sock K =? 0)); [reflexivity|].
  destruct (negb (k_send K =? 0)); [reflexivity|].
  destruct (chunk_loop (S (length (k_chunks K))) (k_chunks K) (k_next K)) as [v j].
  destruct v; reflexivity.
Qed.

Lemma bytes_eq_bz : forall l1 l2 : list byte, map bz l1 = map bz l2 -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as Hx Hl. f_equal; [apply bv_eq; exact Hx | apply IH; exact Hl].
Qed.

Lemma index_of_post_ext : post_ext (fun regs m regs' m' =>
       forall bs tab nm, nlk_at m bs -> iftab_at m bs tab -> cstr_at m (arg regs 0) nm ->
         getr regs' 10 = wz (index_of tab nm)).
Proof.
  intros r1 r2 m q1 q2 m' E1 E2 H bs tab nm H1 H2 H3. rewrite <- E2. apply (H bs tab nm H1 H2).
  unfold arg in *. rewrite E1. exact H3.
Qed.
