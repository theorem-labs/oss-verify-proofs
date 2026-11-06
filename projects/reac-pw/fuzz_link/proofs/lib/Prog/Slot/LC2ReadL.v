(* Piece READ of arm c2 (op_mark) of the slot, plain image: the facts LC2Read.v uses.
   1. the code model_read answers: its range (so `beqz a0` at 0x13d9c decides `r_rc = 0`), the state
      read_core leaves, and mmark's answer on each of the three paths of 0x13d70 - 0x13da0;
   2. the frame of the slot split around the two buffers model_read fills, and joined again;
   3. what model_read's write set W = its window, the model block and the two buffers leaves alone
      (c2r_W), and the transport of every cut fact over it (c2r_keep);
   4. the Pre, Wr and Post of model_read_c.v, and the step past a `leaf` call (c2r_call, the form of
      LC1Call.v's leaf_call_eqv). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem model_read_c mk_leaf printf_facts_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC2Defs.
Local Open Scope Z_scope.

(* ==========================================================================
   1. The model
   ========================================================================== *)

Lemma c2r_rd32s_range : forall c off, -2^31 <= rd32s c off < 2^31.
Proof.
  intros c off. unfold rd32s, rd32, link_spec.rdn. cbv zeta.
  assert (HL : (length (slice c off 4) <= 4)%nat).
  { unfold slice. rewrite length_firstn. change (Z.to_nat 4) with 4%nat. lia. }
  pose proof (bytes_le_to_Z_nonneg (slice c off 4)) as H0.
  pose proof (bytes_le_to_Z_bound (slice c off 4)) as H1.
  assert (H2 : 2 ^ (8 * Z.of_nat (length (slice c off 4))) <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
  assert (H3 : bytes_le_to_Z (slice c off 4) < 2 ^ 32) by (eapply Z.lt_le_trans; [exact H1 | exact H2]).
  clear H1 H2 HL. set (v := bytes_le_to_Z (slice c off 4)) in *.
  destruct (v <? 2 ^ 31) eqn:E; cbv beta iota; [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; lia.
Qed.

Definition c2r_err_ok (v : nlv) : Prop :=
  match v with NlErr code => -2^31 <= code < 2^31 | _ => True end.

Lemma c2r_msg_scan_ok : forall fuel c off left, c2r_err_ok (msg_scan fuel c off left).
Proof.
  induction fuel as [|f IH]; intros c off left; [exact I|].
  cbn [msg_scan]. cbv zeta.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    try exact I; try apply IH; cbn [c2r_err_ok]; apply c2r_rd32s_range.
Qed.

Lemma c2r_chunk_loop_ok : forall fuel cs i, c2r_err_ok (fst (chunk_loop fuel cs i)).
Proof.
  induction fuel as [|f IH]; intros cs i; [exact I|].
  cbn [chunk_loop]. destruct (nth_error cs i) as [c|]; [|exact I].
  unfold chunk_walk.
  pose proof (c2r_msg_scan_ok (S (length c)) c 0 (Z.of_nat (length c))) as H.
  destruct (msg_scan (S (length c)) c 0 (Z.of_nat (length c))); cbn [fst]; first [exact I | exact H | apply IH].
Qed.

Lemma c2r_talk_rc_range : forall K, 0 <= k_sock K < 2^31 -> 0 <= k_send K < 2^31 -> 0 <= k_end K < 2^31 ->
  -2^31 <= talk_rc_lib K < 2^31.
Proof.
  intros K H1 H2 H3. unfold talk_rc_lib, talk_core.
  destruct (negb (k_sock K =? 0)); [cbn [fst]; lia|].
  destruct (negb (k_send K =? 0)); [cbn [fst]; lia|].
  pose proof (c2r_chunk_loop_ok (S (length (k_chunks K))) (k_chunks K) (k_next K)) as HC.
  destruct (chunk_loop (S (length (k_chunks K))) (k_chunks K) (k_next K)) as [v j].
  cbn [fst] in HC.
  assert (EIO : E_IO = 5) by reflexivity.
  destruct v; cbn [fst]; [lia | lia | cbn [c2r_err_ok] in HC; lia | lia].
Qed.

Lemma c2r_read_core_range : forall tab nm kc ac reqs K,
  0 <= k_sock K < 2^31 -> 0 <= k_send K < 2^31 -> 0 <= k_end K < 2^31 ->
  -2^31 <= r_rc (read_core tab nm kc ac reqs K) < 2^31.
Proof.
  intros tab nm kc ac reqs K H1 H2 H3.
  assert (EI : E_INVAL = 22) by reflexivity. assert (ED : E_NODEV = 19) by reflexivity.
  unfold read_core. destruct nm as [s|]; [|cbn [r_rc]; lia]. cbv zeta.
  destruct (Nat.eqb (length s) 0); [cbn [r_rc]; lia|].
  destruct (index_of tab s =? 0); [cbn [r_rc]; lia|].
  cbn [r_rc]. apply c2r_talk_rc_range; assumption.
Qed.

Lemma c2r_rd_range : forall t kbs, nlk_wf kbs -> -2^31 <= r_rc (c2_rd t kbs) <= RC_FAILS.
Proof.
  intros t kbs W. unfold c2_rd, read_model. cbv zeta. cbn [r_rc].
  assert (H : -2^31 <= r_rc (read_core link_tab (Some t) KIND_CAP ALIAS_MAX [] (nk_kstate kbs)) < 2^31).
  { destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & He & Hs & Hd & _).
    apply c2r_read_core_range; unfold nk_kstate; cbn [k_sock k_send k_end]; lia. }
  unfold norm_rc, RC_FAILS.
  match goal with |- context [0 <? ?x] => destruct (0 <? x) eqn:E end; cbv beta iota;
    [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; lia.
Qed.

(* `beqz a0` at 0x13d9c: a0 = wz rc is the zero word exactly when rc = 0 *)
Lemma c2r_rc_zero : forall t kbs, nlk_wf kbs ->
  bv_unsigned (wz (r_rc (c2_rd t kbs))) = 0 -> r_rc (c2_rd t kbs) = 0.
Proof.
  intros t kbs W H. pose proof (c2r_rd_range t kbs W) as R. unfold RC_FAILS in R.
  unfold wz in H. rewrite unsigned_lit_wrap in H.
  set (x := r_rc (c2_rd t kbs)) in *.
  destruct (Z_lt_le_dec x 0) as [Hn|Hp].
  - rewrite <- (Z.mod_add x 1 (2^64)) in H by lia. rewrite Z.mod_small in H by lia. lia.
  - rewrite Z.mod_small in H by lia. exact H.
Qed.

Lemma c2r_read_core_state : forall tab nm kc ac reqs K,
  k_chunks (r_state (read_core tab nm kc ac reqs K)) = k_chunks K /\
  k_end (r_state (read_core tab nm kc ac reqs K)) = k_end K.
Proof.
  intros tab nm kc ac reqs K. unfold read_core. destruct nm as [s|]; [|split; reflexivity]. cbv zeta.
  destruct (Nat.eqb (length s) 0); [split; reflexivity|].
  destruct (index_of tab s =? 0); [split; reflexivity|].
  cbn [r_state]. unfold talk_after, talk_core.
  destruct (negb (k_sock K =? 0)); [split; reflexivity|].
  destruct (negb (k_send K =? 0)); [split; reflexivity|].
  destruct (chunk_loop (S (length (k_chunks K))) (k_chunks K) (k_next K)) as [v j].
  destruct v; split; reflexivity.
Qed.

(* the model block after model_read holds the state of the read, field by field *)
Lemma c2r_kstate : forall mbs' kbs t,
  md_next mbs' = Z.of_nat (k_next (r_state (c2_rd t kbs))) ->
  md_socket_errno mbs' = k_sock (r_state (c2_rd t kbs)) ->
  md_send_errno mbs' = k_send (r_state (c2_rd t kbs)) ->
  md_kstate mbs' kbs = r_state (c2_rd t kbs).
Proof.
  intros mbs' kbs t H1 H2 H3.
  pose proof (c2r_read_core_state link_tab (Some t) KIND_CAP ALIAS_MAX [] (nk_kstate kbs)) as [C1 C2].
  unfold c2_rd, read_model in *. cbv zeta in *. cbn [r_state] in *.
  unfold md_kstate.
  revert C1 C2 H1 H2 H3.
  destruct (r_state (read_core link_tab (Some t) KIND_CAP ALIAS_MAX [] (nk_kstate kbs))) as [ch nx en so se].
  cbn [k_chunks k_end k_next k_sock k_send]. unfold nk_kstate. cbn [k_chunks k_end].
  intros C1 C2 H1 H2 H3. rewrite H1, H2, H3, Nat2Z.id, C1, C2. reflexivity.
Qed.

Lemma c2r_reqs_nil : forall mbs, md_n_req mbs = 0 -> md_reqs mbs = [].
Proof. intros mbs H. unfold md_reqs. rewrite H. reflexivity. Qed.

(* mmark on the three paths: NULL name, empty name, a read that failed *)
Lemma c2r_mm_none : forall s kbs gbs, sel_name s = None ->
  m_rc (c2_MM s kbs gbs) = - E_INVAL /\ m_reqs (c2_MM s kbs gbs) = [] /\ m_marks (c2_MM s kbs gbs) = mk_names gbs.
Proof. intros s kbs gbs EN. unfold c2_MM, mmark. rewrite EN. repeat split; reflexivity. Qed.

Lemma c2r_mm_empty : forall s kbs gbs, sel_name s = Some [] ->
  m_rc (c2_MM s kbs gbs) = - E_INVAL /\ m_reqs (c2_MM s kbs gbs) = [] /\ m_marks (c2_MM s kbs gbs) = mk_names gbs.
Proof. intros s kbs gbs EN. unfold c2_MM, mmark. rewrite EN. repeat split; reflexivity. Qed.

Lemma c2r_mm_read : forall s kbs gbs t, sel_name s = Some t -> t <> [] -> r_rc (c2_rd t kbs) <> 0 ->
  m_rc (c2_MM s kbs gbs) = r_rc (c2_rd t kbs) /\ m_reqs (c2_MM s kbs gbs) = r_reqs (c2_rd t kbs) /\
  m_marks (c2_MM s kbs gbs) = mk_names gbs.
Proof.
  intros s kbs gbs t EN NE RC. unfold c2_MM, mmark. rewrite EN.
  destruct t as [|b t]; [congruence|].
  change (Nat.eqb (length (b :: t)) 0) with false. cbv beta iota zeta.
  change (read_model link_tab (Some (b :: t)) KIND_CAP ALIAS_MAX [] (nk_kstate kbs)) with (c2_rd (b :: t) kbs).
  destruct (r_rc (c2_rd (b :: t) kbs) =? 0) eqn:ER; [apply Z.eqb_eq in ER; contradiction|].
  cbn [negb]. repeat split; reflexivity.
Qed.

(* the two branch words *)
Lemma c2r_eqb0 : forall x : word, bv_eqb x (Z_to_bv 64 0) = true -> bv_unsigned x = 0.
Proof. intros x H. unfold bv_eqb in H. apply Z.eqb_eq in H. exact H. Qed.

Lemma c2r_neqb0 : forall x : word, bv_eqb x (Z_to_bv 64 0) = false -> bv_unsigned x <> 0.
Proof. intros x H. unfold bv_eqb in H. apply Z.eqb_neq in H. exact H. Qed.

Lemma c2r_zxb_zero : forall b : byte, bv_eqb (zxb b) (Z_to_bv 64 0) = true -> b = zb 0.
Proof.
  intros b H. apply c2r_eqb0 in H. unfold zxb in H.
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  rewrite unsigned_lit in H by lia.
  apply bv_eq. rewrite H. reflexivity.
Qed.

(* ==========================================================================
   2. Cells: one CB cell, two lists of cells, the slot frame around the two buffers
   ========================================================================== *)

Lemma c2r_rw_cb : forall m A n bs,
  rw_cells rsegs m A [CB n bs] <-> length bs = n /\ bytes_at rsegs m A bs /\ wr_at rsegs m A (Z.of_nat n).
Proof.
  intros m A n bs. unfold rw_cells, cells_at. cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize].
  rewrite app_nil_r, Nat.add_0_r. tauto.
Qed.

Lemma c2r_wr_app : forall m A n1 n2, 0 <= n1 -> 0 <= n2 ->
  wr_at rsegs m A (n1 + n2) <-> wr_at rsegs m A n1 /\ wr_at rsegs m (A + n1) n2.
Proof.
  intros m A n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & Hc). split.
    + split; [lia|]. split; [lia|]. intros i Hi. apply Hc. lia.
    + split; [lia|]. split; [lia|]. intros i Hi. rewrite <- Z.add_assoc. apply Hc. lia.
  - intros [(Ha & Hb & Hc) (Ha' & Hb' & Hc')]. split; [lia|]. split; [lia|].
    intros i Hi. destruct (Z_lt_le_dec i n1) as [L|L]; [apply Hc; lia|].
    replace (A + i) with (A + n1 + (i - n1)) by lia. apply Hc'. lia.
Qed.

Lemma c2r_rw_app : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) <->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite c2r_wr_app by lia.
  split.
  - intros [[[W1 W2] B] [R1 R2]].
    apply (proj1 (bytes_at_app rsegs _ _ _ _)) in B. destruct B as [B1 B2].
    rewrite cells_bytes_length in B2 by exact W1.
    split; [split; [split; assumption | exact R1] | split; [split; assumption | exact R2]].
  - intros [[[W1 B1] R1] [[W2 B2] R2]].
    split; [split; [split; assumption|] | split; assumption].
    apply (proj2 (bytes_at_app rsegs _ _ _ _)). split; [exact B1|].
    rewrite cells_bytes_length by exact W1. exact B2.
Qed.

Lemma c2r_cb_split : forall m A n1 n2 bs,
  rw_cells rsegs m A [CB (n1 + n2) bs] ->
  rw_cells rsegs m A [CB n1 (firstn n1 bs)] /\ rw_cells rsegs m (A + Z.of_nat n1) [CB n2 (skipn n1 bs)].
Proof.
  intros m A n1 n2 bs H. apply c2r_rw_cb in H. destruct H as (L & B & W).
  rewrite Nat2Z.inj_add in W. apply c2r_wr_app in W; [|lia|lia]. destruct W as [W1 W2].
  rewrite <- (firstn_skipn n1 bs) in B. apply (proj1 (bytes_at_app rsegs _ _ _ _)) in B. destruct B as [B1 B2].
  assert (L1 : length (firstn n1 bs) = n1) by (rewrite length_firstn; lia).
  assert (L2 : length (skipn n1 bs) = n2) by (rewrite length_skipn; lia).
  rewrite L1 in B2.
  split; apply c2r_rw_cb; (split; [assumption | split; assumption]).
Qed.

Lemma c2r_cb_join : forall m A n1 n2 b1 b2,
  rw_cells rsegs m A [CB n1 b1] -> rw_cells rsegs m (A + Z.of_nat n1) [CB n2 b2] ->
  rw_cells rsegs m A [CB (n1 + n2) (b1 ++ b2)].
Proof.
  intros m A n1 n2 b1 b2 H1 H2. apply c2r_rw_cb in H1. apply c2r_rw_cb in H2.
  destruct H1 as (L1 & B1 & W1). destruct H2 as (L2 & B2 & W2).
  apply c2r_rw_cb. split; [rewrite length_app; lia|]. split.
  - apply (proj2 (bytes_at_app rsegs _ _ _ _)). rewrite L1. split; assumption.
  - rewrite Nat2Z.inj_add. apply c2r_wr_app; [lia|lia|]. split; assumption.
Qed.

(* the ten cells below the two buffers *)
Definition c2r_pre10 (md mk P N : Z) (j0 : list byte) : list cell :=
  [CB 8 j0; C8 (wz A_ODD); C8 (wz (md + MD_MARK)); C8 (wz A_EMPTY); C8 (wz mk); C8 (wz A_G_NAMES);
   C8 (wz A_JT); C8 (wz GNL42); C8 (wz P); C8 (wz N)].

Lemma c2r_lh_cells : forall md mk P N j0 j1 j2,
  lh_cells md mk P N j0 j1 j2 = c2r_pre10 md mk P N j0 ++ [CB 40 j1] ++ [CB 256 j2].
Proof. reflexivity. Qed.

Lemma c2r_frame_split : forall E P N j0 j1 j2 m, c2_frame E P N j0 j1 j2 m ->
  rw_cells rsegs m (e_S E - SLOT_FRAME) (c2r_pre10 (e_md E) (e_mk E) P N j0) /\
  rw_cells rsegs m (e_S E - SLOT_FRAME + 80) [CB 32 (firstn 32 j1)] /\
  rw_cells rsegs m (e_S E - SLOT_FRAME + 112) [CB 8 (skipn 32 j1)] /\
  rw_cells rsegs m (e_S E - SLOT_FRAME + 120) [CB 256 j2].
Proof.
  intros E P N j0 j1 j2 m H. unfold c2_frame in H. rewrite c2r_lh_cells in H.
  apply c2r_rw_app in H. destruct H as [H0 H].
  apply c2r_rw_app in H. destruct H as [H1 H2].
  change (Z.of_nat (cells_size (c2r_pre10 (e_md E) (e_mk E) P N j0))) with 80 in H1, H2.
  change (Z.of_nat (cells_size [CB 40 j1])) with 40 in H2.
  change (CB 40 j1) with (CB (32 + 8) j1) in H1.
  apply c2r_cb_split in H1. destruct H1 as [H1a H1b].
  change (Z.of_nat 32) with 32 in H1b.
  replace (e_S E - SLOT_FRAME + 80 + 32) with (e_S E - SLOT_FRAME + 112) in H1b by lia.
  replace (e_S E - SLOT_FRAME + 80 + 40) with (e_S E - SLOT_FRAME + 120) in H2 by lia.
  split; [exact H0 | split; [exact H1a | split; [exact H1b | exact H2]]].
Qed.

Lemma c2r_frame_join : forall E P N j0 a b c m,
  rw_cells rsegs m (e_S E - SLOT_FRAME) (c2r_pre10 (e_md E) (e_mk E) P N j0) ->
  rw_cells rsegs m (e_S E - SLOT_FRAME + 80) [CB 32 a] ->
  rw_cells rsegs m (e_S E - SLOT_FRAME + 112) [CB 8 b] ->
  rw_cells rsegs m (e_S E - SLOT_FRAME + 120) [CB 256 c] ->
  c2_frame E P N j0 (a ++ b) c m.
Proof.
  intros E P N j0 a b c m H0 H1 H2 H3. unfold c2_frame. rewrite c2r_lh_cells.
  apply c2r_rw_app. split; [exact H0|].
  change (Z.of_nat (cells_size (c2r_pre10 (e_md E) (e_mk E) P N j0))) with 80.
  apply c2r_rw_app. split.
  - change (CB 40 (a ++ b)) with (CB (32 + 8) (a ++ b)). apply c2r_cb_join; [exact H1|].
    change (Z.of_nat 32) with 32. replace (e_S E - SLOT_FRAME + 80 + 32) with (e_S E - SLOT_FRAME + 112) by lia.
    exact H2.
  - change (Z.of_nat (cells_size [CB 40 (a ++ b)])) with 40.
    replace (e_S E - SLOT_FRAME + 80 + 40) with (e_S E - SLOT_FRAME + 120) by lia. exact H3.
Qed.

(* ==========================================================================
   3. What model_read leaves alone
   ========================================================================== *)

(* its window [sp - 240, sp), the model block, kind[32] at sp + 0x50, alias[256] at sp + 0x78 (sp = S - 480) *)
Definition c2r_W (E : lenv) : list ivl :=
  [(e_S E - 720, e_S E - 480); (e_md E, e_md E + MD_SIZE); (e_S E - 400, e_S E - 368);
   (e_S E - 360, e_S E - 104)].

(* a range below the window and apart from the model block, or above the buffers *)
Definition c2r_far (E : lenv) (a n : Z) : Prop :=
  (a + n <= e_md E \/ e_md E + MD_SIZE <= a) /\ (a + n <= e_S E - 720 \/ e_S E - 104 <= a).

Lemma c2r_dj : forall E a n, c2r_far E a n -> disjoint_from (c2r_W E) a n.
Proof.
  intros E a n [H1 H2]. unfold c2r_W. cbn [disjoint_from]. unfold MD_SIZE in *.
  repeat split; try exact I; lia.
Qed.

(* the image's reserved segments cover [0x10000, 0x960e0): the walk snprintf.v makes (img_free_bound) *)
Definition c2r_ivs (l : list (word * word)) : list (Z * Z) :=
  map (fun s => (bv_unsigned (fst s), bv_unsigned (fst s) + bv_unsigned (snd s))) l.

Fixpoint c2r_cov (L : list (Z * Z)) (cur : Z) : Z :=
  match L with [] => cur | (a, b) :: L' => c2r_cov L' (if a <=? cur then Z.max cur b else cur) end.

Lemma c2r_cov_in : forall L cur x, cur <= x < c2r_cov L cur -> exists a b, In (a, b) L /\ a <= x < b.
Proof.
  induction L as [|[a b] L IH]; intros cur x Hx; cbn [c2r_cov] in Hx; [lia|].
  revert Hx. destruct (a <=? cur) eqn:E; intros Hx.
  - apply Z.leb_le in E. destruct (Z.lt_ge_cases x (Z.max cur b)) as [H|H].
    + exists a, b. split; [left; reflexivity | lia].
    + destruct (IH (Z.max cur b) x ltac:(lia)) as (a' & b' & Hin & Hab). exists a', b'.
      split; [right; exact Hin | exact Hab].
  - destruct (IH cur x Hx) as (a' & b' & Hin & Hab). exists a', b'. split; [right; exact Hin | exact Hab].
Qed.

Lemma c2r_pages : 0x960e0 <= c2r_cov (c2r_ivs (segments_reserved rsegs)) 0x10000.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma c2r_img_free : forall D n, 0 <= D -> 0 < n -> pf_img_free D n -> D + n <= 0x10000 \/ 0x960e0 <= D.
Proof.
  intros D n HD Hn F.
  assert (C : forall x, 0x10000 <= x < 0x960e0 -> exists s, In s (segments_reserved rsegs)
                /\ bv_unsigned (fst s) <= x < bv_unsigned (fst s) + bv_unsigned (snd s)).
  { intros x Hx. pose proof c2r_pages as PG.
    destruct (c2r_cov_in (c2r_ivs (segments_reserved rsegs)) 0x10000 x ltac:(lia)) as (a & b & Hin & Hab).
    unfold c2r_ivs in Hin. apply in_map_iff in Hin. destruct Hin as (s & Es & Hs). injection Es as Ea Eb.
    exists s. split; [exact Hs | lia]. }
  destruct (Z.lt_ge_cases D 0x10000) as [H1|H1].
  - destruct (Z.le_gt_cases (D + n) 0x10000) as [H2|H2]; [left; exact H2|].
    destruct (C 0x10000 ltac:(lia)) as (s & Hs & Hx). exfalso.
    apply (F (0x10000 - D) ltac:(lia) s Hs). replace (D + (0x10000 - D)) with 0x10000 by lia. exact Hx.
  - destruct (Z.lt_ge_cases D 0x960e0) as [H2|H2]; [|right; exact H2].
    destruct (C D ltac:(lia)) as (s & Hs & Hx). exfalso.
    apply (F 0 ltac:(lia) s Hs). rewrite Z.add_0_r. exact Hx.
Qed.

(* every range of the image's own data (.rodata, .data.rel.ro, .bss) is far *)
Lemma c2r_static_far : forall E a n, lenv_ok E -> 0x10000 <= a -> a + n <= 0x960e0 -> 0 <= n -> c2r_far E a n.
Proof.
  intros E a n HE Ha Hn H0. destruct HE as (S1 & S2 & _ & (M1 & M2 & M3) & _).
  pose proof (c2r_img_free (e_md E) MD_SIZE ltac:(lia) ltac:(unfold MD_SIZE; lia) M3) as IF.
  unfold c2r_far. unfold SLOT_STACK_Z, MD_SIZE in *. split; lia.
Qed.

Lemma c2r_bytes_det : forall m a xs ys,
  bytes_at rsegs m a xs -> bytes_at rsegs m a ys -> length xs = length ys -> xs = ys.
Proof.
  intros m a xs ys (_ & _ & Hx) (_ & _ & Hy) L. apply nth_error_ext. intros n.
  destruct (Nat.lt_ge_cases n (length xs)) as [Hn|Hn].
  - rewrite <- (Hx n Hn), <- (Hy n ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None xs n) Hn), (proj2 (nth_error_None ys n) ltac:(lia)). reflexivity.
Qed.

(* the interface names interfaces() points g_nl.if_name[i] at (LDefs ifptrs_at) *)
Lemma c2r_tab_len : length link_tab = 64%nat.
Proof. vm_compute. reflexivity. Qed.

Definition c2r_ptr_chk (i : nat) : bool :=
  match nth_error link_tab i with
  | Some (nm, _) => (0x10000 <=? nth i link_ptrs 0) && (nth i link_ptrs 0 + Z.of_nat (length nm) + 1 <=? 0x74400)
  | None => true
  end.

Lemma c2r_ptr_chk_all : forallb c2r_ptr_chk (seq 0 64) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma c2r_ptr_bound : forall i nm ix, nth_error link_tab i = Some (nm, ix) ->
  (i < 64)%nat /\ 0x10000 <= nth i link_ptrs 0 /\ nth i link_ptrs 0 + Z.of_nat (length nm) + 1 <= 0x74400.
Proof.
  intros i nm ix E.
  assert (Hi : (i < 64)%nat) by (rewrite <- c2r_tab_len; apply nth_error_Some; congruence).
  pose proof c2r_ptr_chk_all as C. rewrite forallb_forall in C.
  specialize (C i ltac:(apply in_seq; lia)). unfold c2r_ptr_chk in C. rewrite E in C.
  apply andb_true_iff in C. destruct C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2. auto.
Qed.

(* a word the memory holds where ifptrs_at holds the pointer: that pointer, up to 2^64 *)
Lemma c2r_ifp : forall m i n2 ix p, ifptrs_at m -> nth_error link_tab i = Some (n2, ix) ->
  u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
  exists d, p = 2 ^ 64 * d + nth i link_ptrs 0 /\ 0x10000 <= nth i link_ptrs 0 /\
            nth i link_ptrs 0 + Z.of_nat (length n2) + 1 <= 0x74400.
Proof.
  intros m i n2 ix p IP Ei Up.
  destruct (c2r_ptr_bound i n2 ix Ei) as (Hi & B1 & B2).
  pose proof (IP i Hi) as Uq.
  assert (Ew : wz p = wz (nth i link_ptrs 0)).
  { unfold u64_at in Up, Uq.
    pose proof (c2r_bytes_det m _ _ _ Up Uq ltac:(rewrite !length_le8; reflexivity)) as E.
    apply (f_equal le_bytes_to_word) in E. rewrite !le_bytes_to_word_le8 in E. exact E. }
  apply (f_equal (@bv_unsigned 64%N)) in Ew. unfold wz in Ew. rewrite !unsigned_lit_wrap in Ew.
  rewrite (Z.mod_small (nth i link_ptrs 0)) in Ew by lia.
  exists (p / 2 ^ 64). split; [|split; assumption].
  rewrite <- Ew. apply Z_div_mod_eq_full.
Qed.

(* the odd strings sit in .rodata *)
Definition c2r_odd_chk (i : nat) : bool :=
  (0x10000 <=? nth i odd_ptrs 0) && (nth i odd_ptrs 0 + Z.of_nat (length (nth i odd_strs [])) + 1 <=? 0x11eb4).

Lemma c2r_odd_bound : forall i, (i < 6)%nat ->
  0x10000 <= nth i odd_ptrs 0 /\ nth i odd_ptrs 0 + Z.of_nat (length (nth i odd_strs [])) + 1 <= 0x11eb4.
Proof.
  intros i Hi.
  assert (C : c2r_odd_chk i = true).
  { do 6 (destruct i as [|i]; [vm_compute; reflexivity|]). lia. }
  unfold c2r_odd_chk in C. apply andb_true_iff in C. destruct C as [C1 C2].
  apply Z.leb_le in C1. apply Z.leb_le in C2. split; assumption.
Qed.

(* moving a fact from m to m' when only W changed *)
Definition c2r_mv (E : lenv) (m m' : word -> option byte) : Prop :=
  lenv_ok E /\ munch (c2r_W E) m m' /\ wmono rsegs m m'.

Lemma c2r_tr_bytes : forall E m m' a bs, c2r_mv E m m' ->
  bytes_at rsegs m a bs -> c2r_far E a (Z.of_nat (length bs)) -> bytes_at rsegs m' a bs.
Proof.
  intros E m m' a bs (HE & MU & WM) H F. eapply bytes_at_transport; [exact H | exact MU | apply c2r_dj; exact F].
Qed.

Lemma c2r_tr_u8 : forall E m m' a bs, c2r_mv E m m' ->
  u8arr rsegs m a bs -> c2r_far E a (Z.of_nat (length bs)) -> u8arr rsegs m' a bs.
Proof.
  intros E m m' a bs (HE & MU & WM) H F.
  eapply u8arr_transport; [exact H | exact MU | exact WM | apply c2r_dj; exact F].
Qed.

Lemma c2r_tr_rw : forall E m m' a cs, c2r_mv E m m' ->
  rw_cells rsegs m a cs -> disjoint_from (c2r_W E) a (Z.of_nat (cells_size cs)) -> rw_cells rsegs m' a cs.
Proof.
  intros E m m' a cs (HE & MU & WM) H D. eapply rw_cells_transport; [exact H | exact MU | exact WM | exact D].
Qed.

Lemma c2r_tr_cstr : forall E m m' a t, c2r_mv E m m' ->
  cstr_at m a t -> c2r_far E a (Z.of_nat (length t) + 1) -> cstr_at m' a t.
Proof.
  intros E m m' a t MV [H N] F. split; [|exact N]. eapply c2r_tr_bytes; [exact MV | exact H |].
  rewrite length_app, Nat2Z.inj_add. exact F.
Qed.

Lemma c2r_tr_u64 : forall E m m' a v, c2r_mv E m m' -> u64_at m a v -> c2r_far E a 8 -> u64_at m' a v.
Proof.
  intros E m m' a v MV H F. unfold u64_at in *. eapply c2r_tr_bytes; [exact MV | exact H |].
  rewrite length_le8. exact F.
Qed.

Lemma c2r_tr_u32 : forall E m m' a v, c2r_mv E m m' -> u32_at m a v -> c2r_far E a 4 -> u32_at m' a v.
Proof.
  intros E m m' a v MV H F. unfold u32_at in *. eapply c2r_tr_bytes; [exact MV | exact H |].
  rewrite length_le4. exact F.
Qed.

Ltac c2r_sfar HE := apply c2r_static_far; [exact HE | | | ].

Lemma c2r_tr_gnames : forall E m m', c2r_mv E m m' -> gnames_at m -> gnames_at m'.
Proof.
  intros E m m' MV H k Hk. pose proof MV as (HE & _).
  destruct (H k Hk) as (rest & B & L). exists rest. split; [|exact L].
  eapply c2r_tr_bytes; [exact MV | exact B |]. rewrite L.
  c2r_sfar HE; unfold A_G_NAMES; lia.
Qed.

Lemma c2r_tr_odd : forall E m m', c2r_mv E m m' -> odd_at m -> odd_at m'.
Proof.
  intros E m m' MV H i Hi. pose proof MV as (HE & _).
  destruct (H i Hi) as [U C]. pose proof (c2r_odd_bound i Hi) as [B1 B2].
  split.
  - eapply c2r_tr_u64; [exact MV | exact U |]. c2r_sfar HE; unfold A_ODD; lia.
  - eapply c2r_tr_cstr; [exact MV | exact C |]. c2r_sfar HE; lia.
Qed.

Lemma c2r_tr_policy : forall E m m', c2r_mv E m m' -> policy_ro m -> policy_ro m'.
Proof.
  intros E m m' MV (P1 & P2 & P3 & P4). pose proof MV as (HE & _).
  assert (L1 : length S_PREFIX = 8%nat) by reflexivity.
  assert (L2 : length S_SERVED = 14%nat) by reflexivity.
  assert (L3 : length S_VLAN = 4%nat) by reflexivity.
  split; [|split; [|split]].
  - eapply c2r_tr_cstr; [exact MV | exact P1 |]. rewrite L1. c2r_sfar HE; unfold A_PREFIX; lia.
  - eapply c2r_tr_cstr; [exact MV | exact P2 |]. rewrite L2. c2r_sfar HE; unfold A_SERVED; lia.
  - eapply c2r_tr_cstr; [exact MV | exact P3 |]. rewrite L3. c2r_sfar HE; unfold A_VLAN; lia.
  - eapply c2r_tr_cstr; [exact MV | exact P4 |]. cbn [length]. c2r_sfar HE; unfold A_EMPTY; lia.
Qed.

Lemma c2r_tr_la : forall E m m', c2r_mv E m m' -> la_ok m -> la_ok m'.
Proof.
  intros E m m' MV (la & sl & R & B & L). pose proof MV as (HE & _).
  exists la, sl. split; [|split; [|exact L]].
  - eapply c2r_tr_rw; [exact MV | exact R |]. apply c2r_dj.
    change (Z.of_nat (cells_size [CB (Z.to_nat 300) la; C1 (zb 0)])) with 301.
    c2r_sfar HE; unfold A_LONG_ALIAS; lia.
  - eapply c2r_tr_bytes; [exact MV | exact B |]. rewrite L. c2r_sfar HE; unfold A_LONG_ALIAS, LONG_ALIAS_SIZE; lia.
Qed.

Lemma c2r_tr_texts : forall E m m', c2r_mv E m m' -> texts_at m -> texts_at m'.
Proof.
  intros E m m' MV H i Hi. pose proof MV as (HE & _).
  eapply c2r_tr_u64; [exact MV | exact (H i Hi) |]. c2r_sfar HE; unfold A_TEXTS; lia.
Qed.

Lemma c2r_tr_ifptrs : forall E m m', c2r_mv E m m' -> ifptrs_at m -> ifptrs_at m'.
Proof.
  intros E m m' MV H i Hi. pose proof MV as (HE & _).
  eapply c2r_tr_u64; [exact MV | exact (H i Hi) |]. c2r_sfar HE; unfold A_G_NL, NK_IF_NAME; lia.
Qed.

Lemma c2r_tr_guard : forall E m m', c2r_mv E m m' -> guard_m m -> guard_m m'.
Proof.
  intros E m m' MV [G1 (c & G2)]. pose proof MV as (HE & _). split; [|exists c].
  - eapply c2r_tr_bytes; [exact MV | exact G1 |]. rewrite length_le8. c2r_sfar HE; unfold A_GOT_GUARD_S; lia.
  - eapply c2r_tr_bytes; [exact MV | exact G2 |]. rewrite length_le8. c2r_sfar HE; unfold A_GUARD_S; lia.
Qed.

Lemma c2r_task : forall E m m', c2r_mv E m m' -> MemNorm.task_mem rsegs m -> MemNorm.task_mem rsegs m'.
Proof.
  intros E m m' (HE & MU & WM) T a b Ha.
  destruct (c2_outside_dec (c2r_W E) (bv_unsigned a)) as [O|O].
  - rewrite (MU a O) in Ha. exact (T a b Ha).
  - right. pose proof HE as (L1 & L2 & _ & (BM1 & BM2 & _) & _).
    assert (TS : 2 ^ 47 <= TASK_SIZE) by (apply Z.leb_le; vm_compute; reflexivity).
    unfold c2r_W in O. cbn [outside] in O. unfold MD_SIZE, SLOT_STACK_Z in *. lia.
Qed.

Lemma c2r_tr_fix : forall E m m', c2r_mv E m m' -> mem_inv rsegs m' ->
  stk rsegs m' (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME) -> c2_fix E m -> c2_fix E m'.
Proof.
  intros E m m' MV MI ST (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12).
  pose proof MV as (HE & MU & WM).
  pose proof HE as (L1 & L2 & _ & (BM1 & BM2 & _) & _ & _ & _ & _ & _ & _ & _ & _ & LS).
  split.
  { eapply c2r_tr_bytes; [exact MV | exact F1 |]. rewrite LS.
    unfold c2r_far, MD_SIZE, SLOT_STACK_Z in *. split; lia. }
  split; [exact (c2r_tr_gnames E m m' MV F2)|].
  split; [exact (c2r_tr_odd E m m' MV F3)|].
  split; [exact (c2r_tr_policy E m m' MV F4)|].
  split; [exact (c2r_tr_la E m m' MV F5)|].
  split; [exact (c2r_tr_texts E m m' MV F6)|].
  split; [exact (c2r_tr_ifptrs E m m' MV F7)|].
  split; [exact (wr_at_transport rsegs m m' _ _ F8 WM)|].
  split; [exact (c2r_tr_guard E m m' MV F9)|].
  split; [exact MI|]. split; [exact (c2r_task E m m' MV F11)|]. exact ST.
Qed.

Lemma c2r_tr_cursor : forall E m m' P N, c2r_mv E m m' ->
  cursor_ok m (e_p0 E) (e_pl E) P N -> cursor_ok m' (e_p0 E) (e_pl E) P N.
Proof.
  intros E m m' P N MV [B K]. pose proof MV as (HE & _).
  pose proof HE as (L1 & L2 & _ & _ & _ & _ & _ & _ & _ & (Q1 & Q2 & Q3) & Q4 & _).
  split; [|exact K]. eapply c2r_tr_bytes; [exact MV | exact B |].
  split; [exact Q4|]. unfold SLOT_STACK_Z in *. lia.
Qed.

Lemma c2r_tr_name : forall E m m' s, c2r_mv E m m' -> c2_name_ok m s -> c2_name_ok m' s.
Proof.
  intros E m m' s MV [SA K]. pose proof MV as (HE & _).
  assert (BND : forall t, sel_name s = Some t ->
            0x10000 <= sel_ptr s /\ sel_ptr s + Z.of_nat (length t) + 1 + 8 <= 0x960e0).
  { intros t Et. destruct (K t Et) as (Lt & Pl & _).
    destruct Pl as [(P1 & P2) | (k & Hk & Ek & L4)];
      [unfold A_RO_LO, A_RO_END in *; lia | rewrite Ek; unfold A_G_NAMES; lia]. }
  split.
  - revert SA. destruct (sel_name s) as [t|] eqn:Et; intros SA; [|exact SA].
    destruct SA as [NZ C]. split; [exact NZ|]. eapply c2r_tr_cstr; [exact MV | exact C |].
    destruct (BND t eq_refl) as [B1 B2]. c2r_sfar HE; lia.
  - intros t Et. destruct (K t Et) as (Lt & Pl & (sl & B & Ls)). split; [exact Lt|]. split; [exact Pl|].
    exists sl. split; [|exact Ls]. eapply c2r_tr_bytes; [exact MV | exact B |].
    destruct (BND t Et) as [B1 B2].
    pose proof (Z.mod_pos_bound (- (sel_ptr s + Z.of_nat (length t) + 1)) 8 ltac:(lia)) as MB.
    c2r_sfar HE; lia.
Qed.

Lemma c2r_tr_iftab : forall E m m' kbs, c2r_mv E m m' -> ifptrs_at m ->
  iftab_at m kbs link_tab -> iftab_at m' kbs link_tab.
Proof.
  intros E m m' kbs MV IP [N1 [N2 H]]. pose proof MV as (HE & _).
  split; [exact N1|]. split; [exact N2|].
  intros i nm ix Ei. destruct (H i nm ix Ei) as [Rix (p & U & NZ & C & U32)]. split; [exact Rix|].
  destruct (c2r_ifp m i nm ix p IP Ei U) as (d & Ep & B1 & B2).
  destruct (c2r_ptr_bound i nm ix Ei) as (Hi & _ & _).
  assert (Ed : d = 0).
  { destruct C as [(C1 & C2 & _) _]. rewrite length_app in C2. cbn [length] in C2. lia. }
  subst d. rewrite Z.mul_0_r, Z.add_0_l in Ep. subst p.
  exists (nth i link_ptrs 0). split; [|split; [exact NZ|split]].
  - eapply c2r_tr_u64; [exact MV | exact U |]. c2r_sfar HE; unfold A_G_NL, NK_IF_NAME; lia.
  - eapply c2r_tr_cstr; [exact MV | exact C |]. c2r_sfar HE; lia.
  - eapply c2r_tr_u32; [exact MV | exact U32 |]. c2r_sfar HE; unfold A_G_NL, NK_IF_INDEX; lia.
Qed.

Lemma c2r_tr_kern : forall E m m' i kbs, c2r_mv E m m' -> ifptrs_at m -> c2_kern i kbs m -> c2_kern i kbs m'.
Proof.
  intros E m m' i kbs MV IP ([U L] & K2 & K3 & K4). pose proof MV as (HE & _).
  split; [split; [|exact L]|]. 
  { eapply c2r_tr_u8; [exact MV | exact U |]. rewrite L. c2r_sfar HE; unfold A_G_NL, NK_SIZE; lia. }
  split; [exact K2|]. split; [exact (c2r_tr_iftab E m m' kbs MV IP K3)|]. exact K4.
Qed.

Lemma c2r_tr_marks : forall E m m' gbs, c2r_mv E m m' -> c2_marks E gbs m -> c2_marks E gbs m'.
Proof.
  intros E m m' gbs MV [[U L] W]. pose proof MV as (HE & _).
  split; [|exact W]. split; [|exact L]. eapply c2r_tr_u8; [exact MV | exact U |]. rewrite L.
  pose proof HE as (L1 & L2 & L3 & (BM1 & BM2 & BM3) & (BK1 & BK2 & BK3) & L6 & L7 & AMK & _).
  unfold c2r_far, MD_SIZE, MK_SIZE, SLOT_STACK_Z in *. split; lia.
Qed.

Lemma c2r_segfp : forall E m m', c2r_mv E m m' -> seg_fp (e_S E) (c2_hp E) m m'.
Proof.
  intros E m m' (HE & MU & WM). exists (c2r_W E). split; [exact MU|]. split; [exact WM|].
  intros x Hx O. unfold c2r_W in O. cbn [outside] in O. unfold own_w, c2_hp.
  pose proof HE as (L1 & L2 & _ & (BM1 & BM2 & _) & _).
  destruct (Z_lt_le_dec x (e_md E)) as [H1|H1]; [|destruct (Z_lt_le_dec x (e_md E + MD_SIZE)) as [H2|H2]].
  - left. unfold MD_SIZE, SLOT_STACK_Z in *. lia.
  - right; right; right; right; right. exists (e_md E), MD_SIZE. split; [left; reflexivity | lia].
  - left. unfold MD_SIZE, SLOT_STACK_Z in *. lia.
Qed.

(* everything a cut of this arm says of the memory, apart from the model block and the two buffers *)
Lemma c2r_keep : forall E i s m m' P N j0 kbs gbs b,
  c2r_mv E m m' -> mem_inv rsegs m' -> stk rsegs m' (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME) ->
  c2_fix E m -> cursor_ok m (e_p0 E) (e_pl E) P N -> c2_name_ok m s -> c2_kern i kbs m -> c2_marks E gbs m ->
  rw_cells rsegs m (e_S E - SLOT_FRAME) (c2r_pre10 (e_md E) (e_mk E) P N j0) ->
  rw_cells rsegs m (e_S E - SLOT_FRAME + 112) [CB 8 b] ->
  c2_fix E m' /\ cursor_ok m' (e_p0 E) (e_pl E) P N /\ c2_name_ok m' s /\ c2_kern i kbs m' /\
  c2_marks E gbs m' /\ rw_cells rsegs m' (e_S E - SLOT_FRAME) (c2r_pre10 (e_md E) (e_mk E) P N j0) /\
  rw_cells rsegs m' (e_S E - SLOT_FRAME + 112) [CB 8 b] /\ seg_fp (e_S E) (c2_hp E) m m'.
Proof.
  intros E i s m m' P N j0 kbs gbs b MV MI ST HX HC HNm HK HMk F0 F8.
  pose proof MV as (HE & _).
  pose proof HE as (L1 & L2 & _ & (BM1 & BM2 & _) & _).
  pose proof HX as (_ & _ & _ & _ & _ & _ & IP & _).
  split; [exact (c2r_tr_fix E m m' MV MI ST HX)|].
  split; [exact (c2r_tr_cursor E m m' P N MV HC)|].
  split; [exact (c2r_tr_name E m m' s MV HNm)|].
  split; [exact (c2r_tr_kern E m m' i kbs MV IP HK)|].
  split; [exact (c2r_tr_marks E m m' gbs MV HMk)|].
  split.
  { eapply c2r_tr_rw; [exact MV | exact F0 |].
    change (Z.of_nat (cells_size (c2r_pre10 (e_md E) (e_mk E) P N j0))) with 80.
    unfold c2r_W; cbn [disjoint_from]. unfold MD_SIZE, SLOT_FRAME, SLOT_STACK_Z in *.
    repeat split; try exact I; lia. }
  split.
  { eapply c2r_tr_rw; [exact MV | exact F8 |].
    change (Z.of_nat (cells_size [CB 8 b])) with 8.
    unfold c2r_W; cbn [disjoint_from]. unfold MD_SIZE, SLOT_FRAME, SLOT_STACK_Z in *.
    repeat split; try exact I; lia. }
  exact (c2r_segfp E m m' MV).
Qed.

(* ==========================================================================
   4. model_read's contract, and the step past a leaf call
   ========================================================================== *)

Definition c2r_mr_pre : bvmap 5 word -> (word -> option byte) -> Prop :=
  ltac:(let t := eval cbv delta [model_read_contract] in model_read_contract in
        lazymatch t with leaf _ _ ?P _ _ => exact P end).
Definition c2r_mr_wr : bvmap 5 word -> (word -> option byte) -> list ivl :=
  ltac:(let t := eval cbv delta [model_read_contract] in model_read_contract in
        lazymatch t with leaf _ _ _ ?W _ => exact W end).
Definition c2r_mr_post : bvmap 5 word -> (word -> option byte) -> bvmap 5 word -> (word -> option byte) -> Prop :=
  ltac:(let t := eval cbv delta [model_read_contract] in model_read_contract in
        lazymatch t with leaf _ _ _ _ ?Q => exact Q end).

Lemma c2r_eqv_cl_idem : forall (P : machine_state -> Prop) ms, eqv_cl (eqv_cl P) ms -> eqv_cl P ms.
Proof.
  intros P ms (c & (c0 & H0 & E0) & E). exists c0. split; [exact H0|]. exact (c2_ms_eqv_trans _ _ _ E0 E).
Qed.

Lemma c2r_evt_eqv_transport : forall (Q : machine_state -> Prop) c ms,
  ms_eqv c ms -> evt rsegs (eqv_cl Q) c -> evt rsegs (eqv_cl Q) ms.
Proof.
  intros Q c ms E H. pose proof (evt_register_transport rsegs _ c ms E H) as T.
  eapply evt_mono; [exact T|]. intros x Hx. apply c2r_eqv_cl_idem. exact Hx.
Qed.

Lemma c2r_reg_get_getr : forall (R : bvmap 5 word) (n : Z), 1 <= n < 32 ->
  reg_get R (Z_to_bv 5 n) = getr R (Z_to_bv 5 n).
Proof.
  intros R n Hn. unfold getr.
  assert (E : bv_eqb (Z_to_bv 5 n) 0 = false).
  { apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 5) with 32. change (bv_unsigned (0 : bv 5)) with 0. rewrite Z.mod_small; lia. }
  rewrite E. reflexivity.
Qed.

Lemma c2r_mkR_of_preserved :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (regs' : bvmap 5 word),
    regs_preserved (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   regs' ->
    mkR_of regs' =
    mkR (reg_get regs' 1) sp gp tp (reg_get regs' 5) (reg_get regs' 6) (reg_get regs' 7) s0 s1
        (reg_get regs' 10) (reg_get regs' 11) (reg_get regs' 12) (reg_get regs' 13) (reg_get regs' 14)
        (reg_get regs' 15) (reg_get regs' 16) (reg_get regs' 17)
        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
        (reg_get regs' 28) (reg_get regs' 29) (reg_get regs' 30) (reg_get regs' 31).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 regs' H.
  unfold mkR_of.
  assert (G : forall n, callee_saved n -> reg_get regs' (Z_to_bv 5 n) =
     getr (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          (Z_to_bv 5 n)).
  { intros n Hn. rewrite c2r_reg_get_getr by (unfold callee_saved in Hn; lia). apply H, Hn. }
  f_equal.
  all: lazymatch goal with
       | |- reg_get ?R ?k = _ =>
           let z := eval vm_compute in (bv_unsigned k) in
           transitivity (reg_get R (Z_to_bv 5 z)); [reflexivity|];
           rewrite (G z ltac:(unfold callee_saved; lia)); reflexivity
       end.
Qed.

Lemma c2r_getr_canon : forall (regs : bvmap 5 word) (r : reg), getr regs r = getr (mkR_of regs) r.
Proof.
  intros regs r. unfold getr. destruct (bv_eqb r 0) eqn:E; [reflexivity|].
  apply mkR_of_eqv. unfold is_x0. apply Z.eqb_neq. intros H0.
  assert (r = 0%bv) by (apply bv_eq; rewrite H0; reflexivity). subst r.
  rewrite bv_eqb_refl in E. discriminate.
Qed.

(* a call of a `leaf` callee inside a walk whose post holds up to ms_eqv *)
Lemma c2r_call : forall (pc K : Z) Pre Wr Post (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  leaf pc K Pre Wr Post ->
  Pre (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) m ->
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo + K <= bv_unsigned sp -> bv_unsigned sp < 2 ^ 63 ->
  (forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
     (exists regs' : bvmap 5 word,
        (forall r, getr regs' r =
           getr (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') r) /\
        Post (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             m regs' m') ->
     munch ((bv_unsigned sp - K, bv_unsigned sp)
            :: Wr (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) m)
           m m' ->
     wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
     evt rsegs (eqv_cl Q)
       (MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
           F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs (eqv_cl Q)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Proof.
  intros pc K Pre Wr Post Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 F fc m lo HL HP MI ST LO SP KC.
  eapply evt_cut; [exact (HL _ F fc m lo HP MI ST LO SP)|].
  intros ms' (regs' & m' & -> & RP & MU & WM & MI' & ST' & PO).
  set (R0 := mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) in *.
  pose proof (c2r_mkR_of_preserved ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3 t4 t5 t6 regs' RP) as EC.
  assert (EQ : ms_eqv (MS (mkR_of regs') F (ret_pc (getr R0 1)) fc None m' (seg_rom rsegs))
                      (MS regs' F (ret_pc (getr R0 1)) fc None m' (seg_rom rsegs))).
  { split; [apply xregs_eqv_sym, mkR_of_eqv|]. repeat split; reflexivity. }
  eapply c2r_evt_eqv_transport; [exact EQ|].
  rewrite EC. change (getr R0 1) with ra.
  apply KC; [| exact MU | exact WM | exact MI' | exact ST'].
  exists regs'. split; [| exact PO].
  intros r. rewrite (c2r_getr_canon regs' r), EC. reflexivity.
Qed.

(* the end of a piece: the post holds of the state reached *)
Lemma c2r_fin : forall (Q : machine_state -> Prop) S hp m0 c, Q c -> seg_fp S hp m0 (ms_mem c) ->
  evt rsegs (eqv_cl (fun c => Q c /\ seg_fp S hp m0 (ms_mem c))) c.
Proof. intros Q S hp m0 c H1 H2. apply evt_done. exists c. split; [split; assumption | apply c2_ms_eqv_refl]. Qed.
