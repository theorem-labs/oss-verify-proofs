(* Arm c2 (op_mark), piece B (LC2B.v: c2_13db0 -> the loop head of operation i + 1, or the exit): the pure
   facts its walk uses, and the transport of the loop head's memory across the frames of check_marks and
   check_requests ([S - 528, S - 480), below the slot's frame at S - 480).

   1. The model and the library on the same inputs (no request owed): the same marks, the same requests,
      and same_rc of the two codes; the library's code is an int32.
   2. requests_are / marks_are from the equal lists and the well-formedness of the blocks.
   3. Where the slot's pieces lie (lenv_ok), with apart_gnl of the model block.
   4. The memory of the loop head, the frame and task_mem across a write to [S - 528, S - 480). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem printf_facts_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC2Defs.
Local Open Scope Z_scope.

(* ==========================================================================
   1. The model and the library
   ========================================================================== *)

Lemma c2b_sent_nil : forall kbs, nk_n_sent kbs = 0 -> nk_sent kbs = [].
Proof. intros kbs H. unfold nk_sent. rewrite H. reflexivity. Qed.

Lemma c2b_same_rc_refl : forall x, same_rc x x = true.
Proof.
  intros x. unfold same_rc. destruct (Z.eqb_spec x RC_FAILS) as [->|_].
  - reflexivity.
  - apply Z.eqb_refl.
Qed.

Lemma c2b_norm_zero : forall rc, (norm_rc rc =? 0) = (rc =? 0).
Proof.
  intros rc. unfold norm_rc. destruct (Z.ltb_spec 0 rc) as [H|H]; [|reflexivity].
  unfold RC_FAILS. destruct (Z.eqb_spec rc 0) as [E|E]; [lia | reflexivity].
Qed.

Lemma c2b_agree : forall tab nm marks reqs K,
  same_rc (m_rc (mark_lib tab nm marks reqs K)) (m_rc (mmark tab nm marks reqs K)) = true /\
  m_marks (mark_lib tab nm marks reqs K) = m_marks (mmark tab nm marks reqs K) /\
  m_reqs (mark_lib tab nm marks reqs K) = m_reqs (mmark tab nm marks reqs K).
Proof.
  intros tab nm marks reqs K.
  unfold mark_lib, mark_core, mmark, read_model, write_model.
  destruct nm as [s|]; cbv beta iota zeta.
  2: { cbn [m_rc m_marks m_reqs]. split; [apply c2b_same_rc_refl | split; reflexivity]. }
  destruct (Nat.eqb (length s) 0).
  { cbn [m_rc m_marks m_reqs]. split; [apply c2b_same_rc_refl | split; reflexivity]. }
  destruct (read_core tab (Some s) KIND_CAP ALIAS_MAX reqs K) as [rc kd al rq st].
  cbn [r_rc r_kind r_alias r_reqs r_state].
  rewrite c2b_norm_zero.
  destruct (rc =? 0).
  2: { cbn [negb m_rc m_marks m_reqs]. split; [apply same_rc_norm | split; reflexivity]. }
  cbn [negb].
  destruct (decide (Some kd) (Some al) =? V_MARK).
  - destruct (write_core tab (Some s) (Some S_SERVED) rq st) as [wrc wrq wst].
    cbn [w_rc w_reqs w_state].
    rewrite c2b_norm_zero.
    destruct (wrc =? 0); cbn [negb m_rc m_marks m_reqs].
    + split; [apply c2b_same_rc_refl | split; reflexivity].
    + split; [apply same_rc_norm | split; reflexivity].
  - match goal with |- context [if ?b then _ else _] => destruct b end;
      cbn [m_rc m_marks m_reqs]; (split; [apply c2b_same_rc_refl | split; reflexivity]).
Qed.

(* the three errnos of an exchange are below 2^31 (nlk_wf) *)
Definition c2b_kb (K : kstate) : Prop :=
  0 <= k_sock K < 2 ^ 31 /\ 0 <= k_send K < 2 ^ 31 /\ 0 <= k_end K < 2 ^ 31.

Lemma c2b_rd32s_range : forall c off, - 2 ^ 31 <= rd32s c off < 2 ^ 31.
Proof.
  intros c off. unfold rd32s, rd32, rdn, slice. cbv zeta.
  set (l := firstn (Z.to_nat 4) (skipn (Z.to_nat off) c)).
  pose proof (bytes_le_to_Z_nonneg l) as H0. pose proof (bytes_le_to_Z_bound l) as H1.
  assert (HL : (length l <= 4)%nat) by (unfold l; rewrite length_firstn; lia).
  assert (HP : 2 ^ (8 * Z.of_nat (length l)) <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
  destruct (Z.ltb_spec (bytes_le_to_Z l) (2 ^ 31)); lia.
Qed.

Lemma c2b_msg_range : forall fuel c off left,
  match msg_scan fuel c off left with NlErr code => - 2 ^ 31 <= code < 2 ^ 31 | _ => True end.
Proof.
  induction fuel as [|f IH]; intros c off left; cbn [msg_scan]; [exact I|].
  repeat match goal with
         | |- context [if ?b then _ else _] =>
             lazymatch b with true => fail | false => fail | _ => destruct b end
         end;
    cbv beta iota;
    first [ exact I | exact (c2b_rd32s_range _ _) | apply IH ].
Qed.

Lemma c2b_loop_range : forall fuel cs i,
  match fst (chunk_loop fuel cs i) with NlErr code => - 2 ^ 31 <= code < 2 ^ 31 | _ => True end.
Proof.
  induction fuel as [|f IH]; intros cs i; cbn [chunk_loop]; [exact I|].
  destruct (nth_error cs i) as [c|]; [|exact I].
  pose proof (c2b_msg_range (S (length c)) c 0 (Z.of_nat (length c))) as H.
  unfold chunk_walk.
  destruct (msg_scan (S (length c)) c 0 (Z.of_nat (length c))) as [| |code|a]; cbn [fst];
    [apply IH | exact I | exact H | exact I].
Qed.

Lemma c2b_talk_range : forall K, c2b_kb K ->
  - 2 ^ 31 <= talk_rc_lib K < 2 ^ 31 /\ c2b_kb (talk_after K).
Proof.
  intros [ch nx en so se] (Hso & Hse & Hen). cbn [k_sock k_send k_end] in Hso, Hse, Hen.
  unfold talk_rc_lib, talk_after, talk_core, c2b_kb. cbn [k_sock k_send k_end k_chunks k_next].
  destruct (negb (so =? 0)).
  { cbn [fst snd k_sock k_send k_end]. lia. }
  destruct (negb (se =? 0)).
  { cbn [fst snd k_sock k_send k_end]. lia. }
  pose proof (c2b_loop_range (S (length ch)) ch nx) as H.
  destruct (chunk_loop (S (length ch)) ch nx) as [v j]. cbn [fst] in H.
  destruct v as [| |code|a]; cbn [fst snd k_sock k_send k_end]; try unfold E_IO; lia.
Qed.

Lemma c2b_read_range : forall tab nm kc ac reqs K, c2b_kb K ->
  - 2 ^ 31 <= r_rc (read_core tab nm kc ac reqs K) < 2 ^ 31 /\
  c2b_kb (r_state (read_core tab nm kc ac reqs K)).
Proof.
  intros tab nm kc ac reqs K HK. unfold read_core.
  destruct nm as [s|]; cbv beta iota zeta.
  2: { cbn [r_rc r_state]. unfold E_INVAL. split; [lia | exact HK]. }
  destruct (Nat.eqb (length s) 0).
  { cbn [r_rc r_state]. unfold E_INVAL. split; [lia | exact HK]. }
  destruct (index_of tab s =? 0).
  { cbn [r_rc r_state]. unfold E_NODEV. split; [lia | exact HK]. }
  cbn [r_rc r_state]. exact (c2b_talk_range K HK).
Qed.

Lemma c2b_write_range : forall tab nm al reqs K, c2b_kb K ->
  - 2 ^ 31 <= w_rc (write_core tab nm al reqs K) < 2 ^ 31.
Proof.
  intros tab nm al reqs K HK. unfold write_core.
  destruct nm as [s|]; [destruct al as [a|]|]; cbv beta iota zeta.
  3: { cbn [w_rc]. unfold E_INVAL. lia. }
  2: { cbn [w_rc]. unfold E_INVAL. lia. }
  destruct (Nat.eqb (length s) 0); [cbn [w_rc]; unfold E_INVAL; lia|].
  destruct (ALIAS_MAX <=? Z.of_nat (length a)); [cbn [w_rc]; unfold E_NAMETOOLONG; lia|].
  destruct (index_of tab s =? 0); [cbn [w_rc]; unfold E_NODEV; lia|].
  cbn [w_rc]. exact (proj1 (c2b_talk_range K HK)).
Qed.

Lemma c2b_mark_range : forall tab nm marks reqs K, c2b_kb K ->
  - 2 ^ 31 <= m_rc (mark_core tab nm marks reqs K) < 2 ^ 31.
Proof.
  intros tab nm marks reqs K HK.
  pose proof (c2b_read_range tab nm KIND_CAP ALIAS_MAX reqs K HK) as [R1 R2].
  unfold mark_core.
  destruct nm as [s|]; cbv beta iota zeta.
  2: { cbn [m_rc]. unfold E_INVAL. lia. }
  destruct (Nat.eqb (length s) 0).
  { cbn [m_rc]. unfold E_INVAL. lia. }
  destruct (read_core tab (Some s) KIND_CAP ALIAS_MAX reqs K) as [rc kd al rq st].
  cbn [r_rc r_kind r_alias r_reqs r_state] in *.
  pose proof (decide_range (Some kd) (Some al)) as DR. unfold V_MARK, V_LEAVE_HOST in DR.
  destruct (negb (rc =? 0)); [cbn [m_rc]; exact R1|].
  destruct (decide (Some kd) (Some al) =? V_MARK).
  - pose proof (c2b_write_range tab (Some s) (Some S_SERVED) rq st R2) as W.
    destruct (write_core tab (Some s) (Some S_SERVED) rq st) as [wrc wrq wst].
    cbn [w_rc w_reqs w_state] in W |- *.
    destruct (negb (wrc =? 0)); cbn [m_rc]; lia.
  - match goal with |- context [if ?b then _ else _] => destruct b end; cbn [m_rc]; lia.
Qed.

(* check_mark's premise over the two words: same_rc and the int32 range of the library's code *)
Lemma c2b_rc_regs : forall x y, same_rc x y = true -> - 2 ^ 31 <= x < 2 ^ 31 ->
  (Z_to_bv 64 y = Z_to_bv 64 RC_FAILS -> Z_to_bv 64 x <> Z_to_bv 64 0) /\
  (Z_to_bv 64 y <> Z_to_bv 64 RC_FAILS -> Z_to_bv 64 x = Z_to_bv 64 y).
Proof.
  intros x y HS HR. revert HS. unfold same_rc.
  destruct (Z.eqb_spec y RC_FAILS) as [E|E]; intros HS.
  - split.
    + intros _ H0. apply negb_true_iff, Z.eqb_neq in HS. apply HS.
      apply (f_equal bv_unsigned) in H0. rewrite !unsigned_lit_wrap in H0.
      Z.div_mod_to_equations. lia.
    + intros H1. exfalso. apply H1. rewrite E. reflexivity.
  - apply Z.eqb_eq in HS. subst x. split.
    + intros H1 H0. rewrite H1 in H0. apply (f_equal bv_unsigned) in H0.
      rewrite !unsigned_lit_wrap in H0. unfold RC_FAILS in H0. Z.div_mod_to_equations. lia.
    + intros _. reflexivity.
Qed.

(* ==========================================================================
   2. requests_are and marks_are
   ========================================================================== *)

Lemma c2b_nth_map_seq : forall (g : nat -> list byte) n k, (k < n)%nat ->
  nth k (map g (seq 0 n)) [] = g k.
Proof.
  intros g n k Hk.
  rewrite nth_indep with (d' := g 0%nat) by (rewrite length_map, length_seq; exact Hk).
  rewrite map_nth, seq_nth by exact Hk. reflexivity.
Qed.

Lemma c2b_slice_len : forall bs off n, 0 <= off -> 0 <= n -> off + n <= Z.of_nat (length bs) ->
  Z.of_nat (length (slice bs off n)) = n.
Proof. intros bs off n H1 H2 H3. unfold slice. rewrite length_firstn, length_skipn. lia. Qed.

Lemma c2b_requests_are : forall kbs mbs,
  nk_sent kbs = md_reqs mbs -> nlk_wf kbs -> model_wf mbs ->
  Z.of_nat (length kbs) = NK_SIZE -> Z.of_nat (length mbs) = MD_SIZE ->
  requests_are kbs mbs.
Proof.
  intros kbs mbs EQ KW MW LK LM.
  destruct KW as (_ & _ & KS & _ & _ & _ & _ & _ & _ & _ & _ & _ & KL).
  destruct MW as (MS & _ & _ & _ & ML & _).
  assert (LN : Z.of_nat (length (nk_sent kbs)) = nk_n_sent kbs)
    by (unfold nk_sent; rewrite length_map, length_seq; lia).
  assert (LD : Z.of_nat (length (md_reqs mbs)) = md_n_req mbs)
    by (unfold md_reqs; rewrite length_map, length_seq; lia).
  assert (EN : nk_n_sent kbs = md_n_req mbs) by (rewrite <- LN, <- LD, EQ; reflexivity).
  split; [exact EN|].
  intros i Hi.
  assert (E1 : nk_sent_one kbs i = md_req_one mbs i).
  { assert (A : nth (Z.to_nat i) (nk_sent kbs) [] = nk_sent_one kbs i).
    { unfold nk_sent. rewrite c2b_nth_map_seq by lia. cbv beta. rewrite Z2Nat.id by lia. reflexivity. }
    assert (B : nth (Z.to_nat i) (md_reqs mbs) [] = md_req_one mbs i).
    { unfold md_reqs. rewrite c2b_nth_map_seq by lia. cbv beta. rewrite Z2Nat.id by lia. reflexivity. }
    rewrite <- A, <- B, EQ. reflexivity. }
  split; [|exact E1].
  specialize (KL i Hi). specialize (ML i ltac:(lia)).
  unfold NK_SENT_LEN, MD_REQ_LEN, NL_SENT_LEN, NL_SENT_MAX, NK_SIZE, MD_SIZE in *.
  assert (A1 : Z.of_nat (length (nk_sent_one kbs i)) = fld_u64 kbs (270888 + 8 * i)).
  { unfold nk_sent_one, NK_SENT, NK_SENT_LEN, NL_SENT_LEN. apply c2b_slice_len; lia. }
  assert (A2 : Z.of_nat (length (md_req_one mbs i)) = fld_u64 mbs (8208 + 8 * i)).
  { unfold md_req_one, MD_REQ, MD_REQ_LEN, NL_SENT_LEN. apply c2b_slice_len; lia. }
  rewrite <- A1, <- A2, E1. reflexivity.
Qed.

Lemma c2b_md_marks_len : forall mbs, 0 <= md_n_mark mbs ->
  Z.of_nat (length (md_marks mbs)) = md_n_mark mbs.
Proof. intros mbs H. unfold md_marks. rewrite length_map, length_seq. lia. Qed.

Lemma c2b_marks_are : forall gbs mbs l,
  mk_names gbs = l -> mk_n gbs = Z.of_nat (length l) -> md_marks mbs = l -> model_wf mbs ->
  marks_are gbs mbs.
Proof.
  intros gbs mbs l H1 H2 H3 HW. destruct HW as (_ & _ & _ & _ & _ & (HN & _)).
  split.
  - rewrite H2, <- H3. apply c2b_md_marks_len. lia.
  - rewrite H1, H3. reflexivity.
Qed.

(* ==========================================================================
   3. Where the slot's pieces lie
   ========================================================================== *)

Definition c2b_ivs (l : list (word * word)) : list (Z * Z) :=
  map (fun s => (bv_unsigned (fst s), bv_unsigned (fst s) + bv_unsigned (snd s))) l.

Fixpoint c2b_cov (L : list (Z * Z)) (cur : Z) : Z :=
  match L with [] => cur | (a, b) :: L' => c2b_cov L' (if a <=? cur then Z.max cur b else cur) end.

Lemma c2b_cov_in : forall L cur x, cur <= x < c2b_cov L cur -> exists a b, In (a, b) L /\ a <= x < b.
Proof.
  induction L as [|[a b] L IH]; intros cur x Hx; cbn [c2b_cov] in Hx; [lia|].
  revert Hx. destruct (a <=? cur) eqn:E; intros Hx.
  - apply Z.leb_le in E. destruct (Z.lt_ge_cases x (Z.max cur b)) as [H|H].
    + exists a, b. split; [left; reflexivity | lia].
    + destruct (IH (Z.max cur b) x ltac:(lia)) as (a' & b' & Hin & Hab). exists a', b'.
      split; [right; exact Hin | exact Hab].
  - destruct (IH cur x Hx) as (a' & b' & Hin & Hab). exists a', b'. split; [right; exact Hin | exact Hab].
Qed.

(* the end of the image's reserved pages that start at 0x10000 without a gap *)
Definition c2b_PAGES : Z := Eval vm_compute in c2b_cov (c2b_ivs (segments_reserved rsegs)) 0x10000.

Lemma c2b_pages_eq : c2b_cov (c2b_ivs (segments_reserved rsegs)) 0x10000 = c2b_PAGES.
Proof. vm_compute. reflexivity. Qed.

Lemma c2b_img_free_bound : forall D n, 0 <= D -> 0 < n -> pf_img_free D n ->
  D + n <= 0x10000 \/ c2b_PAGES <= D.
Proof.
  intros D n HD Hn F.
  assert (C : forall x, 0x10000 <= x < c2b_PAGES -> exists s, In s (segments_reserved rsegs)
                /\ bv_unsigned (fst s) <= x < bv_unsigned (fst s) + bv_unsigned (snd s)).
  { intros x Hx. rewrite <- c2b_pages_eq in Hx. destruct (c2b_cov_in _ _ _ Hx) as (a & b & Hin & Hab).
    unfold c2b_ivs in Hin. apply in_map_iff in Hin. destruct Hin as (s & Es & Hs). injection Es as Ea Eb.
    exists s. split; [exact Hs | lia]. }
  assert (PL : 0x10000 < c2b_PAGES) by (vm_compute; reflexivity).
  destruct (Z.lt_ge_cases D 0x10000) as [H1|H1].
  - destruct (Z.le_gt_cases (D + n) 0x10000) as [H2|H2]; [left; exact H2|].
    destruct (C 0x10000 ltac:(lia)) as (s & Hs & Hx). exfalso.
    apply (F (0x10000 - D) ltac:(lia) s Hs). replace (D + (0x10000 - D)) with 0x10000 by lia. exact Hx.
  - destruct (Z.lt_ge_cases D c2b_PAGES) as [H2|H2]; [|right; exact H2].
    destruct (C D ltac:(lia)) as (s & Hs & Hx). exfalso.
    apply (F 0 ltac:(lia) s Hs). rewrite Z.add_0_r. exact Hx.
Qed.

Lemma c2b_gnl_pages : A_G_NL + NK_SIZE <= c2b_PAGES.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma c2b_env : forall E, lenv_ok E ->
  0x960e0 + 65536 <= e_S E <= 2 ^ 47 /\
  4096 <= e_md E /\ e_md E + 8856 <= e_S E - 65536 /\
  4096 <= e_mk E /\ e_mk E + 516 <= e_S E - 65536 /\
  0 <= e_p0 E /\ e_p0 E + Z.of_nat (length (e_pl E)) <= e_S E - 65536 /\
  1 <= Z.of_nat (length (e_pl E)) < 2 ^ 26 /\
  apart_gnl (e_md E) MD_SIZE.
Proof.
  intros E (H1 & H2 & H3 & (M1 & M2 & M3) & (K1 & K2 & K3) & H6 & H7 & H8 & H9 & (P1 & P2 & P3)
            & H11 & H12 & H13).
  clear H3 H6 H7 H8 H11 H12 H13.
  unfold SLOT_STACK_Z, MD_SIZE, MK_SIZE in *.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [lia|]. split; [lia|]. split; [lia|].
  unfold apart_gnl, MD_SIZE.
  destruct (c2b_img_free_bound (e_md E) 8856 ltac:(lia) ltac:(lia) M3) as [B|B].
  - left. unfold A_G_NL. lia.
  - right. pose proof c2b_gnl_pages. lia.
Qed.

(* ==========================================================================
   4. The loop head's memory across a write to [S - 528, S - 480)
   ========================================================================== *)

(* the loop head's memory (lh_mem) without the frame, whose cursor cell the caller fixes *)
Definition c2b_rest (E : lenv) (i P N : Z) (kbs mbs gbs : list byte) (m : word -> option byte) : Prop :=
  bytes_at rsegs m (e_S E - 104) (e_saved E) /\
  nlk_at m kbs /\ nlk_wf kbs /\ iftab_at m kbs link_tab /\
  nk_open kbs = 0 /\ nk_misuse kbs = 0 /\ nk_opened kbs = nk_closed kbs /\ nk_opened kbs <= 64 * i /\
  gnames_at m /\ odd_at m /\ policy_ro m /\
  la_ok m /\ texts_at m /\ ifptrs_at m /\
  model_at m (e_md E) mbs /\ model_wf mbs /\
  marks_at m (e_mk E) gbs /\ marks_wf gbs /\ marks_are gbs mbs /\
  cursor_ok m (e_p0 E) (e_pl E) P N /\
  wr_at rsegs m A_ERRNO 4 /\ guard_m m.

Lemma c2b_rest_N : forall E i P N kbs mbs gbs m, lenv_ok E ->
  c2b_rest E i P N kbs mbs gbs m -> 0 <= N < 2 ^ 26.
Proof.
  intros E i P N kbs mbs gbs m HE R.
  destruct (c2b_env E HE) as (_ & _ & _ & _ & _ & _ & _ & HL & _).
  unfold c2b_rest in R.
  destruct R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                 & (_ & k & Hk & _ & HN) & _ & _).
  lia.
Qed.

Lemma c2b_rest_ex : forall E i P N kbs mbs gbs m, c2b_rest E i P N kbs mbs gbs m ->
  bytes_at rsegs m (e_S E - 104) (e_saved E) /\ wr_at rsegs m A_ERRNO 4 /\ guard_m m.
Proof.
  intros E i P N kbs mbs gbs m R. unfold c2b_rest in R.
  destruct R as (SV & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ER & GD).
  split; [exact SV | split; [exact ER | exact GD]].
Qed.

Lemma c2b_rest_la : forall E i P N kbs mbs gbs m, c2b_rest E i P N kbs mbs gbs m -> la_ok m.
Proof.
  intros E i P N kbs mbs gbs m R. unfold c2b_rest in R.
  destruct R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LA & _). exact LA.
Qed.

Definition c2b_W (S : Z) : list ivl := [(S - 528, S - 480)].

Lemma c2b_bytes_tr : forall S m m' a bs, munch (c2b_W S) m m' ->
  a + Z.of_nat (length bs) <= S - 528 \/ S - 480 <= a ->
  bytes_at rsegs m a bs -> bytes_at rsegs m' a bs.
Proof.
  intros S m m' a bs MU H B. eapply bytes_at_transport; [exact B | exact MU |].
  unfold c2b_W. cbn [disjoint_from]. split; [exact H | exact I].
Qed.

Lemma c2b_rw_tr : forall S m m' a cs, munch (c2b_W S) m m' -> wmono rsegs m m' ->
  a + Z.of_nat (cells_size cs) <= S - 528 \/ S - 480 <= a ->
  rw_cells rsegs m a cs -> rw_cells rsegs m' a cs.
Proof.
  intros S m m' a cs MU WM H R. eapply rw_cells_transport; [exact R | exact MU | exact WM |].
  unfold c2b_W. cbn [disjoint_from]. split; [exact H | exact I].
Qed.

Lemma c2b_u8arr_tr : forall S m m' a bs, munch (c2b_W S) m m' -> wmono rsegs m m' ->
  a + Z.of_nat (length bs) <= S - 528 ->
  u8arr rsegs m a bs -> u8arr rsegs m' a bs.
Proof.
  intros S m m' a bs MU WM H [B W]. split.
  - eapply c2b_bytes_tr; [exact MU | left; exact H | exact B].
  - eapply wr_at_transport; [exact W | exact WM].
Qed.

(* the pointers g_nl.if_name[] holds and the names of link_tab *)
Lemma c2b_ptrs_low : forall i, 0 <= nth i link_ptrs 0 <= 0x743f0.
Proof.
  intros i.
  assert (H : forallb (fun x => (0 <=? x) && (x <=? 0x743f0)) link_ptrs = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. destruct (Nat.lt_ge_cases i (length link_ptrs)) as [L|L].
  - assert (Hin : In (nth i link_ptrs 0) link_ptrs) by (apply nth_In; exact L).
    specialize (H _ Hin). apply andb_true_iff in H as [H1 H2].
    apply Z.leb_le in H1, H2. lia.
  - rewrite nth_overflow by exact L. lia.
Qed.

Lemma c2b_tab_short : forall i nm ix, nth_error link_tab i = Some (nm, ix) -> (length nm <= 11)%nat.
Proof.
  intros i nm ix H.
  assert (A : forallb (fun e => Nat.leb (length (fst e)) 11) link_tab = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in A. apply nth_error_In in H. specialize (A _ H). cbn [fst] in A.
  apply Nat.leb_le in A. exact A.
Qed.

Lemma c2b_odd_low : forall i, (i < 6)%nat ->
  nth i odd_ptrs 0 + Z.of_nat (length (nth i odd_strs [])) + 1 <= 0x960e0.
Proof.
  intros i Hi. do 6 (destruct i as [|i]; [apply Z.leb_le; vm_compute; reflexivity|]). lia.
Qed.

Lemma c2b_bytes_det : forall (mm : word -> option byte) a l1 l2,
  bytes_at rsegs mm a l1 -> bytes_at rsegs mm a l2 -> length l1 = length l2 -> l1 = l2.
Proof.
  intros mm a l1 l2 (_ & _ & H1) (_ & _ & H2) L.
  apply nth_ext with (d := zb 0) (d' := zb 0); [exact L|].
  intros k Hk. specialize (H1 k Hk). specialize (H2 k ltac:(lia)). rewrite H1 in H2.
  rewrite nth_error_nth' with (d := zb 0) in H2 by lia.
  rewrite nth_error_nth' with (d := zb 0) in H2 by lia.
  injection H2 as E. exact E.
Qed.

Lemma c2b_u64_det : forall (mm : word -> option byte) a p q, u64_at mm a p -> u64_at mm a q ->
  0 <= p < 2 ^ 64 -> 0 <= q < 2 ^ 64 -> p = q.
Proof.
  intros mm a p q Hp Hq Rp Rq. unfold u64_at in Hp, Hq.
  assert (E : le8 (wz p) = le8 (wz q))
    by (eapply c2b_bytes_det; [exact Hp | exact Hq | rewrite !length_le8; reflexivity]).
  apply (f_equal le_bytes_to_word) in E. rewrite !le_bytes_to_word_le8 in E.
  apply (f_equal bv_unsigned) in E. unfold wz in E. rewrite !unsigned_lit in E by lia. exact E.
Qed.

Section Tr.
Variables (S : Z) (m m' : word -> option byte).
Hypothesis HS : 0x960e0 + 65536 <= S.
Hypothesis MU : munch (c2b_W S) m m'.
Hypothesis WM : wmono rsegs m m'.

Lemma c2b_lo_bytes : forall a bs, a + Z.of_nat (length bs) <= 0x960e0 ->
  bytes_at rsegs m a bs -> bytes_at rsegs m' a bs.
Proof using HS MU WM. intros a bs H B. eapply c2b_bytes_tr; [exact MU | left; lia | exact B]. Qed.

Lemma c2b_lo_u64 : forall a v, a + 8 <= 0x960e0 -> u64_at m a v -> u64_at m' a v.
Proof using HS MU WM. intros a v H B. apply c2b_lo_bytes; [rewrite length_le8; lia | exact B]. Qed.

Lemma c2b_lo_u32 : forall a v, a + 4 <= 0x960e0 -> u32_at m a v -> u32_at m' a v.
Proof using HS MU WM. intros a v H B. apply c2b_lo_bytes; [rewrite length_le4; lia | exact B]. Qed.

Lemma c2b_lo_cstr : forall a s, a + Z.of_nat (length s) + 1 <= 0x960e0 -> cstr_at m a s -> cstr_at m' a s.
Proof using HS MU WM.
  intros a s H [B N]. split; [|exact N].
  apply c2b_lo_bytes; [rewrite length_app; cbn [length]; lia | exact B].
Qed.

Lemma c2b_gnames_tr : gnames_at m -> gnames_at m'.
Proof using HS MU WM.
  intros G k Hk. destruct (G k Hk) as (rest & B & L). exists rest. split; [|exact L].
  apply c2b_lo_bytes; [rewrite L; unfold A_G_NAMES; lia | exact B].
Qed.

Lemma c2b_odd_tr : odd_at m -> odd_at m'.
Proof using HS MU WM.
  intros O i Hi. destruct (O i Hi) as [U C]. split.
  - apply c2b_lo_u64; [unfold A_ODD; lia | exact U].
  - apply c2b_lo_cstr; [apply c2b_odd_low; exact Hi | exact C].
Qed.

Lemma c2b_policy_tr : policy_ro m -> policy_ro m'.
Proof using HS MU WM.
  intros (P1 & P2 & P3 & P4).
  split; [|split; [|split]]; apply c2b_lo_cstr; try assumption;
    apply Z.leb_le; vm_compute; reflexivity.
Qed.

Lemma c2b_la_tr : la_ok m -> la_ok m'.
Proof using HS MU WM.
  intros (la & sl & R & B & L). exists la, sl. split; [|split; [|exact L]].
  - eapply c2b_rw_tr; [exact MU | exact WM | left | exact R].
    assert (Z.of_nat (cells_size [CB (Z.to_nat 300) la; C1 (zb 0)]) = 301) by reflexivity.
    unfold A_LONG_ALIAS. lia.
  - apply c2b_lo_bytes; [rewrite L; unfold A_LONG_ALIAS, LONG_ALIAS_SIZE; lia | exact B].
Qed.

Lemma c2b_texts_tr : texts_at m -> texts_at m'.
Proof using HS MU WM. intros T i Hi. apply c2b_lo_u64; [unfold A_TEXTS; lia | exact (T i Hi)]. Qed.

Lemma c2b_ifptrs_tr : ifptrs_at m -> ifptrs_at m'.
Proof using HS MU WM. intros T i Hi. apply c2b_lo_u64; [unfold A_G_NL, NK_IF_NAME; lia | exact (T i Hi)]. Qed.

Lemma c2b_nlk_tr : forall kbs, nlk_at m kbs -> nlk_at m' kbs.
Proof using HS MU WM.
  intros kbs [A L]. split; [|exact L].
  eapply c2b_u8arr_tr; [exact MU | exact WM | | exact A]. rewrite L. unfold A_G_NL, NK_SIZE. lia.
Qed.

Lemma c2b_blk_tr : forall a bs, a + Z.of_nat (length bs) <= S - 65536 ->
  u8arr rsegs m a bs -> u8arr rsegs m' a bs.
Proof using HS MU WM. intros a bs H A. eapply c2b_u8arr_tr; [exact MU | exact WM | lia | exact A]. Qed.

Lemma c2b_model_tr : forall a bs, a + MD_SIZE <= S - 65536 -> model_at m a bs -> model_at m' a bs.
Proof using HS MU WM. intros a bs H [A L]. split; [|exact L]. apply c2b_blk_tr; [lia | exact A]. Qed.

Lemma c2b_marks_tr : forall a bs, a + MK_SIZE <= S - 65536 -> marks_at m a bs -> marks_at m' a bs.
Proof using HS MU WM. intros a bs H [A L]. split; [|exact L]. apply c2b_blk_tr; [lia | exact A]. Qed.

Lemma c2b_iftab_tr : forall kbs, ifptrs_at m -> iftab_at m kbs link_tab -> iftab_at m' kbs link_tab.
Proof using HS MU WM.
  intros kbs IP (HN & HL & HT). split; [exact HN|]. split; [exact HL|].
  intros i nm ix Hi. destruct (HT i nm ix Hi) as (Hix & p & U & Hp & C & U4). split; [exact Hix|].
  assert (Li : (i < length link_tab)%nat) by (apply nth_error_Some; congruence).
  assert (L64 : length link_tab = 64%nat) by (vm_compute; reflexivity).
  assert (Rp : 0 <= p < 2 ^ 64).
  { destruct C as [(B0 & B1 & _) _]. rewrite length_app in B1. cbn [length] in B1. lia. }
  pose proof (c2b_ptrs_low i) as Rq.
  assert (Ep : p = nth i link_ptrs 0).
  { apply (c2b_u64_det m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i)); [exact U | apply IP; lia | exact Rp | lia]. }
  pose proof (c2b_tab_short i nm ix Hi) as Hs.
  exists p. split; [apply c2b_lo_u64; [unfold A_G_NL, NK_IF_NAME; lia | exact U]|].
  split; [exact Hp|]. split.
  - apply c2b_lo_cstr; [lia | exact C].
  - apply c2b_lo_u32; [unfold A_G_NL, NK_IF_INDEX; lia | exact U4].
Qed.

Lemma c2b_guard_tr : guard_m m -> guard_m m'.
Proof using HS MU WM.
  intros (G1 & c & G2). split.
  - apply c2b_lo_bytes; [rewrite length_le8; unfold A_GOT_GUARD_S; lia | exact G1].
  - exists c. apply c2b_lo_bytes; [rewrite length_le8; unfold A_GUARD_S; lia | exact G2].
Qed.

Lemma c2b_cursor_tr : forall p0 pl P N, p0 + Z.of_nat (length pl) <= S - 65536 ->
  cursor_ok m p0 pl P N -> cursor_ok m' p0 pl P N.
Proof using HS MU WM.
  intros p0 pl P N H (B & K). split; [|exact K]. eapply c2b_bytes_tr; [exact MU | left; lia | exact B].
Qed.

Lemma c2b_rest_tr : forall E i P N kbs mbs gbs, e_S E = S -> lenv_ok E ->
  c2b_rest E i P N kbs mbs gbs m -> c2b_rest E i P N kbs mbs gbs m'.
Proof using HS MU WM.
  intros E i P N kbs mbs gbs ES HE R.
  destruct (c2b_env E HE) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9).
  rewrite ES in *.
  unfold c2b_rest in R |- *.
  destruct R as (SV & KA & KW & IF & KO & KM & KOC & KOB & GN & OD & PR & LA & TX & IP & MA & MW
                 & GA & GW & GR & CU & ER & GD).
  refine (conj _ (conj _ (conj KW (conj _ (conj KO (conj KM (conj KOC (conj KOB (conj _ (conj _
    (conj _ (conj _ (conj _ (conj _ (conj _ (conj MW (conj _ (conj GW (conj GR (conj _
    (conj _ _))))))))))))))))))))).
  - eapply c2b_bytes_tr; [exact MU | right; lia | exact SV].
  - apply c2b_nlk_tr; exact KA.
  - apply c2b_iftab_tr; [exact IP | exact IF].
  - apply c2b_gnames_tr; exact GN.
  - apply c2b_odd_tr; exact OD.
  - apply c2b_policy_tr; exact PR.
  - apply c2b_la_tr; exact LA.
  - apply c2b_texts_tr; exact TX.
  - apply c2b_ifptrs_tr; exact IP.
  - apply c2b_model_tr; [unfold MD_SIZE; lia | exact MA].
  - apply c2b_marks_tr; [unfold MK_SIZE; lia | exact GA].
  - apply c2b_cursor_tr; [lia | exact CU].
  - eapply wr_at_transport; [exact ER | exact WM].
  - apply c2b_guard_tr; exact GD.
Qed.

Lemma c2b_frame_tr : forall E P N j0 j1 j2, e_S E = S ->
  c2_frame E P N j0 j1 j2 m -> c2_frame E P N j0 j1 j2 m'.
Proof using HS MU WM.
  intros E P N j0 j1 j2 ES F. unfold c2_frame in *. rewrite ES in *.
  eapply c2b_rw_tr; [exact MU | exact WM | right; unfold SLOT_FRAME; lia | exact F].
Qed.

(* task_mem: the bytes of the window were already there (stk), so each is in a segment or below
   TASK_SIZE by task_mem of m *)
Lemma c2b_task_tr : MemNorm.task_mem rsegs m -> stk rsegs m (S - SLOT_STACK_Z) (S - SLOT_FRAME) ->
  MemNorm.task_mem rsegs m'.
Proof using HS MU WM.
  intros TM ST a b E.
  destruct (c2_outside_dec (c2b_W S) (bv_unsigned a)) as [O|O].
  - rewrite (MU a O) in E. exact (TM a b E).
  - assert (IN : S - 528 <= bv_unsigned a < S - 480).
    { unfold c2b_W in O. cbn [outside] in O.
      destruct (Z_le_gt_dec (S - 528) (bv_unsigned a)); [|exfalso; apply O; split; [lia | exact I]].
      destruct (Z_lt_ge_dec (bv_unsigned a) (S - 480)); [lia | exfalso; apply O; split; [lia | exact I]]. }
    destruct ST as (_ & _ & STa). unfold SLOT_STACK_Z, SLOT_FRAME in STa.
    destruct (STa (bv_unsigned a) ltac:(lia)) as [_ (b0 & Hb0)].
    assert (Ew : wa (bv_unsigned a) = a) by (unfold wa; apply Z_to_bv_bv_unsigned).
    rewrite Ew in Hb0. unfold mrd in Hb0.
    destruct (m a) as [b1|] eqn:Ema; [exact (TM a b1 Ema)|].
    left. unfold seg_rom, memory_read in Hb0. try change (Z.of_N 1) with 1 in Hb0.
    destruct (find_segment rsegs (bv_unsigned a) 1) as [sg|] eqn:FS; [discriminate | discriminate Hb0].
Qed.

Lemma c2b_fp : forall hp, seg_fp S hp m m'.
Proof using HS MU WM.
  intros hp. exists (c2b_W S). split; [exact MU|]. split; [exact WM|].
  intros x Hx Hn. left. unfold c2b_W in Hn. cbn [outside] in Hn. unfold SLOT_STACK_Z.
  destruct (Z_le_gt_dec (S - 528) x); [destruct (Z_lt_ge_dec x (S - 480))|].
  - lia.
  - exfalso. apply Hn. split; [lia | exact I].
  - exfalso. apply Hn. split; [lia | exact I].
Qed.

End Tr.

Lemma c2b_addiw : forall i, 0 <= i <= 46 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 i) + 1)) = Z_to_bv 64 (i + 1).
Proof.
  intros i Hi. rewrite unsigned_lit by lia.
  assert (H32 : bv_half_modulus 32 = 2 ^ 31) by reflexivity.
  rewrite bv_swrap_small; [reflexivity | rewrite H32; lia].
Qed.
