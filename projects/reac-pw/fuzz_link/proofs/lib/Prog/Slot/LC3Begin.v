(* The op_unmark arm (c3), plain image: model_begin (fuzz_link.c:668-675) as the arm inlines it at
   0x13b2c-0x13b48, right after kernel returns:
     m->socket_errno = g_nl.socket_errno; m->send_errno = g_nl.send_errno; m->next = 0; m->n_req = 0;
     g_nl.n_sent = 0.
   The walk (c3_begin) and the two byte blocks it leaves (c3_kb, c3_mbb), with the fields of each. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem printf_facts_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC3Lib LC3Defs.
Local Open Scope Z_scope.

(* the fake kernel after `g_nl.n_sent = 0`, and the model after the four stores into m *)
Definition c3_kb (kbs : list byte) : list byte := upd_bytes kbs (Z.to_nat NK_N_SENT) (le4 (Z_to_bv 64 0)).
Definition c3_mbb (mbs : list byte) (se sd : Z) : list byte :=
  upd_bytes (upd_bytes (upd_bytes (upd_bytes mbs (Z.to_nat 0) (le4 (Z_to_bv 64 se))) (Z.to_nat 8) (le4 (Z_to_bv 64 0)))
            (Z.to_nat 4) (le4 (Z_to_bv 64 sd))) (Z.to_nat MD_N_REQ) (le4 (Z_to_bv 64 0)).

Lemma c3_sx32_small : forall v, 0 <= v < 2 ^ 31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sx32. rewrite unsigned_lit by lia. f_equal. apply bv_swrap_small.
  change (bv_half_modulus 32) with (2 ^ 31). lia.
Qed.

(* ==========================================================================
   1. The fields of the two blocks
   ========================================================================== *)

Lemma c3_kb_length : forall kbs, Z.of_nat (length kbs) = NK_SIZE -> Z.of_nat (length (c3_kb kbs)) = NK_SIZE.
Proof. intros kbs H. unfold c3_kb. rewrite upd_bytes_length; [exact H|]. rewrite length_le4. unfold NK_SIZE, NK_N_SENT in *. lia. Qed.

Lemma c3_kb_rdn : forall kbs off n, Z.of_nat (length kbs) = NK_SIZE -> 0 <= off -> 0 <= n ->
  (off + n <= NK_N_SENT \/ NK_N_SENT + 4 <= off) -> link_spec.rdn (c3_kb kbs) off n = link_spec.rdn kbs off n.
Proof.
  intros kbs off n H H0 H1 H2. unfold c3_kb. apply c3_rdn_upd_other; rewrite ?length_le4; unfold NK_SIZE, NK_N_SENT in *; lia.
Qed.

Lemma c3_kb_slice : forall kbs off n, Z.of_nat (length kbs) = NK_SIZE -> 0 <= off -> 0 <= n ->
  (off + n <= NK_N_SENT \/ NK_N_SENT + 4 <= off) -> slice (c3_kb kbs) off n = slice kbs off n.
Proof.
  intros kbs off n H H0 H1 H2. unfold c3_kb. apply c3_slice_upd_other; rewrite ?length_le4; unfold NK_SIZE, NK_N_SENT in *; lia.
Qed.

Lemma c3_kb_n_sent : forall kbs, Z.of_nat (length kbs) = NK_SIZE -> nk_n_sent (c3_kb kbs) = 0.
Proof.
  intros kbs H. unfold nk_n_sent, c3_kb. change NK_N_SENT with (Z.of_nat (Z.to_nat NK_N_SENT)) at 2.
  rewrite c3_fld_u32_upd_same by (unfold NK_SIZE, NK_N_SENT in *; lia). reflexivity.
Qed.

Ltac c3_kb_fld := unfold nk_n_chunks, nk_next, nk_end_errno, nk_socket_errno, nk_send_errno, nk_open, nk_opened,
  nk_closed, nk_misuse, nk_n_if, fld_u32, fld_u64;
  apply c3_kb_rdn; [assumption | | | ]; unfold NK_N_CHUNKS, NK_NEXT, NK_END_ERRNO, NK_SOCKET_ERRNO, NK_SEND_ERRNO,
  NK_OPEN, NK_OPENED, NK_CLOSED, NK_MISUSE, NK_N_IF, NK_N_SENT; lia.

Lemma c3_kb_fields : forall kbs, Z.of_nat (length kbs) = NK_SIZE ->
  nk_n_chunks (c3_kb kbs) = nk_n_chunks kbs /\ nk_next (c3_kb kbs) = nk_next kbs /\
  nk_end_errno (c3_kb kbs) = nk_end_errno kbs /\ nk_socket_errno (c3_kb kbs) = nk_socket_errno kbs /\
  nk_send_errno (c3_kb kbs) = nk_send_errno kbs /\ nk_open (c3_kb kbs) = nk_open kbs /\
  nk_opened (c3_kb kbs) = nk_opened kbs /\ nk_closed (c3_kb kbs) = nk_closed kbs /\
  nk_misuse (c3_kb kbs) = nk_misuse kbs /\ nk_n_if (c3_kb kbs) = nk_n_if kbs.
Proof. intros kbs H. repeat split; c3_kb_fld. Qed.

Lemma c3_kb_chunks : forall kbs, Z.of_nat (length kbs) = NK_SIZE -> nlk_wf kbs -> nk_chunks (c3_kb kbs) = nk_chunks kbs.
Proof.
  intros kbs H W. pose proof (c3_kb_fields kbs H) as (E1 & _).
  unfold nk_chunks. rewrite E1. apply map_ext_in. intros j Hj. apply in_seq in Hj.
  destruct W as (W1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W12 & _).
  assert (Hj' : 0 <= Z.of_nat j < nk_n_chunks kbs) by lia.
  specialize (W12 _ Hj').
  unfold nk_chunk.
  assert (EL : fld_u64 (c3_kb kbs) (NK_CHUNK_LEN + 8 * Z.of_nat j) = fld_u64 kbs (NK_CHUNK_LEN + 8 * Z.of_nat j))
    by (unfold fld_u64; apply c3_kb_rdn; [assumption | | | ]; unfold NK_CHUNK_LEN, NK_N_SENT, NL_CHUNKS in *; lia).
  rewrite EL. apply c3_kb_slice; [assumption | | | ]; unfold NK_CHUNK, NL_CHUNK_MAX, NK_N_SENT, NL_CHUNKS in *; lia.
Qed.

Lemma c3_kb_kstate : forall kbs, Z.of_nat (length kbs) = NK_SIZE -> nlk_wf kbs -> nk_kstate (c3_kb kbs) = nk_kstate kbs.
Proof.
  intros kbs H W. pose proof (c3_kb_fields kbs H) as (_ & E2 & E3 & E4 & E5 & _).
  unfold nk_kstate. rewrite (c3_kb_chunks kbs H W), E2, E3, E4, E5. reflexivity.
Qed.

Lemma c3_kb_sent : forall kbs, Z.of_nat (length kbs) = NK_SIZE -> nk_sent (c3_kb kbs) = [].
Proof. intros kbs H. unfold nk_sent. rewrite (c3_kb_n_sent kbs H). reflexivity. Qed.

Lemma c3_kb_wf : forall kbs, Z.of_nat (length kbs) = NK_SIZE -> nlk_wf kbs -> nlk_wf (c3_kb kbs).
Proof.
  intros kbs H W. pose proof (c3_kb_fields kbs H) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10).
  pose proof (c3_kb_n_sent kbs H) as E11.
  destruct W as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13).
  unfold nlk_wf. rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11.
  repeat split; try lia.
  all: lazymatch goal with Hj : 0 <= ?j < nk_n_chunks _ |- _ =>
    specialize (W12 j Hj);
    assert (EL : fld_u64 (c3_kb kbs) (NK_CHUNK_LEN + 8 * j) = fld_u64 kbs (NK_CHUNK_LEN + 8 * j))
      by (unfold fld_u64; apply c3_kb_rdn; [assumption | | | ]; unfold NK_CHUNK_LEN, NK_N_SENT, NL_CHUNKS in *; lia);
    rewrite EL; lia end.
Qed.

Lemma c3_mbb_lens : forall mbs se sd, Z.of_nat (length mbs) = MD_SIZE ->
  Z.of_nat (length (upd_bytes mbs (Z.to_nat 0) (le4 (Z_to_bv 64 se)))) = MD_SIZE /\
  Z.of_nat (length (upd_bytes (upd_bytes mbs (Z.to_nat 0) (le4 (Z_to_bv 64 se))) (Z.to_nat 8) (le4 (Z_to_bv 64 0))))
    = MD_SIZE /\
  Z.of_nat (length (upd_bytes (upd_bytes (upd_bytes mbs (Z.to_nat 0) (le4 (Z_to_bv 64 se))) (Z.to_nat 8)
            (le4 (Z_to_bv 64 0))) (Z.to_nat 4) (le4 (Z_to_bv 64 sd)))) = MD_SIZE /\
  Z.of_nat (length (c3_mbb mbs se sd)) = MD_SIZE.
Proof.
  intros mbs se sd L0. unfold MD_SIZE in *.
  assert (L1 : Z.of_nat (length (upd_bytes mbs (Z.to_nat 0) (le4 (Z_to_bv 64 se)))) = 8856)
    by (rewrite upd_bytes_length; rewrite ?length_le4; lia).
  assert (L2 : Z.of_nat (length (upd_bytes (upd_bytes mbs (Z.to_nat 0) (le4 (Z_to_bv 64 se))) (Z.to_nat 8)
                 (le4 (Z_to_bv 64 0)))) = 8856) by (rewrite upd_bytes_length; rewrite ?length_le4; lia).
  assert (L3 : Z.of_nat (length (upd_bytes (upd_bytes (upd_bytes mbs (Z.to_nat 0) (le4 (Z_to_bv 64 se))) (Z.to_nat 8)
                 (le4 (Z_to_bv 64 0))) (Z.to_nat 4) (le4 (Z_to_bv 64 sd)))) = 8856)
    by (rewrite upd_bytes_length; rewrite ?length_le4; lia).
  split; [exact L1|]. split; [exact L2|]. split; [exact L3|].
  unfold c3_mbb. rewrite upd_bytes_length; rewrite ?length_le4; unfold MD_N_REQ; lia.
Qed.

Lemma c3_mbb_length : forall mbs se sd, Z.of_nat (length mbs) = MD_SIZE -> Z.of_nat (length (c3_mbb mbs se sd)) = MD_SIZE.
Proof.
  intros mbs se sd H. destruct (c3_mbb_lens mbs se sd H) as (_ & _ & _ & L). exact L.
Qed.

Ltac c3_mbb_sc L0 L1 L2 L3 := rewrite ?length_le4; unfold MD_N_REQ, MD_SIZE in *; lia.

Lemma c3_mbb_rdn : forall mbs se sd off n, Z.of_nat (length mbs) = MD_SIZE -> 0 <= off -> 0 <= n ->
  12 <= off -> (off + n <= MD_N_REQ \/ MD_N_REQ + 4 <= off) ->
  link_spec.rdn (c3_mbb mbs se sd) off n = link_spec.rdn mbs off n.
Proof.
  intros mbs se sd off n H H0 H1 H2 H3.
  pose proof H as L0. destruct (c3_mbb_lens mbs se sd H) as (L1 & L2 & L3 & _).
  unfold c3_mbb.
  rewrite c3_rdn_upd_other by c3_mbb_sc L0 L1 L2 L3.
  rewrite c3_rdn_upd_other by c3_mbb_sc L0 L1 L2 L3.
  rewrite c3_rdn_upd_other by c3_mbb_sc L0 L1 L2 L3.
  rewrite c3_rdn_upd_other by c3_mbb_sc L0 L1 L2 L3.
  reflexivity.
Qed.

Lemma c3_mbb_slice : forall mbs se sd off n, Z.of_nat (length mbs) = MD_SIZE -> 0 <= off -> 0 <= n ->
  12 <= off -> (off + n <= MD_N_REQ \/ MD_N_REQ + 4 <= off) ->
  slice (c3_mbb mbs se sd) off n = slice mbs off n.
Proof.
  intros mbs se sd off n H H0 H1 H2 H3.
  pose proof H as L0. destruct (c3_mbb_lens mbs se sd H) as (L1 & L2 & L3 & _).
  unfold c3_mbb.
  rewrite c3_slice_upd_other by c3_mbb_sc L0 L1 L2 L3.
  rewrite c3_slice_upd_other by c3_mbb_sc L0 L1 L2 L3.
  rewrite c3_slice_upd_other by c3_mbb_sc L0 L1 L2 L3.
  rewrite c3_slice_upd_other by c3_mbb_sc L0 L1 L2 L3.
  reflexivity.
Qed.

Lemma c3_mbb_fields : forall mbs se sd, Z.of_nat (length mbs) = MD_SIZE -> 0 <= se < 2 ^ 31 -> 0 <= sd < 2 ^ 31 ->
  md_socket_errno (c3_mbb mbs se sd) = se /\ md_send_errno (c3_mbb mbs se sd) = sd /\
  md_next (c3_mbb mbs se sd) = 0 /\ md_n_req (c3_mbb mbs se sd) = 0 /\
  md_n_mark (c3_mbb mbs se sd) = md_n_mark mbs.
Proof.
  intros mbs se sd H Hse Hsd.
  assert (L0 : Z.of_nat (length mbs) = 8856) by (unfold MD_SIZE in H; lia).
  set (b1 := upd_bytes mbs (Z.to_nat 0) (le4 (Z_to_bv 64 se))).
  set (b2 := upd_bytes b1 (Z.to_nat 8) (le4 (Z_to_bv 64 0))).
  set (b3 := upd_bytes b2 (Z.to_nat 4) (le4 (Z_to_bv 64 sd))).
  assert (L1 : Z.of_nat (length b1) = 8856) by (unfold b1; rewrite upd_bytes_length; rewrite ?length_le4; lia).
  assert (L2 : Z.of_nat (length b2) = 8856) by (unfold b2; rewrite upd_bytes_length; rewrite ?length_le4; lia).
  assert (L3 : Z.of_nat (length b3) = 8856) by (unfold b3; rewrite upd_bytes_length; rewrite ?length_le4; lia).
  unfold c3_mbb. fold b1 b2 b3.
  unfold md_socket_errno, md_send_errno, md_next, md_n_req, md_n_mark, fld_u32,
    MD_SOCKET_ERRNO, MD_SEND_ERRNO, MD_NEXT, MD_N_MARK.
  repeat split.
  - rewrite c3_rdn_upd_other by (rewrite ?length_le4; unfold MD_N_REQ; lia). unfold b3.
    rewrite c3_rdn_upd_other by (rewrite ?length_le4; lia). unfold b2.
    rewrite c3_rdn_upd_other by (rewrite ?length_le4; lia). unfold b1.
    pose proof (c3_fld_u32_upd_same mbs (Z.to_nat 0) (Z_to_bv 64 se) ltac:(lia)) as EF.
    change (Z.of_nat (Z.to_nat 0)) with 0 in EF. unfold fld_u32 in EF. rewrite EF.
    rewrite unsigned_lit by lia. apply Z.mod_small. lia.
  - rewrite c3_rdn_upd_other by (rewrite ?length_le4; unfold MD_N_REQ; lia). unfold b3.
    pose proof (c3_fld_u32_upd_same b2 (Z.to_nat 4) (Z_to_bv 64 sd) ltac:(lia)) as EF.
    change (Z.of_nat (Z.to_nat 4)) with 4 in EF. unfold fld_u32 in EF. rewrite EF.
    rewrite unsigned_lit by lia. apply Z.mod_small. lia.
  - rewrite c3_rdn_upd_other by (rewrite ?length_le4; unfold MD_N_REQ; lia). unfold b3.
    rewrite c3_rdn_upd_other by (rewrite ?length_le4; lia). unfold b2.
    pose proof (c3_fld_u32_upd_same b1 (Z.to_nat 8) (Z_to_bv 64 0) ltac:(lia)) as EF.
    change (Z.of_nat (Z.to_nat 8)) with 8 in EF. unfold fld_u32 in EF. rewrite EF. reflexivity.
  - pose proof (c3_fld_u32_upd_same b3 (Z.to_nat MD_N_REQ) (Z_to_bv 64 0) ltac:(unfold MD_N_REQ; lia)) as EF.
    change (Z.of_nat (Z.to_nat MD_N_REQ)) with MD_N_REQ in EF. unfold fld_u32 in EF. rewrite EF. reflexivity.
  - apply (c3_mbb_rdn mbs se sd); [exact H | lia | lia | lia | unfold MD_N_REQ; lia].
Qed.

Lemma c3_mbb_marks : forall mbs se sd, Z.of_nat (length mbs) = MD_SIZE -> model_wf mbs ->
  md_marks (c3_mbb mbs se sd) = md_marks mbs.
Proof.
  intros mbs se sd H W. destruct W as (_ & _ & _ & _ & _ & W6 & _).
  pose proof (c3_mbb_fields) as _.
  unfold md_marks.
  assert (EN : md_n_mark (c3_mbb mbs se sd) = md_n_mark mbs)
    by (unfold md_n_mark, fld_u32; apply c3_mbb_rdn; [exact H | | | | ]; unfold MD_N_MARK, MD_N_REQ; lia).
  rewrite EN. apply map_ext_in. intros j Hj. apply in_seq in Hj. f_equal.
  apply c3_mbb_slice; [exact H | | | | ]; unfold MD_MARK, MARK_LEN, MD_N_REQ; lia.
Qed.

Lemma c3_mbb_reqs : forall mbs se sd, Z.of_nat (length mbs) = MD_SIZE -> 0 <= se < 2 ^ 31 -> 0 <= sd < 2 ^ 31 ->
  md_reqs (c3_mbb mbs se sd) = [].
Proof.
  intros mbs se sd H Hse Hsd. destruct (c3_mbb_fields mbs se sd H Hse Hsd) as (_ & _ & _ & E & _).
  unfold md_reqs. rewrite E. reflexivity.
Qed.

Lemma c3_mbb_wf : forall mbs se sd, Z.of_nat (length mbs) = MD_SIZE -> 0 <= se < 2 ^ 31 -> 0 <= sd < 2 ^ 31 ->
  model_wf mbs -> model_wf (c3_mbb mbs se sd).
Proof.
  intros mbs se sd H Hse Hsd W.
  destruct (c3_mbb_fields mbs se sd H Hse Hsd) as (E1 & E2 & E3 & E4 & E5).
  pose proof W as (_ & _ & _ & _ & _ & W6a & W6b).
  unfold model_wf. rewrite E1, E2, E3, E4.
  split; [unfold NL_SENT_MAX; lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [intros j Hj; lia|].
  unfold model_marks_wf. rewrite E5. split; [exact W6a|].
  intros j Hj. specialize (W6b j Hj).
  rewrite (c3_mbb_slice mbs se sd); [exact W6b | exact H | | | | ]; unfold MD_MARK, MARK_LEN, MD_N_REQ in *; lia.
Qed.

(* ==========================================================================
   2. The walk 0x13b2c -> 0x13b4c
   ========================================================================== *)

Lemma c3_begin : forall (E : lenv) (i : Z) (gp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (j0 kbs mbs : list byte) (Q : machine_state -> Prop),
  lenv_ok E ->
  rw_cells rsegs m (e_S E - SLOT_FRAME) [CB 8 j0; C8 (wz A_ODD); C8 (wz (e_md E + MD_MARK)); C8 (wz A_EMPTY);
    C8 (wz (e_mk E)); C8 (wz A_G_NAMES); C8 (wz A_JT); C8 (wz GNL42)] ->
  nlk_at m kbs -> nlk_wf kbs -> model_at m (e_md E) mbs -> mem_inv rsegs m ->
  (forall m' : word -> option byte,
     munch [(e_md E, e_md E + 12); (e_md E + MD_N_REQ, e_md E + MD_N_REQ + 4);
            (A_G_NL + NK_N_SENT, A_G_NL + NK_N_SENT + 4)] m m' ->
     wmono rsegs m m' -> mem_inv rsegs m' ->
     rw_cells rsegs m' (e_S E - SLOT_FRAME) [CB 8 j0; C8 (wz A_ODD); C8 (wz (e_md E + MD_MARK)); C8 (wz A_EMPTY);
       C8 (wz (e_mk E)); C8 (wz A_G_NAMES); C8 (wz A_JT); C8 (wz GNL42)] ->
     nlk_at m' (c3_kb kbs) ->
     model_at m' (e_md E) (c3_mbb mbs (nk_socket_errno kbs) (nk_send_errno kbs)) ->
     evt rsegs Q (MS (c3_regs E i gp ra t0 t1 t2 (wz GNL42) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6)
                     F (wz L3_MB) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (c3_regs E i gp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6)
                  F (wz L3_KRET) fc None m (seg_rom rsegs)).
Proof.
  intros E i gp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6 F fc m j0 kbs mbs Q
    HE HC [HK LK] HKW [HM LM] MI K.
  destruct HE as (ES1 & ES2 & _ & (Hmd1 & Hmd2 & Hmd3) & _).
  pose proof (c3_img_free _ _ Hmd3 ltac:(unfold MD_SIZE; lia)) as Hmdi.
  pose proof HKW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hse & Hsd & _).
  set (se := nk_socket_errno kbs) in *. set (sd := nk_send_errno kbs) in *.
  pose proof (munch_refl [(e_md E, e_md E + 12); (e_md E + MD_N_REQ, e_md E + MD_N_REQ + 4);
                          (A_G_NL + NK_N_SENT, A_G_NL + NK_N_SENT + 4)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (Lk : Z.of_nat (length kbs) = 271992) by (unfold NK_SIZE in LK; lia).
  assert (Lm : Z.of_nat (length mbs) = 8856) by (unfold MD_SIZE in LM; lia).
  unfold c3_regs.
  unfold wz, L3_KRET, L3_MB, A_TP, GNL40, GNL42, A_JT, A_G_NL, MD_N_REQ, NK_N_SENT, SLOT_FRAME, SLOT_STACK_Z,
    MD_SIZE in *.
  (* 0x13b2c lw a0, 0x20c(s1) *)
  pose proof (c3_u8arr_rd32 m 203648 kbs NK_SOCKET_ERRNO 466316 HK ltac:(unfold NK_SOCKET_ERRNO; lia)
               ltac:(rewrite Lk; unfold NK_SOCKET_ERRNO; lia) ltac:(reflexivity)) as HR1.
  unfold wz in HR1. change (fld_u32 kbs NK_SOCKET_ERRNO) with se in HR1.
  step. rewrite (c3_sx32_small se Hse).
  (* 0x13b30 sw a0, 0(s0) *)
  pose proof (c3_u8arr_store_ok m (e_md E) mbs 0 (e_md E) 4 HM ltac:(lia) ltac:(rewrite Lm; lia) ltac:(lia)) as HS1.
  step.
  set (m1 := write_to_mem m (Z_to_bv 64 (e_md E)) (le4 (Z_to_bv 64 se))).
  assert (HM1 : u8arr rsegs m1 (e_md E) (upd_bytes mbs (Z.to_nat 0) (le4 (Z_to_bv 64 se))))
    by exact (c3_u8arr_write m (e_md E) mbs 0 (e_md E) _ HM ltac:(lia) ltac:(rewrite length_le4; lia) ltac:(lia)).
  assert (HK1 : u8arr rsegs m1 203648 kbs)
    by (apply (u8arr_frame rsegs m 203648 kbs (e_md E) _ HK); rewrite ?length_le4; lia).
  assert (HC1 : rw_cells rsegs m1 (e_S E - 480) [CB 8 j0; C8 (Z_to_bv 64 A_ODD); C8 (Z_to_bv 64 (e_md E + MD_MARK));
     C8 (Z_to_bv 64 A_EMPTY); C8 (Z_to_bv 64 (e_mk E)); C8 (Z_to_bv 64 A_G_NAMES); C8 (Z_to_bv 64 67248);
     C8 (Z_to_bv 64 (203648 + 270336))])
    by (apply (rw_cells_frame rsegs m _ _ (e_md E) _ HC); cbn [cells_size csize Nat.add]; rewrite ?length_le4; lia).
  assert (MI1 : mem_inv rsegs m1) by exact (mem_inv_store rsegs m _ (le4 (Z_to_bv 64 se)) MI HS1).
  assert (MU1 : munch [(e_md E, e_md E + 12); (e_md E + 8336, e_md E + 8336 + 4); (203648 + 271016, 203648 + 271016 + 4)]
                  m m1)
    by (apply (munch_write _ m m (e_md E) _ MU); rewrite ?length_le4; [lia | lia | cbn [inside]; lia]).
  assert (WM1 : wmono rsegs m m1) by exact (wmono_write rsegs m m _ _ WM).
  clearbody m1. clear HM HK HC MI MU WM HS1 HR1.
  (* 0x13b34 lw a0, 0x210(s1) *)
  pose proof (c3_u8arr_rd32 m1 203648 kbs NK_SEND_ERRNO 466320 HK1 ltac:(unfold NK_SEND_ERRNO; lia)
               ltac:(rewrite Lk; unfold NK_SEND_ERRNO; lia) ltac:(reflexivity)) as HR2.
  unfold wz in HR2. change (fld_u32 kbs NK_SEND_ERRNO) with sd in HR2.
  step. rewrite (c3_sx32_small sd Hsd).
  (* 0x13b38 sw zero, 8(s0) *)
  set (mbs1 := upd_bytes mbs (Z.to_nat 0) (le4 (Z_to_bv 64 se))) in HM1.
  assert (Lm1 : Z.of_nat (length mbs1) = 8856) by (unfold mbs1; rewrite upd_bytes_length; rewrite ?length_le4; lia).
  pose proof (c3_u8arr_store_ok m1 (e_md E) mbs1 8 (e_md E + 8) 4 HM1 ltac:(lia) ltac:(rewrite Lm1; lia) ltac:(lia))
    as HS2.
  step.
  set (m2 := write_to_mem m1 (Z_to_bv 64 (e_md E + 8)) (le4 (Z_to_bv 64 0))).
  assert (HM2 : u8arr rsegs m2 (e_md E) (upd_bytes mbs1 (Z.to_nat 8) (le4 (Z_to_bv 64 0))))
    by exact (c3_u8arr_write m1 (e_md E) mbs1 8 (e_md E + 8) _ HM1 ltac:(lia) ltac:(rewrite length_le4; lia) ltac:(lia)).
  assert (HK2 : u8arr rsegs m2 203648 kbs)
    by (apply (u8arr_frame rsegs m1 203648 kbs (e_md E + 8) _ HK1); rewrite ?length_le4; lia).
  assert (HC2 : rw_cells rsegs m2 (e_S E - 480) [CB 8 j0; C8 (Z_to_bv 64 A_ODD); C8 (Z_to_bv 64 (e_md E + MD_MARK));
     C8 (Z_to_bv 64 A_EMPTY); C8 (Z_to_bv 64 (e_mk E)); C8 (Z_to_bv 64 A_G_NAMES); C8 (Z_to_bv 64 67248);
     C8 (Z_to_bv 64 (203648 + 270336))])
    by (apply (rw_cells_frame rsegs m1 _ _ (e_md E + 8) _ HC1); cbn [cells_size csize Nat.add]; rewrite ?length_le4; lia).
  assert (MI2 : mem_inv rsegs m2) by exact (mem_inv_store rsegs m1 _ (le4 (Z_to_bv 64 0)) MI1 HS2).
  assert (MU2 : munch [(e_md E, e_md E + 12); (e_md E + 8336, e_md E + 8336 + 4); (203648 + 271016, 203648 + 271016 + 4)]
                  m m2)
    by (apply (munch_write _ m m1 (e_md E + 8) _ MU1); rewrite ?length_le4; [lia | lia | cbn [inside]; lia]).
  assert (WM2 : wmono rsegs m m2) by exact (wmono_write rsegs m m1 _ _ WM1).
  clearbody m2. clear HM1 HK1 HC1 MI1 MU1 WM1 HS2 HR2.
  (* 0x13b3c sw a0, 4(s0) *)
  set (mbs2 := upd_bytes mbs1 (Z.to_nat 8) (le4 (Z_to_bv 64 0))) in HM2.
  assert (Lm2 : Z.of_nat (length mbs2) = 8856) by (unfold mbs2; rewrite upd_bytes_length; rewrite ?length_le4; lia).
  pose proof (c3_u8arr_store_ok m2 (e_md E) mbs2 4 (e_md E + 4) 4 HM2 ltac:(lia) ltac:(rewrite Lm2; lia) ltac:(lia))
    as HS3.
  step.
  set (m3 := write_to_mem m2 (Z_to_bv 64 (e_md E + 4)) (le4 (Z_to_bv 64 sd))).
  assert (HM3 : u8arr rsegs m3 (e_md E) (upd_bytes mbs2 (Z.to_nat 4) (le4 (Z_to_bv 64 sd))))
    by exact (c3_u8arr_write m2 (e_md E) mbs2 4 (e_md E + 4) _ HM2 ltac:(lia) ltac:(rewrite length_le4; lia) ltac:(lia)).
  assert (HK3 : u8arr rsegs m3 203648 kbs)
    by (apply (u8arr_frame rsegs m2 203648 kbs (e_md E + 4) _ HK2); rewrite ?length_le4; lia).
  assert (HC3 : rw_cells rsegs m3 (e_S E - 480) [CB 8 j0; C8 (Z_to_bv 64 A_ODD); C8 (Z_to_bv 64 (e_md E + MD_MARK));
     C8 (Z_to_bv 64 A_EMPTY); C8 (Z_to_bv 64 (e_mk E)); C8 (Z_to_bv 64 A_G_NAMES); C8 (Z_to_bv 64 67248);
     C8 (Z_to_bv 64 (203648 + 270336))])
    by (apply (rw_cells_frame rsegs m2 _ _ (e_md E + 4) _ HC2); cbn [cells_size csize Nat.add]; rewrite ?length_le4; lia).
  assert (MI3 : mem_inv rsegs m3) by exact (mem_inv_store rsegs m2 _ (le4 (Z_to_bv 64 sd)) MI2 HS3).
  assert (MU3 : munch [(e_md E, e_md E + 12); (e_md E + 8336, e_md E + 8336 + 4); (203648 + 271016, 203648 + 271016 + 4)]
                  m m3)
    by (apply (munch_write _ m m2 (e_md E + 4) _ MU2); rewrite ?length_le4; [lia | lia | cbn [inside]; lia]).
  assert (WM3 : wmono rsegs m m3) by exact (wmono_write rsegs m m2 _ _ WM2).
  clearbody m3. clear HM2 HK2 HC2 MI2 MU2 WM2 HS3.
  (* 0x13b40 sw zero, 0(s10) *)
  set (mbs3 := upd_bytes mbs2 (Z.to_nat 4) (le4 (Z_to_bv 64 sd))) in HM3.
  assert (Lm3 : Z.of_nat (length mbs3) = 8856) by (unfold mbs3; rewrite upd_bytes_length; rewrite ?length_le4; lia).
  pose proof (c3_u8arr_store_ok m3 (e_md E) mbs3 8336 (e_md E + 8336) 4 HM3 ltac:(lia) ltac:(rewrite Lm3; lia)
                ltac:(lia)) as HS4.
  step.
  set (m4 := write_to_mem m3 (Z_to_bv 64 (e_md E + 8336)) (le4 (Z_to_bv 64 0))).
  assert (HM4 : u8arr rsegs m4 (e_md E) (upd_bytes mbs3 (Z.to_nat 8336) (le4 (Z_to_bv 64 0))))
    by exact (c3_u8arr_write m3 (e_md E) mbs3 8336 (e_md E + 8336) _ HM3 ltac:(lia) ltac:(rewrite length_le4; lia)
                ltac:(lia)).
  assert (HK4 : u8arr rsegs m4 203648 kbs)
    by (apply (u8arr_frame rsegs m3 203648 kbs (e_md E + 8336) _ HK3); rewrite ?length_le4; lia).
  assert (HC4 : rw_cells rsegs m4 (e_S E - 480) [CB 8 j0; C8 (Z_to_bv 64 A_ODD); C8 (Z_to_bv 64 (e_md E + MD_MARK));
     C8 (Z_to_bv 64 A_EMPTY); C8 (Z_to_bv 64 (e_mk E)); C8 (Z_to_bv 64 A_G_NAMES); C8 (Z_to_bv 64 67248);
     C8 (Z_to_bv 64 (203648 + 270336))])
    by (apply (rw_cells_frame rsegs m3 _ _ (e_md E + 8336) _ HC3); cbn [cells_size csize Nat.add]; rewrite ?length_le4;
        lia).
  assert (MI4 : mem_inv rsegs m4) by exact (mem_inv_store rsegs m3 _ (le4 (Z_to_bv 64 0)) MI3 HS4).
  assert (MU4 : munch [(e_md E, e_md E + 12); (e_md E + 8336, e_md E + 8336 + 4); (203648 + 271016, 203648 + 271016 + 4)]
                  m m4)
    by (apply (munch_write _ m m3 (e_md E + 8336) _ MU3); rewrite ?length_le4; [lia | lia | cbn [inside]; lia]).
  assert (WM4 : wmono rsegs m m4) by exact (wmono_write rsegs m m3 _ _ WM3).
  clearbody m4. clear HM3 HK3 HC3 MI3 MU3 WM3 HS4.
  (* 0x13b44 ld a0, 0x38(sp); 0x13b48 sw zero, 0x2a8(a0) *)
  step.
  pose proof (c3_u8arr_store_ok m4 203648 kbs NK_N_SENT 474664 4 HK4 ltac:(unfold NK_N_SENT; lia)
                ltac:(rewrite Lk; unfold NK_N_SENT; lia) ltac:(unfold NK_N_SENT; lia)) as HS5.
  step.
  set (m5 := write_to_mem m4 (Z_to_bv 64 474664) (le4 (Z_to_bv 64 0))).
  assert (HK5 : u8arr rsegs m5 203648 (upd_bytes kbs (Z.to_nat NK_N_SENT) (le4 (Z_to_bv 64 0))))
    by exact (c3_u8arr_write m4 203648 kbs NK_N_SENT 474664 _ HK4 ltac:(unfold NK_N_SENT; lia)
                ltac:(rewrite length_le4, Lk; unfold NK_N_SENT; lia) ltac:(unfold NK_N_SENT; lia)).
  assert (HM5 : u8arr rsegs m5 (e_md E) (upd_bytes mbs3 (Z.to_nat 8336) (le4 (Z_to_bv 64 0))))
    by (apply (u8arr_frame rsegs m4 (e_md E) _ 474664 _ HM4); rewrite ?length_le4, ?upd_bytes_length;
        rewrite ?length_le4; lia).
  assert (HC5 : rw_cells rsegs m5 (e_S E - 480) [CB 8 j0; C8 (Z_to_bv 64 A_ODD); C8 (Z_to_bv 64 (e_md E + MD_MARK));
     C8 (Z_to_bv 64 A_EMPTY); C8 (Z_to_bv 64 (e_mk E)); C8 (Z_to_bv 64 A_G_NAMES); C8 (Z_to_bv 64 67248);
     C8 (Z_to_bv 64 (203648 + 270336))])
    by (apply (rw_cells_frame rsegs m4 _ _ 474664 _ HC4); cbn [cells_size csize Nat.add]; rewrite ?length_le4; lia).
  assert (MI5 : mem_inv rsegs m5) by exact (mem_inv_store rsegs m4 _ (le4 (Z_to_bv 64 0)) MI4 HS5).
  assert (MU5 : munch [(e_md E, e_md E + 12); (e_md E + 8336, e_md E + 8336 + 4); (203648 + 271016, 203648 + 271016 + 4)]
                  m m5)
    by (apply (munch_write _ m m4 474664 _ MU4); rewrite ?length_le4; [lia | lia | cbn [inside]; lia]).
  assert (WM5 : wmono rsegs m m5) by exact (wmono_write rsegs m m4 _ _ WM4).
  clearbody m5.
  apply K; [exact MU5 | exact WM5 | exact MI5 | exact HC5 | | ].
  - split; [exact HK5|]. apply c3_kb_length. exact LK.
  - split; [exact HM5|]. apply c3_mbb_length. exact LM.
Qed.
