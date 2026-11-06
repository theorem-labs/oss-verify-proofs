(* The op_unmark arm (c3) of LLVMFuzzerTestOneInput, plain image: the TAIL piece, from the cut c3_ub
   (0x13bb8) to the next loop head or the exit.

     0x13bb8 sw zero, 0x204(s10)       m->n_mark = 0 (s10 = &m->n_req, so md + 8852)
     0x13bbc mv a0, s7                 marks
     0x13bc0 jal reac_served_unmark_all
     0x13bc4 jal check_socket
     0x13bc8 j 0x13dc4
     0x13dc4 mv a0, s7; mv a1, s0; jal check_marks
     0x13dd0 mv a0, s0; jal check_requests
     0x13dd8 bltu s5, s11, 0x1413c     operation 47 done: the exit
     0x13ddc j 0x1406c
     0x1406c ld s2, 0x48(sp); addiw s11, s11, 1; bnez s2, 0x13a1c   the next loop head
     0x14078 j 0x1413c                 the input is used up: the exit

   The four callees enter as Section hypotheses (their contracts). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import
  reac_served_unmark_all_c check_socket_c check_marks_c check_requests_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC3Lib LC3Defs LC3Keep.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Numbers
   ========================================================================== *)

Ltac c3t_unf := cbv [SLOT_FRAME SLOT_STACK_Z A_G_NL NK_N_SENT NK_SIZE NK_IF_NAME NK_IF_INDEX A_ERRNO A_TP
  ERRNO_TP_OFF MK_SIZE MD_SIZE MD_N_MARK MD_N_REQ A_LONG_ALIAS LONG_ALIAS_SIZE A_G_NAMES G_NAMES_SIZE
  A_GUARD_S A_GOT_GUARD_S A_ODD A_TEXTS MARKS_MAX TASK_SIZE].
Ltac c3t_unfa := cbv [SLOT_FRAME SLOT_STACK_Z A_G_NL NK_N_SENT NK_SIZE NK_IF_NAME NK_IF_INDEX A_ERRNO A_TP
  ERRNO_TP_OFF MK_SIZE MD_SIZE MD_N_MARK MD_N_REQ A_LONG_ALIAS LONG_ALIAS_SIZE A_G_NAMES G_NAMES_SIZE
  A_GUARD_S A_GOT_GUARD_S A_ODD A_TEXTS MARKS_MAX TASK_SIZE] in *.
Ltac c3t_dj := cbn [disjoint_from]; repeat split; c3t_unf; lia.

Lemma c3t_env : forall E, lenv_ok E ->
  0x960e0 + 65536 <= e_S E <= 2 ^ 47 /\
  4096 <= e_md E /\ e_md E + 8856 <= e_S E - 65536 /\ (e_md E + 8856 <= 0x10000 \/ 0x97000 <= e_md E) /\
  4096 <= e_mk E /\ e_mk E + 516 <= e_S E - 65536 /\ (e_mk E + 516 <= 0x10000 \/ 0x97000 <= e_mk E) /\
  (e_md E + 8856 <= e_mk E \/ e_mk E + 516 <= e_md E) /\
  1 <= Z.of_nat (length (e_pl E)) < 2 ^ 26 /\ 4096 <= e_p0 E /\
  e_p0 E + Z.of_nat (length (e_pl E)) <= e_S E - 65536 /\
  (e_p0 E + Z.of_nat (length (e_pl E)) <= 0x10000 \/ 0x97000 <= e_p0 E) /\
  (e_p0 E + Z.of_nat (length (e_pl E)) <= e_md E \/ e_md E + 8856 <= e_p0 E) /\
  (e_p0 E + Z.of_nat (length (e_pl E)) <= e_mk E \/ e_mk E + 516 <= e_p0 E).
Proof.
  intros E HE. pose proof HE as (H1 & H2 & _ & Bd & Bk & _ & _ & Hdk & Hl & Bp & Hpd & Hpk & _).
  pose proof (c3_blk_img _ _ _ Bd ltac:(unfold MD_SIZE; lia)) as Id.
  pose proof (c3_blk_img _ _ _ Bk ltac:(unfold MK_SIZE; lia)) as Ik.
  pose proof (c3_blk_img _ _ _ Bp ltac:(lia)) as Ip.
  destruct Bd as (Bd1 & Bd2 & _). destruct Bk as (Bk1 & Bk2 & _). destruct Bp as (Bp1 & Bp2 & _).
  unfold SLOT_STACK_Z, MD_SIZE, MK_SIZE in *.
  repeat split; lia.
Qed.

(* ==========================================================================
   2. The views of c3_mem that no write of the tail touches, carried across a write set
   ========================================================================== *)

Definition c3t_st (E : lenv) (P N : Z) (m : word -> option byte) : Prop :=
  (exists j0 j1 j2, rw_cells rsegs m (e_S E - SLOT_FRAME) (lh_cells (e_md E) (e_mk E) P N j0 j1 j2)) /\
  bytes_at rsegs m (e_S E - 104) (e_saved E) /\
  gnames_at m /\ odd_at m /\ policy_ro m /\ la_ok m /\ texts_at m /\ ifptrs_at m /\
  cursor_ok m (e_p0 E) (e_pl E) P N /\ wr_at rsegs m A_ERRNO 4 /\ guard_m m.

Lemma c3t_st_of : forall E P N kbs mbs gbs m, c3_mem E P N kbs mbs gbs m -> c3t_st E P N m.
Proof.
  intros E P N kbs mbs gbs m
    (FR & SV & _ & _ & _ & GN & OD & PR & LA & TX & IP & _ & _ & _ & _ & CU & ER & GU & _ & _ & _).
  exact (conj FR (conj SV (conj GN (conj OD (conj PR (conj LA (conj TX (conj IP (conj CU (conj ER GU)))))))))).
Qed.

Lemma c3t_st_keep : forall E P N W m m', lenv_ok E -> c3t_st E P N m -> munch W m m' -> wmono rsegs m m' ->
  disjoint_from W (e_S E - SLOT_FRAME) SLOT_FRAME ->
  disjoint_from W 0x10000 0x11000 ->
  disjoint_from W (A_G_NL + NK_IF_NAME) (NK_SIZE - NK_IF_NAME) ->
  disjoint_from W A_G_NAMES (G_NAMES_SIZE + LONG_ALIAS_SIZE + 3) ->
  disjoint_from W A_GUARD_S 8 ->
  disjoint_from W (e_p0 E) (Z.of_nat (length (e_pl E))) ->
  c3t_st E P N m'.
Proof.
  intros E P N W m m' HE (FR & SV & GN & OD & PR & LA & TX & IP & CU & ER & GU) MU WM D1 D2 D3 D4 D5 D6.
  destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSV).
  unfold c3t_st.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
  - destruct FR as (j0 & j1 & j2 & FR). exists j0, j1, j2.
    eapply (rw_cells_transport rsegs); [exact FR | exact MU | exact WM |].
    change (Z.of_nat (cells_size (lh_cells (e_md E) (e_mk E) P N j0 j1 j2))) with 376.
    eapply c3_dj_sub; [exact D1 | | |]; unfold SLOT_FRAME; lia.
  - eapply (bytes_at_transport rsegs); [exact SV | exact MU |]. rewrite HSV.
    eapply c3_dj_sub; [exact D1 | | |]; unfold SLOT_FRAME; lia.
  - eapply c3_gnames_tr; [exact GN | exact MU |].
    eapply c3_dj_sub; [exact D4 | | |]; unfold G_NAMES_SIZE, LONG_ALIAS_SIZE; lia.
  - eapply c3_odd_tr; [exact OD | exact MU | |].
    + eapply c3_dj_sub; [exact D2 | | |]; unfold A_ODD; lia.
    + eapply c3_dj_sub; [exact D2 | | |]; lia.
  - eapply c3_policy_tr; [exact PR | exact MU |]. eapply c3_dj_sub; [exact D2 | | |]; lia.
  - eapply c3_la_tr; [exact LA | exact MU | exact WM |].
    eapply c3_dj_sub; [exact D4 | | |]; unfold A_LONG_ALIAS, A_G_NAMES, G_NAMES_SIZE, LONG_ALIAS_SIZE; lia.
  - eapply c3_texts_tr; [exact TX | exact MU |]. eapply c3_dj_sub; [exact D2 | | |]; unfold A_TEXTS; lia.
  - eapply c3_ifptrs_tr; [exact IP | exact MU |].
    eapply c3_dj_sub; [exact D3 | | |]; unfold NK_SIZE, NK_IF_NAME; lia.
  - eapply c3_cursor_tr; [exact CU | exact MU | exact D6].
  - exact (wr_at_transport rsegs m m' A_ERRNO 4 ER WM).
  - eapply c3_guard_tr; [exact GU | exact MU | | exact D5].
    eapply c3_dj_sub; [exact D2 | | |]; unfold A_GOT_GUARD_S; lia.
Qed.

Lemma c3t_iftab_keep : forall W m m' kbs, iftab_at m kbs link_tab -> ifptrs_at m -> munch W m m' ->
  disjoint_from W 0x10000 0x11000 -> disjoint_from W (A_G_NL + NK_IF_NAME) (NK_SIZE - NK_IF_NAME) ->
  disjoint_from W A_G_NAMES (G_NAMES_SIZE + LONG_ALIAS_SIZE + 3) -> iftab_at m' kbs link_tab.
Proof.
  intros W m m' kbs HT HP MU D2 D3 D4.
  eapply c3_iftab_tr; [exact HT | exact HP | exact MU | reflexivity | | | |].
  - eapply c3_dj_sub; [exact D3 | | |]; unfold NK_SIZE, NK_IF_NAME; lia.
  - eapply c3_dj_sub; [exact D3 | | |]; unfold NK_SIZE, NK_IF_NAME, NK_IF_INDEX; lia.
  - eapply c3_dj_sub; [exact D4 | | |]; unfold G_NAMES_SIZE, LONG_ALIAS_SIZE; lia.
  - eapply c3_dj_sub; [exact D2 | | |]; lia.
Qed.

Lemma c3t_mem_md : forall E P N kbs mbs gbs m, c3_mem E P N kbs mbs gbs m ->
  Z.of_nat (length mbs) = MD_SIZE /\ model_wf mbs.
Proof.
  intros E P N kbs mbs gbs m (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & L) & W & _). split; assumption.
Qed.

Lemma c3t_mem_inv : forall E P N kbs mbs gbs m, c3_mem E P N kbs mbs gbs m -> mem_inv rsegs m.
Proof.
  intros E P N kbs mbs gbs m (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _).
  exact H.
Qed.

(* ==========================================================================
   3. The model block after m->n_mark = 0, and the request check
   ========================================================================== *)

Lemma c3t_mbs1 : forall mbs, Z.of_nat (length mbs) = MD_SIZE -> model_wf mbs ->
  model_wf (upd_bytes mbs (Z.to_nat 8852) (le4 (Z_to_bv 64 0))) /\
  md_n_mark (upd_bytes mbs (Z.to_nat 8852) (le4 (Z_to_bv 64 0))) = 0 /\
  md_reqs (upd_bytes mbs (Z.to_nat 8852) (le4 (Z_to_bv 64 0))) = md_reqs mbs /\
  Z.of_nat (length (upd_bytes mbs (Z.to_nat 8852) (le4 (Z_to_bv 64 0)))) = MD_SIZE.
Proof.
  intros mbs HL HW.
  assert (Hk : (Z.to_nat 8852 + length (le4 (Z_to_bv 64 0)) <= length mbs)%nat)
    by (rewrite length_le4; unfold MD_SIZE in HL; lia).
  assert (O : forall off n, 0 <= off -> 0 <= n -> off + n <= 8852 ->
            link_spec.rdn (upd_bytes mbs (Z.to_nat 8852) (le4 (Z_to_bv 64 0))) off n = link_spec.rdn mbs off n).
  { intros off n H0 H1 H2. apply c3_rdn_upd_other; [exact Hk | lia | lia | left; lia]. }
  assert (Sl : forall off n, 0 <= off -> 0 <= n -> off + n <= 8852 ->
            slice (upd_bytes mbs (Z.to_nat 8852) (le4 (Z_to_bv 64 0))) off n = slice mbs off n).
  { intros off n H0 H1 H2. apply c3_slice_upd_other; [exact Hk | lia | lia | left; lia]. }
  assert (NM : md_n_mark (upd_bytes mbs (Z.to_nat 8852) (le4 (Z_to_bv 64 0))) = 0).
  { pose proof (c3_fld_u32_upd_same mbs (Z.to_nat 8852) (Z_to_bv 64 0) ltac:(rewrite length_le4 in Hk; exact Hk))
      as F.
    change (Z.of_nat (Z.to_nat 8852)) with 8852 in F. unfold md_n_mark, MD_N_MARK. rewrite F. reflexivity. }
  assert (NR : md_n_req (upd_bytes mbs (Z.to_nat 8852) (le4 (Z_to_bv 64 0))) = md_n_req mbs)
    by (unfold md_n_req, fld_u32, MD_N_REQ; apply O; lia).
  destruct HW as (W1 & W2 & W3 & W4 & W5 & W6). unfold NL_SENT_MAX in W1.
  assert (L64 : forall i, 0 <= i < md_n_req mbs ->
            fld_u64 (upd_bytes mbs (Z.to_nat 8852) (le4 (Z_to_bv 64 0))) (MD_REQ_LEN + 8 * i) =
            fld_u64 mbs (MD_REQ_LEN + 8 * i)).
  { intros i Hi. unfold fld_u64, MD_REQ_LEN. apply O; lia. }
  split; [|split; [exact NM | split]].
  - unfold model_wf. rewrite NR.
    assert (E1 : md_next (upd_bytes mbs (Z.to_nat 8852) (le4 (Z_to_bv 64 0))) = md_next mbs)
      by (unfold md_next, fld_u32, MD_NEXT; apply O; lia).
    assert (E2 : md_socket_errno (upd_bytes mbs (Z.to_nat 8852) (le4 (Z_to_bv 64 0))) = md_socket_errno mbs)
      by (unfold md_socket_errno, fld_u32, MD_SOCKET_ERRNO; apply O; lia).
    assert (E3 : md_send_errno (upd_bytes mbs (Z.to_nat 8852) (le4 (Z_to_bv 64 0))) = md_send_errno mbs)
      by (unfold md_send_errno, fld_u32, MD_SEND_ERRNO; apply O; lia).
    rewrite E1, E2, E3.
    split; [unfold NL_SENT_MAX; lia|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. split.
    + intros i Hi. rewrite (L64 i Hi). exact (W5 i Hi).
    + unfold model_marks_wf. rewrite NM. split; [unfold MARKS_MAX; lia|]. intros i Hi; lia.
  - unfold md_reqs. rewrite NR. apply map_ext_in. intros j Hj. apply in_seq in Hj.
    assert (Hj' : 0 <= Z.of_nat j < md_n_req mbs) by lia.
    unfold md_req_one. rewrite (L64 _ Hj'). pose proof (W5 _ Hj') as Hb.
    unfold MD_REQ_LEN, NL_SENT_LEN in *. apply Sl; unfold MD_REQ, NL_SENT_LEN; lia.
  - rewrite c3_upd_length by exact Hk. exact HL.
Qed.

Lemma c3t_nth_map_seq : forall {A : Type} (f : nat -> A) n k d, (k < n)%nat -> nth k (map f (seq 0 n)) d = f k.
Proof.
  intros A f n k d Hk. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; exact Hk).
  rewrite map_nth, seq_nth by exact Hk. reflexivity.
Qed.

Lemma c3t_requests : forall kbs mbs, nlk_wf kbs -> Z.of_nat (length kbs) = NK_SIZE -> model_wf mbs ->
  Z.of_nat (length mbs) = MD_SIZE -> nk_sent kbs = md_reqs mbs -> requests_are kbs mbs.
Proof.
  intros kbs mbs KW KL MW ML ES.
  destruct KW as (_ & _ & K3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & K13).
  destruct MW as (M1 & _ & _ & _ & M5 & _).
  unfold NL_SENT_MAX in K3, M1.
  assert (EN : nk_n_sent kbs = md_n_req mbs).
  { pose proof (f_equal (@length (list byte)) ES) as EL. unfold nk_sent, md_reqs in EL.
    rewrite !length_map, !length_seq in EL. lia. }
  split; [exact EN|]. intros i Hi.
  assert (Ei : nk_sent_one kbs i = md_req_one mbs i).
  { pose proof (f_equal (fun l => nth (Z.to_nat i) l []) ES) as E2. cbn beta in E2.
    unfold nk_sent, md_reqs in E2. rewrite !c3t_nth_map_seq in E2 by lia. cbn beta in E2.
    rewrite Z2Nat.id in E2 by lia. exact E2. }
  split; [|exact Ei].
  pose proof (K13 i Hi) as Bk. pose proof (M5 i ltac:(lia)) as Bm.
  assert (LK : length (nk_sent_one kbs i) = Z.to_nat (fld_u64 kbs (NK_SENT_LEN + 8 * i))).
  { unfold nk_sent_one, slice. rewrite length_firstn, length_skipn.
    unfold NK_SENT, NL_SENT_LEN, NK_SIZE, NK_CHUNK in *. lia. }
  assert (LM : length (md_req_one mbs i) = Z.to_nat (fld_u64 mbs (MD_REQ_LEN + 8 * i))).
  { unfold md_req_one, slice. rewrite length_firstn, length_skipn.
    unfold MD_REQ, NL_SENT_LEN, MD_SIZE in *. lia. }
  rewrite Ei in LK. rewrite LK in LM. unfold NL_SENT_LEN in *. lia.
Qed.

(* ==========================================================================
   4. The memory across each step of the tail
   ========================================================================== *)

(* m->n_mark = 0 *)
Lemma c3t_store : forall E P N kbs mbs gbs m, lenv_ok E -> c3_mem E P N kbs mbs gbs m ->
  c3_mem E P N kbs (upd_bytes mbs (Z.to_nat 8852) (le4 (Z_to_bv 64 0))) gbs
         (write_to_mem m (Z_to_bv 64 (e_md E + 8852)) (le4 (Z_to_bv 64 0))) /\
  wmono rsegs m (write_to_mem m (Z_to_bv 64 (e_md E + 8852)) (le4 (Z_to_bv 64 0))) /\
  store_ok rsegs m (Z_to_bv 64 (e_md E + 8852)) 4 = true.
Proof.
  intros E P N kbs mbs gbs m HE MEM.
  pose proof (c3t_env E HE) as V.
  pose proof (c3t_st_of _ _ _ _ _ _ _ MEM) as SST.
  destruct (c3t_mem_md _ _ _ _ _ _ _ MEM) as [ML MW].
  destruct (c3t_mbs1 mbs ML MW) as (MW1 & _ & _ & ML1).
  destruct MEM as (FR & SV & NK & NW & IT & GN & OD & PR & LA & TX & IP & MD & _ & MK & KW & CU & ER & GU & MI & TM & ST).
  destruct MD as [MDu _].
  assert (SO : store_ok rsegs m (Z_to_bv 64 (e_md E + 8852)) 4 = true).
  { apply (c3_u8arr_store_ok m (e_md E) mbs 8852 (e_md E + 8852) 4%nat MDu); [lia | rewrite ML; unfold MD_SIZE; lia | reflexivity]. }
  assert (MU1 : munch [(e_md E + 8852, e_md E + 8852 + 4)] m
                  (write_to_mem m (Z_to_bv 64 (e_md E + 8852)) (le4 (Z_to_bv 64 0)))).
  { apply (munch_write [(e_md E + 8852, e_md E + 8852 + 4)] m m (e_md E + 8852) (le4 (Z_to_bv 64 0)) (munch_refl _ m));
      rewrite ?length_le4; cbn [inside]; lia. }
  assert (WM1 : wmono rsegs m (write_to_mem m (Z_to_bv 64 (e_md E + 8852)) (le4 (Z_to_bv 64 0))))
    by exact (wmono_write rsegs m m _ _ (wmono_refl rsegs m)).
  assert (SST1 : c3t_st E P N (write_to_mem m (Z_to_bv 64 (e_md E + 8852)) (le4 (Z_to_bv 64 0)))).
  { eapply c3t_st_keep; [exact HE | exact SST | exact MU1 | exact WM1 | c3t_dj .. ]. }
  destruct SST1 as (FR1 & SV1 & GN1 & OD1 & PR1 & LA1 & TX1 & IP1 & CU1 & ER1 & GU1).
  split; [|split; [exact WM1 | exact SO]].
  refine (conj FR1 (conj SV1 (conj _ (conj NW (conj _ (conj GN1 (conj OD1 (conj PR1 (conj LA1 (conj TX1 (conj IP1
    (conj _ (conj MW1 (conj _ (conj KW (conj CU1 (conj ER1 (conj GU1 (conj _ (conj _ _)))))))))))))))))))).
  - destruct NK as [NKu NKl]. split; [|exact NKl].
    apply (u8arr_transport rsegs _ m _ A_G_NL kbs NKu MU1 WM1). rewrite NKl. c3t_dj.
  - eapply c3t_iftab_keep; [exact IT | exact IP | exact MU1 | c3t_dj | c3t_dj | c3t_dj].
  - split; [|exact ML1].
    apply (c3_u8arr_write m (e_md E) mbs 8852 (e_md E + 8852) (le4 (Z_to_bv 64 0)) MDu);
      [lia | rewrite length_le4, ML; unfold MD_SIZE; lia | reflexivity].
  - destruct MK as [MKu MKl]. split; [|exact MKl].
    apply (u8arr_transport rsegs _ m _ (e_mk E) gbs MKu MU1 WM1). rewrite MKl. c3t_dj.
  - apply (mem_inv_store rsegs m (Z_to_bv 64 (e_md E + 8852)) (le4 (Z_to_bv 64 0)) MI).
    rewrite length_le4. exact SO.
  - apply (c3_task_mem_munch _ m _ TM MU1). intros x Hx Ho. cbn [outside] in Ho. c3t_unf. lia.
  - apply (stk_write rsegs m _ _ (e_md E + 8852) (le4 (Z_to_bv 64 0)) ST); rewrite ?length_le4; lia.
Qed.

Lemma c3t_W_store : forall E m0 m, lenv_ok E -> munch (c3_W E) m0 m ->
  munch (c3_W E) m0 (write_to_mem m (Z_to_bv 64 (e_md E + 8852)) (le4 (Z_to_bv 64 0))).
Proof.
  intros E m0 m HE MU. pose proof (c3t_env E HE) as V.
  apply (munch_write (c3_W E) m0 m (e_md E + 8852) (le4 (Z_to_bv 64 0)) MU); rewrite ?length_le4; [lia | lia |].
  unfold c3_W. cbn [inside]. c3t_unf. lia.
Qed.

(* a call that writes only its own frame below sp = S - 480 *)
Lemma c3t_frame_mem : forall E P N kbs mbs gbs K m m',
  lenv_ok E -> 0 <= K <= 17232 -> c3_mem E P N kbs mbs gbs m ->
  munch [(e_S E - SLOT_FRAME - K, e_S E - SLOT_FRAME)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  stk rsegs m' (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME) -> c3_mem E P N kbs mbs gbs m'.
Proof.
  intros E P N kbs mbs gbs K m m' HE HK MEM MU WM MI' ST'.
  pose proof (c3t_env E HE) as V.
  pose proof (c3t_st_of _ _ _ _ _ _ _ MEM) as SST.
  destruct MEM as (FR & SV & NK & NW & IT & GN & OD & PR & LA & TX & IP & MD & MW & MK & KW & CU & ER & GU & MI & TM & ST).
  assert (SST1 : c3t_st E P N m') by (eapply c3t_st_keep; [exact HE | exact SST | exact MU | exact WM | c3t_dj .. ]).
  destruct SST1 as (FR1 & SV1 & GN1 & OD1 & PR1 & LA1 & TX1 & IP1 & CU1 & ER1 & GU1).
  refine (conj FR1 (conj SV1 (conj _ (conj NW (conj _ (conj GN1 (conj OD1 (conj PR1 (conj LA1 (conj TX1 (conj IP1
    (conj _ (conj MW (conj _ (conj KW (conj CU1 (conj ER1 (conj GU1 (conj MI' (conj _ ST')))))))))))))))))))).
  - destruct NK as [NKu NKl]. split; [|exact NKl].
    apply (u8arr_transport rsegs _ m _ A_G_NL kbs NKu MU WM). rewrite NKl. c3t_dj.
  - eapply c3t_iftab_keep; [exact IT | exact IP | exact MU | c3t_dj | c3t_dj | c3t_dj].
  - destruct MD as [MDu MDl]. split; [|exact MDl].
    apply (u8arr_transport rsegs _ m _ (e_md E) mbs MDu MU WM). rewrite MDl. c3t_dj.
  - destruct MK as [MKu MKl]. split; [|exact MKl].
    apply (u8arr_transport rsegs _ m _ (e_mk E) gbs MKu MU WM). rewrite MKl. c3t_dj.
  - apply (c3_task_mem_munch _ m _ TM MU). intros x Hx Ho. cbn [outside] in Ho. c3t_unfa. lia.
Qed.

Lemma c3t_W_frame : forall E K m0 m m', lenv_ok E -> 0 <= K <= 17232 -> munch (c3_W E) m0 m ->
  munch [(e_S E - SLOT_FRAME - K, e_S E - SLOT_FRAME)] m m' -> munch (c3_W E) m0 m'.
Proof.
  intros E K m0 m m' HE HK MU MU'. pose proof (c3t_env E HE) as V.
  eapply munch_extend; [exact MU | exact MU' |]. unfold sub_fp, c3_W. cbn [outside]. intros x Hx. c3t_unfa. lia.
Qed.

(* reac_served_unmark_all: its frame, the head of g_nl up to n_sent, errno, the marks block *)
Lemma c3t_unmark_mem : forall E P N kbs mbs gbs kbs' gbs' m m',
  lenv_ok E -> c3_mem E P N kbs mbs gbs m ->
  munch [(e_S E - SLOT_FRAME - 17232, e_S E - SLOT_FRAME); (A_G_NL, A_G_NL + NK_N_SENT + 4);
         (A_ERRNO, A_ERRNO + 4); (e_mk E, e_mk E + MK_SIZE)] m m' ->
  wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME) ->
  nlk_at m' kbs' -> nlk_wf kbs' -> iftab_at m' kbs' link_tab -> marks_at m' (e_mk E) gbs' -> marks_wf gbs' ->
  c3_mem E P N kbs' mbs gbs' m'.
Proof.
  intros E P N kbs mbs gbs kbs' gbs' m m' HE MEM MU WM MI' ST' NK' NW' IT' MK' KW'.
  pose proof (c3t_env E HE) as V.
  pose proof (c3t_st_of _ _ _ _ _ _ _ MEM) as SST.
  destruct MEM as (FR & SV & NK & NW & IT & GN & OD & PR & LA & TX & IP & MD & MW & MK & KW & CU & ER & GU & MI & TM & ST).
  assert (SST1 : c3t_st E P N m') by (eapply c3t_st_keep; [exact HE | exact SST | exact MU | exact WM | c3t_dj .. ]).
  destruct SST1 as (FR1 & SV1 & GN1 & OD1 & PR1 & LA1 & TX1 & IP1 & CU1 & ER1 & GU1).
  refine (conj FR1 (conj SV1 (conj NK' (conj NW' (conj IT' (conj GN1 (conj OD1 (conj PR1 (conj LA1 (conj TX1 (conj IP1
    (conj _ (conj MW (conj MK' (conj KW' (conj CU1 (conj ER1 (conj GU1 (conj MI' (conj _ ST')))))))))))))))))))).
  - destruct MD as [MDu MDl]. split; [|exact MDl].
    apply (u8arr_transport rsegs _ m _ (e_md E) mbs MDu MU WM). rewrite MDl. c3t_dj.
  - apply (c3_task_mem_munch _ m _ TM MU). intros x Hx Ho. cbn [outside] in Ho. c3t_unfa. lia.
Qed.

Lemma c3t_W_unmark : forall E m0 m m', lenv_ok E -> munch (c3_W E) m0 m ->
  munch [(e_S E - SLOT_FRAME - 17232, e_S E - SLOT_FRAME); (A_G_NL, A_G_NL + NK_N_SENT + 4);
         (A_ERRNO, A_ERRNO + 4); (e_mk E, e_mk E + MK_SIZE)] m m' -> munch (c3_W E) m0 m'.
Proof.
  intros E m0 m m' HE MU MU'. pose proof (c3t_env E HE) as V.
  eapply munch_extend; [exact MU | exact MU' |]. unfold sub_fp, c3_W. cbn [outside]. intros x Hx. c3t_unfa. lia.
Qed.

(* ==========================================================================
   5. The register file of a leaf contract, read on the canonical state
   ========================================================================== *)

Lemma c3t_errno_A : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6,
  errno_at (mkR ra sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
              t3 t4 t5 t6) = A_ERRNO.
Proof. intros. reflexivity. Qed.

Lemma c3t_arg0 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6,
  arg (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) 0 =
  bv_unsigned a0.
Proof. intros. reflexivity. Qed.

Lemma c3t_arg1 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6,
  arg (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) 1 =
  bv_unsigned a1.
Proof. intros. reflexivity. Qed.

Lemma c3t_spZ : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6,
  spZ (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) =
  bv_unsigned sp.
Proof. intros. reflexivity. Qed.

(* ==========================================================================
   6. The two ends
   ========================================================================== *)

Lemma c3t_lh : forall E i gp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 F fc m P N kbs mbs gbs,
  frm0 fc -> 0 <= i + 1 <= 47 -> 1 <= N ->
  c3_mem E P N kbs mbs gbs m -> nk_open kbs = 0 -> nk_misuse kbs = 0 -> nk_opened kbs = nk_closed kbs ->
  nk_opened kbs <= 64 * (i + 1) -> marks_are gbs mbs ->
  lh_ms E (i + 1) gp (MS (mkR ra (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40)
       a0 a1 a2 a3 a4 a5 a6 a7 (wz N) s3 s4 (wz 46) (wz A_JT) (wz (e_mk E)) (wz 0xab) (wz 4)
       (wz (e_md E + MD_N_REQ)) (wz (i + 1)) t3 t4 t5 t6) F (wz L_LH) fc None m (seg_rom rsegs)).
Proof.
  intros until gbs. intros FC Hi HN MEM H1 H2 H3 H4 MA.
  destruct MEM as ((j0 & j1 & j2 & FR) & SV & NK & NW & IT & GN & OD & PR & LA & TX & IP & MD & MW & MK & KW & CU & ER &
                   GU & MI & TM & ST).
  exists ra, t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, s3, s4, t3, t4, t5, t6, F, fc, m, P, N, kbs, mbs, gbs.
  split; [reflexivity|]. split; [exact FC|]. split; [exact Hi|]. split; [exact HN|].
  split; [|exact (conj MI (conj TM ST))].
  exact (conj (ex_intro _ j0 (ex_intro _ j1 (ex_intro _ j2 (ex_intro _ N FR))))
    (conj SV (conj NK (conj NW (conj IT (conj H1 (conj H2 (conj H3 (conj H4 (conj GN (conj OD (conj PR (conj LA
    (conj TX (conj IP (conj MD (conj MW (conj MK (conj KW (conj MA (conj CU (conj ER GU)))))))))))))))))))))).
Qed.

Lemma c3t_ex : forall E gp ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    P N kbs mbs gbs,
  frm0 fc -> c3_mem E P N kbs mbs gbs m ->
  ex_ms E gp (MS (mkR ra (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 (wz (e_mk E)) s8 s9 s10 s11 t3 t4 t5 t6) F (wz L_EXIT) fc None m (seg_rom rsegs)).
Proof.
  intros until gbs. intros FC MEM.
  destruct MEM as ((j0 & j1 & j2 & FR) & SV & _ & _ & _ & _ & _ & _ & LA & _ & _ & _ & _ & _ & _ & _ & ER & GU & MI &
                   TM & ST).
  destruct (rw_cells_forget rsegs _ _ _ FR) as (j & FJ).
  change (cells_size (lh_cells (e_md E) (e_mk E) P N j0 j1 j2)) with 376%nat in FJ.
  exists ra, t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, s1, s2, s3, s4, s5, s6, s8, s9, s10, s11, t3, t4, t5, t6,
    F, fc, m, j.
  split; [reflexivity|]. exact (conj FC (conj FJ (conj SV (conj ER (conj GU (conj LA (conj MI (conj TM ST)))))))).
Qed.

(* ==========================================================================
   7. The tail
   ========================================================================== *)

(* where an interface-table pointer of link_tab points: .rodata, g_names, or (as a Z the u64 cell only fixes
   mod 2^64) wholly below 0 or at or above 2^64 *)
Lemma c3t_name_where : forall m i n2 ix p, ifptrs_at m ->
  nth_error link_tab i = Some (n2, ix) -> u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
  (0x10000 <= p /\ p + Z.of_nat (length n2) + 1 <= 0x12000) \/
  (A_G_NAMES <= p /\ p + Z.of_nat (length n2) + 1 <= A_G_NAMES + G_NAMES_SIZE) \/
  p + Z.of_nat (length n2) + 1 <= 0 \/ 2 ^ 64 <= p.
Proof.
  intros m i n2 ix p HP Hn Hu.
  destruct (c3_link_tab_home i n2 ix Hn) as (Hi & Hhome).
  pose proof (c3_link_ptr_range i Hi) as Rq.
  pose proof (HP i Hi) as Hq.
  assert (Epq : Z_to_bv 64 p = Z_to_bv 64 (nth i link_ptrs 0)).
  { apply c3_le8_inj. unfold u64_at, wz in Hu, Hq.
    exact (c3_bytes_at_same _ _ _ _ Hu Hq ltac:(rewrite !length_le8; reflexivity)). }
  apply (f_equal bv_unsigned) in Epq.
  rewrite unsigned_lit_wrap, (unsigned_lit (nth i link_ptrs 0)) in Epq by (unfold A_G_NAMES, G_NAMES_SIZE in Rq; lia).
  set (q := nth i link_ptrs 0) in *. clearbody q.
  unfold A_G_NAMES, G_NAMES_SIZE in *.
  destruct (Z_lt_dec p 0) as [H|H].
  - right; right; left. assert (Hp : p <= q - 2 ^ 64) by (Z.div_mod_to_equations; nia). destruct Hhome; lia.
  - destruct (Z_le_dec (2 ^ 64) p) as [H'|H']; [right; right; right; exact H'|].
    rewrite Z.mod_small in Epq by lia. subst p. destruct Hhome as [Hh|Hh]; [right; left | left]; lia.
Qed.

Section C3Tail.
Hypothesis UNMARK_ALL_C : reac_served_unmark_all_contract.
Hypothesis CHECK_SOCKET_C : check_socket_contract.
Hypothesis CHECK_MARKS_C : check_marks_contract.
Hypothesis CHECK_REQUESTS_C : check_requests_contract.

Lemma c3_tail : forall (E : lenv) (i : Z) (gp : word) (m0 : word -> option byte) (ms : machine_state),
  lenv_ok E -> c3_ub E i gp m0 ms -> evt rsegs (eqv_cl (c3_post E i gp m0)) ms.
Proof.
  intros E i gp m0 ms HE HU.
  destruct HU as (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & t3 & t4 & t5 & t6 &
                  F & fc & m & P & N & kbs & mbs & gbs & -> & FC & Hi & MEM & KF & MA & RQ & MU & WM).
  pose proof (c3t_env E HE) as V.
  destruct (c3t_mem_md _ _ _ _ _ _ _ MEM) as [ML MW].
  destruct (c3t_mbs1 mbs ML MW) as (MW1 & NM1 & RQ1 & ML1).
  destruct (c3t_store E P N kbs mbs gbs m HE MEM) as (MEM1 & WMs & SO).
  pose proof (c3t_W_store E m0 m HE MU) as MU1.
  pose proof (wmono_trans rsegs _ _ _ WM WMs) as WM1.
  pose proof (c3t_mem_inv _ _ _ _ _ _ _ MEM) as MI.
  clear MU WM WMs.
  destruct KF as (K1 & K2 & K3 & K4 & K5).
  unfold c3_regs, wz, L3_UB, MD_N_REQ.
  remember (Z_to_bv 64 (e_S E - SLOT_FRAME)) as sp eqn:Esp.
  assert (HSP : bv_unsigned sp = e_S E - SLOT_FRAME) by (subst sp; apply unsigned_lit; unfold SLOT_FRAME; lia).
  (* 0x13bb8 sw zero, 0x204(s10); 0x13bbc mv a0, s7; 0x13bc0 jal reac_served_unmark_all *)
  step.
  set (mbs1 := upd_bytes mbs (Z.to_nat 8852) (le4 (Z_to_bv 64 0))) in *.
  set (m1 := write_to_mem m (Z_to_bv 64 (e_md E + 8852)) (le4 (Z_to_bv 64 0))) in *.
  clear MI SO MEM.
  step. step.
  pose proof MEM1 as (FR1 & SV1 & NK1 & NW1 & IT1 & GN1 & OD1 & PR1 & LA1 & TX1 & IP1 & MD1 & MWa & MK1 & KW1 & CU1 &
                      ER1 & GU1 & MI1 & TM1 & ST1).
  pose proof UNMARK_ALL_C as HL. unfold reac_served_unmark_all_contract in HL.
  eapply (leaf_run _ _ _ _ _ _ HL);
    [ | exact MI1 | rewrite HSP; exact ST1 | rewrite HSP; c3t_unf; lia | rewrite HSP; c3t_unf; lia | ].
  { cbv beta. exists kbs, link_tab.
    rewrite c3t_errno_A, c3t_arg0. unfold frame_apart_gnl, apart_frame, apart_gnl, apart.
    rewrite c3t_spZ, HSP. rewrite unsigned_lit by lia.
    refine (conj NK1 (conj _ (conj NW1 (conj K1 (conj _ (conj _ (conj IT1 (conj ER1 (conj _ (conj _ (conj _ _)))))))))));
      try (c3t_unf; lia).
    { (* the interface names (a Theorem Labs lane's gap 13): g_names or .rodata, apart from the stack window, g_nl,
         errno and the marks block *)
      intros i' n2 ix p Hn Hu. cbv zeta.
      pose proof (c3t_name_where m1 i' n2 ix p IP1 Hn Hu) as W.
      pose proof V as (VS & _ & _ & _ & Vk1 & Vk2 & Vki & _).
      clear - W VS Vk1 Vk2 Vki HSP. unfold A_G_NAMES, G_NAMES_SIZE in W. c3t_unf.
      repeat match goal with |- _ /\ _ => split end; try intros; lia. }
    intros _. split; [c3t_unf; lia|]. split; [c3t_unf; lia|]. split; [c3t_unf; lia|].
    exists gbs. exact (conj MK1 KW1). }
  intros regs2 m2 MU2 WM2 MI2 ST2 PO2.
  cbv beta in MU2, PO2.
  rewrite c3t_errno_A, c3t_arg0, HSP in MU2. rewrite unsigned_lit in MU2 by lia.
  rewrite (proj2 (Z.eqb_neq (e_mk E) 0)) in MU2 by lia. cbv iota in MU2.
  rewrite HSP in ST2.
  rewrite c3t_arg0 in PO2. rewrite unsigned_lit in PO2 by lia.
  destruct PO2 as [_ PO2].
  specialize (PO2 ltac:(lia) kbs link_tab gbs NK1 IT1 MK1). cbv zeta in PO2.
  destruct PO2 as ((gbs2 & MK2 & KW2 & KN2) &
                   (kbs2 & NK2 & NW2 & KC2 & KE2 & KI2 & IT2 & KX2 & KS2 & KL2 & KO2 & KM2 & KD2 & KR2)).
  pose proof (c3t_unmark_mem _ _ _ _ _ _ _ _ _ _ HE MEM1 MU2 WM2 MI2 ST2 NK2 NW2 IT2 MK2 KW2) as MEM2.
  pose proof (c3t_W_unmark E m0 m1 m2 HE MU1 MU2) as MU2'.
  pose proof (wmono_trans rsegs _ _ _ WM1 WM2) as WM2'.
  clear MU2 WM2 MU1 WM1 FR1 SV1 NK1 NW1 IT1 GN1 OD1 PR1 LA1 TX1 IP1 MD1 MWa MK1 KW1 CU1 ER1 GU1 MI1 TM1 ST1 MEM1.
  rewrite ret_pc_even by (first [lia | reflexivity]).
  (* 0x13bc4 jal check_socket *)
  step.
  pose proof CHECK_SOCKET_C as HS. unfold check_socket_contract in HS.
  eapply (leaf_run _ _ _ _ _ _ HS);
    [ | exact MI2 | rewrite HSP; exact ST2 | rewrite HSP; c3t_unf; lia | rewrite HSP; c3t_unf; lia | ].
  { cbv beta. exists kbs2. refine (conj NK2 (conj KO2 (conj _ _))); lia. }
  intros regs3 m3 MU3 WM3 MI3 ST3 PO3. cbv beta in PO3. unfold unchanged in PO3. subst m3.
  clear MU3 WM3 MI3 ST3.
  rewrite ret_pc_even by (first [lia | reflexivity]).
  (* 0x13bc8 j 0x13dc4; mv a0, s7; mv a1, s0; jal check_marks *)
  step. step. step. step.
  pose proof CHECK_MARKS_C as HM. unfold check_marks_contract in HM.
  eapply (leaf_run _ _ _ _ _ _ HM);
    [ | exact MI2 | rewrite HSP; exact ST2 | rewrite HSP; c3t_unf; lia | rewrite HSP; c3t_unf; lia | ].
  { cbv beta. exists gbs2, mbs1. rewrite c3t_arg0, c3t_arg1. rewrite !unsigned_lit by lia.
    unfold apart_frame. rewrite c3t_spZ, HSP.
    pose proof MEM2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MD2 & _).
    destruct MW1 as (_ & _ & _ & _ & _ & MM1).
    refine (conj MK2 (conj MD2 (conj KW2 (conj MM1 (conj _ (conj _ _)))))); [| c3t_unf; lia | c3t_unf; lia].
    split; [rewrite KN2, NM1; reflexivity|]. unfold mk_names, md_marks. rewrite KN2, NM1. reflexivity. }
  intros regs4 m4 MU4 WM4 MI4 ST4 PO4. clear PO4.
  cbv beta in MU4. unfold writes_nothing in MU4. rewrite HSP in MU4, ST4.
  pose proof (c3t_frame_mem _ _ _ _ _ _ 32 _ _ HE ltac:(lia) MEM2 MU4 WM4 MI4 ST4) as MEM4.
  pose proof (c3t_W_frame E 32 _ _ _ HE ltac:(lia) MU2' MU4) as MU4'.
  pose proof (wmono_trans rsegs _ _ _ WM2' WM4) as WM4'.
  clear MU4 WM4 MU2' WM2' MEM2 MI2 ST2.
  rewrite ret_pc_even by (first [lia | reflexivity]).
  (* 0x13dd0 mv a0, s0; jal check_requests *)
  step. step.
  pose proof CHECK_REQUESTS_C as HR. unfold check_requests_contract in HR.
  eapply (leaf_run _ _ _ _ _ _ HR);
    [ | exact MI4 | rewrite HSP; exact ST4 | rewrite HSP; c3t_unf; lia | rewrite HSP; c3t_unf; lia | ].
  { cbv beta. exists kbs2, mbs1. rewrite c3t_arg0. rewrite unsigned_lit by lia.
    unfold frame_apart_gnl, apart_frame, apart_gnl. rewrite c3t_spZ, HSP.
    pose proof MEM4 as (_ & _ & NK4 & _ & _ & _ & _ & _ & _ & _ & _ & MD4 & _).
    refine (conj NK4 (conj _ (conj MD4 (conj NW2 (conj MW1 (conj _ (conj _ _))))))); try (c3t_unf; lia).
    apply c3t_requests; [exact NW2 | exact (proj2 NK4) | exact MW1 | exact ML1 |].
    rewrite KS2, RQ1, RQ. reflexivity. }
  intros regs5 m5 MU5 WM5 MI5 ST5 PO5. clear PO5.
  cbv beta in MU5. unfold writes_nothing in MU5. rewrite HSP in MU5, ST5.
  pose proof (c3t_frame_mem _ _ _ _ _ _ 48 _ _ HE ltac:(lia) MEM4 MU5 WM5 MI5 ST5) as MEM5.
  pose proof (c3t_W_frame E 48 _ _ _ HE ltac:(lia) MU4' MU5) as MU5'.
  pose proof (wmono_trans rsegs _ _ _ WM4' WM5) as WM5'.
  clear MU5 WM5 MU4' WM4' MEM4 MI4 ST4.
  rewrite ret_pc_even by (first [lia | reflexivity]).
  (* 0x13dd8 bltu s5, s11, 0x1413c *)
  step.
  destruct (Z_lt_ge_dec 46 i) as [Hgt|Hle].
  { (* operation 47 done: 0x1413c, the exit *)
    replace (bv_ltu (Z_to_bv 64 46) (Z_to_bv 64 i)) with true
      by (symmetry; unfold bv_ltu; rewrite !unsigned_lit by lia; apply Z.ltb_lt; lia).
    cbv iota. subst sp.
    apply evt_eqv_done. split; [right | ].
    - eapply c3t_ex; [exact FC | exact MEM5].
    - apply c3_seg_fp; assumption. }
  replace (bv_ltu (Z_to_bv 64 46) (Z_to_bv 64 i)) with false
    by (symmetry; unfold bv_ltu; rewrite !unsigned_lit by lia; apply Z.ltb_ge; lia).
  cbv iota.
  (* 0x13ddc j 0x1406c; ld s2, 0x48(sp); addiw s11, s11, 1; bnez s2, 0x13a1c *)
  step.
  pose proof MEM5 as ((j0 & j1 & j2 & FR5) & _).
  rewrite <- HSP in FR5. unfold lh_cells, wz in FR5.
  step. step. step.
  replace (bv_swrap 32 (bv_unsigned (Z_to_bv 64 i) + 1)) with (i + 1)
    by (rewrite unsigned_lit by lia; symmetry; apply bv_swrap_small; change (bv_half_modulus 32) with (2 ^ 31); lia).
  pose proof MEM5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & kc & Hkc & _ & HN) & _).
  assert (MA2 : marks_are gbs2 mbs1).
  { split; [rewrite KN2, NM1; reflexivity|]. unfold mk_names, md_marks. rewrite KN2, NM1. reflexivity. }
  destruct (Z.eq_dec N 0) as [HN0|HN0].
  { (* the input is used up: 0x14078 j 0x1413c, the exit *)
    replace (negb (bv_eqb (Z_to_bv 64 N) (Z_to_bv 64 0))) with false by (rewrite HN0; reflexivity).
    cbv iota. step. subst sp.
    apply evt_eqv_done. split; [right | ].
    - eapply c3t_ex; [exact FC | exact MEM5].
    - apply c3_seg_fp; assumption. }
  (* 0x13a1c, the loop head of operation i + 1 *)
  replace (negb (bv_eqb (Z_to_bv 64 N) (Z_to_bv 64 0))) with true
    by (symmetry; apply negb_true_iff; unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; exact HN0).
  cbv iota. subst sp.
  apply evt_eqv_done. split; [left; split; [lia|] | ].
  - unfold MARKS_MAX in KR2.
    eapply c3t_lh; [exact FC | lia | lia | exact MEM5 | exact KO2 | lia | lia | lia | exact MA2].
  - apply c3_seg_fp; assumption.
Qed.
End C3Tail.

About c3_tail.
Print Assumptions c3_tail.
