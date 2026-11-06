(* The slot LLVMFuzzerTestOneInput, plain image, op_write arm, segment B1: the memory after the inlined
   model_begin (fuzz_link.c:668-675) and g_nl.n_sent = 0, 0x13fc4-0x13fe4:
     md->socket_errno = g_nl.socket_errno, md->next = 0, md->send_errno = g_nl.send_errno, md->n_req = 0
     (stores at md + 0 / 8 / 4 / 8336), g_nl.n_sent = 0 (store at g_nl + 271016 = 474664).
   The model block and g_nl are rebuilt from the stored cells and every byte the stores missed; the loop
   memory holds again with the new kbs / mbs, n_sent = 0, no requests, and the model's kstate the fake
   kernel's (talk then runs on the state nl_talk runs on). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem kernel_c model_write_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC1Defs LC1Call LC1B1Lib.
Local Open Scope Z_scope.

Lemma c1b1_begin_mem : forall E i P N kbs mbs gbs mk m own s t sl m0 (c d e : word),
  lenv_ok E -> lh_mem E i P N kbs mbs gbs mk -> nk_next kbs = 0 ->
  rw_cells rsegs m (e_S E - SLOT_FRAME + FO_P) [C8 (wz P); C8 (wz N)] ->
  bytes_at rsegs mk (e_S E - SLOT_FRAME + FO_B256) (le8 (wz own)) -> al_ok E mk s t sl ->
  MemNorm.task_mem rsegs mk -> seg_fp (e_S E) (c1_hp E) m0 mk ->
  munch [(e_md E, e_md E + 12); (e_md E + 8336, e_md E + 8336 + 4); (474664, 474664 + 4)] mk m ->
  wmono rsegs mk m ->
  rw_cells rsegs m (e_md E) [C4 (wz (nk_socket_errno kbs)); C4 (wz (nk_send_errno kbs)); C4 c] ->
  rw_cells rsegs m (e_md E + 8336) [C4 d] -> rw_cells rsegs m 474664 [C4 e] ->
  bv_unsigned c mod 2 ^ 32 = 0 -> bv_unsigned d mod 2 ^ 32 = 0 -> bv_unsigned e mod 2 ^ 32 = 0 ->
  exists kbs' mbs', lh_mem E i P N kbs' mbs' gbs m /\ nk_n_sent kbs' = 0 /\ md_reqs mbs' = [] /\
    md_kstate mbs' kbs' = nk_kstate kbs' /\ nk_opened kbs' = nk_opened kbs /\
    bytes_at rsegs m (e_S E - SLOT_FRAME + FO_B256) (le8 (wz own)) /\ al_ok E m s t sl /\
    MemNorm.task_mem rsegs m /\ seg_fp (e_S E) (c1_hp E) m0 m.
Proof.
  intros E i P N kbs mbs gbs mk m own s t sl m0 c d e HE HL NX HC HO HA HT HF MU WM HM1 HM2 HNS Hc Hd He.
  destruct (c1b1_lenv E HE) as (S1 & S2 & M1 & M2 & M3 & _).
  destruct (c1b1_lh_split _ _ _ _ _ _ _ _ HL)
    as (ST & _ & NK & NW & IT & O1 & O2 & O3 & O4 & LA & MD & MW & KW & MA & K).
  pose proof ST as ST0. destruct ST0 as (_ & _ & _ & _ & _ & _ & _ & IP & _).
  set (W := [(e_md E, e_md E + 12); (e_md E + 8336, e_md E + 8336 + 4); (474664, 474664 + 4)]) in MU.
  assert (WK : c1b1_wok E W).
  { intros x Hx HO'. unfold W in HO'. cbn [outside] in HO'. unfold c1b1_al. lia. }
  destruct HM1 as [[_ B1] _]. cbn [cells_bytes cbytes] in B1. rewrite app_nil_r in B1.
  destruct HM2 as [[_ B2] _]. cbn [cells_bytes cbytes] in B2. rewrite app_nil_r in B2.
  destruct HNS as [[_ B3] _]. cbn [cells_bytes cbytes] in B3. rewrite app_nil_r in B3.
  destruct NK as [NKu NKl]. destruct MD as [MDu MDl].
  unfold NK_SIZE in NKl. unfold MD_SIZE in MDl.
  pose proof NW as NW0.
  destruct NW0 as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13).
  (* the two blocks after the stores *)
  assert (NK' : u8arr rsegs m A_G_NL (upd_bytes kbs (Z.to_nat 271016) (le4 e))).
  { eapply (c1b1_u8_patch1 W mk m A_G_NL kbs 271016 (le4 e) 474664);
      [exact NKu | exact MU | exact WM | exact B3 | reflexivity | lia | rewrite length_le4; lia |].
    intros y Hy Hn. unfold W. cbn [outside]. rewrite length_le4 in Hn. unfold A_G_NL in *. lia. }
  set (x1 := le4 (wz (nk_socket_errno kbs)) ++ le4 (wz (nk_send_errno kbs)) ++ le4 c) in *.
  assert (LX1 : length x1 = 12%nat) by (unfold x1; rewrite !length_app, !length_le4; reflexivity).
  assert (MD' : u8arr rsegs m (e_md E) (upd_bytes (upd_bytes mbs (Z.to_nat 0) x1) (Z.to_nat 8336) (le4 d))).
  { eapply (c1b1_u8_patch2 W mk m (e_md E) mbs 0 x1 8336 (le4 d) (e_md E) (e_md E + 8336));
      [exact MDu | exact MU | exact WM | exact B1 | exact B2 | lia | reflexivity | lia | | |].
    - rewrite LX1. lia.
    - rewrite length_le4. lia.
    - intros y Hy H1 H2. unfold W. cbn [outside]. rewrite LX1 in H1. rewrite length_le4 in H2. lia. }
  set (kbs' := upd_bytes kbs (Z.to_nat 271016) (le4 e)) in *.
  set (mb1 := upd_bytes mbs (Z.to_nat 0) x1) in *.
  set (mbs' := upd_bytes mb1 (Z.to_nat 8336) (le4 d)) in *.
  assert (LK : length kbs' = length kbs) by (unfold kbs'; apply upd_bytes_length; rewrite length_le4; lia).
  assert (LM1 : length mb1 = length mbs) by (unfold mb1; apply upd_bytes_length; rewrite LX1; lia).
  assert (LM : length mbs' = length mbs) by (unfold mbs'; rewrite upd_bytes_length; [exact LM1 | rewrite LM1, length_le4; lia]).
  (* the fields of the fake kernel *)
  assert (FK : forall a n, 0 <= a -> 0 <= n -> a + n <= 271016 \/ 271020 <= a ->
             link_spec.rdn kbs' a n = link_spec.rdn kbs a n).
  { intros a n Ha Hn Hd'. unfold kbs'. apply c1b1_rdn_upd_out; [lia | lia | rewrite length_le4; lia |].
    rewrite length_le4. lia. }
  assert (ESN : nk_n_sent kbs' = 0).
  { unfold nk_n_sent, fld_u32, NK_N_SENT. unfold kbs'.
    rewrite c1b1_rdn_upd_in by (rewrite ?length_le4; lia).
    replace (271016 - Z.of_nat (Z.to_nat 271016)) with 0 by lia. rewrite c1b1_rdn_le4_0. exact He. }
  assert (E_nch : nk_n_chunks kbs' = nk_n_chunks kbs) by (unfold nk_n_chunks, fld_u32, NK_N_CHUNKS; apply FK; lia).
  assert (E_next : nk_next kbs' = nk_next kbs) by (unfold nk_next, fld_u32, NK_NEXT; apply FK; lia).
  assert (E_nif : nk_n_if kbs' = nk_n_if kbs) by (unfold nk_n_if, fld_u32, NK_N_IF; apply FK; lia).
  assert (E_open : nk_open kbs' = nk_open kbs) by (unfold nk_open, fld_u32, NK_OPEN; apply FK; lia).
  assert (E_opened : nk_opened kbs' = nk_opened kbs) by (unfold nk_opened, fld_u32, NK_OPENED; apply FK; lia).
  assert (E_closed : nk_closed kbs' = nk_closed kbs) by (unfold nk_closed, fld_u32, NK_CLOSED; apply FK; lia).
  assert (E_misuse : nk_misuse kbs' = nk_misuse kbs) by (unfold nk_misuse, fld_u32, NK_MISUSE; apply FK; lia).
  assert (E_end : nk_end_errno kbs' = nk_end_errno kbs) by (unfold nk_end_errno, fld_u32, NK_END_ERRNO; apply FK; lia).
  assert (E_sock : nk_socket_errno kbs' = nk_socket_errno kbs)
    by (unfold nk_socket_errno, fld_u32, NK_SOCKET_ERRNO; apply FK; lia).
  assert (E_send : nk_send_errno kbs' = nk_send_errno kbs)
    by (unfold nk_send_errno, fld_u32, NK_SEND_ERRNO; apply FK; lia).
  assert (NW' : nlk_wf kbs').
  { unfold nlk_wf. rewrite E_nch, E_next, ESN, E_nif, E_open, E_opened, E_closed, E_misuse, E_end, E_sock, E_send.
    refine (conj W1 (conj W2 (conj _ (conj W4 (conj W5 (conj W6 (conj W7 (conj W8 (conj W9 (conj W10
      (conj W11 (conj _ _)))))))))))).
    - lia.
    - intros j Hj. unfold NL_CHUNKS in W1. unfold NK_CHUNK_LEN in *.
      replace (fld_u64 kbs' (262144 + 8 * j)) with (fld_u64 kbs (262144 + 8 * j))
        by (unfold fld_u64; symmetry; apply FK; lia).
      apply W12. exact Hj.
    - intros j Hj. lia. }
  (* the fields of the model *)
  assert (FM : forall a n, 0 <= a -> 0 <= n -> 12 <= a -> a + n <= 8336 \/ 8340 <= a ->
             link_spec.rdn mbs' a n = link_spec.rdn mbs a n).
  { intros a n Ha Hn H12 Hd'. unfold mbs'.
    rewrite c1b1_rdn_upd_out by (rewrite ?LM1, ?length_le4; lia).
    unfold mb1. rewrite c1b1_rdn_upd_out by (rewrite ?LX1; lia). reflexivity. }
  assert (FS : forall a n, 0 <= a -> 0 <= n -> 12 <= a -> a + n <= 8336 \/ 8340 <= a ->
             slice mbs' a n = slice mbs a n).
  { intros a n Ha Hn H12 Hd'. unfold mbs'.
    rewrite c1b1_slice_upd_out by (rewrite ?LM1, ?length_le4; lia).
    unfold mb1. rewrite c1b1_slice_upd_out by (rewrite ?LX1; lia). reflexivity. }
  assert (E_msock : md_socket_errno mbs' = nk_socket_errno kbs).
  { unfold md_socket_errno, fld_u32, MD_SOCKET_ERRNO. unfold mbs'.
    rewrite c1b1_rdn_upd_out by (rewrite ?LM1, ?length_le4; lia).
    unfold mb1. rewrite c1b1_rdn_upd_in by (rewrite ?LX1; lia).
    replace (0 - Z.of_nat (Z.to_nat 0)) with 0 by lia. unfold x1.
    rewrite c1b1_rdn_le4_head by reflexivity. rewrite unsigned_lit by lia. apply Z.mod_small. lia. }
  assert (E_msend : md_send_errno mbs' = nk_send_errno kbs).
  { unfold md_send_errno, fld_u32, MD_SEND_ERRNO. unfold mbs'.
    rewrite c1b1_rdn_upd_out by (rewrite ?LM1, ?length_le4; lia).
    unfold mb1. rewrite c1b1_rdn_upd_in by (rewrite ?LX1; lia).
    replace (4 - Z.of_nat (Z.to_nat 0)) with 4 by lia. unfold x1.
    rewrite c1b1_rdn_le4_cons by lia. rewrite c1b1_rdn_le4_head by lia.
    rewrite unsigned_lit by lia. apply Z.mod_small. lia. }
  assert (E_mnext : md_next mbs' = 0).
  { unfold md_next, fld_u32, MD_NEXT. unfold mbs'.
    rewrite c1b1_rdn_upd_out by (rewrite ?LM1, ?length_le4; lia).
    unfold mb1. rewrite c1b1_rdn_upd_in by (rewrite ?LX1; lia).
    replace (8 - Z.of_nat (Z.to_nat 0)) with 8 by lia. unfold x1.
    rewrite c1b1_rdn_le4_cons by lia. rewrite c1b1_rdn_le4_cons by lia.
    replace (8 - 4 - 4) with 0 by lia. rewrite c1b1_rdn_le4_0. exact Hc. }
  assert (E_nreq : md_n_req mbs' = 0).
  { unfold md_n_req, fld_u32, MD_N_REQ. unfold mbs'.
    rewrite c1b1_rdn_upd_in by (rewrite ?LM1, ?length_le4; lia).
    replace (8336 - Z.of_nat (Z.to_nat 8336)) with 0 by lia. rewrite c1b1_rdn_le4_0. exact Hd. }
  assert (E_nmark : md_n_mark mbs' = md_n_mark mbs) by (unfold md_n_mark, fld_u32, MD_N_MARK; apply FM; lia).
  destruct MW as (MW1 & MW2 & MW3 & MW4 & MW5 & MM1 & MM2).
  assert (E_marks : md_marks mbs' = md_marks mbs).
  { unfold md_marks. rewrite E_nmark. apply map_ext_in. intros j Hj. apply in_seq in Hj.
    f_equal. apply FS; unfold MD_MARK, MARK_LEN; lia. }
  assert (MW' : model_wf mbs').
  { unfold model_wf. rewrite E_nreq, E_mnext, E_msock, E_msend.
    refine (conj _ (conj _ (conj W10 (conj W11 (conj _ _))))).
    - lia.
    - lia.
    - intros j Hj. lia.
    - unfold model_marks_wf. rewrite E_nmark. split; [exact MM1|].
      intros j Hj. unfold MD_MARK, MARK_LEN in *. rewrite FS by lia. apply MM2. exact Hj. }
  (* the transports *)
  assert (CL1 : c1b1_clr W 474672 968) by (intros x Hx; unfold W; cbn [outside]; lia).
  assert (CL2 : c1b1_clr W 65536 8000) by (intros x Hx; unfold W; cbn [outside]; lia).
  assert (CL3 : c1b1_clr W 475640 512) by (intros x Hx; unfold W; cbn [outside]; lia).
  exists kbs', mbs'.
  refine (conj _ (conj ESN (conj _ (conj _ (conj E_opened (conj _ (conj _ (conj _ _)))))))).
  - apply c1b1_lh_join.
    + exact (c1b1_static_tr E gbs mk m W HE ST MU WM WK).
    + exists N. exact HC.
    + split; [exact NK' | rewrite LK, NKl; reflexivity].
    + exact NW'.
    + exact (c1b1_iftab_tr W mk m kbs kbs' IT IP MU CL1 CL2 CL3 E_nif).
    + rewrite E_open. exact O1.
    + rewrite E_misuse. exact O2.
    + rewrite E_opened, E_closed. exact O3.
    + rewrite E_opened. exact O4.
    + destruct LA as [la LA]. exists la. eapply c1b1_rw_tr; [exact LA | exact MU | exact WM |].
      change (Z.of_nat (cells_size [CB (Z.to_nat 300) la; C1 (zb 0)])) with 301.
      intros x Hx. unfold W. cbn [outside]. unfold A_LONG_ALIAS in Hx. lia.
    + split; [exact MD' | rewrite LM, MDl; reflexivity].
    + exact MW'.
    + exact KW.
    + unfold marks_are in *. rewrite E_nmark, E_marks. exact MA.
    + exact K.
  - unfold md_reqs. rewrite E_nreq. reflexivity.
  - unfold md_kstate, nk_kstate. rewrite E_mnext, E_msock, E_msend, E_next, E_sock, E_send, NX. reflexivity.
  - exact (c1b1_own_tr E mk m W own HE HO MU WK).
  - exact (c1b1_alok_tr E mk m W s t sl HA MU WK).
  - exact (c1b1_task E W mk m HE HT MU WK).
  - exact (c1b1_segfp E W m0 mk m HF MU WM WK).
Qed.
