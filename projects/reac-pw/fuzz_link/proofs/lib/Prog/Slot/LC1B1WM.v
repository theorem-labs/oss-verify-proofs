(* The slot LLVMFuzzerTestOneInput, plain image, op_write arm, segment B1: the call of model_write at 0x13ff4
   (entry 0x15c50, ra 0x13ff8, model_write_c.v, leaf K 704), a0 = md, a1 = name_of's answer, a2 = the alias.
   - c1b1_mwpre: model_write's Pre from the loop memory after model_begin (the name: g_names or odd, NULL for
     selector 255; the alias: al_ok);
   - c1b1_mwpost: its Post at link_tab, the selector's name and the alias, on the state model_begin left
     (no requests, the fake kernel's kstate), and its footprint (its frame and the model block). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem kernel_c model_write_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC1Defs LC1Call LC1B1Lib.
Local Open Scope Z_scope.

Lemma c1b1_alias_arg : forall E m s t sl, al_ok E m s t sl ->
  str_arg m s (Some t) /\
  exists slack, bytes_at rsegs m (s + Z.of_nat (length t) + 1) slack /\
    (- (s + Z.of_nat (length t) + 1)) mod 8 <= Z.of_nat (length slack).
Proof.
  intros E m s t sl (A1 & A2 & A3 & A4 & A5 & _).
  assert (A2' : bytes_at rsegs m s ((t ++ [zb 0]) ++ sl)) by (rewrite <- app_assoc; exact A2).
  apply bytes_at_app in A2'. destruct A2' as [B1 B2].
  split; [split; [exact A1 | split; [exact B1 | exact A3]]|].
  exists sl. split.
  - replace (s + Z.of_nat (length t) + 1) with (s + Z.of_nat (length (t ++ [zb 0])))
      by (rewrite length_app; cbn [length]; lia). exact B2.
  - rewrite A5. apply Z.le_refl.
Qed.

Lemma c1b1_mwpre : forall E i P N kbs mbs gbs m nb s t sl regs,
  lenv_ok E -> lh_mem E i P N kbs mbs gbs m -> 0 <= nb < 256 -> al_ok E m s t sl ->
  spZ regs = e_S E - SLOT_FRAME -> arg regs 0 = e_md E -> arg regs 1 = sel_ptr nb -> arg regs 2 = s ->
  c1b1_mP regs m.
Proof.
  intros E i P N kbs mbs gbs m nb s t sl regs HE HL Hnb HA HSP HA0 HA1 HA2.
  destruct (c1b1_lenv E HE) as (S1 & S2 & M1 & M2 & M3 & _).
  destruct (c1b1_lh_split _ _ _ _ _ _ _ _ HL) as (ST & _ & NK & NW & IT & _ & _ & _ & _ & _ & MD & MW & _).
  destruct ST as (_ & _ & _ & GN & OD & _ & _ & IP & _).
  destruct (c1b1_sel m nb Hnb GN OD) as (SA & SB & SC).
  destruct (c1b1_alias_arg E m s t sl HA) as (SAl & slack & SLB & SLM).
  pose proof HA as (A1 & A2 & A3 & A4 & A5 & A6 & _).
  unfold c1b1_mP. cbv beta.
  exists mbs, kbs, link_tab, (sel_name nb), (Some t).
  unfold apart_frame, frame_apart_gnl, apart_gnl. rewrite HSP, HA0, HA1, HA2.
  unfold SLOT_FRAME, A_G_NL, NK_SIZE, MD_SIZE in *.
  split; [exact MD|]. split; [exact MW|]. split; [exact NK|].
  split; [lia|].
  split; [exact NW|]. split; [exact IT|]. split; [exact SA|]. split; [exact SAl|].
  split; [lia|].
  split; [lia|].
  split; [intros s' Hs'; destruct (SC s' Hs'); lia|].
  split.
  { intros s' Hs'. assert (Es : s' = t) by congruence. subst s'.
    unfold apart, SLOT_STACK_Z in A6. lia. }
  split.
  { intros s' Hs'. assert (Es : s' = t) by congruence. subst s'. exists slack. exact (conj SLB SLM). }
  intros j n2 ix p Hn U.
  assert (Hj : (j < 64)%nat) by (pose proof (nth_error_lt _ _ _ Hn) as Hl; rewrite c1b1_link_len in Hl; exact Hl).
  pose proof (c1b1_nth_error_nth link_tab j ([], 0) ltac:(rewrite c1b1_link_len; exact Hj)) as Hl.
  rewrite Hn in Hl.
  assert (En2 : n2 = fst (nth j link_tab ([], 0))) by (change n2 with (fst (n2, ix)); congruence).
  pose proof (c1b1_link_bnd j Hj) as B. rewrite <- En2 in B.
  destruct (c1b1_wz_eq p _ (c1b1_u64_eq _ _ _ _ U (IP j Hj)) ltac:(lia)) as [q Hq].
  lia.
Qed.

Lemma c1b1_mwpost : forall E i P N kbs mbs gbs m m' nb s t sl own m0 regs regs' sp0,
  lenv_ok E -> lh_mem E i P N kbs mbs gbs m -> 0 <= nb < 256 ->
  md_reqs mbs = [] -> md_kstate mbs kbs = nk_kstate kbs ->
  rw_cells rsegs m (e_S E - SLOT_FRAME + FO_P) [C8 (wz P); C8 (wz N)] ->
  bytes_at rsegs m (e_S E - SLOT_FRAME + FO_B256) (le8 (wz own)) ->
  al_ok E m s t sl -> MemNorm.task_mem rsegs m -> seg_fp (e_S E) (c1_hp E) m0 m ->
  sp0 = e_S E - SLOT_FRAME -> arg regs 0 = e_md E -> arg regs 1 = sel_ptr nb -> arg regs 2 = s ->
  c1b1_mQ regs m regs' m' ->
  munch ((sp0 - 704, sp0) :: c1b1_mW regs m) m m' -> wmono rsegs m m' ->
  exists mbs', getr regs' 10 = wz (w_rc (c1_wm nb t kbs)) /\ lh_mem E i P N kbs mbs' gbs m' /\
    md_reqs mbs' = w_reqs (c1_wm nb t kbs) /\
    md_n_req mbs' = Z.of_nat (length (w_reqs (c1_wm nb t kbs))) /\
    rw_cells rsegs m' (e_S E - SLOT_FRAME + FO_P) [C8 (wz P); C8 (wz N)] /\
    bytes_at rsegs m' (e_S E - SLOT_FRAME + FO_B256) (le8 (wz own)) /\
    al_ok E m' s t sl /\ MemNorm.task_mem rsegs m' /\ seg_fp (e_S E) (c1_hp E) m0 m'.
Proof.
  intros E i P N kbs mbs gbs m m' nb s t sl own m0 regs regs' sp0 HE HL Hnb ER EK HC HO HA HT HF Esp HA0 HA1 HA2
    PO MU WM.
  subst sp0.
  destruct (c1b1_lenv E HE) as (S1 & S2 & M1 & M2 & M3 & _).
  destruct (c1b1_lh_split _ _ _ _ _ _ _ _ HL)
    as (ST & _ & NK & NW & IT & O1 & O2 & O3 & O4 & LA & MD & MW & KW & MA & K).
  pose proof ST as ST0. destruct ST0 as (_ & _ & _ & GN & OD & _ & _ & IP & _).
  destruct (c1b1_sel m nb Hnb GN OD) as (SA & SB & SC).
  destruct (c1b1_alias_arg E m s t sl HA) as (SAl & _).
  unfold c1b1_mQ in PO. cbv beta in PO. rewrite HA0, HA1, HA2 in PO.
  specialize (PO mbs kbs link_tab (sel_name nb) (Some t) MD NK IT SA SAl).
  cbv zeta in PO.
  destruct PO as (R10 & mbs' & MD' & MW' & _ & _ & _ & RQ & NRQ & NM & MM).
  rewrite ER, EK in R10, RQ, NRQ.
  unfold c1b1_mW in MU. cbv beta in MU. rewrite HA0 in MU.
  lazymatch type of MU with munch ?W _ _ => assert (WK : c1b1_wok E W) end.
  { intros x Hx HO'. cbn [outside] in HO'. unfold c1b1_al. unfold SLOT_FRAME, MD_SIZE in *. lia. }
  lazymatch type of MU with munch ?W0 _ _ => set (W := W0) in * end.
  assert (CL1 : c1b1_clr W 474672 968) by (intros x Hx; unfold W; cbn [outside]; unfold SLOT_FRAME, MD_SIZE; lia).
  assert (CL2 : c1b1_clr W 65536 8000) by (intros x Hx; unfold W; cbn [outside]; unfold SLOT_FRAME, MD_SIZE; lia).
  assert (CL3 : c1b1_clr W 475640 512) by (intros x Hx; unfold W; cbn [outside]; unfold SLOT_FRAME, MD_SIZE; lia).
  exists mbs'.
  refine (conj R10 (conj _ (conj RQ (conj NRQ (conj _ (conj _ (conj _ (conj _ _)))))))).
  - apply c1b1_lh_join.
    + exact (c1b1_static_tr E gbs m m' W HE ST MU WM WK).
    + exists N. eapply c1b1_rw_tr; [exact HC | exact MU | exact WM |].
      change (Z.of_nat (cells_size [C8 (wz P); C8 (wz N)])) with 16.
      intros x Hx. unfold W. cbn [outside]. unfold SLOT_FRAME, FO_P, MD_SIZE in *. lia.
    + destruct NK as [NKu NKl]. split; [|exact NKl]. eapply c1b1_u8_tr; [exact NKu | exact MU | exact WM |].
      rewrite NKl. intros x Hx. unfold W. cbn [outside]. unfold SLOT_FRAME, MD_SIZE, A_G_NL, NK_SIZE in *. lia.
    + exact NW.
    + exact (c1b1_iftab_tr W m m' kbs kbs IT IP MU CL1 CL2 CL3 eq_refl).
    + exact O1.
    + exact O2.
    + exact O3.
    + exact O4.
    + destruct LA as [la LA]. exists la. eapply c1b1_rw_tr; [exact LA | exact MU | exact WM |].
      change (Z.of_nat (cells_size [CB (Z.to_nat 300) la; C1 (zb 0)])) with 301.
      intros x Hx. unfold W. cbn [outside]. unfold SLOT_FRAME, MD_SIZE, A_LONG_ALIAS in *. lia.
    + exact MD'.
    + exact MW'.
    + exact KW.
    + unfold marks_are in *. rewrite NM, MM. exact MA.
    + exact K.
  - eapply c1b1_rw_tr; [exact HC | exact MU | exact WM |].
    change (Z.of_nat (cells_size [C8 (wz P); C8 (wz N)])) with 16.
    intros x Hx. unfold W. cbn [outside]. unfold SLOT_FRAME, FO_P, MD_SIZE in *. lia.
  - exact (c1b1_own_tr E m m' W own HE HO MU WK).
  - exact (c1b1_alok_tr E m m' W s t sl HA MU WK).
  - exact (c1b1_task E W m m' HE HT MU WK).
  - exact (c1b1_segfp E W m0 m m' HF MU WM WK).
Qed.
