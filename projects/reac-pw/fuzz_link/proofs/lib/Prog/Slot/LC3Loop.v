(* The op_unmark arm (c3) of LLVMFuzzerTestOneInput, plain image: the inlined model_unmark loop
   (fuzz_link.c:462-473, listing 0x13b4c-0x13bb4), from c3_mb (0x13b4c) to c3_ub (0x13bb8).
     0x13b4c  lw a0, 0x204(s10)    m->n_mark; blez -> 0x13bb8
     0x13b54  s3 = 0; s2 = &m->mark[0] (frame cell FO_MARK0)
     0x13b5c  model_read (m, s2, NULL, 0, sp + 0x78, 256); bnez -> 0x13ba8
     0x13b7c  bcmp (sp + 0x78, "reac-pw:served", 15); bnez -> 0x13ba8
     0x13b94  model_write (m, s2, "")
     0x13ba8  lw a0, m->n_mark; s3 += 1; s2 += 16; blt s3, a0 -> 0x13b5c, else 0x13bb8
   Each round is one step of link_spec `unmark_walk` over the marks' names (c3_lp's invariant). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import model_read_c model_write_c bcmp_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Spec Require StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC3Lib LC3Defs LC3Keep LC3LoopLib.
From Stdlib Require Import FunctionalExtensionality.
Local Open Scope Z_scope.

(* where one round ends: the next round, or the loop's exit *)
Definition c3l_Q (E : lenv) (i : Z) (gp : word) (m0 : word -> option byte) (P N : Z) (kbs gbs : list byte) (j : Z)
  : machine_state -> Prop :=
  fun c => c3_lp E i gp m0 P N kbs gbs (j + 1) c \/ c3_ub E i gp m0 c.

(* the memory side of a state inside round j *)
Definition c3l_st (E : lenv) (i : Z) (m0 : word -> option byte) (P N : Z) (kbs gbs : list byte) (j : Z)
    (mbs : list byte) (m : word -> option byte) : Prop :=
  0 <= i <= 47 /\ 0 <= j < md_n_mark mbs /\ c3_mem E P N kbs mbs gbs m /\ c3_kfacts i kbs /\
  marks_are gbs mbs /\ munch (c3_W E) m0 m /\ wmono rsegs m0 m.

(* 0x13ba8: the latch *)
Lemma c3l_latch : forall E i gp m0 P N kbs gbs j (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word)
    F fc m mbs,
  lenv_ok E -> frm0 fc -> c3l_st E i m0 P N kbs gbs j mbs m ->
  unmark_walk link_tab (skipn (Z.to_nat (j + 1)) (mk_names gbs)) (md_reqs mbs) (md_kstate mbs kbs) = c3_U kbs gbs ->
  evt rsegs (eqv_cl (c3l_Q E i gp m0 P N kbs gbs j))
    (MS (c3_regs E i gp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz (e_md E + MD_MARK + MARK_LEN * j)) (wz j) s4
                 t3 t4 t5 t6) F (wz L3_LATCH) fc None m (seg_rom rsegs)).
Proof.
  intros E i gp m0 P N kbs gbs j ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 F fc m mbs HE FC
    (Hi & Hj & CM & KF & MA & MU & WM) UW.
  pose proof CM as CM'. destruct CM' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MDA & MDW & _).
  pose proof (c3l_nmark_le mbs MDW) as Hn32.
  pose proof (c3l_lenv_nums E HE) as (HS1 & HS2 & Hm1 & Hm2 & Imd).
  assert (HR : ov_read_bytes rsegs m (Z_to_bv 64 (e_md E + MD_N_REQ + 516)) 4 =
               Some (le4 (wz (fld_u32 mbs MD_N_MARK)))).
  { destruct MDA as [U L]. apply (c3_u8arr_rd32 m (e_md E) mbs MD_N_MARK);
      [exact U | unfold MD_N_MARK; lia | unfold MD_N_MARK, MD_SIZE in *; lia | unfold MD_N_REQ, MD_N_MARK; lia]. }
  unfold c3_regs, wz, L3_LATCH.
  step.
  change (fld_u32 mbs MD_N_MARK) with (md_n_mark mbs).
  rewrite (c3l_sx32 (md_n_mark mbs)) by lia. unfold wz.
  step. step.
  step.
  rewrite (c3l_lts_small (j + 1) (md_n_mark mbs)) by lia.
  destruct (Z.ltb_spec (j + 1) (md_n_mark mbs)) as [Lt|Ge].
  - apply evt_eqv_done. left.
    replace (Z_to_bv 64 (e_md E + MD_MARK + MARK_LEN * j + 16))
      with (wz (e_md E + MD_MARK + MARK_LEN * (j + 1))) by (unfold wz; f_equal; unfold MARK_LEN; lia).
    unfold c3_lp. do 17 eexists. exists F, fc, m, mbs. split; [reflexivity|].
    split; [exact FC|]. split; [exact Hi|]. split; [lia|]. split; [exact CM|]. split; [exact KF|].
    split; [exact MA|]. split; [exact UW|]. split; [exact MU | exact WM].
  - apply evt_eqv_done. right. unfold c3_ub. do 19 eexists. exists F, fc, m, P, N, kbs, mbs, gbs.
    split; [reflexivity|].
    split; [exact FC|]. split; [exact Hi|]. split; [exact CM|]. split; [exact KF|]. split; [exact MA|].
    split; [|split; [exact MU | exact WM]].
    rewrite <- UW. rewrite skipn_all2 by (rewrite c3l_mk_names_length, (proj1 MA); lia). reflexivity.
Qed.

Section C3Loop.
Hypothesis MODEL_READ_C : model_read_contract.
Hypothesis MODEL_WRITE_C : model_write_contract.
Hypothesis BCMP_C : bcmp_contract.

(* 0x13b94: the alias is "reac-pw:served": model_write (m, &m->mark[j], "") *)
Lemma c3l_wr : forall E i gp m0 P N kbs gbs j (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word)
    F fc m mbs nm reqs0 K0,
  lenv_ok E -> frm0 fc -> c3l_st E i m0 P N kbs gbs j mbs m ->
  nth_error (mk_names gbs) (Z.to_nat j) = Some nm ->
  unmark_walk link_tab (skipn (Z.to_nat j) (mk_names gbs)) reqs0 K0 = c3_U kbs gbs ->
  r_rc (read_core link_tab (Some nm) 0 ALIAS_MAX reqs0 K0) = 0 ->
  bl_eqb (r_alias (read_core link_tab (Some nm) 0 ALIAS_MAX reqs0 K0)) S_SERVED = true ->
  md_reqs mbs = r_reqs (read_core link_tab (Some nm) 0 ALIAS_MAX reqs0 K0) ->
  md_kstate mbs kbs = r_state (read_core link_tab (Some nm) 0 ALIAS_MAX reqs0 K0) ->
  evt rsegs (eqv_cl (c3l_Q E i gp m0 P N kbs gbs j))
    (MS (c3_regs E i gp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz (e_md E + MD_MARK + MARK_LEN * j)) (wz j) s4
                 t3 t4 t5 t6) F (Z_to_bv 64 0x13b94) fc None m (seg_rom rsegs)).
Proof.
  intros E i gp m0 P N kbs gbs j ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 F fc m mbs nm reqs0 K0
    HE FC (Hi & Hj & CM & KF & MA & MU & WM) Hnth UW Hrc Hsv Erq Est.
  pose proof (c3l_lenv_nums E HE) as (HS1 & HS2 & Hm1 & Hm2 & Imd).
  pose proof CM as CM'.
  destruct CM' as ((j0 & j1 & j2 & FR) & _ & NL & NW & IT & _ & _ & (_ & _ & _ & Cemp) & _ & _ & IP & MDA & MDW &
                   _ & _ & _ & _ & _ & MI & _ & ST).
  apply c3l_frame_split in FR. destruct FR as [_ B256].
  destruct (c3l_slot m (e_md E) mbs j MDA MDW Hj) as (Hn' & Cnm & Lnm).
  rewrite <- (proj2 MA), Hnth in Hn'. injection Hn' as Enm. rewrite <- Enm in Cnm.
  pose proof (c3l_nmark_le mbs MDW) as Hn32.
  assert (Usp : bv_unsigned (Z_to_bv 64 (e_S E - SLOT_FRAME)) = e_S E - SLOT_FRAME)
    by (apply unsigned_lit; unfold SLOT_FRAME, SLOT_STACK_Z in *; lia).
  rewrite <- Usp in ST.
  unfold c3_regs, wz.
  step. step. step. step. step.
  pose proof MODEL_WRITE_C as HL. unfold model_write_contract in HL.
  eapply (leaf_run _ _ _ _ _ _ HL).
  { eapply (c3l_write_pre E P N kbs mbs gbs m j _ HE CM Hj); c3l_arg_solve. }
  { exact MI. }
  { exact ST. }
  { rewrite Usp. unfold SLOT_FRAME, SLOT_STACK_Z. lia. }
  { rewrite Usp. unfold SLOT_FRAME, SLOT_STACK_Z in *. lia. }
  intros regs' m' MU1 WM1 MI1 ST1 PO1.
  rewrite Usp in ST1.
  pose proof (c3l_write_post _ _ _ _ PO1 mbs kbs nm (e_md E) (e_md E + MD_MARK + MARK_LEN * j)) as RP.
  specialize (RP ltac:(c3l_arg_solve) ltac:(c3l_arg_solve) ltac:(c3l_arg_solve) MDA NL IT
                 ltac:(unfold MD_MARK, MARK_LEN in *; lia) Cnm Cemp).
  destruct RP as (mbs' & MDA' & MDW' & Enx & Esk & Esd & Erq' & Enm' & Emk').
  assert (MUz : munch (c3l_Wz E) m m').
  { eapply munch_weaken; [|exact MU1]. eapply (c3l_wr_fp E _ m); [exact HE | exact Usp | c3l_arg_solve]. }
  assert (Bb : rw_cells rsegs m' (e_S E - SLOT_FRAME + FO_B256) [CB 256 j2]).
  { eapply (rw_cells_transport rsegs); [exact B256 | exact MU1 | exact WM1 |].
    replace (Z.of_nat (cells_size [CB 256 j2])) with 256 by reflexivity.
    eapply (c3l_wr_buf_dj E _ m); [exact HE | exact Usp | c3l_arg_solve]. }
  pose proof (c3l_keep E P N kbs mbs mbs' gbs m m' HE CM MUz WM1 MI1 ST1 MDA' MDW' (ex_intro _ j2 Bb)) as CM1.
  replace (ret_pc (Z_to_bv 64 80808)) with (Z_to_bv 64 80808) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  eapply (c3l_latch E i gp m0 P N kbs gbs j _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m' mbs' HE FC).
  - split; [exact Hi|]. split; [rewrite Enm'; exact Hj|]. split; [exact CM1|]. split; [exact KF|].
    split; [unfold marks_are; rewrite Enm', Emk'; exact MA|].
    split; [exact (munch_extend _ _ _ _ _ MU MUz (c3l_Wz_sub E HE)) | exact (wmono_trans rsegs _ _ _ WM WM1)].
  - assert (KS : md_kstate mbs' kbs =
                 w_state (write_core link_tab (Some nm) (Some []) (md_reqs mbs) (md_kstate mbs kbs))).
    { apply c3l_md_kstate; [| | exact Enx | exact Esk | exact Esd].
      - rewrite (proj1 (c3l_write_ce _ _ _ _ _)). reflexivity.
      - rewrite (proj2 (c3l_write_ce _ _ _ _ _)). reflexivity. }
    rewrite Erq', KS, Erq, Est.
    exact (c3l_step_write link_tab (mk_names gbs) j nm reqs0 K0 _ ltac:(lia) Hnth UW Hrc Hsv).
Qed.

(* 0x13b7c: the read answered 0: bcmp (sp + 0x78, "reac-pw:served", 15) *)
Lemma c3l_cmp : forall E i gp m0 P N kbs gbs j (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word)
    F fc m mbs nm reqs0 K0,
  lenv_ok E -> frm0 fc -> c3l_st E i m0 P N kbs gbs j mbs m ->
  nth_error (mk_names gbs) (Z.to_nat j) = Some nm ->
  unmark_walk link_tab (skipn (Z.to_nat j) (mk_names gbs)) reqs0 K0 = c3_U kbs gbs ->
  r_rc (read_core link_tab (Some nm) 0 ALIAS_MAX reqs0 K0) = 0 ->
  cstr_at m (e_S E - SLOT_FRAME + FO_B256) (r_alias (read_core link_tab (Some nm) 0 ALIAS_MAX reqs0 K0)) ->
  md_reqs mbs = r_reqs (read_core link_tab (Some nm) 0 ALIAS_MAX reqs0 K0) ->
  md_kstate mbs kbs = r_state (read_core link_tab (Some nm) 0 ALIAS_MAX reqs0 K0) ->
  evt rsegs (eqv_cl (c3l_Q E i gp m0 P N kbs gbs j))
    (MS (c3_regs E i gp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz (e_md E + MD_MARK + MARK_LEN * j)) (wz j) s4
                 t3 t4 t5 t6) F (Z_to_bv 64 0x13b7c) fc None m (seg_rom rsegs)).
Proof.
  intros E i gp m0 P N kbs gbs j ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 F fc m mbs nm reqs0 K0
    HE FC STt Hnth UW Hrc Cal Erq Est.
  pose proof STt as (Hi & Hj & CM & KF & MA & MU & WM).
  pose proof (c3l_lenv_nums E HE) as (HS1 & HS2 & Hm1 & Hm2 & Imd).
  pose proof CM as CM'.
  destruct CM' as (_ & _ & _ & _ & _ & _ & _ & (_ & Csrv & _ & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI & _).
  destruct (c3l_bcmp_served _ (proj2 Cal)) as (v & Hv & Rv & Iv).
  unfold c3_regs, wz.
  step. step. step. step. step.
  pose proof BCMP_C as HB. unfold bcmp_contract in HB.
  eapply evt_cut.
  { eapply (HB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m
              (r_alias (read_core link_tab (Some nm) 0 ALIAS_MAX reqs0 K0) ++ [zb 0]) (S_SERVED ++ [zb 0]) v).
    - rewrite unsigned_lit by (unfold SLOT_FRAME, SLOT_STACK_Z in *; lia). exact (proj1 Cal).
    - rewrite unsigned_lit by lia. exact (proj1 Csrv).
    - exact Hv.
    - exact MI. }
  intros ms' PO. unfold memcmp_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> &
                  MUb & WMb & MIb & _ & _).
  assert (Em : m' = m) by (apply functional_extensionality; intros x; exact (MUb x I)). subst m'.
  replace (ret_pc (Z_to_bv 64 80784)) with (Z_to_bv 64 80784) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  step.
  rewrite c3l_eqb0 by lia.
  destruct (Z.eqb_spec v 0) as [V0|VN]; cbn [negb].
  - apply Iv in V0.
    exact (c3l_wr E i gp m0 P N kbs gbs j _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m mbs nm reqs0 K0
             HE FC STt Hnth UW Hrc V0 Erq Est).
  - assert (Hs : bl_eqb (r_alias (read_core link_tab (Some nm) 0 ALIAS_MAX reqs0 K0)) S_SERVED = false).
    { apply Bool.not_true_iff_false. intros B. apply VN. apply Iv. exact B. }
    eapply (c3l_latch E i gp m0 P N kbs gbs j _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m mbs HE FC STt).
    rewrite Erq, Est.
    exact (c3l_step_skip link_tab (mk_names gbs) j nm reqs0 K0 _ ltac:(lia) Hnth UW (or_intror Hs)).
Qed.

(* 0x13b5c: one round, model_read (m, &m->mark[j], NULL, 0, sp + 0x78, 256) first *)
Lemma c3l_body : forall E i gp m0 P N kbs gbs j ms, lenv_ok E -> c3_lp E i gp m0 P N kbs gbs j ms ->
  evt rsegs (eqv_cl (c3l_Q E i gp m0 P N kbs gbs j)) ms.
Proof.
  intros E i gp m0 P N kbs gbs j ms HE H.
  destruct H as (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s4 & t3 & t4 & t5 & t6 & F & fc & m & mbs &
                 -> & FC & Hi & Hj & CM & KF & MA & UW & MU & WM).
  pose proof (c3l_lenv_nums E HE) as (HS1 & HS2 & Hm1 & Hm2 & Imd).
  pose proof CM as CM'.
  destruct CM' as ((j0 & j1 & j2 & FR) & _ & NL & NW & IT & _ & _ & _ & _ & _ & IP & MDA & MDW & _ & _ & _ & _ & _ &
                   MI & _ & ST).
  clear FR.
  destruct (c3l_slot m (e_md E) mbs j MDA MDW Hj) as (Hn' & Cnm & Lnm).
  set (nm := cstr (slice mbs (MD_MARK + MARK_LEN * j) MARK_LEN)) in *.
  assert (Hnth : nth_error (mk_names gbs) (Z.to_nat j) = Some nm) by (rewrite (proj2 MA); exact Hn').
  pose proof (c3l_nmark_le mbs MDW) as Hn32.
  pose proof (c3l_read_rc nm mbs kbs MDW NW) as (Rrc & Irc).
  assert (Usp : bv_unsigned (Z_to_bv 64 (e_S E - SLOT_FRAME)) = e_S E - SLOT_FRAME)
    by (apply unsigned_lit; unfold SLOT_FRAME, SLOT_STACK_Z in *; lia).
  rewrite <- Usp in ST.
  unfold c3_regs, wz, L3_BODY.
  step. step. step. step. step. step. step.
  pose proof MODEL_READ_C as HL. unfold model_read_contract in HL.
  eapply (leaf_run _ _ _ _ _ _ HL).
  { eapply (c3l_read_pre E P N kbs mbs gbs m j _ HE CM Hj); c3l_arg_solve. }
  { exact MI. }
  { exact ST. }
  { rewrite Usp. unfold SLOT_FRAME, SLOT_STACK_Z. lia. }
  { rewrite Usp. unfold SLOT_FRAME, SLOT_STACK_Z in *. lia. }
  intros regs' m' MU1 WM1 MI1 ST1 PO1.
  rewrite Usp in ST1.
  pose proof (c3l_read_post _ _ _ _ PO1 mbs kbs nm (e_md E) (e_md E + MD_MARK + MARK_LEN * j)
                (e_S E - SLOT_FRAME + FO_B256)) as RP.
  specialize (RP ltac:(c3l_arg_solve) ltac:(c3l_arg_solve) ltac:(c3l_arg_solve) ltac:(c3l_arg_solve)
                 ltac:(c3l_arg_solve) ltac:(c3l_arg_solve) ltac:(unfold SLOT_FRAME, SLOT_STACK_Z, FO_B256 in *; lia)
                 MDA NL IT ltac:(unfold MD_MARK, MARK_LEN in *; lia) Cnm).
  destruct RP as (R10 & (mbs' & MDA' & MDW' & Enx & Esk & Esd & Erq & Enm & Emk) & Cal & (jb & Bb)).
  assert (MUz : munch (c3l_Wz E) m m').
  { eapply munch_weaken; [|exact MU1].
    eapply (c3l_rd_fp E _ m); [exact HE | exact Usp | c3l_arg_solve ..]. }
  pose proof (c3l_keep E P N kbs mbs mbs' gbs m m' HE CM MUz WM1 MI1 ST1 MDA' MDW' (ex_intro _ jb Bb)) as CM1.
  assert (STt : c3l_st E i m0 P N kbs gbs j mbs' m').
  { split; [exact Hi|]. split; [rewrite Enm; exact Hj|]. split; [exact CM1|]. split; [exact KF|].
    split; [unfold marks_are; rewrite Enm, Emk; exact MA|].
    split; [exact (munch_extend _ _ _ _ _ MU MUz (c3l_Wz_sub E HE)) | exact (wmono_trans rsegs _ _ _ WM WM1)]. }
  assert (KS : md_kstate mbs' kbs =
               r_state (read_core link_tab (Some nm) 0 ALIAS_MAX (md_reqs mbs) (md_kstate mbs kbs))).
  { apply c3l_md_kstate; [| | exact Enx | exact Esk | exact Esd].
    - rewrite (proj1 (c3l_read_ce _ _ _ _ _ _)). reflexivity.
    - rewrite (proj2 (c3l_read_ce _ _ _ _ _ _)). reflexivity. }
  replace (ret_pc (Z_to_bv 64 80760)) with (Z_to_bv 64 80760) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  step.
  rewrite R10. unfold wz. rewrite c3l_eqb0 by lia.
  destruct (Z.eqb_spec (norm_rc (r_rc (read_core link_tab (Some nm) 0 ALIAS_MAX (md_reqs mbs) (md_kstate mbs kbs)))) 0)
    as [Z0|NZ]; cbn [negb].
  - apply Irc in Z0.
    exact (c3l_cmp E i gp m0 P N kbs gbs j _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m' mbs' nm (md_reqs mbs)
             (md_kstate mbs kbs) HE FC STt Hnth UW Z0 Cal Erq KS).
  - assert (NZ' : r_rc (read_core link_tab (Some nm) 0 ALIAS_MAX (md_reqs mbs) (md_kstate mbs kbs)) <> 0)
      by (intros E0; apply NZ, Irc, E0).
    eapply (c3l_latch E i gp m0 P N kbs gbs j _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m' mbs' HE FC STt).
    rewrite Erq, KS.
    exact (c3l_step_skip link_tab (mk_names gbs) j nm (md_reqs mbs) (md_kstate mbs kbs) _ ltac:(lia) Hnth UW
             (or_introl NZ')).
Qed.

(* the loop, by the number of rounds left *)
Lemma c3l_iter : forall E i gp m0 P N kbs gbs, lenv_ok E ->
  forall k j ms, Z.to_nat (mk_n gbs - j) = k -> c3_lp E i gp m0 P N kbs gbs j ms ->
  evt rsegs (eqv_cl (c3_ub E i gp m0)) ms.
Proof.
  intros E i gp m0 P N kbs gbs HE k. induction k as [|k IH]; intros j ms Hk H.
  - exfalso.
    destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & mbs &
                   _ & _ & _ & Hj & _ & _ & MA & _).
    destruct MA as [Hn _]. lia.
  - pose proof H as H'.
    destruct H' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & mbs &
                    _ & _ & _ & Hj & _ & _ & MA & _).
    destruct MA as [Hn _].
    eapply evt_eqv_cut; [exact (c3l_body E i gp m0 P N kbs gbs j ms HE H)|].
    intros c [Hl|Hu].
    + apply (IH (j + 1) c); [lia | exact Hl].
    + apply evt_eqv_done. exact Hu.
Qed.

Lemma c3_loop : forall (E : lenv) (i : Z) (gp : word) (m0 : word -> option byte) (ms : machine_state),
  lenv_ok E -> c3_mb E i gp m0 ms -> evt rsegs (eqv_cl (c3_ub E i gp m0)) ms.
Proof.
  intros E i gp m0 ms HE H.
  destruct H as (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & t3 & t4 & t5 & t6 & F & fc &
                 m & P & N & kbs & mbs & gbs & -> & FC & Hi & CM & KF & KS & NR & MA & MU & WM).
  pose proof (c3l_lenv_nums E HE) as (HS1 & HS2 & Hm1 & Hm2 & Imd).
  pose proof CM as CM'.
  destruct CM' as ((j0 & j1 & j2 & FR) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MDA & MDW & _).
  pose proof (c3l_nmark_le mbs MDW) as Hn32.
  assert (HR : ov_read_bytes rsegs m (Z_to_bv 64 (e_md E + MD_N_REQ + 516)) 4 =
               Some (le4 (wz (fld_u32 mbs MD_N_MARK)))).
  { destruct MDA as [U L]. apply (c3_u8arr_rd32 m (e_md E) mbs MD_N_MARK);
      [exact U | unfold MD_N_MARK; lia | unfold MD_N_MARK, MD_SIZE in *; lia | unfold MD_N_REQ, MD_N_MARK; lia]. }
  unfold lh_cells in FR.
  unfold c3_regs, wz, L3_MB.
  step.
  change (fld_u32 mbs MD_N_MARK) with (md_n_mark mbs).
  rewrite (c3l_sx32 (md_n_mark mbs)) by lia. unfold wz.
  step.
  rewrite (c3l_lts_small 0 (md_n_mark mbs)) by lia.
  destruct (Z_lt_le_dec 0 (md_n_mark mbs)) as [Pos|Zer].
  - rewrite (proj2 (Z.ltb_lt 0 (md_n_mark mbs)) Pos).
    cbn [negb].
    step. step.
    replace (wz (e_md E + MD_MARK)) with (wz (e_md E + MD_MARK + MARK_LEN * 0)) by (f_equal; unfold MARK_LEN; lia).
    apply (c3l_iter E i gp m0 P N kbs gbs HE (Z.to_nat (mk_n gbs - 0)) 0); [reflexivity|].
    unfold c3_lp. do 17 eexists. exists F, fc, m, mbs. split; [reflexivity|].
    split; [exact FC|]. split; [exact Hi|]. split; [lia|]. split; [exact CM|]. split; [exact KF|].
    split; [exact MA|]. split; [|split; [exact MU | exact WM]].
    change (skipn (Z.to_nat 0) (mk_names gbs)) with (mk_names gbs).
    assert (L2 : md_reqs mbs = nk_sent kbs).
    { unfold md_reqs, nk_sent. rewrite NR. destruct KF as (_ & _ & _ & _ & K5). rewrite K5. reflexivity. }
    rewrite L2, KS. reflexivity.
  - rewrite (proj2 (Z.ltb_ge 0 (md_n_mark mbs)) Zer).
    cbn [negb].
    apply evt_eqv_done. unfold c3_ub. do 19 eexists. exists F, fc, m, P, N, kbs, mbs, gbs. split; [reflexivity|].
    split; [exact FC|]. split; [exact Hi|]. split; [exact CM|]. split; [exact KF|]. split; [exact MA|].
    split; [|split; [exact MU | exact WM]].
    assert (L1 : mk_names gbs = []).
    { unfold mk_names. rewrite (proj1 MA). replace (md_n_mark mbs) with 0 by lia. reflexivity. }
    assert (L2 : md_reqs mbs = []) by (unfold md_reqs; rewrite NR; reflexivity).
    assert (L3 : nk_sent kbs = []).
    { unfold nk_sent. destruct KF as (_ & _ & _ & _ & K5). rewrite K5. reflexivity. }
    unfold c3_U, unmark. rewrite L1, L2, L3. reflexivity.
Qed.

End C3Loop.

Print Assumptions c3_loop.
About c3_loop.
