(* op_refused (arm 5 of the slot's loop, fuzz_link.c:759-761), plain image: the segment from
   mark_quietly's return (0x13c74, c45_13c74) to the arm's end at 0x13dd8 (c45_end at C45_END_R).
   0x13c74 `addi a1, zero, -0x16`, `jal check_mark` (0x15e04, ra 0x13c7c): mark_quietly answered
   -EINVAL in both cases (w odd: a0 = NULL; w even: the name is NULL or "", mark_core's first two
   arms), so same_rc_regs holds; `j 0x13dd0`; `mv a0, s0`, `jal check_requests` (0x15284, ra 0x13dd8):
   g_nl.n_sent = model.n_req = 0 since model_begin, so requests_are holds. Written: check_requests'
   48-byte frame below sp. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf check_write_c check_requests_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC45Defs LC45Call LC45RLib LC45RTr.
Local Open Scope Z_scope.

(* the memory of c45_end at operation i + 1, with the two counters model_begin cleared *)
Definition c45r_m74 (E : lenv) (i : Z) (m : word -> option byte) : Prop :=
  exists (P N : Z) (kbs mbs gbs j0 j1 j2 : list byte),
    0 <= i <= 47 /\ c45_frame E j0 P N m /\ c45_cur E P N /\
    rw_cells rsegs m (c45_sp E + FO_B40) [CB 40 j1] /\
    rw_cells rsegs m (c45_sp E + FO_B256) [CB 256 j2] /\
    c45_kmg E (i + 1) kbs mbs gbs m /\ nk_n_sent kbs = 0 /\ md_n_req mbs = 0 /\
    c45_keep E m /\ c45_mach E m.

Lemma c45r_end_of : forall E i gp pc (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6 : word) F fc m,
  c45r_m74 E i m -> frm0 fc ->
  c45_end E i gp pc (MS (c45_R E i gp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6)
                        F (wz pc) fc None m (seg_rom rsegs)).
Proof.
  intros E i gp pc ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6 F fc m
    (P & N & kbs & mbs & gbs & j0 & j1 & j2 & Hi & FR & CUR & B40 & B256 & KMG & _ & _ & KEEP & MACH) FRM.
  exists ra, t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, s2, s3, s4, t3, t4, t5, t6, F, fc, m, P, N,
    kbs, mbs, gbs, j0, j1, j2.
  exact (conj eq_refl (conj FRM (conj Hi (conj FR (conj CUR (conj B40 (conj B256 (conj KMG (conj KEEP MACH))))))))).
Qed.

(* the two cases of mark_quietly's Post give the same facts: rc = -EINVAL and the cut at i + 1 *)
Lemma c45r_r1_cases : forall E i gp w ms, c45_13c74 E i gp w ms ->
  exists (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6 : word) F fc m,
    ms = MS (c45_R E i gp ra t0 t1 t2 (wz (- E_INVAL)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6)
            F (wz C45_MQ_RA) fc None m (seg_rom rsegs) /\
    frm0 fc /\ c45r_m74 E i m.
Proof.
  intros E i gp w ms (ra & t0 & t1 & t2 & rc & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & t3 & t4 & t5 & t6
    & F & fc & m & P & N & kbs & mbs & gbs & j0 & j1 & j2 & -> & FRM & Hi & Hw & FR & CUR & B40 & B256
    & KW & Kop & Kmis & Koc & Kle & Kns & MA & MW & Hnr & GW & GARE & ODD & EVEN & KEEP & MACH).
  destruct (Z.odd w) eqn:Ho.
  - destruct (ODD eq_refl) as (Hrc & KA & KI & GA). subst rc.
    exists ra, t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, s2, s3, s4, t3, t4, t5, t6, F, fc, m.
    split; [reflexivity|]. split; [exact FRM|].
    exists P, N, kbs, mbs, gbs, j0, j1, j2.
    split; [exact Hi|]. split; [exact FR|]. split; [exact CUR|]. split; [exact B40|]. split; [exact B256|].
    split; [|split; [exact Kns|]; split; [exact Hnr|]; split; [exact KEEP | exact MACH]].
    split; [exact KA|]. split; [exact KW|]. split; [exact KI|]. split; [exact Kop|]. split; [exact Kmis|].
    split; [exact Koc|]. split; [lia|]. split; [exact MA|]. split; [exact MW|]. split; [exact GA|].
    split; [exact GW | exact GARE].
  - specialize (EVEN eq_refl). cbv zeta in EVEN.
    assert (MR : mark_lib link_tab (c45_mq_nm w) (mk_names gbs) (nk_sent kbs) (nk_kstate kbs)
                 = Mres (- E_INVAL) (mk_names gbs) (nk_sent kbs) (nk_kstate kbs))
      by (unfold mark_lib, mark_core, c45_mq_nm; destruct (Z.testbit w 1); reflexivity).
    rewrite MR in EVEN. cbn [m_rc m_marks m_reqs m_state] in EVEN.
    destruct EVEN as (Hrc & (gbs' & GA' & GW' & Gn & Gk) & (kbs' & KA' & KW' & _ & _ & _ & KI' & _ & _ & Kns'
                      & Kop' & Kmis' & Kd & Kb)).
    subst rc.
    assert (LS : length (nk_sent kbs) = 0%nat)
      by (unfold nk_sent; rewrite length_map, length_seq, Kns; reflexivity).
    assert (LG : Z.of_nat (length (mk_names gbs)) = mk_n gbs).
    { unfold mk_names. rewrite length_map, length_seq. destruct GW as [GW _]. lia. }
    exists ra, t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, s2, s3, s4, t3, t4, t5, t6, F, fc, m.
    split; [reflexivity|]. split; [exact FRM|].
    exists P, N, kbs', mbs, gbs', j0, j1, j2.
    split; [exact Hi|]. split; [exact FR|]. split; [exact CUR|]. split; [exact B40|]. split; [exact B256|].
    split; [|split; [rewrite Kns', LS; reflexivity|]; split; [exact Hnr|]; split; [exact KEEP | exact MACH]].
    split; [exact KA'|]. split; [exact KW'|]. split; [exact KI'|]. split; [exact Kop'|].
    split; [rewrite Kmis'; exact Kmis|]. split; [lia|]. split; [lia|]. split; [exact MA|]. split; [exact MW|].
    split; [exact GA'|]. split; [exact GW'|].
    destruct GARE as [G1 G2]. split; [rewrite Gk, LG; exact G1 | rewrite Gn; exact G2].
Qed.

(* the cut at mark_quietly's return carried across check_requests' frame [sp - 48, sp) *)
Lemma c45r_fin1 : forall E i m m2, lenv_ok E -> c45r_m74 E i m ->
  munch [(c45_sp E - 48, c45_sp E)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
  stk rsegs m2 (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME) ->
  c45r_m74 E i m2.
Proof.
  intros E i m m2 LE (P & N & kbs & mbs & gbs & j0 & j1 & j2 & Hi & (PT & CU & SV) & CUR & B40 & B256
    & ((KU & KL) & KW & KI & Kop & Kmis & Koc & Kle & (MD & ML) & MW & (GU & GL) & GW & GARE)
    & Kns & Hnr & KEEP & (MI & TM & ST)) MU WM MI2 ST2.
  pose proof LE as LE'. destruct LE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LS).
  destruct (c45r_lenv E LE) as (HS & Hmd1 & Hmd2 & _ & Hmk1 & Hmk2 & _ & Hpl1 & Hpl2 & Hpl3 & _).
  set (Pw := fun x => c45_sp E - 48 <= x < c45_sp E).
  assert (HW : forall x, ~ outside [(c45_sp E - 48, c45_sp E)] x -> Pw x) by (intros x; apply c45r_hw1).
  assert (HST : c45r_stat Pw).
  { intros x Hx1 Hx2 HP. unfold Pw in HP. clear - Hx1 HP HS. unfold c45_sp, SLOT_FRAME in *. lia. }
  assert (FAR : forall x, x < e_S E - 65536 -> ~ Pw x).
  { intros x Hx HP. unfold Pw in HP. clear - Hx HP HS. unfold c45_sp, SLOT_FRAME in *. lia. }
  assert (NEAR : forall x, c45_sp E <= x -> ~ Pw x).
  { intros x Hx HP. unfold Pw in HP. lia. }
  exists P, N, kbs, mbs, gbs, j0, j1, j2.
  split; [exact Hi|].
  split.
  { split; [|split].
    - apply (c45r_tr_rw Pw _ m m2 HW MU WM _ _ PT). intros x Hx. apply NEAR. lia.
    - apply (c45r_tr_rw Pw _ m m2 HW MU WM _ _ CU). intros x Hx. apply NEAR. unfold FO_P in Hx. lia.
    - apply (c45r_tr_bytes Pw _ m m2 HW MU _ _ SV). intros x Hx. apply NEAR. unfold c45_sp, SLOT_FRAME. lia. }
  split; [exact CUR|].
  split; [apply (c45r_tr_rw Pw _ m m2 HW MU WM _ _ B40); intros x Hx; apply NEAR; unfold FO_B40 in Hx; lia|].
  split; [apply (c45r_tr_rw Pw _ m m2 HW MU WM _ _ B256); intros x Hx; apply NEAR; unfold FO_B256 in Hx; lia|].
  split.
  { split.
    { split; [|exact KL]. apply (c45r_tr_u8 Pw _ m m2 HW MU WM _ _ KU). rewrite KL. intros x Hx. apply FAR.
      clear - Hx HS. unfold A_G_NL, NK_SIZE in *. lia. }
    split; [exact KW|].
    split; [apply (c45r_tr_iftab Pw _ m m2 HW MU HST kbs KI); destruct KEEP as (_ & _ & _ & _ & _ & IP & _); exact IP|].
    split; [exact Kop|]. split; [exact Kmis|]. split; [exact Koc|]. split; [exact Kle|].
    split.
    { split; [|exact ML]. apply (c45r_tr_u8 Pw _ m m2 HW MU WM _ _ MD). rewrite ML. intros x Hx. apply FAR.
      clear - Hx Hmd2. unfold MD_SIZE in *. lia. }
    split; [exact MW|].
    split.
    { split; [|exact GL]. apply (c45r_tr_u8 Pw _ m m2 HW MU WM _ _ GU). rewrite GL. intros x Hx. apply FAR.
      clear - Hx Hmk2. unfold MK_SIZE in *. lia. }
    split; [exact GW | exact GARE]. }
  split; [exact Kns|]. split; [exact Hnr|].
  split.
  { apply (c45r_tr_keep Pw _ m m2 HW MU WM HST E KEEP). intros x Hx. apply FAR. lia. }
  split; [exact MI2|]. split; [|exact ST2].
  apply (c45r_tr_task _ m m2 TM MU). intros x Hx. apply HW in Hx. unfold Pw in Hx.
  rewrite c45r_task_size. clear - Hx HS. unfold c45_sp, SLOT_FRAME in *. lia.
Qed.

Lemma c45r_post_unchanged : post_ext unchanged.
Proof. intros r1 r2 m q1 q2 m' _ _ H. exact H. Qed.

Lemma c45r_post_only_frame : post_ext only_frame.
Proof. intros r1 r2 m q1 q2 m' _ _ H. exact H. Qed.

Lemma c45r_same_rc : forall R, getr R 11 = Z_to_bv 64 (-22) -> getr R 10 = Z_to_bv 64 (-22) -> same_rc_regs R.
Proof.
  intros R H11 H10. unfold same_rc_regs. rewrite H11, H10.
  assert (NE : Z_to_bv 64 (-22) <> wz RC_FAILS).
  { intros E. apply (f_equal bv_unsigned) in E. revert E. vm_compute. intros E. discriminate E. }
  split; [intros H; exfalso; exact (NE H) | intros _; reflexivity].
Qed.

Section R1.
Hypothesis CMK : check_mark_contract.
Hypothesis CRQ : check_requests_contract.

Lemma c45_r1 : forall E i gp w ms, lenv_ok E -> c45_13c74 E i gp w ms ->
  evt rsegs (eqv_cl (c45_post E (ms_mem ms) (c45_end E i gp C45_END_R))) ms.
Proof.
  intros E i gp w ms LE H.
  destruct (c45r_r1_cases E i gp w ms H) as (ra & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4
    & t3 & t4 & t5 & t6 & F & fc & m & -> & FRM & M74).
  clear H. cbn [ms_mem].
  pose proof M74 as (P & N & kbs & mbs & gbs & j0 & j1 & j2 & Hi & _ & _ & _ & _
    & ((KU & KL) & KW & _ & _ & _ & _ & _ & (MD & ML) & MW & _) & Kns & Hnr & _ & (MI & _ & ST)).
  destruct (c45r_lenv E LE) as (HS & Hmd1 & Hmd2 & Hmd3 & _).
  assert (SPu : bv_unsigned (Z_to_bv 64 (c45_sp E)) = c45_sp E)
    by (apply unsigned_lit; unfold c45_sp, SLOT_FRAME; lia).
  unfold c45_R, wz.
  change (Z_to_bv 64 C45_MQ_RA) with (Z_to_bv 64 0x13c74).
  change (Z_to_bv 64 (- E_INVAL)) with (Z_to_bv 64 (-22)).
  (* addi a1, zero, -0x16; jal check_mark *)
  zstep. zstep.
  eapply (c45_leaf_call CHECK_MARK 0 _ _ _ CMK c45r_post_unchanged);
    [ apply c45_eqv_cl_ext
    | cbv beta; apply c45r_same_rc; reflexivity
    | exact MI
    | rewrite SPu; exact ST
    | rewrite SPu; unfold SLOT_STACK_Z, c45_sp, SLOT_FRAME; lia
    | rewrite SPu; unfold c45_sp, SLOT_FRAME; lia
    | ].
  intros ra1 t01 t11 t21 a01 a11 a21 a31 a41 a51 a61 a71 t31 t41 t51 t61 m1 _ _ _ _ PO1.
  unfold unchanged in PO1. subst m1.
  rewrite ret_pc_even by (lia || reflexivity).
  (* j 0x13dd0; mv a0, s0; jal check_requests *)
  zstep. zstep. zstep.
  eapply (c45_leaf_call CHECK_REQUESTS 48 _ _ _ CRQ c45r_post_only_frame);
    [ apply c45_eqv_cl_ext
    | cbv beta
    | exact MI
    | rewrite SPu; exact ST
    | rewrite SPu; unfold SLOT_STACK_Z, c45_sp, SLOT_FRAME; lia
    | rewrite SPu; unfold c45_sp, SLOT_FRAME; lia
    | ].
  - exists kbs, mbs. unfold frame_apart_gnl, apart_frame, apart_gnl. rewrite mkR_a0, mkR_sp, SPu.
    rewrite unsigned_lit by lia.
    split; [exact (conj KU KL)|].
    split; [unfold c45_sp, SLOT_FRAME, A_G_NL, NK_SIZE; lia|].
    split; [exact (conj MD ML)|]. split; [exact KW|]. split; [exact MW|].
    split; [split; [lia | intros j Hj; lia]|].
    split; [unfold c45_sp, SLOT_FRAME, MD_SIZE; lia|].
    unfold MD_SIZE, A_G_NL, NK_SIZE; lia.
  - intros ra2 t02 t12 t22 a02 a12 a22 a32 a42 a52 a62 a72 t32 t42 t52 t62 m2 MU2 WM2 MI2 ST2 _.
    rewrite ret_pc_even by (lia || reflexivity).
    unfold writes_nothing in MU2. rewrite SPu in MU2, ST2.
    assert (M74' : c45r_m74 E i m2) by (apply (c45r_fin1 E i m m2 LE M74); assumption).
    apply evt_done. apply c45_eqv_cl_of. unfold c45_post. cbn [ms_mem]. split.
    + apply c45r_end_of; [exact M74' | exact FRM].
    + exists [(c45_sp E - 48, c45_sp E)]. split; [exact MU2|]. split; [exact WM2|].
      intros x Hx Hout. apply c45r_hw1 in Hout. left. unfold c45_sp, SLOT_FRAME, SLOT_STACK_Z in *. lia.
Qed.
End R1.

Print Assumptions c45_r1.
