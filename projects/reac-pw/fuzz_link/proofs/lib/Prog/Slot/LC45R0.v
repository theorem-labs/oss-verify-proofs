(* op_refused (arm 5 of the slot's loop, fuzz_link.c:756-759), plain image: the segment from the
   dispatch (0x13bf4, c45_disp at op 5) to the call of mark_quietly at 0x13c70 (c45_13c70).
   `beqz a1` on N - 1: N = 1 takes 0x13c30 (w = 0, the cursor stays (P + 1, 0)); else the byte w at
   P + 1 and the cursor (P + 2, N - 2) (LC45RLib.v c45r_pb / c45r_pa). Then model_begin's five stores
   into the md block and g_nl and the two arguments of mark_quietly (c45r_mb). Written: the cursor
   cells, md[0, 12), md.n_req, g_nl.n_sent. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC45Defs LC45Call LC45RLib LC45RTr.
Local Open Scope Z_scope.

(* what the segment writes: the cursor cells, the md block, g_nl.n_sent *)
Definition c45r_P0 (E : lenv) (x : Z) : Prop :=
  (c45_sp E + FO_P <= x < c45_sp E + FO_P + 16) \/ (e_md E <= x < e_md E + MD_SIZE) \/
  (A_G_NL + NK_N_SENT <= x < A_G_NL + NK_N_SENT + 4).

(* the memory half of c45_13c70 *)
Definition c45r_m70 (E : lenv) (i w : Z) (m : word -> option byte) : Prop :=
  exists (P N : Z) (kbs mbs gbs j0 j1 j2 : list byte),
    0 <= i <= 47 /\ 0 <= w < 256 /\
    c45_frame E j0 P N m /\ c45_cur E P N /\
    rw_cells rsegs m (c45_sp E + FO_B40) [CB 40 j1] /\
    rw_cells rsegs m (c45_sp E + FO_B256) [CB 256 j2] /\
    c45_kmg E i kbs mbs gbs m /\ nk_n_sent kbs = 0 /\ md_n_req mbs = 0 /\
    c45_keep E m /\ c45_mach E m.

Lemma c45r_13c70_of : forall E i gp w (t0 t1 t2 a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6 : word) F fc m,
  c45r_m70 E i w m -> frm0 fc ->
  c45_13c70 E i gp w (MS (c45_R E i gp (wz C45_MQ_RA) t0 t1 t2 (wz (c45_mq_a0 E w)) (wz (c45_mq_a1 w))
                             a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6)
                          F (wz P_mark_quietly) fc None m (seg_rom rsegs)).
Proof.
  intros E i gp w t0 t1 t2 a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6 F fc m
    (P & N & kbs & mbs & gbs & j0 & j1 & j2 & Hi & Hw & FR & CUR & B40 & B256 & KMG & Hns & Hnr & KEEP & MACH) FRM.
  exists t0, t1, t2, a2, a3, a4, a5, a6, a7, s2, s3, s4, t3, t4, t5, t6, F, fc, m, P, N, kbs, mbs, gbs, j0, j1, j2.
  exact (conj eq_refl (conj FRM (conj Hi (conj Hw (conj FR (conj CUR (conj B40 (conj B256 (conj KMG
    (conj Hns (conj Hnr (conj KEEP MACH)))))))))))).
Qed.

Ltac c45r_out :=
  cbn [outside c45r_Wmb app]; repeat split; try exact I;
  unfold c45_sp, SLOT_FRAME, FO_P, MD_N_REQ, MD_SIZE, A_G_NL, NK_N_SENT, NK_SIZE in *; lia.

(* the end of the segment: every carried fact from the memory at the dispatch, the written ones as given *)
Lemma c45r_fin0 : forall E i w P N m0 m W kbs mbs gbs j0 j1 j2,
  lenv_ok E -> 0 <= i <= 47 -> 0 <= w < 256 ->
  rw_cells rsegs m0 (c45_sp E) (c45_ptrs E j0) -> bytes_at rsegs m0 (e_S E - 104) (e_saved E) ->
  rw_cells rsegs m0 (c45_sp E + FO_B40) [CB 40 j1] -> rw_cells rsegs m0 (c45_sp E + FO_B256) [CB 256 j2] ->
  c45_kmg E i kbs mbs gbs m0 -> c45_keep E m0 -> c45_mach E m0 ->
  rw_cells rsegs m (c45_sp E + FO_P) [C8 (wz P); C8 (wz N)] -> c45_cur E P N ->
  mem_inv rsegs m -> munch W m0 m -> wmono rsegs m0 m -> (forall x, ~ outside W x -> c45r_P0 E x) ->
  u8arr rsegs m A_G_NL (c45r_kbs kbs) ->
  u8arr rsegs m (e_md E) (c45r_mbs mbs (nk_socket_errno kbs) (nk_send_errno kbs)) ->
  c45r_m70 E i w m /\ seg_fp (e_S E) (c45_hp E) m0 m.
Proof.
  intros E i w P N m0 m W kbs mbs gbs j0 j1 j2 LE Hi Hw PT SV B40 B256
    (KA & KW & KI & Kop & Kmis & Koc & Kle & MA & MW & GA & GW & GARE) KEEP (MI0 & TM0 & ST0)
    CU CUR MI MU WM HW KU MDU.
  pose proof LE as LE'. destruct LE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LS).
  destruct (c45r_lenv E LE) as (HS & Hmd1 & Hmd2 & Hmd3 & Hmk1 & Hmk2 & Hmk3 & Hpl1 & Hpl2 & Hpl3 & Hpl4
                                & Hmdmk & Hplmd & Hplmk).
  destruct KA as [KU0 KL]. destruct MA as [MD0 ML]. destruct GA as [GU0 GL].
  pose proof KW as KW'. destruct KW' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hse & Hsd & _).
  assert (HST : c45r_stat (c45r_P0 E)).
  { intros x Hx1 Hx2 HP. clear - Hx1 Hx2 HP HS Hmd3.
    unfold c45r_P0, c45_sp, FO_P, SLOT_FRAME, MD_SIZE, NK_N_SENT, A_G_NL, NK_IF_NAME in *. lia. }
  (* the carried facts *)
  assert (PT' : rw_cells rsegs m (c45_sp E) (c45_ptrs E j0)).
  { apply (c45r_tr_rw (c45r_P0 E) W m0 m HW MU WM _ _ PT). unfold c45_ptrs. cbn [cells_size csize Nat.add].
    intros x Hx HP. clear - Hx HP HS Hmd2.
    unfold c45r_P0, c45_sp, FO_P, SLOT_FRAME, MD_SIZE, NK_N_SENT, A_G_NL in *. lia. }
  assert (SV' : bytes_at rsegs m (e_S E - 104) (e_saved E)).
  { apply (c45r_tr_bytes (c45r_P0 E) W m0 m HW MU _ _ SV). rewrite LS.
    intros x Hx HP. clear - Hx HP HS Hmd2.
    unfold c45r_P0, c45_sp, FO_P, SLOT_FRAME, MD_SIZE, NK_N_SENT, A_G_NL in *. lia. }
  assert (B40' : rw_cells rsegs m (c45_sp E + FO_B40) [CB 40 j1]).
  { apply (c45r_tr_rw (c45r_P0 E) W m0 m HW MU WM _ _ B40). cbn [cells_size csize Nat.add].
    intros x Hx HP. clear - Hx HP HS Hmd2.
    unfold c45r_P0, c45_sp, FO_P, FO_B40, SLOT_FRAME, MD_SIZE, NK_N_SENT, A_G_NL in *. lia. }
  assert (B256' : rw_cells rsegs m (c45_sp E + FO_B256) [CB 256 j2]).
  { apply (c45r_tr_rw (c45r_P0 E) W m0 m HW MU WM _ _ B256). cbn [cells_size csize Nat.add].
    intros x Hx HP. clear - Hx HP HS Hmd2.
    unfold c45r_P0, c45_sp, FO_P, FO_B256, SLOT_FRAME, MD_SIZE, NK_N_SENT, A_G_NL in *. lia. }
  assert (GU' : u8arr rsegs m (e_mk E) gbs).
  { apply (c45r_tr_u8 (c45r_P0 E) W m0 m HW MU WM _ _ GU0). rewrite GL.
    intros x Hx HP. clear - Hx HP HS Hmd2 Hmk2 Hmk3 Hmdmk.
    unfold c45r_P0, c45_sp, FO_P, SLOT_FRAME, MD_SIZE, MK_SIZE, NK_N_SENT, A_G_NL in *. lia. }
  assert (KI' : iftab_at m kbs link_tab).
  { apply (c45r_tr_iftab (c45r_P0 E) W m0 m HW MU HST kbs KI).
    destruct KEEP as (_ & _ & _ & _ & _ & IP & _). exact IP. }
  assert (KEEP' : c45_keep E m).
  { apply (c45r_tr_keep (c45r_P0 E) W m0 m HW MU WM HST E KEEP).
    intros x Hx HP. clear - Hx HP HS Hmd2 Hpl3 Hpl4 Hplmd.
    unfold c45r_P0, c45_sp, FO_P, SLOT_FRAME, MD_SIZE, NK_N_SENT, A_G_NL in *. lia. }
  assert (TM : MemNorm.task_mem rsegs m).
  { apply (c45r_tr_task W m0 m TM0 MU). intros x Hx. specialize (HW x Hx). rewrite c45r_task_size.
    clear - HW HS Hmd2. unfold c45r_P0, c45_sp, FO_P, SLOT_FRAME, MD_SIZE, NK_N_SENT, A_G_NL in *. lia. }
  assert (ST : stk rsegs m (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME)).
  { apply (c45r_tr_stk (c45r_P0 E) W m0 m HW MU WM _ _ ST0).
    intros x Hx HP. clear - Hx HP HS Hmd2.
    unfold c45r_P0, c45_sp, FO_P, SLOT_FRAME, SLOT_STACK_Z, MD_SIZE, NK_N_SENT, A_G_NL in *. lia. }
  split.
  - exists P, N, (c45r_kbs kbs), (c45r_mbs mbs (nk_socket_errno kbs) (nk_send_errno kbs)), gbs, j0, j1, j2.
    split; [exact Hi|]. split; [exact Hw|].
    split; [exact (conj PT' (conj CU SV'))|]. split; [exact CUR|].
    split; [exact B40'|]. split; [exact B256'|].
    split.
    + split; [exact (conj KU (c45r_kbs_len kbs KL))|].
      split; [exact (c45r_kbs_wf kbs KL KW)|].
      split; [exact (c45r_kbs_iftab kbs KL m link_tab KI')|].
      unfold nk_open, nk_misuse, nk_opened, nk_closed in *.
      rewrite !(c45r_kbs_fld kbs KL) by (unfold NK_OPEN, NK_MISUSE, NK_OPENED, NK_CLOSED, NK_N_SENT; lia).
      split; [exact Kop|]. split; [exact Kmis|]. split; [exact Koc|]. split; [exact Kle|].
      split; [exact (conj MDU (c45r_mbs_len mbs _ _ ML))|].
      split; [apply (c45r_mbs_wf mbs _ _ ML MW); lia|].
      split; [exact (conj GU' GL)|]. split; [exact GW|].
      exact (c45r_mbs_are mbs _ _ ML gbs MW GARE).
    + split; [exact (c45r_kbs_n_sent kbs KL)|]. split; [exact (c45r_mbs_n_req mbs _ _ ML)|].
      split; [exact KEEP'|]. exact (conj MI (conj TM ST)).
  - exists W. split; [exact MU|]. split; [exact WM|]. intros x Hx Hout.
    destruct (HW x Hout) as [H|[H|H]]; unfold own_w.
    + left. clear - H HS. unfold c45_sp, FO_P, SLOT_FRAME, SLOT_STACK_Z in *. lia.
    + right; right; right; right; right. exists (e_md E), MD_SIZE. split; [left; reflexivity | exact H].
    + right; left. clear - H. unfold NK_N_SENT, NK_SIZE in *. lia.
Qed.

Lemma c45_r0 : forall E i gp ms, lenv_ok E -> c45_disp E i gp 5 ms ->
  evt rsegs (eqv_cl (c45_post E (ms_mem ms) (fun ms' => exists w, c45_13c70 E i gp w ms'))) ms.
Proof.
  intros E i gp ms LE D.
  destruct D as (ra & t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s3 & s4 & t3 & t4 & t5 & t6 & F & fc & m
                 & P & N & kbs & mbs & gbs & j0 & j1 & j2 & -> & FRM & Hi & HN & FR & CUR & B40 & B256
                 & KMG & KEEP & MACH).
  cbn [ms_mem].
  pose proof FR as (PT & CU & SV).
  pose proof KMG as ((KU0 & KL) & KW & _ & _ & _ & _ & _ & (MD0 & ML) & _).
  pose proof KW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hse & Hsd & _).
  pose proof MACH as (MI0 & _).
  destruct (c45r_lenv E LE) as (HS & Hmd1 & Hmd2 & Hmd3 & Hmk1 & Hmk2 & _ & Hpl1 & Hpl2 & Hpl3 & _ & _ & _ & _).
  assert (APg : apart (e_md E) MD_SIZE A_G_NL NK_SIZE) by (unfold apart, MD_SIZE, NK_SIZE, A_G_NL; lia).
  clear Hmd3.
  pose proof CUR as (k & Hk & HPk & HNk).
  assert (HSP1 : 0x960e0 <= c45_sp E) by (unfold c45_sp, SLOT_FRAME; lia).
  assert (HSP2 : c45_sp E + 480 <= 2 ^ 47) by (unfold c45_sp, SLOT_FRAME; lia).
  assert (Hmd2' : e_md E + 8856 <= c45_sp E) by (unfold c45_sp, SLOT_FRAME; lia).
  assert (Hmk' : 0 <= e_mk E < 2 ^ 64) by lia.
  change (rw_cells rsegs m (c45_sp E + FO_P) [C8 (wz (P + 1)); C8 (wz (N - 1))]) in CU.
  change (rw_cells rsegs m (c45_sp E + 64) [C8 (Z_to_bv 64 (P + 1)); C8 (Z_to_bv 64 (N - 1))]) in CU.
  unfold c45_R. change (wz (op_pc 5)) with (Z_to_bv 64 0x13bf4).
  destruct (Z.eq_dec N 1) as [E1|E1].
  - (* N = 1: w = 0 *)
    eapply c45r_pb; [exact E1 | lia |].
    eapply c45r_mb with (SP := c45_sp E) (md := e_md E) (mk := e_mk E) (i := i) (w := 0)
                        (j0 := j0) (kbs := kbs) (mbs := mbs) (m := m);
      [lia | exact HSP1 | exact HSP2 | exact Hmd1 | exact Hmd2' | exact Hmk' | exact Hi | exact APg
      | exact PT | exact KU0 | exact KL | exact MD0 | exact ML | exact Hse | exact Hsd | exact MI0 |].
    intros m2 x12 x13 MI2 MU2 WM2 KU2 MD2.
    assert (CU2 : rw_cells rsegs m2 (c45_sp E + FO_P) [C8 (wz (P + 1)); C8 (wz (N - 1))]).
    { apply (c45r_tr_rw (fun x => ~ outside (c45r_Wmb (e_md E)) x) (c45r_Wmb (e_md E)) m m2
               (fun x H => H) MU2 WM2 _ _ CU).
      intros x Hx Hn. cbv beta in Hn. apply Hn. clear - Hx HS Hmd2. cbn [cells_size csize Nat.add] in Hx.
      c45r_out. }
    assert (CUR2 : c45_cur E (P + 1) (N - 1)) by (exists (k + 1); lia).
    assert (HW' : forall x, ~ outside (c45r_Wmb (e_md E)) x -> c45r_P0 E x).
    { intros x Hx. clear - Hx. unfold c45r_P0. cbn [outside c45r_Wmb] in Hx.
      unfold MD_N_REQ, MD_SIZE in *. lia. }
    destruct (c45r_fin0 E i 0 (P + 1) (N - 1) m m2 (c45r_Wmb (e_md E)) kbs mbs gbs j0 j1 j2
                LE Hi ltac:(lia) PT SV B40 B256 KMG KEEP MACH CU2 CUR2 MI2 MU2 WM2 HW' KU2 MD2) as (M70 & SEG).
    apply c45_eqv_cl_of. unfold c45_post. cbn [ms_mem]. split; [|exact SEG].
    exists 0. apply c45r_13c70_of; [exact M70 | exact FRM].
  - (* N >= 2: w = the byte at P + 1 *)
    pose proof KEEP as (_ & _ & _ & _ & _ & _ & _ & _ & PL).
    destruct (nth_error (e_pl E) (Z.to_nat (k + 1))) as [b|] eqn:Eb;
      [| exfalso; apply nth_error_None in Eb; lia].
    pose proof (u8ro_read rsegs m (e_p0 E) (e_pl E) (k + 1) b (wa (P + 1)) PL Eb ltac:(lia)
                  ltac:(unfold wa; f_equal; lia)) as HRb.
    pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
    eapply c45r_pa; [exact HSP1 | exact HSP2 | lia | lia | lia | exact CU | exact HRb | exact MI0 |].
    intros m1 x12 x18 CU1 MI1 MU1 WM1.
    assert (HW1 : forall x, ~ outside [(c45_sp E + 64, c45_sp E + 80)] x ->
                    c45_sp E + 64 <= x < c45_sp E + 80) by (intros x; apply c45r_hw1).
    assert (PT1 : rw_cells rsegs m1 (c45_sp E) (c45_ptrs E j0)).
    { apply (c45r_tr_rw _ _ m m1 HW1 MU1 WM1 _ _ PT). unfold c45_ptrs. cbn [cells_size csize Nat.add].
      intros x Hx Hn. cbv beta in Hn. lia. }
    assert (KU1 : u8arr rsegs m1 A_G_NL kbs).
    { apply (c45r_tr_u8 _ _ m m1 HW1 MU1 WM1 _ _ KU0). rewrite KL.
      intros x Hx Hn. cbv beta in Hn. clear - Hx Hn HSP1. unfold A_G_NL, NK_SIZE in *. lia. }
    assert (MD1 : u8arr rsegs m1 (e_md E) mbs).
    { apply (c45r_tr_u8 _ _ m m1 HW1 MU1 WM1 _ _ MD0). rewrite ML.
      intros x Hx Hn. cbv beta in Hn. clear - Hx Hn Hmd2'. unfold MD_SIZE in *. lia. }
    eapply c45r_mb with (SP := c45_sp E) (md := e_md E) (mk := e_mk E) (i := i) (w := bv_unsigned b)
                        (j0 := j0) (kbs := kbs) (mbs := mbs) (m := m1);
      [lia | exact HSP1 | exact HSP2 | exact Hmd1 | exact Hmd2' | exact Hmk' | exact Hi | exact APg
      | exact PT1 | exact KU1 | exact KL | exact MD1 | exact ML | exact Hse | exact Hsd | exact MI1 |].
    intros m2 x12' x13 MI2 MU2 WM2 KU2 MD2.
    assert (CU2 : rw_cells rsegs m2 (c45_sp E + FO_P) [C8 (wz (P + 2)); C8 (wz (N + -2))]).
    { apply (c45r_tr_rw (fun x => ~ outside (c45r_Wmb (e_md E)) x) (c45r_Wmb (e_md E)) m1 m2
               (fun x H => H) MU2 WM2 _ _ CU1).
      intros x Hx Hn. cbv beta in Hn. apply Hn. clear - Hx HS Hmd2. cbn [cells_size csize Nat.add] in Hx.
      c45r_out. }
    assert (CUR2 : c45_cur E (P + 2) (N + -2)) by (exists (k + 2); lia).
    assert (MU' : munch ([(c45_sp E + 64, c45_sp E + 80)] ++ c45r_Wmb (e_md E)) m m2)
      by (apply (munch_trans _ m m1 m2); [apply c45r_munch_app_l; exact MU1 | apply c45r_munch_app_r; exact MU2]).
    assert (WM' : wmono rsegs m m2) by exact (wmono_trans rsegs m m1 m2 WM1 WM2).
    assert (HW' : forall x, ~ outside ([(c45_sp E + 64, c45_sp E + 80)] ++ c45r_Wmb (e_md E)) x -> c45r_P0 E x).
    { intros x Hx. rewrite c45r_outside_app in Hx.
      destruct (c45r_outside_dec [(c45_sp E + 64, c45_sp E + 80)] x) as [O1|O1].
      - destruct (c45r_outside_dec (c45r_Wmb (e_md E)) x) as [O2|O2]; [exfalso; exact (Hx (conj O1 O2))|].
        clear - O2. unfold c45r_P0. cbn [outside c45r_Wmb] in O2. unfold MD_N_REQ, MD_SIZE in *. lia.
      - apply c45r_hw1 in O1. unfold c45r_P0. left. unfold FO_P. lia. }
    destruct (c45r_fin0 E i (bv_unsigned b) (P + 2) (N + -2) m m2 _ kbs mbs gbs j0 j1 j2
                LE Hi ltac:(lia) PT SV B40 B256 KMG KEEP MACH CU2 CUR2 MI2 MU' WM' HW' KU2 MD2) as (M70 & SEG).
    apply c45_eqv_cl_of. unfold c45_post. cbn [ms_mem]. split; [|exact SEG].
    exists (bv_unsigned b). apply c45r_13c70_of; [exact M70 | exact FRM].
Qed.

Print Assumptions c45_r0.
