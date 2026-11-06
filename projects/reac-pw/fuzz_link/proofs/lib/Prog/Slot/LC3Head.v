(* The op_unmark arm (c3), plain image: the head of its segment, from the loop head of operation i with
   op byte % 6 = 3 to the loop test 0x13b4c:
     0x13a1c-0x13a64  the dispatch (cursor p+1 / n-1 stored back, byte % 6 = 3, jump table entry 3)
     0x13b24-0x13b28  kernel(sp + 0x40)            (leaf call: kernel_c.v)
     0x13b2c-0x13b48  model_begin                  (LC3Begin.c3_begin)
   ending in the cut c3_mb. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem printf_facts_c kernel_c mk_leaf.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC3Lib LC3Keep LC3Defs LC3Begin LC3Kern.
Local Open Scope Z_scope.

(* the byte % 6 the dispatch computes, 0x13a2c-0x13a44, for every byte *)
Lemma c3_mod6 : forall z, 0 <= z < 256 ->
  Z.land (bv_unsigned (Z_to_bv 64 (z + bv_swrap 32
     (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (z * 171))) 10))) 1))
      - bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (z * 171))) 10))) 3))))))
    255 = z mod 6.
Proof.
  intros z Hz.
  assert (C : forallb (fun z => Z.eqb (Z.land (bv_unsigned (Z_to_bv 64 (z + bv_swrap 32
     (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (z * 171))) 10))) 1))
      - bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (z * 171))) 10))) 3))))))
    255) (z mod 6)) (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in C.
  apply Z.eqb_eq, C. apply in_map_iff. exists (Z.to_nat z). split; [lia|]. apply in_seq. lia.
Qed.

Lemma c3_frame_join : forall m A pre mid post, rw_cells rsegs m A pre ->
  rw_cells rsegs m (A + Z.of_nat (cells_size pre)) mid ->
  rw_cells rsegs m (A + Z.of_nat (cells_size pre) + Z.of_nat (cells_size mid)) post ->
  rw_cells rsegs m A (pre ++ mid ++ post).
Proof.
  intros m A pre mid post H1 H2 H3. apply (proj2 (c3_rw_cells_app _ _ _ _)). split; [exact H1|].
  apply (proj2 (c3_rw_cells_app _ _ _ _)). split; [exact H2 | exact H3].
Qed.

Ltac c3h_sub := let x := fresh "x" in let Hx := fresh "Hx" in
  unfold sub_fp; intros x Hx; cbn [outside] in Hx |- *;
  unfold A_G_NAMES, G_NAMES_SIZE, A_LONG_ALIAS, LONG_ALIAS_SIZE, A_G_NL, NK_SIZE, NK_OPEN, NK_N_SENT, NK_CHUNK,
    SLOT_FRAME, SLOT_STACK_Z, A_ERRNO, A_TP, ERRNO_TP_OFF, MD_SIZE, MK_SIZE, MD_N_REQ in Hx |- *;
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.

Ltac c3h_dj := cbn [disjoint_from]; unfold A_G_NAMES, G_NAMES_SIZE, A_ODD, A_TEXTS, A_LONG_ALIAS, LONG_ALIAS_SIZE,
  NK_IF_NAME, NK_IF_INDEX, A_G_NL, A_GOT_GUARD_S, A_GUARD_S, NK_SIZE, NK_OPEN, NK_N_SENT, NK_CHUNK, SLOT_FRAME,
  SLOT_STACK_Z, A_ERRNO, A_TP, ERRNO_TP_OFF, MD_SIZE, MK_SIZE, MD_N_REQ;
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.

Section C3Head.
Hypothesis KERNEL_C : kernel_contract.

Lemma c3_head : forall (E : lenv) (i : Z) (gp : word) (ms : machine_state),
  lenv_ok E -> lh_ms E i gp ms -> lh_op E ms 3 -> evt rsegs (eqv_cl (c3_mb E i gp (ms_mem ms))) ms.
Proof.
  intros E i gp ms HE HL HOP.
  destruct HL as (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s4 & t3 & t4 & t5 & t6 & F & fc & m
                  & P & N & kbs & mbs & gbs & -> & FRM & Hi & HN & HM & MI & TM & ST).
  destruct HOP as (P' & b & HP' & Hb & Hop). cbn [ms_mem MS] in HP', Hb |- *.
  pose proof HE as HE0.
  destruct HE as (ES1 & ES2 & ES3 & (Hmd1 & Hmd2 & Hmd3) & (Hmk1 & Hmk2 & Hmk3) & Hmd16 & Hmk16 & Hmdmk & Hpl &
                  (Hp01 & Hp02 & Hp03) & Hp0md & Hp0mk & Hsv).
  pose proof (c3_img_free _ _ Hmd3 ltac:(unfold MD_SIZE; lia)) as Hmdi.
  pose proof (c3_img_free _ _ Hmk3 ltac:(unfold MK_SIZE; lia)) as Hmki.
  pose proof (c3_img_free _ _ Hp03 ltac:(lia)) as Hp0i.
  pose proof HM as HM0.
  destruct HM as ((j0 & j1 & j2 & nc & HC) & HSV & [HK LK] & HKW & HIF & Hop0 & Hmis & Hoc & Hop64 & HGN & HODD & HPOL &
                  HLA & HTX & HIP & [HMD LMD] & HMWF & [HMK LMK] & HMKWF & HMA & HCUR & HERR & HGD).
  (* the frame in three pieces: [0, 64), the cursor cells, [80, 376) *)
  unfold lh_cells in HC.
  change [CB 8 j0; C8 (wz A_ODD); C8 (wz (e_md E + MD_MARK)); C8 (wz A_EMPTY); C8 (wz (e_mk E)); C8 (wz A_G_NAMES);
          C8 (wz A_JT); C8 (wz GNL42); C8 (wz P); C8 (wz nc); CB 40 j1; CB 256 j2]
    with ([CB 8 j0; C8 (wz A_ODD); C8 (wz (e_md E + MD_MARK)); C8 (wz A_EMPTY); C8 (wz (e_mk E)); C8 (wz A_G_NAMES);
           C8 (wz A_JT); C8 (wz GNL42)] ++ ([C8 (wz P); C8 (wz nc)] ++ [CB 40 j1; CB 256 j2])) in HC.
  apply c3_rw_cells_app in HC as [HC1 HC23]. apply c3_rw_cells_app in HC23 as [HC2 HC3].
  cbn [cells_size csize Nat.add] in HC2, HC3. change (Z.of_nat 64) with 64 in HC2, HC3.
  change (Z.of_nat 16) with 16 in HC3.
  (* the cursor P is the frame's (lh_op reads the same cell) *)
  assert (EP : Z_to_bv 64 P' = Z_to_bv 64 P).
  { apply c3_le8_inj. pose proof HC2 as [[_ HB2] _]. cbn [cells_bytes cbytes] in HB2.
    apply (proj1 (bytes_at_app rsegs _ _ _ _)) in HB2. destruct HB2 as [HB2 _].
    unfold FO_P in HP'. exact (c3_bytes_at_same _ _ _ _ HP' HB2 ltac:(rewrite !length_le8; reflexivity)). }
  pose proof (c3_byte_read m P' b Hb) as HRB. rewrite EP in HRB.
  assert (Zb : bv_unsigned (zxb b) = bz b).
  { unfold zxb, bz. apply unsigned_lit. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
    change (2 ^ Z.of_N 8) with 256 in R. lia. }
  assert (Rb : 0 <= bz b < 256).
  { unfold bz. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
    lia. }
  destruct HCUR as [HPL (k & Hk & EPk & ENk)].
  clear HSV HIF HGN HODD HPOL HLA HTX HIP HMK LMK HMKWF HMA HERR HGD HP' Hb EP.
  pose proof (munch_refl [(e_S E - SLOT_FRAME + 64, e_S E - SLOT_FRAME + 80)] m) as MUd.
  pose proof (wmono_refl rsegs m) as WMd.
  unfold wz, L_LH, A_TP, GNL40, GNL42, A_JT, A_G_NL, MD_N_REQ, SLOT_FRAME, SLOT_STACK_Z, MD_SIZE, MK_SIZE, NK_SIZE in *.
  (* 0x13a1c-0x13a48: load the cursor, the byte, byte % 6, store p+1 and n-1 back *)
  do 12 step.
  rewrite (c3_mod6 (bv_unsigned (zxb b))) by lia. rewrite Zb, Hop.
  (* 0x13a4c sd a1; 0x13a50 bltu s9, a3 (4 < 3: not taken); the jump table *)
  step. step. if_false.
  do 5 step.
  (* 0x13b24 addi a0, sp, 0x40; 0x13b28 jal kernel *)
  step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  pose proof HM0 as (_ & _ & _ & _ & HIF & _ & _ & _ & _ & HGN & HODD & HPOL & HLA0 & HTX & HIP & _).
  assert (HIF1 : iftab_at m1 kbs link_tab)
    by (eapply c3_iftab_tr; [exact HIF | exact HIP | exact MUd | reflexivity | c3h_dj ..]).
  assert (HIP1 : ifptrs_at m1) by (eapply c3_ifptrs_tr; [exact HIP | exact MUd | c3h_dj]).
  assert (HTX1 : texts_at m1) by (eapply c3_texts_tr; [exact HTX | exact MUd | c3h_dj]).
  assert (HGN1 : gnames_at m1) by (eapply c3_gnames_tr; [exact HGN | exact MUd | c3h_dj]).
  assert (HODD1 : odd_at m1) by (eapply c3_odd_tr; [exact HODD | exact MUd | c3h_dj | c3h_dj]).
  assert (HLA1 : la_ok m1) by (eapply c3_la_tr; [exact HLA0 | exact MUd | exact WMd | c3h_dj]).
  eapply (leaf_run _ _ _ _ _ _ KERNEL_C) with (lo := e_S E - 65536).
  { (* kernel's Pre *)
    cbv beta.
    apply (c3_kernel_pre E _ m1 kbs (Z_to_bv 64 (P + 1)) (Z_to_bv 64 (N + -1))).
    - exact HE0.
    - rewrite mkR_sp. unfold SLOT_FRAME. apply unsigned_lit. lia.
    - rewrite mkR_a0. unfold SLOT_FRAME, FO_P. apply unsigned_lit. lia.
    - rewrite mkR_a0, unsigned_lit by lia. exact HC2.
    - exists (skipn (Z.to_nat (k + 1)) (e_pl E)). rewrite unsigned_lit by lia. split.
      + replace (P + 1) with (e_p0 E + Z.of_nat (Z.to_nat (k + 1))) by lia.
        apply c3_bytes_at_skipn; [exact HPL | lia].
      + rewrite length_skipn. rewrite unsigned_lit by lia. lia.
    - rewrite !unsigned_lit by lia. lia.
    - rewrite !unsigned_lit by lia. unfold SLOT_STACK_Z. lia.
    - split; [exact HK | exact LK].
    - exact HKW.
    - exact HIF1.
    - exact HIP1.
    - exact HTX1.
    - exact HGN1.
    - exact HODD1.
    - exact HLA1.
    - exact MI. }
  { exact MI. }
  { rewrite unsigned_lit by lia. exact ST. }
  { rewrite unsigned_lit by lia. lia. }
  { rewrite unsigned_lit by lia. lia. }
  (* after kernel *)
  intros regs' m2 MUk WMk MI2 ST2 POk.
  cbv beta in POk. rewrite unsigned_lit in MUk, ST2 by lia.
  rewrite mkR_a0, (unsigned_lit (e_S E - 480 + 64)) in MUk, POk by lia.
  rewrite (ret_pc_even 80684) by lia.
  destruct (POk kbs (conj HK LK)) as (kbs2 & [HK2 LK2] & HKW2 & Hnx2 & _ & _ & _ & _ & Hopn2 & Hopd2 & Hcls2 & Hmis2
                                       & _ & _ & Hnif2 & HIF2 & HCUR2 & HLA2).
  specialize (HIF2 link_tab HIF1).
  destruct (HCUR2 _ _ HC2) as (adv & Hadv & HC2').
  rewrite (unsigned_lit (N + -1)) in Hadv by lia.
  rewrite (unsigned_lit (P + 1)), (unsigned_lit (N + -1)) in HC2' by lia.
  clear POk HCUR2.
  assert (HC1' : rw_cells rsegs m2 (e_S E - 480) [CB 8 j0; C8 (Z_to_bv 64 A_ODD); C8 (Z_to_bv 64 (e_md E + MD_MARK));
     C8 (Z_to_bv 64 A_EMPTY); C8 (Z_to_bv 64 (e_mk E)); C8 (Z_to_bv 64 A_G_NAMES); C8 (Z_to_bv 64 67248);
     C8 (Z_to_bv 64 (203648 + 270336))])
    by (eapply (rw_cells_transport rsegs); [exact HC1 | exact MUk | exact WMk | cbn [cells_size csize Nat.add]; c3h_dj]).
  assert (HC3' : rw_cells rsegs m2 (e_S E - 480 + 64 + 16) [CB 40 j1; CB 256 j2])
    by (eapply (rw_cells_transport rsegs); [exact HC3 | exact MUk | exact WMk | cbn [cells_size csize Nat.add]; c3h_dj]).
  assert (HMD' : u8arr rsegs m2 (e_md E) mbs)
    by (eapply (u8arr_transport rsegs); [exact HMD | exact MUk | exact WMk | rewrite LMD; c3h_dj]).
  assert (HPL' : bytes_at rsegs m2 (e_p0 E) (e_pl E))
    by (eapply (bytes_at_transport rsegs); [exact HPL | exact MUk | c3h_dj]).
  eapply (c3_begin E i gp); [exact HE0 | exact HC1' | exact (conj HK2 LK2) | exact HKW2 | exact (conj HMD' LMD) | exact MI2 |].
  intros m5 MU5 WM5 MI5 HC1'' HK5 HM5.
  (* the whole write set of the head, from m to m5 *)
  set (WH := [(e_S E - 65536, e_S E - 480); (e_S E - 480 + 64, e_S E - 480 + 80); (203648, 203648 + NK_OPEN);
              (203648 + NK_N_SENT, 203648 + NK_N_SENT + 4); (A_LONG_ALIAS, A_LONG_ALIAS + LONG_ALIAS_SIZE);
              (e_md E, e_md E + 12); (e_md E + 8336, e_md E + 8336 + 4)]).
  assert (MUall : munch WH m m5).
  { eapply munch_extend; [ | exact MU5 | unfold WH; c3h_sub ].
    eapply munch_extend; [ | exact MUk | unfold WH; c3h_sub ].
    eapply munch_weaken; [ | exact MUd ]. unfold WH; c3h_sub. }
  assert (WMall : wmono rsegs m m5) by (eapply wmono_trans; [eapply wmono_trans; [exact WMd | exact WMk] | exact WM5]).
  pose proof HM0 as (_ & HSV & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLA & _ & _ & _ & _ & [HMK LMK] & HMKWF & HMA &
                     _ & HERR & HGD).
  pose proof (c3_kb_fields kbs2 LK2) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10).
  pose proof HKW2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hse2 & Hsd2 & _).
  destruct (c3_mbb_fields mbs (nk_socket_errno kbs2) (nk_send_errno kbs2) LMD Hse2 Hsd2) as (M1 & M2 & M3 & M4 & M5).
  apply evt_eqv_done. unfold c3_mb.
  do 19 eexists. exists F, fc, m5, (P + 1 + adv), (N + -1 - adv), (c3_kb kbs2),
    (c3_mbb mbs (nk_socket_errno kbs2) (nk_send_errno kbs2)), gbs.
  split; [reflexivity|].
  split; [exact FRM|]. split; [exact Hi|].
  split.
  { (* c3_mem *)
    split.
    { exists j0, j1, j2. unfold lh_cells.
      change [CB 8 j0; C8 (wz A_ODD); C8 (wz (e_md E + MD_MARK)); C8 (wz A_EMPTY); C8 (wz (e_mk E)); C8 (wz A_G_NAMES);
              C8 (wz A_JT); C8 (wz GNL42); C8 (wz (P + 1 + adv)); C8 (wz (N + -1 - adv)); CB 40 j1; CB 256 j2]
        with ([CB 8 j0; C8 (wz A_ODD); C8 (wz (e_md E + MD_MARK)); C8 (wz A_EMPTY); C8 (wz (e_mk E)); C8 (wz A_G_NAMES);
               C8 (wz A_JT); C8 (wz GNL42)] ++ ([C8 (wz (P + 1 + adv)); C8 (wz (N + -1 - adv))] ++ [CB 40 j1; CB 256 j2])).
      apply c3_frame_join; cbn [cells_size csize Nat.add];
        change (Z.of_nat 64) with 64; try change (Z.of_nat 16) with 16; unfold SLOT_FRAME.
      - exact HC1''.
      - eapply (rw_cells_transport rsegs); [exact HC2' | exact MU5 | exact WM5 | cbn [cells_size csize Nat.add];
          c3h_dj].
      - eapply (rw_cells_transport rsegs); [exact HC3' | exact MU5 | exact WM5 | cbn [cells_size csize Nat.add]; c3h_dj]. }
    split; [eapply (bytes_at_transport rsegs); [exact HSV | exact MUall | rewrite Hsv; unfold WH; c3h_dj]|].
    split; [exact HK5|]. split; [exact (c3_kb_wf kbs2 LK2 HKW2)|].
    split; [eapply c3_iftab_tr; [exact HIF | exact HIP | exact MUall | rewrite K10, Hnif2; reflexivity | unfold WH; c3h_dj ..]|].
    split; [eapply c3_gnames_tr; [exact HGN | exact MUall | unfold WH; c3h_dj]|].
    split; [eapply c3_odd_tr; [exact HODD | exact MUall | unfold WH; c3h_dj | unfold WH; c3h_dj]|].
    split; [eapply c3_policy_tr; [exact HPOL | exact MUall | unfold WH; c3h_dj]|].
    split.
    { destruct HLA2 as (la & HLA2). destruct HLA as (la0 & sl & _ & HSL & LSL). exists la, sl. split; [|split; [|exact LSL]].
      - eapply (rw_cells_transport rsegs); [exact HLA2 | exact MU5 | exact WM5 | cbn [cells_size csize Nat.add]; c3h_dj].
      - eapply (bytes_at_transport rsegs); [exact HSL | exact MUall | rewrite LSL; unfold WH; c3h_dj]. }
    split; [eapply c3_texts_tr; [exact HTX | exact MUall | unfold WH; c3h_dj]|].
    split; [eapply c3_ifptrs_tr; [exact HIP | exact MUall | unfold WH; c3h_dj]|].
    split; [exact HM5|].
    split; [exact (c3_mbb_wf mbs _ _ LMD Hse2 Hsd2 HMWF)|].
    split; [split; [eapply (u8arr_transport rsegs); [exact HMK | exact MUall | exact WMall | rewrite LMK; unfold WH; c3h_dj]
                   | exact LMK]|].
    split; [exact HMKWF|].
    split.
    { split; [eapply (bytes_at_transport rsegs); [exact HPL' | exact MU5 | c3h_dj]|].
      exists (k + 1 + adv). lia. }
    split; [eapply (wr_at_transport rsegs); [exact HERR | exact WMall]|].
    split; [eapply c3_guard_tr; [exact HGD | exact MUall | unfold WH; c3h_dj | unfold WH; c3h_dj]|].
    split; [exact MI5|].
    split; [eapply c3_task_mem_munch; [exact TM | exact MUall |]; intros x Hx HO;
            destruct (c3_not_outside _ _ HO) as (lo & hi & Hin & Hr); unfold WH in Hin; cbn [In] in Hin;
            unfold A_LONG_ALIAS, LONG_ALIAS_SIZE, NK_OPEN, NK_N_SENT in *;
            destruct Hin as [E1|[E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]]; inversion E1; subst lo hi; unfold TASK_SIZE; lia|].
    eapply (stk_transport_disjoint rsegs); [exact ST2 | exact MU5 | exact WM5 | c3h_dj]. }
  split; [unfold c3_kfacts; rewrite K6, K7, K8, K9, Hopn2, Hopd2, Hcls2, Hmis2, (c3_kb_n_sent kbs2 LK2); lia|].
  split; [unfold md_kstate; rewrite (c3_kb_kstate kbs2 LK2 HKW2); unfold nk_kstate;
         rewrite M1, M2, M3, Hnx2, (c3_kb_chunks kbs2 LK2 HKW2), K3; reflexivity|].
  split; [exact M4|].
  split; [destruct HMA as [HMA1 HMA2]; split; [rewrite M5; exact HMA1 | rewrite (c3_mbb_marks mbs _ _ LMD HMWF); exact HMA2]|].
  split; [eapply munch_weaken; [|exact MUall]; unfold c3_W, WH; c3h_sub|].
  exact WMall.
Qed.

End C3Head.

Print Assumptions c3_head.
