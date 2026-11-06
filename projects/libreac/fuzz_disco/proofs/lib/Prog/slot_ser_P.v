From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes ZBridge FP Image.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv slot_lib slot_ser_defs slot_ser_pure.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import printf_facts_c snprintf_c snprintf_stk_c jtok_is_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model reac_box_name_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c disco_table disco_json_text reac_disco_table_json_c tj_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model disco_json_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_ser_tokb slot_ser_Pq slot_ser slot_ser_J1.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_ser_P1 slot_ser_P2 slot_ser_P3 slot_ser_P4 slot_ser_P5.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require MemNorm.
Import ListNotations.
Open Scope Z_scope.

Lemma stk_cb_at : forall m A B n j, rw_cells rsegs m A [CB n j] -> B = A + Z.of_nat n -> stk rsegs m A B.
Proof.
  intros m A B n j H E. subst B. pose proof (stk_of_rw_cells rsegs m A _ H) as S.
  cbn [cells_size csize] in S. rewrite Nat.add_0_r in S. exact S.
Qed.

Lemma u32_cb : forall m A k, u32arr rsegs m A (used_ws k) -> rw_cells rsegs m A [CB 32 (u32s (used_ws k))].
Proof.
  intros m A k [B W]. apply ser_cb. split; [rewrite u32s_length, len_used; reflexivity|]. split; [exact B|].
  rewrite len_used in W. exact W.
Qed.

Theorem ser_P3 : reac_box_name_contract -> snprintf_stk_contract -> jtok_is_contract -> ser_P3_spec.
Proof.
  intros BNC SNK JT. unfold ser_P3_spec.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m canary
    X lo buf now i p count T os vpad j0 jage jwid jtok jused jnm jscr
    Esp Es3 Es6 Es11 HX0 HX16 HX1 Hnow Hb LT TOK LV JR Hbl BB CT CO C0 C160 C184 C208 CAGE CWID CTOK CUSED CNM CSCR
    BN GG GW FC MI TM ST HLO HI.
  assert (CX : p3ctx X lo buf now count T os vpad) by (unfold p3ctx; tauto).
  destruct (p3_count X lo buf now count T os vpad CX) as (Ec & Hc & Los & L6 & IB & G33 & L969).
  unfold SNPRINTF_K, IMG_END in HLO, HI.
  pose proof (ser_cb_bytes _ _ _ _ CT) as HT. pose proof (ser_cb_bytes _ _ _ _ CO) as HO.
  pose proof CUSED as CUw. apply ser_cb in CUw as (LU & BU & _).
  assert (S1 : stk rsegs m X (X + 16)) by (apply (stk_cb_at m X (X + 16) 16 j0 C0); lia).
  assert (S2 : stk rsegs m (X + 920) (X + 992)).
  { apply (stk_merge rsegs m (X + 920) (X + 944) (X + 992)); [apply (stk_cb_at m _ _ 24 jage CAGE); lia | | lia].
    apply (stk_merge rsegs m (X + 944) (X + 968) (X + 992)); [apply (stk_cb_at m _ _ 24 jwid CWID); lia | | lia].
    apply (stk_cb_at m _ _ 24 jtok CTOK); lia. }
  assert (S3 : stk rsegs m (X + 2320) (X + 2488)).
  { apply (stk_merge rsegs m (X + 2320) (X + 2344) (X + 2488)); [apply (stk_cb_at m _ _ 24 jnm CNM); lia | | lia].
    apply (stk_cb_at m _ _ 144 jscr CSCR); lia. }
  pose proof (rd_sub m (X + 512) T 384 4 HT ltac:(lia) ltac:(rewrite LT; lia)) as RN.
  assert (PRE : bytes_at rsegs m (X + 512) T /\ bytes_at rsegs m (X + 1024) (objs_bytes buf vpad os) /\
     bytes_at rsegs m buf (pf_bytes (tj_text T now ++ [0])) /\
     rw_cells rsegs m (X + 160) [C8 (Z_to_bv 64 i)] /\ rw_cells rsegs m (X + 184) [C8 (Z_to_bv 64 p)] /\
     rw_cells rsegs m (X + 208) [C8 (Z_to_bv 64 W0X0)] /\
     stk rsegs m X (X + 16) /\ stk rsegs m (X + 920) (X + 992) /\ stk rsegs m (X + 2320) (X + 2488) /\
     bytes_at rsegs m BN_TS bn_table /\ bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) /\
     bytes_at rsegs m GUARD (le8 canary) /\ stk rsegs m lo X /\ bytes_at rsegs m (X + 992) jused) by tauto.
  clear HT HO BB CT CO C0 C160 C184 C208 CAGE CWID CTOK CNM CSCR BN GG GW ST S1 S2 S3 BU.
  pose proof (munch_refl [(X + 992, X + 1024)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  subst sp s3 s6 s11. unfold SER_R12.
  assert (EXIT : forall (m' : word -> option byte) (F' : bvmap 5 word) (fc' : bv 32) (kk : Z)
      (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y23 y25 y26 y28 y29 y30 y31 : word),
      pinv X lo buf now i p T os vpad canary m kk m' -> MemNorm.task_mem rsegs m' -> frm0 fc' -> fl F F' ->
      evt rsegs QQ (MS (mkR y1 (Z_to_bv 64 X) gp tp y5 y6 y7 s0 y9 y10 y11 y12 y13 y14 y15 y16 y17
                           s2 (Z_to_bv 64 buf) y20 y21 y22 y23 s8 y25 y26 (Z_to_bv 64 now) y28 y29 y30 y31)
                       F' (Z_to_bv 64 0x14314) fc' None m' (seg_rom rsegs))).
  { intros m' F' fc' kk y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y23 y25 y26 y28 y29 y30 y31
      PI' TM' FC' FL'.
    pose proof PI' as (_ & _ & _ & C160' & C184' & _ & S1' & S2' & U' & S3' & _ & _ & _ & MI' & ST' & WM' & MU').
    step. step. step. step.
    destruct (stk_rw m' X (X + 16) X 16 S1' ltac:(lia) ltac:(lia)) as [j0' C0'].
    destruct (stk_rw m' (X + 920) (X + 992) (X + 920) 24 S2' ltac:(lia) ltac:(lia)) as [ja CA'].
    destruct (stk_rw m' (X + 920) (X + 992) (X + 944) 24 S2' ltac:(lia) ltac:(lia)) as [jw CW'].
    destruct (stk_rw m' (X + 920) (X + 992) (X + 968) 24 S2' ltac:(lia) ltac:(lia)) as [jt CT'].
    destruct (stk_rw m' (X + 2320) (X + 2488) (X + 2320) 24 S3' ltac:(lia) ltac:(lia)) as [jn CN'].
    destruct (stk_rw m' (X + 2320) (X + 2488) (X + 2344) 144 S3' ltac:(lia) ltac:(lia)) as [js CS'].
    pose proof (u32_cb m' (X + 992) kk U') as CU'.
    apply evt_done. unfold QQ.
    do 19 eexists. exists F', fc', m', j0', ja, jw, jt, (u32s (used_ws kk)), jn, js.
    split; [reflexivity|]. split; [exact FC'|]. split; [exact FL'|]. split; [exact MU'|]. split; [exact WM'|].
    split; [exact MI'|]. split; [exact TM'|]. split; [exact ST'|]. split; [exact C0'|]. split; [exact CA'|].
    split; [exact CW'|]. split; [exact CT'|]. split; [exact CU'|]. split; [exact CN'|exact CS']. }
  step. rewrite (unsigned_lit count) by lia. rewrite Z.add_0_r, swrap32_small by lia.
  step. rewrite lts_lit by lia. replace (count <? 0) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
  step. rewrite lw_val by (apply length_sub; rewrite ?LT; lia).
  change (bv_swrap 32 (bytes_le_to_Z (sub T 384 4))) with (n_of T). rewrite <- Ec.
  step. rewrite ser_eqb_refl. cbn [negb]. cbv iota.
  step. step. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  assert (U1 : u32arr rsegs m1 (X + 992) (used_ws 0)).
  { destruct CUSED as [[_ B] W]. split.
    - replace (u32s (used_ws 0)) with (cells_bytes [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                                                     C8 (Z_to_bv 64 0)])
        by (apply ser_map_unsigned_inj; vm_compute; reflexivity).
      exact B.
    - rewrite len_used. exact W. }
  destruct PRE as (HT & HO & HB & C160 & C184 & C208 & S1 & S2 & S3 & BN & GG & GW & ST0 & BU).
  assert (LO : Z.of_nat (length (objs_bytes buf vpad os)) <= 1296) by exact (objs_len_le buf vpad os count LV L6 Los Hc).
  assert (PI0 : pinv X lo buf now i p T os vpad canary m 0 m1).
  { unfold pinv.
    split; [eapply bytes_tr; [exact HT | exact MU |]; rewrite LT; intros x Hx; cbn [outside]; split; [lia | exact I]|].
    split; [eapply bytes_tr; [exact HO | exact MU |]; intros x Hx; cbn [outside]; split; [lia | exact I]|].
    split; [eapply bytes_tr; [exact HB | exact MU |]; rewrite length_pf_bytes, length_app; cbn [length];
            intros x Hx; cbn [outside]; split; [lia | exact I]|].
    split; [eapply rw_tr; [exact C160 | exact MU | exact WM |]; cbn [cells_size csize];
            intros x Hx; cbn [outside]; split; [lia | exact I]|].
    split; [eapply rw_tr; [exact C184 | exact MU | exact WM |]; cbn [cells_size csize];
            intros x Hx; cbn [outside]; split; [lia | exact I]|].
    split; [eapply rw_tr; [exact C208 | exact MU | exact WM |]; cbn [cells_size csize];
            intros x Hx; cbn [outside]; split; [lia | exact I]|].
    split; [eapply stk_tr; [exact S1 | exact MU | exact WM |]; intros x Hx; left; cbn [outside]; split; [lia | exact I]|].
    split; [eapply stk_tr; [exact S2 | exact MU | exact WM |]; intros x Hx; left; cbn [outside]; split; [lia | exact I]|].
    split; [exact U1|].
    split; [eapply stk_tr; [exact S3 | exact MU | exact WM |]; intros x Hx; left; cbn [outside]; split; [lia | exact I]|].
    split; [eapply bytes_tr; [exact BN | exact MU |]; rewrite len_bn_table; unfold BN_TS;
            intros x Hx; cbn [outside]; split; [lia | exact I]|].
    split; [eapply bytes_tr; [exact GG | exact MU |]; rewrite length_le8; unfold GOT_GUARD;
            intros x Hx; cbn [outside]; split; [lia | exact I]|].
    split; [eapply bytes_tr; [exact GW | exact MU |]; rewrite length_le8; unfold GUARD;
            intros x Hx; cbn [outside]; split; [lia | exact I]|].
    split; [exact MI|].
    split; [eapply stk_tr; [exact ST0 | exact MU | exact WM |]; intros x Hx; left; cbn [outside]; split; [lia | exact I]|].
    split; [exact WM|].
    eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]; intros; intuition lia. }
  assert (TM1 : MemNorm.task_mem rsegs m1).
  { eapply task_of; [exact TM | exact MU |]. intros x Hx O. cbn [outside] in O.
    destruct (bytes_at_mrd m (X + 992) jused x BU) as [b Hb'].
    - rewrite LU. lia.
    - exact (tsk_of_mrd m x b TM Hx Hb'). }
  clear HT HO HB C160 C184 C208 S1 S2 S3 BN GG GW ST0 BU U1 CUSED.
  step. rewrite eqb_lit by lia. destruct (Z.eqb_spec count 0) as [E0|E0]; cbv iota.
  - eapply EXIT; [exact PI0 | exact TM1 | exact FC | intros k _; reflexivity].
  - step. step. rewrite ltu_lit by lia.
    destruct (Z.ltb_spec count 8) as [L8|L8]; cbv iota.
    + step.
      eapply (obj_loop BNC SNK JT (Z.to_nat count)) with (k := 0) (X := X) (count := count) (lo := lo) (buf := buf)
        (now := now) (T := T) (os := os) (vpad := vpad) (m0 := m) (F0 := F) (canary := canary) (i0 := i) (p := p);
        [ first [ exact CX | exact PI0 | exact TM1 | exact FC | (intros k _; reflexivity) | reflexivity
                | (f_equal; lia) | lia ] .. |].
      intros m' F' fc' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y23 y25 y26 y28 y29 y30 y31 PI' TM' FC' FL'.
      eapply EXIT; [exact PI' | exact TM' | exact FC' | exact FL'].
    + step. step.
      eapply (obj_loop BNC SNK JT (Z.to_nat count)) with (k := 0) (X := X) (count := count) (lo := lo) (buf := buf)
        (now := now) (T := T) (os := os) (vpad := vpad) (m0 := m) (F0 := F) (canary := canary) (i0 := i) (p := p);
        [ first [ exact CX | exact PI0 | exact TM1 | exact FC | (intros k _; reflexivity) | reflexivity
                | (f_equal; lia) | lia ] .. |].
      intros m' F' fc' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y23 y25 y26 y28 y29 y30 y31 PI' TM' FC' FL'.
      eapply EXIT; [exact PI' | exact TM' | exact FC' | exact FL'].
Qed.
