(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2 Sj_new Sj_h_dtor Sj_h_deldtor Atp_fzwA Atp_pdtorA Pj_pdtor2wA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section PDtor2.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis DELA : del_cps RT e_delarr.
Hypothesis DOCD : docdtor_cps RT.
Hypothesis DELD : deldtor_cps RT.
Hypothesis AFV : forall Σ m, ART RT Σ m -> vt_dpi m.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, PID_STACK in *; lia.

Lemma pdtor_tail : forall (Σ : rts RT) PMc (ra sp gp t0 t1 t2 s0 s1 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m1 : mem) (P : Z) (L0 : list (Z * Z)) (lo : Z) (j : list byte),
  fdfs_only PMc -> mat_stable PMc ->
  pdone RT Σ m1 P L0 -> ART RT Σ m1 -> mem_inv bsegs m1 ->
  stk bsegs m1 lo (bv_unsigned sp + -32) -> rw_cells bsegs m1 (bv_unsigned sp + -32) [CB 8 j; C8 s1; C8 s0; C8 ra] ->
  rt_sp0 RT Σ - STACK_WIN <= lo -> lo + PID_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> unwind_ok ra s0 sp -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st (Z_to_bv 64 0xb7500) (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 0x6be3e8) t0 t1 t2 (Z_to_bv 64 P) (Z_to_bv 64 2147450880)
                                       (Z_to_bv 64 (P + 24)) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_docdtor m1)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists v m', ret_st ra sp gp (Z_to_bv 64 0x6be3e8) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m1 m'
         /\ rt_pres_fp L0 (rt_frames RT Σ) (bv_unsigned sp) [(P, P + 80)] m1 m') c
       /\ rt_live RT Σ' = L0 /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).
Proof using AF DOCD DELD AFV.
  intros Σ PMc ra sp gp t0 t1 t2 s0 s1 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 P L0 lo j
    FDO MST PD ART1 MI1 ST1 FR1 LOW LOR SPT SPA UOK FRM.
  destruct PD as (impl & tape & sbuf & idx & oc & ia & nt & ns & nidx & noc & nia & dcap & pre8 & mid & mid2 & rest & ipre8 & imid & irest
                  & FOBJ1 & PC1 & INM & I8 & IC1 & INS & INT & INA & INO & INX & NS0 & NT0 & NA0 & NO0 & NX0 & ND & EL0).
  intros T c1 (Hc1' & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ m1 ART1) as SP0R. pose proof (af_sp0_win RT AF Σ m1 ART1) as SP0W.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof FOBJ1 as (D8 & _ & (f & k & INF & FLO & FHI) & _). change ((80 + 7) / 8) with 10 in FHI.
  pose proof (fframe_ranges RT AF Σ m1 f k ART1 INF) as (F0 & F1 & FSZ & _).
  pose proof (af_frames_align RT AF Σ m1 f k ART1 INF) as (_ & FSEG).
  pose proof (af_live_range RT AF Σ m1 impl 96 ART1 INM) as (IM0 & IM1 & IMX).
  pose proof (af_frames_range RT AF Σ m1 f k ART1 INF) as (_ & _ & _ & FLV). specialize (FLV impl 96 INM).
  assert (NE : neq sbuf tape /\ neq ia oc /\ neq ia idx /\ neq ia impl /\ neq oc idx /\ neq oc impl /\ neq idx impl
               /\ neq sbuf ia /\ neq sbuf oc /\ neq sbuf idx /\ neq sbuf impl /\ neq tape ia /\ neq tape oc /\ neq tape idx /\ neq tape impl).
  { pose proof (fun i j x y => @nodup_nth_neq Z _ i j x y ND) as NN.
    repeat split; [exact (NN 0 1 _ _ eq_refl eq_refl ltac:(discriminate))%nat| exact (NN 2 3 _ _ eq_refl eq_refl ltac:(discriminate))%nat
      | exact (NN 2 4 _ _ eq_refl eq_refl ltac:(discriminate))%nat| exact (NN 2 5 _ _ eq_refl eq_refl ltac:(discriminate))%nat
      | exact (NN 3 4 _ _ eq_refl eq_refl ltac:(discriminate))%nat| exact (NN 3 5 _ _ eq_refl eq_refl ltac:(discriminate))%nat
      | exact (NN 4 5 _ _ eq_refl eq_refl ltac:(discriminate))%nat| exact (NN 0 2 _ _ eq_refl eq_refl ltac:(discriminate))%nat
      | exact (NN 0 3 _ _ eq_refl eq_refl ltac:(discriminate))%nat| exact (NN 0 4 _ _ eq_refl eq_refl ltac:(discriminate))%nat
      | exact (NN 0 5 _ _ eq_refl eq_refl ltac:(discriminate))%nat| exact (NN 1 2 _ _ eq_refl eq_refl ltac:(discriminate))%nat
      | exact (NN 1 3 _ _ eq_refl eq_refl ltac:(discriminate))%nat| exact (NN 1 4 _ _ eq_refl eq_refl ltac:(discriminate))%nat
      | exact (NN 1 5 _ _ eq_refl eq_refl ltac:(discriminate))%nat]. }
  destruct NE as (N01 & N1 & N2 & N3 & N4 & N5 & N6 & M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8).
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -32)) = usp + -32) by (apply unsigned_lit; ul).
  assert (SPA2 : (usp + -32) mod 16 = 0) by (replace (usp + -32) with (usp + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact SPA).
  assert (EUP : bv_unsigned (Z_to_bv 64 P) = P) by (apply unsigned_lit; ul).

  unfold pd_cells in PC1.
  change [CB 8 pre8; C8 (Z_to_bv 64 impl); CB 8 mid; C8 (Z_to_bv 64 tape); C8 (Z_to_bv 64 sbuf); C8 dcap; CB 16 mid2; C8 (Z_to_bv 64 0); CB 8 rest]
    with ([CB 8 pre8; C8 (Z_to_bv 64 impl); CB 8 mid] ++ [C8 (Z_to_bv 64 tape); C8 (Z_to_bv 64 sbuf); C8 dcap] ++ [CB 16 mid2; C8 (Z_to_bv 64 0); CB 8 rest]) in PC1.
  apply Sj_stage1_kit.rw_cells_app in PC1 as [PCa PC1]. apply Sj_stage1_kit.rw_cells_app in PC1 as [PCd PCz].
  cbn [cells_size csize Nat.add] in PCd, PCz. change (Z.of_nat 24) with 24 in PCd, PCz. replace (P + 24 + 24) with (P + 48) in PCz by lia.
  pose proof (fobj_sub RT AF Σ m1 P 80 24 24 FOBJ1 eq_refl ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as FOBJD1.

  apply (DOCD Σ PMc (Z_to_bv 64 0xb7500) (Z_to_bv 64 (usp + -32)) gp (Z_to_bv 64 0x6be3e8) t0 t1 t2 (Z_to_bv 64 P) (Z_to_bv 64 2147450880)
           (Z_to_bv 64 (P + 24)) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 (P + 24) tape sbuf nt ns dcap lo FDO MST);
    try reflexivity; try assumption; [.. | split; [exact Hc1'| apply (cfrm0_of_asta RT Σ PMc (eq _) c1 Hc1'); intros ms0 <-; exact FRM] |].
  - rewrite EU2. exact ST1.
  - rewrite EU2. ul.
  - rewrite EU2. ul.
  - rewrite EU2. exact SPA2.
  - unfold unwind_ok. rewrite EU2, EUP. left. ul.
  - intros c2 ((Σ1 & v1 & Hc2 & LV1 & FRS1 & SP1 & CR1) & FC2).
    destruct (ASTA_unpack_f RT Σ1 _ _ c2 Hc2 FC2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & ST2) & PRES2 & DOC2 & FOBJD2) & FRM2 & Hc2'). clear Hc2.
    destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
    cbn [ms_fcsr] in FRM2. rewrite EU2 in ST2, PRES2.
    rewrite (ret_pc_even 0xb7500) in Hc2' by lia.
    assert (INM1 : In (impl, 96) (rt_live RT Σ1)) by (rewrite LV1; apply live_remove_keep; [apply live_remove_keep; [exact INM| exact (not_eq_sym M4)]| exact (not_eq_sym M8)]).
    assert (INA1 : In (ia, nia) (rt_live RT Σ1)) by (rewrite LV1; apply live_remove_keep; [apply live_remove_keep; [exact INA| exact (not_eq_sym M1)]| exact (not_eq_sym M5)]).
    assert (INO1 : In (oc, noc) (rt_live RT Σ1)) by (rewrite LV1; apply live_remove_keep; [apply live_remove_keep; [exact INO| exact (not_eq_sym M2)]| exact (not_eq_sym M6)]).
    assert (INX1 : In (idx, nidx) (rt_live RT Σ1)) by (rewrite LV1; apply live_remove_keep; [apply live_remove_keep; [exact INX| exact (not_eq_sym M3)]| exact (not_eq_sym M7)]).
    assert (LOW1 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SP1; exact LOW).
    assert (INF1 : In (f, k) (rt_frames RT Σ1)) by (rewrite FRS1; exact INF).
    assert (CLP : forall x, P <= x < P + 80 -> aclient (rt_live RT Σ1) (rt_frames RT Σ) (usp + -32) x).
    { intros x Hx. right; right; right; left. exists f, k. split; [exact INF| lia]. }
    assert (FR2 : rw_cells bsegs m2 (usp + -32) [CB 8 j; C8 s1; C8 s0; C8 ra]).
    { apply (rw_cells_agree_nw bsegs m1 m2 _ _ FR1). apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES2).
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; ul|]. cbn [outside]. split; [ul| exact I]. }
    assert (PCa2 : rw_cells bsegs m2 P [CB 8 pre8; C8 (Z_to_bv 64 impl); CB 8 mid]).
    { apply (rw_cells_agree_nw bsegs m1 m2 _ _ PCa). apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES2).
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [apply CLP; lia|]. cbn [outside]. split; [lia| exact I]. }
    assert (PCz2 : rw_cells bsegs m2 (P + 48) [CB 16 mid2; C8 (Z_to_bv 64 0); CB 8 rest]).
    { apply (rw_cells_agree_nw bsegs m1 m2 _ _ PCz). apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES2).
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [apply CLP; lia|]. cbn [outside]. split; [lia| exact I]. }
    assert (IC2 : rw_cells bsegs m2 impl (dl_cells (Z_to_bv 64 0x17a150) ipre8 (Z_to_bv 64 idx) imid (Z_to_bv 64 oc) (Z_to_bv 64 ia) irest)).
    { apply (rw_cells_agree_nw bsegs m1 m2 _ _ IC1). apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES2).
      intros x Hx. unfold dl_cells in Hx. cbn [cells_size csize Nat.add] in Hx. split; [right; right; left; exists impl, 96; split; [exact INM1| lia]|].
      cbn [outside]. split; [lia| exact I]. }
    assert (PC2 : rw_cells bsegs m2 P (pd_cells pre8 (Z_to_bv 64 impl) mid (Z_to_bv 64 0) (Z_to_bv 64 0) dcap mid2 (Z_to_bv 64 0) rest)).
    { unfold pd_cells.
      change [CB 8 pre8; C8 (Z_to_bv 64 impl); CB 8 mid; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 dcap; CB 16 mid2; C8 (Z_to_bv 64 0); CB 8 rest]
        with ([CB 8 pre8; C8 (Z_to_bv 64 impl); CB 8 mid] ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 dcap] ++ [CB 16 mid2; C8 (Z_to_bv 64 0); CB 8 rest]).
      apply Sj_stage1_kit.rw_cells_app. split; [exact PCa2|]. apply Sj_stage1_kit.rw_cells_app. cbn [cells_size csize Nat.add]. change (Z.of_nat 24) with 24.
      replace (P + 24 + 24) with (P + 48) by lia. split; [exact DOC2| exact PCz2]. }
    assert (FOBJ2 : fobj RT Σ1 m2 P 80).
    { apply (fobj_pres_fp RT AF Σ Σ1 _ _ _ m1 m2 P 80 ART1 FOBJ1 PRES2 FRS1).
      intros r [<-|[]]. exists f, k. cbn [fst snd]. split; [exact INF| lia]. }
    assert (FPP : fp_client RT Σ1 lo [(P, P + 80)]).
    { constructor; [| constructor]. right; right. exists f, k. cbn [fst snd]. split; [exact INF1| lia]. }
    assert (SHZ2 : pt_shz [(P, P + 80)] m2 P impl).
    { intros m' MU WM. pose proof (art_fp_client RT AF Σ1 m2 m' lo _ ART2 LOW1 FPP MU WM) as ART'.
      split; [exact (fobj_shz RT AF Σ1 m' P 80 ART' (fobj_munch RT AF Σ1 m2 m' lo _ P 80 ART2 LOW1 FPP MU FOBJ2))|].
      split; [exact (shz_live RT AF Σ1 m' impl 96 ART' INM1 I8)|].
      change 96 with (8 * (96 / 8)). apply shz_of_acc; [| reflexivity| lia].
      apply (acc_lit RT AF Σ1 m' _ _ ART'). unfold ACC_LITS. repeat (first [left; reflexivity | right]). }

    pose proof (pt_walk2 usp P impl lo (Z_to_bv 64 0) (Z_to_bv 64 0) dcap (Z_to_bv 64 idx) (Z_to_bv 64 oc) (Z_to_bv 64 ia) pre8 mid mid2 rest ipre8 imid irest j
                  gp (Z_to_bv 64 0x6be3e8) u0 u1 u2 v1 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 s0 s1 ra F2 fc2 m2
                  ST2 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(lia) I8 SHZ2 (AFV Σ1 m2 ART2) FR2 PC2 IC2 MI2) as W2.
    lazymatch type of W2 with evt bsegs _ ?X =>
      assert (W2' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W2) end.
    clear W2.
    apply (cps_realizes bsegs _ _ _ c2 (asta_evt_c RT AF Σ1 PMc _ _ MST W2') Hc2'). clear W2'. intros c3 Hc3.
    destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (m3 & a2' & -> & MU3 & WM3 & MI3 & ST3 & PC3 & IC3) & Hc3'). clear Hc3.
    pose proof (art_fp_client RT AF Σ1 m2 m3 lo _ ART2 LOW1 FPP MU3 WM3) as ART3.

    rewrite <- ESP in Hc3'.
    apply (DELD Σ1 PMc ra sp gp (Z_to_bv 64 0x6be3e8) u0 (Z_to_bv 64 0xf5f18) u2 s0 s1 (Z_to_bv 64 impl) (Z_to_bv 64 0x17a198) a2' b3 b4 b5 b6 b7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m3 impl idx oc ia nidx noc nia (Z_to_bv 64 0x17a150) ipre8 imid irest lo FDO MST);
      try reflexivity; try assumption; [.. | split; [exact Hc3'| apply (cfrm0_of_asta RT Σ1 PMc (eq _) c3 Hc3'); intros ms0 <-; exact FRM2] |].
    + fold usp. ul.
    + intros c4 ((Σ2 & v2 & Hc4 & LV2 & FRS2 & SP2 & CR2) & FC4).
      apply Hk. split; [| exact FC4]. exists Σ2.
      split; [| split; [rewrite LV2, LV1; exact EL0| split; [rewrite FRS2, FRS1; reflexivity| split; [rewrite SP2, SP1; reflexivity| rewrite CR2, CR1; reflexivity]]]].
      eapply ASTA_conseq; [exact Hc4|]. intros ms (m4 & RS4 & AFT4 & PRES4). fold usp in AFT4, PRES4. exists v2, m4.
      split; [exact RS4|]. split; [exact AFT4|].
      assert (SUB2 : forall e, In e L0 -> In e (rt_live RT Σ2)) by (intros e He; rewrite LV2, LV1, EL0; exact He).
      assert (SUB1 : forall e, In e (rt_live RT Σ2) -> In e (rt_live RT Σ1)).
      { intros e He. rewrite LV2 in He. exact (live_remove_sub _ _ _ (live_remove_sub _ _ _ (live_remove_sub _ _ _ (live_remove_sub _ _ _ He)))). }
      assert (SUB0 : forall e, In e (rt_live RT Σ1) -> In e (rt_live RT Σ)).
      { intros e He. rewrite LV1 in He. exact (live_remove_sub _ _ _ (live_remove_sub _ _ _ He)). }
      intros a Ha Hout. cbn [outside] in Hout. destruct Hout as (HO & _).
      assert (Ha0 : aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a)).
      { apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact (SUB0 _ (SUB1 _ (SUB2 _ He)))| auto| lia]. }
      assert (E2 : m2 a = m1 a).
      { apply PRES2; [apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact (SUB1 _ (SUB2 _ He))| auto| lia]| cbn [outside]; split; [lia| exact I]]. }
      assert (E3 : m3 a = m2 a) by (apply MU3; cbn [outside]; split; [exact HO| exact I]).
      assert (E4 : m4 a = m3 a).
      { apply PRES4; [rewrite FRS1; apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact SUB2| auto| lia]| exact I]. }
      rewrite E4, E3, E2. reflexivity.
Qed.

Definition pdone_copy (Σ : rts RT) (m : mem) (P : Z) (L0 : list (Z * Z)) : Prop :=
  exists (impl tape sbuf idx oc ia nt ns nidx noc nia copy ncopy : Z) (dcap : word) (pre8 mid mid2 rest ipre8 imid irest : list byte),
    fobj RT Σ m P 80
    /\ rw_cells bsegs m P (pd_cells pre8 (Z_to_bv 64 impl) mid (Z_to_bv 64 tape) (Z_to_bv 64 sbuf) dcap mid2 (Z_to_bv 64 copy) rest)
    /\ In (impl, 96) (rt_live RT Σ) /\ impl mod 8 = 0
    /\ rw_cells bsegs m impl (dl_cells (Z_to_bv 64 0x17a150) ipre8 (Z_to_bv 64 idx) imid (Z_to_bv 64 oc) (Z_to_bv 64 ia) irest)
    /\ In (sbuf, ns) (rt_live RT Σ) /\ In (tape, nt) (rt_live RT Σ) /\ In (ia, nia) (rt_live RT Σ) /\ In (oc, noc) (rt_live RT Σ)
    /\ In (idx, nidx) (rt_live RT Σ) /\ In (copy, ncopy) (rt_live RT Σ)
    /\ 0 <= ns /\ 0 <= nt /\ 0 <= nia /\ 0 <= noc /\ 0 <= nidx /\ 0 <= ncopy
    /\ List.NoDup [sbuf; tape; ia; oc; idx; impl] /\ ~ In copy [sbuf; tape; ia; oc; idx; impl]
    /\ live_remove impl (live_remove idx (live_remove oc (live_remove ia (live_remove tape (live_remove sbuf (live_remove copy (rt_live RT Σ))))))) = L0.

Definition pdone2 (Σ : rts RT) (m : mem) (P : Z) (L0 : list (Z * Z)) : Prop := pdone RT Σ m P L0 \/ pdone_copy Σ m P L0.

Theorem pdtor2_ok : pdtor_cps RT pdone2.
Proof using AF DELA DOCD DELD AFV.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P L0 lo
    FDO MST EA0 ETP PD ART0 MI0 ST0 LOW LOR SPT SPA UOK FRM.
  destruct PD as [PD|PD].
  { exact (pdtor_ok RT AF DOCD DELD AFV Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P L0 lo
             FDO MST EA0 ETP PD ART0 MI0 ST0 LOW LOR SPT SPA UOK FRM). }
  subst a0 tp.
  destruct PD as (impl & tape & sbuf & idx & oc & ia & nt & ns & nidx & noc & nia & copy & ncopy & dcap & pre8 & mid & mid2 & rest & ipre8 & imid & irest
                  & FOBJ0 & PC0 & INM & I8 & IC0 & INS & INT & INA & INO & INX & INC & NS0 & NT0 & NA0 & NO0 & NX0 & NC0 & ND & NIC & EL0).
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof FOBJ0 as (D8 & _ & (f & k & INF & FLO & FHI) & _). change ((80 + 7) / 8) with 10 in FHI.
  pose proof (fframe_ranges RT AF Σ m f k ART0 INF) as (F0 & F1 & FSZ & _).
  pose proof (af_frames_align RT AF Σ m f k ART0 INF) as (_ & FSEG).
  pose proof (af_live_range RT AF Σ m impl 96 ART0 INM) as (IM0 & IM1 & _).
  pose proof (af_live_range RT AF Σ m copy ncopy ART0 INC) as (CP0 & CP1 & _).

  assert (NC : neq sbuf copy /\ neq tape copy /\ neq ia copy /\ neq oc copy /\ neq idx copy /\ neq impl copy).
  { unfold neq. cbn [In] in NIC. repeat split; intros E; apply NIC; rewrite <- E; tauto. }
  destruct NC as (C1 & C2 & C3 & C4 & C5 & C6).
  assert (FPC : fp_client RT Σ lo (pt_W usp P)).
  { unfold pt_W. constructor; [left; cbn [fst snd]; ul|]. constructor; [| constructor].
    right; right. exists f, k. cbn [fst snd]. split; [exact INF| lia]. }
  assert (SHZ0 : forall m' : mem, munch (pt_W usp P) m m' -> wmono bsegs m m' -> shz m' P 80).
  { intros m' MU WM. apply (fobj_shz RT AF Σ m'); [exact (art_fp_client RT AF Σ m m' lo _ ART0 LOW FPC MU WM)|].
    exact (fobj_munch RT AF Σ m m' lo _ P 80 ART0 LOW FPC MU FOBJ0). }

  pose proof (pt_walk1a usp P copy lo (Z_to_bv 64 impl) (Z_to_bv 64 tape) (Z_to_bv 64 sbuf) dcap pre8 mid mid2 rest ra gp (Z_to_bv 64 0x6be3e8) t0 t1 t2 s0 s1
                a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ST0 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(lia) ltac:(ul) ltac:(ul)
                (conj G1 G2) SHZ0 PC0 MI0) as W1.
  rewrite <- ESP in W1.
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & j & -> & MU1 & WM1 & MI1 & ST1 & FR1 & PC1) & Hc1'). clear Hc1.
  pose proof (art_fp_client RT AF Σ m m1 lo _ ART0 LOW FPC MU1 WM1) as ART1.
  pose proof (fobj_munch RT AF Σ m m1 lo _ P 80 ART0 LOW FPC MU1 FOBJ0) as FOBJ1.
  assert (IC1 : rw_cells bsegs m1 impl (dl_cells (Z_to_bv 64 0x17a150) ipre8 (Z_to_bv 64 idx) imid (Z_to_bv 64 oc) (Z_to_bv 64 ia) irest)).
  { apply (rw_cells_agree bsegs m m1 _ _ IC0); [| exact WM1]. apply (agree_of_munch _ _ _ _ MU1).
    pose proof (af_frames_range RT AF Σ m f k ART0 INF) as (_ & _ & _ & FLV). specialize (FLV impl 96 INM).
    intros x Hx. unfold dl_cells in Hx. cbn [cells_size csize Nat.add] in Hx. unfold pt_W. cbn [outside]. split; [ul|]. split; [lia| exact I]. }
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -32)) = usp + -32) by (apply unsigned_lit; ul).
  assert (SPA2 : (usp + -32) mod 16 = 0) by (replace (usp + -32) with (usp + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact SPA).
  assert (EUP : bv_unsigned (Z_to_bv 64 P) = P) by (apply unsigned_lit; ul).

  apply (DELA Σ PMc (Z_to_bv 64 0xb74f8) (Z_to_bv 64 (usp + -32)) gp (Z_to_bv 64 0x6be3e8) t0 t1 t2 (Z_to_bv 64 P) (Z_to_bv 64 2147450880)
           (Z_to_bv 64 copy) (Z_to_bv 64 copy) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 copy ncopy lo FDO MST INC eq_refl eq_refl
           ART1 MI1); [| | exact FRM| split; [exact Hc1'| apply (cfrm0_of_asta RT Σ PMc (eq _) c1 Hc1'); intros ms0 <-; exact FRM] |].
  - unfold call_ok. rewrite EU2. split; [exact ST1|]. split; [exact LOW|]. split; [ul|]. split; [ul| exact SPA2].
  - unfold unwind_ok. rewrite EU2, EUP. left. ul.
  - intros c2 ((Σ1 & v1 & Hc2 & LV1 & FRS1 & SP1 & CR1) & FC2).
    destruct (ASTA_unpack_f RT Σ1 _ _ c2 Hc2 FC2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & ST2) & PRES2) & FRM2 & Hc2'). clear Hc2.
    destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
    cbn [ms_fcsr] in FRM2. rewrite EU2 in ST2, PRES2.
    rewrite (ret_pc_even 0xb74f8) in Hc2' by lia.
    assert (KEEP : forall e, In e (rt_live RT Σ) -> fst e <> copy -> In e (rt_live RT Σ1)) by (intros e He Hn; rewrite LV1; apply live_remove_keep; assumption).
    assert (LOW1 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SP1; exact LOW).
    assert (FR2 : rw_cells bsegs m2 (usp + -32) [CB 8 j; C8 s1; C8 s0; C8 ra]).
    { apply (rw_cells_agree_nw bsegs m1 m2 _ _ FR1). apply (agree_of_pres _ _ _ _ _ _ PRES2).
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. left; ul. }
    assert (PC2 : rw_cells bsegs m2 P (pd_cells pre8 (Z_to_bv 64 impl) mid (Z_to_bv 64 tape) (Z_to_bv 64 sbuf) dcap mid2 (Z_to_bv 64 0) rest)).
    { apply (rw_cells_agree_nw bsegs m1 m2 _ _ PC1). apply (agree_of_pres _ _ _ _ _ _ PRES2).
      intros x Hx. unfold pd_cells in Hx. cbn [cells_size csize Nat.add] in Hx. right; right; right; left. exists f, k. split; [exact INF| lia]. }
    assert (IC2 : rw_cells bsegs m2 impl (dl_cells (Z_to_bv 64 0x17a150) ipre8 (Z_to_bv 64 idx) imid (Z_to_bv 64 oc) (Z_to_bv 64 ia) irest)).
    { apply (rw_cells_agree_nw bsegs m1 m2 _ _ IC1). apply (agree_of_pres _ _ _ _ _ _ PRES2).
      intros x Hx. unfold dl_cells in Hx. cbn [cells_size csize Nat.add] in Hx. right; right; left. exists impl, 96. split; [apply KEEP; [exact INM| exact C6]| lia]. }
    pose proof (fobj_pres RT AF Σ Σ1 _ _ m1 m2 P 80 ART1 FOBJ1 PRES2 FRS1) as FOBJ2.
    assert (PD2 : pdone RT Σ1 m2 P L0).
    { exists impl, tape, sbuf, idx, oc, ia, nt, ns, nidx, noc, nia, dcap, pre8, mid, mid2, rest, ipre8, imid, irest.
      split; [exact FOBJ2|]. split; [exact PC2|]. split; [apply KEEP; [exact INM| exact C6]|]. split; [exact I8|]. split; [exact IC2|].
      split; [apply KEEP; [exact INS| exact C1]|]. split; [apply KEEP; [exact INT| exact C2]|]. split; [apply KEEP; [exact INA| exact C3]|].
      split; [apply KEEP; [exact INO| exact C4]|]. split; [apply KEEP; [exact INX| exact C5]|].
      repeat (split; [assumption|]). rewrite LV1. exact EL0. }

    pose proof (pt_walk1b P (Z_to_bv 64 (usp + -32)) gp (Z_to_bv 64 0x6be3e8) u0 u1 u2 v1 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6
                  F2 fc2 m2 ltac:(ul)) as W2.
    lazymatch type of W2 with evt bsegs _ ?X =>
      assert (W2' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W2) end.
    clear W2.
    apply (cps_realizes bsegs _ _ _ c2 (asta_evt_c RT AF Σ1 PMc _ _ MST W2') Hc2'). clear W2'. intros c3 Hc3.

    apply (pdtor_tail Σ1 PMc ra sp gp u0 u1 u2 s0 s1 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 P L0 lo j FDO MST PD2 ART2 MI2);
      [exact ST2| exact FR2| exact LOW1| exact LOR| exact SPT| exact SPA| exact UOK| exact FRM2
      | split; [exact Hc3| apply (cfrm0_of_asta RT Σ1 PMc _ c3 Hc3); intros ms0 <-; exact FRM2] |].
    intros c4 ((Σ2 & Hc4 & LV2 & FRS2 & SP2 & CR2) & FC4).
    apply Hk. split; [| exact FC4]. exists Σ2.
    split; [| split; [exact LV2| split; [rewrite FRS2, FRS1; reflexivity| split; [rewrite SP2, SP1; reflexivity| rewrite CR2, CR1; reflexivity]]]].
    eapply ASTA_conseq; [exact Hc4|]. intros ms (v4 & m4 & RS4 & AFT4 & PRES4). fold usp in AFT4, PRES4. exists v4, m4.
    split; [exact RS4|]. split; [exact AFT4|].
    assert (SUB1 : forall e, In e L0 -> In e (rt_live RT Σ1)).
    { intros e He. rewrite <- EL0 in He. rewrite LV1.
      exact (live_remove_sub _ _ _ (live_remove_sub _ _ _ (live_remove_sub _ _ _ (live_remove_sub _ _ _ (live_remove_sub _ _ _ (live_remove_sub _ _ _ He)))))). }
    intros a Ha Hout. cbn [outside] in Hout. destruct Hout as (HO & _).
    assert (Ha0 : aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a)).
    { apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; pose proof (SUB1 e He) as X; rewrite LV1 in X; exact (live_remove_sub _ _ _ X)| auto| lia]. }
    pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha0) as SPL.
    assert (E1 : m1 a = m a) by (apply MU1; unfold pt_W; cbn [outside]; split; [clear - SPL LOW LOR; ul|]; split; [exact HO| exact I]).
    assert (E2 : m2 a = m1 a).
    { apply PRES2. apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact SUB1| auto| lia]. }
    assert (E4 : m4 a = m2 a).
    { apply PRES4; [rewrite FRS1; exact Ha| cbn [outside]; split; [exact HO| exact I]]. }
    rewrite E4, E2, E1. reflexivity.
Qed.

End PDtor2.
