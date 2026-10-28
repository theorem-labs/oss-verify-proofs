(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import PropExec ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP Frame.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_rlkit D_libiface D_auxv I_lkit X_aexdefs X_ixdefs X_atcxa Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_num_akit Sj_h_alloc Sj_stage2_iface Atp_hkit4A Atp_fzwA Atp_setcapA Atp_defsA Atp_activewA Atp_pid1A Atp_pidiA Pj_rtkA Pj_cpsA Pj_defsA Pj_hdefsA Imp_hdefsA Imp_ifaceA Imp_libifaceA Imp_ios_defsA Imp_gsidefsA Imp_lftoi1A Imp_lftoi2A Imp_lftoi3A Imp_lftoi4A Imp_segdefsA Imp_segA3a Imp_segA3 Imp_segA2 Imp_segA1b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma rw_cells_CB_of_bytes : forall (m : mem) a (l : list byte), bytes_at bsegs m a l -> wr_at bsegs m a (Z.of_nat (length l)) -> rw_cells bsegs m a [CB (length l) l].
Proof. intros m a l BY WR. split; [split; [cbn; split; [reflexivity| exact I]| cbn; rewrite app_nil_r; exact BY]| cbn; rewrite Nat.add_0_r; exact WR]. Qed.

Definition gofv (v : option Z) : Z := match v with Some _ => 1 | None => 0 end.

Definition imp_setup_costA (n : Z) : Z := GRSI_COST_A + imp_body_costA n.

Section Setup1.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PDONE : rts RT -> mem -> Z -> list (Z * Z) -> Prop.
Hypothesis PDT : pdtor_cps RT PDONE.
Hypothesis PDFP : pdone_fpA RT PDONE.
Hypothesis PID : pj_pid_cpsA RT (pj_libA sj_lib) PDONE.
Hypothesis OKARM : forall PMc, imp_okarm_cpsA RT PMc.
Hypothesis GRSI : grsi_icontractA RT.
Hypothesis ATCXA : atcxa_icontract RT.
Local Ltac ul := unfold FUZZ_STACK, PID_STACK, GRSI_STACK_A, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.

Section WithPM.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Notation aevt := (aevt RT PMc).

Lemma imp_firstA : forall (Σ0 Σ : rts RT) (K : config -> Prop) (usp sp' f lo d : Z) (bs : list byte)
    (x1 gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8x s9x s10x s11x t3 t4 t5 t6 : word) (cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word)
    Fr fc (m0 m : mem) (cb : Z) (j0 j8 j48 j128 j152 j192 h3 jx : list byte),
  let n := Z.of_nat (length bs) in
  impG (rt_sp0 RT Σ0) usp sp' f lo ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo sp' ->
  rt_frames RT Σ = [(f, 5%nat)] -> rt_live RT Σ = rt_live RT Σ0 -> rt_sp0 RT Σ = rt_sp0 RT Σ0 -> cb + imp_setup_costA n <= rt_credit RT Σ -> 0 <= cb ->
  (forall q k, In (q, k) (rt_live RT Σ) -> 0 < k) -> Z.of_nat (length (rt_live RT Σ)) + 14 <= LIVE_MAX ->
  0 < d -> n < 2^26 -> bytes_at bsegs m d bs ->
  ((exists p k, In (p, k) (rt_live RT Σ0) /\ p <= d /\ d + n <= p + k) \/ (bs = [] /\ d < SEGTOP_A)) ->

  rw_cells bsegs m sp' (imp_locals2 j0 j8 f j48 (wz d) j128 j152 j192) -> stk bsegs m (sp' + 216) (usp - 104) ->
  rw_cells bsegs m (usp - 104) (imp_savedA cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11) ->
  rw_cells bsegs m f (fz_hdr (C8 (wz IMP_MAGIC0)) (C8 (wz IMP_HDR_DESC_A)) (C8 (wz e_fuzz)) h3) ->
  rw_cells bsegs m (shad f) (map C1 imp_sh20) -> rw_cells bsegs m (shad f + 20) [CB 68 jx] -> rw_cells bsegs m (shad f + 88) (map C1 imp_sh88) ->
  setupF m f ->

  imp_libA None m -> aex4A m ->
  libc_nl m0 -> io_ssp m0 ->
  (forall a : word, aclient (rt_live RT Σ0) [] usp (bv_unsigned a) -> outside IMP_XFP_A (bv_unsigned a) -> m a = m0 a) ->
  frm0 fc ->
  imp_fin_k RT PMc K Σ0 None usp lo cra gp (wz TPV_A) cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 m0 cb ->
  aevt Σ K (setup_st IMP_GTEST_A x1 sp' gp t0 t1 t2 usp (sxb (Z_to_bv 8 0)) a1 a2 a3 a4 a5 a6 a7 f (wz (-14)) n s8x s9x s10x s11x t3 t4 t5 t6 Fr fc m).
Proof using AF RC PDT PDFP PID OKARM GRSI ATCXA FDO MST.
  intros until jx. intros n G ARTx MIx STx FRSx LVx SPx CRx CB0 LVP LVB D0 NB BS INLV L2 STp SV HD SH20 SHX SH88 SF LB0 AX4 NL0 IOS0 PRES FRM KFIN.
  pose proof (impG_facts _ _ _ _ _ G) as (F0 & FLO & SH0 & SLO & SLO' & GLO & GLO' & LO64 & LSP & LUSP & SPH & SPH' & SP6 & F8).
  pose proof G as (FSEG & F64 & FTOP & SHB0 & SHT & SEP & LOW & LOR & UT & SPR & SPA & SPW & SPT).
  assert (EU : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  assert (INF : In (f, 5%nat) (rt_frames RT Σ)) by (rewrite FRSx; left; reflexivity).
  assert (LV0x : forall e, In e (rt_live RT Σ0) -> In e (rt_live RT Σ)) by (intros e He; rewrite LVx; exact He).
  pose proof (imp_csep RT AF Σ0 Σ m usp sp' f lo ARTx INF LV0x SPx G) as CSEP.
  assert (SHF0 : shad f = f / 8 + SHB) by reflexivity. unfold SHB in SHF0.
  pose proof (af_frames_range RT AF Σ m f 5%nat ARTx INF) as (_ & _ & _ & FLV). change (fs_size 5) with 2048 in FLV.
  pose proof (proj1 (af_fshadow_apart RT AF Σ m f 5%nat ARTx INF)) as FSL. change (fs_size 5) with 2048 in FSL.
  assert (SHF : shad (f + 2048) = shad f + 256) by (unfold shad; Z.div_mod_to_equations; lia). rewrite SHF in FSL.
  assert (COK : forall Σy mx, rt_sp0 RT Σy = rt_sp0 RT Σ0 -> stk bsegs mx lo sp' -> call_ok RT Σy mx (Z_to_bv 64 sp') lo).
  { intros Σy mx SPy STm. unfold call_ok. rewrite EU, SPy. split; [exact STm|]. split; [lia|]. split; [ul|]. split; [ul| clear - SPA; Z.div_mod_to_equations; lia]. }
  assert (NLIOS : forall mx, (forall a : word, aclient (rt_live RT Σ0) [] usp (bv_unsigned a) -> outside IMP_XFP_A (bv_unsigned a) -> mx a = m0 a) -> libc_nl mx).
  { intros mx PR. apply (libc_nl_agree m0 mx NL0). intros a Ha. apply PR; [right; left; apply client_static_intro; unfold LIBC_NL in Ha; lia|].
    unfold LIBC_NL in Ha. unfold IMP_XFP_A, LIB_FP, IMP_FP_A, IMP_AEX_W, IMP_VEC_OBJ_A, IMP_GUARD_A, IMP_AVL_GUARD_A. aex_lits. cbn [outside app]. repeat split; try exact I; lia. }
  destruct LB0 as (ST0 & LB & LX & TP & LK). destruct ST0 as (L00 & AVL0 & SPAN0 & AVG0 & ARR0 & VEC0 & GD0).

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (imp_walk12a usp sp' f n x1 gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8x s9x s10x s11x t3 t4 t5 t6 Fr fc m GD0 MIx)|].
  cbv beta. intros ms1 (m1 & a1' & a2' & -> & MU1 & WM1 & MI1 & GD1). apply evt_done.
  assert (AG01 : forall P : Z -> Prop, (forall x, P x -> ~ (IMP_GUARD_A <= x < IMP_GUARD_A + 2)) -> agree_on P m m1).
  { intros P HP a Ha. apply MU1. cbn [outside]. pose proof (HP _ Ha). split; [lia| exact I]. }
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 sp' ARTx ltac:(rewrite SPx; lia)); [| exact WM1]. intros a Ha. apply MU1. cbn [outside]. split; [| exact I].
    intros Hc. apply Ha. right; left. apply client_static_intro. unfold IMP_GUARD_A in Hc. lia. }
  assert (ST1 : stk bsegs m1 lo sp') by (apply (stk_agree_nw bsegs m m1 _ _ STx); apply AG01; intros x Hx; cbv beta in Hx; unfold IMP_GUARD_A; clear - Hx GLO; lia).

  assert (PRE1 : grsi_preA m1).
  { unfold grsi_preA. unfold IMP_GUARD_A, IMP_AVL_GUARD_A, IMP_AVP_SPAN_A, IMP_AVP_GUARD_A, IMP_AVP_ARR_A, IMP_VEC_OBJ_A, g00 in *.
    split; [apply (lib0_agree m m1 L00); apply AG01; intros x Hx; lia|].
    split; [apply (rw_cells_agree_nw bsegs m m1 _ _ AVL0); apply AG01; intros x Hx; cbn in Hx; lia|].
    split; [apply (rw_cells_agree_nw bsegs m m1 _ _ SPAN0); apply AG01; intros x Hx; cbn in Hx; lia|].
    split; [apply (rw_cells_agree_nw bsegs m m1 _ _ AVG0); apply AG01; intros x Hx; cbn in Hx; lia|].
    split; [apply (rw_cells_agree_nw bsegs m m1 _ _ ARR0); apply AG01; intros x Hx; cbn in Hx; lia|].
    apply (rw_cells_agree_nw bsegs m m1 _ _ VEC0); apply AG01; intros x Hx; cbn in Hx; lia. }
  assert (N0 : 0 <= n < 2^26) by (subst n; lia).
  assert (PC0 : 0 <= pj_pid_costA n).
  { assert (CAP : 32 <= Z.max n 32 <= 2^26) by (change (2^26) with 67108864 in *; lia).
    pose proof (al_sbuf_bounds _ CAP) as B1. pose proof (al_tape_bounds _ CAP) as B2. pose proof (sc_idx_bounds (Z.max n 32) ltac:(lia)) as B3.
    pose proof (mcost_nonneg (al_sbuf (Z.max n 32)) ltac:(lia)). pose proof (mcost_nonneg (al_tape (Z.max n 32)) ltac:(lia)). pose proof (mcost_nonneg (sc_idx (Z.max n 32)) ltac:(lia)).
    pose proof (mcost_nonneg 96 ltac:(lia)). pose proof (mcost_nonneg 8192 ltac:(lia)). pose proof (mcost_nonneg 1024 ltac:(lia)). pose proof (mcost_nonneg (n + 64) ltac:(lia)).
    unfold pj_pid_costA, pid_cost6, S2A_COST, Sj_num_iface.NUMA_CREDIT. lia. }
  assert (GC : GRSI_COST_A <= rt_credit RT Σ) by (unfold imp_setup_costA, imp_body_costA, imp_okarm_costA, IMP_PUT_COST_A in CRx; clear - CRx CB0 PC0 N0; lia).
  unfold setup_st.
  eapply (aevt_icall RT PMc).
  { exact (GRSI Σ PMc (wz IMP_GRSIRET_A) (wz sp') gp (wz TPV_A) t0 t1 t2 (wz usp) (wz sp') (wz IMP_VEC_OBJ_A) a1' a2' a3 a4 a5 a6 a7
            (wz (-8)) (wz (shad f)) (wz (-14)) (wz n) (wz f) (wz (shad f + 20)) s8x s9x s10x s11x t3 t4 t5 t6 Fr fc m1 lo
            FDO MST eq_refl eq_refl PRE1 ltac:(rewrite FRSx; cbn; unfold GRSI_FRAMES_A, FRAMES_MAX; lia) LVP ltac:(unfold GRSI_LIVE_A; lia)
            GC
            ART1 MI1 ltac:(rewrite EU; exact ST1) ltac:(rewrite SPx; lia) ltac:(rewrite EU; ul) ltac:(rewrite EU; ul) ltac:(rewrite EU; clear - SPA; Z.div_mod_to_equations; lia)
            ltac:(unfold unwind_ok; rewrite EU, !unsigned_lit by ul; right; right; lia) FRM). }
  intros c (Σ1 & A8 & HQ & LV1 & A80 & A16 & FRS1 & SP1 & CR1). eexists Σ1, _. split; [exact HQ|].
  intros ms' (vr & m2 & RS2 & (ART2 & MI2 & ST2) & PR2 & POST2).
  apply (ret_stF_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 ms' (fun ms => aevt Σ1 K ms) RS2).
  intros w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 w3 w4 w5 w6 F2. rewrite EU in ST2, PR2.
  rewrite (ret_pc_even IMP_GRSIRET_A) by (unfold IMP_GRSIRET_A; lia). rewrite FRSx in FRS1, PR2. rewrite SPx in SP1.
  assert (A8IN : In (A8, 8) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
  assert (LV01 : forall e, In e (rt_live RT Σ0) -> In e (rt_live RT Σ1)) by (intros e He; rewrite LV1; right; exact (LV0x _ He)).

  assert (AG12 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x /\ outside GRSI_W x) -> agree_on P m1 m2).
  { intros P HP a Ha. destruct (HP _ Ha) as (C0 & C1). apply PR2; [rewrite FRSx in C0; exact C0| exact C1]. }
  assert (GWL : forall x, outside GRSI_W x <-> (~ (0x6bc000 <= x < 0x6bc018) /\ ~ (0x6bc100 <= x < 0x6bc102) /\ ~ (0x6bc160 <= x < 0x6bc170) /\ ~ (0x6bc180 <= x < 0x6bc182)
                                              /\ ~ (0x6bc1a0 <= x < 0x6bc1a8) /\ ~ (0x6bc1c0 <= x < 0x6bc1ec) /\ ~ (0x6bc220 <= x < 0x6bc222))).
  { intros x. unfold GRSI_W, IMP_VEC_OBJ_A, IMP_AVL_GUARD_A, IMP_AVP_SPAN_A, IMP_AVP_GUARD_A, IMP_AVP_ARR_A, SJ_SINGLETON. cbn [outside]. tauto. }
  assert (AWL : forall x, outside AEX_W x <-> (~ (AEX <= x < AEX + 80) /\ ~ (AEX_A0 <= x < AEX_A0 + 48))).
  { intros x. unfold AEX_W. cbn [outside]. tauto. }

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [apply (imp_walk12b usp sp' f n _ gp w0 w1 w2 vr e1 e2 e3 e4 e5 e6 e7 _ s8x s9x s10x s11x w3 w4 w5 w6 F2 fc m2)|].
  cbv beta. intros ms3 <-. apply evt_done.

  assert (AX42 : aex4 m2).
  { destruct AX4 as [(p1 & p2 & f4 & f5 & T4) (b4 & b5 & A4)]. split.
    - exists p1, p2, f4, f5. apply (rw_cells_agree_nw bsegs m m2 _ _ T4). eapply agree_trans; [apply AG01| apply AG12]; intros x Hx; unfold aex_tbl in Hx; cbn [cells_size csize Nat.add] in Hx;
        unfold IMP_GUARD_A; aex_lits; [lia| split; [right; left; apply client_static_intro; lia| apply GWL; lia]].
    - exists b4, b5. apply (rw_cells_agree_nw bsegs m m2 _ _ A4). eapply agree_trans; [apply AG01| apply AG12]; intros x Hx; unfold aex_args in Hx; cbn [cells_size csize Nat.add] in Hx;
        unfold IMP_GUARD_A; aex_lits; [lia| split; [right; left; apply client_static_intro; lia| apply GWL; lia]]. }
  assert (PRES2 : forall a : word, aclient (rt_live RT Σ0) [] usp (bv_unsigned a) -> outside IMP_XFP_A (bv_unsigned a) -> m2 a = m0 a).
  { intros a Ha Ho. rewrite <- (PRES a Ha Ho). unfold IMP_XFP_A, LIB_FP, IMP_FP_A, IMP_VEC_OBJ_A, IMP_GUARD_A, IMP_AVL_GUARD_A in Ho. cbn [outside app] in Ho.
    eapply eq_trans; [apply (AG12 (fun x => x = bv_unsigned a)); [| reflexivity]| apply (AG01 (fun x => x = bv_unsigned a)); [| reflexivity]]; intros x ->.
    - split; [apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact LV0x| intros e []| lia]|]. apply GWL. clear - Ho. lia.
    - unfold IMP_GUARD_A. clear - Ho. lia. }
  unfold setup_st.
  eapply (aevt_icall RT PMc).
  { exact (ATCXA Σ1 PMc (wz IMP_ATCXARET_A) (wz sp') gp (wz TPV_A) w0 w1 w2 (wz usp) (wz sp') (wz IMP_XVECDTOR_A) (wz IMP_VEC_OBJ_A) (wz IMP_DSO_A) e3 e4 e5 e6 e7
             (wz (-8)) (wz (shad f)) (wz (-14)) (wz n) (wz f) (wz (shad f + 20)) s8x s9x s10x s11x w3 w4 w5 w6 F2 fc m2 X_VECDTOR AEX_VEC_OBJ IMP_DSO_A lo
             FDO MST eq_refl eq_refl eq_refl eq_refl ltac:(unfold X_VECDTOR; lia) ltac:(unfold AEX_VEC_OBJ; lia) AX42 (NLIOS m2 PRES2) ART2 MI2 (COK Σ1 m2 SP1 ST2)). }
  intros c' HQ'. eexists Σ1, _. split; [exact HQ'|].
  intros ms'' (m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PR3 & (p1 & p2 & T6) & A6).
  apply (ret_stF_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 ms'' (fun ms => aevt Σ1 K ms) RS3).
  intros u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F3. rewrite EU in ST3, PR3.
  rewrite (ret_pc_even IMP_ATCXARET_A) by (unfold IMP_ATCXARET_A; lia). rewrite FRS1 in PR3.
  assert (AX6 : aex6A m3) by (split; [exists p1, p2; exact T6| exact A6]).
  assert (AG23 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ1) [(f, 5%nat)] sp' x /\ outside AEX_W x) -> agree_on P m2 m3).
  { intros P HP a Ha. destruct (HP _ Ha) as (C0 & C1). exact (PR3 a C0 C1). }

  assert (GD3 : rw_cells bsegs m3 IMP_GUARD_A [C1 z8; C1 (Z_to_bv 8 2)]).
  { apply (rw_cells_agree_nw bsegs m1 m3 _ _ GD1). eapply agree_trans; [apply AG12| apply AG23]; intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold IMP_GUARD_A in Hx.
    - split; [right; left; apply client_static_intro; lia| apply GWL; lia].
    - split; [right; left; apply client_static_intro; lia| apply AWL; aex_lits; lia]. }
  assert (AGS : forall P : Z -> Prop, (forall x, P x -> sp' <= x < usp) -> agree_on P m m3).
  { intros P HP. eapply agree_trans; [apply AG01; intros x Hx; pose proof (HP _ Hx); unfold IMP_GUARD_A; clear - H GLO LOR SPR; ul|].
    eapply agree_trans; [apply AG12| apply AG23]; intros x Hx; pose proof (HP _ Hx); (split; [left; ul|]); [apply GWL; clear - H GLO LOR SPR; ul| apply AWL; aex_lits; clear - H GLO LOR SPR; ul]. }
  assert (L23 : rw_cells bsegs m3 sp' (imp_locals2 j0 j8 f j48 (Z_to_bv 64 d) j128 j152 j192)).
  { apply (rw_cells_agree_nw bsegs m m3 _ _ L2). apply AGS. intros x Hx. unfold imp_locals2 in Hx. cbn [cells_size csize Nat.add] in Hx. lia. }
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (imp_walk12c usp sp' f d n _ gp u0 u1 u2 _ b1 b2 b3 b4 b5 b6 b7 _ _ s8x s9x s10x s11x u3 u4 u5 u6 _ _ j0 j8 j48 j128 j152 j192 F3 fc m3 SP6 SPH' GD3 L23 MI3)|].
  cbv beta. intros ms4 (m4 & -> & MU4 & WM4 & MI4 & GD4). apply evt_done.
  assert (AG34 : forall P : Z -> Prop, (forall x, P x -> ~ (IMP_GUARD_A <= x < IMP_GUARD_A + 2)) -> agree_on P m3 m4).
  { intros P HP a Ha. apply MU4. cbn [outside]. pose proof (HP _ Ha). split; [lia| exact I]. }
  assert (ART4 : ART RT Σ1 m4).
  { apply (art_client_write RT AF Σ1 m3 m4 sp' ART3 ltac:(rewrite SP1; lia)); [| exact WM4]. intros a Ha. apply MU4. cbn [outside]. split; [| exact I].
    intros Hc. apply Ha. right; left. apply client_static_intro. unfold IMP_GUARD_A in Hc. lia. }
  assert (ST4 : stk bsegs m4 lo sp') by (apply (stk_agree_nw bsegs m3 m4 _ _ ST3); apply AG34; intros x Hx; cbv beta in Hx; unfold IMP_GUARD_A; clear - Hx GLO; lia).

  assert (AG04 : forall P : Z -> Prop,
            (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x /\ ~ (IMP_GUARD_A <= x < IMP_GUARD_A + 2) /\ outside GRSI_W x /\ outside AEX_W x) ->
            agree_on P m m4).
  { intros P HP. eapply agree_trans; [apply AG01; intros x Hx; destruct (HP _ Hx) as (C0 & C1 & C2 & C3); exact C1|].
    eapply agree_trans; [apply AG12; intros x Hx; destruct (HP _ Hx) as (C0 & C1 & C2 & C3); split; assumption|].
    eapply agree_trans; [apply AG23; intros x Hx; destruct (HP _ Hx) as (C0 & C1 & C2 & C3); split; [| exact C3]|].
    - rewrite FRSx in C0. apply (aclient_mono _ _ _ _ _ _ _ C0); [intros e He; rewrite LV1; right; exact He| intros e He; exact He| lia].
    - apply AG34. intros x Hx. destruct (HP _ Hx) as (C0 & C1 & C2 & C3). exact C1. }

  assert (ZST : forall x, sp' <= x < usp -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x /\ ~ (IMP_GUARD_A <= x < IMP_GUARD_A + 2) /\ outside GRSI_W x /\ outside AEX_W x).
  { intros x Hx. unfold IMP_GUARD_A. split; [left; ul|]. split; [clear - Hx GLO LOR SPR; ul|]. split; [apply GWL; clear - Hx GLO LOR SPR; ul| apply AWL; aex_lits; clear - Hx GLO LOR SPR; ul]. }
  assert (ZFR : forall x, f <= x < f + 2040 -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x /\ ~ (IMP_GUARD_A <= x < IMP_GUARD_A + 2) /\ outside GRSI_W x /\ outside AEX_W x).
  { intros x Hx. unfold IMP_GUARD_A. split; [right; right; right; left; exists f, 5%nat; change (fs_size 5) with 2048; split; [exact INF| lia]|].
    split; [clear - Hx FSEG; ul|]. split; [apply GWL; clear - Hx FSEG; ul| apply AWL; aex_lits; clear - Hx FSEG; ul]. }
  assert (ZSH : forall x, shad f <= x < shad f + 156 -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x /\ ~ (IMP_GUARD_A <= x < IMP_GUARD_A + 2) /\ outside GRSI_W x /\ outside AEX_W x).
  { intros x Hx. unfold IMP_GUARD_A. split; [right; right; right; right; exists f, 5%nat; split; [exact INF| change (fs_size 5) with 2048; rewrite SHF; lia]|].
    split; [clear - Hx SHB0; ul|]. split; [apply GWL; clear - Hx SHB0; ul| apply AWL; aex_lits; clear - Hx SHB0; ul]. }
  assert (ZCS : forall x lo' hi', lo' <= x < hi' -> (0x6bcc28 <= lo' /\ hi' <= 0x6bdad8) \/ (0x6be3b8 <= lo' /\ hi' <= 0x6be3c0) \/ (0x6de758 <= lo' /\ hi' <= 0x6de75c) ->
            aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x /\ ~ (IMP_GUARD_A <= x < IMP_GUARD_A + 2) /\ outside GRSI_W x /\ outside AEX_W x).
  { intros x lo' hi' Hx R. unfold IMP_GUARD_A. split; [right; left; apply client_static_intro; lia|]. split; [lia|]. split; [apply GWL; lia| apply AWL; aex_lits; lia]. }
  assert (PRES4 : forall a : word, aclient (rt_live RT Σ0) [] usp (bv_unsigned a) -> outside IMP_XFP_A (bv_unsigned a) -> m4 a = m0 a).
  { intros a Ha Ho. rewrite <- (PRES a Ha Ho). apply (AG04 (fun x => x = bv_unsigned a)); [| reflexivity]. intros x ->.
    unfold IMP_XFP_A, LIB_FP, IMP_FP_A, IMP_AEX_W, IMP_VEC_OBJ_A, IMP_GUARD_A, IMP_AVL_GUARD_A in Ho. revert Ho. aex_lits. cbn [outside app]. intros Ho. unfold IMP_GUARD_A.
    split; [apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact LV0x| intros e []| lia]|]. split; [clear - Ho; lia|]. split; [apply GWL; clear - Ho; lia| apply AWL; aex_lits; clear - Ho; lia]. }

  destruct POST2 as (LM2 & AVL2 & SPAN2 & AVG2 & ARR2 & VEC2 & VW2).
  destruct SF as ((jsb & FB) & (i0 & i1 & i2 & i3 & FI) & (jos & FO) & (jtmp & FT)).
  apply (imp_setup2A RT AF RC PDONE PDT PDFP PID OKARM PMc FDO MST Σ0 Σ1 K None A8 usp sp' f lo d bs _ gp u0 u1 u2 _ _ b2 b3 b4 b5 b6 b7 _ s8x s9x s10x s11x u3 u4 u5 u6
           cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 F3 fc m0 m4 cb G ART4 MI4 ST4 FRS1);
    [cbn [xnewA app]; rewrite LV1, LVx; reflexivity| exact SP1| | exact CB0| exact A8IN| intros B EB; discriminate EB| | rewrite LV1; cbn [length]; lia| exact D0| exact NB| | exact INLV| | | exact NL0| exact IOS0| exact PRES4| exact FRM| exact KFIN].
  - clear - CRx CR1 CB0. unfold imp_setup_costA in CRx. subst n. lia.
  - intros q k Hq. rewrite LV1 in Hq. destruct Hq as [E|Hq]; [injection E as <- <-; lia| exact (LVP q k Hq)].
  - apply (bytes_at_agree bsegs m m4 _ _ BS). apply AG04. intros x Hx. cbv beta in Hx.
    destruct INLV as [(p & k & Hin & P1 & P2)| (E0 & DL)]; [| rewrite E0 in Hx; cbn [length] in Hx; lia].
    pose proof (af_live_range RT AF Σ m p k ARTx (LV0x _ Hin)) as (_ & Y3 & Y4). rewrite SPx in Y3. unfold IMP_GUARD_A.
    split; [right; right; left; exists p, k; split; [exact (LV0x _ Hin)| subst n; lia]|].
    split; [clear - Hx P1 P2 Y4; subst n; ul|]. split; [apply GWL; clear - Hx P1 P2 Y4; subst n; ul| apply AWL; aex_lits; clear - Hx P1 P2 Y3 Y4 LOW LOR SPR; subst n; ul].
  -
    split; [| split; [| split; [| split; [| split; [| split; [split; [| split; [| split; [| split; [| split]]]]|]]]]]].
    + exists j0, j8, j48, j128, j152, j192. apply (rw_cells_agree_nw bsegs m3 m4 _ _ L23). apply AG34. intros x Hx. unfold imp_locals2 in Hx. cbn [cells_size csize Nat.add] in Hx. unfold IMP_GUARD_A. clear - Hx GLO LOR SPR. ul.
    + apply (stk_agree_nw bsegs m m4 _ _ STp). apply AG04. intros x Hx. cbv beta in Hx. apply ZST. lia.
    + apply (rw_cells_agree_nw bsegs m m4 _ _ SV). apply AG04. intros x Hx. rewrite imp_savedA_size in Hx. apply ZST. lia.
    + exists h3. apply (rw_cells_agree_nw bsegs m m4 _ _ HD). apply AG04. intros x Hx. unfold fz_hdr in Hx. cbn [cells_size csize Nat.add] in Hx. apply ZFR. lia.
    + split; [| split; [exists jx|]];
        [apply (rw_cells_agree_nw bsegs m m4 _ _ SH20)| apply (rw_cells_agree_nw bsegs m m4 _ _ SHX)| apply (rw_cells_agree_nw bsegs m m4 _ _ SH88)]; apply AG04; intros x Hx;
        [rewrite cells_size_map_C1' in Hx; change (Z.of_nat (length imp_sh20)) with 20 in Hx| cbn [cells_size csize Nat.add] in Hx| rewrite cells_size_map_C1' in Hx; change (Z.of_nat (length imp_sh88)) with 68 in Hx];
        apply ZSH; lia.
    + left. apply (libm_agree m2 m4 LM2). eapply agree_trans; [apply AG23| apply AG34]; intros x Hx; unfold sj4_rng in Hx; unfold IMP_GUARD_A; [| lia].
      split; [right; left; apply client_static_intro; lia| apply AWL; aex_lits; lia].
    + unfold imp_restA. unfold IMP_AVL_GUARD_A, IMP_AVP_SPAN_A, IMP_AVP_GUARD_A, IMP_AVP_ARR_A, IMP_VEC_OBJ_A, IMP_GUARD_A, g11 in *.
      assert (T24 : forall P : Z -> Prop, (forall x, P x -> imp_rest_rng A8 x /\ ~ (7061568 <= x < 7061570)) -> agree_on P m2 m4).
      { intros P HP. pose proof (af_live_range RT AF Σ1 m2 A8 8 ART2 A8IN) as (_ & Y3 & Y4). rewrite SP1 in Y3.
        eapply agree_trans; [apply AG23| apply AG34]; intros x Hx; destruct (HP _ Hx) as [H GN]; [| exact GN]. unfold imp_rest_rng in H.
        destruct H as [H|[H|[H|[H|[H|[H|H]]]]]]; [split; [right; left; apply client_static_intro; lia| apply AWL; aex_lits; lia] ..|].
        split; [right; right; left; exists A8, 8; split; [exact A8IN| lia]| apply AWL; aex_lits; clear - H Y3 Y4 LOW LOR SPR; ul]. }
      split; [apply (rw_cells_agree_nw bsegs m2 m4 _ _ AVL2); apply T24; intros x Hx; cbn in Hx; unfold imp_rest_rng; lia|].
      split; [apply (rw_cells_agree_nw bsegs m2 m4 _ _ SPAN2); apply T24; intros x Hx; cbn in Hx; unfold imp_rest_rng; lia|].
      split; [apply (rw_cells_agree_nw bsegs m2 m4 _ _ AVG2); apply T24; intros x Hx; cbn in Hx; unfold imp_rest_rng; lia|].
      split; [apply (rw_cells_agree_nw bsegs m2 m4 _ _ ARR2); apply T24; intros x Hx; cbn in Hx; unfold imp_rest_rng; lia|].
      split; [apply (rw_cells_agree_nw bsegs m2 m4 _ _ VEC2); apply T24; intros x Hx; cbn in Hx; unfold imp_rest_rng; lia|].
      split; [exact GD4|].
      pose proof (af_live_range RT AF Σ1 m2 A8 8 ART2 A8IN) as (_ & _ & A8SG).
      split; [apply (rw_cells_agree_nw bsegs m2 m4 _ _ VW2); apply T24; intros x Hx; cbn in Hx; unfold imp_rest_rng; clear - Hx A8SG; ul|]. lia.
    + apply (LOCBA_agree m m4 LB). apply AG04. intros x Hx. apply (ZCS x PJ_LOC_LO_A PJ_LOC_HI_A Hx). unfold PJ_LOC_LO_A, PJ_LOC_HI_A. lia.
    + destruct LX as (X1 & X2 & X3). unfold locx3, LOC_CVC, LOC_CVW in *. split; [| split];
        [apply (rw_cells_agree_nw bsegs m m4 _ _ X1)| apply (rw_cells_agree_nw bsegs m m4 _ _ X2)| apply (rw_cells_agree_nw bsegs m m4 _ _ X3)];
        apply AG04; intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply (ZCS x _ _ Hx); lia.
    + unfold imp_tplocA in *. apply (rw_cells_agree_nw bsegs m m4 _ _ TP). apply AG04. intros x Hx. cbn [cells_size csize Nat.add] in Hx. unfold TPV_A in Hx. apply (ZCS x _ _ Hx). lia.
    + apply (lockwA_agree m m4 LK). apply AG04. intros x Hx. unfold PJ_LOCKW_A in Hx. apply (ZCS x _ _ Hx). lia.
    + apply (aex6A_agree m3 m4 AX6). apply AG34. intros x (l & h & Hin & R). unfold IMP_AEX_W in Hin. revert R. aex_lits. cbn [In] in Hin. intros R. unfold IMP_GUARD_A.
      destruct Hin as [E|[E|[]]]; injection E as <- <-; lia.
  -
    apply (setupF_agree m m4 f). { split; [exists jsb; exact FB|]. split; [exists i0, i1, i2, i3; exact FI|]. split; [exists jos; exact FO| exists jtmp; exact FT]. }
    apply AG04. intros x Hx. apply ZFR. lia.
Qed.

Lemma imp_setupA : forall (Σ0 Σ : rts RT) (K : config -> Prop) (v : option Z) (usp sp' f lo d : Z) (bs : list byte)
    (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3x s4x s6x s7x s8x s9x s10x s11x t3 t4 t5 t6 : word) (cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word)
    Fr fc (m0 m : mem) (cb : Z) (j0 j8 j120 : list byte),
  let n := Z.of_nat (length bs) in
  impG (rt_sp0 RT Σ0) usp sp' f lo ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo sp' ->
  rt_frames RT Σ = [(f, 5%nat)] -> rt_live RT Σ = rt_live RT Σ0 -> rt_sp0 RT Σ = rt_sp0 RT Σ0 -> cb + imp_setup_costA n <= rt_credit RT Σ -> 0 <= cb ->
  (forall B, v = Some B -> In (B, 8) (rt_live RT Σ0)) ->
  (forall q k, In (q, k) (rt_live RT Σ) -> 0 < k) -> Z.of_nat (length (rt_live RT Σ)) + 14 <= LIVE_MAX ->
  0 < d -> n < 2^26 -> bytes_at bsegs m d bs ->
  ((exists p k, In (p, k) (rt_live RT Σ0) /\ p <= d /\ d + n <= p + k) \/ (bs = [] /\ d < SEGTOP_A)) ->
  rw_cells bsegs m sp' (imp_locals0 j0 j8 (wz d) j120) -> stk bsegs m (sp' + 216) (usp - 104) ->
  rw_cells bsegs m (usp - 104) (imp_savedA cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11) ->
  wr_at bsegs m f 2040 -> wr_at bsegs m (shad f) 256 ->
  imp_libA v m -> aexvA v m ->
  libc_nl m0 -> io_ssp m0 ->
  (forall a : word, aclient (rt_live RT Σ0) [] usp (bv_unsigned a) -> outside IMP_XFP_A (bv_unsigned a) -> m a = m0 a) ->
  frm0 fc ->
  imp_fin_k RT PMc K Σ0 v usp lo cra gp (wz TPV_A) cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 m0 cb ->
  aevt Σ K (MS (mkR (wz IMP_SMRET_A) (wz sp') gp (wz TPV_A) t0 t1 t2 (wz usp) (wz sp') (wz f) a1 a2 a3 a4 a5 a6 a7
                    (wz SHB) s3x s4x (wz n) s6x s7x s8x s9x s10x s11x t3 t4 t5 t6) Fr (wz IMP_SMRET_A) fc None m (seg_rom bsegs)).
Proof using AF RC PDT PDFP PID OKARM GRSI ATCXA FDO MST.
  intros until j120. intros n G ARTx MIx STx FRSx LVx SPx CRx CB0 VIN LVP LVB D0 NB BS INLV L0 STp SV WRF WRS LBv AXv NL0 IOS0 PRES FRM KFIN.
  pose proof (impG_facts _ _ _ _ _ G) as (F0 & FLO & SH0 & SLO & SLO' & GLO & GLO' & LO64 & LSP & LUSP & SPH & SPH' & SP6 & F8).
  pose proof G as (FSEG & F64 & FTOP & SHB0 & SHT & SEP & LOW & LOR & UT & SPR & SPA & SPW & SPT).
  assert (EU : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  assert (INF : In (f, 5%nat) (rt_frames RT Σ)) by (rewrite FRSx; left; reflexivity).
  assert (LV0x : forall e, In e (rt_live RT Σ0) -> In e (rt_live RT Σ)) by (intros e He; rewrite LVx; exact He).
  pose proof (imp_csep RT AF Σ0 Σ m usp sp' f lo ARTx INF LV0x SPx G) as CSEP.
  assert (SHF0 : shad f = f / 8 + SHB) by reflexivity. unfold SHB in SHF0.
  assert (SHF : shad (f + 2048) = shad f + 256) by (unfold shad; Z.div_mod_to_equations; lia).
  assert (SEP' : f + 2048 <= shad f \/ shad f + 156 <= f) by lia.
  assert (N0 : 0 <= n < 2^26) by (subst n; lia).
  assert (DR : 0 <= d < 2^64).
  { destruct INLV as [(p & k & Hin & P1 & P2)|(E & DL)]; [| clear - D0 DL; ul].
    pose proof (af_live_range RT AF Σ m p k ARTx (LV0x _ Hin)) as (R0 & R1 & R2). pose proof (af_sp0_range RT AF Σ m ARTx). clear - D0 P1 P2 R1 N0 H. ul. }
  assert (COK : forall mx, stk bsegs mx lo sp' -> call_ok RT Σ mx (Z_to_bv 64 sp') lo).
  { intros mx STm. unfold call_ok. rewrite EU, SPx. split; [exact STm|]. split; [lia|]. split; [ul|]. split; [ul| clear - SPA; Z.div_mod_to_equations; lia]. }

  destruct (wr_at_rw_CB m f 32 (wr_at_sub _ f 2040 f 32 WRF ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jH & FH). change (Z.to_nat 32) with 32%nat in FH.
  apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FH; [| reflexivity]. cbn [mk_CB_cells app] in FH.
  repeat match type of FH with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "hb" in set (j := t) in FH; clearbody j end.
  lazymatch type of FH with rw_cells _ _ _ [CB 8 ?x0; CB 8 ?x1; CB 8 ?x2; CB 8 ?x3] => change (rw_cells bsegs m f (fz_hdr (CB 8 x0) (CB 8 x1) (CB 8 x2) x3)) in FH end.
  destruct (wr_at_rw_CB m (f + 32) 88 (wr_at_sub _ f 2040 (f + 32) 88 WRF ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jsb & FB). change (Z.to_nat 88) with 88%nat in FB.
  destruct (wr_at_rw_CB m (f + 160) 544 (wr_at_sub _ f 2040 (f + 160) 544 WRF ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (ji & FI). change (Z.to_nat 544) with 544%nat in FI.
  apply (rw_cells_split_CB bsegs _ _ [] 544 _ [] [136; 136; 136; 136]%nat) in FI; [| reflexivity]. cbn [mk_CB_cells app] in FI.
  repeat match type of FI with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "ib" in set (j := t) in FI; clearbody j end.
  destruct (wr_at_rw_CB m (f + 832) 264 (wr_at_sub _ f 2040 (f + 832) 264 WRF ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jos & FO). change (Z.to_nat 264) with 264%nat in FO.
  destruct (wr_at_rw_CB m (f + 1168) 24 (wr_at_sub _ f 2040 (f + 1168) 24 WRF ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jtmp & FT). change (Z.to_nat 24) with 24%nat in FT.
  destruct (wr_at_rw_CB m (shad f) 156 (wr_at_sub _ (shad f) 256 (shad f) 156 WRS ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jsh & FS). change (Z.to_nat 156) with 156%nat in FS.

  apply (aevt_evt RT AF PMc MST).
  lazymatch type of FH with rw_cells _ _ _ (fz_hdr (CB 8 ?x0) (CB 8 ?x1) (CB 8 ?x2) ?x3) =>
    eapply evt_cut; [eapply (imp_walk1 usp sp' f lo d n gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3x s4x s6x s7x s8x s9x s10x s11x t3 t4 t5 t6 j0 j8 j120 x0 x1 x2 x3 jsh Fr fc m
                               F0 FLO SLO' SH0 SEP' GLO' LSP LUSP SPH DR ltac:(lia) L0 FH FS MIx)|] end.
  cbv beta. intros ms1 (m1 & j8a & j48 & j128 & j152 & j192 & jsh20 & -> & MU1 & WM1 & MI1 & L1 & HD1 & SH1). apply evt_done.
  assert (W1 : forall a, ~ outside (imp_W1 sp' f) a -> (sp' <= a < sp' + 192) \/ (f <= a < f + 24) \/ (shad f <= a < shad f + 20)) by (intros a Ha; unfold imp_W1 in Ha; cbn [outside] in Ha; lia).
  assert (AG01 : forall P : Z -> Prop, (forall x, P x -> ~ (sp' <= x < sp' + 192) /\ ~ (f <= x < f + 24) /\ ~ (shad f <= x < shad f + 20)) -> agree_on P m m1).
  { intros P HP a Ha. apply MU1. destruct (outside_dec' (imp_W1 sp' f) (bv_unsigned a)) as [Ho|Ho]; [exact Ho|]. pose proof (W1 _ Ho). pose proof (HP _ Ha). exfalso. lia. }
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 sp' ARTx ltac:(rewrite SPx; lia)); [| exact WM1]. intros a Ha. apply MU1.
    destruct (outside_dec' (imp_W1 sp' f) (bv_unsigned a)) as [Ho|Ho]; [exact Ho|]. exfalso. apply Ha. destruct (W1 _ Ho) as [H|[H|H]]; [left; ul| |].
    - right; right; right; left. exists f, 5%nat. change (fs_size 5) with 2048. split; [exact INF| lia].
    - right; right; right; right. exists f, 5%nat. split; [exact INF| change (fs_size 5) with 2048; rewrite SHF; lia]. }
  assert (ST1 : stk bsegs m1 lo sp') by (apply (stk_agree_nw bsegs m m1 _ _ STx); apply AG01; intros x Hx; cbv beta in Hx; rewrite SHF0; clear - Hx FLO LO64 SLO SHF0; rewrite SHF0 in SLO; lia).
  apply rw_cells_app in SH1. destruct SH1 as [SH20 SHR]. rewrite cells_size_map_C1' in SHR. change (Z.of_nat (length imp_sh20)) with 20 in SHR.

  eapply (aevt_setshadow RT RC PMc FDO MST Σ K 0xf8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc m1 (shad f + 20) 68 lo);
    [cbn; tauto| reflexivity| reflexivity| lia| | | exact ART1| exact MI1| exact (COK m1 ST1)|].
  { intros i Hi. exists f, 5%nat. rewrite FRSx. split; [left; reflexivity|]. change (fs_size 5) with 2048. rewrite SHF. lia. }
  { pose proof SHR as [_ W]. cbn [cells_size csize Nat.add] in W. change (Z.of_nat 136) with 136 in W. exact (wr_at_sub _ (shad f + 20) 136 (shad f + 20) 68 W ltac:(lia) ltac:(lia) ltac:(lia)). }
  intros v0 w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 w3 w4 w5 w6 F2 m2 (ART2 & MI2 & WM2 & ST2) PR2 BY2. rewrite EU in ST2, PR2.
  rewrite (ret_pc_even IMP_SSF8RET_A) by (unfold IMP_SSF8RET_A; lia). change (Z.to_nat 68) with 68%nat in BY2.
  assert (AG12 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x /\ ~ (shad f + 20 <= x < shad f + 88)) -> agree_on P m1 m2).
  { intros P HP a Ha. destruct (HP _ Ha) as (C0 & C1). apply PR2; [exact C0| lia]. }

  assert (ZST : forall x, sp' + 192 <= x < usp -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x /\ ~ (shad f + 20 <= x < shad f + 88)).
  { intros x Hx. split; [left; ul|]. rewrite SHF0. clear - Hx SLO LO64 SHF0. rewrite SHF0 in SLO. lia. }
  assert (ZFR : forall x, f <= x < f + 2040 -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x /\ ~ (shad f + 20 <= x < shad f + 88)).
  { intros x Hx. split; [right; right; right; left; exists f, 5%nat; change (fs_size 5) with 2048; split; [exact INF| lia]|].
    rewrite SHF0. clear - Hx SEP F0 SHF0. rewrite SHF0 in SEP. lia. }
  assert (ZSH : forall x, (shad f <= x < shad f + 20 \/ shad f + 88 <= x < shad f + 156) -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x /\ ~ (shad f + 20 <= x < shad f + 88)).
  { intros x Hx. split; [right; right; right; right; exists f, 5%nat; split; [exact INF| change (fs_size 5) with 2048; rewrite SHF; lia]| lia]. }
  assert (ZCS : forall x, client_static x -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x /\ ~ (shad f + 20 <= x < shad f + 88)).
  { intros x Hx. split; [right; left; exact Hx|]. pose proof (client_static_range _ Hx) as R. clear - R SHB0. ul. }
  assert (ZLV : forall x, in_live (rt_live RT Σ) x -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x /\ ~ (shad f + 20 <= x < shad f + 88)).
  { intros x Hx. split; [right; right; left; exact Hx|]. destruct Hx as (p & k & Hin & R).
    pose proof (proj1 (af_fshadow_apart RT AF Σ m f 5%nat ARTx INF) p k Hin) as Y2. change (fs_size 5) with 2048 in Y2. rewrite SHF in Y2. lia. }
  assert (CSL : forall x, (client_static x \/ in_live (rt_live RT Σ) x) -> ~ (sp' <= x < sp' + 192) /\ ~ (f <= x < f + 24) /\ ~ (shad f <= x < shad f + 156)).
  { intros x [Hx|Hx].
    - pose proof (client_static_range _ Hx) as R. clear - R FSEG SHB0 GLO LOR SPR. ul.
    - destruct Hx as (p & k & Hin & R). pose proof (proj2 (proj2 (proj2 (af_frames_range RT AF Σ m f 5%nat ARTx INF))) p k Hin) as Y1. change (fs_size 5) with 2048 in Y1.
      pose proof (proj1 (af_fshadow_apart RT AF Σ m f 5%nat ARTx INF) p k Hin) as Y2. change (fs_size 5) with 2048 in Y2. rewrite SHF in Y2.
      pose proof (af_live_range RT AF Σ m p k ARTx Hin) as (_ & Y3 & _). rewrite SPx in Y3. clear - R Y1 Y2 Y3 LOW LOR SPR. ul. }
  assert (AG02s : forall P : Z -> Prop, (forall x, P x -> client_static x \/ in_live (rt_live RT Σ) x) -> agree_on P m m2).
  { intros P HP. eapply agree_trans; [apply AG01; intros x Hx; pose proof (CSL x (HP _ Hx)); lia|]. apply AG12. intros x Hx. destruct (HP _ Hx) as [H|H]; [exact (ZCS x H)| exact (ZLV x H)]. }

  assert (L12 : rw_cells bsegs m2 sp' (imp_locals1 j0 j8a f j48 (Z_to_bv 64 d) j128 j152 j192)).
  { apply (rw_cells_agree_nw bsegs m1 m2 _ _ L1). apply AG12. intros x Hx. unfold imp_locals1 in Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; ul|].
    rewrite SHF0. clear - Hx SLO LO64 SHF0. rewrite SHF0 in SLO. lia. }
  pose proof SHR as SHR'. apply (rw_cells_split_CB bsegs _ _ [] 136 _ [] [68; 68]%nat) in SHR'; [| reflexivity]. cbn [mk_CB_cells app] in SHR'.
  lazymatch type of SHR' with rw_cells _ _ _ (?c0 :: ?c1 :: nil) => change (c0 :: c1 :: nil) with ([c0] ++ [c1]) in SHR' end.
  apply rw_cells_app in SHR'. destruct SHR' as [_ SH88]. cbn [cells_size csize Nat.add] in SH88. replace (shad f + 20 + Z.of_nat 68) with (shad f + 88) in SH88 by lia.
  lazymatch type of SH88 with rw_cells _ _ _ [CB 68 ?t] => set (jsh88 := t) in SH88; clearbody jsh88 end.
  assert (SH88_2 : rw_cells bsegs m2 (shad f + 88) [CB 68 jsh88]).
  { apply (rw_cells_agree_nw bsegs m1 m2 _ _ SH88). apply AG12. intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply ZSH. lia. }
  assert (GV : 0 <= gofv v <= 1) by (destruct v; cbn; lia).
  assert (GB : rw_cells bsegs m IMP_GUARD_A [C1 (Z_to_bv 8 (gofv v)); C1 (Z_to_bv 8 (gofv v))]).
  { destruct LBv as (STv & _). destruct v as [B|]; cbn [gofv].
    - destruct STv as (_ & _ & _ & _ & _ & _ & GD & _). exact GD.
    - destruct STv as (_ & _ & _ & _ & _ & _ & GD). exact GD. }
  assert (GB2 : ro_cells bsegs m2 IMP_GUARD_A [C1 (Z_to_bv 8 (gofv v))]).
  { lazymatch type of GB with rw_cells _ _ _ (?c :: ?r) => change (c :: r) with ([c] ++ r) in GB end. apply rw_cells_app in GB. destruct GB as [GB _].
    refine (proj1 (rw_cells_agree_nw bsegs m m2 _ _ GB _)). apply AG02s. intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. apply client_static_intro. unfold IMP_GUARD_A in Hx. lia. }

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (imp_walk2 usp sp' f lo d n (gofv v) _ gp w0 w1 w2 v0 e1 e2 e3 e4 e5 e6 e7 s8x s9x s10x s11x w3 w4 w5 w6 j0 j8a j48 j128 j152 j192 jsh88 F2 fc m2
                             F0 FLO SLO' SH0 SEP' GLO' LSP LUSP SPH DR ltac:(lia) GV L12 SH88_2 GB2 MI2)|].
  cbv beta. intros ms3 (m3 & j8b & -> & MU3 & WM3 & MI3 & L23 & SH88_3). apply evt_done.
  assert (W2 : forall a, ~ outside (imp_W2 sp' f) a -> (sp' <= a < sp' + 192) \/ (shad f + 88 <= a < shad f + 156)) by (intros a Ha; unfold imp_W2 in Ha; cbn [outside] in Ha; lia).
  assert (AG23 : forall P : Z -> Prop, (forall x, P x -> ~ (sp' <= x < sp' + 192) /\ ~ (shad f + 88 <= x < shad f + 156)) -> agree_on P m2 m3).
  { intros P HP a Ha. apply MU3. destruct (outside_dec' (imp_W2 sp' f) (bv_unsigned a)) as [Ho|Ho]; [exact Ho|]. pose proof (W2 _ Ho). pose proof (HP _ Ha). exfalso. lia. }
  assert (ART3 : ART RT Σ m3).
  { apply (art_client_write RT AF Σ m2 m3 sp' ART2 ltac:(rewrite SPx; lia)); [| exact WM3]. intros a Ha. apply MU3.
    destruct (outside_dec' (imp_W2 sp' f) (bv_unsigned a)) as [Ho|Ho]; [exact Ho|]. exfalso. apply Ha. destruct (W2 _ Ho) as [H|H]; [left; ul|].
    right; right; right; right. exists f, 5%nat. split; [exact INF| change (fs_size 5) with 2048; rewrite SHF; lia]. }
  assert (ST3 : stk bsegs m3 lo sp') by (apply (stk_agree_nw bsegs m2 m3 _ _ ST2); apply AG23; intros x Hx; cbv beta in Hx; rewrite SHF0; clear - Hx FLO LO64 SLO SHF0; rewrite SHF0 in SLO; lia).

  assert (AG03s : forall P : Z -> Prop, (forall x, P x -> client_static x \/ in_live (rt_live RT Σ) x) -> agree_on P m m3).
  { intros P HP. eapply agree_trans; [apply AG02s; exact HP|]. apply AG23. intros x Hx. pose proof (CSL x (HP _ Hx)). lia. }

  assert (AGST : forall P : Z -> Prop, (forall x, P x -> sp' + 192 <= x < usp) -> agree_on P m m3).
  { intros P HP. eapply agree_trans; [apply AG01; intros x Hx; pose proof (HP _ Hx); rewrite SHF0; clear - H FLO LO64 SLO SHF0; rewrite SHF0 in SLO; lia|].
    eapply agree_trans; [apply AG12; intros x Hx; apply ZST; exact (HP _ Hx)|]. apply AG23. intros x Hx. pose proof (HP _ Hx). rewrite SHF0. clear - H FLO LO64 SLO SHF0. rewrite SHF0 in SLO. lia. }
  assert (AGF13 : forall P : Z -> Prop, (forall x, P x -> f <= x < f + 2040) -> agree_on P m1 m3).
  { intros P HP. eapply agree_trans; [apply AG12; intros x Hx; apply ZFR; exact (HP _ Hx)|]. apply AG23. intros x Hx. pose proof (HP _ Hx). rewrite SHF0. clear - H FLO LO64 SEP F0 SHF0. rewrite SHF0 in SEP. lia. }
  assert (AGF03 : forall P : Z -> Prop, (forall x, P x -> f + 32 <= x < f + 2040) -> agree_on P m m3).
  { intros P HP. eapply agree_trans; [apply AG01; intros x Hx; pose proof (HP _ Hx); rewrite SHF0; clear - H FLO LO64 SEP F0 SHF0; rewrite SHF0 in SEP; lia|]. apply AGF13. intros x Hx. pose proof (HP _ Hx). lia. }
  assert (STp3 : stk bsegs m3 (sp' + 216) (usp - 104)) by (apply (stk_agree_nw bsegs m m3 _ _ STp); apply AGST; intros x Hx; cbv beta in Hx; lia).
  assert (SV3 : rw_cells bsegs m3 (usp - 104) (imp_savedA cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11)) by (apply (rw_cells_agree_nw bsegs m m3 _ _ SV); apply AGST; intros x Hx; rewrite imp_savedA_size in Hx; lia).
  assert (HD3 := rw_cells_agree_nw bsegs m1 m3 _ _ HD1 ltac:(apply AGF13; intros x Hx; unfold fz_hdr in Hx; cbn [cells_size csize Nat.add] in Hx; lia)).
  assert (SH20_3 : rw_cells bsegs m3 (shad f) (map C1 imp_sh20)).
  { apply (rw_cells_agree_nw bsegs m1 m3 _ _ SH20). eapply agree_trans; [apply AG12| apply AG23]; intros x Hx; rewrite cells_size_map_C1' in Hx; change (Z.of_nat (length imp_sh20)) with 20 in Hx;
      [apply ZSH; lia|]. rewrite SHF0 in Hx |- *. clear - Hx FLO LO64 SLO SEP F0 SHF0. rewrite SHF0 in SLO, SEP. lia. }
  assert (SHX3 : rw_cells bsegs m3 (shad f + 20) [CB 68 (repeat (Z_to_bv 8 248) 68)]).
  { apply (rw_cells_agree_nw bsegs m2 m3 _ _).
    - apply (rw_cells_CB_of_bytes m2 _ _ BY2). rewrite repeat_length. pose proof SHR as [_ W]. cbn [cells_size csize Nat.add] in W. change (Z.of_nat 136) with 136 in W.
      exact (wr_at_transport bsegs m1 m2 _ _ (wr_at_sub _ (shad f + 20) 136 (shad f + 20) 68 W ltac:(lia) ltac:(lia) ltac:(lia)) WM2).
    - apply AG23. intros x Hx. cbn [cells_size csize Nat.add] in Hx. rewrite SHF0 in Hx |- *. clear - Hx FLO LO64 SLO SEP F0 SHF0. rewrite SHF0 in SLO, SEP. lia. }
  assert (SF3 : setupF m3 f).
  { apply (setupF_agree m m3 f); [| apply AGF03; intros x Hx; lia].
    split; [exists jsb; exact FB|]. split; [| split; [exists jos; exact FO| exists jtmp; exact FT]].
    lazymatch type of FI with rw_cells _ _ _ [CB 136 ?a; CB 136 ?b; CB 136 ?c; CB 136 ?e] => exists a, b, c, e; exact FI end. }
  assert (LB3 : imp_libA v m3).
  { apply (imp_libA_agree v m m3 LBv). apply AG03s. intros x Hx. destruct (imp_lib_rng_cases v x Hx) as [[CS _]|(B & EB & R)]; [left; exact CS|].
    right. exists B, 8. split; [rewrite LVx; exact (VIN B EB)| lia]. }
  assert (AX3 : aexvA v m3).
  { destruct v as [B|]; cbn [aexvA] in AXv |- *.
    - apply (aex6A_agree m m3 AXv). apply AG03s. intros x (l & h & Hin & R). left. unfold IMP_AEX_W in Hin. revert R. aex_lits. cbn [In] in Hin. intros R.
      destruct Hin as [E|[E|[]]]; injection E as <- <-; apply client_static_intro; lia.
    - destruct AXv as [(p1 & p2 & f4 & f5 & T4) (b4 & b5 & A4)]. split; [exists p1, p2, f4, f5| exists b4, b5];
        [apply (rw_cells_agree_nw bsegs m m3 _ _ T4)| apply (rw_cells_agree_nw bsegs m m3 _ _ A4)]; apply AG03s; intros x Hx;
        [unfold aex_tbl in Hx| unfold aex_args in Hx]; cbn [cells_size csize Nat.add] in Hx; left; apply client_static_intro; aex_lits; lia. }
  assert (BS3 : bytes_at bsegs m3 d bs).
  { apply (bytes_at_agree bsegs m m3 _ _ BS). apply AG03s. intros x Hx. cbv beta in Hx. right.
    destruct INLV as [(p & k & Hin & P1 & P2)| (E0 & DL)]; [| rewrite E0 in Hx; cbn [length] in Hx; lia]. exists p, k. split; [exact (LV0x _ Hin)| subst n; lia]. }
  assert (PRES3 : forall a : word, aclient (rt_live RT Σ0) [] usp (bv_unsigned a) -> outside IMP_XFP_A (bv_unsigned a) -> m3 a = m0 a).
  { intros a Ha Ho. rewrite <- (PRES a Ha Ho). pose proof (CSEP _ Ha) as (C1 & C2 & C3).
    transitivity (m2 a); [| transitivity (m1 a)].
    - apply (AG23 (fun x => x = bv_unsigned a)); [| reflexivity]. intros x ->. clear - C1 C2 C3 LO64 LUSP. lia.
    - apply (AG12 (fun x => x = bv_unsigned a)); [| reflexivity]. intros x ->. split; [apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact LV0x| intros e []| lia]| clear - C2; lia].
    - apply (AG01 (fun x => x = bv_unsigned a)); [| reflexivity]. intros x ->. clear - C1 C2 C3 LO64 LUSP. lia. }
  clear AG01 AG12 AG23 AG02s AGST AGF13 AGF03 MU1 MU3 PR2 WM1 WM2 WM3 L0 L1 L12 HD1 SH20 SHR SH88 SH88_2 FH FB FI FO FT FS GB GB2 BS PRES ART1 ART2 ARTx MI1 MI2 MIx ST1 ST2 STx BY2 W1 W2.
  destruct v as [B|]; cbn [gofv aexvA] in AX3 |- *.
  -
    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut; [apply (imp_walk2c usp sp' f n _ gp w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 s8x s9x s10x s11x w3 w4 w5 w6 F2 fc m3)|].
    cbv beta. intros ms4 <-. apply evt_done.
    assert (BIN : In (B, 8) (rt_live RT Σ)) by (rewrite LVx; exact (VIN B eq_refl)).
    destruct LB3 as (ST3v & LBb & LXb & TPb & LKb).
    apply (imp_setup2A RT AF RC PDONE PDT PDFP PID OKARM PMc FDO MST Σ0 Σ K (Some B) B usp sp' f lo d bs _ gp w0 w1 w2 _ e1 e2 e3 e4 e5 e6 e7 _ s8x s9x s10x s11x w3 w4 w5 w6
             cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 F2 fc m0 m3 cb G ART3 MI3 ST3 FRSx);
      [cbn [xnewA app]; exact LVx| exact SPx| | exact CB0| exact BIN| intros B' EB; injection EB as <-; reflexivity| exact LVP| lia| exact D0| exact NB| exact BS3| exact INLV| | exact SF3| exact NL0| exact IOS0| exact PRES3| exact FRM| exact KFIN].
    + unfold imp_setup_costA, GRSI_COST_A in CRx. pose proof (mcost_nonneg 8 ltac:(lia)). clear - CRx H. subst n. lia.
    + split; [exists j0, j8b, j48, j128, j152, j192; exact L23|]. split; [exact STp3|]. split; [exact SV3|]. split; [eexists; exact HD3|].
      split; [split; [exact SH20_3| split; [eexists; exact SHX3| exact SH88_3]]|].
      split; [| exact AX3]. split; [right; exact (proj1 ST3v)|]. split; [exact (proj2 ST3v)|]. exact (conj LBb (conj LXb (conj TPb LKb))).
  -
    apply (imp_firstA Σ0 Σ K usp sp' f lo d bs _ gp w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 s8x s9x s10x s11x w3 w4 w5 w6 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11
             F2 fc m0 m3 cb j0 j8b j48 j128 j152 j192 _ _ G ART3 MI3 ST3 FRSx LVx SPx CRx CB0 LVP LVB D0 NB BS3 INLV L23 STp3 SV3 HD3 SH20_3 SHX3 SH88_3 SF3 LB3 AX3 NL0 IOS0 PRES3 FRM KFIN).
Qed.

End WithPM.
End Setup1.
