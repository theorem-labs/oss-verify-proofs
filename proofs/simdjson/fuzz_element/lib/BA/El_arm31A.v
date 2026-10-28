(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun Stdio SjModel AtpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit Atp_h_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_iface3 RT_iface5. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_hkit2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_num_akit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_h_alloc Sj_stage2_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_fzwA Atp_setcapA Atp_activewA Atp_activeA Atp_defsA Atp_kitA Atp_h_defsA Atp_pidiA Atp_pdtorA Pj_rtkA Pj_lftoi1A Pj_defsA Pj_os_defsA El_defsA El_lf1A El_lf2A El_lf2bA El_phasesA El_frontA El_parsekA El_tailA El_osdtorA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac ls := lstep; try sb_fix.

Lemma a31_walk1 : forall (usp sp' f P L idx : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (t : list byte) F fc (m : mem),
  0 < f -> f + 1024 < 2^63 -> 0 <= shad f -> shad f + 128 < 2^63 -> SEGTOP_A <= sp' -> sp' + 256 < 2^63 ->
  (sp' + 256 <= shad f \/ shad f + 128 <= sp') ->
  rw_cells asegs m (shad f) (el_shadowA 0 0 0 (-8) t) ->
  rw_cells asegs m (sp' + 24) [C8 (wz P); C8 (wz L); C8 (wz idx); C8 (wz (f + 240)); C8 (wz 31)] -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = tl_st usp sp' f PJ_OS_CTOR_A (Z_to_bv 64 0xb1d30) gp t0 t1 t2 (Z_to_bv 64 (f + 240)) a1 a2 a3 a4 a5 a6 a7 s6 (Z_to_bv 64 (f + 240)) s8 s9 s10 s11 t3 t4 t5 t6 F fc m1
      /\ munch [(shad f + 30, shad f + 66)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (shad f) (el_shadowA 0 0 0 0 t))
    (tl_st usp sp' f 0xb1c94 ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH SH0 SHH GLO SPH APART FS C16 MI.
  unfold tl_st, el_shadowA, el_shbytesA, PJ_OS_CTOR_A, SEGTOP_A, shad, SHB in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(f / 8 + 2147450880 + 30, f / 8 + 2147450880 + 66)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  do 36 ls.
  step. zstep. zstep.
  apply evt_done. eexists. split; [atp_st_eq_goal|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|]. eassumption.
Qed.

Lemma a31_walk2 : forall (usp sp' f D : Z) (gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < f -> f + 1024 < 2^63 ->
  rw_cells asegs m (f + 208) [C8 (wz D); C8 (wz 1)] -> mem_inv asegs m ->
  evt asegs (fun ms => ms = tl_st usp sp' f EL_DUMP_A (Z_to_bv 64 EL_DUMPRET_A) gp t0 t1 t2 (Z_to_bv 64 D) (Z_to_bv 64 (f + 240 + 128)) a2 a3 a4 a5 a6 a7
                                  (Z_to_bv 64 (f + 208)) (Z_to_bv 64 (f + 240)) s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
    (tl_st usp sp' f 0xb1d30 (Z_to_bv 64 0xb1d30) gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (f + 208)) (Z_to_bv 64 (f + 240)) s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH CE MI. unfold tl_st, EL_DUMP_A, EL_DUMPRET_A in *.
  assert (EF : bv_unsigned (Z_to_bv 64 (f + 208)) = f + 208) by (apply unsigned_lit; lia).
  step. zstep. zstep. apply evt_done. atp_st_eq_goal.
Qed.

Lemma a31_walk3 : forall (usp sp' f : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (t : list byte) F fc (m : mem),
  0 < f -> f + 1024 < 2^63 -> 0 <= shad f -> shad f + 128 < 2^63 ->
  rw_cells asegs m (shad f) (el_shadowA 0 0 0 0 t) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = tl_st usp sp' f EL_EXIT_A ra gp t0 t1 t2 (Z_to_bv 64 (-8)) a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1
      /\ munch [(shad f + 30, shad f + 66)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (shad f) (el_shadowA 0 0 0 (-8) t))
    (tl_st usp sp' f 0xb1d44 ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH SH0 SHH FS MI.
  unfold tl_st, el_shadowA, el_shbytesA, EL_EXIT_A, shad, SHB in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(f / 8 + 2147450880 + 30, f / 8 + 2147450880 + 66)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  zstep. do 36 ls. zstep.
  apply evt_done. eexists. split; [atp_st_eq_goal|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|]. eassumption.
Qed.

Lemma el_shadow_os_zero : forall m f t, f mod 8 = 0 -> rw_cells asegs m (shad f) (el_shadowA 0 0 0 0 t) -> bytes_at asegs m (shad (f + 240)) (repeat z8 36).
Proof.
  intros m f t F8 FS.
  pose proof (rw_cells_bytes_at asegs m (shad f) _ FS) as X. unfold el_shadowA, el_shbytesA in X. cbn [cells_bytes cbytes map app repeat] in X.
  lazymatch type of X with bytes_at _ _ _ ?l =>
    pose proof (bytes_at_skipn m (shad f) l 30 X ltac:(cbn; lia)) as Y end.
  cbn [skipn] in Y. apply (bytes_at_firstn m _ _ 36) in Y. cbn [firstn] in Y.
  replace (shad (f + 240)) with (shad f + Z.of_nat 30) by (unfold shad; Z.div_mod_to_equations; lia). exact Y.
Qed.

Section Arm31.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable PMc : Model -> Prop.
Hypothesis CTOR : ctor_cpsA RT PMc OSFRESHA.
Hypothesis DUMP : dump_cpsA RT PMc.
Hypothesis OSDTOR : osdtor_cps2A RT PMc.

Local Ltac ul := unfold FUZZ_STACK, PID_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB, EL_DUMP_STACK_A, PJ_OS_CTOR_STACK_A, PJ_LOC_STACK_A, EL_OSDTOR_STACK_A in *; lia.

Theorem arm31_okA : forall W, arm_cpsA RT PMc W 31.
Proof using AF CTOR DUMP OSDTOR.
  intros W Σ K X E sel idx jr jos t ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 t3 t4 t5 t6 F fc m
    FDO MST LK OKE LE WFS SEL IDX AL FRS LPA LVB CRB ARTg MIg STg NEED AM FRM XD AUX SPB POST.
  pose proof LK as [(SPR & SPA') (SPT & SPA) (LLO & LOR) (FPOS & F64 & FSEG & FLO) (FSELF & SHB0 & SHT)].
  destruct X as [usp sp' f lo]. cbn [lf_usp lf_S1 lf_F lf_lo] in *.
  pose proof LE as (EDOC & EFD & EKD & ELO & EHI). cbn [lf_usp lf_S1 lf_F lf_lo] in EDOC, EFD, EKD, ELO, EHI.
  pose proof AM as (C16 & C100 & C128 & CE & CO & CS & AI & LIB & NL & IOS). cbn [lf_usp lf_S1 lf_F lf_lo] in C16, C100, C128, CE, CO, CS.
  pose proof (af_sp0_range RT AF Σ m ARTg) as SP0R. pose proof AL as (ALT & ALS & ALP & ALF & WLO).
  change (el_arm_pcA 31) with 0xb1c94. unfold lf_st. cbn [lf_usp lf_S1 lf_F lf_lo].
  assert (INF : In (f, 4%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  assert (NEED' : lo + EL_DUMP_STACK_A <= sp') by (clear - NEED; unfold arm_needA in NEED; cbn [Z.eqb Pos.eqb orb] in NEED; exact NEED).
  assert (CRB' : EL_DUMP_C0 + EL_DUMP_CW * ae_n E + EL_DUMP_CSB * ae_sn E <= rt_credit RT Σ) by (clear - CRB; unfold arm_costA in CRB; cbn [Z.eqb Pos.eqb orb] in CRB; exact CRB).
  assert (STAT : forall x, client_static x -> x < sp') by (intros x Hx; pose proof (client_static_range _ Hx); clear - H LLO LOR SPR; ul).
  pose proof (af_frames_range RT AF Σ m f 4%nat ARTg INF) as (_ & _ & _ & FLV). change (fs_size 4) with 1024 in FLV.
  pose proof (af_fshadow_apart RT AF Σ m f 4%nat ARTg INF) as (FSL & _). change (fs_size 4) with 1024 in FSL.
  assert (SHF0 : shad f = f / 8 + SHB) by reflexivity.
  pose proof OKE as OK'. destruct OK' as [_ _ _ _ (T16 & NT8 & TN & TS & TL) (S16 & NS8 & SN & SS & SL) PTRR PTR0 (D8 & DF & DL & DS & DT) LOW' [HL HT]].

  assert (OWA : forall a, outside (arm_WA (mkLF usp sp' f lo)) a ->
            ~ (shad f + 30 <= a < shad f + 66) /\ outside [(PJ_LOC_LO_A, PJ_LOC_HI_A); (f + 240, f + 240 + 288)] a
            /\ outside ([(f + 240, f + 240 + 288); (EL_TPLOC_A, EL_TPLOC_A + 8)] ++ EL_LIB_FP) a /\ outside [(f + 240, f + 240 + 288)] a).
  { intros a Ho. unfold arm_WA, EL_LIB_FP, LIB_FP, EL_UNW_A, EL_EHG_A, EL_TPLOC_A, TPV_A, PJ_LOC_LO_A, PJ_LOC_HI_A in *. cbn [lf_usp lf_S1 lf_F lf_lo outside app] in Ho |- *.
    clear - Ho. repeat split; try exact I; lia. }
  assert (OWL : forall a q k, In (q, k) (rt_live RT Σ) -> q <= a < q + k -> outside (arm_WA (mkLF usp sp' f lo)) a).
  { intros a q k Hin Ha. pose proof (af_live_range RT AF Σ m q k ARTg Hin) as (Y0 & Y1 & Y2). pose proof (FLV q k Hin) as Y3. pose proof (FSL q k Hin) as Y4.
    rewrite SHF0 in Y4. unfold arm_WA, EL_LIB_FP, LIB_FP, EL_UNW_A, EL_EHG_A, EL_TPLOC_A, TPV_A. cbn [lf_usp lf_S1 lf_F lf_lo outside app].
    unfold shad, SHB, SEGTOP_A, FUZZ_STACK, STACK_WIN, USTACK_TOP in *.
    replace ((f + 1024) / 8 + 2147450880) with (f / 8 + 2147450880 + 128) in Y4 by (Z.div_mod_to_equations; lia).
    clear - Ha Y0 Y1 Y2 Y3 Y4 SPR LOR LLO WLO ELO. repeat split; try exact I; lia. }
  assert (OWD : forall a, (f <= a < f + 240 \/ shad f <= a < shad f + 30 \/ sp' <= a < sp' + 96 \/ sp' + 120 <= a < usp) -> outside (arm_WA (mkLF usp sp' f lo)) a).
  { intros a Ha. unfold arm_WA, EL_LIB_FP, LIB_FP, EL_UNW_A, EL_EHG_A, EL_TPLOC_A, TPV_A. cbn [lf_usp lf_S1 lf_F lf_lo outside app].
    unfold shad, SHB, SEGTOP_A, FUZZ_STACK, STACK_WIN, USTACK_TOP in *. clear - Ha FSEG FLO FSELF SHB0 SHT SPR LOR LLO.
    repeat split; try exact I; lia. }
  assert (AIN : forall x, ainv_rng E x -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x /\ outside (arm_WA (mkLF usp sp' f lo)) x).
  { intros x Hx. split; [exact (ainv_rng_aclient RT Σ E sp' x AL OKE Hx)|].
    unfold ainv_rng in Hx. rewrite EDOC in Hx. destruct Hx as [Hx|[Hx|[Hx|[Hx|Hx]]]].
    - apply (OWL x _ _ ALT). lia.
    - apply (OWL x _ _ ALS). lia.
    - destruct ALP as [E0|INPB]; [rewrite E0 in Hx; unfold zlength in Hx; cbn [length] in Hx; lia|].
      assert (NE : ae_p1 E <> []) by (intros E0; rewrite E0 in Hx; unfold zlength in Hx; cbn [length] in Hx; lia).
      pose proof (PTRR NE) as (PB0 & PB1 & PB2 & PB3). apply (OWL x _ _ INPB). lia.
    - apply OWD. lia.
    - apply OWD. right; left. unfold shad, SHB in *. clear - Hx F64. Z.div_mod_to_equations. lia. }
  assert (INS : forall x, sp' <= x < usp -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x) by (intros x Hx; left; clear - Hx SPT; ul).
  assert (INFR : forall x, f <= x < f + 1016 -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x).
  { intros x Hx. right; right; right; left. exists f, 4%nat. split; [exact INF| change (fs_size 4) with 1024; lia]. }
  assert (INSH : forall x, shad f <= x < shad f + 128 -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x).
  { intros x Hx. right; right; right; right. exists f, 4%nat. split; [exact INF| change (fs_size 4) with 1024; unfold shad in *; Z.div_mod_to_equations; lia]. }
  assert (INST : forall x, client_static x -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x) by (intros x Hx; right; left; exact Hx).

  set (REL := fun mk : mem => forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) sp' (bv_unsigned a) -> outside (arm_WA (mkLF usp sp' f lo)) (bv_unsigned a) -> mk a = m a).
  assert (RELAG : forall mk, REL mk -> forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x /\ outside (arm_WA (mkLF usp sp' f lo)) x) -> agree_on P m mk).
  { intros mk R P HP a Ha. destruct (HP _ Ha) as [H1 H2]. exact (R a H1 H2). }

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (a31_walk1 usp sp' f (ae_PTR E) (zlength (ae_p1 E)) idx ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz (f + 208)) (wz 0) (wz f) s9 s10 (wz (f + 120)) t3 t4 t5 t6 t F fc m);
                   [exact FPOS| clear - FLO LOR SPT; ul| clear - SHB0; unfold SHB in *; lia| clear - SHT LOR SPT; ul| clear - LLO LOR SPR; ul| clear - SPR SPT; ul
                   | right; clear - SHT LOR SPR; ul| unfold el_shadow_armA in CS; exact CS| exact C16| exact MIg]|].
  cbv beta. intros ms1 (m1 & -> & MU1 & WM1 & MI1 & FS1). apply evt_done. unfold tl_st.
  assert (REL1 : REL m1) by (intros a Ha Ho; apply MU1; cbn [outside]; split; [exact (proj1 (OWA _ Ho))| exact I]).
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 sp' ARTg ltac:(clear - WLO ELO LOR SPR; ul)); [| exact WM1]. intros a Ha. apply MU1. cbn [outside]. split; [| exact I].
    intros Hin. apply Ha. apply INSH. clear - Hin. lia. }
  assert (ST1 : stk asegs m1 lo sp') by (apply (stk_agree asegs m m1 _ _ STg); [| exact WM1]; intros a Ha; apply MU1; cbn [outside]; cbv beta in Ha; split; [clear - Ha SHT; lia| exact I]).
  pose proof (RELAG m1 REL1) as AG1.
  assert (HULL1 : os_hullA m1 (f + 240)).
  { split; [exists jos; eapply rw_cells_agree_nw; [exact CO|]; apply (agree_of_munch _ _ _ _ MU1); intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside]; split; [clear - Hx FSELF; lia| exact I]|].
    exact (el_shadow_os_zero m1 f t ltac:(clear - F64; Z.div_mod_to_equations; lia) FS1). }

  assert (LIBX : forall ma mb, el_libA ma -> LOCBA mb ->
            agree_on (fun a => sj_lib_rng a \/ PJ_LOCKW_A <= a < PJ_LOCKW_A + 4 \/ EL_EHG_A <= a < EL_EHG_A + 12 \/ EL_UNW_A <= a < EL_UNW_A + 8 \/ EL_TPLOC_A <= a < EL_TPLOC_A + 8) ma mb ->
            el_libA mb).
  { intros ma mb [(S & L & LW) (Eh & U & T)] LB AG. split; [split; [| split]| split; [| split]].
    - eapply sj_lib_agree; [exact S|]. intros a Ha. apply AG. left; exact Ha.
    - right. exact LB.
    - eapply lockwA_agree; [exact LW|]. intros a Ha. apply AG. right; left; exact Ha.
    - eapply rw_cells_agree_nw; [exact Eh|]. intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. right; right; left. lia.
    - destruct U as [uw U]. exists uw. eapply rw_cells_agree_nw; [exact U|]. intros a Ha. apply AG. rewrite uw_cellsA_size in Ha. right; right; right; left. lia.
    - eapply rw_cells_agree_nw; [exact T|]. intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. do 4 right. lia. }
  assert (LIBRNG : forall a, (sj_lib_rng a \/ PJ_LOCKW_A <= a < PJ_LOCKW_A + 4 \/ EL_EHG_A <= a < EL_EHG_A + 12 \/ EL_UNW_A <= a < EL_UNW_A + 8 \/ EL_TPLOC_A <= a < EL_TPLOC_A + 8) ->
            client_static a /\ outside [(PJ_LOC_LO_A, PJ_LOC_HI_A); (f + 240, f + 240 + 288)] a /\ ~ (shad f + 30 <= a < shad f + 66)).
  { intros a Ha. unfold sj_lib_rng, PJ_LOCKW_A, EL_EHG_A, EL_UNW_A, EL_TPLOC_A, TPV_A, PJ_LOC_LO_A, PJ_LOC_HI_A in *. cbn [outside].
    rewrite SHF0. unfold SHB. split; [apply client_static_intro; clear - Ha; lia|]. clear - Ha FSEG. unfold SEGTOP_A in FSEG. repeat split; try exact I; try lia.
    all: Z.div_mod_to_equations; lia. }
  assert (LIB1 : el_libA m1).
  { apply (el_libA_agree m m1 LIB). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. pose proof (el_lib_rng_static x Hx) as [_ R]. cbn [outside].
    rewrite SHF0. unfold SHB. clear - R FPOS. split; [| exact I]. Z.div_mod_to_equations; lia. }
  assert (NL1 : libc_nl m1).
  { apply (libc_nl_agree m m1 NL). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. unfold LIBC_NL in Hx. cbn [outside]. rewrite SHF0. unfold SHB. clear - Hx FPOS. split; [| exact I]. Z.div_mod_to_equations; lia. }
  assert (IOS1 : io_ssp m1).
  { destruct IOS as (g & G1 & G2). exists g. split; [exact (proj1 (af_got_lib RT AF Σ m1 ART1))|]. apply (ro_cells_agree asegs m m1 _ _ G2). apply (agree_of_munch _ _ _ _ MU1). intros x Hx.
    cbn [cells_size csize Nat.add] in Hx. cbn [outside]. rewrite SHF0. unfold SHB. clear - Hx FPOS. split; [| exact I]. Z.div_mod_to_equations; lia. }
  pose proof LIB1 as [(_ & LOC1 & LW1) _].

  eapply (CTOR Σ K (f + 240) sp' lo f 4%nat (wz 0xb1d30) gp t0 t1 t2 (wz usp) (wz sp') a1 a2 a3 a4 a5 a6 a7
            (wz f) (wz (shad f)) (wz (f + 32)) (wz (f + 96)) (wz (f + 208)) (wz (f + 240)) (wz f) s9 s10 (wz (f + 120)) t3 t4 t5 t6 F fc m1 FDO MST INF);
    [clear; lia| change (fs_size 4) with 1024; clear; lia| clear - F64; Z.div_mod_to_equations; lia| exact HULL1| exact LOC1| exact NL1| exact LW1| exact IOS1
    | exact ART1| exact MI1| exact ST1| rewrite <- ELO; exact WLO| clear - NEED'; ul| clear - SPR SPT; ul| clear - SPA'; Z.div_mod_to_equations; lia|].
  intros u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 m2 ART2 MI2 ST2 FRESH2 HULL2 LOCB2 PRES2.
  assert (REL2 : REL m2).
  { intros a Ha Ho. rewrite (PRES2 a Ha (proj1 (proj2 (OWA _ Ho)))). exact (REL1 a Ha Ho). }
  pose proof (RELAG m2 REL2) as AG2.
  assert (LIB2 : el_libA m2).
  { apply (LIBX m1 m2 LIB1 LOCB2). intros a Ha. destruct (LIBRNG _ Ha) as (CSa & Oa & _). exact (PRES2 a (INST _ CSa) Oa). }
  assert (CE2 : rw_cells asegs m2 (f + 208) [C8 (wz (ae_DOC E)); C8 (wz 1)]).
  { eapply rw_cells_agree_nw; [exact CE|]. apply AG2. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [apply INFR; lia| apply OWD; lia]. }
  assert (AI2 : AINV_A E m2) by (apply (AINV_A_agree E m m2 AI); apply AG2; exact AIN).
  assert (OWST : forall a, (LIBC_NL <= a < LIBC_NL + 1 \/ 0x6c7ea8 <= a < 0x6c7ea8 + 8) -> outside (arm_WA (mkLF usp sp' f lo)) a).
  { intros a Ha. unfold arm_WA, EL_LIB_FP, LIB_FP, EL_UNW_A, EL_EHG_A, EL_TPLOC_A, TPV_A, LIBC_NL in *. cbn [lf_usp lf_S1 lf_F lf_lo outside app].
    rewrite SHF0. unfold SHB, SEGTOP_A, FUZZ_STACK, STACK_WIN, USTACK_TOP in *. clear - Ha FSEG FLO LLO LOR SPR. repeat split; try exact I; try lia. all: Z.div_mod_to_equations; lia. }
  assert (NLX : forall mk, REL mk -> libc_nl mk).
  { intros mk R. apply (libc_nl_agree m mk NL). apply (RELAG mk R). intros x Hx. split; [exact (INST _ (libc_nl_static _ Hx))| apply OWST; left; exact Hx]. }
  assert (IOSX : forall (Σx : rts RT) mk, REL mk -> ART RT Σx mk -> io_ssp mk).
  { intros Σx mk R A'. destruct IOS as (g & G1 & G2). exists g. split; [exact (proj1 (af_got_lib RT AF Σx mk A'))|]. apply (ro_cells_agree asegs m mk _ _ G2). apply (RELAG mk R).
    intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [apply INST; apply client_static_intro; clear - Hx; lia| apply OWST; right; exact Hx]. }
  assert (SHZX : forall mk, REL mk -> bytes_at asegs mk (shad f) (cells_bytes (el_shadowA 0 0 0 0 t)) -> True) by (intros; exact I).

  assert (FS2 : rw_cells asegs m2 (shad f) (el_shadowA 0 0 0 0 t)).
  { eapply rw_cells_agree_nw; [exact FS1|]. intros a Ha. rewrite el_shadowA_size in Ha. apply PRES2; [apply INSH; lia|].
    cbn [outside]. unfold PJ_LOC_LO_A, PJ_LOC_HI_A. rewrite SHF0 in Ha. unfold SHB in *. clear - Ha FSELF FSEG SHF0. unfold SEGTOP_A in FSEG. rewrite SHF0 in FSELF.
    repeat split; try exact I; Z.div_mod_to_equations; lia. }

  rewrite (ret_pc_even 0xb1d30) by lia. apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (a31_walk2 usp sp' f (ae_DOC E) gp u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 (wz f) s9 s10 (wz (f + 120)) u3 u4 u5 u6 F2 fc m2
                             FPOS ltac:(clear - FLO LOR SPT; ul) CE2 MI2)|].
  cbv beta. intros ms2 ->. apply evt_done. unfold tl_st.

  eapply (DUMP Σ K {| lf_usp := usp; lf_S1 := sp'; lf_F := f; lf_lo := lo |} E (f + 240) t gp u0 u1 u2 (wz usp) (wz sp') b2 b3 b4 b5 b6 b7
            (wz f) (wz (shad f)) (wz (f + 32)) (wz (f + 96)) (wz (f + 208)) (wz (f + 240)) (wz f) s9 s10 (wz (f + 120)) u3 u4 u5 u6 F2 fc m2
            FDO MST LK OKE LE WFS eq_refl AL FRS); cbn [lf_usp lf_S1 lf_F lf_lo];
    [clear - CRB'; lia| exact ART2| exact MI2| exact ST2| clear - NEED'; lia| exact AI2| exact LIB2| exact LOCB2| exact (NLX m2 REL2)| exact (IOSX Σ m2 REL2 ART2)
    | exact FRESH2| exact (el_shadow_os_zero m2 f t ltac:(clear - F64; Z.div_mod_to_equations; lia) FS2)| exact FRM|].
  intros Σ3 m3 fc3 F3 v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 ART3 MI3 ST3 FRM3 LV3 FRS3 SP3 CR3 PRES3 AI3 LIB3 LOCB3 OSD3. cbn [lf_usp lf_S1 lf_F lf_lo] in ST3, PRES3.
  assert (REL3 : REL m3).
  { intros a Ha Ho. rewrite (PRES3 a Ha (proj1 (proj2 (proj2 (OWA _ Ho))))). exact (REL2 a Ha Ho). }
  assert (SHOUT : forall a, shad f <= a < shad f + 128 -> outside ([(f + 240, f + 240 + 288); (EL_TPLOC_A, EL_TPLOC_A + 8)] ++ EL_LIB_FP) a /\ outside [(f + 240, f + 240 + 288)] a).
  { intros a Ha. unfold EL_LIB_FP, LIB_FP, EL_UNW_A, EL_EHG_A, EL_TPLOC_A, TPV_A. cbn [outside app]. rewrite SHF0 in Ha. unfold SHB in Ha.
    clear - Ha FSELF FSEG SHF0. unfold SEGTOP_A in FSEG. rewrite SHF0 in FSELF. unfold SHB in FSELF. repeat split; try exact I; Z.div_mod_to_equations; lia. }
  assert (FS3 : rw_cells asegs m3 (shad f) (el_shadowA 0 0 0 0 t)).
  { eapply rw_cells_agree_nw; [exact FS2|]. intros a Ha. rewrite el_shadowA_size in Ha. apply PRES3; [apply INSH; lia| exact (proj1 (SHOUT _ Ha))]. }
  pose proof LIB3 as [(_ & LOC3 & LW3) _].

  apply (aevt_evt RT AF PMc MST). unfold EL_DUMPRET_A. zstep. zstep. apply evt_done.
  eapply (OSDTOR Σ3 K (f + 240) sp' lo f 4%nat (wz 0xb1d44) gp v0 v1 v2 (wz usp) (wz sp') c1 c2 c3 c4 c5 c6 c7
            (wz f) (wz (shad f)) (wz (f + 32)) (wz (f + 96)) (wz (f + 208)) (wz (f + 240)) (wz f) s9 s10 (wz (f + 120)) v3 v4 v5 v6 F3 fc3 m3 FDO MST);
    [rewrite FRS3; exact INF| clear; lia| change (fs_size 4) with 1024; clear; lia| clear - F64; Z.div_mod_to_equations; lia
    | unfold unwind_ok; rewrite !unsigned_lit by (clear - SPR SPT LLO LOR; ul); right; right; clear - SPR; lia| exact OSD3
    | exact (el_shadow_os_zero m3 f t ltac:(clear - F64; Z.div_mod_to_equations; lia) FS3)| exact LOCB3| exact (NLX m3 REL3)| exact LW3
    | exact ART3| exact MI3| exact ST3| rewrite SP3, <- ELO; exact WLO| clear - NEED'; ul| clear - SPR SPT; ul| clear - SPA'; Z.div_mod_to_equations; lia|].
  intros w0 w1 w2 d0 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 F4 m4 ART4 MI4 ST4 [jos4 HULL4] LOC4 PRES4. rewrite LV3, FRS3 in PRES4.
  assert (REL4 : REL m4).
  { intros a Ha Ho. rewrite (PRES4 a Ha (proj2 (proj2 (proj2 (OWA _ Ho))))). exact (REL3 a Ha Ho). }
  assert (FS4 : rw_cells asegs m4 (shad f) (el_shadowA 0 0 0 0 t)).
  { eapply rw_cells_agree_nw; [exact FS3|]. intros a Ha. rewrite el_shadowA_size in Ha. apply PRES4; [apply INSH; lia| exact (proj2 (SHOUT _ Ha))]. }

  rewrite (ret_pc_even 0xb1d44) by lia. apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (a31_walk3 usp sp' f (wz 0xb1d44) gp w0 w1 w2 d0 d1 d2 d3 d4 d5 d6 d7 (wz (f + 208)) (wz (f + 240)) (wz f) s9 s10 (wz (f + 120)) w3 w4 w5 w6 t F4 fc3 m4
                             FPOS ltac:(clear - FLO LOR SPT; ul) ltac:(clear - SHB0; unfold SHB in *; lia) ltac:(clear - SHT LOR SPT; ul) FS4 MI4)|].
  cbv beta. intros ms5 (m5 & -> & MU5 & WM5 & MI5 & FS5). apply evt_done. unfold tl_st.
  assert (REL5 : REL m5).
  { intros a Ha Ho. rewrite (MU5 a); [exact (REL4 a Ha Ho)|]. cbn [outside]. split; [exact (proj1 (OWA _ Ho))| exact I]. }
  pose proof (RELAG m5 REL5) as AG5.
  assert (ART5 : ART RT Σ3 m5).
  { apply (art_client_write RT AF Σ3 m4 m5 sp' ART4 ltac:(rewrite SP3; clear - WLO ELO LOR SPR; ul)); [| exact WM5]. intros a Ha. apply MU5. cbn [outside]. split; [| exact I].
    intros Hin. apply Ha. rewrite LV3, FRS3. apply INSH. clear - Hin. lia. }
  assert (ST5 : stk asegs m5 lo sp') by (apply (stk_agree asegs m4 m5 _ _ ST4); [| exact WM5]; intros a Ha; apply MU5; cbn [outside]; cbv beta in Ha; split; [clear - Ha SHT; lia| exact I]).

  assert (RELS : forall a : word, sp' <= bv_unsigned a < usp -> m5 a = m a).
  { intros a Ha. pose proof (INS _ Ha) as CA.
    rewrite (MU5 a); [| cbn [outside]; split; [clear - Ha SHT LOR SPR; ul| exact I]].
    rewrite (PRES4 a CA); [| cbn [outside]; split; [clear - Ha FLO LOR SPR; ul| exact I]].
    rewrite (PRES3 a CA); [| unfold EL_LIB_FP, LIB_FP, EL_UNW_A, EL_EHG_A, EL_TPLOC_A, TPV_A; cbn [outside app]; clear - Ha FLO LOR SPR LLO; unfold FUZZ_STACK in *; repeat split; try exact I; lia].
    rewrite (PRES2 a CA); [| cbn [outside]; unfold PJ_LOC_LO_A, PJ_LOC_HI_A; clear - Ha FLO LOR SPR LLO; unfold FUZZ_STACK in *; repeat split; try exact I; lia].
    apply MU1. cbn [outside]. split; [clear - Ha SHT LOR SPR; ul| exact I]. }
  assert (AGS : forall P : Z -> Prop, (forall x, P x -> sp' <= x < usp) -> agree_on P m m5) by (intros P HP a Ha; exact (RELS a (HP _ Ha))).
  apply (POST false (rt_credit RT Σ3) Σ3 m5 fc3 F4). unfold arm_postA, artxA. cbn [lf_usp lf_S1 lf_F lf_lo].
  split; [split; [exact ART5| reflexivity]|]. split; [exact MI5|]. split; [exact ST5|]. split; [exact FRM3|].
  split; [exact LV3|]. split; [exact FRS3|]. split; [exact SP3|].
  split; [clear - CR3; unfold arm_costA; cbn [Z.eqb Pos.eqb orb]; lia|].
  split; [intros a Ha Ho; exact (REL5 a Ha Ho)|].
  split; [| intros X; discriminate X].
  exists jr, jos4. unfold arm_memA. cbn [lf_usp lf_S1 lf_F lf_lo].
  split; [eapply rw_cells_agree_nw; [exact C16|]; apply AGS; intros x Hx; cbn [cells_size csize Nat.add] in Hx; clear - Hx SPR; lia|].
  split; [eapply rw_cells_agree_nw; [exact C100|]; apply AGS; intros x Hx; cbn [cells_size csize Nat.add] in Hx; clear - Hx SPR; lia|].
  split; [eapply rw_cells_agree_nw; [exact C128|]; apply AGS; intros x Hx; cbn [cells_size csize Nat.add] in Hx; clear - Hx SPR; lia|].
  split; [eapply rw_cells_agree_nw; [exact CE|]; apply AG5; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [apply INFR; lia| apply OWD; lia]|].
  split; [eapply rw_cells_agree_nw; [exact HULL4|]; apply (agree_of_munch _ _ _ _ MU5); intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside]; split; [clear - Hx FSELF; lia| exact I]|].
  split; [unfold el_shadow_armA; exact FS5|].
  split.
  { apply (AINV_A_agree E m3 m5 AI3). intros a Ha. destruct (AIN _ Ha) as [CA OA].
    rewrite (MU5 a); [| cbn [outside]; split; [exact (proj1 (OWA _ OA))| exact I]].
    apply PRES4; [rewrite <- LV3, <- FRS3 in CA |- *; exact CA| exact (proj2 (proj2 (proj2 (OWA _ OA))))]. }
  split.
  { apply (el_libA_agree m3 m5 LIB3). intros a Ha. pose proof (el_lib_rng_static _ Ha) as [CSa R].
    rewrite (MU5 a); [| cbn [outside]; rewrite SHF0; unfold SHB; split; [clear - R FPOS; Z.div_mod_to_equations; lia| exact I]].
    apply PRES4; [exact (INST _ CSa)| cbn [outside]; split; [clear - R FSEG; unfold SEGTOP_A in FSEG; lia| exact I]]. }
  split; [exact (NLX m5 REL5)| exact (IOSX Σ3 m5 REL5 ART5)].
Qed.
End Arm31.
