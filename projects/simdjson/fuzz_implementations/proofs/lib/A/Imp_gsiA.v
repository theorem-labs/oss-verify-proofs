(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.AS Require Import PropExec ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP Frame.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A Require Import Layout Shadow RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_rlkit D_libiface I_lkit X_ixdefs
     Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_hkit4A Atp_hkit5A Atp_fzwA Atp_activewA Atp_pidwA Pj_rtkA Pj_cpsA Pj_defsA
     Atp_kitA Imp_hdefs0A Imp_libifaceA Imp_gsidefsA Imp_annotA Imp_gsi1A Imp_gsi2A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma g_walk1 : forall (usp lo : Z) (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 64 -> 0x100000000 <= lo -> usp < 2^63 -> client_consts m -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m' : mem) (j : list byte),
      ms = MS (mkR (wz 0xb48b8) (wz (usp - 64)) gp tp t0 t1 t2 (wz IMP_VEC_OBJ_A) s1 (wz IMP_VEC_OBJ_A) (wz 0) (wz 24) a3 a4 a5 a6 a7
                   s2 s3 (wz SHB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz e_asan_memset) fc None m' (seg_rom asegs)
      /\ munch [(usp - 64, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (usp - 64)
      /\ rw_cells asegs m' (usp - 64) [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    (entry_st ra (wz usp) gp tp t0 t1 t2 s0 s1 (wz IMP_VEC_OBJ_A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc IMP_GRSI_A m).
Proof.
  intros until m. intros ST LO GLO SPH (CC1 & CC2 & _ & _) MI.
  unfold entry_st, IMP_VEC_OBJ_A, IMP_GRSI_A, e_asan_memset, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SHB in *.
  pose proof (munch_refl [(usp - 64, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep. carve_frame 64%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 64 _ [] [8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac | skipn _ _ => idtac end; let j := fresh "jk" in set (j := t) in FR; clearbody j end.
  ls. ls. ls. ls. ls. ls. ls.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  apply evt_done. eexists _, _. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| exact FR].
Qed.

Lemma g_walk3 : forall (usp lo A8 : Z) (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (j : list byte) F fc (m : mem),
  stk asegs m lo (usp - 64) -> lo <= usp - 64 -> 0x100000000 <= lo -> usp < 2^63 -> 0 < A8 -> A8 + 16 < 2^63 ->
  pb_statsh m ->
  rw_cells asegs m IMP_VEC_OBJ_A [C8 (wz A8); C8 (wz (A8 + 8)); C8 (wz (A8 + 8))] ->
  rw_cells asegs m (usp - 64) [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m' : mem),
      ms = MS (mkR ra (wz usp) gp tp t0 t1 t2 s0 s1 (wz (A8 + 8)) (wz A8) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(usp - 64, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp)
    (MS (mkR (wz 0xb4904) (wz (usp - 64)) gp tp t0 t1 t2 (wz IMP_VEC_OBJ_A) (wz IMP_AVP_ARR_A) (wz A8) a1 a2 a3 a4 a5 a6 a7
             (wz (IMP_AVP_ARR_A + 8)) (wz IMP_AVP_ARR_A) (wz SHB) (wz 2148326364) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0xb4904) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO GLO SPH A80 A8H (SA8 & SA9 & SAA & SDC) VEC FR MI.
  unfold IMP_VEC_OBJ_A, IMP_AVP_ARR_A, SHB, z8 in *. change (7003872 + 8) with 7003880 in *.
  pose proof (munch_refl [(usp - 64, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 64)) = usp - 64) by (apply unsigned_lit; lia).
  replace (usp - 64) with (usp + -64) in * by lia.

  zstep. zstep. zstep. zstep. if_false.

  zstep. try rewrite shr3_div. zstep. try change (7003456 / 8 + 2147450880) with 2148326312. zstep. shz_norm. zstep. if_false.
  zstep. zstep. try rewrite shr3_div. zstep. try change (7003464 / 8 + 2147450880) with 2148326313. zstep. shz_norm. zstep. if_false.

  zstep. zstep. step. if_cases K; zify_cond K; [exfalso; lia|].

  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. release_frame FR ST usp. zstep.
  apply evt_done. eexists _. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact ST].
Qed.

Section GRSI.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.

Hypothesis AFI : forall Σ m, ART RT Σ m -> vt_impl m.

Hypothesis AF_IXIT : forall Σ m, ART RT Σ m -> ixit_rt (rt_sp0 RT Σ) m.

Hypothesis AF_LVM : forall Σ m p k, ART RT Σ m -> In (p, k) (rt_live RT Σ) ->
  (0 <= p /\ p + k <= 0x7fff8000) \/ (0x10007fff7fff < p /\ p + k <= 0x800000000000).
Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.
Local Ltac ua := unfold IMP_VEC_OBJ_A, IMP_AVL_GUARD_A, IMP_AVP_SPAN_A, IMP_AVP_GUARD_A, IMP_AVP_ARR_A, SJ_SINGLETON, SEGTOP_A in *.

Lemma sup_sh_art : forall Σ m, ART RT Σ m ->
  ro_cells asegs m 2148326368 [C1 z8] /\ ro_cells asegs m 2147637348 [C1 z8] /\ ro_cells asegs m 2148326373 [C1 z8].
Proof using AF.
  intros Σ m HA.
  pose proof (shz_static RT AF Σ m SJ_SINGLETON 48 HA eq_refl ltac:(unfold SJ_SINGLETON; lia) eq_refl
                ltac:(intros i Hi; unfold SJ_SINGLETON; split; [apply client_static_intro; lia| lia])) as S1.
  pose proof (shz_lit RT AF Σ m 0x16c300 64 HA ltac:(unfold ACC_LITS; repeat (first [left; reflexivity | right])) eq_refl ltac:(lia) eq_refl) as S2.
  unfold SJ_SINGLETON in S1.
  change 2148326368 with (shad 7003904). change 2147637348 with (shad 1491744). change 2148326373 with (shad 7003944).
  refine (conj _ (conj _ _)); (apply shz_ro1; [| reflexivity| lia]); first [eapply shz_sub; [exact S1| lia| lia] | eapply shz_sub; [exact S2| lia| lia]].
Qed.

Theorem grsi_okA : grsi_icontractA RT.
Proof using AF RC AFI AF_IXIT AF_LVM.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    FDO MST -> -> (LIB0 & AVL0 & SPAN0 & AVPG0 & ARR0 & VEC0) FRM LPOS LVB CRB ART0 MI0 ST0 LOW LOSP SPA SP16 _ _.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP. clear ESP.
  unfold GRSI_STACK_A, RT_STACK in LOSP. unfold GRSI_LIVE_A in LVB. unfold GRSI_COST_A in CRB. unfold GRSI_FRAMES_A in FRM.
  assert (GLO : 0x100000000 <= lo) by ul. assert (SPH : usp < 2^63) by ul.
  assert (SPLIT : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) usp a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split_c RT AF Σ m usp a ART0 Ha); [left; lia| right; lia]. }
  destruct LIB0 as (ACT0 & AG0 & SING0 & SGD0).
  apply (cps_of_aevt RT PMc).

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (g_walk1 usp lo ra gp _ t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ST0 ltac:(lia) GLO SPH
                             (af_client_consts RT AF Σ m ART0) MI0)|].
  cbv beta. intros ms1 (m1 & j & -> & MU1 & WM1 & MI1 & ST1 & FR1). apply evt_done.
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 (usp - 64) ART0 ltac:(ul)); [| exact WM1].
    intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. ul. }
  assert (T1 : forall P : Z -> Prop, (forall x, P x -> x < lo) -> agree_on P m m1).
  { intros P HP a Ha. apply MU1. cbn [outside]. pose proof (HP _ Ha). split; [lia| exact I]. }
  assert (AGR1 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> outside GRSI_W (bv_unsigned a) -> m1 a = m a).
  { intros a Ha _. apply MU1. cbn [outside]. pose proof (SPLIT _ Ha). split; [lia| exact I]. }
  Local Ltac stat T H := eapply rw_cells_agree_nw; [exact H|]; apply T; intros x Hx; cbn [cells_size csize Nat.add length g00 g11] in Hx;
                         unfold IMP_VEC_OBJ_A, IMP_AVL_GUARD_A, IMP_AVP_SPAN_A, IMP_AVP_GUARD_A, IMP_AVP_ARR_A, SJ_SINGLETON, SEGTOP_A in *; lia.
  assert (VEC1 : rw_cells asegs m1 IMP_VEC_OBJ_A [C8 (wz 0); C8 (wz 0); C8 (wz 0)]) by stat T1 VEC0.
  assert (AVL1 : rw_cells asegs m1 IMP_AVL_GUARD_A g00) by stat T1 AVL0.
  assert (SPAN1 : rw_cells asegs m1 IMP_AVP_SPAN_A [C8 (wz 0); C8 (wz 0)]) by stat T1 SPAN0.
  assert (AVPG1 : rw_cells asegs m1 IMP_AVP_GUARD_A g00) by stat T1 AVPG0.
  assert (ARR1 : rw_cells asegs m1 IMP_AVP_ARR_A [C8 (wz 0)]) by stat T1 ARR0.
  assert (ACT1 : rw_cells asegs m1 0x6ade60 [C8 (Z_to_bv 64 0)]) by stat T1 ACT0.
  assert (AG1 : rw_cells asegs m1 0x6ade80 [C1 z8; C1 z8]) by stat T1 AG0.
  assert (SING1 : rw_cells asegs m1 0x6adf00 [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 0)]) by stat T1 SING0.
  assert (SGD1 : rw_cells asegs m1 0x6adf60 [C1 z8; C1 z8]) by stat T1 SGD0.
  clear T1 MU1 VEC0 AVL0 SPAN0 AVPG0 ARR0 ACT0 AG0 SING0 SGD0.

  assert (EU64 : bv_unsigned (Z_to_bv 64 (usp - 64)) = usp - 64) by (apply unsigned_lit; lia).
  assert (CDST : checked_dst RT Σ m1 (wz (usp - 64)) IMP_VEC_OBJ_A 24).
  { unfold checked_dst. rewrite EU64. split; [| split].
    - intros _. split.
      + apply (af_acc_static RT AF Σ m1 IMP_VEC_OBJ_A 24 ART1 ltac:(unfold IMP_VEC_OBJ_A; lia)).
        intros i Hi. unfold IMP_VEC_OBJ_A. split; [apply client_static_intro; lia| lia].
      + right; right; right. unfold IMP_VEC_OBJ_A, SEGTOP_A. lia.
    - intros i Hi. right; left. apply client_static_intro. unfold IMP_VEC_OBJ_A. lia.
    - exact (rw_cells_wr_at asegs _ _ _ 24 VEC1 ltac:(cbn; lia)). }
  assert (COK1 : call_ok RT Σ m1 (wz (usp - 64)) lo).
  { unfold call_ok. rewrite EU64. split; [exact ST1|]. split; [lia|]. split; [ul|]. split; [ul| clear - SP16; Z.div_mod_to_equations; lia]. }
  eapply (aevt_memsetP RT RC PMc FDO MST Σ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 IMP_VEC_OBJ_A 24 z8 lo eq_refl eq_refl eq_refl
            ltac:(unfold IMP_VEC_OBJ_A; lia) ltac:(lia) CDST ART1 MI1 COK1).
  intros w0 w1 w2 b1 b2 b3 b4 b5 b6 b7 w3 w4 w5 w6 F2 m2 (ART2 & MI2 & WM2 & ST2) PR2 BY2. rewrite EU64 in ST2, PR2.
  rewrite (ret_pc_even 0xb48b8) by lia. change (Z.to_nat 24) with 24%nat in BY2.
  assert (T2 : forall P : Z -> Prop, (forall x, P x -> (usp - 64 <= x < usp) \/ (x < SEGTOP_A /\ client_static x /\ ~ (IMP_VEC_OBJ_A <= x < IMP_VEC_OBJ_A + 24))) -> agree_on P m1 m2).
  { intros P HP. apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PR2). intros x Hx. destruct (HP _ Hx) as [H|(H1 & H2 & H3)].
    - split; [left; ul| unfold IMP_VEC_OBJ_A, SEGTOP_A in *; ul].
    - split; [right; left; exact H2| exact H3]. }
  assert (AGR2 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> outside GRSI_W (bv_unsigned a) -> m2 a = m a).
  { intros a Ha Ho. rewrite <- (AGR1 a Ha Ho). apply PR2; [apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| intros e He; exact He| lia]|].
    cbn [outside GRSI_W] in Ho. unfold IMP_VEC_OBJ_A in *. lia. }
  Local Ltac statc T H := eapply rw_cells_agree_nw; [exact H|]; apply T; intros x Hx; cbn [cells_size csize Nat.add length g00 g11] in Hx; right;
                          unfold IMP_VEC_OBJ_A, IMP_AVL_GUARD_A, IMP_AVP_SPAN_A, IMP_AVP_GUARD_A, IMP_AVP_ARR_A, SJ_SINGLETON, SEGTOP_A in *;
                          (split; [lia| split; [apply client_static_intro; lia| lia]]).
  assert (FR2 : rw_cells asegs m2 (usp - 64) [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_agree_nw; [exact FR1|]. apply T2. intros x Hx. cbn [cells_size csize Nat.add length g00 g11] in Hx. left. lia. }
  assert (AVL2 : rw_cells asegs m2 IMP_AVL_GUARD_A g00) by statc T2 AVL1.
  assert (SPAN2 : rw_cells asegs m2 IMP_AVP_SPAN_A [C8 (wz 0); C8 (wz 0)]) by statc T2 SPAN1.
  assert (AVPG2 : rw_cells asegs m2 IMP_AVP_GUARD_A g00) by statc T2 AVPG1.
  assert (ARR2 : rw_cells asegs m2 IMP_AVP_ARR_A [C8 (wz 0)]) by statc T2 ARR1.
  assert (ACT2 : rw_cells asegs m2 0x6ade60 [C8 (Z_to_bv 64 0)]) by statc T2 ACT1.
  assert (AG2 : rw_cells asegs m2 0x6ade80 [C1 z8; C1 z8]) by statc T2 AG1.
  assert (SING2 : rw_cells asegs m2 0x6adf00 [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 0)]) by statc T2 SING1.
  assert (SGD2 : rw_cells asegs m2 0x6adf60 [C1 z8; C1 z8]) by statc T2 SGD1.
  assert (VEC2 : rw_cells asegs m2 IMP_VEC_OBJ_A [C8 (wz 0); C8 (wz 0); C8 (wz 0)]).
  { eapply (rw_cells_recastA m2 IMP_VEC_OBJ_A [CB 24 (repeat z8 24)]); [| cbn; repeat split; exact I| reflexivity].
    exact (rw_cells_CB_intro m2 IMP_VEC_OBJ_A (repeat z8 24) BY2 (wr_at_transport asegs m1 m2 _ _ (rw_cells_wr_at asegs _ _ _ 24 VEC1 ltac:(cbn; lia)) WM2)). }
  clear T2 PR2 BY2 FR1 VEC1 AVL1 SPAN1 AVPG1 ARR1 ACT1 AG1 SING1 SGD1 CDST COK1 AGR1 WM1 MI1 ST1 ART1 WM2.

  apply (aevt_evt RT AF PMc MST).
  pose proof (munch_refl [(usp - 64 - 16, usp - 64)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
  zstep. clear MU WM.
  eapply evt_cut; [eapply (getavailA (usp - 64) lo _ gp _ w0 w1 w2 _ s1 _ b1 b2 b3 b4 b5 b6 b7 s2 s3 _ s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F2 fc m2 ST2 ltac:(lia) GLO ltac:(lia) AVL2 MI2)|].
  cbv beta. intros ms3 (c1 & c2 & m3 & -> & MU3 & WM3 & MI3 & ST3 & AVL3). apply evt_done.
  rewrite (ret_pc_even 0xb48bc) by lia.
  assert (ART3 : ART RT Σ m3).
  { apply (art_client_write RT AF Σ m2 m3 (usp - 80) ART2 ltac:(ul)); [| exact WM3].
    intros a Ha. apply MU3. cbn [outside]. split; [| split; [| exact I]]; intros Hin; apply Ha; [left; ul| right; left; apply client_static_intro; unfold IMP_AVL_GUARD_A in Hin; lia]. }
  assert (T3 : forall P : Z -> Prop, (forall x, P x -> (usp - 64 <= x < usp) \/ (x < SEGTOP_A /\ ~ (IMP_AVL_GUARD_A <= x < IMP_AVL_GUARD_A + 2))) -> agree_on P m2 m3).
  { intros P HP a Ha. apply MU3. cbn [outside]. pose proof (HP _ Ha). ua. split; [lia| split; [lia| exact I]]. }
  assert (AGR3 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> outside GRSI_W (bv_unsigned a) -> m3 a = m a).
  { intros a Ha Ho. rewrite <- (AGR2 a Ha Ho). apply MU3. cbn [outside GRSI_W] in Ho |- *. pose proof (SPLIT _ Ha). ua. split; [lia| split; [lia| exact I]]. }
  Local Ltac statn T H := eapply rw_cells_agree_nw; [exact H|]; apply T; intros x Hx; cbn [cells_size csize Nat.add length g00 g11] in Hx; right;
                          unfold IMP_VEC_OBJ_A, IMP_AVL_GUARD_A, IMP_AVP_SPAN_A, IMP_AVP_GUARD_A, IMP_AVP_ARR_A, SJ_SINGLETON, SEGTOP_A in *; lia.
  assert (FR3 : rw_cells asegs m3 (usp - 64) [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_agree_nw; [exact FR2|]. apply T3. intros x Hx. cbn [cells_size csize Nat.add length g00 g11] in Hx. left. lia. }
  assert (SPAN3 : rw_cells asegs m3 IMP_AVP_SPAN_A [C8 (wz 0); C8 (wz 0)]) by statn T3 SPAN2.
  assert (AVPG3 : rw_cells asegs m3 IMP_AVP_GUARD_A g00) by statn T3 AVPG2.
  assert (ARR3 : rw_cells asegs m3 IMP_AVP_ARR_A [C8 (wz 0)]) by statn T3 ARR2.
  assert (ACT3 : rw_cells asegs m3 0x6ade60 [C8 (Z_to_bv 64 0)]) by statn T3 ACT2.
  assert (AG3 : rw_cells asegs m3 0x6ade80 [C1 z8; C1 z8]) by statn T3 AG2.
  assert (SING3 : rw_cells asegs m3 0x6adf00 [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 0)]) by statn T3 SING2.
  assert (SGD3 : rw_cells asegs m3 0x6adf60 [C1 z8; C1 z8]) by statn T3 SGD2.
  assert (VEC3 : rw_cells asegs m3 IMP_VEC_OBJ_A [C8 (wz 0); C8 (wz 0); C8 (wz 0)]) by statn T3 VEC2.
  clear T3 MU3 WM3 FR2 AVL2 SPAN2 AVPG2 ARR2 ACT2 AG2 SING2 SGD2 VEC2 AGR2 MI2 ST2 ART2.

  apply (aevt_evt RT AF PMc MST).
  pose proof (munch_refl [(usp - 64 - 16, usp - 64)] m3) as MU. pose proof (wmono_refl asegs m3) as WM.
  zstep. zstep. clear MU WM.
  eapply evt_cut; [eapply (implbeginA (usp - 64) lo _ gp _ w0 w1 w2 _ s1 c1 c2 b3 b4 b5 b6 b7 _ s3 _ s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F2 fc m3
                             ST3 ltac:(lia) GLO ltac:(lia) AVPG3 SGD3 SING3 SPAN3 ARR3 MI3)|].
  cbv beta. intros ms4 (d1 & d2 & d3 & d4 & d5 & d6 & m4 & -> & MU4 & WM4 & MI4 & ST4 & AVPG4 & SGD4 & SING4 & SPAN4 & ARR4). apply evt_done.
  rewrite (ret_pc_even 0xb48c4) by lia. unfold begin_W in MU4.
  assert (ART4 : ART RT Σ m4).
  { apply (art_client_write RT AF Σ m3 m4 (usp - 96) ART3 ltac:(ul)); [| exact WM4].
    intros a Ha. apply MU4. cbn [outside]. unfold IMP_AVP_SPAN_A, IMP_AVP_GUARD_A, IMP_AVP_ARR_A, SJ_SINGLETON.
    repeat (split; [intros Hin; apply Ha; first [left; ul | right; left; apply client_static_intro; lia]|]). exact I. }
  assert (T4 : forall P : Z -> Prop, (forall x, P x -> (usp - 64 <= x < usp) \/ (x < SEGTOP_A /\ outside (tl (begin_W usp)) x)) -> agree_on P m3 m4).
  { intros P HP a Ha. apply MU4. pose proof (HP _ Ha) as X. cbn [outside begin_W tl] in X |- *. ua. split; [lia| ]. destruct X as [X|(X1 & X2)]; [| exact X2].
    repeat (split; [lia|]). exact I. }
  assert (AGR4 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> outside GRSI_W (bv_unsigned a) -> m4 a = m a).
  { intros a Ha Ho. rewrite <- (AGR3 a Ha Ho). apply MU4. cbn [outside GRSI_W] in Ho |- *. pose proof (SPLIT _ Ha).
    destruct Ho as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & _). ua. split; [lia|]. repeat (split; [first [assumption| lia]|]). exact I. }
  Local Ltac stato T H := eapply rw_cells_agree_nw; [exact H|]; apply T; intros x Hx; cbn [cells_size csize Nat.add length g00 g11 outside begin_W tl] in Hx |- *; right;
                          unfold IMP_VEC_OBJ_A, IMP_AVL_GUARD_A, IMP_AVP_SPAN_A, IMP_AVP_GUARD_A, IMP_AVP_ARR_A, SJ_SINGLETON, SEGTOP_A in *;
                          (split; [lia|]); repeat (split; [lia|]); exact I.
  assert (FR4 : rw_cells asegs m4 (usp - 64) [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_agree_nw; [exact FR3|]. apply T4. intros x Hx. cbn [cells_size csize Nat.add length g00 g11] in Hx. left. lia. }
  assert (AVL4 : rw_cells asegs m4 IMP_AVL_GUARD_A g11) by stato T4 AVL3.
  assert (ACT4 : rw_cells asegs m4 0x6ade60 [C8 (Z_to_bv 64 0)]) by stato T4 ACT3.
  assert (AG4 : rw_cells asegs m4 0x6ade80 [C1 z8; C1 z8]) by stato T4 AG3.
  assert (VEC4 : rw_cells asegs m4 IMP_VEC_OBJ_A [C8 (wz 0); C8 (wz 0); C8 (wz 0)]) by stato T4 VEC3.
  clear T4 MU4 WM4 FR3 AVL3 SPAN3 AVPG3 ARR3 ACT3 AG3 SING3 SGD3 VEC3 AGR3 MI3 ST3 ART3.

  apply (aevt_evt RT AF PMc MST).
  pose proof (munch_refl [(usp - 64 - 16, usp - 64)] m4) as MU. pose proof (wmono_refl asegs m4) as WM.
  zstep. zstep. zstep. clear MU WM.
  eapply evt_cut; [eapply (implendA (usp - 64) lo _ gp _ w0 w1 w2 _ _ _ d1 d2 d3 d4 d5 d6 b7 _ s3 _ s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F2 fc m4
                             ST4 ltac:(lia) GLO ltac:(lia) AVPG4 SPAN4 MI4)|].
  cbv beta. intros ms5 (e1 & m5 & -> & MU5 & WM5 & MI5 & ST5). apply evt_done.
  rewrite (ret_pc_even 0xb48d0) by lia.
  assert (ART5 : ART RT Σ m5).
  { apply (art_client_write RT AF Σ m4 m5 (usp - 80) ART4 ltac:(ul)); [| exact WM5].
    intros a Ha. apply MU5. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. ul. }
  assert (T5 : forall P : Z -> Prop, (forall x, P x -> (usp - 64 <= x < usp) \/ x < SEGTOP_A) -> agree_on P m4 m5).
  { intros P HP a Ha. apply MU5. cbn [outside]. pose proof (HP _ Ha). ua. split; [lia| exact I]. }
  assert (AGR5 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> outside GRSI_W (bv_unsigned a) -> m5 a = m a).
  { intros a Ha Ho. rewrite <- (AGR4 a Ha Ho). apply MU5. cbn [outside]. pose proof (SPLIT _ Ha). split; [lia| exact I]. }
  assert (FR5 : rw_cells asegs m5 (usp - 64) [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_agree_nw; [exact FR4|]. apply T5. intros x Hx. cbn [cells_size csize Nat.add length g00 g11] in Hx. left. lia. }
  assert (AVL5 : rw_cells asegs m5 IMP_AVL_GUARD_A g11) by statn T5 AVL4.
  assert (AVPG5 : rw_cells asegs m5 IMP_AVP_GUARD_A g11) by statn T5 AVPG4.
  assert (SGD5 : rw_cells asegs m5 0x6adf60 [C1 one8; C1 one8]) by statn T5 SGD4.
  assert (SING5 : rw_cells asegs m5 SJ_SINGLETON [C8 (wz 0x16c310); C8 (wz 0x29900); C8 (wz 8); C8 (wz 0x2cfe0); C8 (wz 31); C4 (wz 0)]) by statn T5 SING4.
  assert (SPAN5 : rw_cells asegs m5 IMP_AVP_SPAN_A [C8 (wz IMP_AVP_ARR_A); C8 (wz 1)]) by statn T5 SPAN4.
  assert (ARR5 : rw_cells asegs m5 IMP_AVP_ARR_A [C8 (wz SJ_SINGLETON)]) by statn T5 ARR4.
  assert (ACT5 : rw_cells asegs m5 0x6ade60 [C8 (Z_to_bv 64 0)]) by statn T5 ACT4.
  assert (AG5 : rw_cells asegs m5 0x6ade80 [C1 z8; C1 z8]) by statn T5 AG4.
  assert (VEC5 : rw_cells asegs m5 IMP_VEC_OBJ_A [C8 (wz 0); C8 (wz 0); C8 (wz 0)]) by statn T5 VEC4.
  clear T5 MU5 WM5 FR4 AVL4 AVPG4 SGD4 SING4 SPAN4 ARR4 ACT4 AG4 VEC4 AGR4 MI4 ST4 ART4.

  destruct (pb_statsh_art RT AF Σ m5 ART5) as (_ & _ & _ & SDC). destruct (sup_sh_art Σ m5 ART5) as (SS0 & SS1 & SS2).
  apply (aevt_evt RT AF PMc MST).
  pose proof (munch_refl [(usp - 64 - 16, usp - 64)] m5) as MU. pose proof (wmono_refl asegs m5) as WM.
  unfold IMP_AVP_ARR_A, SHB in *. change (7003872 + 8) with 7003880.
  zstep. if_false. zstep. zstep. try rewrite shr3_div. zstep. try change (2147450880 + 7003872 / 8) with 2148326364. zstep.
  zstep. shz_norm. zstep. if_false. zstep. zstep. clear MU WM.
  eapply evt_cut; [eapply (supportedA (usp - 64) lo _ gp _ w0 w1 w2 _ _ e1 d2 d3 d4 d5 d6 b7 _ _ _ _ s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F2 fc m5
                             ST5 ltac:(lia) GLO ltac:(lia) SS0 SS1 SS2 (AFI Σ m5 ART5) (af_client_consts RT AF Σ m5 ART5) SING5 MI5)|].
  cbv beta. intros ms6 (f1 & f2 & f3 & m6 & -> & MU6 & WM6 & MI6 & ST6). apply evt_done.
  rewrite (ret_pc_even 0xb48f4) by lia.
  assert (ART6 : ART RT Σ m6).
  { apply (art_client_write RT AF Σ m5 m6 (usp - 96) ART5 ltac:(ul)); [| exact WM6].
    intros a Ha. apply MU6. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. ul. }
  assert (T6 : forall P : Z -> Prop, (forall x, P x -> (usp - 64 <= x < usp) \/ x < SEGTOP_A) -> agree_on P m5 m6).
  { intros P HP a Ha. apply MU6. cbn [outside]. pose proof (HP _ Ha). ua. split; [lia| exact I]. }
  assert (AGR6 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> outside GRSI_W (bv_unsigned a) -> m6 a = m a).
  { intros a Ha Ho. rewrite <- (AGR5 a Ha Ho). apply MU6. cbn [outside]. pose proof (SPLIT _ Ha). split; [lia| exact I]. }
  assert (FR6 : rw_cells asegs m6 (usp - 64) [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_agree_nw; [exact FR5|]. apply T6. intros x Hx. cbn [cells_size csize Nat.add length g00 g11] in Hx. left. lia. }
  assert (AVL6 : rw_cells asegs m6 IMP_AVL_GUARD_A g11) by statn T6 AVL5.
  assert (AVPG6 : rw_cells asegs m6 IMP_AVP_GUARD_A g11) by statn T6 AVPG5.
  assert (SGD6 : rw_cells asegs m6 0x6adf60 [C1 one8; C1 one8]) by statn T6 SGD5.
  assert (SING6 : rw_cells asegs m6 SJ_SINGLETON [C8 (wz 0x16c310); C8 (wz 0x29900); C8 (wz 8); C8 (wz 0x2cfe0); C8 (wz 31); C4 (wz 0)]) by statn T6 SING5.
  assert (SPAN6 : rw_cells asegs m6 IMP_AVP_SPAN_A [C8 (wz 7003872); C8 (wz 1)]) by statn T6 SPAN5.
  assert (ARR6 : rw_cells asegs m6 7003872 [C8 (wz SJ_SINGLETON)]) by statn T6 ARR5.
  assert (ACT6 : rw_cells asegs m6 0x6ade60 [C8 (Z_to_bv 64 0)]) by statn T6 ACT5.
  assert (AG6 : rw_cells asegs m6 0x6ade80 [C1 z8; C1 z8]) by statn T6 AG5.
  assert (VEC6 : rw_cells asegs m6 IMP_VEC_OBJ_A [C8 (wz 0); C8 (wz 0); C8 (wz 0)]) by statn T6 VEC5.
  clear T6 MU6 WM6 FR5 AVL5 AVPG5 SGD5 SING5 SPAN5 ARR5 ACT5 AG5 VEC5 AGR5 MI5 ST5 ART5 SDC SS0 SS1 SS2.

  apply (aevt_evt RT AF PMc MST).
  pose proof (munch_refl [(usp - 64 - 16, usp - 64)] m6) as MU. pose proof (wmono_refl asegs m6) as WM.
  zstep. if_false. zstep. zstep. zstep. clear MU WM. apply evt_done.
  eapply (pushbackA RT AF RC AF_IXIT AF_LVM PMc FDO MST Σ _ (usp - 64) lo (wz 0xb4904) gp (wz TPV_A) w0 w1 w2 _ _ _ _ _ _ _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F2 fc m6
            ART6 MI6 ST6 LOW ltac:(ul) ltac:(ul) ltac:(clear - SP16; Z.div_mod_to_equations; lia) eq_refl ltac:(lia) ltac:(lia) VEC6 ARR6).
  intros Σ1 A8 g1 g2 g3 g4 g5 g6 g7 v0 v1 v2 v3 v4 v5 v6 F3 m7 ART7 MI7 ST7 PR7 LV1 FRS1 SP1 CR1 P0 P16 VEC7 CH7.
  rewrite (ret_pc_even 0xb4904) by lia.
  pose proof (af_live_range RT AF Σ1 m7 A8 8 ART7 ltac:(rewrite LV1; left; reflexivity)) as (_ & PZ & PSG). rewrite SP1 in PZ.
  assert (T7 : forall P : Z -> Prop, (forall x, P x -> (usp - 64 <= x < usp) \/ (x < SEGTOP_A /\ client_static x /\ ~ (IMP_VEC_OBJ_A <= x < IMP_VEC_OBJ_A + 24))) -> agree_on P m6 m7).
  { intros P HP. apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PR7). intros x Hx. destruct (HP _ Hx) as [H|(H1 & H2 & H3)].
    - split; [left; ul| unfold IMP_VEC_OBJ_A, SEGTOP_A in *; ul].
    - split; [right; left; exact H2| exact H3]. }
  assert (AGR7 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> outside GRSI_W (bv_unsigned a) -> m7 a = m a).
  { intros a Ha Ho. rewrite <- (AGR6 a Ha Ho). apply PR7; [apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| intros e He; exact He| lia]|].
    cbn [outside GRSI_W] in Ho. unfold IMP_VEC_OBJ_A in *. lia. }
  assert (FR7 : rw_cells asegs m7 (usp - 64) [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_agree_nw; [exact FR6|]. apply T7. intros x Hx. cbn [cells_size csize Nat.add length g00 g11] in Hx. left. lia. }
  assert (AVL7 : rw_cells asegs m7 IMP_AVL_GUARD_A g11) by statc T7 AVL6.
  assert (AVPG7 : rw_cells asegs m7 IMP_AVP_GUARD_A g11) by statc T7 AVPG6.
  assert (SGD7 : rw_cells asegs m7 0x6adf60 [C1 one8; C1 one8]) by statc T7 SGD6.
  assert (SING7 : rw_cells asegs m7 SJ_SINGLETON [C8 (wz 0x16c310); C8 (wz 0x29900); C8 (wz 8); C8 (wz 0x2cfe0); C8 (wz 31); C4 (wz 0)]) by statc T7 SING6.
  assert (SPAN7 : rw_cells asegs m7 IMP_AVP_SPAN_A [C8 (wz 7003872); C8 (wz 1)]) by statc T7 SPAN6.
  assert (ARR7 : rw_cells asegs m7 7003872 [C8 (wz SJ_SINGLETON)]) by statc T7 ARR6.
  assert (ACT7 : rw_cells asegs m7 0x6ade60 [C8 (Z_to_bv 64 0)]) by statc T7 ACT6.
  assert (AG7 : rw_cells asegs m7 0x6ade80 [C1 z8; C1 z8]) by statc T7 AG6.
  clear T7 PR7 FR6 AVL6 AVPG6 SGD6 SING6 SPAN6 ARR6 ACT6 AG6 VEC6 AGR6 MI6 ST6 ART6.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (g_walk3 usp lo A8 ra gp _ v0 v1 v2 s0 s1 g1 g2 g3 g4 g5 g6 g7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 j F3 fc m7
                             ST7 ltac:(lia) GLO SPH P0 ltac:(ul) (pb_statsh_art RT AF Σ1 m7 ART7) VEC7 FR7 MI7)|].
  cbv beta. intros ms8 (m8 & -> & MU8 & WM8 & MI8 & ST8). apply evt_done.
  assert (ART8 : ART RT Σ1 m8).
  { apply (art_client_write RT AF Σ1 m7 m8 (usp - 64) ART7 ltac:(rewrite SP1; ul)); [| exact WM8].
    intros a Ha. apply MU8. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. ul. }
  assert (T8 : forall P : Z -> Prop, (forall x, P x -> x < lo) -> agree_on P m7 m8).
  { intros P HP a Ha. apply MU8. cbn [outside]. pose proof (HP _ Ha). split; [lia| exact I]. }
  assert (AGR8 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> outside GRSI_W (bv_unsigned a) -> m8 a = m a).
  { intros a Ha Ho. rewrite <- (AGR7 a Ha Ho). apply MU8. cbn [outside]. pose proof (SPLIT _ Ha). split; [lia| exact I]. }

  apply (aevt_done RT PMc). intros c Hc. exists Σ1, A8.
  split; [| refine (conj LV1 (conj P0 (conj P16 (conj FRS1 (conj SP1 _))))); rewrite CR1; unfold GRSI_COST_A; lia].
  eapply ASTA_conseq; [exact Hc|]. intros ms <-. exists (wz (A8 + 8)), m8.
  split; [eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _; reflexivity|].
  split; [exact (conj ART8 (conj MI8 ST8))|].
  split; [exact AGR8|].
  unfold grsi_postA, libm. unfold IMP_AVP_ARR_A.
  refine (conj (conj _ (conj _ (conj _ _))) (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  - stat T8 ACT7. - stat T8 AG7. - stat T8 SING7. - stat T8 SGD7. - stat T8 AVL7. - stat T8 SPAN7. - stat T8 AVPG7. - stat T8 ARR7.
  - eapply rw_cells_agree_nw; [exact VEC7|]. apply T8. intros x Hx. cbn [cells_size csize Nat.add length g00 g11] in Hx. unfold IMP_VEC_OBJ_A, SEGTOP_A in *. lia.
  - eapply rw_cells_agree_nw; [exact CH7|]. apply T8. intros x Hx. cbn [cells_size csize Nat.add length g00 g11] in Hx. lia.
Qed.
End GRSI.
