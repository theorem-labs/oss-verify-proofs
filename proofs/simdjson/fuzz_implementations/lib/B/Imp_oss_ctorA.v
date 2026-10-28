(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel ImpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Startup_glue Sj_stage1_kit Pj_loc_kit Pj_os_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_new Sj_num_akit Sj_num_amem Atp_hkit4A Atp_hkit5A Pj_rtkA Pj_defsA Pj_cpsA Pj_loc_getA Pj_os_defsA Imp_hdefsA Imp_oss_defsA Imp_str_growA Imp_sb_overflowA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma bytes_at_repeat_sub : forall (m : mem) a (b : byte) (n i k : nat), bytes_at bsegs m a (repeat b n) -> (i + k <= n)%nat ->
  bytes_at bsegs m (a + Z.of_nat i) (repeat b k).
Proof.
  intros m a b n i k H Hik. replace n with (i + (k + (n - i - k)))%nat in H by lia. rewrite !repeat_app in H.
  apply bytes_at_app in H. destruct H as [_ H]. rewrite repeat_length in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

Section CT.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis RC2 : rt_contracts2 RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis ROWS : forall Σ m, ART RT Σ m -> imp_rowsA m.

Local Ltac ul := unfold OSS_CTOR_STACK_A, PJ_LOC_STACK_A, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma append_short0A : forall (Σ : rts RT) (K : config -> Prop) (lo P q fO : Z) (kO : nat)
    (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  In (fO, kO) (rt_frames RT Σ) -> fO <= P -> P + 24 <= fO + fs_size kO - 8 -> P mod 8 = 0 -> rt_sp0 RT Σ - STACK_WIN <= lo -> 0x7fff7f800000 <= lo ->
  rw_cells bsegs m P [C8 (wz 0); C8 (wz 0); C8 (wz 0)] -> bytes_at bsegs m (shad P) [z8; z8; z8] ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo q -> lo + 80 + RT_STACK <= q -> q + 16 <= USTACK_TOP -> q mod 16 = 0 ->
  (forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     ART RT Σ m' -> mem_inv bsegs m' -> stk bsegs m' lo q ->
     rw_cells bsegs m' P [C1 (Z_to_bv 8 44); CB 23 (repeat z8 23)] -> bytes_at bsegs m' (shad P) [z8; z8; z8] ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(P, P + 24)] m m' ->
     aevt RT PMc Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0' t1' t2' s0 s1 (wz P) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt RT PMc Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz P) (wz 22) (wz 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz OSS_APPEND_A) fc None m (seg_rom bsegs)).
Proof using AF RC FDO MST.
  intros until m. intros INF PLO PHI P8 LOW LOR REP PSH ART0 MI ST LOQ QT Q16 HK.
  unfold OSS_APPEND_A, RT_STACK in *.
  pose proof (af_frames_range RT AF Σ m fO kO ART0 INF) as (F0 & FTOP & FSEG & FLIVE).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof (proj2 (af_fshadow_apart RT AF Σ m fO kO ART0 INF) fO kO INF) as FSELF.
  pose proof (fframe_ranges RT AF Σ m fO kO ART0 INF) as (_ & _ & _ & _ & SHT).
  remember (fs_size kO) as FSZ eqn:EFSZ.
  assert (Q0 : 0 <= q - 96) by (destruct ST; ul).
  assert (UQ80 : bv_unsigned (wz (q + -80)) = q + -80) by (apply unsigned_lit; ul).
  assert (SHP : shad fO <= shad P /\ shad P + 3 <= shad (fO + FSZ)) by (unfold shad; clear - PLO PHI P8; Z.div_mod_to_equations; lia).
  assert (CLF : forall Lx sp x, fO <= x < fO + FSZ - 8 -> aclient Lx (rt_frames RT Σ) sp x).
  { intros Lx sp x Hx. right; right; right; left. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia]. }
  assert (CLS : forall Lx sp x, shad fO <= x < shad (fO + FSZ) -> aclient Lx (rt_frames RT Σ) sp x).
  { intros Lx sp x Hx. right; right; right; right. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia]. }
  assert (CSEP : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) q a -> q <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split_c RT AF Σ m q a ART0 Ha) as [H|H]; [left; exact H| right; lia]. }
  apply (aevt_evt RT AF PMc MST).
  pose proof (munch_refl [(q - 80, q); (P, P + 24)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pj_hide PSH.
  lstep. carve_frame 80%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 80 _ [] [8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR. forget_junk FR.

  do 10 lstep. lstep. lstep. if_false. lstep.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (rw_cells_C8_read1_g bsegs mx _ _ _ REP) as RD end. change (bv_unsigned (Z_to_bv 64 0)) with 0 in RD.
  lstep. lstep. lstep. lstep. if_false.

  lstep. lstep. lstep. if_false. lstep. lstep. lstep. lstep. if_false.

  lstep. if_true. lstep. lstep. lstep. lstep. lstep. lstep.

  clear RD. retype REP [C1 (Z_to_bv 8 0); CB 22 (repeat (Z_to_bv 8 0) 22); C1 (Z_to_bv 8 0)].
  takeZ REP 1%nat (P + 1) R0. takeZ REP 1%nat (P + 23) RZ.
  lstep. apply evt_done.
  lazymatch goal with |- aevt _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  rename REP into RNUL. rename R0 into RB0.
  pj_unhide PSH.
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 (q - 80) ART0 ltac:(ul)); [| exact WM]. intros a Ha. apply MU. cbn [outside].
    split; [intros Hin; apply Ha; left; ul|]. split; [intros Hin; apply Ha; apply CLF; lia| exact I]. }
  assert (AG1 : forall Q : Z -> Prop, (forall x, Q x -> ~ (q - 80 <= x < q) /\ ~ (P <= x < P + 24)) -> agree_on Q m m1).
  { intros Q HP a Ha. apply MU. cbn [outside]. destruct (HP _ Ha) as [X Y]. split; [exact X| split; [exact Y| exact I]]. }
  assert (PSH1 : bytes_at bsegs m1 (shad P) [z8; z8; z8]).
  { eapply bytes_at_agree; [exact PSH|]. apply AG1. intros x Hx. cbn [length] in Hx. clear - Hx SHP FSELF SHT LOW LOQ PLO PHI. split; lia. }
  assert (CD : checked_dst RT Σ m1 (Z_to_bv 64 (q + -80)) (P + 1) 22).
  { unfold checked_dst. rewrite UQ80. split; [| split].
    - intros _. split; [apply (acc_sub bsegs m1 P 24); [apply (acc_zero_run bsegs m1 P 3); [exact P8| lia| exact PSH1]| lia| lia]|].
      right; left. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia].
    - intros i Hi. apply CLF. lia.
    - apply (rw_cells_wr_at bsegs m1 _ _ 22 RZ). cbn. lia. }
  assert (COK : call_ok RT Σ m1 (Z_to_bv 64 (q + -80)) lo).
  { unfold call_ok. rewrite UQ80. split; [exact ST|]. split; [lia|]. split; [ul|]. split; [ul| clear - Q16; Z.div_mod_to_equations; lia]. }
  clear MU WM.
  eapply (aevt_memsetS RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (P + 1) 22 (Z_to_bv 8 0) lo eq_refl eq_refl eq_refl ltac:(ul) ltac:(lia) CD ART1 ltac:(assumption) COK).
  intros w0 w1 w2 b1 b2 b3 b4 b5 b6 b7 w3 w4 w5 w6 F2 m2 (ART2 & MI2 & WM2 & ST2) PRES2 BY2. rewrite UQ80 in ST2, PRES2.
  rewrite (ret_pc_even 0x11c148) by lia.
  assert (AG2 : forall Q : Z -> Prop, (forall x, Q x -> ((q + -80 <= x < q) \/ (fO <= x < fO + FSZ - 8) \/ (shad fO <= x < shad (fO + FSZ))) /\ ~ (P + 1 <= x < P + 1 + 22)) -> agree_on Q m1 m2).
  { intros Q HP a Ha. destruct (HP _ Ha) as [HX HN]. apply PRES2; [| exact HN]. destruct HX as [H|[H|H]]; [left; ul| apply CLF; exact H| apply CLS; exact H]. }
  lazymatch type of FR with rw_cells _ _ _ ?cs => assert (FR2 : rw_cells bsegs m2 (q + -80) cs)
    by (eapply rw_cells_agree_nw; [exact FR|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [left; lia| clear - Hx PLO PHI FTOP LOW LOQ; lia]) end.
  assert (RB2 : rw_cells bsegs m2 P [C1 (Z_to_bv 8 0)]) by (eapply rw_cells_agree_nw; [exact RB0|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [right; left; lia| lia]).
  assert (RN2 : rw_cells bsegs m2 (P + 23) [C1 (Z_to_bv 8 0)]) by (eapply rw_cells_agree_nw; [exact RNUL|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [right; left; lia| lia]).
  assert (PSH2 : bytes_at bsegs m2 (shad P) [z8; z8; z8]).
  { eapply bytes_at_agree; [exact PSH1|]. apply AG2. intros x Hx. cbn [length] in Hx. clear - Hx SHP FSELF PLO PHI. split; [do 2 right; lia| lia]. }
  assert (RZ2 : rw_cells bsegs m2 (P + 1) [CB 22 (repeat (Z_to_bv 8 0) 22)]).
  { pose proof (rw_cells_CB_intro m2 (P + 1) _ BY2) as X. rewrite repeat_length in X. apply X. cbn.
    apply (wr_at_transport bsegs m1 m2 (P + 1) 22); [| exact WM2]. apply (rw_cells_wr_at bsegs m1 _ _ 22 RZ). cbn. lia. }
  assert (PRES02 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> ~ (P <= bv_unsigned a < P + 24) -> m2 a = m a).
  { intros a Ha Ho. rewrite (PRES2 a); [| apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| intros e He; exact He| lia]| lia].
    apply AG1 with (Q := fun x => x = bv_unsigned a); [| reflexivity]. intros x ->. split; [destruct (CSEP _ Ha); lia| exact Ho]. }
  clear AG2 AG1 PRES2 BY2 FR RB0 RNUL RZ PSH PSH1 CD COK ST MI ART0 ART1.

  apply (aevt_evt RT AF PMc MST).
  pose proof (munch_refl [(q - 80, q); (P, P + 24)]%Z m2) as MU. pose proof (wmono_refl bsegs m2) as WM.
  pj_hide PSH2.
  lstep. lstep. rewrite ?zxb_u, ?u8_lit. change (Z.land (0 mod 256) 1) with 0. lstep. if_false. lstep. lstep. lstep. lstep.
  replace (Z_to_bv 64 (P + 1 + 22)) with (Z_to_bv 64 (P + 23)) by (f_equal; lia). lstep.

  lstep. do 10 lstep. lstep. release_frame FR2 ST2 q. lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
  pj_unhide PSH2.
  pose proof (rw_cells_joinA _ _ _ _ _ RZ2 RN2 ltac:(cbn; lia)) as R23. cbn [app] in R23.
  lazymatch type of R23 with rw_cells _ _ _ ?cs => pose proof (rw_cells_merge bsegs _ _ [] cs [] ltac:(rewrite app_nil_l, app_nil_r; exact R23)) as R23' end.
  cbn [cells_size csize cells_bytes cbytes app] in R23'. change (repeat (Z_to_bv 8 0) 22 ++ [Z_to_bv 8 0]) with (repeat z8 23) in R23'.
  pose proof (rw_cells_joinA _ _ _ _ _ RB2 R23' ltac:(cbn; lia)) as RALL. cbn [app] in RALL.
  apply evt_done. eapply HK.
  - apply (art_client_write RT AF Σ m2 m9 (q + -80) ART2 ltac:(ul)); [| exact WM]. intros a Ha. apply MU. cbn [outside].
    split; [intros Hin; apply Ha; left; ul|]. split; [intros Hin; apply Ha; apply CLF; lia| exact I].
  - assumption.
  - exact ST2.
  - exact RALL.
  - eapply bytes_at_agree; [exact PSH2|]. apply (agree_of_munch _ _ _ _ MU). intros x Hx. cbn [length] in Hx. cbn [outside]. clear - Hx SHP FSELF SHT LOW LOQ PLO PHI. split; [| split; [| exact I]]; lia.
  - intros a Ha Ho. cbn [outside] in Ho. rewrite <- (PRES02 a Ha ltac:(lia)). apply MU. cbn [outside]. split; [destruct (CSEP _ Ha); lia|]. split; [lia| exact I].
Qed.

Local Ltac chk SHZ a := lstep; rewrite ?shr3_div; lstep; shz_pose SHZ a; lstep; shz_norm; lstep; if_false.

Local Ltac chk2 SHZ a := shz_pose SHZ a; lstep; shz_norm; lstep; if_false.

Local Ltac lit_addr H := match type of H with context [wa ?e] => let e' := eval cbv in e in change e with e' in H end.
Local Ltac chkV2 SHZ a := let H := fresh "VRD" in shz_pose_with SHZ a H; lit_addr H; lstep; shz_norm; lstep; if_false; try clear H.
Local Ltac chkV SHZ a := lstep; rewrite ?shr3_div; lstep; chkV2 SHZ a.

Lemma b2z_pos : forall x, (0 < x)%Z -> Z.b2z (0 <? x) = 1%Z.
Proof. intros x H. rewrite (proj2 (Z.ltb_lt 0 x) H). reflexivity. Qed.
Lemma b2z_lt1 : forall x, (0 < x)%Z -> Z.b2z (x <? 1) = 0%Z.
Proof. intros x H. rewrite (proj2 (Z.ltb_ge x 1)) by lia. reflexivity. Qed.
Local Ltac gref G := exfalso; rewrite ?unsigned_lit in G by lia; lia.
Local Ltac gtrap := let G := fresh "G" in zstep; if_cases G; zify_cond G; [gref G|]; try clear G.
Local Ltac unz := rewrite ?b2z_pos, ?b2z_lt1 by lia.

Lemma init_bufA : forall (Σ : rts RT) (K : config -> Prop) (lo O q fO : Z) (kO : nat) (j108 : list byte)
    (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  In (fO, kO) (rt_frames RT Σ) -> oss_inA fO kO O -> rt_sp0 RT Σ - STACK_WIN <= lo -> 0x7fff7f800000 <= lo ->
  rw_cells bsegs m (O + 8) [C8 (wz OSS_SB_VPTR_A); C8 (wz OSS_CLASSIC_A); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
  rw_cells bsegs m (O + 72) [C8 (wz 0); C8 (wz 0); C8 (wz 0)] -> rw_cells bsegs m (O + 96) [C8 (wz 0)] -> rw_cells bsegs m (O + 104) [CB 4 mode16; CB 4 j108] ->
  OSHADOWA m O ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo q -> lo + 160 + RT_STACK <= q -> q + 16 <= USTACK_TOP -> q mod 16 = 0 ->
  (forall t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     ART RT Σ m' -> mem_inv bsegs m' -> stk bsegs m' lo q ->
     rw_cells bsegs m' (O + 8) (sb_cellsA (ossA0 O)) -> rw_cells bsegs m' (O + 96) [C8 (wz (O + 73))] ->
     rw_cells bsegs m' (O + 72) [C1 (Z_to_bv 8 44); CB 23 (repeat z8 23)] -> rw_cells bsegs m' (O + 104) [CB 4 mode16; CB 4 j108] -> OSHADOWA m' O ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(O + 48, O + 104)] m m' ->
     aevt RT PMc Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt RT PMc Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz (O + 8)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz OSS_INIT_BUF_A) fc None m (seg_rom bsegs)).
Proof using AF RC FDO MST.
  intros until m. intros INF (FLO & FHI & AL16) LOW LOR SBC REP HMC MODE SH ART0 MI ST LOQ QT Q16 HK.
  unfold OSS_INIT_BUF_A, RT_STACK in *.
  pose proof (af_frames_range RT AF Σ m fO kO ART0 INF) as (F0 & FTOP & FSEG & FLIVE).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof (proj2 (af_fshadow_apart RT AF Σ m fO kO ART0 INF) fO kO INF) as FSELF.
  pose proof (fframe_ranges RT AF Σ m fO kO ART0 INF) as (_ & _ & _ & _ & SHT).
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in G1, G2, G3, G4.
  remember (fs_size kO) as FSZ eqn:EFSZ.
  assert (Q0 : 0 <= q - 176) by (destruct ST; ul).
  assert (SHO : shad fO <= shad O /\ shad O + 33 <= shad (fO + FSZ)) by (unfold shad; clear - FLO FHI AL16; Z.div_mod_to_equations; lia).
  assert (CLF : forall Lx sp x, fO <= x < fO + FSZ - 8 -> aclient Lx (rt_frames RT Σ) sp x).
  { intros Lx sp x Hx. right; right; right; left. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia]. }
  assert (CLS : forall Lx sp x, shad fO <= x < shad (fO + FSZ) -> aclient Lx (rt_frames RT Σ) sp x).
  { intros Lx sp x Hx. right; right; right; right. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia]. }
  assert (CSEP : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) q a -> q <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split_c RT AF Σ m q a ART0 Ha) as [H|H]; [left; exact H| right; lia]. }

  assert (SHZ0 : forall mx, OSHADOWA mx O -> shz mx O 264).
  { intros mx HB. change 264 with (8 * Z.of_nat 33). apply (shz_of_zero_run mx O 33); [clear - AL16; Z.div_mod_to_equations; lia| lia| exact HB]. }
  assert (SHZ : forall m', munch [(q - 80, q); (O + 48, O + 104)] m m' -> wmono bsegs m m' -> shz m' O 264).
  { intros m' MU' _. apply SHZ0. apply (OSHADOWA_agree m m' O SH). apply (agree_of_munch _ _ _ _ MU'). intros x Hx. cbn [outside].
    clear - Hx SHO FSELF SHT LOW LOQ FLO FHI. split; [lia| split; [lia| exact I]]. }
  unfold OSS_SB_VPTR_A, OSS_CLASSIC_A in SBC. unfold SHB in G2. unfold SEGTOP_A, STACK_WIN, USTACK_TOP in FTOP, SP0R, QT, LOW, SHT.
  apply (aevt_evt RT AF PMc MST).
  pose proof (munch_refl [(q - 80, q); (O + 48, O + 104)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  lstep. carve_frame 80%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 80 _ [] [8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR. forget_junk FR.

  do 10 lstep. lstep. lstep. lstep. lstep. lstep.

  chk SHZ (O + 96). lstep. lstep. chk SHZ (O + 72).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (rw_cells_C8_read1_g bsegs mx _ _ _ REP) as RD end. change (bv_unsigned (Z_to_bv 64 0)) with 0 in RD.
  lstep. lstep. lstep. if_false.

  lstep. lstep. rewrite ?zxb_u, ?u8_lit. change (Z.shiftr (0 mod 256) 1) with 0. lstep. lstep. chk SHZ (O + 104).
  lstep. lstep. lstep. if_true.

  lstep. lstep. if_false. lstep. try replace (0 + (O + 8 + 65)) with (O + 73) by lia. try replace (O + 8 + 65 + 0) with (O + 73) by lia.
  gtrap. lstep. lstep. lstep. unz. change (Z.lxor 1 0) with 1%Z. lstep. if_false.
  chk2 SHZ (O + 96). lstep. lstep. if_false. lstep. lstep. lstep. lstep. lstep.

  clear RD. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (rw_cells_C8_read1_g bsegs mx _ _ _ REP) as RD end. change (bv_unsigned (Z_to_bv 64 0)) with 0 in RD.
  lstep. lstep. rewrite ?zxb_u, ?u8_lit. lstep. if_true. lstep. change (Z.shiftr (0 mod 256) 1) with 0. lstep. if_cases Kc; zify_cond Kc; [exfalso; rewrite ?unsigned_lit in Kc by lia; cbn in Kc; lia| try clear Kc].
  lstep. lstep. clear RD.

  try replace (Z_to_bv 64 (22 - 0)) with (Z_to_bv 64 22) by (f_equal; lia). try replace (Z_to_bv 64 (22 + - 0)) with (Z_to_bv 64 22) by (f_equal; lia).
  apply evt_done.
  lazymatch goal with |- aevt _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
  assert (ART2 : ART RT Σ m2).
  { apply (art_client_write RT AF Σ m m2 (q - 80) ART0 ltac:(ul)); [| exact WM]. intros a Ha. apply MU. cbn [outside].
    split; [intros Hin; apply Ha; left; ul|]. split; [intros Hin; apply Ha; apply CLF; lia| exact I]. }
  assert (AG02 : forall Q : Z -> Prop, (forall x, Q x -> ~ (q - 80 <= x < q) /\ ~ (O + 48 <= x < O + 104)) -> agree_on Q m m2).
  { intros Q HP a Ha. apply MU. cbn [outside]. destruct (HP _ Ha) as [X Y]. split; [exact X| split; [exact Y| exact I]]. }
  assert (SH2 : OSHADOWA m2 O).
  { apply (OSHADOWA_agree m m2 O SH). apply AG02. intros x Hx. clear - Hx SHO FSELF SHT LOW LOQ FLO FHI. split; lia. }
  assert (PSH2 : bytes_at bsegs m2 (shad (O + 72)) [z8; z8; z8]).
  { replace (shad (O + 72)) with (shad O + Z.of_nat 9) by (unfold shad; clear - AL16; Z.div_mod_to_equations; lia).
    exact (bytes_at_repeat_sub m2 (shad O) z8 33 9 3 SH2 ltac:(lia)). }
  assert (PRES02 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> ~ (O + 48 <= bv_unsigned a < O + 104) -> m2 a = m a).
  { intros a Ha Ho. apply MU. cbn [outside]. split; [destruct (CSEP _ Ha); lia|]. split; [exact Ho| exact I]. }
  clear MU WM.
  eapply (append_short0A Σ K lo (O + 72) (q + -80) fO kO _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 INF ltac:(lia) ltac:(lia) ltac:(clear - AL16; Z.div_mod_to_equations; lia)
            ltac:(unfold STACK_WIN; exact LOW) LOR REP PSH2 ART2 ltac:(assumption) ST ltac:(unfold RT_STACK; lia) ltac:(unfold USTACK_TOP; lia) ltac:(clear - Q16; Z.div_mod_to_equations; lia)).
  intros w0 w1 w2 b1 b2 b3 b4 b5 b6 b7 w3 w4 w5 w6 F2 m3 ART3 MI3 ST3 REP3 PSH3 PRES3.
  rewrite (ret_pc_even 0xbfc4c) by lia.
  assert (AG3 : forall Q : Z -> Prop, (forall x, Q x -> ((q + -80 <= x < q) \/ (fO <= x < fO + FSZ - 8) \/ (shad fO <= x < shad (fO + FSZ))) /\ ~ (O + 72 <= x < O + 96)) -> agree_on Q m2 m3).
  { intros Q HP a Ha. destruct (HP _ Ha) as [HX HN]. apply PRES3; [| cbn [outside]; split; [clear - HN; lia| exact I]]. destruct HX as [H|[H|H]]; [left; ul| apply CLF; exact H| apply CLS; exact H]. }
  lazymatch type of FR with rw_cells _ _ _ ?cs => assert (FR3 : rw_cells bsegs m3 (q + -80) cs)
    by (eapply rw_cells_agree_nw; [exact FR|]; apply AG3; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [left; lia| clear - Hx FLO FHI FTOP LOW LOQ; lia]) end.
  lazymatch type of SBC with rw_cells _ _ _ ?cs => assert (SBC3 : rw_cells bsegs m3 (O + 8) cs)
    by (eapply rw_cells_agree_nw; [exact SBC|]; apply AG3; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [right; left; lia| lia]) end.
  lazymatch type of HMC with rw_cells _ _ _ ?cs => assert (HMC3 : rw_cells bsegs m3 (O + 96) cs)
    by (eapply rw_cells_agree_nw; [exact HMC|]; apply AG3; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [right; left; lia| lia]) end.
  assert (MODE3 : rw_cells bsegs m3 (O + 104) [CB 4 mode16; CB 4 j108])
    by (eapply rw_cells_agree_nw; [exact MODE|]; apply AG3; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [right; left; lia| lia]).
  assert (SH3 : OSHADOWA m3 O).
  { apply (OSHADOWA_agree m2 m3 O SH2). apply AG3. intros x Hx. clear - Hx SHO FSELF FLO FHI. split; [do 2 right; lia| lia]. }
  assert (PRES03 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> ~ (O + 48 <= bv_unsigned a < O + 104) -> m3 a = m a).
  { intros a Ha Ho. rewrite <- (PRES02 a Ha Ho). apply PRES3; [apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| intros e He; exact He| lia]| cbn [outside]; split; [lia| exact I]]. }
  assert (SHZ3 : forall m', munch [(q - 80, q); (O + 48, O + 104)] m3 m' -> wmono bsegs m3 m' -> shz m' O 264).
  { intros m' MU' _. apply SHZ0. apply (OSHADOWA_agree m3 m' O SH3). apply (agree_of_munch _ _ _ _ MU'). intros x Hx. cbn [outside].
    clear - Hx SHO FSELF SHT LOW LOQ FLO FHI. split; [lia| split; [lia| exact I]]. }
  clear AG3 FR SBC HMC MODE SH2 PSH2 PRES3 PRES02 ART2 REP ST.

  apply (aevt_evt RT AF PMc MST).
  pose proof (munch_refl [(q - 80, q); (O + 48, O + 104)]%Z m3) as MU. pose proof (wmono_refl bsegs m3) as WM.
  pj_hide PSH3.
  chk2 SHZ3 (O + 72).
  lstep. lstep. rewrite ?zxb_u, ?u8_lit. change (Z.land (44 mod 256) 1) with 0. lstep. if_false. lstep. change (Z.shiftr (44 mod 256) 1) with 22. lstep.

  takeZ SBC3 5%nat (O + 48) SBA.
  lstep. gtrap. lstep. lstep. unz. change (Z.lxor 1 0) with 1%Z. lstep. if_false.
  lstep. chk SHZ3 (O + 56). lstep. lstep. chk SHZ3 (O + 48). lstep. lstep. chk SHZ3 (O + 64). lstep.

  chk2 SHZ3 (O + 104).
  lstep. lstep. rewrite ?zxb_u, ?u8_lit. cbn [firstn skipn mode16]. change (Z.land (bv_unsigned (Z_to_bv 8 16)) 3) with 0. lstep. if_true.
  do 10 lstep. lstep. release_frame FR3 ST3 q. lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
  pj_unhide PSH3.
  lazymatch goal with H : rw_cells bsegs m9 (O + 48) _ |- _ => rename H into SBB end.
  pose proof (rw_cells_joinA _ _ _ _ _ SBA SBB ltac:(cbn; lia)) as SBALL. cbn [app] in SBALL.
  try replace (22 + (O + 73)) with (O + 95) in SBALL by lia.
  lazymatch goal with H : rw_cells bsegs m9 (O + 96) _ |- _ => try replace (0 + (O + 73)) with (O + 73) in H by lia end.
  apply evt_done. eapply HK.
  - apply (art_client_write RT AF Σ m3 m9 (q + -80) ART3 ltac:(ul)); [| exact WM]. intros a Ha. apply MU. cbn [outside].
    split; [intros Hin; apply Ha; left; ul|]. split; [intros Hin; apply Ha; apply CLF; lia| exact I].
  - assumption.
  - exact ST3.
  - unfold sb_cellsA, ossA0, oa_lim. cbn [oa_data oa_w oa_cap oa_heap]. unfold OSS_SB_VPTR_A, OSS_CLASSIC_A.
    replace (O + 73 + 0) with (O + 73) by lia. replace (O + 73 + 22) with (O + 95) by lia. exact SBALL.
  - assumption.
  - exact REP3.
  - assumption.
  - apply (OSHADOWA_agree m3 m9 O SH3). apply (agree_of_munch _ _ _ _ MU). intros x Hx. cbn [outside]. clear - Hx SHO FSELF SHT LOW LOQ FLO FHI. split; [lia| split; [lia| exact I]].
  - intros a Ha Ho. cbn [outside] in Ho. rewrite <- (PRES03 a Ha ltac:(lia)). apply MU. cbn [outside]. split; [destruct (CSEP _ Ha); lia|]. split; [lia| exact I].
Qed.

Lemma sb_ctorA : forall (Σ : rts RT) (K : config -> Prop) (lo O q fO : Z) (kO : nat) (junk : list byte)
    (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  In (fO, kO) (rt_frames RT Σ) -> oss_inA fO kO O -> rt_sp0 RT Σ - STACK_WIN <= lo -> 0x7fff7f800000 <= lo ->
  rw_cells bsegs m (O + 8) [CB 104 junk] -> OSHADOWA m O -> LOCBA m ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo q -> lo + 240 + RT_STACK <= q -> q + 16 <= USTACK_TOP -> q mod 16 = 0 ->
  (forall t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m' j108,
     ART RT Σ m' -> mem_inv bsegs m' -> stk bsegs m' lo q ->
     rw_cells bsegs m' (O + 8) (sb_cellsA (ossA0 O)) -> rw_cells bsegs m' (O + 96) [C8 (wz (O + 73))] ->
     rw_cells bsegs m' (O + 72) [C1 (Z_to_bv 8 44); CB 23 (repeat z8 23)] -> rw_cells bsegs m' (O + 104) [CB 4 mode16; CB 4 j108] -> OSHADOWA m' O -> LOCBA m' ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(O + 8, O + 112)] m m' ->
     aevt RT PMc Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt RT PMc Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz (O + 8)) (wz 16) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz OSS_SB_CTOR_A) fc None m (seg_rom bsegs)).
Proof using AF RC FDO MST ROWS.
  intros until m. intros INF OIN LOW LOR OSR SH LB ART0 MI ST LOQ QT Q16 HK.
  pose proof OIN as (FLO & FHI & AL16).
  unfold OSS_SB_CTOR_A, PJ_LOC_STACK_A, RT_STACK in *.
  pose proof (af_frames_range RT AF Σ m fO kO ART0 INF) as (F0 & FTOP & FSEG & FLIVE).
  pose proof (af_frames_align RT AF Σ m fO kO ART0 INF) as (_ & FSG).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof (proj2 (af_fshadow_apart RT AF Σ m fO kO ART0 INF) fO kO INF) as FSELF.
  pose proof (fframe_ranges RT AF Σ m fO kO ART0 INF) as (_ & _ & _ & _ & SHT).
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in G1, G2, G3, G4.
  pose proof (ROWS Σ m ART0) as (V1 & _). unfold OSS_GOT_VT_A, OSS_VTT_A, OSS_SB_VPTR_A, OSS_SBB_VPTR_A, OSS_VBOFF_A in V1.
  replace (0x17d740 - 16) with 0x17d730 in V1 by reflexivity. replace (0x17d500 - 16) with 0x17d4f0 in V1 by reflexivity.
  remember (fs_size kO) as FSZ eqn:EFSZ.
  assert (Q0 : 0 <= q - 256) by (destruct ST; ul).
  assert (UQ80 : bv_unsigned (wz (q + -64)) = q + -64) by (apply unsigned_lit; ul).
  assert (SHO : shad fO <= shad O /\ shad O + 33 <= shad (fO + FSZ)) by (unfold shad; clear - FLO FHI AL16; Z.div_mod_to_equations; lia).
  assert (CLF : forall Lx sp x, fO <= x < fO + FSZ - 8 -> aclient Lx (rt_frames RT Σ) sp x).
  { intros Lx sp x Hx. right; right; right; left. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia]. }
  assert (CLS : forall Lx sp x, shad fO <= x < shad (fO + FSZ) -> aclient Lx (rt_frames RT Σ) sp x).
  { intros Lx sp x Hx. right; right; right; right. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia]. }
  assert (CSEP : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) q a -> q <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split_c RT AF Σ m q a ART0 Ha) as [H|H]; [left; exact H| right; lia]. }
  assert (SHZ0 : forall mx, OSHADOWA mx O -> shz mx O 264).
  { intros mx HB. change 264 with (8 * Z.of_nat 33). apply (shz_of_zero_run mx O 33); [clear - AL16; Z.div_mod_to_equations; lia| lia| exact HB]. }
  unfold SHB in G2. unfold SEGTOP_A, STACK_WIN, USTACK_TOP in FTOP, SP0R, QT, LOW, SHT, FSG.
  assert (SHZ : forall m', munch [(q - 112, q); (O + 8, O + 112)] m m' -> wmono bsegs m m' -> shz m' O 264).
  { intros m' MU' _. apply SHZ0. apply (OSHADOWA_agree m m' O SH). apply (agree_of_munch _ _ _ _ MU'). intros x Hx. cbn [outside].
    clear - Hx SHO FSELF SHT LOW LOQ FLO FHI. split; [lia| split; [lia| exact I]]. }
  apply (rw_cells_split_CB bsegs _ _ [] 104 junk [] [8; 8; 48; 24; 8; 4; 4]%nat) in OSR; [|reflexivity]. cbn [mk_CB_cells app] in OSR. forget_junk OSR.
  apply (aevt_evt RT AF PMc MST).
  pose proof (munch_refl [(q - 112, q); (O + 8, O + 112)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  lstep. carve_frame 64%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 64 _ [] [8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR. forget_junk FR.

  do 8 lstep. lstep. lstep. lstep. lstep.
  chk SHZ (O + 8).

  lstep. lstep. lstep. lstep. lstep. lstep. lstep. lstep.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => tryif constr_eq mx m1 then idtac else (try rename m1 into m1o; rename mx into m1) end.
  lazymatch goal with H : stk bsegs m1 _ _ |- _ => rename H into ST1 end.
  takeZ OSR 1%nat (O + 16) VP. takeZ OSR 1%nat (O + 24) LOCC.
  assert (LOCB1 : LOCBA m1).
  { apply (LOCBA_agree m m1 LB). apply (agree_of_munch _ _ _ _ MU). intros x Hx. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx. cbn [outside]. clear - Hx FSG FLO LOR LOQ. split; [lia| split; [lia| exact I]]. }
  assert (MI1 : mem_inv bsegs m1) by assumption.
  eapply evt_cut.
  { eapply (locale_ctor_specB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fc m1 lo (O + 16) _); rewrite ?UQ80;
      [exact ST1| lia| lia| exact LOCB1| exact LOCC| lia| lia| left; lia| clear - FSEG FLO FHI; unfold SEGTOP_A in FSEG; lia| exact MI1]. }
  cbv beta. intros ms1 (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & ST2 & IMP2 & LOCB2).
  rewrite ?UQ80 in MU2. rewrite ?UQ80 in ST2. rewrite (ret_pc_even 0xbf96c) by lia.
  change (rw_cells bsegs m2 (O + 16) [C8 (Z_to_bv 64 PJ_LOC_IMP_A)]) in IMP2.
  assert (AG2 : forall Q : Z -> Prop, (forall x, Q x -> ~ (q + -64 - 32 <= x < q + -64) /\ ~ (O + 16 <= x < O + 16 + 8)) -> agree_on Q m1 m2).
  { intros Q HP a Ha. apply MU2. cbn [outside]. destruct (HP _ Ha) as [X Y]. split; [exact X| split; [exact Y| exact I]]. }
  lazymatch type of FR with rw_cells _ _ _ ?cs => assert (FR2 : rw_cells bsegs m2 (q + -64) cs)
    by (eapply rw_cells_agree_nw; [exact FR|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; lia) end.
  lazymatch type of VP with rw_cells _ _ _ ?cs => assert (VP2 : rw_cells bsegs m2 (O + 8) cs)
    by (eapply rw_cells_agree_nw; [exact VP|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [clear - Hx FHI FTOP LOW LOQ; lia| lia]) end.
  lazymatch type of OSR with rw_cells _ _ _ ?cs => assert (OSR2 : rw_cells bsegs m2 (O + 24) cs)
    by (eapply rw_cells_agree_nw; [exact OSR|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [clear - Hx FHI FTOP LOW LOQ; lia| lia]) end.
  assert (SH2 : OSHADOWA m2 O).
  { apply (OSHADOWA_agree m1 m2 O); [apply (OSHADOWA_agree m m1 O SH); apply (agree_of_munch _ _ _ _ MU)| apply AG2]; intros x Hx; cbn [outside];
      clear - Hx SHO FSELF SHT LOW LOQ FLO FHI; [split; [lia| split; [lia| exact I]]| split; lia]. }

  assert (MU' : munch [(q - 112, q); (O + 8, O + 112)] m m2).
  { apply (munch_trans _ m m1 m2 MU). eapply munch_weaken; [| exact MU2]. intros x Hx. cbn [outside] in Hx |- *. lia. }
  pose proof (wmono_trans bsegs m m1 m2 WM WM2) as WM'.
  clear MU WM MU2 WM2 AG2 FR VP OSR LOCC LOCB1 ST1 MI1. rename MU' into MU. rename WM' into WM.

  lstep. lstep. lstep. lstep.
  apply evt_done.
  assert (ART2 : ART RT Σ m2).
  { apply (art_client_write RT AF Σ m m2 (q - 112) ART0 ltac:(ul)); [| exact WM]. intros a Ha. apply MU. cbn [outside].
    split; [intros Hin; apply Ha; left; ul|]. split; [intros Hin; apply Ha; apply CLF; lia| exact I]. }
  assert (PRES02 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> ~ (O + 8 <= bv_unsigned a < O + 112) -> m2 a = m a).
  { intros a Ha Ho. apply MU. cbn [outside]. split; [destruct (CSEP _ Ha); lia|]. split; [exact Ho| exact I]. }
  assert (SHZ2 : forall m', munch [(q - 64, q); (O + 8, O + 112)] m2 m' -> wmono bsegs m2 m' -> shz m' O 264).
  { intros m' MU' _. apply SHZ0. apply (OSHADOWA_agree m2 m' O SH2). apply (agree_of_munch _ _ _ _ MU'). intros x Hx. cbn [outside].
    clear - Hx SHO FSELF SHT LOW LOQ FLO FHI. split; [lia| split; [lia| exact I]]. }
  pose proof (ROWS Σ m2 ART2) as (V1' & _). unfold OSS_GOT_VT_A, OSS_VTT_A, OSS_SB_VPTR_A, OSS_SBB_VPTR_A, OSS_VBOFF_A in V1'.
  replace (0x17d740 - 16) with 0x17d730 in V1' by reflexivity. replace (0x17d500 - 16) with 0x17d4f0 in V1' by reflexivity. clear V1. rename V1' into V1.
  pose proof (af_client_consts RT AF Σ m2 ART2) as (G1' & G2' & _). unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SHB in G1', G2'.
  clear MU WM MI ART0 SH. try clear G1 G2.
  takeZ OSR2 1%nat (O + 72) OC2. rename OSR2 into Z48.

  assert (ACCO : forall mx, OSHADOWA mx O -> acc bsegs mx O 264).
  { intros mx HB. change 264 with (8 * Z.of_nat 33). apply (acc_zero_run bsegs mx O 33); [clear - AL16; Z.div_mod_to_equations; lia| lia| exact HB]. }
  assert (COK2 : forall mx, stk bsegs mx lo (q + -64) -> call_ok RT Σ mx (Z_to_bv 64 (q + -64)) lo).
  { intros mx STx. unfold call_ok. rewrite UQ80. split; [exact STx|]. split; [unfold STACK_WIN; exact LOW|]. split; [ul|]. split; [ul| clear - Q16; Z.div_mod_to_equations; lia]. }
  assert (CD1 : checked_dst RT Σ m2 (Z_to_bv 64 (q + -64)) (O + 24) 48).
  { unfold checked_dst. rewrite UQ80. split; [| split].
    - intros _. split; [apply (acc_sub bsegs m2 O 264); [exact (ACCO m2 SH2)| lia| lia]|]. right; left. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia].
    - intros i Hi. apply CLF. lia.
    - apply (rw_cells_wr_at bsegs m2 _ _ 48 OC2). cbn. lia. }
  eapply (aevt_memsetP RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 (O + 24) 48 (Z_to_bv 8 0) lo eq_refl eq_refl eq_refl ltac:(ul) ltac:(lia) CD1 ART2 MI2 (COK2 m2 ST2)).
  intros w0 w1 w2 c1 c2 c3 c4 c5 c6 c7 w3 w4 w5 w6 F2 m3 (ART3 & MI3 & WM3 & ST3) PRES3 BY3. rewrite UQ80 in ST3, PRES3.
  rewrite (ret_pc_even 0xbf97c) by lia.
  assert (AG3 : forall Q : Z -> Prop, (forall x, Q x -> ((q + -64 <= x < q) \/ (fO <= x < fO + FSZ - 8) \/ (shad fO <= x < shad (fO + FSZ))) /\ ~ (O + 24 <= x < O + 24 + 48)) -> agree_on Q m2 m3).
  { intros Q HP a Ha. destruct (HP _ Ha) as [HX HN]. apply PRES3; [| exact HN]. destruct HX as [H|[H|H]]; [left; ul| apply CLF; exact H| apply CLS; exact H]. }
  lazymatch type of FR2 with rw_cells _ _ _ ?cs => assert (FR3 : rw_cells bsegs m3 (q + -64) cs)
    by (eapply rw_cells_agree_nw; [exact FR2|]; apply AG3; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [left; lia| clear - Hx FLO FHI FTOP LOW LOQ; lia]) end.
  assert (VP3 : rw_cells bsegs m3 (O + 8) [C8 (Z_to_bv 64 1561856)]) by (eapply rw_cells_agree_nw; [exact VP2|]; apply AG3; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [right; left; lia| lia]).
  assert (IMP3 : rw_cells bsegs m3 (O + 16) [C8 (Z_to_bv 64 PJ_LOC_IMP_A)]) by (eapply rw_cells_agree_nw; [exact IMP2|]; apply AG3; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [right; left; lia| lia]).
  lazymatch type of Z48 with rw_cells _ _ _ ?cs => assert (Z483 : rw_cells bsegs m3 (O + 72) cs)
    by (eapply rw_cells_agree_nw; [exact Z48|]; apply AG3; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [right; left; lia| lia]) end.
  assert (SH3 : OSHADOWA m3 O) by (apply (OSHADOWA_agree m2 m3 O SH2); apply AG3; intros x Hx; clear - Hx SHO FSELF FLO FHI; split; [do 2 right; lia| lia]).
  assert (Z24 : rw_cells bsegs m3 (O + 24) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)]).
  { pose proof (rw_cells_CB_intro m3 (O + 24) _ BY3) as X. rewrite repeat_length in X. cbn [Z.to_nat Pos.to_nat] in X.
    specialize (X ltac:(apply (wr_at_transport bsegs m2 m3 (O + 24) 48); [apply (rw_cells_wr_at bsegs m2 _ _ 48 OC2); cbn; lia| exact WM3])).
    retype X [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)]. exact X. }
  assert (PRES23 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> ~ (O + 8 <= bv_unsigned a < O + 112) -> m3 a = m2 a).
  { intros a Ha Ho. apply PRES3; [apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| intros e He; exact He| lia]| lia]. }
  assert (SHZ3 : forall m', munch [(q - 64, q); (O + 8, O + 112)] m3 m' -> wmono bsegs m3 m' -> shz m' O 264).
  { intros m' MU' _. apply SHZ0. apply (OSHADOWA_agree m3 m' O SH3). apply (agree_of_munch _ _ _ _ MU'). intros x Hx. cbn [outside].
    clear - Hx SHO FSELF SHT LOW LOQ FLO FHI. split; [lia| split; [lia| exact I]]. }
  pose proof (ROWS Σ m3 ART3) as (V1' & _). unfold OSS_GOT_VT_A, OSS_VTT_A, OSS_SB_VPTR_A, OSS_SBB_VPTR_A, OSS_VBOFF_A in V1'.
  replace (0x17d740 - 16) with 0x17d730 in V1' by reflexivity. replace (0x17d500 - 16) with 0x17d4f0 in V1' by reflexivity. clear V1. rename V1' into V1.
  pose proof (af_client_consts RT AF Σ m3 ART3) as (G1'' & G2'' & _). unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SHB in G1'', G2''. clear G1' G2'.
  clear AG3 PRES3 BY3 FR2 VP2 IMP2 Z48 OC2 SH2 CD1 ART2 MI2 ST2 SHZ2 WM3.

  apply (aevt_evt RT AF PMc MST).
  pose proof (munch_refl [(q - 64, q); (O + 8, O + 112)]%Z m3) as MU. pose proof (wmono_refl bsegs m3) as WM.
  chk2 SHZ3 (O + 8).
  lstep. lstep. lstep. lstep. lstep. lstep. lstep. lstep. lstep.
  apply evt_done.
  lazymatch goal with |- aevt _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.

  assert (ART4 : ART RT Σ m4).
  { apply (art_client_write RT AF Σ m3 m4 (q - 64) ART3 ltac:(ul)); [| exact WM]. intros a Ha. apply MU. cbn [outside].
    split; [intros Hin; apply Ha; left; ul|]. split; [intros Hin; apply Ha; apply CLF; lia| exact I]. }
  assert (AG4 : forall Q : Z -> Prop, (forall x, Q x -> ~ (q - 64 <= x < q) /\ ~ (O + 8 <= x < O + 112)) -> agree_on Q m3 m4).
  { intros Q HP a Ha. apply MU. cbn [outside]. destruct (HP _ Ha) as [X Y]. split; [exact X| split; [exact Y| exact I]]. }
  assert (SH4 : OSHADOWA m4 O) by (apply (OSHADOWA_agree m3 m4 O SH3); apply AG4; intros x Hx; clear - Hx SHO FSELF SHT LOW LOQ FLO FHI; split; lia).
  assert (PRES24 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> ~ (O + 8 <= bv_unsigned a < O + 112) -> m4 a = m2 a).
  { intros a Ha Ho. rewrite <- (PRES23 a Ha Ho). apply MU. cbn [outside]. split; [destruct (CSEP _ Ha); lia|]. split; [exact Ho| exact I]. }
  lazymatch goal with H : rw_cells bsegs m4 (O + 72) _ |- _ => rename H into Z484 end.
  lazymatch goal with H : rw_cells bsegs m4 (O + 8) _ |- _ => rename H into VP4 end.
  lazymatch goal with H : rw_cells bsegs m4 (O + 16) _ |- _ => rename H into IMP4 end.
  lazymatch goal with H : rw_cells bsegs m4 (O + 24) _ |- _ => rename H into Z244 end.
  lazymatch goal with H : rw_cells bsegs m4 (q + -64) _ |- _ => rename H into FR4 end.
  lazymatch goal with H : stk bsegs m4 _ _ |- _ => rename H into ST4 end.
  clear MU WM.
  assert (CD2 : checked_dst RT Σ m4 (Z_to_bv 64 (q + -64)) (O + 72) 24).
  { unfold checked_dst. rewrite UQ80. split; [| split].
    - intros _. split; [apply (acc_sub bsegs m4 O 264); [exact (ACCO m4 SH4)| lia| lia]|]. right; left. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia].
    - intros i Hi. apply CLF. lia.
    - apply (rw_cells_wr_at bsegs m4 _ _ 24 Z484). cbn. lia. }
  eapply (aevt_memsetP RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc m4 (O + 72) 24 (Z_to_bv 8 0) lo eq_refl eq_refl eq_refl ltac:(ul) ltac:(lia) CD2 ART4 ltac:(assumption) (COK2 m4 ST4)).
  intros x0 x1 x2 d1 d2 d3 d4 d5 d6 d7 x3 x4 x5 x6 F3 m5 (ART5 & MI5 & WM5 & ST5) PRES5 BY5. rewrite UQ80 in ST5, PRES5.
  rewrite (ret_pc_even 0xbf9a8) by lia.
  assert (AG5 : forall Q : Z -> Prop, (forall x, Q x -> ((q + -64 <= x < q) \/ (fO <= x < fO + FSZ - 8) \/ (shad fO <= x < shad (fO + FSZ))) /\ ~ (O + 72 <= x < O + 72 + 24)) -> agree_on Q m4 m5).
  { intros Q HP a Ha. destruct (HP _ Ha) as [HX HN]. apply PRES5; [| exact HN]. destruct HX as [H|[H|H]]; [left; ul| apply CLF; exact H| apply CLS; exact H]. }
  lazymatch type of FR4 with rw_cells _ _ _ ?cs => assert (FR5 : rw_cells bsegs m5 (q + -64) cs)
    by (eapply rw_cells_agree_nw; [exact FR4|]; apply AG5; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [left; lia| clear - Hx FLO FHI FTOP LOW LOQ; lia]) end.
  lazymatch type of VP4 with rw_cells _ _ _ ?cs => assert (VP5 : rw_cells bsegs m5 (O + 8) cs)
    by (eapply rw_cells_agree_nw; [exact VP4|]; apply AG5; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [right; left; lia| lia]) end.
  assert (IMP5 : rw_cells bsegs m5 (O + 16) [C8 (Z_to_bv 64 PJ_LOC_IMP_A)]) by (eapply rw_cells_agree_nw; [exact IMP4|]; apply AG5; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [right; left; lia| lia]).
  lazymatch type of Z244 with rw_cells _ _ _ ?cs => assert (Z245 : rw_cells bsegs m5 (O + 24) cs)
    by (eapply rw_cells_agree_nw; [exact Z244|]; apply AG5; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [right; left; lia| lia]) end.
  takeZ Z484 1%nat (O + 96) ZJ.
  lazymatch type of Z484 with rw_cells _ _ _ ?cs => assert (MODE5 : rw_cells bsegs m5 (O + 96) cs)
    by (eapply rw_cells_agree_nw; [exact Z484|]; apply AG5; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [right; left; lia| lia]) end.
  assert (SH5 : OSHADOWA m5 O) by (apply (OSHADOWA_agree m4 m5 O SH4); apply AG5; intros x Hx; clear - Hx SHO FSELF FLO FHI; split; [do 2 right; lia| lia]).
  assert (Z72 : rw_cells bsegs m5 (O + 72) [C8 (wz 0); C8 (wz 0); C8 (wz 0)]).
  { pose proof (rw_cells_CB_intro m5 (O + 72) _ BY5) as X. rewrite repeat_length in X. cbn [Z.to_nat Pos.to_nat] in X.
    specialize (X ltac:(apply (wr_at_transport bsegs m4 m5 (O + 72) 24); [apply (rw_cells_wr_at bsegs m4 _ _ 24 ZJ); cbn; lia| exact WM5])).
    retype X [C8 (wz 0); C8 (wz 0); C8 (wz 0)]. exact X. }
  rename Z72 into REP5.
  assert (PRES25 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> ~ (O + 8 <= bv_unsigned a < O + 112) -> m5 a = m2 a).
  { intros a Ha Ho. rewrite <- (PRES24 a Ha Ho). apply PRES5; [apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| intros e He; exact He| lia]| lia]. }
  assert (SHZ5 : forall m', munch [(q - 64, q); (O + 8, O + 112)] m5 m' -> wmono bsegs m5 m' -> shz m' O 264).
  { intros m' MU' _. apply SHZ0. apply (OSHADOWA_agree m5 m' O SH5). apply (agree_of_munch _ _ _ _ MU'). intros x Hx. cbn [outside].
    clear - Hx SHO FSELF SHT LOW LOQ FLO FHI. split; [lia| split; [lia| exact I]]. }
  pose proof (af_client_consts RT AF Σ m5 ART5) as (G1' & G2' & _). unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SHB in G1', G2'. clear G1'' G2''.
  clear AG5 AG4 PRES5 BY5 FR4 VP4 IMP4 Z244 ZJ Z484 SH4 SH3 PRES24 PRES23 CD2 ART3 ART4 SHZ3 WM5 V1. try clear MI3. try clear ST3. try clear ST4.

  apply (aevt_evt RT AF PMc MST).
  pose proof (munch_refl [(q - 64, q); (O + 8, O + 112)]%Z m5) as MU. pose proof (wmono_refl bsegs m5) as WM.
  lstep. chk SHZ5 (O + 96). lstep. lstep. chk SHZ5 (O + 104). lstep. lstep. lstep.
  apply evt_done.
  lazymatch goal with |- aevt _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
  try clear LOCC.
  lazymatch goal with H : rw_cells bsegs m6 (O + 96) _ |- _ => rename H into MODE6 end.
  takeZ MODE6 1%nat (O + 104) HMC6.
  lazymatch goal with H : rw_cells bsegs m6 (O + 72) _ |- _ => rename H into REP6 end.
  lazymatch goal with H : rw_cells bsegs m6 (O + 24) _ |- _ => rename H into Z246 end.
  lazymatch goal with H : rw_cells bsegs m6 (O + 16) _ |- _ => rename H into IMP6 end.
  lazymatch goal with H : rw_cells bsegs m6 (O + 8) _ |- _ => rename H into VP6 end.
  lazymatch goal with H : rw_cells bsegs m6 (q + -64) _ |- _ => rename H into FR6 end.
  lazymatch goal with H : stk bsegs m6 _ _ |- _ => rename H into ST6 end.
  assert (ART6 : ART RT Σ m6).
  { apply (art_client_write RT AF Σ m5 m6 (q - 64) ART5 ltac:(ul)); [| exact WM]. intros a Ha. apply MU. cbn [outside].
    split; [intros Hin; apply Ha; left; ul|]. split; [intros Hin; apply Ha; apply CLF; lia| exact I]. }
  assert (AG6 : forall Q : Z -> Prop, (forall x, Q x -> ~ (q - 64 <= x < q) /\ ~ (O + 8 <= x < O + 112)) -> agree_on Q m5 m6).
  { intros Q HP a Ha. apply MU. cbn [outside]. destruct (HP _ Ha) as [X Y]. split; [exact X| split; [exact Y| exact I]]. }
  assert (SH6 : OSHADOWA m6 O) by (apply (OSHADOWA_agree m5 m6 O SH5); apply AG6; intros x Hx; clear - Hx SHO FSELF SHT LOW LOQ FLO FHI; split; lia).
  assert (PRES26 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> ~ (O + 8 <= bv_unsigned a < O + 112) -> m6 a = m2 a).
  { intros a Ha Ho. rewrite <- (PRES25 a Ha Ho). apply MU. cbn [outside]. split; [destruct (CSEP _ Ha); lia|]. split; [exact Ho| exact I]. }
  retype_at MODE6 0%nat 1%nat [CB 4 mode16].
  pose proof (rw_cells_joinA _ _ _ _ _ VP6 IMP6 ltac:(cbn [cells_size csize]; lia)) as SB1. cbn [app] in SB1.
  pose proof (rw_cells_joinA _ _ _ _ _ SB1 Z246 ltac:(cbn [cells_size csize Nat.add]; lia)) as SBC6. cbn [app] in SBC6. clear SB1 VP6 IMP6 Z246.
  clear MU WM.
  lazymatch type of MODE6 with rw_cells _ _ _ [_; CB 4 ?j] =>
  eapply (init_bufA Σ K lo O (q + -64) fO kO j _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fc m6 INF OIN ltac:(unfold STACK_WIN; exact LOW) LOR);
    [unfold OSS_SB_VPTR_A, OSS_CLASSIC_A; exact SBC6| exact REP6| exact HMC6| exact MODE6| exact SH6| exact ART6| assumption| exact ST6
    | unfold RT_STACK; lia| unfold USTACK_TOP; lia| clear - Q16; Z.div_mod_to_equations; lia|] end.
  intros y0 y1 y2 e0 e1 e2 e3 e4 e5 e6 e7 y3 y4 y5 y6 F7 m7 ART7 MI7 ST7 SBC7 HMC7 R44 MODE7 SH7 PRES7.
  rewrite (ret_pc_even 0xbf9e0) by lia.
  assert (AG7 : forall Q : Z -> Prop, (forall x, Q x -> ((q + -64 <= x < q) \/ (fO <= x < fO + FSZ - 8) \/ (shad fO <= x < shad (fO + FSZ))) /\ ~ (O + 48 <= x < O + 104)) -> agree_on Q m6 m7).
  { intros Q HP a Ha. destruct (HP _ Ha) as [HX HN]. apply PRES7; [| cbn [outside]; split; [clear - HN; lia| exact I]]. destruct HX as [H|[H|H]]; [left; ul| apply CLF; exact H| apply CLS; exact H]. }
  lazymatch type of FR6 with rw_cells _ _ _ ?cs => assert (FR7 : rw_cells bsegs m7 (q + -64) cs)
    by (eapply rw_cells_agree_nw; [exact FR6|]; apply AG7; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [left; lia| clear - Hx FLO FHI FTOP LOW LOQ; lia]) end.
  assert (PRES27 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> ~ (O + 8 <= bv_unsigned a < O + 112) -> m7 a = m2 a).
  { intros a Ha Ho. rewrite <- (PRES26 a Ha Ho). apply PRES7; [apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| intros e He; exact He| lia]| cbn [outside]; split; [lia| exact I]]. }
  assert (LOCB7 : LOCBA m7).
  { apply (LOCBA_agree m2 m7 LOCB2). intros a Ha. apply PRES27; [right; left; apply client_static_intro; unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Ha; lia| unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Ha; lia]. }
  clear AG7 PRES7 FR6 AG6 SH6 PRES26 PRES25 SH5 SHZ5 MODE6 HMC6 REP6 SBC6 ART5 ART6. try clear MI5. try clear ST5. try clear ST6. try clear MI6.

  apply (aevt_evt RT AF PMc MST).
  pose proof (munch_refl [(q - 64, q); (O + 8, O + 112)]%Z m7) as MU. pose proof (wmono_refl bsegs m7) as WM.
  do 8 lstep. lstep. release_frame FR7 ST7 q. lstep.
  apply evt_done. eapply HK; [exact ART7| assumption| assumption| exact SBC7| exact HMC7| exact R44| exact MODE7| exact SH7| exact LOCB7|].
  intros a Ha Ho. cbn [outside] in Ho. rewrite <- (PRES02 a Ha ltac:(lia)). exact (PRES27 a Ha ltac:(lia)).
Qed.

Theorem oss_ctorA_proof : oss_ctorA_cps RT PMc.
Proof using AF RC FDO MST ROWS.
  unfold oss_ctorA_cps. intros until m. intros _ _ INF OIN LOW LOR OSR SH LB HLEN ART0 MI ST LOQ QT Q16 HK.
  pose proof OIN as (FLO & FHI & AL16).
  unfold OSS_CTOR_A, OSS_CTOR_STACK_A, PJ_LOC_STACK_A, RT_STACK in *.
  pose proof (af_frames_range RT AF Σ m fO kO ART0 INF) as (F0 & FTOP & FSEG & FLIVE).
  pose proof (af_frames_align RT AF Σ m fO kO ART0 INF) as (_ & FSG).
  pose proof (af_frames_hi RT AF Σ m fO kO ART0 INF) as FRHI.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof (proj2 (af_fshadow_apart RT AF Σ m fO kO ART0 INF) fO kO INF) as FSELF.
  pose proof (fframe_ranges RT AF Σ m fO kO ART0 INF) as (_ & _ & _ & _ & SHT).
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in G1, G2, G3, G4.
  pose proof (ROWS Σ m ART0) as (V1 & V2 & _).
  unfold OSS_GOT_VT_A, OSS_VTT_A, OSS_SB_VPTR_A, OSS_SBB_VPTR_A, OSS_VBOFF_A, OSS_OS_VPTR_A, OSS_OS_CVPTR_A, OSS_IOS_CVPTR_A, OSS_IOS_VPTR_A in V1, V2.
  replace (0x17d740 - 16) with 0x17d730 in V1 by reflexivity. replace (0x17d500 - 16) with 0x17d4f0 in V1 by reflexivity.
  remember (fs_size kO) as FSZ eqn:EFSZ.
  assert (Q0 : 0 <= q - 400) by (destruct ST; ul).
  assert (UQ96 : bv_unsigned (wz (q + -96)) = q + -96) by (apply unsigned_lit; ul).
  assert (UQ112 : bv_unsigned (wz (q + -112)) = q + -112) by (apply unsigned_lit; ul).
  assert (SHO : shad fO <= shad O /\ shad O + 33 <= shad (fO + FSZ)) by (unfold shad; clear - FLO FHI AL16; Z.div_mod_to_equations; lia).
  assert (CLF : forall Lx sp x, fO <= x < fO + FSZ - 8 -> aclient Lx (rt_frames RT Σ) sp x).
  { intros Lx sp x Hx. right; right; right; left. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia]. }
  assert (CLS : forall Lx sp x, shad fO <= x < shad (fO + FSZ) -> aclient Lx (rt_frames RT Σ) sp x).
  { intros Lx sp x Hx. right; right; right; right. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia]. }
  assert (CSEP : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) q a -> q <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split_c RT AF Σ m q a ART0 Ha) as [H|H]; [left; exact H| right; lia]. }
  assert (SHZ0 : forall mx, OSHADOWA mx O -> shz mx O 264).
  { intros mx HB. change 264 with (8 * Z.of_nat 33). apply (shz_of_zero_run mx O 33); [clear - AL16; Z.div_mod_to_equations; lia| lia| exact HB]. }
  assert (ACCO : forall mx, OSHADOWA mx O -> acc bsegs mx O 264).
  { intros mx HB. change 264 with (8 * Z.of_nat 33). apply (acc_zero_run bsegs mx O 33); [clear - AL16; Z.div_mod_to_equations; lia| lia| exact HB]. }

  pose proof (acc_lit RT AF Σ m 0x17d908 40 ART0 ltac:(unfold ACC_LITS; repeat (first [left; reflexivity | right]))) as ACV.
  unfold SHB in G2. unfold SEGTOP_A, STACK_WIN, USTACK_TOP in FTOP, SP0R, QT, LOW, SHT, FSG, FSEG.
  assert (VSEP : forall x, shad 0x17d908 <= x <= shad (0x17d908 + 40) -> ~ (q - 128 <= x < q) /\ ~ (O <= x < O + 264)).
  { intros x Hx. change (2147646241 <= x <= 2147646246) in Hx. clear - Hx FRHI FLO FHI LOR LOQ. split; lia. }
  assert (SHZ : forall m', munch [(q - 112, q); (O, O + 264)] m m' -> wmono bsegs m m' -> shz m' O 264).
  { intros m' MU' _. apply SHZ0. apply (OSHADOWA_agree m m' O SH). apply (agree_of_munch _ _ _ _ MU'). intros x Hx. cbn [outside].
    clear - Hx SHO FSELF SHT LOW LOQ FLO FHI. split; [lia| split; [lia| exact I]]. }
  assert (SHZV : forall m', munch [(q - 112, q); (O, O + 264)] m m' -> wmono bsegs m m' -> shz m' 0x17d908 40).
  { intros m' MU' _. apply (shz_of_acc m' 0x17d908 40); [| reflexivity| lia]. apply (acc_agree_at m m' 0x17d908 40 ACV ltac:(lia)).
    apply (agree_of_munch _ _ _ _ MU'). intros x Hx. cbn [outside]. destruct (VSEP x Hx) as [X Y]. split; [clear - X; lia| split; [exact Y| exact I]]. }
  apply (rw_cells_split_CB bsegs _ _ [] 264 junk [] [8; 104; 8; 4; 4; 8; 8; 4; 4; 8; 8; 80; 8; 1; 1; 1; 1; 4]%nat) in OSR; [|reflexivity].
  cbn [mk_CB_cells app] in OSR. forget_junk OSR.
  apply (aevt_evt RT AF PMc MST).
  pose proof (munch_refl [(q - 112, q); (O, O + 264)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  lstep. carve_frame 96%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 96 _ [] [8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR. forget_junk FR.

  do 11 lstep. lstep. lstep. lstep. lstep. lstep.

  chk SHZ (O + 160). lstep. chk SHZ O.

  lstep. lstep. lstep. lstep. rewrite ?shr3_div. lstep. lstep. lstep. chk2 SHZ (O + 112).

  lstep. lstep. lstep. lstep. lstep. chkV SHZV 1562896.

  lstep. lstep. lstep. rewrite ?shr3_div. lstep. lstep. chkV2 SHZV 1562904.

  lstep. chkV SHZV 1562920. lstep. lstep. chk SHZ (O + 112). lstep. lstep.

  lstep. lstep. chkV SHZV 1562920. lstep. lstep. lstep. lstep. lstep. lstep.

  lstep. carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8;8]%nat) in FR0; [|reflexivity]. cbn [mk_CB_cells app] in FR0. forget_junk FR0.
  do 17 lstep. lstep.
  replace (O + 8 <? 1) with false in OSR by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z] in OSR.
  apply evt_done.
  lazymatch goal with |- aevt _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
  rename OSR into OSR5. rename FR into FR5. rename FR0 into FRI5. lazymatch goal with H : stk bsegs m5 _ _ |- _ => rename H into ST5 end.
  assert (ART5 : ART RT Σ m5).
  { apply (art_client_write RT AF Σ m m5 (q - 112) ART0 ltac:(ul)); [| exact WM]. intros a Ha. apply MU. cbn [outside].
    split; [intros Hin; apply Ha; left; ul|]. split; [intros Hin; apply Ha; apply CLF; lia| exact I]. }
  assert (AG05 : forall Q : Z -> Prop, (forall x, Q x -> ~ (q - 112 <= x < q) /\ ~ (O <= x < O + 264)) -> agree_on Q m m5).
  { intros Q HP a Ha. apply MU. cbn [outside]. destruct (HP _ Ha) as [X Y]. split; [exact X| split; [exact Y| exact I]]. }
  assert (SH5 : OSHADOWA m5 O) by (apply (OSHADOWA_agree m m5 O SH); apply AG05; intros x Hx; clear - Hx SHO FSELF SHT LOW LOQ FLO FHI; split; lia).
  assert (LB5 : LOCBA m5) by (apply (LOCBA_agree m m5 LB); apply AG05; intros x Hx; unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx; clear - Hx FSG FLO LOR LOQ; lia).
  assert (PRES05 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> ~ (O <= bv_unsigned a < O + 264) -> m5 a = m a).
  { intros a Ha Ho. apply MU. cbn [outside]. split; [destruct (CSEP _ Ha); lia|]. split; [exact Ho| exact I]. }
  takeZ OSR5 11%nat (O + 168) P0. takeZ OSR5 1%nat (O + 248) Z80.

  clear MU WM.
  assert (COKI : forall mx, stk bsegs mx lo (q + -112) -> call_ok RT Σ mx (Z_to_bv 64 (q + -112)) lo).
  { intros mx STx. unfold call_ok. rewrite UQ112. split; [exact STx|]. split; [unfold STACK_WIN; exact LOW|]. split; [ul|]. split; [ul| clear - Q16; Z.div_mod_to_equations; lia]. }
  assert (CD5 : checked_dst RT Σ m5 (Z_to_bv 64 (q + -112)) (O + 168) 80).
  { unfold checked_dst. rewrite UQ112. split; [| split].
    - intros _. split; [apply (acc_sub bsegs m5 O 264); [exact (ACCO m5 SH5)| lia| lia]|]. right; left. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia].
    - intros i Hi. apply CLF. lia.
    - apply (rw_cells_wr_at bsegs m5 _ _ 80 Z80). cbn. lia. }
  eapply (aevt_memsetS RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m5 (O + 168) 80 (Z_to_bv 8 0) lo
            eq_refl eq_refl eq_refl ltac:(ul) ltac:(lia) CD5 ART5 ltac:(assumption) (COKI m5 ST5)).
  intros x0 x1 x2 d1 d2 d3 d4 d5 d6 d7 x3 x4 x5 x6 F6 m6 (ART6 & MI6 & WM6 & ST6) PRES6 BY6. rewrite UQ112 in ST6, PRES6.
  rewrite (ret_pc_even 0x11f698) by lia.
  assert (AG6 : forall Q : Z -> Prop, (forall x, Q x -> ((q + -112 <= x < q) \/ (fO <= x < fO + FSZ - 8) \/ (shad fO <= x < shad (fO + FSZ))) /\ ~ (O + 168 <= x < O + 168 + 80)) -> agree_on Q m5 m6).
  { intros Q HP a Ha. destruct (HP _ Ha) as [HX HN]. apply PRES6; [| exact HN]. destruct HX as [H|[H|H]]; [left; ul| apply CLF; exact H| apply CLS; exact H]. }
  lazymatch type of FR5 with rw_cells _ _ _ ?cs => assert (FR6 : rw_cells bsegs m6 (q + -96) cs)
    by (eapply rw_cells_agree_nw; [exact FR5|]; apply AG6; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [left; lia| clear - Hx FLO FHI FTOP LOW LOQ; lia]) end.
  lazymatch type of FRI5 with rw_cells _ _ _ ?cs => assert (FRI6 : rw_cells bsegs m6 (q + -112) cs)
    by (eapply rw_cells_agree_nw; [exact FRI5|]; apply AG6; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [left; lia| clear - Hx FLO FHI FTOP LOW LOQ; lia]) end.
  lazymatch type of P0 with rw_cells _ _ _ ?cs => assert (P06 : rw_cells bsegs m6 O cs)
    by (eapply rw_cells_agree_nw; [exact P0|]; apply AG6; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [right; left; lia| lia]) end.
  lazymatch type of OSR5 with rw_cells _ _ _ ?cs => assert (OSR6 : rw_cells bsegs m6 (O + 248) cs)
    by (eapply rw_cells_agree_nw; [exact OSR5|]; apply AG6; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [right; left; lia| lia]) end.
  assert (SH6 : OSHADOWA m6 O) by (apply (OSHADOWA_agree m5 m6 O SH5); apply AG6; intros x Hx; clear - Hx SHO FSELF FLO FHI; split; [do 2 right; lia| lia]).
  assert (LB6 : LOCBA m6).
  { apply (LOCBA_agree m5 m6 LB5). intros a Ha. apply PRES6; [right; left; apply client_static_intro; unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Ha; lia| unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Ha; clear - Ha FSG FLO; lia]. }
  assert (Z806 : rw_cells bsegs m6 (O + 168) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)]).
  { pose proof (rw_cells_CB_intro m6 (O + 168) _ BY6) as X. rewrite repeat_length in X. cbn [Z.to_nat Pos.to_nat] in X.
    specialize (X ltac:(apply (wr_at_transport bsegs m5 m6 (O + 168) 80); [apply (rw_cells_wr_at bsegs m5 _ _ 80 Z80); cbn; lia| exact WM6])).
    retype X [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)]. exact X. }
  assert (PRES06 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> ~ (O <= bv_unsigned a < O + 264) -> m6 a = m a).
  { intros a Ha Ho. rewrite <- (PRES05 a Ha Ho). apply PRES6; [apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| intros e He; exact He| lia]| lia]. }
  assert (SHZ6 : forall m', munch [(q - 128, q); (O, O + 264)] m6 m' -> wmono bsegs m6 m' -> shz m' O 264).
  { intros m' MU' _. apply SHZ0. apply (OSHADOWA_agree m6 m' O SH6). apply (agree_of_munch _ _ _ _ MU'). intros x Hx. cbn [outside].
    clear - Hx SHO FSELF SHT LOW LOQ FLO FHI. split; [lia| split; [lia| exact I]]. }
  pose proof (acc_lit RT AF Σ m6 0x17d908 40 ART6 ltac:(unfold ACC_LITS; repeat (first [left; reflexivity | right]))) as ACV6.
  assert (SHZV6 : forall m', munch [(q - 128, q); (O, O + 264)] m6 m' -> wmono bsegs m6 m' -> shz m' 0x17d908 40).
  { intros m' MU' _. apply (shz_of_acc m' 0x17d908 40); [| reflexivity| lia]. apply (acc_agree_at m6 m' 0x17d908 40 ACV6 ltac:(lia)).
    apply (agree_of_munch _ _ _ _ MU'). intros x Hx. cbn [outside]. destruct (VSEP x Hx) as [X Y]. split; [exact X| split; [exact Y| exact I]]. }
  pose proof (af_client_consts RT AF Σ m6 ART6) as (G1' & G2' & _). unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SHB in G1', G2'.
  clear AG6 PRES6 BY6 FR5 FRI5 P0 Z80 OSR5 SH5 LB5 PRES05 CD5 ART5 ST5 AG05 ACV SH LB ART0 MI. try clear G1 G2 V1 V2.

  apply (aevt_evt RT AF PMc MST).
  pose proof (munch_refl [(q - 128, q); (O, O + 264)]%Z m6) as MU. pose proof (wmono_refl bsegs m6) as WM.
  lstep. lstep. lstep. lstep. release_frame FRI6 ST6 (q + -96). lstep.
  takeZ P06 10%nat (O + 160) P00. retype P06 [CB 8 (repeat (Z_to_bv 8 0) 8)].

  assert (ST6' : stk bsegs m6 lo (q + -96)) by assumption.
  eapply evt_cut.
  { eapply (locale_ctor_specB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fc m6 lo (O + 160) _); rewrite ?UQ96;
      [exact ST6'| lia| lia| exact LB6| exact P06| lia| lia| left; lia| clear - FSEG FLO FHI; lia| exact MI6]. }
  cbv beta. intros ms1 (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m7 & -> & MU7 & WM7 & MI7 & ST7 & LOCW7 & LB7).
  rewrite ?UQ96 in MU7. rewrite ?UQ96 in ST7. rewrite (ret_pc_even 0xb5920) by lia.
  change (rw_cells bsegs m7 (O + 160) [C8 (Z_to_bv 64 PJ_LOC_IMP_A)]) in LOCW7.
  assert (AG7 : forall Q : Z -> Prop, (forall x, Q x -> ~ (q + -96 - 32 <= x < q + -96) /\ ~ (O + 160 <= x < O + 160 + 8)) -> agree_on Q m6 m7).
  { intros Q HP a Ha. apply MU7. cbn [outside]. destruct (HP _ Ha) as [X Y]. split; [exact X| split; [exact Y| exact I]]. }
  lazymatch type of FR6 with rw_cells _ _ _ ?cs => assert (FR7 : rw_cells bsegs m7 (q + -96) cs)
    by (eapply rw_cells_agree_nw; [exact FR6|]; apply AG7; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; lia) end.
  lazymatch type of P00 with rw_cells _ _ _ ?cs => assert (P07 : rw_cells bsegs m7 O cs)
    by (eapply rw_cells_agree_nw; [exact P00|]; apply AG7; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [clear - Hx FHI FTOP LOW LOQ; lia| lia]) end.
  lazymatch type of Z806 with rw_cells _ _ _ ?cs => assert (Z807 : rw_cells bsegs m7 (O + 168) cs)
    by (eapply rw_cells_agree_nw; [exact Z806|]; apply AG7; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [clear - Hx FHI FTOP LOW LOQ; lia| lia]) end.
  lazymatch type of OSR6 with rw_cells _ _ _ ?cs => assert (OSR7 : rw_cells bsegs m7 (O + 248) cs)
    by (eapply rw_cells_agree_nw; [exact OSR6|]; apply AG7; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [clear - Hx FHI FTOP LOW LOQ; lia| lia]) end.
  assert (SH7 : OSHADOWA m7 O) by (apply (OSHADOWA_agree m6 m7 O SH6); apply AG7; intros x Hx; cbn [outside]; clear - Hx SHO FSELF SHT LOW LOQ FLO FHI; split; lia).

  assert (MU' : munch [(q - 128, q); (O, O + 264)] m6 m7).
  { apply (munch_trans _ m6 m6 m7 MU). eapply munch_weaken; [| exact MU7]. intros x Hx. cbn [outside] in Hx |- *. lia. }
  pose proof (wmono_trans bsegs m6 m6 m7 WM WM7) as WM'.
  clear MU WM MU7 WM7 AG7 FR6 P00 P06 Z806 OSR6 ST6'. try clear ST6. try clear FRI6. rename MU' into MU. rename WM' into WM.

  lstep. chk SHZ6 (O + 248). lstep. lstep. chk SHZ6 (O + 256). lstep. chk SHZ6 (O + 259). lstep.

  do 4 (zstep; change (le1 (Z_to_bv 64 (-1))) with [Z_to_bv 8 18446744073709551615]; mem_after_store).
  lazymatch goal with H : rw_cells bsegs _ (O + 248) _ |- _ => retype_at H 1%nat 4%nat [C4 (Z_to_bv 64 0xFFFFFFFF)]; rename H into FILL end.

  chk2 SHZ6 O. lstep. chk2 SHZ6 (O + 112). lstep. lstep. lstep. lstep.
  apply evt_done.
  lazymatch goal with |- aevt _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mq end.
  lazymatch goal with H : rw_cells bsegs mq O _ |- _ => rename H into P08 end.
  lazymatch goal with H : rw_cells bsegs mq (O + 160) _ |- _ => rename H into LOCW8 end.
  lazymatch goal with H : rw_cells bsegs mq (O + 168) _ |- _ => rename H into Z808 end.
  lazymatch goal with H : rw_cells bsegs mq (O + 248) _ |- _ => rename H into FILL8 end.
  lazymatch goal with H : rw_cells bsegs mq (q + -96) _ |- _ => rename H into FR8 end.
  lazymatch goal with H : stk bsegs mq _ _ |- _ => rename H into ST8 end.
  assert (ART8 : ART RT Σ mq).
  { apply (art_client_write RT AF Σ m6 mq (q - 128) ART6 ltac:(ul)); [| exact WM]. intros a Ha. apply MU. cbn [outside].
    split; [intros Hin; apply Ha; left; ul|]. split; [intros Hin; apply Ha; apply CLF; lia| exact I]. }
  assert (AG68 : forall Q : Z -> Prop, (forall x, Q x -> ~ (q - 128 <= x < q) /\ ~ (O <= x < O + 264)) -> agree_on Q m6 mq).
  { intros Q HP a Ha. apply MU. cbn [outside]. destruct (HP _ Ha) as [X Y]. split; [exact X| split; [exact Y| exact I]]. }
  assert (SH8 : OSHADOWA mq O) by (apply (OSHADOWA_agree m6 mq O SH6); apply AG68; intros x Hx; clear - Hx SHO FSELF SHT LOW LOQ FLO FHI; split; lia).
  assert (LB8 : LOCBA mq) by (apply (LOCBA_agree m6 mq LB6); apply AG68; intros x Hx; unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx; clear - Hx FSG FLO LOR LOQ; lia).
  assert (PRES08 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> ~ (O <= bv_unsigned a < O + 264) -> mq a = m a).
  { intros a Ha Ho. rewrite <- (PRES06 a Ha Ho). apply MU. cbn [outside]. split; [destruct (CSEP _ Ha); lia|]. split; [exact Ho| exact I]. }
  takeZ P08 1%nat (O + 8) VP8. takeZ P08 1%nat (O + 112) SBJ.

  clear MU WM AG68 LB6 LB7 SH6 SH7 SHZ6 SHZV6 ACV6 PRES06 WM6 ART6.
  eapply (sb_ctorA Σ K lo O (q + -96) fO kO _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fc mq INF OIN ltac:(unfold STACK_WIN; exact LOW) LOR SBJ SH8 LB8 ART8
            ltac:(assumption) ST8 ltac:(unfold RT_STACK; lia) ltac:(unfold USTACK_TOP; lia) ltac:(clear - Q16; Z.div_mod_to_equations; lia)).
  intros y0 y1 y2 e0 e1 e2 e3 e4 e5 e6 e7 y3 y4 y5 y6 F9 mr j108 ART9 MI9 ST9 SBC9 HMC9 R44 MODE9 SH9 LB9 PRES9.
  rewrite (ret_pc_even 0xb5998) by lia.
  assert (AG9 : forall Q : Z -> Prop, (forall x, Q x -> ((q + -96 <= x < q) \/ (fO <= x < fO + FSZ - 8) \/ (shad fO <= x < shad (fO + FSZ))) /\ ~ (O + 8 <= x < O + 112)) -> agree_on Q mq mr).
  { intros Q HP a Ha. destruct (HP _ Ha) as [HX HN]. apply PRES9; [| cbn [outside]; split; [clear - HN; lia| exact I]]. destruct HX as [H|[H|H]]; [left; ul| apply CLF; exact H| apply CLS; exact H]. }
  lazymatch type of FR8 with rw_cells _ _ _ ?cs => assert (FR9 : rw_cells bsegs mr (q + -96) cs)
    by (eapply rw_cells_agree_nw; [exact FR8|]; apply AG9; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [left; lia| clear - Hx FLO FHI FTOP LOW LOQ; lia]) end.
  lazymatch type of VP8 with rw_cells _ _ _ ?cs => assert (VP9 : rw_cells bsegs mr O cs)
    by (eapply rw_cells_agree_nw; [exact VP8|]; apply AG9; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [right; left; lia| lia]) end.
  lazymatch type of P08 with rw_cells _ _ _ ?cs => assert (P09 : rw_cells bsegs mr (O + 112) cs)
    by (eapply rw_cells_agree_nw; [exact P08|]; apply AG9; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [right; left; lia| lia]) end.
  lazymatch type of LOCW8 with rw_cells _ _ _ ?cs => assert (LOCW9 : rw_cells bsegs mr (O + 160) cs)
    by (eapply rw_cells_agree_nw; [exact LOCW8|]; apply AG9; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [right; left; lia| lia]) end.
  lazymatch type of Z808 with rw_cells _ _ _ ?cs => assert (Z809 : rw_cells bsegs mr (O + 168) cs)
    by (eapply rw_cells_agree_nw; [exact Z808|]; apply AG9; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [right; left; lia| lia]) end.
  lazymatch type of FILL8 with rw_cells _ _ _ ?cs => assert (FILL9 : rw_cells bsegs mr (O + 248) cs)
    by (eapply rw_cells_agree_nw; [exact FILL8|]; apply AG9; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [right; left; lia| lia]) end.
  assert (PRES09 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> ~ (O <= bv_unsigned a < O + 264) -> mr a = m a).
  { intros a Ha Ho. rewrite <- (PRES08 a Ha Ho). apply PRES9; [apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| intros e He; exact He| lia]| cbn [outside]; split; [lia| exact I]]. }

  pose proof (rw_cells_joinA _ _ _ _ _ P09 LOCW9 ltac:(cbn [cells_size csize Nat.add]; lia)) as J1. cbn [app] in J1.
  pose proof (rw_cells_joinA _ _ _ _ _ J1 Z809 ltac:(cbn [cells_size csize Nat.add]; lia)) as J2. cbn [app] in J2.
  pose proof (rw_cells_joinA _ _ _ _ _ J2 FILL9 ltac:(cbn [cells_size csize Nat.add]; lia)) as IOSC. cbn [app] in IOSC. clear J1 J2 P09 LOCW9 Z809 FILL9.
  clear AG9 PRES9 FR8 VP8 P08 LOCW8 Z808 FILL8 SBJ SH8 LB8 PRES08 ART8 ST8.

  apply (aevt_evt RT AF PMc MST).
  pose proof (munch_refl [(q - 96, q); (O, O + 264)]%Z mr) as MU. pose proof (wmono_refl bsegs mr) as WM.
  do 11 lstep. lstep. release_frame FR9 ST9 q. lstep.
  takeZ R44 1%nat (O + 73) R1.
  apply evt_done. eapply HK; [exact ART9| exact MI9| assumption| | exact SH9| exact LB9| intros a Ha Ho; cbn [outside] in Ho; exact (PRES09 a Ha (proj1 Ho))].
  unfold OSSINVA, SBINVA', IOSINVA, PUTCELLSA, STRREPA, OSNUMA, ossA0, oa_lim. cbn [oa_data oa_w oa_cap oa_heap oa_k].
  split; [split; [| split]| split].
  - split; [exact SBC9|]. split; [exists (O + 73); split; [exact HMC9| lia]| exists j108; exact MODE9].
  - split; [exact R1|]. split; [eexists; exact R44| reflexivity].
  - unfold PJ_CAPMAX, PJ_OUTMAX, IMP_SCAP0. rewrite Z.pow_0_r. repeat split; lia.
  - unfold OSS_OS_VPTR_A. exact VP9.
  - lazymatch type of IOSC with rw_cells _ _ _ (_ :: _ :: CB 4 ?ja :: ?rest) =>
      lazymatch eval cbv in (last rest (C8 (Z_to_bv 64 0))) with CB 4 ?jb => exists ja, jb end end.
    unfold ios_cellsI, OSS_IOS_VPTR_A, OSS_CLASSIC_A. exact IOSC.
Qed.

End CT.
