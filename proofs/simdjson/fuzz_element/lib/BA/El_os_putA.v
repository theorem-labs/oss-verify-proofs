(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep ZBridge.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Startup_glue Sj_stage1_kit Pj_loc_kit Pj_os_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_iface3. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_new. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_num_akit Sj_num_amem Sj_num_aframe. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_fzwA Pj_lftoi1A Pj_rtkA Pj_defsA Pj_cpsA Pj_os_defsA Pj_mciA Pj_loc_akitA Pj_loc_getA Pj_os_put1A Pj_os_put2A Pj_os_put3A Pj_os_put4A Pj_os_xsputnA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import I_consts I_qck R_m2s. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import F_achk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import El_os_xsputnLA El_os_padA El_os_put4A El_ins_ifaceA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Export El_os_defsA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma retype_fill4 : forall m A cs n1 FL, (FL = 0x20 \/ FL = 0x30) ->
  firstn 4 (skipn n1 cs) = [C1 (Z_to_bv 8 FL); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m A cs -> rw_cells asegs m A (firstn n1 cs ++ [C4 (wz FL)] ++ skipn 4 (skipn n1 cs)).
Proof.
  intros m A cs n1 FL HFL E H. apply (rw_cells_retype_at asegs m A cs n1 4 [C4 (wz FL)] H).
  - cbn [cells_wf cell_wf]. repeat split; try apply repeat_length; reflexivity.
  - rewrite E. destruct HFL as [-> | ->]; apply bytes_eq_unsigned; vm_compute; reflexivity.
  - rewrite E. reflexivity.
Qed.
Lemma fill_after_set : forall fill, (fill = 0x20 \/ fill = 0x30) -> fill_after fill = fill.
Proof. intros fill [-> | ->]; reflexivity. Qed.

Definition fillb (fill b0 b1 b2 b3 : Z) : Prop :=
  (fill = 0xffffffff /\ b0 = 255 /\ b1 = 255 /\ b2 = 255 /\ b3 = 255) \/ ((fill = 0x20 \/ fill = 0x30) /\ b0 = fill /\ b1 = 0 /\ b2 = 0 /\ b3 = 0).

Lemma srcA_call : forall RT (Σ Σ1 : rts RT) q S BUF CAP bs, srcA RT Σ q BUF CAP bs -> S <= q ->
  (forall fk, In fk (rt_frames RT Σ) -> In fk (rt_frames RT Σ1)) -> srcA RT Σ1 S BUF CAP bs.
Proof.
  intros RT Σ Σ1 q S BUF CAP bs [H|[H|(f & k & Hin & H1 & H2)]] LE FR; [left; exact H| right; left; lia| right; right].
  exists f, k. split; [apply FR; exact Hin| lia].
Qed.

Section Put.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis RC2 : rt_contracts2 RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis RIP : rip_stmt.
Hypothesis AF_IC : forall Σ m, ART RT Σ m -> ictx m.
Hypothesis AF_SHW : forall Σ m p n, ART RT Σ m -> 0 < n -> rng_class RT Σ p n -> qc_words m p n /\ region_in_mem p n.
Hypothesis DCC : forall Σ m, ART RT Σ m -> el_dccA m.
Local Notation PAD := (padX_okA RT AF RC RC2 PMc FDO MST RIP AF_IC AF_SHW DCC).
Local Notation VTACC := (vt_accA RT AF).

Local Ltac ul := unfold EL_PUT_STACK_A, EL_PAD_STACK_A, EL_XSPUTN_DEPTH, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Theorem put_okXA : os_put_cpsA RT PMc.
Proof using AF RC RC2 FDO MST RIP AF_IC AF_SHW DCC.
  unfold os_put_cpsA. intros until bs. intros FDO' MST' INF FLO FHI AL16 OSF FOK HULL LB SRC LB' NR CAP40 B0 ACC SK SEP ART0 MI ST LOW LOR SPT SP16 FRB CRB HK.
  pose proof (af_frames_range RT AF Σ m fO kO ART0 INF) as (F0 & FTOP & _ & FLIVE).
  pose proof (af_frames_align RT AF Σ m fO kO ART0 INF) as (_ & FSEG).
  pose proof (proj2 (af_fshadow_apart RT AF Σ m fO kO ART0 INF) fO kO INF) as FSELF.
  pose proof (fframe_ranges RT AF Σ m fO kO ART0 INF) as (_ & _ & _ & _ & SHT).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  unfold EL_PUT_STACK_A, EL_PAD_STACK_A, EL_XSPUTN_DEPTH in *. unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *. remember (fs_size kO) as FSZ eqn:EFSZ.
  assert (Q0 : 0 <= q - 208) by (destruct ST; lia).
  assert (UQ : bv_unsigned (wz q) = q) by (apply unsigned_lit; lia).
  assert (EO : bv_unsigned (wz OS) = OS) by (apply unsigned_lit; lia).
  assert (LBS : length bs = Z.to_nat CAP) by lia.
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W0.
  assert (BHI : BUF + CAP <= 2^47).
  { destruct SK as [(RB & B1 & B2 & _)|[(B1 & B2)|(fB & kB & INB & B1 & B2)]]; [lia| unfold USTACK_TOP in B2; lia|].
    pose proof (fframe_ranges RT AF Σ m fB kB ART0 INB) as (_ & Y1 & _). unfold STACK_WIN in Y1. clear - Y1 B2 SP0R. lia. }
  destruct HULL as [(bo & FO) SHBY]. clear bo FO.

  destruct OSF as (pb & pp & ep & dum & j148 & j284 & OSF & PI). unfold os_cellsX, sb_cellsX, ios_cellsX in OSF. cbn [app] in OSF.
  takeZ OSF 9%nat (OS + 128)%Z SB. rename OSF into IOS.
  assert (RPP : 0 <= pp < 2^63 /\ 0 <= ep < 2^63) by (pose proof PI as [[P1 P2]|[P1 P2]]; clear - P1 P2 FLO FHI FTOP F0 SP0R EFSZ; lia).
  assert (XB : exists b0 b1 b2 b3, fillb fill b0 b1 b2 b3 /\ rw_cells asegs m (OS + 128) (ios_midA OS b0 b1 b2 b3 j148 j284)).
  { destruct FOK as [-> | [-> | ->]];
    [ retype_at IOS 21%nat 1%nat [C1 (Z_to_bv 8 255); C1 (Z_to_bv 8 255); C1 (Z_to_bv 8 255); C1 (Z_to_bv 8 255)]; exists 255, 255, 255, 255
    | retype_at IOS 21%nat 1%nat [C1 (Z_to_bv 8 32); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]; exists 32, 0, 0, 0
    | retype_at IOS 21%nat 1%nat [C1 (Z_to_bv 8 48); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]; exists 48, 0, 0, 0];
    retype_at IOS 2%nat 1%nat [CB 4 [Z_to_bv 8 2; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 0]]; (split; [unfold fillb; lia| exact IOS]). }
  clear IOS. destruct XB as (b0 & b1 & b2 & b3 & FB & IOS).
  change (rw_cells asegs m OS (sb_cellsA pb (wz pp) (wz ep) dum)) in SB.

  destruct (op_prologue q lo (OS + 128) BUF N ra gp (wz TPV_A) t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m
              ST ltac:(lia) ltac:(lia) ltac:(lia) SP16 ltac:(lia) ltac:(lia) ltac:(lia) (af_client_consts RT AF Σ m ART0) MI) as (sp' & SPR & SPA' & W0).
  apply (aevt_evt RT AF PMc MST). eapply evt_cut; [exact W0|]. cbv beta.
  intros ms1 (m1 & a1' & a2' & j0 & j1 & j2 & j3 & j4 & j5 & j6 & j7 & j8 & j9 & j10 & -> & MU1 & WM1 & MI1 & ST1 & FRl1 & STp1 & FRs1). apply evt_done. clear W0.
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 sp' ART0 ltac:(ul)); [| exact WM1].
    intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. ul. }
  assert (PRES1 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> m1 a = m a).
  { intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. destruct (aclient_split_c RT AF Σ m q _ ART0 Ha); ul. }
  assert (US : bv_unsigned (wz sp') = sp') by (apply unsigned_lit; lia).

  unfold entry_st.
  eapply (aevt_smalloc1 RT PMc FDO MST RC2 Σ); [reflexivity| unfold FRAMES_MAX2, FRAMES_TOT in *; lia| lia| exact ART1| exact MI1| | intros Efr0; exfalso; rewrite Efr0 in INF; exact INF |].
  { unfold call_ok. rewrite US. split; [exact ST1|]. split; [ul|]. split; [ul|]. split; [ul| clear - SPA'; Z.div_mod_to_equations; lia]. }
  intros Σ1 f w0 w1 w2 c1 c2 c3 c4 c5 c6 c7 w3 w4 w5 w6 F1 m2 (ART2 & MI2 & WM2 & ST2) PRES2 WRF WRS FRS1 LV1 SP1 CR1 FPOS F64 FTOP1.
  rewrite US in ST2, PRES2. rewrite (ret_pc_even 0xb816c) by lia.
  change (fs_size 1) with 128 in *. change (128 / 8) with 16 in WRS. replace (128 - 8) with 120 in WRF by reflexivity.
  assert (INF1 : In (f, 1%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
  assert (INO1 : In (fO, kO) (rt_frames RT Σ1)) by (rewrite FRS1; right; exact INF).
  pose proof (fframe_ranges RT AF Σ1 m2 f 1 ART2 INF1) as (_ & FR1' & _ & SHB1 & SHT1).
  pose proof (af_fshadow_apart RT AF Σ1 m2 f 1 ART2 INF1) as (FSL1 & FSF1). pose proof (FSF1 f 1%nat INF1) as FSELF1. pose proof (FSF1 fO kO INO1) as FSO1.
  pose proof (proj2 (af_fshadow_apart RT AF Σ1 m2 fO kO ART2 INO1) f 1%nat INF1) as OSF1.
  pose proof (af_frames_align RT AF Σ1 m2 f 1 ART2 INF1) as (_ & FSEG1).
  pose proof (af_frames_disj RT AF Σ1 m2 f 1 fO kO [] (rt_frames RT Σ) ART2 FRS1 INF) as FDJ.
  change (fs_size 1) with 128 in *. rewrite <- EFSZ in *. rewrite SP1 in FR1', SHT1.
  assert (SHF : shad (f + 128) = shad f + 16) by (unfold shad; Z.div_mod_to_equations; lia).
  rewrite SHF in *. unfold shad, SHB in SHB1, SHT1, FSELF1, FSL1, FSO1, OSF1, WRS.
  assert (FD0 : 0 <= f / 8) by (apply Z.div_pos; lia).
  pose proof (af_sp0_win RT AF Σ1 m2 ART2) as SP0W. rewrite SP1 in SP0W.
  pose proof (af_frames_hi RT AF Σ1 m2 f 1%nat ART2 INF1) as FHI1. change (fs_size 1) with 128 in FHI1.
  assert (FD8 : 0xd9400 <= f / 8) by (unfold SEGTOP_A in FSEG1; clear - FSEG1; Z.div_mod_to_equations; lia).
  assert (LOW' : 0x7fff7f800000 <= lo) by (clear - SP0W LOW; lia). unfold SEGTOP_A, STACK_WIN, USTACK_TOP in *.

  assert (OSLO : OS / 8 + 2147450880 + 37 <= lo) by (clear - FLO FHI SHT LOW; unfold shad, SHB in *; Z.div_mod_to_equations; lia).
  assert (OF : OS + 288 <= f \/ f + 128 <= OS) by (clear - FDJ FLO FHI; lia).
  assert (OSH : f + 128 <= OS / 8 + 2147450880 \/ (OS + 288) / 8 + 2147450880 <= f) by (clear - OSF1 FLO FHI; Z.div_mod_to_equations; lia).
  assert (OSH2 : OS + 288 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= OS) by (clear - FSO1 FLO FHI; lia).
  assert (OSELF : OS + 288 <= OS / 8 + 2147450880 \/ OS / 8 + 2147450880 + 37 <= OS) by (clear - FSELF FLO FHI; unfold shad, SHB in *; Z.div_mod_to_equations; lia).

  assert (CSEP : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) q a -> ~ (f <= a < f + 120) /\ ~ (f / 8 + 2147450880 <= a < f / 8 + 2147450880 + 16)).
  { intros a Ha. destruct Ha as [H|[H|[H|[H|H]]]].
    - clear - H FR1' SHT1 LOW LOR. unfold USTACK_TOP in H. split; intros X; lia.
    - pose proof (client_static_range _ H) as R. unfold SEGTOP_A in R. clear - R FSEG1 SHB1. split; intros X; lia.
    - destruct H as (p & k & Hin & Hr). pose proof (proj2 (proj2 (proj2 (af_frames_range RT AF Σ1 m2 f 1%nat ART2 INF1))) p k ltac:(rewrite LV1; exact Hin)) as Y1.
      pose proof (FSL1 p k ltac:(rewrite LV1; exact Hin)) as Y2. change (fs_size 1) with 128 in Y1. clear - Hr Y1 Y2. split; intros X; lia.
    - destruct H as (f9 & k9 & Hin & Hr). pose proof (af_frames_disj RT AF Σ1 m2 f 1 f9 k9 [] (rt_frames RT Σ) ART2 FRS1 Hin) as Y1.
      pose proof (FSF1 f9 k9 ltac:(rewrite FRS1; right; exact Hin)) as Y2. unfold shad, SHB in Y2. change (fs_size 1) with 128 in Y1.
      pose proof (fframe_ranges RT AF Σ m f9 k9 ART0 Hin) as (_ & _ & Y3 & _). clear - Hr Y1 Y2 Y3. split; intros X; lia.
    - destruct H as (f9 & k9 & Hin & Hr). pose proof (proj2 (af_fshadow_apart RT AF Σ1 m2 f9 k9 ART2 ltac:(rewrite FRS1; right; exact Hin)) f 1%nat INF1) as Y1.
      pose proof (af_frames_disj RT AF Σ1 m2 f 1 f9 k9 [] (rt_frames RT Σ) ART2 FRS1 Hin) as Y2. change (fs_size 1) with 128 in Y1, Y2.
      unfold shad, SHB in Hr, Y1. clear - Hr Y1 Y2 FD0. split; intros X; Z.div_mod_to_equations; lia. }

  assert (AG02 : forall (P : Z -> Prop), (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) q x /\ ~ (sp' <= x < q)) -> agree_on P m m2).
  { intros P HP a Ha. destruct (HP _ Ha) as [H1 H2]. rewrite (PRES2 a); [exact (PRES1 a H1)|]. apply (aclient_mono _ _ _ _ _ _ _ H1); [auto| auto| lia]. }
  assert (AG12 : forall (P : Z -> Prop), (forall x, P x -> sp' <= x < q) -> agree_on P m1 m2).
  { intros P HP a Ha. apply PRES2. left. pose proof (HP _ Ha). ul. }
  assert (CL : forall sp2 x, (fO <= x < fO + FSZ - 8) \/ (fO / 8 + 2147450880 <= x < (fO + FSZ) / 8 + 2147450880) \/ (PJ_LOC_LO_A <= x < PJ_LOC_HI_A) ->
            aclient (rt_live RT Σ) (rt_frames RT Σ) sp2 x).
  { intros sp2 x [H|[H|H]]; [right; right; right; left| do 4 right| right; left; apply client_static_intro; unfold PJ_LOC_LO_A, PJ_LOC_HI_A in H; lia];
      [exists fO, kO; rewrite <- EFSZ; split; [exact INF| exact H]| exists fO, kO; rewrite <- EFSZ; split; [exact INF| unfold shad, SHB; exact H]]. }
  assert (SRCT : forall mx : mem, mem_inv asegs mx ->
            (forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> outside [(OS, OS + 288)] (bv_unsigned a) -> mx a = m a) -> bytes_at asegs mx BUF bs).
  { intros mx MIx PRx. destruct SK as [(RB & B1 & B2 & _)|[(B1 & B2)|(fB & kB & INB & B1 & B2)]].
    - apply (ro_bytes_at asegs mx BUF bs MIx); [lia| rewrite LBS; lia| exact RB].
    - eapply bytes_at_agree; [exact SRC|]. intros a Ha. rewrite LBS in Ha. apply PRx; [left; lia| cbn [outside]; split; [clear - Ha SEP NR; lia| exact I]].
    - eapply bytes_at_agree; [exact SRC|]. intros a Ha. rewrite LBS in Ha.
      apply PRx; [right; right; right; left; exists fB, kB; split; [exact INB| lia]| cbn [outside]; split; [clear - Ha SEP NR; lia| exact I]]. }
  assert (ACCT : forall (Σx : rts RT) (mx : mem), ART RT Σx mx -> rt_live RT Σx = rt_live RT Σ -> rt_sp0 RT Σx = rt_sp0 RT Σ ->
            (forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> outside [(OS, OS + 288)] (bv_unsigned a) -> mx a = m a) -> acc asegs mx BUF N).
  { intros Σx mx ARTx LVx SPx PRx. destruct SK as [(RB & B1 & B2 & (la & ln & INL & L1 & L2))|[(B1 & B2)|(fB & kB & INB & B1 & B2)]].
    - apply (acc_sub asegs mx la ln); [exact (acc_lit RT AF Σx mx la ln ARTx INL)| lia| lia].
    - apply (af_acc_stack RT AF Σx mx BUF N ARTx); [rewrite SPx; ul| ul].
    - apply (acc_agreeP m mx BUF N ACC). intros a Ha. pose proof (fframe_ranges RT AF Σ m fB kB ART0 INB) as (Y0 & _).
      pose proof (proj2 (af_fshadow_apart RT AF Σ m fB kB ART0 INB) fO kO INF) as Y1. rewrite <- EFSZ in Y1. unfold shad, SHB in Ha, Y1.
      apply PRx; [do 4 right; exists fB, kB; split; [exact INB| unfold shad, SHB; clear - Ha B1 B2 NR Y0; Z.div_mod_to_equations; lia]
                | cbn [outside]; split; [clear - Ha B1 B2 NR Y0 Y1 FLO FHI; Z.div_mod_to_equations; lia| exact I]]. }
  Local Ltac byAG H AG := eapply rw_cells_agree_nw; [exact H|]; apply AG; intros x Hx;
                          cbn [ios_midA sb_cellsA fa_saved op_locals0 op_sh12 cells_size csize Nat.add length app map repeat] in Hx.
  assert (FRl2 : rw_cells asegs m2 sp' (op_locals0 j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10)) by (byAG FRl1 AG12; lia).
  assert (FRs2 : rw_cells asegs m2 (q - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)) by (byAG FRs1 AG12; lia).
  assert (STp2 : stk asegs m2 (sp' + 88) (q - 104)) by (eapply stk_agree_nw; [exact STp1|]; apply AG12; intros x Hx; cbv beta in Hx; lia).
  assert (SB2 : rw_cells asegs m2 OS (sb_cellsA pb (wz pp) (wz ep) dum)) by (byAG SB AG02; split; [apply (CL q); left; lia| clear - Hx FHI FTOP LOW LOR SPR; lia]).
  assert (IOS2 : rw_cells asegs m2 (OS + 128) (ios_midA OS b0 b1 b2 b3 j148 j284)) by (byAG IOS AG02; split; [apply (CL q); left; lia| clear - Hx FHI FTOP LOW LOR SPR; lia]).
  assert (SHBY2 : bytes_at asegs m2 (OS / 8 + 2147450880) (repeat z8 36)).
  { eapply bytes_at_agree; [exact SHBY|]. apply AG02. intros x Hx. rewrite repeat_length in Hx. unfold shad, SHB in *.
    split; [apply (CL q); right; left| clear - Hx FLO FHI SHT LOW LOR SPR]; Z.div_mod_to_equations; lia. }
  assert (LB2 : LOCBA m2).
  { apply (LOCBA_agree m m2 LB). apply AG02. intros x Hx. split; [apply (CL q); right; right; exact Hx| unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx; clear - Hx LOW' LOR SPR; lia]. }
  assert (PRES2' : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> m2 a = m a).
  { intros a Ha. apply (AG02 (fun x => x = bv_unsigned a)); [| reflexivity]. intros x ->. split; [exact Ha|].
    destruct (aclient_split_c RT AF Σ m q _ ART0 Ha); ul. }
  clear PRES1 PRES2 AG12 AG02 FRl1 FRs1 STp1 ST1 MI1 ART1 MU1 WM1 SB IOS SHBY.

  destruct (wr_at_rw_CB m2 f 24 (wr_at_sub m2 f 120 f 24 WRF ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jH & FH2).
  change (Z.to_nat 24) with 24%nat in FH2.
  apply (rw_cells_split_CB asegs _ _ [] 24 _ [] [8; 8; 8]%nat) in FH2; [| reflexivity]. cbn [mk_CB_cells app] in FH2. forget_junk FH2.
  destruct (wr_at_rw_CB m2 (f + 32) 8 (wr_at_sub m2 f 120 (f + 32) 8 WRF ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jT & TMP2).
  change (Z.to_nat 8) with 8%nat in TMP2.
  destruct (wr_at_rw_CB m2 (f + 64) 16 (wr_at_sub m2 f 120 (f + 64) 16 WRF ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jE & SEN2).
  change (Z.to_nat 16) with 16%nat in SEN2.
  apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [1; 7; 8]%nat) in SEN2; [| reflexivity]. cbn [mk_CB_cells app] in SEN2. forget_junk SEN2.
  destruct (wr_at_rw_CB m2 (f / 8 + 2147450880) 16 WRS ltac:(lia)) as (jS & FS2).
  change (Z.to_nat 16) with 16%nat in FS2.
  apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1]%nat) in FS2; [| reflexivity]. cbn [mk_CB_cells app] in FS2.
  lazymatch type of FS2 with rw_cells _ _ _ ?cs =>
    let ls := eval cbv in (map (fun c => match c with CB _ l => l | _ => [] end) cs) in
    change (rw_cells asegs m2 (f / 8 + 2147450880) (map (fun l => CB 1 l) ls)) in FS2; set (lS := ls) in FS2;
    assert (LS : length lS = 16%nat) by reflexivity; clearbody lS
  end.
  assert (LS4 : length (skipn 12 lS) = 4%nat) by (rewrite length_skipn, LS; reflexivity).
  pose proof (DCC Σ1 m2 ART2) as (VT2 & _). change (ro_cells asegs m2 PJ_NULSB_VT_A [C8 (wz PJ_XSPUTN_A); C8 (wz PJ_OVERFLOW_A); C8 (wz 8)]) in VT2.

  apply (aevt_evt RT AF PMc MST). unfold SHB.
  lazymatch type of FH2 with rw_cells _ _ _ [CB 8 ?h0; CB 8 ?h1; CB 8 ?h2] => lazymatch type of SEN2 with rw_cells _ _ _ [CB 1 ?e0; CB 7 ?e1; CB 8 ?e2] =>
  eapply evt_cut; [eapply (op_segAX b0 b1 b2 b3 q sp' f OS BUF N lo gp (wz TPV_A) w0 w1 w2 c1 c2 c3 c4 c5 c6 c7 s2 s4 s5 s6 s9 s10 w3 w4 w5 w6
                              j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 h0 h1 h2 e0 e1 e2 j148 j284 lS F1 fc m2 LS);
                   [lia| lia| exact FD8| lia| exact FSELF1| lia| lia| exact AL16| exact OF| exact OSH2| exact LOW'| lia| lia| lia| lia| lia| lia
                   | exact FRl2| exact FH2| exact SEN2| exact FS2| exact IOS2| exact VT2| exact MI2]|] end end.
  cbv beta. intros ms3 (m3 & -> & MU3 & WM3 & MI3 & FRl3 & FH3 & SEN3 & FS3). apply evt_done.

  assert (ARTW : forall (mx my : mem) (sp2 : Z) W, ART RT Σ1 mx -> rt_sp0 RT Σ - 8388608 <= sp2 -> munch W mx my -> wmono asegs mx my ->
            Forall (fun iv => (sp2 <= fst iv /\ snd iv <= q) \/ (f <= fst iv /\ snd iv <= f + 120) \/ (f / 8 + 2147450880 <= fst iv /\ snd iv <= f / 8 + 2147450880 + 16)
                              \/ (fO <= fst iv /\ snd iv <= fO + FSZ - 8)) W ->
            ART RT Σ1 my).
  { intros mx my sp2 W ARTx SP2 MU WM HW. apply (art_client_write RT AF Σ1 mx my sp2 ARTx ltac:(rewrite SP1; ul)); [| exact WM].
    intros a Ha. apply MU. clear - HW Ha INF1 INO1 EFSZ SPT FD0. induction W as [|[lo' hi'] W IH]; [exact I|].
    apply Forall_cons_iff in HW. destruct HW as [H1 HW]. cbn [outside fst snd] in *. split; [| exact (IH HW)].
    intros Hin. apply Ha. destruct H1 as [H1|[H1|[H1|H1]]].
    - left. unfold USTACK_TOP. lia.
    - right; right; right; left. exists f, 1%nat. split; [exact INF1| change (fs_size 1) with 128; lia].
    - do 4 right. exists f, 1%nat. split; [exact INF1| unfold shad, SHB; change (fs_size 1) with 128; Z.div_mod_to_equations; lia].
    - right; right; right; left. exists fO, kO. rewrite <- EFSZ. split; [exact INO1| lia]. }
  assert (PRESW : forall (mx my : mem) W, (forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> outside [(OS, OS + 288)] (bv_unsigned a) -> mx a = m a) ->
            munch W mx my ->
            Forall (fun iv => (snd iv <= q /\ lo <= fst iv) \/ (f <= fst iv /\ snd iv <= f + 120) \/ (f / 8 + 2147450880 <= fst iv /\ snd iv <= f / 8 + 2147450880 + 16)
                              \/ (OS <= fst iv /\ snd iv <= OS + 288)) W ->
            forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> outside [(OS, OS + 288)] (bv_unsigned a) -> my a = m a).
  { intros mx my W PR MU HW a Ha Ho. rewrite <- (PR a Ha Ho). apply MU. pose proof (CSEP _ Ha) as [C1 C2]. destruct (aclient_split_c RT AF Σ m q _ ART0 Ha) as [X|X];
      unfold STACK_WIN in X; cbn [outside] in Ho; (clear - HW C1 C2 X Ho LOW; induction W as [|[lo' hi'] W IH]; [exact I|];
      apply Forall_cons_iff in HW; destruct HW as [H1 HW]; cbn [outside fst snd] in *; split; [lia| exact (IH HW)]). }
  Local Ltac fa1 tac := apply Forall_cons; [cbn [fst snd]; tac|].
  assert (ART3 : ART RT Σ1 m3).
  { apply (ARTW m2 m3 sp' _ ART2 ltac:(clear - LOW LOR SPR; lia) MU3 WM3).
    fa1 ltac:(left; clear - SPR; lia). fa1 ltac:(right; left; clear; lia). fa1 ltac:(right; left; clear; lia). fa1 ltac:(right; right; left; clear; lia). apply Forall_nil. }
  assert (PRES3 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> outside [(OS, OS + 288)] (bv_unsigned a) -> m3 a = m a).
  { apply (PRESW m2 m3 _ ltac:(intros a Ha _; exact (PRES2' a Ha)) MU3).
    fa1 ltac:(left; clear - SPR LOR; lia). fa1 ltac:(right; left; clear; lia). fa1 ltac:(right; left; clear; lia). fa1 ltac:(right; right; left; clear; lia). apply Forall_nil. }
  assert (AG3 : forall P : Z -> Prop, (forall x, P x -> ~ (sp' <= x < sp' + 88) /\ ~ (f <= x < f + 24) /\ ~ (f + 64 <= x < f + 80) /\ ~ (f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 16)) ->
                 agree_on P m2 m3).
  { intros P HP a Ha. apply MU3. cbn [outside]. destruct (HP _ Ha) as (H1 & H2 & H3 & H4). repeat split; assumption. }
  assert (FRs3 : rw_cells asegs m3 (q - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)) by (byAG FRs2 AG3; clear - Hx FR1' SHT1 LOW LOR SPR; lia).
  assert (STp3 : stk asegs m3 (sp' + 88) (q - 104)) by (eapply stk_agree_nw; [exact STp2|]; apply AG3; intros x Hx; cbv beta in Hx; clear - Hx FR1' SHT1 LOW LOR SPR; lia).
  assert (ST3 : stk asegs m3 lo sp') by (eapply stk_agree_nw; [exact ST2|]; apply AG3; intros x Hx; cbv beta in Hx; clear - Hx FR1' SHT1 LOW LOR SPR; lia).
  assert (TMP3 : rw_cells asegs m3 (f + 32) [CB 8 jT]) by (byAG TMP2 AG3; clear - Hx FLO FR1' LOW LOR SPR FSELF1; lia).
  assert (SB3 : rw_cells asegs m3 OS (sb_cellsA pb (wz pp) (wz ep) dum)) by (byAG SB2 AG3; clear - Hx FLO FHI FTOP LOW LOR SPR OF OSH2; lia).
  assert (IOS3 : rw_cells asegs m3 (OS + 128) (ios_midA OS b0 b1 b2 b3 j148 j284)) by (byAG IOS2 AG3; clear - Hx FLO FHI FTOP LOW LOR SPR OF OSH2; lia).
  assert (SHBY3 : bytes_at asegs m3 (OS / 8 + 2147450880) (repeat z8 36)).
  { eapply bytes_at_agree; [exact SHBY2|]. apply AG3. intros x Hx. rewrite repeat_length in Hx.
    clear - Hx OSLO LOR SPR OSH OF FD8 F0 FLO. repeat split; Z.div_mod_to_equations; lia. }
  assert (LB3 : LOCBA m3).
  { apply (LOCBA_agree m2 m3 LB2). apply AG3. intros x Hx. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx. clear - Hx LOW' LOR SPR FD8 FSEG1. unfold SEGTOP_A in *. lia. }
  clear AG3 MU3 WM3 FRl2 FH2 SEN2 FS2 FRs2 STp2 ST2 SB2 IOS2 SHBY2 MI2 WM2 TMP2 LB2 PRES2'.

  lazymatch type of FH3 with rw_cells _ _ _ ?fhc => lazymatch type of SEN3 with rw_cells _ _ _ ?senc => lazymatch type of FS3 with rw_cells _ _ ?fsa ?fsc =>
  lazymatch type of FRs3 with rw_cells _ _ ?frsa ?frsc => lazymatch type of STp3 with stk _ _ ?stpa ?stpb =>
  assert (TAIL : forall (m6 : mem) (LC : list cell) (FL : Z) (yt0 yt1 yt2 ya6 ya7 yt3 yt4 yt5 yt6 : word),
    rw_cells asegs m6 sp' LC -> cells_size LC = 88%nat -> (FL = 0x20 \/ FL = 0x30) -> fill_after fill = FL ->
    ART RT Σ1 m6 ->
    (forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> outside [(OS, OS + 288)] (bv_unsigned a) -> m6 a = m a) ->
    rw_cells asegs m6 frsa frsc -> stk asegs m6 stpa stpb -> stk asegs m6 lo sp' ->
    rw_cells asegs m6 f fhc -> rw_cells asegs m6 (f + 64) senc ->
    rw_cells asegs m6 OS (sb_cellsA pb (wz pp) (wz ep) dum) -> bytes_at asegs m6 (OS / 8 + 2147450880) (repeat z8 36) ->
    rw_cells asegs m6 (OS + 128) (ios_midA OS FL 0 0 0 j148 j284) -> rw_cells asegs m6 fsa fsc -> mem_inv asegs m6 ->
    aevt RT PMc Σ1 K (MS (mkR (wz 0xb83e8) (wz sp') gp (wz TPV_A) yt0 yt1 yt2 (wz q) (wz sp') (wz OS) (wz BUF) (wz BUF) (wz (BUF + N)) (wz (OS + 136)) (wz FL) ya6 ya7 (wz f) (wz (OS + 128)) (wz (f + 64)) (wz (f / 8 + 2147450880)) (wz (OS + 136)) (wz BUF) (wz ((OS + 280) / 8 + 2147450880)) (wz f) (wz (OS + 280)) (wz 2147450880) yt3 yt4 yt5 yt6)
                 F1 (wz PJ_PADOUT_A) fc None m6 (seg_rom asegs)))
  end end end end end.
  { intros m6 LC FL yt0 yt1 yt2 ya6 ya7 yt3 yt4 yt5 yt6 FRl6 LCS HFL HFA ART6 PRES6 FRs6 STp6 ST6 FH6 SEN6 SB6 SHBY6 IOS6 FS6 MI6.

  pose proof IOS6 as IOSc. unfold ios_midA in IOSc. takeZ IOSc 5%nat (OS + 160)%Z IOSa6. takeZ IOSc 1%nat (OS + 168)%Z WID6. rename IOSc into IOSb6.
  assert (HULL6 : os_hullA m6 OS).
  { split; [| unfold shad, SHB; exact SHBY6]. pose proof SB6 as SBc. unfold sb_cellsA in SBc. pose proof IOS6 as IOSc. unfold ios_midA in IOSc. glueZ SBc IOSc.
    destruct (rw_cells_forget asegs m6 OS _ SBc) as (bo6 & H6). exists bo6. exact H6. }
  pose proof (ACCT Σ1 m6 ART6 LV1 SP1 PRES6) as ACC6. pose proof (SRCT m6 MI6 PRES6) as SRC6.
  assert (SK1 : srcA RT Σ1 sp' BUF CAP bs) by (apply (srcA_call RT Σ Σ1 q sp' BUF CAP bs SK); [clear - SPR; lia| intros fk Hfk; rewrite FRS1; right; exact Hfk]).
  eapply (PAD Σ1 K OS BUF N CAP sp' lo fO FL pp ep kO pb dum bs); [exact FDO| exact MST| exact INO1| exact FLO| rewrite <- EFSZ; exact FHI| exact AL16| exact SB6| exact PI| exact WID6| exact HULL6
    | exact SRC6| lia| lia| exact CAP40| lia| exact ACC6| exact SK1| exact SEP| clear - HFL; lia| exact ART6| exact MI6| exact ST6| rewrite SP1; ul| ul| ul| clear - SPA'; Z.div_mod_to_equations; lia
    | rewrite FRS1; cbn [length]; unfold FRAMES_TOT in *; lia| rewrite CR1; lia|].
  intros Σ2 x0 x1 x2 d1 d2 d3 d4 d5 d6 d7 x3 x4 x5 x6 F7 m7 pb' pp' ep' dum' ART7 MI7 ST7 HULL7 SB7 PI7 WID7 LV2 FRS2 SP2 CR2 PRES7. rewrite (ret_pc_even 0xb83e8) by lia.
  apply (aevt_evt RT AF PMc MST). zstep. if_cases KB; zify_cond KB; [| exfalso; clear - KB F0 FLO; lia]. apply evt_done.

  assert (AG7 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) sp' x /\ ~ (OS + 40 <= x < OS + 128) /\ ~ (OS + 160 <= x < OS + 168)) -> agree_on P m6 m7).
  { intros P HP a Ha. destruct (HP _ Ha) as (H1 & H2 & H3). apply PRES7; [exact H1| cbn [outside]; split; [exact H2| split; [exact H3| exact I]]]. }
  assert (CL1 : forall sp2 x, (sp' <= x < q /\ sp2 <= sp') \/ (fO <= x < fO + FSZ - 8) \/ (fO / 8 + 2147450880 <= x < (fO + FSZ) / 8 + 2147450880)
                             \/ (f <= x < f + 120) \/ (f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 16) -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) sp2 x).
  { intros sp2 x [[H1 H2]|[H|[H|[H|H]]]]; [left; ul| right; right; right; left| do 4 right| right; right; right; left| do 4 right].
    - exists fO, kO. rewrite <- EFSZ. split; [exact INO1| exact H].
    - exists fO, kO. rewrite <- EFSZ. split; [exact INO1| unfold shad, SHB; exact H].
    - exists f, 1%nat. split; [exact INF1| change (fs_size 1) with 128; lia].
    - exists f, 1%nat. split; [exact INF1| unfold shad, SHB; change (fs_size 1) with 128; clear - H FD0; Z.div_mod_to_equations; lia]. }
  assert (FRl7 : rw_cells asegs m7 sp' LC)
    by (eapply rw_cells_agree_nw; [exact FRl6|]; apply AG7; intros x Hx; rewrite LCS in Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; split; [apply (CL1 sp'); left; lia| clear - Hx FLO FHI FTOP LOW LOR SPR; lia]).
  assert (FRs7 : rw_cells asegs m7 (q - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)) by (byAG FRs6 AG7; split; [apply (CL1 sp'); left; lia| clear - Hx FLO FHI FTOP LOW LOR SPR; lia]).
  assert (STp7 : stk asegs m7 (sp' + 88) (q - 104)).
  { eapply stk_agree_nw; [exact STp6|]. apply AG7. intros x Hx. cbv beta in Hx. split; [apply (CL1 sp'); left; lia| clear - Hx FLO FHI FTOP LOW LOR SPR; lia]. }
  assert (FH7 : rw_cells asegs m7 f [C8 (wz 0x41b58ab3); C8 (wz 0x22601); C8 (wz 0xb80f4)]) by (byAG FH6 AG7; split; [apply (CL1 sp'); right; right; right; left; lia| clear - Hx OF; lia]).
  lazymatch type of SEN6 with rw_cells _ _ _ ?cs => assert (SEN7 : rw_cells asegs m7 (f + 64) cs) by (byAG SEN6 AG7; split; [apply (CL1 sp'); right; right; right; left; lia| clear - Hx OF; lia]) end.
  assert (FS7 : rw_cells asegs m7 (f / 8 + 2147450880) (map C1 (op_sh12 (-8)) ++ map (fun l => CB 1 l) (skipn 12 lS))).
  { eapply rw_cells_agree_nw; [exact FS6|]. apply AG7. intros x Hx. rewrite cells_size_app, cells_size_map_C1p, cells_size_map_CB1, LS4 in Hx.
    cbn [length op_sh12 app repeat Nat.add] in Hx. split; [apply (CL1 sp'); do 4 right; lia| clear - Hx OSH2; lia]. }
  lazymatch type of IOSa6 with rw_cells _ _ _ ?cs => assert (IOSa7 : rw_cells asegs m7 (OS + 128) cs) by (byAG IOSa6 AG7; split; [apply (CL1 sp'); right; left; lia| lia]) end.
  lazymatch type of IOSb6 with rw_cells _ _ _ ?cs => assert (IOSb7 : rw_cells asegs m7 (OS + 168) cs) by (byAG IOSb6 AG7; split; [apply (CL1 sp'); right; left; lia| lia]) end.
  destruct HULL7 as [_ SHBY7]. unfold shad, SHB in SHBY7.
  assert (PRES7' : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> outside [(OS, OS + 288)] (bv_unsigned a) -> m7 a = m a).
  { intros a Ha Ho. rewrite <- (PRES6 a Ha Ho). apply PRES7; [| cbn [outside] in Ho |- *; clear - Ho; repeat split; try exact I; lia].
    apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LV1; auto| rewrite FRS1; intros e He; right; exact He| lia]. }
  clear AG7 PRES7 FRl6 FRs6 STp6 ST6 FH6 SEN6 FS6 IOSa6 IOSb6 WID6 IOS6 SB6 SHBY6 SRC6 MI6 HULL6 ACC6 ART6 PRES6.

  pose proof (DCC Σ2 m7 ART7) as (VT7 & _). change (ro_cells asegs m7 PJ_NULSB_VT_A [C8 (wz PJ_XSPUTN_A); C8 (wz PJ_OVERFLOW_A); C8 (wz 8)]) in VT7.
  pose proof IOSb7 as IOSc. takeZ IOSc 3%nat (OS + 184)%Z IOS3c. clear IOSc. pose proof WID7 as WIDc. glueZ WIDc IOS3c. pose proof IOSa7 as IOS9. glueZ IOS9 WIDc.
  pose proof FH7 as FHc. takeZ FHc 1%nat (f + 8)%Z FH0. clear FHc.
  apply (aevt_evt RT AF PMc MST).
  lazymatch type of SEN7 with rw_cells _ _ _ [C1 _; CB 7 ?e1; C8 _] =>
  eapply evt_cut; [eapply (op_exit1 q sp' f lo OS PJ_IOS_VPTR_A _ gp (wz TPV_A) x0 x1 x2 _ d1 d2 d3 d4 d5 d6 d7 _ _ _ _ _ x3 x4 x5 x6 _ e1 j148 (op_sh12 (-8)) (skipn 12 lS) F7 fc m7);
                   [reflexivity| exact LS4| lia| lia| exact FD0| lia| exact FSELF1| lia| lia| exact OF| exact OSH2| clear - LOW'; lia| clear - LOR SPR; lia| lia| unfold PJ_IOS_VPTR_A; lia
                   | exact ST7| exact SEN7| exact IOS9| exact VT7| exact FH0| exact FS7| exact MI7]|] end.
  cbv beta. intros ms8 (a1x & a2x & m8 & -> & MU8 & WM8 & MI8 & ST8 & FH8 & FS8).
  assert (AG8 : forall P : Z -> Prop, (forall x, P x -> ~ (sp' - 16 <= x < sp') /\ ~ (f <= x < f + 8) /\ ~ (f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 16)) -> agree_on P m7 m8).
  { intros P HP a Ha. apply MU8. cbn [outside]. destruct (HP _ Ha) as (H1 & H2 & H3). repeat split; assumption. }
  assert (ART8 : ART RT Σ2 m8).
  { apply (art_client_write RT AF Σ2 m7 m8 (sp' - 16) ART7 ltac:(rewrite SP2, SP1; clear - LOW LOR SPR; unfold STACK_WIN; lia)); [| exact WM8]. intros a Ha. apply MU8. rewrite LV2, FRS2 in Ha. cbn [outside].
    split; [intros Hin; apply Ha; left; ul|].
    split; [intros Hin; apply Ha; right; right; right; left; exists f, 1%nat; split; [exact INF1| change (fs_size 1) with 128; lia]|].
    split; [| exact I]. intros Hin; apply Ha. do 4 right. exists f, 1%nat. split; [exact INF1|]. unfold shad, SHB. change (fs_size 1) with 128. clear - Hin FD0. Z.div_mod_to_equations. lia. }
  destruct (af_frame_release RT AF Σ2 m8 f 1%nat (rt_frames RT Σ) ART8 ltac:(rewrite FRS2; exact FRS1)) as (Σ3 & fl & FLC & NAC & FL0 & FLW & FW & REL).
  change (fs_size 1) with 128 in FW. replace (f + 128 - 8) with (f + 120) in FW by lia. rewrite SP2, SP1 in FLW.
  assert (FRl8 : rw_cells asegs m8 sp' LC)
    by (eapply rw_cells_agree_nw; [exact FRl7|]; apply AG8; intros x Hx; rewrite LCS in Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; clear - Hx FR1' SHT1 LOW LOR SPR; lia).
  assert (FRs8 : rw_cells asegs m8 (q - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)) by (byAG FRs7 AG8; clear - Hx FR1' SHT1 LOW LOR SPR; lia).
  assert (STp8 : stk asegs m8 (sp' + 88) (q - 104)) by (eapply stk_agree_nw; [exact STp7|]; apply AG8; intros x Hx; cbv beta in Hx; clear - Hx FR1' SHT1 LOW LOR SPR; lia).
  assert (SB8 : rw_cells asegs m8 OS (sb_cellsA pb' (wz pp') (wz ep') dum')) by (byAG SB7 AG8; clear - Hx FLO FHI FTOP LOW LOR SPR OF OSH2; lia).
  lazymatch type of IOSa7 with rw_cells _ _ _ ?cs => assert (IOSa8 : rw_cells asegs m8 (OS + 128) cs) by (byAG IOSa7 AG8; clear - Hx FLO FHI FTOP LOW LOR SPR OF OSH2; lia) end.
  assert (WID8 : rw_cells asegs m8 (OS + 160) [C8 (wz 0)]) by (byAG WID7 AG8; clear - Hx FLO FHI FTOP LOW LOR SPR OF OSH2; lia).
  lazymatch type of IOSb7 with rw_cells _ _ _ ?cs => assert (IOSb8 : rw_cells asegs m8 (OS + 168) cs) by (byAG IOSb7 AG8; clear - Hx FLO FHI FTOP LOW LOR SPR OF OSH2; lia) end.
  assert (SHBY8 : bytes_at asegs m8 (OS / 8 + 2147450880) (repeat z8 36)).
  { eapply bytes_at_agree; [exact SHBY7|]. apply AG8. intros x Hx. rewrite repeat_length in Hx.
    clear - Hx OSLO LOR SPR OSH OF FD8 F0 FLO FHI. repeat split; Z.div_mod_to_equations; lia. }
  assert (PRES8 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> outside [(OS, OS + 288)] (bv_unsigned a) -> m8 a = m a).
  { apply (PRESW m7 m8 _ PRES7' MU8). fa1 ltac:(left; clear - SPR LOR; lia). fa1 ltac:(right; left; clear; lia). fa1 ltac:(right; right; left; clear; lia). apply Forall_nil. }
  clear AG8 IOS9 FH0 VT7 FRl7 FRs7 STp7 ST7 FH7 SEN7 FS7 IOSa7 IOSb7 WID7 SB7 SHBY7 PRES7' MI7.

  eapply evt_cut; [eapply (op_exit2 q sp' f fl lo (OS + 128) (wz 0xb8440) gp (wz TPV_A) x0 x1 x2 (wz (-11)) a1x a2x d3 d4 d5 d6 d7 _ _ _ _ _ _ _ _ x3 x4 x5 x6
                             ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                             LC F7 fc m8);
                   [lia| lia| exact FL0| clear - FLW LOW; unfold STACK_WIN in *; lia| lia| clear - LOW'; lia| lia| exact LCS| lia| lia| exact ST8| exact FRl8| exact STp8| exact FRs8| exact FW| exact FLC| exact MI8]|].
  cbv beta. intros ms9 (m9 & -> & MU9 & WM9 & MI9 & ST9 & FLC9).
  destruct (REL m9 MU9 WM9 FLC9) as (ART9 & FRS9 & LV9 & SP9 & CR9 & AL9 & AM9).
  apply evt_done. apply (aevt_switch RT PMc Σ2 Σ3 K _ AL9 AM9).
  assert (AG9 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) q x) -> agree_on P m8 m9).
  { intros P HP a Ha. pose proof (HP _ Ha) as H1. apply MU9. cbn [outside]. split; [| exact I]. intros E. apply NAC. rewrite LV2, LV1, FRS2, FRS1. replace fl with (bv_unsigned a) by lia.
    destruct H1 as [H|[H|[H|[H|H]]]]; [exfalso; clear - H E FLW LOW LOR; ul| right; left; exact H| right; right; left; exact H
      | right; right; right; left; destruct H as (f9 & k9 & Hin & Hr); exists f9, k9; split; [right; exact Hin| exact Hr]
      | do 4 right; destruct H as (f9 & k9 & Hin & Hr); exists f9, k9; split; [right; exact Hin| exact Hr]]. }
  assert (SB9 : rw_cells asegs m9 OS (sb_cellsA pb' (wz pp') (wz ep') dum')) by (byAG SB8 AG9; apply (CL q); left; lia).
  lazymatch type of IOSa8 with rw_cells _ _ _ ?cs => assert (IOSa9 : rw_cells asegs m9 (OS + 128) cs) by (byAG IOSa8 AG9; apply (CL q); left; lia) end.
  assert (WID9 : rw_cells asegs m9 (OS + 160) [C8 (wz 0)]) by (byAG WID8 AG9; apply (CL q); left; lia).
  lazymatch type of IOSb8 with rw_cells _ _ _ ?cs => assert (IOSb9 : rw_cells asegs m9 (OS + 168) cs) by (byAG IOSb8 AG9; apply (CL q); left; lia) end.
  unfold sb_cellsA in SB9. glueZ WID9 IOSb9. glueZ IOSa9 WID9. glueZ SB9 IOSa9.
  lazymatch type of SB9 with rw_cells _ _ _ ?cs => pose proof (retype_fill4 m9 OS cs 30%nat FL HFL eq_refl SB9) as SB9x end. clear SB9. rename SB9x into SB9.
  cbv [firstn skipn app] in SB9. retype_at SB9 11%nat 1%nat [C4 (Z_to_bv 64 0x1002)].
  assert (OSU : OSX m9 OS (fill_after fill)).
  { rewrite HFA. exists pb', pp', ep', dum', j148, j284. split; [| exact PI7]. unfold os_cellsX, sb_cellsX, ios_cellsX. cbn [app]. exact SB9. }
  assert (PRES9 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> outside [(OS, OS + 288)] (bv_unsigned a) -> m9 a = m a).
  { intros a Ha Ho. rewrite <- (PRES8 a Ha Ho). apply (AG9 (fun x => x = bv_unsigned a)); [| reflexivity]. intros x ->. exact Ha. }
  assert (LB9 : LOCBA m9).
  { apply (LOCBA_agree m m9 LB). intros a Ha. apply PRES9; [apply (CL q); right; right; exact Ha|].
    cbn [outside]. unfold PJ_LOC_LO_A, PJ_LOC_HI_A, SEGTOP_A in *. split; [clear - Ha FLO FSEG; lia| exact I]. }
  assert (HULL9 : os_hullA m9 OS).
  { split; [apply rw_cells_forget in SB9; exact SB9|].
    eapply bytes_at_agree; [exact SHBY8|]. apply AG9. intros x Hx. rewrite repeat_length in Hx. unfold shad, SHB in Hx.
    apply (CL q). right; left. clear - Hx FLO FHI F0. Z.div_mod_to_equations. lia. }
  eapply (HK Σ3 x0 x1 x2 _ a2x d3 d4 d5 d6 d7 x3 x4 x5 x6 F7 m9 ART9 MI9 ST9 OSU HULL9 LB9);
    [rewrite LV9, LV2, LV1; reflexivity| exact FRS9| rewrite SP9, SP2, SP1; reflexivity| rewrite CR9; clear - CR2 CR1; lia| exact PRES9].
  }

  destruct FB as [(Efill & -> & -> & -> & ->) | (HFL & -> & -> & -> & ->)].
  {
  assert (SHZ3 : shz m3 OS 288).
  { change 288 with (8 * Z.of_nat 36). apply (shz_of_zero_run m3 OS 36); [clear - AL16; Z.div_mod_to_equations; lia| lia| exact SHBY3]. }
  assert (SHV3 : shz m3 PJ_NULSB_VT_A 24).
  { pose proof (shz_of_acc m3 PJ_NULSB_VT_A 24 (proj1 (VTACC Σ1 m3 ART3)) eq_refl ltac:(unfold PJ_NULSB_VT_A; lia)) as X. exact X. }
  pose proof (DCC Σ1 m3 ART3) as (VT3 & _ & _ & _ & _ & _ & GOT3). change (ro_cells asegs m3 PJ_NULSB_VT_A [C8 (wz PJ_XSPUTN_A); C8 (wz PJ_OVERFLOW_A); C8 (wz 8)]) in VT3.
  change (ro_cells asegs m3 PJ_GOT_CTYPE_ID_A [C8 (wz PJ_CTYPE_ID_A)]) in GOT3.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (op_segB q sp' f OS BUF N lo gp (wz TPV_A) w0 w1 w2 c4 c5 c6 c7 s6 s10 w3 w4 w5 w6 j0 j1 j2 j3 j4 j5 j6 j8 j9 jT j148 j284 (skipn 12 lS) F1 fc m3 LS4);
                   [lia| lia| exact FD8| lia| exact FSELF1| lia| lia| exact AL16| exact OF| exact OSH2| exact LOW'| lia| lia| lia| lia| lia| lia
                   | exact SHZ3| exact SHV3| exact ST3| exact FRl3| exact TMP3| exact FS3| exact IOS3| exact VT3| exact GOT3| exact MI3]|].
  cbv beta. intros ms4 (a5' & a6' & m4 & -> & MU4 & WM4 & MI4 & ST4 & FRl4 & TMP4 & FS4 & IOS4). apply evt_done.
  assert (ART4 : ART RT Σ1 m4).
  { apply (ARTW m3 m4 (sp' - 16) _ ART3 ltac:(clear - LOW LOR SPR; lia) MU4 WM4).
    fa1 ltac:(left; clear - SPR; lia). fa1 ltac:(left; clear - SPR; lia). fa1 ltac:(right; left; clear; lia). fa1 ltac:(right; right; left; clear; lia). apply Forall_nil. }
  assert (PRES4 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> outside [(OS, OS + 288)] (bv_unsigned a) -> m4 a = m a).
  { apply (PRESW m3 m4 _ PRES3 MU4).
    fa1 ltac:(left; clear - SPR LOR; lia). fa1 ltac:(left; clear - SPR LOR; lia). fa1 ltac:(right; left; clear; lia). fa1 ltac:(right; right; left; clear; lia). apply Forall_nil. }
  assert (AG4 : forall P : Z -> Prop, (forall x, P x -> ~ (sp' - 16 <= x < sp') /\ ~ (sp' + 16 <= x < sp' + 56) /\ ~ (f + 32 <= x < f + 40) /\ ~ (f / 8 + 2147450880 + 4 <= x < f / 8 + 2147450880 + 5)) ->
                 agree_on P m3 m4).
  { intros P HP a Ha. apply MU4. cbn [outside]. destruct (HP _ Ha) as (H1 & H2 & H3 & H4). repeat split; assumption. }
  assert (FRs4 : rw_cells asegs m4 (q - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)) by (byAG FRs3 AG4; clear - Hx FR1' SHT1 LOW LOR SPR; lia).
  assert (STp4 : stk asegs m4 (sp' + 88) (q - 104)) by (eapply stk_agree_nw; [exact STp3|]; apply AG4; intros x Hx; cbv beta in Hx; clear - Hx FR1' SHT1 LOW LOR SPR; lia).
  assert (FH4 : rw_cells asegs m4 f [C8 (wz 0x41b58ab3); C8 (wz 0x22601); C8 (wz 0xb80f4)]) by (byAG FH3 AG4; clear - Hx FLO FR1' LOW LOR SPR FSELF1; lia).
  lazymatch type of SEN3 with rw_cells _ _ _ ?cs => assert (SEN4 : rw_cells asegs m4 (f + 64) cs) by (byAG SEN3 AG4; clear - Hx FLO FR1' LOW LOR SPR FSELF1; lia) end.
  assert (SB4 : rw_cells asegs m4 OS (sb_cellsA pb (wz pp) (wz ep) dum)) by (byAG SB3 AG4; clear - Hx FLO FHI FTOP LOW LOR SPR OF OSH2; lia).
  assert (SHBY4 : bytes_at asegs m4 (OS / 8 + 2147450880) (repeat z8 36)).
  { eapply bytes_at_agree; [exact SHBY3|]. apply AG4. intros x Hx. rewrite repeat_length in Hx.
    clear - Hx OSLO LOR SPR OSH OF FD8 F0 FLO. repeat split; Z.div_mod_to_equations; lia. }
  assert (LB4 : LOCBA m4).
  { apply (LOCBA_agree m3 m4 LB3). apply AG4. intros x Hx. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx. clear - Hx LOW' LOR SPR FD8 FSEG1. unfold SEGTOP_A in *. lia. }
  clear AG4 MU4 WM4 FRl3 FH3 SEN3 FS3 FRs3 STp3 ST3 SB3 IOS3 SHBY3 MI3 TMP3 LB3 PRES3 SHZ3 SHV3 VT3 GOT3 ART3.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (use_facet_ctype_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc m4 lo (f + 32)); rewrite ?US;
                   [exact ST4| clear - LOR SPR; lia| clear - LOW'; lia| exact LB4| exact TMP4| lia| lia| left; clear - FR1' LOW LOR SPR; lia| right; unfold SEGTOP_A in FSEG1; clear - FSEG1; lia| exact MI4]|].
  cbv beta. intros ms5 (a1'' & a2'' & m5 & -> & MU5 & WM5 & MI5 & ST5 & LB5). rewrite US in MU5, ST5. rewrite (ret_pc_even 0xb8334) by lia. apply evt_done.
  assert (ART5 : ART RT Σ1 m5).
  { apply (ARTW m4 m5 (sp' - 48) _ ART4 ltac:(clear - LOW LOR SPR; lia) MU5 WM5). fa1 ltac:(left; clear - SPR; lia). apply Forall_nil. }
  assert (PRES5 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> outside [(OS, OS + 288)] (bv_unsigned a) -> m5 a = m a).
  { apply (PRESW m4 m5 _ PRES4 MU5). fa1 ltac:(left; clear - SPR LOR; lia). apply Forall_nil. }
  assert (AG5 : forall P : Z -> Prop, (forall x, P x -> ~ (sp' - 48 <= x < sp')) -> agree_on P m4 m5).
  { intros P HP a Ha. apply MU5. cbn [outside]. split; [exact (HP _ Ha)| exact I]. }
  assert (FRl5 : rw_cells asegs m5 sp' [CB 8 j0; CB 8 j1; C8 (wz (OS + 283)); C8 (wz BUF); C8 (wz (BUF + N)); C8 (wz OS); C8 (wz BUF); C8 (wz ((OS + 128) / 8 + 2147450880)); CB 8 j8; CB 8 j9; C8 (wz f)])
    by (byAG FRl4 AG5; lia).
  assert (FRs5 : rw_cells asegs m5 (q - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)) by (byAG FRs4 AG5; clear - Hx SPR; lia).
  assert (STp5 : stk asegs m5 (sp' + 88) (q - 104)) by (eapply stk_agree_nw; [exact STp4|]; apply AG5; intros x Hx; cbv beta in Hx; lia).
  assert (TMP5 : rw_cells asegs m5 (f + 32) [C8 (wz PJ_LOC_IMP_A)]) by (byAG TMP4 AG5; clear - Hx FR1' LOW LOR SPR; lia).
  assert (FH5 : rw_cells asegs m5 f [C8 (wz 0x41b58ab3); C8 (wz 0x22601); C8 (wz 0xb80f4)]) by (byAG FH4 AG5; clear - Hx FR1' LOW LOR SPR; lia).
  lazymatch type of SEN4 with rw_cells _ _ _ ?cs => assert (SEN5 : rw_cells asegs m5 (f + 64) cs) by (byAG SEN4 AG5; clear - Hx FR1' LOW LOR SPR; lia) end.
  assert (FS5 : rw_cells asegs m5 (f / 8 + 2147450880) (map C1 (op_sh12 0) ++ map (fun l => CB 1 l) (skipn 12 lS))).
  { eapply rw_cells_agree_nw; [exact FS4|]. apply AG5. intros x Hx. rewrite cells_size_app, cells_size_map_C1p, cells_size_map_CB1, LS4 in Hx.
    cbn [length op_sh12 app repeat Nat.add] in Hx. clear - Hx SHT1 LOW LOR SPR. lia. }
  assert (SB5 : rw_cells asegs m5 OS (sb_cellsA pb (wz pp) (wz ep) dum)) by (byAG SB4 AG5; clear - Hx FLO FHI FTOP LOW LOR SPR; lia).
  assert (IOS5 : rw_cells asegs m5 (OS + 128) (ios_midA OS 255 255 255 255 j148 j284)) by (byAG IOS4 AG5; clear - Hx FLO FHI FTOP LOW LOR SPR; lia).
  assert (SHBY5 : bytes_at asegs m5 (OS / 8 + 2147450880) (repeat z8 36)).
  { eapply bytes_at_agree; [exact SHBY4|]. apply AG5. intros x Hx. rewrite repeat_length in Hx. clear - Hx OSLO LOR SPR. lia. }
  clear AG5 MU5 WM5 FRl4 FH4 SEN4 FS4 FRs4 STp4 ST4 SB4 IOS4 SHBY4 MI4 TMP4 LB4 PRES4 ART4.

  assert (SHF5 : shz m5 PJ_CTYPE_FACET_A 8).
  { pose proof (af_acc_static RT AF Σ1 m5 PJ_CTYPE_FACET_A 8 ART5 ltac:(unfold PJ_CTYPE_FACET_A; lia)
                 ltac:(intros i Hi; unfold PJ_CTYPE_FACET_A; split; [apply client_static_intro; lia| lia])) as AC.
    pose proof (shz_of_acc m5 _ 8 AC eq_refl ltac:(unfold PJ_CTYPE_FACET_A; lia)) as X. exact X. }
  assert (SHW5 : shz m5 PJ_WIDEN_SLOT_A 8) by (pose proof (shz_of_acc m5 _ 8 (proj2 (VTACC Σ1 m5 ART5)) eq_refl ltac:(unfold PJ_WIDEN_SLOT_A; lia)) as X; exact X).
  pose proof (DCC Σ1 m5 ART5) as (_ & WRO5 & _). change (ro_cells asegs m5 PJ_WIDEN_SLOT_A [C8 (wz PJ_DO_WIDEN_A)]) in WRO5.
  pose proof LB5 as (l1 & l2 & l3 & l4 & l5 & l6 & l7 & l8 & l9 & l10 & l11 & l12 & l13 & l14 & l15 & LBC). unfold locb_cellsA, PJ_LOC_LO_A in LBC.
  takeZ LBC 19%nat 0x6a6bc8 LBpre. clear LBpre. takeZ LBC 1%nat 0x6a6bd0 FACV. clear LBC.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (op_segC q sp' f OS BUF N lo gp (wz TPV_A) w0 w1 w2 a1'' a2'' a5' a6' c7 w3 w4 w5 w6 j0 j1 j8 j9 j148 j284 (skipn 12 lS) F1 fc m5 LS4);
                   [lia| lia| exact FD8| lia| exact FSELF1| lia| lia| exact AL16| exact OSLO| exact OF| exact OSH2| exact OSELF| exact LOW'| lia| lia| lia| lia| lia| lia
                   | exact SHF5| exact SHW5| exact SHBY5| exact FACV| exact WRO5| exact FRl5| exact TMP5| exact FS5| exact IOS5| exact MI5]|].
  cbv beta. intros ms6 (m6 & -> & MU6 & WM6 & MI6 & FRl6 & FS6 & IOS6). apply evt_done.
  assert (ART6 : ART RT Σ1 m6).
  { apply (ARTW m5 m6 sp' _ ART5 ltac:(clear - LOW LOR SPR; lia) MU6 WM6).
    fa1 ltac:(left; clear - SPR; lia). fa1 ltac:(right; right; left; clear; lia). fa1 ltac:(right; right; right; clear - FLO FHI; lia). apply Forall_nil. }
  assert (PRES6 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> outside [(OS, OS + 288)] (bv_unsigned a) -> m6 a = m a).
  { apply (PRESW m5 m6 _ PRES5 MU6). fa1 ltac:(left; clear - SPR LOR; lia). fa1 ltac:(right; right; left; clear; lia). fa1 ltac:(right; right; right; clear; lia). apply Forall_nil. }
  assert (AG6 : forall P : Z -> Prop, (forall x, P x -> ~ (sp' + 8 <= x < sp' + 16) /\ ~ (f / 8 + 2147450880 + 4 <= x < f / 8 + 2147450880 + 5) /\ ~ (OS + 280 <= x < OS + 284)) -> agree_on P m5 m6).
  { intros P HP a Ha. apply MU6. cbn [outside]. destruct (HP _ Ha) as (H1 & H2 & H3). repeat split; assumption. }
  assert (FRs6 : rw_cells asegs m6 (q - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)) by (byAG FRs5 AG6; clear - Hx FR1' SHT1 LOW LOR SPR FLO FHI FTOP; lia).
  assert (STp6 : stk asegs m6 (sp' + 88) (q - 104)) by (eapply stk_agree_nw; [exact STp5|]; apply AG6; intros x Hx; cbv beta in Hx; clear - Hx FR1' SHT1 LOW LOR SPR FLO FHI FTOP; lia).
  assert (ST6 : stk asegs m6 lo sp') by (eapply stk_agree_nw; [exact ST5|]; apply AG6; intros x Hx; cbv beta in Hx; clear - Hx FR1' SHT1 LOW LOR SPR FLO FHI FTOP; lia).
  assert (FH6 : rw_cells asegs m6 f [C8 (wz 0x41b58ab3); C8 (wz 0x22601); C8 (wz 0xb80f4)]) by (byAG FH5 AG6; clear - Hx FLO FR1' LOW LOR SPR FSELF1 OF; lia).
  lazymatch type of SEN5 with rw_cells _ _ _ ?cs => assert (SEN6 : rw_cells asegs m6 (f + 64) cs) by (byAG SEN5 AG6; clear - Hx FLO FR1' LOW LOR SPR FSELF1 OF; lia) end.
  assert (SB6 : rw_cells asegs m6 OS (sb_cellsA pb (wz pp) (wz ep) dum)) by (byAG SB5 AG6; clear - Hx FLO FHI FTOP LOW LOR SPR OSH2; lia).
  assert (SHBY6 : bytes_at asegs m6 (OS / 8 + 2147450880) (repeat z8 36)).
  { eapply bytes_at_agree; [exact SHBY5|]. apply AG6. intros x Hx. rewrite repeat_length in Hx.
    clear - Hx OSLO LOR SPR OF OSELF FD8 F0 FLO. repeat split; Z.div_mod_to_equations; lia. }
  clear AG6 MU6 WM6 FRl5 FH5 SEN5 FS5 FRs5 STp5 ST5 SB5 IOS5 SHBY5 MI5 TMP5 LB5 PRES5 ART5 SHF5 SHW5 WRO5 FACV.
  eapply TAIL; [exact FRl6| reflexivity| lia| rewrite Efill; reflexivity| exact ART6| exact PRES6| exact FRs6| exact STp6| exact ST6| exact FH6| exact SEN6
    | exact SB6| exact SHBY6| exact IOS6| exact FS6| exact MI6]. }

  assert (SHZ3 : shz m3 OS 288).
  { change 288 with (8 * Z.of_nat 36). apply (shz_of_zero_run m3 OS 36); [clear - AL16; Z.div_mod_to_equations; lia| lia| exact SHBY3]. }
  assert (SHV3 : shz m3 PJ_NULSB_VT_A 24).
  { pose proof (shz_of_acc m3 PJ_NULSB_VT_A 24 (proj1 (VTACC Σ1 m3 ART3)) eq_refl ltac:(unfold PJ_NULSB_VT_A; lia)) as X. exact X. }
  pose proof (DCC Σ1 m3 ART3) as (VT3 & _ & _ & _ & _ & _ & GOT3). change (ro_cells asegs m3 PJ_NULSB_VT_A [C8 (wz PJ_XSPUTN_A); C8 (wz PJ_OVERFLOW_A); C8 (wz 8)]) in VT3.
  change (ro_cells asegs m3 PJ_GOT_CTYPE_ID_A [C8 (wz PJ_CTYPE_ID_A)]) in GOT3.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (op_segB2 fill q sp' f OS BUF N lo gp (wz TPV_A) w0 w1 w2 c4 c5 c6 c7 s6 s10 w3 w4 w5 w6 j0 j1 j2 j3 j4 j5 j6 j8 j9 jT j148 j284 (skipn 12 lS) F1 fc m3 LS4);
                   [lia| lia| exact FD8| lia| exact FSELF1| lia| lia| exact AL16| exact OF| exact OSH2| exact LOW'| lia| lia| lia| lia| lia| lia| exact HFL| exact SHZ3| exact SHV3| exact ST3| exact FRl3| exact TMP3| exact FS3| exact IOS3| exact VT3| exact GOT3| exact MI3]|].
  cbv beta. intros ms4 (a6' & m4 & -> & MU4 & WM4 & MI4 & ST4 & FRl4 & TMP4 & FS4 & IOS4). apply evt_done.
  assert (ART4 : ART RT Σ1 m4).
  { apply (ARTW m3 m4 (sp' - 16) _ ART3 ltac:(clear - LOW LOR SPR; lia) MU4 WM4). fa1 ltac:(left; clear - SPR; lia). apply Forall_nil. }
  assert (PRES4 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> outside [(OS, OS + 288)] (bv_unsigned a) -> m4 a = m a).
  { apply (PRESW m3 m4 _ PRES3 MU4). fa1 ltac:(left; clear - SPR LOR; lia). apply Forall_nil. }
  assert (AG4 : forall P : Z -> Prop, (forall x, P x -> ~ (sp' - 16 <= x < sp')) -> agree_on P m3 m4).
  { intros P HP a Ha. apply MU4. cbn [outside]. split; [exact (HP _ Ha)| exact I]. }
  assert (FRs4 : rw_cells asegs m4 (q - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)) by (byAG FRs3 AG4; clear - Hx SPR; lia).
  assert (STp4 : stk asegs m4 (sp' + 88) (q - 104)) by (eapply stk_agree_nw; [exact STp3|]; apply AG4; intros x Hx; cbv beta in Hx; lia).
  lazymatch type of FH3 with rw_cells _ _ _ ?cs => assert (FH4 : rw_cells asegs m4 f cs) by (byAG FH3 AG4; clear - Hx FR1' LOW LOR SPR; lia) end.
  lazymatch type of SEN3 with rw_cells _ _ _ ?cs => assert (SEN4 : rw_cells asegs m4 (f + 64) cs) by (byAG SEN3 AG4; clear - Hx FR1' LOW LOR SPR; lia) end.
  assert (SB4 : rw_cells asegs m4 OS (sb_cellsA pb (wz pp) (wz ep) dum)) by (byAG SB3 AG4; clear - Hx FLO FHI FTOP LOW LOR SPR; lia).
  assert (SHBY4 : bytes_at asegs m4 (OS / 8 + 2147450880) (repeat z8 36)).
  { eapply bytes_at_agree; [exact SHBY3|]. apply AG4. intros x Hx. rewrite repeat_length in Hx. clear - Hx OSLO LOR SPR. lia. }
  eapply TAIL; [exact FRl4| reflexivity| exact HFL| exact (fill_after_set fill HFL)| exact ART4| exact PRES4| exact FRs4| exact STp4| exact ST4| exact FH4| exact SEN4
    | exact SB4| exact SHBY4| exact IOS4| exact FS4| exact MI4].
Qed.
End Put.
