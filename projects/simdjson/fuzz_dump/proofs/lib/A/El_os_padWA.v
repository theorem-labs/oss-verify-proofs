(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep ZBridge.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Startup_glue Sj_stage1_kit Pj_loc_kit Pj_os_kit El_os_pad.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.A Require Import Layout Shadow RT_iface RT_iface2 RT_iface3 IcptSpec D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps
     Sj_hkit Sj_new Sj_num_akit Sj_num_amem Sj_num_aframe Atp_fzwA Pj_lftoi1A Pj_rtkA Pj_defsA Pj_cpsA Pj_os_defsA Pj_os_put1A Pj_os_put2A Pj_os_put3A.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.A Require Import I_consts I_qck R_m2s F_achk.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.A Require Import Atp_defsA Atp_objkA.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.A Require Import El_os_xsputnLA El_os_pad3A El_os_pad4A.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.A Require Export El_os_defsA.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import StoreFast.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Section Stmt.
Variable RT : rt_sig.
Variable PMc : Model -> Prop.
Definition EL_PADW_STACK_A : Z := 176 + EL_XSPUTN_DEPTH + RT_STACK.
Definition padW_cpsA : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (OS BUF N CAP S lo fO FILL W pp ep : Z) (kO : nat) (pb : word) (dum bs : list byte)
         (ra gp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  fdfs_only PMc -> mat_stable PMc ->
  In (fO, kO) (rt_frames RT Σ) -> fO <= OS -> OS + 288 <= fO + fs_size kO - 8 -> OS mod 16 = 0 ->
  rw_cells asegs m OS (sb_cellsA pb (wz pp) (wz ep) dum) -> PUTINV OS pp ep -> rw_cells asegs m (OS + 160) [C8 (wz W)] -> os_hullA m OS ->
  bytes_at asegs m BUF bs -> Z.of_nat (length bs) = CAP -> 0 <= N <= CAP -> CAP <= 2^40 -> 0 < BUF -> acc asegs m BUF N -> srcA RT Σ S BUF CAP bs ->
  (BUF + CAP <= OS \/ OS + 288 <= BUF) -> 0 <= FILL < 256 -> 0 < N -> N < W -> W <= 22 ->
  ART RT Σ m -> mem_inv asegs m -> stk asegs m lo S -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + EL_PADW_STACK_A <= S ->
  S + 16 <= USTACK_TOP -> S mod 16 = 0 ->
  Z.of_nat (length (rt_frames RT Σ)) + 1 <= FRAMES_TOT -> 1 <= rt_credit RT Σ ->
  (forall (Σ' : rts RT) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m' (pb' : word) (pp' ep' : Z) (dum' : list byte),
     ART RT Σ' m' -> mem_inv asegs m' -> stk asegs m' lo S -> os_hullA m' OS ->
     rw_cells asegs m' OS (sb_cellsA pb' (wz pp') (wz ep') dum') -> PUTINV OS pp' ep' -> rw_cells asegs m' (OS + 160) [C8 (wz 0)] ->
     rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_credit RT Σ - 1 <= rt_credit RT Σ' ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) S [(OS + 40, OS + 128); (OS + 160, OS + 168)] m m' ->
     aevt RT PMc Σ' K (MS (mkR ra (wz S) gp (wz TPV_A) t0' t1' t2' s0 s1 (wz OS) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                         F' (ret_pc ra) fc None m' (seg_rom asegs))) ->
  aevt RT PMc Σ K (MS (mkR ra (wz S) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz OS) (wz BUF) (wz BUF) (wz (BUF + N)) (wz (OS + 136)) (wz FILL) a6 a7
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (wz PJ_PADOUT_A) fc None m (seg_rom asegs)).
End Stmt.

Section Pad.
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
Local Notation XSP := (xsputnX_aevt RT AF RIP AF_IC AF_SHW DCC PMc FDO MST).

Lemma vt_accA : forall Σ m, ART RT Σ m -> acc asegs m PJ_NULSB_VT_A 24 /\ acc asegs m PJ_WIDEN_SLOT_A 8.
Proof using AF.
  intros Σ m H. split; (apply (acc_lit RT AF Σ m _ _ H); unfold ACC_LITS, PJ_NULSB_VT_A, PJ_WIDEN_SLOT_A; cbn [In]; repeat (first [left; reflexivity | right])).
Qed.
Local Notation VTACC := vt_accA.

Local Ltac ul := unfold EL_PADW_STACK_A, EL_XSPUTN_DEPTH, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Theorem padW_okA : padW_cpsA RT PMc.
Proof using AF RC RC2 FDO MST RIP AF_IC AF_SHW DCC.
  unfold padW_cpsA. intros until m. intros FDO' MST' INF FLO FHI AL16 SB PI WID HULL SRC LB NR CAP40 B0 ACC SK SEP FIR NPOS NW W22 ART0 MI ST LOW LOR SPT S16 FRB CRB HK.
  pose proof (af_frames_range RT AF Σ m fO kO ART0 INF) as (F0 & FTOP & _ & FLIVE).
  pose proof (af_frames_align RT AF Σ m fO kO ART0 INF) as (_ & FSEG).
  pose proof (proj2 (af_fshadow_apart RT AF Σ m fO kO ART0 INF) fO kO INF) as FSELF.
  pose proof (fframe_ranges RT AF Σ m fO kO ART0 INF) as (_ & _ & _ & _ & SHT).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  unfold EL_PADW_STACK_A, EL_XSPUTN_DEPTH in *. unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *. remember (fs_size kO) as FSZ eqn:EFSZ.
  pose proof (af_frames_hi RT AF Σ m fO kO ART0 INF) as FHIo. rewrite <- EFSZ in FHIo. unfold shad, SHB in FSELF.
  assert (US : bv_unsigned (wz S) = S) by (apply unsigned_lit; lia).
  assert (EO : bv_unsigned (wz OS) = OS) by (apply unsigned_lit; lia).
  assert (LBS : length bs = Z.to_nat CAP) by lia.
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W0.
  assert (RPP : 0 <= pp < 2^63 /\ 0 <= ep < 2^63) by (pose proof PI as [[P1 P2]|[P1 P2]]; clear - P1 P2 FLO FHI FTOP F0 SP0R EFSZ; lia).
  assert (BHI : BUF + CAP <= 2^47).
  { destruct SK as [(RB & B1 & B2 & _)|[(B1 & B2)|[(fB & kB & INB & B1 & B2)|(pB & nB & INP & B1 & B2)]]]; [lia| unfold USTACK_TOP in B2; lia| |].
    - pose proof (fframe_ranges RT AF Σ m fB kB ART0 INB) as (_ & Y1 & _). unfold STACK_WIN in Y1. clear - Y1 B2 SP0R. lia.
    - pose proof (af_live_range RT AF Σ m pB nB ART0 INP) as (_ & Y1 & _). unfold STACK_WIN in Y1. clear - Y1 B2 SP0R. lia. }
  destruct HULL as [(bo & FO) SHBY].

  destruct (pad_walk0X S lo OS BUF N FILL ra gp (wz TPV_A) t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a6 a7 t3 t4 t5 t6 F fc m ST ltac:(lia) ltac:(lia) ltac:(lia) S16 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              (af_client_consts RT AF Σ m ART0) MI) as (sp2 & SP2R & SP2M & W0).
  assert (S0 : 0 <= sp2) by (destruct ST; lia).
  assert (US2 : bv_unsigned (wz (sp2)) = sp2) by (apply unsigned_lit; lia).
  apply (aevt_evt RT AF PMc MST). eapply evt_cut; [exact W0|]. cbv beta. intros ms1 (m1 & a1' & a2' & j0 & j1 & j2 & j4 & j5 & j6 & -> & MU1 & WM1 & MI1 & ST1 & FRl1 & STp1 & FRs1). apply evt_done. clear W0.
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 sp2 ART0 ltac:(ul)); [| exact WM1].
    intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. ul. }
  assert (PRES1 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) S (bv_unsigned a) -> m1 a = m a).
  { intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. destruct (aclient_split_c RT AF Σ m S _ ART0 Ha); ul. }

  unfold entry_st.
  eapply (aevt_smalloc1 RT PMc FDO MST RC2 Σ); [reflexivity| unfold FRAMES_MAX2, FRAMES_TOT in *; lia| lia| exact ART1| exact MI1| | intros Efr0; exfalso; rewrite Efr0 in INF; exact INF |].
  { unfold call_ok. rewrite US2. split; [exact ST1|]. split; [ul|]. split; [ul|]. split; [ul| Z.div_mod_to_equations; lia]. }
  intros Σ1 f w0 w1 w2 c1 c2 c3 c4 c5 c6 c7 w3 w4 w5 w6 F1 m2 (ART2 & MI2 & WM2 & ST2) PRES2 WRF WRS FRS1 LV1 SP1 CR1 FPOS F64 FTOP1.
  rewrite US2 in ST2, PRES2. rewrite (ret_pc_even 0xb11b8) by lia.
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
  assert (FD8 : 0xd8200 <= f / 8) by (unfold SEGTOP_A in FSEG1; clear - SP2R SP2M FSEG1; Z.div_mod_to_equations; lia).
  assert (LOW' : 0x7fff7f800000 <= lo) by (clear - SP2R SP2M SP0W LOW; lia). unfold SEGTOP_A, STACK_WIN, USTACK_TOP in *.

  assert (AG02 : forall (P : Z -> Prop), (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) S x /\ ~ (sp2 <= x < S)) -> agree_on P m m2).
  { intros P HP a Ha. destruct (HP _ Ha) as [H1 H2]. rewrite (PRES2 a); [exact (PRES1 a H1)|].
    apply (aclient_mono _ _ _ _ _ _ _ H1); [auto| auto| lia]. }
  assert (AG12 : forall (P : Z -> Prop), (forall x, P x -> sp2 <= x < S) -> agree_on P m1 m2).
  { intros P HP a Ha. apply PRES2. left. pose proof (HP _ Ha). ul. }
  assert (CL : forall sp' x, (fO <= x < fO + FSZ - 8) \/ (fO / 8 + 2147450880 <= x < (fO + FSZ) / 8 + 2147450880) ->
            aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x).
  { intros sp' x [H|H]; [right; right; right; left| do 4 right]; [exists fO, kO; rewrite <- EFSZ; split; [exact INF| exact H]
      | exists fO, kO; rewrite <- EFSZ; split; [exact INF| unfold shad, SHB; exact H]]. }

  assert (SRCT : forall mx : mem, mem_inv asegs mx -> (forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) S (bv_unsigned a) -> outside [(OS + 40, OS + 128)] (bv_unsigned a) -> mx a = m a) -> bytes_at asegs mx BUF bs).
  { intros mx MIx PRx. destruct SK as [(RB & B1 & B2 & _)|[(B1 & B2)|[(fB & kB & INB & B1 & B2)|(pB & nB & INP & B1 & B2)]]].
    - apply (ro_bytes_at asegs mx BUF bs MIx); [lia| rewrite LBS; lia| exact RB].
    - eapply bytes_at_agree; [exact SRC|]. intros a Ha. rewrite LBS in Ha. apply PRx; [left; lia| cbn [outside]; split; [clear - Ha SEP; lia| exact I]].
    - eapply bytes_at_agree; [exact SRC|]. intros a Ha. rewrite LBS in Ha. apply PRx; [right; right; right; left; exists fB, kB; split; [exact INB| lia]| cbn [outside]; split; [clear - Ha SEP; lia| exact I]].
    - eapply bytes_at_agree; [exact SRC|]. intros a Ha. rewrite LBS in Ha. apply PRx; [right; right; left; exists pB, nB; split; [exact INP| lia]| cbn [outside]; split; [clear - Ha SEP; lia| exact I]].     }
  assert (ACCT : forall (Σx : rts RT) (mx : mem), ART RT Σx mx -> rt_live RT Σx = rt_live RT Σ -> rt_sp0 RT Σx = rt_sp0 RT Σ ->
            (forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) S (bv_unsigned a) -> outside [(OS + 40, OS + 128)] (bv_unsigned a) -> mx a = m a) -> acc asegs mx BUF N).
  { intros Σx mx ARTx LVx SPx PRx. destruct SK as [(RB & B1 & B2 & (la & ln & INL & L1 & L2))|[(B1 & B2)|[(fB & kB & INB & B1 & B2)|(pB & nB & INP & B1 & B2)]]].
    - apply (acc_sub asegs mx la ln); [exact (acc_lit RT AF Σx mx la ln ARTx INL)| lia| lia].
    - apply (af_acc_stack RT AF Σx mx BUF N ARTx); [rewrite SPx; ul| ul].
    - apply (acc_agreeP m mx BUF N ACC). intros a Ha. pose proof (fframe_ranges RT AF Σ m fB kB ART0 INB) as (Y0 & Y1 & _). apply PRx.
      + do 4 right. exists fB, kB. split; [exact INB|]. unfold shad, SHB in *. clear - SP2R SP2M Ha B1 B2 NR Y0. Z.div_mod_to_equations. lia.
      + cbn [outside]. split; [| exact I]. unfold shad, SHB in *. clear - Ha FHIo FLO FHI B1 B2 Y0 Y1 NR SP0R. unfold STACK_WIN in *. Z.div_mod_to_equations. lia.
    - apply (acc_sub asegs mx pB nB); [exact (proj2 (af_acc_live RT AF Σx mx pB nB ARTx ltac:(rewrite LVx; exact INP)))| clear - B1; lia| clear - B2 NR; lia].     }
  assert (FRl2 : rw_cells asegs m2 sp2 (pad_locals0 j0 j1 j2 (BUF + N) j4 j5 j6)).
  { eapply rw_cells_agree_nw; [exact FRl1|]. apply AG12. intros x Hx. unfold pad_locals0 in Hx. cbn [cells_size csize Nat.add] in Hx. lia. }
  assert (FRs2 : rw_cells asegs m2 (S - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { eapply rw_cells_agree_nw; [exact FRs1|]. apply AG12. intros x Hx. unfold fa_saved in Hx. cbn [cells_size csize Nat.add] in Hx. lia. }
  assert (STp2 : stk asegs m2 (sp2 + 56) (S - 104)) by (eapply stk_agree_nw; [exact STp1|]; apply AG12; intros x Hx; cbv beta in Hx; lia).
  assert (SB2 : rw_cells asegs m2 OS (sb_cellsA pb (wz pp) (wz ep) dum)).
  { eapply rw_cells_agree_nw; [exact SB|]. apply AG02. intros x Hx. unfold sb_cellsA in Hx. cbn [cells_size csize Nat.add] in Hx.
    split; [apply (CL S); left; lia| clear - SP2R SP2M Hx FHI FTOP LOW LOR; lia]. }
  assert (WID2 : rw_cells asegs m2 (OS + 160) [C8 (wz W)]).
  { eapply rw_cells_agree_nw; [exact WID|]. apply AG02. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [apply (CL S); left; lia| clear - SP2R SP2M Hx FHI FTOP LOW LOR; lia]. }
  assert (FO2 : rw_cells asegs m2 OS [CB 288 bo]).
  { eapply rw_cells_agree_nw; [exact FO|]. apply AG02. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [apply (CL S); left; lia| clear - SP2R SP2M Hx FHI FTOP LOW LOR; lia]. }
  assert (SHBY2 : bytes_at asegs m2 (shad OS) (repeat z8 36)).
  { eapply bytes_at_agree; [exact SHBY|]. apply AG02. intros x Hx. rewrite repeat_length in Hx. unfold shad, SHB in *.
    split; [apply (CL S); right| clear - SP2R SP2M Hx FLO FHI SHT LOW LOR]; Z.div_mod_to_equations; lia. }
  assert (PRES2' : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) S (bv_unsigned a) -> m2 a = m a).
  { intros a Ha. apply AG02 with (P := fun x => x = bv_unsigned a); [| reflexivity]. intros x ->. split; [exact Ha|].
    destruct (aclient_split_c RT AF Σ m S _ ART0 Ha); ul. }
  clear PRES1 PRES2 AG12 AG02 FRl1 FRs1 STp1 ST1 MI1 ART1 MU1 WM1 SB WID FO SHBY.

  destruct (wr_at_rw_CB m2 f 24 (wr_at_sub m2 f 120 f 24 WRF ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jH & FH2).
  change (Z.to_nat 24) with 24%nat in FH2.
  apply (rw_cells_split_CB asegs _ _ [] 24 _ [] [8; 8; 8]%nat) in FH2; [| reflexivity]. cbn [mk_CB_cells app] in FH2. forget_junk FH2.
  destruct (wr_at_rw_CB m2 (f + 32) 24 (wr_at_sub m2 f 120 (f + 32) 24 WRF ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jO & FOBJ2). change (Z.to_nat 24) with 24%nat in FOBJ2.
  destruct (wr_at_rw_CB m2 (f / 8 + 2147450880) 16 WRS ltac:(lia)) as (jS & FS2).
  change (Z.to_nat 16) with 16%nat in FS2.
  apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1]%nat) in FS2; [| reflexivity]. cbn [mk_CB_cells app] in FS2.
  lazymatch type of FS2 with rw_cells _ _ _ ?cs =>
    let ls := eval cbv in (map (fun c => match c with CB _ l => l | _ => [] end) cs) in
    change (rw_cells asegs m2 (f / 8 + 2147450880) (map (fun l => CB 1 l) ls)) in FS2; set (lS := ls) in FS2;
    assert (LS : length lS = 16%nat) by reflexivity; clearbody lS
  end.

  apply (rw_cells_split_CB asegs _ _ [] 288 _ [] [128; 32; 8; 120]%nat) in FO2; [| reflexivity]. cbn [mk_CB_cells app] in FO2. forget_junk FO2.
  takeZ FO2 1%nat (OS + 128)%Z FOa. clear FOa. takeZ FO2 1%nat (OS + 160)%Z HX2. takeZ FO2 1%nat (OS + 168)%Z FOb. clear FOb. rename FO2 into HY2.

  assert (CSEP : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) S a -> ~ (f <= a < f + 120) /\ ~ (f / 8 + 2147450880 <= a < f / 8 + 2147450880 + 16)).
  { intros a Ha. destruct Ha as [H|[H|[H|[H|H]]]].
    - clear - SP2R SP2M H FR1' SHT1 LOW LOR. unfold USTACK_TOP in H. split; intros X; lia.
    - pose proof (client_static_range _ H) as R. unfold SEGTOP_A in R. clear - SP2R SP2M R FSEG1 SHB1. split; intros X; lia.
    - destruct H as (p & k & Hin & Hr). pose proof (proj2 (proj2 (proj2 (af_frames_range RT AF Σ1 m2 f 1%nat ART2 INF1))) p k ltac:(rewrite LV1; exact Hin)) as Y1.
      pose proof (FSL1 p k ltac:(rewrite LV1; exact Hin)) as Y2. change (fs_size 1) with 128 in Y1. clear - SP2R SP2M Hr Y1 Y2. split; intros X; lia.
    - destruct H as (f9 & k9 & Hin & Hr). pose proof (af_frames_disj RT AF Σ1 m2 f 1 f9 k9 [] (rt_frames RT Σ) ART2 FRS1 Hin) as Y1.
      pose proof (FSF1 f9 k9 ltac:(rewrite FRS1; right; exact Hin)) as Y2. unfold shad, SHB in Y2. change (fs_size 1) with 128 in Y1.
      pose proof (fframe_ranges RT AF Σ m f9 k9 ART0 Hin) as (_ & _ & Y3 & _). clear - SP2R SP2M Hr Y1 Y2 Y3. split; intros X; lia.
    - destruct H as (f9 & k9 & Hin & Hr). pose proof (proj2 (af_fshadow_apart RT AF Σ1 m2 f9 k9 ART2 ltac:(rewrite FRS1; right; exact Hin)) f 1%nat INF1) as Y1.
      pose proof (af_frames_disj RT AF Σ1 m2 f 1 f9 k9 [] (rt_frames RT Σ) ART2 FRS1 Hin) as Y2. change (fs_size 1) with 128 in Y1, Y2.
      unfold shad, SHB in Hr, Y1. clear - SP2R SP2M Hr Y1 Y2 FD0. split; intros X; Z.div_mod_to_equations; lia. }

  assert (EXIT : forall (mx : mem) (xra xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt0 xt1 xt2 xt3 xt4 xt5 xt6 xs7 xs8 xs9 : word) (Fx : bvmap 5 word) (pb' : word) (pp' ep' : Z) (dum' hx hy : list byte),
    PUTINV OS pp' ep' -> ART RT Σ1 mx -> mem_inv asegs mx -> stk asegs mx lo sp2 ->
    rw_cells asegs mx sp2 [C8 (wz ((OS + 160) / 8 + 2147450880)); C8 (wz BUF); C8 (wz (OS / 8)); C8 (wz (BUF + N)); CB 8 j4; CB 8 j5; C8 (wz f)] ->
    stk asegs mx (sp2 + 56) (S - 104) -> rw_cells asegs mx (S - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells asegs mx OS (sb_cellsA pb' (wz pp') (wz ep') dum') -> rw_cells asegs mx (OS + 128) [CB 32 hx] -> rw_cells asegs mx (OS + 160) [C8 (wz W)] ->
    rw_cells asegs mx (OS + 168) [CB 120 hy] -> bytes_at asegs mx (OS / 8 + 2147450880) (repeat z8 36) ->
    rw_cells asegs mx f [C8 (wz 0x41b58ab3); C8 (wz 0x16a1c); C8 (wz 0xb1134)] ->
    rw_cells asegs mx (f / 8 + 2147450880) (map C1 pad_sh12 ++ map (fun l => CB 1 l) (skipn 12 lS)) ->
    (forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) S (bv_unsigned a) -> outside [(OS + 40, OS + 128); (OS + 160, OS + 168)] (bv_unsigned a) -> mx a = m a) ->
    aevt RT PMc Σ1 K (MS (mkR xra (wz sp2) gp (wz TPV_A) xt0 xt1 xt2 (wz S) (wz sp2) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                            (wz f) (wz OS) (wz 2147450880) (wz N) (wz (OS + 160)) xs7 xs8 xs9 (wz (f / 8 + 2147450880)) (wz f) xt3 xt4 xt5 xt6)
                       Fx (wz 0xb13d4) fc None mx (seg_rom asegs))).
  { intros mx xra xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt0 xt1 xt2 xt3 xt4 xt5 xt6 xs7 xs8 xs9 Fx pb' pp' ep' dum' hx hy PIx ARTx MIx STx FRlx STpx FRsx SBx HXx WIDx HYx SHx FHx FSx PRESx.
    takeZ FHx 1%nat (f + 8)%Z FH0. clear FHx.
    apply (aevt_evt RT AF PMc MST).
    takeZ FRlx 1%nat (sp2 + 8)%Z L0.
    eapply evt_cut; [eapply (pad_exit1W S sp2 f lo OS N W xra gp (wz TPV_A) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs7 xs8 xs9 xt3 xt4 xt5 xt6 _ pad_sh12 (skipn 12 lS) Fx fc mx);
                     [reflexivity| rewrite length_skipn, LS; reflexivity| lia| lia| lia| lia| exact FSELF1| lia| lia| | | lia| lia| lia| lia| | exact L0| exact WIDx| exact FH0| exact FSx| exact MIx]|].
    { clear - SP2R SP2M FDJ FLO FHI. lia. }
    { clear - SP2R SP2M FSO1 FLO FHI. lia. }
    { change 288 with (8 * Z.of_nat 36). apply (shz_of_zero_run mx OS 36); [clear - SP2R SP2M AL16; Z.div_mod_to_equations; lia| lia| exact SHx]. }
    cbv beta. intros ms4 (m4 & -> & MU4 & WM4 & MI4 & WID4 & FH4 & FS4).
    assert (AG4 : forall P : Z -> Prop, (forall x, P x -> ~ (OS + 160 <= x < OS + 168) /\ ~ (f <= x < f + 8) /\ ~ (f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 16)) -> agree_on P mx m4).
    { intros P HP a Ha. apply MU4. cbn [outside]. destruct (HP _ Ha) as (H1 & H2 & H3). split; [exact H1| split; [exact H2| split; [exact H3| exact I]]]. }
    assert (ART4 : ART RT Σ1 m4).
    { apply (art_client_write RT AF Σ1 mx m4 sp2 ARTx ltac:(ul)); [| exact WM4]. intros a Ha. apply MU4. cbn [outside].
      split; [intros Hin; apply Ha; right; right; right; left; exists fO, kO; split; [exact INO1| lia]|].
      split; [intros Hin; apply Ha; right; right; right; left; exists f, 1%nat; split; [exact INF1| change (fs_size 1) with 128; lia]|].
      split; [| exact I]. intros Hin; apply Ha. do 4 right. exists f, 1%nat. split; [exact INF1|]. unfold shad, SHB. change (fs_size 1) with 128. clear - SP2R SP2M Hin FD0. Z.div_mod_to_equations. lia. }
    destruct (af_frame_release RT AF Σ1 m4 f 1%nat (rt_frames RT Σ) ART4 FRS1) as (Σ3 & fl & FLC & NAC & FL0 & FLW & FW & REL).
    change (fs_size 1) with 128 in FW. replace (f + 128 - 8) with (f + 120) in FW by lia. rewrite SP1 in FLW.
    assert (FRl4 : rw_cells asegs m4 (sp2 + 8) [C8 (wz BUF); C8 (wz (OS / 8)); C8 (wz (BUF + N)); CB 8 j4; CB 8 j5; C8 (wz f)]).
    { eapply rw_cells_agree_nw; [exact FRlx|]. apply AG4. intros x Hx. cbn [cells_size csize Nat.add] in Hx. clear - SP2R SP2M Hx FLO FHI FTOP LOW LOR FR1' SHT1. lia. }
    assert (L04 : rw_cells asegs m4 sp2 [C8 (wz ((OS + 160) / 8 + 2147450880))]).
    { eapply rw_cells_agree_nw; [exact L0|]. apply AG4. intros x Hx. cbn [cells_size csize Nat.add] in Hx. clear - SP2R SP2M Hx FLO FHI FTOP LOW LOR FR1' SHT1. lia. }
    glueZ L04 FRl4.
    assert (STp4 : stk asegs m4 (sp2 + 56) (S - 104)) by (eapply stk_agree_nw; [exact STpx|]; apply AG4; intros x Hx; cbv beta in Hx; clear - SP2R SP2M Hx FLO FHI FTOP LOW LOR FR1' SHT1; lia).
    assert (FRs4 : rw_cells asegs m4 (S - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
    { eapply rw_cells_agree_nw; [exact FRsx|]. apply AG4. intros x Hx. unfold fa_saved in Hx. cbn [cells_size csize Nat.add] in Hx. clear - SP2R SP2M Hx FLO FHI FTOP LOW LOR FR1' SHT1. lia. }
    assert (ST4 : stk asegs m4 lo sp2) by (eapply stk_agree_nw; [exact STx|]; apply AG4; intros x Hx; cbv beta in Hx; clear - SP2R SP2M Hx FLO FHI FTOP LOW LOR FR1' SHT1; Z.div_mod_to_equations; lia).
    eapply evt_cut; [eapply (pad_exit2 S sp2 f fl lo OS xra gp (wz TPV_A) xt0 xt1 xt2 (wz (-11)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 _ _ _ _ _ _ _ _ xt3 xt4 xt5 xt6
                               ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                               [C8 (wz ((OS + 160) / 8 + 2147450880)); C8 (wz BUF); C8 (wz (OS / 8)); C8 (wz (BUF + N)); CB 8 j4; CB 8 j5; C8 (wz f)] Fx fc m4);
                     [lia| lia| exact FL0| ul| lia| lia| ul| lia| reflexivity| lia| lia| exact ST4| exact L04| exact STp4| exact FRs4| exact FW| exact FLC| exact MI4]|].
    cbv beta. intros ms5 (m5 & -> & MU5 & WM5 & MI5 & ST5 & FLC5).
    destruct (REL m5 MU5 WM5 FLC5) as (ART5 & FRS5 & LV5 & SP5 & CR5 & AL5 & AM5).
    apply evt_done. apply (aevt_switch RT PMc Σ1 Σ3 K _ AL5 AM5).

    assert (AG5 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) S x /\ ~ (OS + 160 <= x < OS + 168)) -> agree_on P mx m5).
    { intros P HP a Ha. destruct (HP _ Ha) as [H1 H2]. pose proof (CSEP _ H1) as [C1 C2]. rewrite (MU5 a), (MU4 a); [reflexivity| |].
      - cbn [outside]. clear - SP2R SP2M H2 C1 C2. repeat split; try exact I; lia.
      - cbn [outside]. split; [| exact I]. intros E. apply NAC. rewrite LV1, FRS1. replace fl with (bv_unsigned a) by lia.
        destruct H1 as [H|[H|[H|[H|H]]]]; [exfalso; clear - SP2R SP2M H E FLW LOW LOR; ul| right; left; exact H| right; right; left; exact H
          | right; right; right; left; destruct H as (f9 & k9 & Hin & Hr); exists f9, k9; split; [right; exact Hin| exact Hr]
          | do 4 right; destruct H as (f9 & k9 & Hin & Hr); exists f9, k9; split; [right; exact Hin| exact Hr]]. }
    eapply (HK Σ3 xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 Fx m5 pb' pp' ep' dum' ART5 MI5 ST5);
      [| | exact PIx| | rewrite LV5, LV1; reflexivity| exact FRS5| rewrite SP5, SP1; reflexivity| rewrite CR5, CR1; lia|].
    - split.
      + assert (SB5 : rw_cells asegs m5 OS (sb_cellsA pb' (wz pp') (wz ep') dum')).
        { eapply rw_cells_agree_nw; [exact SBx|]. apply AG5. intros x Hx. unfold sb_cellsA in Hx. cbn [cells_size csize Nat.add] in Hx. split; [apply (CL S); left; lia| lia]. }
        assert (HX5 : rw_cells asegs m5 (OS + 128) [CB 32 hx]).
        { eapply rw_cells_agree_nw; [exact HXx|]. apply AG5. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [apply (CL S); left; lia| lia]. }
        assert (WID5 : rw_cells asegs m5 (OS + 160) [C8 (wz 0)]).
        { eapply rw_cells_agree_nw; [exact WID4|]. apply (agree_of_munch _ _ _ _ MU5). intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbn [outside]. split; [| exact I].
          intros E. apply NAC. replace fl with x by lia. right; right; right; left. exists fO, kO. split; [exact INO1| rewrite <- EFSZ; lia]. }
        assert (HY5 : rw_cells asegs m5 (OS + 168) [CB 120 hy]).
        { eapply rw_cells_agree_nw; [exact HYx|]. apply AG5. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [apply (CL S); left; lia| lia]. }
        unfold sb_cellsA in SB5. glueZ WID5 HY5. glueZ HX5 WID5. glueZ SB5 HX5.
        destruct (rw_cells_forget asegs m5 OS _ SB5) as (bo5 & H5). exists bo5. exact H5.
      + eapply bytes_at_agree; [exact SHx|]. apply AG5. intros x Hx. rewrite repeat_length in Hx. unfold shad, SHB in Hx.
        split; [apply (CL S); right; clear - SP2R SP2M Hx FLO FHI F0; Z.div_mod_to_equations; lia| clear - SP2R SP2M Hx FLO FHI F0 FSELF; unfold shad, SHB in *; Z.div_mod_to_equations; lia].
    - eapply rw_cells_agree_nw; [exact SBx|]. apply AG5. intros x Hx. unfold sb_cellsA in Hx. cbn [cells_size csize Nat.add] in Hx. split; [apply (CL S); left; lia| lia].
    - eapply rw_cells_agree_nw; [exact WID4|]. apply (agree_of_munch _ _ _ _ MU5). intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbn [outside]. split; [| exact I].
      intros E. apply NAC. replace fl with x by lia. right; right; right; left. exists fO, kO. split; [exact INO1| rewrite <- EFSZ; lia].
    - intros a Ha Ho. rewrite <- (PRESx a Ha Ho). apply (AG5 (fun x => x = bv_unsigned a)); [| reflexivity]. intros x ->. split; [exact Ha|].
      cbn [outside] in Ho. lia. }

  apply (aevt_evt RT AF PMc MST). unfold SHB.
  lazymatch type of FH2 with rw_cells _ _ _ [CB 8 ?h0; CB 8 ?h1; CB 8 ?h2] =>
  eapply evt_cut; [eapply (pad_segAW S sp2 f OS BUF N FILL W lo gp (wz TPV_A) w0 w1 w2 c1 c2 c3 c4 c5 c6 c7 s2 s7 s10 s11 w3 w4 w5 w6 j0 j1 j2 j4 j5 j6 h0 h1 h2 lS F1 fc m2 LS);
                   [ lia| lia| exact FD8| lia| exact FSELF1| lia| lia| exact AL16| | | | | exact LOW'| lia| exact SP2R| lia| lia| lia| lia| lia| lia| exact SHBY2| exact FRl2| exact WID2| exact FH2| exact FS2| exact MI2]|] end.
  { clear - SP2R SP2M FLO FHI SHT LOW. unfold shad, SHB in *. Z.div_mod_to_equations. lia. }
  { clear - SP2R SP2M FDJ FLO FHI. lia. }
  { clear - SP2R SP2M OSF1 FLO FHI. Z.div_mod_to_equations. lia. }
  { clear - SP2R SP2M FSO1 FLO FHI. lia. }
  cbv beta. intros ms3 (a0x & a1x & m3 & -> & MU3 & WM3 & MI3 & FRl3 & WID3 & FH3 & FS3). apply evt_done.
  assert (AG3 : forall P : Z -> Prop, (forall x, P x -> ~ (sp2 <= x < sp2 + 56) /\ ~ (f <= x < f + 24) /\ ~ (f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 16)) -> agree_on P m2 m3).
  { intros P HP a Ha. apply MU3. cbn [outside]. destruct (HP _ Ha) as (H1 & H2 & H3). split; [exact H1| split; [exact H2| split; [exact H3| exact I]]]. }
  assert (ART3 : ART RT Σ1 m3).
  { apply (art_client_write RT AF Σ1 m2 m3 sp2 ART2 ltac:(ul)); [| exact WM3]. intros a Ha. apply MU3. cbn [outside].
    split; [intros Hin; apply Ha; left; ul|].
    split; [intros Hin; apply Ha; right; right; right; left; exists f, 1%nat; split; [exact INF1| change (fs_size 1) with 128; lia]|].
    split; [| exact I]. intros Hin; apply Ha. do 4 right. exists f, 1%nat. split; [exact INF1|]. unfold shad, SHB. change (fs_size 1) with 128. clear - SP2R SP2M Hin FD0. Z.div_mod_to_equations. lia. }
  assert (PRES3 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) S (bv_unsigned a) -> m3 a = m a).
  { intros a Ha. rewrite <- (PRES2' a Ha). apply MU3. pose proof (CSEP _ Ha) as [C1 C2]. destruct (aclient_split_c RT AF Σ m S _ ART0 Ha) as [X|X]; cbn [outside];
      (split; [| split; [clear - SP2R SP2M C1; lia| split; [exact C2| exact I]]]); clear - SP2R SP2M X LOW LOR; ul. }
  Local Ltac by3 H AG := eapply rw_cells_agree_nw; [exact H|]; apply AG; intros x Hx; cbn [sb_cellsA fa_saved cells_size csize Nat.add] in Hx.
  assert (FRs3 : rw_cells asegs m3 (S - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)) by (by3 FRs2 AG3; clear - SP2R SP2M Hx FR1' SHT1 LOW LOR; lia).
  assert (STp3 : stk asegs m3 (sp2 + 56) (S - 104)) by (eapply stk_agree_nw; [exact STp2|]; apply AG3; intros x Hx; cbv beta in Hx; clear - SP2R SP2M Hx FR1' SHT1 LOW LOR; lia).
  assert (ST3 : stk asegs m3 lo sp2) by (eapply stk_agree_nw; [exact ST2|]; apply AG3; intros x Hx; cbv beta in Hx; clear - SP2R SP2M Hx FR1' SHT1 LOW LOR; lia).
  assert (SB3 : rw_cells asegs m3 OS (sb_cellsA pb (wz pp) (wz ep) dum)) by (by3 SB2 AG3; clear - SP2R SP2M Hx FLO FHI FTOP LOW LOR FDJ FSO1; lia).
  lazymatch type of HX2 with rw_cells _ _ _ ?cs => assert (HX3 : rw_cells asegs m3 (OS + 128) cs) by (by3 HX2 AG3; clear - SP2R SP2M Hx FLO FHI FTOP LOW LOR FDJ FSO1; lia) end.
  lazymatch type of HY2 with rw_cells _ _ _ ?cs => assert (HY3 : rw_cells asegs m3 (OS + 168) cs) by (by3 HY2 AG3; clear - SP2R SP2M Hx FLO FHI FTOP LOW LOR FDJ FSO1; lia) end.
  pose proof (SRCT m3 MI3 ltac:(intros a Ha _; exact (PRES3 a Ha))) as SRC3.
  assert (FOBJ3 : rw_cells asegs m3 (f + 32) [CB 24 jO]) by (by3 FOBJ2 AG3; clear - SP2R SP2M Hx FR1' LOW LOR FSELF1; lia).
  unfold id in SHBY2.
  assert (SHBY3 : bytes_at asegs m3 (OS / 8 + 2147450880) (repeat z8 36)).
  { eapply bytes_at_agree; [exact SHBY2|]. apply AG3. intros x Hx. rewrite repeat_length in Hx. unfold shad, SHB in *.
    clear - SP2R SP2M Hx FLO FHI F0 SHT LOW LOR OSF1 FDJ. split; [| split]; Z.div_mod_to_equations; lia. }
  assert (PRES3' : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) S (bv_unsigned a) -> outside [(OS + 40, OS + 128); (OS + 160, OS + 168)] (bv_unsigned a) -> m3 a = m a)
    by (intros a Ha _; exact (PRES3 a Ha)).
  clear AG3 MU3 WM3 FRl2 WID2 FH2 FS2 FRs2 STp2 ST2 SB2 HX2 HY2 FOBJ2 SHBY2 MI2 WM2.

  replace (pad_ns N W) with (W - N) by (unfold pad_ns; destruct (Z.ltb_spec N W); lia).
  destruct (rw_cells_CB_cut3 m3 (f + 32) 24 jO 1 (W - N) ltac:(lia) ltac:(lia) ltac:(lia) FOBJ3) as (ob1 & ob2 & ob3 & X1 & X2 & X3).
  change (Z.to_nat 1) with 1%nat in X1. replace (f + 32 + 1) with (f + 33) in X2, X3 by lia.
  replace (24 - Z.to_nat 1 - Z.to_nat (W - N))%nat with (Z.to_nat (23 - (W - N))) in X3 by lia.
  destruct (rw_cells_CB_cut3 m3 (f + 33 + (W - N)) (Z.to_nat (23 - (W - N))) ob3 1 (22 - (W - N)) ltac:(lia) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) X3) as (ob4 & ob5 & ob6 & X4 & X5 & _).
  change (Z.to_nat 1) with 1%nat in X4. clear X3 X5 FOBJ3.
  assert (ED8 : (f + 32) / 8 + 2147450880 = f / 8 + 2147450880 + 4) by (clear - F64 NPOS NW W22; Z.div_mod_to_equations; lia).

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pad_w1 S sp2 f OS FILL W (W - N) lo gp (wz TPV_A) w0 w1 w2 a0x a1x (wz 0xb1134) (wz (-13)) (wz (-8)) c5 c6 c7 w3 w4 w5 w6 (skipn 12 lS) F1 fc m3);
                   [rewrite length_skipn, LS; reflexivity| lia| lia| exact FD0| lia| lia| lia| exact FS3| exact MI3]|].
  cbv beta. intros msA (mw1 & -> & MUA & WMA & MIA & FSA). apply evt_done.
  assert (ARTA : ART RT Σ1 mw1).
  { apply (art_client_write RT AF Σ1 m3 mw1 sp2 ART3 ltac:(ul)); [| exact WMA]. intros a Ha. apply MUA. cbn [outside]. split; [| exact I].
    intros Hin; apply Ha. do 4 right. exists f, 1%nat. split; [exact INF1|]. unfold shad, SHB. change (fs_size 1) with 128. clear - SP2R SP2M Hin FD0 NPOS NW W22. Z.div_mod_to_equations. lia. }
  Local Ltac mvc H m' AG tac := lazymatch type of H with rw_cells _ _ ?a ?cs => let Hn := fresh "T" in
      assert (Hn : rw_cells asegs m' a cs) by (eapply rw_cells_agree_nw; [exact H|]; apply AG; intros x Hx;
        cbn [sb_cellsA sb_cellsX fa_saved cells_size csize Nat.add length app map pad_sh12 pad_sh12u repeat] in Hx; rewrite ?Nat.add_0_r in Hx; rewrite ?Z2Nat.id in Hx by lia; tac); clear H; rename Hn into H end.
  Local Ltac mvs H m' AG LS tac := lazymatch type of H with rw_cells _ _ ?a ?cs => let Hn := fresh "T" in
      assert (Hn : rw_cells asegs m' a cs) by (eapply rw_cells_agree_nw; [exact H|]; apply AG; intros x Hx;
        rewrite cells_size_app, cells_size_map_C1p, cells_size_map_CB1, length_skipn, LS in Hx; cbn [length pad_sh12 pad_sh12u app repeat Nat.add Nat.sub] in Hx; tac); clear H; rename Hn into H end.
  assert (AGA : forall P : Z -> Prop, (forall x, P x -> ~ (f / 8 + 2147450880 + 4 <= x < f / 8 + 2147450880 + 7)) -> agree_on P m3 mw1).
  { intros P HP a Ha. apply MUA. cbn [outside]. split; [exact (HP _ Ha)| exact I]. }
  mvc X1 mw1 AGA ltac:(clear - SP2R SP2M Hx FSELF1 NPOS NW W22; lia). mvc X2 mw1 AGA ltac:(clear - SP2R SP2M Hx FSELF1 NPOS NW W22; lia). mvc X4 mw1 AGA ltac:(clear - SP2R SP2M Hx FSELF1 NPOS NW W22; lia).
  assert (STA : stk asegs mw1 lo sp2) by (eapply stk_agree_nw; [exact ST3|]; apply AGA; intros x Hx; cbv beta in Hx; clear - SP2R SP2M Hx SHT1 LOW NPOS NW W22; lia).

  assert (SHDA : bytes_at asegs mw1 ((f + 32) / 8 + 2147450880) [z8; z8; z8]).
  { rewrite ED8. pose proof FSA as T. unfold pad_sh12u in T. cbn [map app repeat] in T. takeZ T 4%nat (f / 8 + 2147450880 + 4)%Z T0. clear T0.
    takeZ T 3%nat (f / 8 + 2147450880 + 7)%Z T1. clear T. exact (rw_cells_bytes_at _ _ _ _ T1). }

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (sn_walk1 sp2 (f + 32) (W - N) FILL lo (wz 0xb1304) gp (wz TPV_A) w0 w1 w2 (wz (-13)) (wz (-8)) c5 c6 c7 (wz S) (wz sp2)
                             (wz f) (wz OS) (wz 2147450880) (wz FILL) (wz (OS + 160)) (wz W) (wz (W - N)) (wz (f + 32)) (wz (f / 8 + 2147450880)) (wz f) w3 w4 w5 w6 ob1 F1 fc mw1);
                   [exact STA| ul| lia| lia| lia| lia| clear - F64 NPOS NW W22; Z.div_mod_to_equations; lia| rewrite ED8; lia| rewrite ED8; clear - SP2R SP2M FSELF1 NPOS NW W22; lia| lia| lia
                   | exact (af_client_consts RT AF Σ1 mw1 ARTA)| exact SHDA| exact X1| exact MIA]|].
  cbv beta. intros msB (mw2 & jfr & -> & MUB & WMB & MIB & STB & SNFR & X1B). apply evt_done. clear X1.
  assert (ARTB : ART RT Σ1 mw2).
  { apply (art_client_write RT AF Σ1 mw1 mw2 (sp2 - 64) ARTA ltac:(ul)); [| exact WMB]. intros a Ha. apply MUB. cbn [outside].
    split; [intros Hin; apply Ha; left; ul|]. split; [| exact I].
    intros Hin; apply Ha. right; right; right; left. exists f, 1%nat. split; [exact INF1| change (fs_size 1) with 128; lia]. }
  assert (AGB : forall P : Z -> Prop, (forall x, P x -> ~ (sp2 - 64 <= x < sp2) /\ ~ (f + 32 <= x < f + 33)) -> agree_on P mw1 mw2).
  { intros P HP a Ha. apply MUB. cbn [outside]. destruct (HP _ Ha) as [H1 H2]. split; [exact H1| split; [clear - H2 NPOS NW W22; lia| exact I]]. }
  mvc X2 mw2 AGB ltac:(clear - SP2R SP2M Hx FR1' LOW LOR NPOS NW W22; lia). mvc X4 mw2 AGB ltac:(clear - SP2R SP2M Hx FR1' LOW LOR NPOS NW W22; lia).
  assert (SHDB : bytes_at asegs mw2 ((f + 32) / 8 + 2147450880) [z8; z8; z8]).
  { eapply bytes_at_agree; [exact SHDA|]. apply AGB. intros x Hx. cbn [length] in Hx. rewrite ED8 in Hx. clear - SP2R SP2M Hx SHT1 LOW LOR FSELF1 NPOS NW W22. lia. }

  assert (US64 : bv_unsigned (wz (sp2 - 64)) = sp2 - 64) by (apply unsigned_lit; lia).
  eapply (aevt_memsetP RT RC PMc FDO MST Σ1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc mw2 (f + 33) (W - N) (Z_to_bv 8 FILL) lo);
    [f_equal; lia| rewrite (a_u8_small FILL) by lia; reflexivity| reflexivity| lia| lia| | exact ARTB| exact MIB| |].
  {   split; [| split].
    - intros _. split.
      + apply (acc_sub asegs mw2 (f + 32) (8 * Z.of_nat 3) (f + 33) (W - N)); [| lia| lia].
        apply (acc_zero_run asegs mw2 (f + 32) 3); [clear - F64 NPOS NW W22; Z.div_mod_to_equations; lia| lia| unfold shad, SHB; exact SHDB].
      + right; left. exists f, 1%nat. split; [exact INF1| change (fs_size 1) with 128; lia].
    - intros i Hi. right; right; right; left. exists f, 1%nat. split; [exact INF1| change (fs_size 1) with 128; lia].
    - eapply rw_cells_wr_at; [exact X2| cbn [cells_size csize Nat.add]; lia]. }
  { unfold call_ok. rewrite US64. split; [exact STB|]. split; [ul|]. split; [ul|]. split; [ul| clear - SP2R SP2M NPOS NW W22; Z.div_mod_to_equations; lia]. }
  intros u0 u1 u2 g1 g2 g3 g4 g5 g6 g7 u3 u4 u5 u6 F2 mw3 (ARTC & MIC & WMC & STC) PRESC FILLC.
  rewrite US64 in STC, PRESC. rewrite (ret_pc_even 0xb16a0) by lia.
  assert (AGC : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) (sp2 - 64) x /\ ~ (f + 33 <= x < f + 33 + (W - N))) -> agree_on P mw2 mw3).
  { intros P HP a Ha. destruct (HP _ Ha) as [H1 H2]. apply PRESC; [exact H1| exact H2]. }
  Local Ltac infr INF1 := lazymatch type of INF1 with In (?f, _) _ => right; right; right; left; exists f, 1%nat; split; [exact INF1| change (fs_size 1) with 128; lia] end.
  Local Ltac infs INF1 FD0 := lazymatch type of INF1 with In (?f, _) _ => do 4 right; exists f, 1%nat; split; [exact INF1| unfold shad, SHB; change (fs_size 1) with 128; Z.div_mod_to_equations; lia] end.
  mvc X4 mw3 AGC ltac:(split; [infr INF1| lia]). mvc SNFR mw3 AGC ltac:(split; [left; ul| clear - SP2R SP2M Hx FR1' LOW LOR NPOS NW W22; lia]).
  mvc X1B mw3 AGC ltac:(split; [infr INF1| lia]).
  assert (SHDC : bytes_at asegs mw3 ((f + 32) / 8 + 2147450880) [z8; z8; z8]).
  { eapply bytes_at_agree; [exact SHDB|]. apply AGC. intros x Hx. cbn [length] in Hx. rewrite ED8 in Hx. split; [clear - Hx INF1 FD0 NPOS NW W22; infs INF1 FD0| clear - SP2R SP2M Hx FSELF1 NPOS NW W22; lia]. }

  replace (f + 33 + (W - N)) with (f + 32 + 1 + (W - N)) in X4 by lia.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (sn_walk2 sp2 (f + 32) (W - N) FILL lo (wz 0xb1304) gp (wz TPV_A) u0 u1 u2 (wz (f + 33)) g1 g2 g3 g4 g5 g6 g7 (wz S) (wz sp2)
                             (wz f) (wz OS) (wz 2147450880) (wz FILL) (wz (OS + 160)) (wz W) (wz (W - N)) (wz (f + 32)) (wz (f / 8 + 2147450880)) (wz f) u3 u4 u5 u6 jfr ob4 F2 fc mw3);
                   [exact STC| ul| lia| lia| lia| lia| clear - F64 NPOS NW W22; Z.div_mod_to_equations; lia| rewrite ED8; lia| rewrite ED8; clear - SP2R SP2M FSELF1 NPOS NW W22; lia| lia
                   | exact SHDC| exact SNFR| exact X4| exact MIC]|].
  cbv beta. intros msD (mw4 & -> & MUD & WMD & MID & STD & X4D). apply evt_done. rewrite (ret_pc_even 0xb1304) by lia. clear X4 SNFR.
  assert (ARTD : ART RT Σ1 mw4).
  { apply (art_client_write RT AF Σ1 mw3 mw4 sp2 ARTC ltac:(ul)); [| exact WMD]. intros a Ha. apply MUD. cbn [outside]. split; [| exact I].
    intros Hin; apply Ha. right; right; right; left. exists f, 1%nat. split; [exact INF1| change (fs_size 1) with 128; lia]. }
  assert (AGD : forall P : Z -> Prop, (forall x, P x -> ~ (f + 33 + (W - N) <= x < f + 33 + (W - N) + 1)) -> agree_on P mw3 mw4).
  { intros P HP a Ha. apply MUD. cbn [outside]. split; [pose proof (HP _ Ha); clear - H NPOS NW W22; lia| exact I]. }
  mvc X1B mw4 AGD ltac:(clear - Hx NPOS NW W22; lia).

  assert (AG34 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) sp2 x /\ ~ (f + 32 <= x < f + 56) /\ ~ (f / 8 + 2147450880 + 4 <= x < f / 8 + 2147450880 + 7)) -> agree_on P m3 mw4).
  { intros P HP a Ha. destruct (HP _ Ha) as (H1 & H2 & H3).
    assert (XS : sp2 <= bv_unsigned a \/ bv_unsigned a < rt_sp0 RT Σ - 8388608).
    { destruct (aclient_split_c RT AF Σ1 m3 sp2 _ ART3 H1) as [X|X]; [left; exact X| right; rewrite SP1 in X; unfold STACK_WIN in X; exact X]. }
    rewrite (MUD a). 2:{ cbn [outside]. split; [clear - H2 NPOS NW W22; lia| exact I]. }
    rewrite (PRESC a). 2:{ apply (aclient_mono _ _ _ _ _ _ _ H1); [auto| auto| lia]. } 2:{ clear - H2 NPOS NW W22. lia. }
    rewrite (MUB a). 2:{ cbn [outside]. split; [clear - SP2R SP2M XS H2 FR1' LOW LOR NPOS NW W22; lia| split; [clear - H2 NPOS NW W22; lia| exact I]]. }
    apply MUA. cbn [outside]. split; [clear - H3 NPOS NW W22; lia| exact I]. }
  mvc FRl3 mw4 AG34 ltac:(split; [left; ul| clear - SP2R SP2M Hx FR1' SHT1 LOW LOR NPOS NW W22; lia]).
  mvc FRs3 mw4 AG34 ltac:(split; [left; ul| clear - SP2R SP2M Hx FR1' SHT1 LOW LOR NPOS NW W22; lia]).
  assert (STp4w : stk asegs mw4 (sp2 + 56) (S - 104)) by (eapply stk_agree_nw; [exact STp3|]; apply AG34; intros x Hx; cbv beta in Hx; split; [left; ul| clear - SP2R SP2M Hx FR1' SHT1 LOW LOR NPOS NW W22; lia]). clear STp3. rename STp4w into STp3.
  assert (CLw : forall sp' x, (fO <= x < fO + FSZ - 8) \/ (fO / 8 + 2147450880 <= x < (fO + FSZ) / 8 + 2147450880) -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) sp' x).
  { intros sp' x [H|H]; [right; right; right; left| do 4 right]; exists fO, kO; rewrite <- EFSZ; (split; [exact INO1|]); [exact H| unfold shad, SHB; exact H]. }
  mvc SB3 mw4 AG34 ltac:(split; [apply (CLw sp2); left; lia| clear - SP2R SP2M Hx FLO FHI FDJ FSO1 NPOS NW W22; lia]).
  mvc HX3 mw4 AG34 ltac:(split; [apply (CLw sp2); left; lia| clear - SP2R SP2M Hx FLO FHI FDJ FSO1 NPOS NW W22; lia]).
  mvc HY3 mw4 AG34 ltac:(split; [apply (CLw sp2); left; lia| clear - SP2R SP2M Hx FLO FHI FDJ FSO1 NPOS NW W22; lia]).
  mvc WID3 mw4 AG34 ltac:(split; [apply (CLw sp2); left; lia| clear - SP2R SP2M Hx FLO FHI FDJ FSO1 NPOS NW W22; lia]).
  mvc FH3 mw4 AG34 ltac:(split; [infr INF1| clear - SP2R SP2M Hx FSELF1 NPOS NW W22; lia]).
  assert (SHBY4w : bytes_at asegs mw4 (OS / 8 + 2147450880) (repeat z8 36)).
  { eapply bytes_at_agree; [exact SHBY3|]. apply AG34. intros x Hx. rewrite repeat_length in Hx.
    split; [apply (CLw sp2); right; clear - SP2R SP2M Hx FLO FHI F0 NPOS NW W22; Z.div_mod_to_equations; lia| clear - SP2R SP2M Hx FLO FHI F0 OSF1 FSO1 FDJ FSELF1 FSELF NPOS NW W22; Z.div_mod_to_equations; lia]. }
  clear SHBY3. rename SHBY4w into SHBY3.
  assert (AG14 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) sp2 x /\ ~ (f + 32 <= x < f + 56)) -> agree_on P mw1 mw4).
  { intros P HP a Ha. destruct (HP _ Ha) as (H1 & H2).
    assert (XS : sp2 <= bv_unsigned a \/ bv_unsigned a < rt_sp0 RT Σ - 8388608).
    { destruct (aclient_split_c RT AF Σ1 mw1 sp2 _ ARTA H1) as [X|X]; [left; exact X| right; rewrite SP1 in X; unfold STACK_WIN in X; exact X]. }
    rewrite (MUD a). 2:{ cbn [outside]. split; [clear - H2 NPOS NW W22; lia| exact I]. }
    rewrite (PRESC a). 2:{ apply (aclient_mono _ _ _ _ _ _ _ H1); [auto| auto| lia]. } 2:{ clear - H2 NPOS NW W22. lia. }
    apply MUB. cbn [outside]. split; [clear - SP2R SP2M XS H2 FR1' LOW LOR NPOS NW W22; lia| split; [clear - H2 NPOS NW W22; lia| exact I]]. }
  mvs FSA mw4 AG14 LS ltac:(split; [clear - Hx INF1 FD0 NPOS NW W22; infs INF1 FD0| clear - SP2R SP2M Hx FSELF1 NPOS NW W22; lia]).
  assert (FILLD : bytes_at asegs mw4 (f + 33) (repeat (Z_to_bv 8 FILL) (Z.to_nat (W - N)))).
  { eapply bytes_at_agree; [exact FILLC|]. apply AGD. intros x Hx. rewrite repeat_length in Hx. clear - Hx NPOS NW W22. lia. }
  clear FILLC SHDC AGD AGC PRESC MUD WMD.

  assert (SHZ4w : shz mw4 OS 288).
  { change 288 with (8 * Z.of_nat 36). apply (shz_of_zero_run mw4 OS 36); [clear - SP2R SP2M AL16 NPOS NW W22; Z.div_mod_to_equations; lia| lia| exact SHBY3]. }
  assert (SHV4w : shz mw4 PJ_NULSB_VT_A 24).
  { pose proof (shz_of_acc mw4 PJ_NULSB_VT_A 24 (proj1 (VTACC Σ1 mw4 ARTD)) eq_refl ltac:(unfold PJ_NULSB_VT_A; lia)) as X. exact X. }
  pose proof (DCC Σ1 mw4 ARTD) as (VT4w & _). change (ro_cells asegs mw4 PJ_NULSB_VT_A [C8 (wz PJ_XSPUTN_A); C8 (wz PJ_OVERFLOW_A); C8 (wz 8)]) in VT4w.
  pose proof SB3 as SBc. unfold sb_cellsA in SBc. takeZ SBc 1%nat (OS + 8)%Z SBVw. clear SBc.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pad_w2 S sp2 f OS BUF N FILL W (W - N) gp (wz TPV_A) u0 u1 u2 _ _ g2 g3 g4 g5 g6 g7 u3 u4 u5 u6 j4 j5 F2 fc mw4);
                   [ lia| lia| lia| lia| exact AL16| lia| lia| lia| lia| lia| lia| exact SHZ4w| exact SHV4w| exact FRl3| exact X1B| exact SBVw| exact VT4w| exact MID]|].
  cbv beta. intros msE <-. apply evt_done.
  eapply (XSP Σ1 K OS (f + 33) (W - N) (W - N) sp2 lo fO kO pb pp ep dum (repeat (Z_to_bv 8 FILL) (Z.to_nat (W - N))));
    [exact FDO| exact MST| exact INO1| exact FLO| rewrite <- EFSZ; exact FHI| exact AL16
    | unfold sb_cellsX; unfold sb_cellsA in SB3; exact SB3| exact PI| unfold shad, SHB; exact SHBY3
    | exact FILLD| rewrite repeat_length, Z2Nat.id by lia; reflexivity| lia| lia| lia| clear - SP2R SP2M FR1' SP0R LOW NPOS NW W22; lia| | | | exact ARTD| exact MID| exact STD| rewrite SP1; ul| ul| ul
    | clear - SP2R SP2M NPOS NW W22; Z.div_mod_to_equations; lia|].
  { apply (acc_sub asegs mw4 (f + 32) (8 * Z.of_nat 3) (f + 33) (W - N)); [| lia| lia].
    apply (acc_zero_run asegs mw4 (f + 32) 3); [clear - F64 NPOS NW W22; Z.div_mod_to_equations; lia| lia|].
    eapply bytes_at_agree; [exact SHDA|]. unfold shad, SHB. rewrite ED8. apply AG14. intros x Hx. cbn [length repeat] in Hx. split; [clear - Hx INF1 FD0 NPOS NW W22; infs INF1 FD0| clear - SP2R SP2M Hx FSELF1 NPOS NW W22; lia]. }
  { intros _. right; left. exists f, 1%nat. split; [exact INF1| change (fs_size 1) with 128; lia]. }
  { left. split; [clear - SP2R SP2M FR1' LOW NPOS NW W22; lia| clear - FDJ FLO FHI NPOS NW W22; lia]. }
  intros v0 v1 v2 e1 e2 e3 e4 e5 e6 e7 v3 v4 v5 v6 mw5 pb1 pp1 ep1 dum1 ARTE MIE STE SBE PI1 SHBYE' PRESE. rewrite (ret_pc_even 0xb1354) by lia.
  assert (AGE : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) sp2 x /\ ~ (OS + 40 <= x < OS + 128)) -> agree_on P mw4 mw5).
  { intros P HP a Ha. destruct (HP _ Ha) as [H1 H2]. apply PRESE; [exact H1| cbn [outside]; split; [exact H2| exact I]]. }
  mvc FRl3 mw5 AGE ltac:(split; [left; ul| clear - SP2R SP2M Hx FLO FHI FTOP LOW LOR NPOS NW W22; lia]).
  mvc X1B mw5 AGE ltac:(split; [infr INF1| clear - SP2R SP2M Hx FDJ FLO FHI NPOS NW W22; lia]).
  mvs FSA mw5 AGE LS ltac:(split; [clear - Hx INF1 FD0 NPOS NW W22; infs INF1 FD0| clear - SP2R SP2M Hx FSO1 FLO FHI NPOS NW W22; lia]).

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pad_w3 S sp2 f OS BUF N FILL W (W - N) lo gp (wz TPV_A) v0 v1 v2 e1 e2 e3 e4 e5 e6 e7 v3 v4 v5 v6 j4 j5 (skipn 12 lS) F2 fc mw5);
                   [rewrite length_skipn, LS; reflexivity| lia| lia| exact FD0| lia| lia| lia| exact FSELF1| lia| lia| lia| lia| exact FRl3| exact X1B| exact FSA| exact MIE]|].
  cbv beta. intros msF (mw6 & -> & MUF & WMF & MIF & FSF). apply evt_done.
  assert (ARTF : ART RT Σ1 mw6).
  { apply (art_client_write RT AF Σ1 mw5 mw6 sp2 ARTE ltac:(ul)); [| exact WMF]. intros a Ha. apply MUF. cbn [outside]. split; [| exact I].
    intros Hin; apply Ha. do 4 right. exists f, 1%nat. split; [exact INF1|]. unfold shad, SHB. change (fs_size 1) with 128. clear - SP2R SP2M Hin FD0 NPOS NW W22. Z.div_mod_to_equations. lia. }
  assert (AG46 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) sp2 x /\ ~ (OS + 40 <= x < OS + 128) /\ ~ (f / 8 + 2147450880 + 4 <= x < f / 8 + 2147450880 + 7)) -> agree_on P mw4 mw6).
  { intros P HP a Ha. destruct (HP _ Ha) as (H1 & H2 & H3). rewrite (MUF a); [| cbn [outside]; split; [exact H3| exact I]]. apply PRESE; [exact H1| cbn [outside]; split; [exact H2| exact I]]. }
  assert (AG56 : forall P : Z -> Prop, (forall x, P x -> ~ (f / 8 + 2147450880 + 4 <= x < f / 8 + 2147450880 + 7)) -> agree_on P mw5 mw6).
  { intros P HP a Ha. apply MUF. cbn [outside]. split; [exact (HP _ Ha)| exact I]. }
  mvc FRl3 mw6 AG56 ltac:(clear - SP2R SP2M Hx FR1' SHT1 LOW LOR NPOS NW W22; lia).
  mvc FRs3 mw6 AG46 ltac:(split; [left; ul| split; [clear - SP2R SP2M Hx FLO FHI FTOP LOW LOR NPOS NW W22; lia| clear - SP2R SP2M Hx FR1' SHT1 LOW LOR NPOS NW W22; lia]]).
  assert (STp6 : stk asegs mw6 (sp2 + 56) (S - 104)).
  { eapply stk_agree_nw; [exact STp3|]. apply AG46. intros x Hx. cbv beta in Hx. split; [left; ul| split; [clear - SP2R SP2M Hx FLO FHI FTOP LOW LOR NPOS NW W22; lia| clear - SP2R SP2M Hx FR1' SHT1 LOW LOR NPOS NW W22; lia]]. }
  clear STp3. rename STp6 into STp3.
  assert (ST6 : stk asegs mw6 lo sp2) by (eapply stk_agree_nw; [exact STE|]; apply AG56; intros x Hx; cbv beta in Hx; clear - SP2R SP2M Hx SHT1 LOW LOR LOR NPOS NW W22; lia).
  mvc SBE mw6 AG56 ltac:(clear - SP2R SP2M Hx FSO1 FLO FHI NPOS NW W22; lia).
  mvc HX3 mw6 AG46 ltac:(split; [apply (CLw sp2); left; lia| split; [lia| clear - SP2R SP2M Hx FSO1 FLO FHI NPOS NW W22; lia]]).
  mvc HY3 mw6 AG46 ltac:(split; [apply (CLw sp2); left; lia| split; [lia| clear - SP2R SP2M Hx FSO1 FLO FHI NPOS NW W22; lia]]).
  mvc WID3 mw6 AG46 ltac:(split; [apply (CLw sp2); left; lia| split; [lia| clear - SP2R SP2M Hx FSO1 FLO FHI NPOS NW W22; lia]]).
  mvc FH3 mw6 AG46 ltac:(split; [infr INF1| split; [clear - SP2R SP2M Hx FDJ FLO FHI NPOS NW W22; lia| clear - SP2R SP2M Hx FSELF1 NPOS NW W22; lia]]).
  assert (SHBY6 : bytes_at asegs mw6 (OS / 8 + 2147450880) (repeat z8 36)).
  { eapply bytes_at_agree; [exact SHBY3|]. apply AG46. intros x Hx. rewrite repeat_length in Hx.
    split; [apply (CLw sp2); right; clear - SP2R SP2M Hx FLO FHI F0 NPOS NW W22; Z.div_mod_to_equations; lia|].
    split; [clear - SP2R SP2M Hx FLO FHI F0 FSELF NPOS NW W22; Z.div_mod_to_equations; lia| clear - SP2R SP2M Hx FLO FHI F0 OSF1 FDJ FSO1 NPOS NW W22; Z.div_mod_to_equations; lia]. }
  clear SHBY3. rename SHBY6 into SHBY3.
  assert (PRES6 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) S (bv_unsigned a) -> outside [(OS + 40, OS + 128)] (bv_unsigned a) -> mw6 a = m a).
  { intros a Ha Ho. cbn [outside] in Ho. destruct Ho as [Ho _]. pose proof (CSEP _ Ha) as [C1 C2]. rewrite <- (PRES3 a Ha).
    assert (Ha1 : aclient (rt_live RT Σ1) (rt_frames RT Σ1) sp2 (bv_unsigned a)).
    { apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LV1; auto| rewrite FRS1; intros e He; right; exact He| lia]. }
    transitivity (mw4 a).
    { apply (AG46 (fun x => x = bv_unsigned a)); [| reflexivity]. intros x ->. split; [exact Ha1|]. split; [exact Ho| clear - SP2R SP2M C2 NPOS NW W22; lia]. }
    apply (AG34 (fun x => x = bv_unsigned a)); [| reflexivity]. intros x ->. split; [exact Ha1|]. split; [clear - SP2R SP2M C1 NPOS NW W22; lia| clear - SP2R SP2M C2 NPOS NW W22; lia]. }
  pose proof (SRCT mw6 MIF PRES6) as SRC6.
  clear MUA WMA MIA AGA ARTA STA SHDA MUB WMB MIB STB ARTB AGB SHDB US64 ARTC MIC WMC STC STD ARTD MID AG34 AG14 FILLD SHZ4w SHV4w VT4w SBVw
        ARTE MIE STE PI SHBYE' PRESE AGE X1B FSA MUF WMF AG46 AG56 ART3 MI3 ST3 SB3 FS3 PRES3 PRES3' SRC3 X2 X4D ob5 ob6.
  clear mw1 mw2 mw3 mw4 mw5 m3.
  rename mw6 into m3, ARTF into ART3, MIF into MI3, ST6 into ST3, SBE into SB3, FSF into FS3, PRES6 into PRES3, SRC6 into SRC3.
  change (rw_cells asegs m3 OS (sb_cellsA pb1 (wz pp1) (wz ep1) dum1)) in SB3.

  assert (SHZ3 : shz m3 OS 288).
  { change 288 with (8 * Z.of_nat 36). apply (shz_of_zero_run m3 OS 36); [clear - SP2R SP2M AL16; Z.div_mod_to_equations; lia| lia| exact SHBY3]. }
  assert (SHV3 : shz m3 PJ_NULSB_VT_A 24).
  { pose proof (shz_of_acc m3 PJ_NULSB_VT_A 24 (proj1 (VTACC Σ1 m3 ART3)) eq_refl ltac:(unfold PJ_NULSB_VT_A; lia)) as X. exact X. }
  pose proof (DCC Σ1 m3 ART3) as (VT3 & _). change (ro_cells asegs m3 PJ_NULSB_VT_A [C8 (wz PJ_XSPUTN_A); C8 (wz PJ_OVERFLOW_A); C8 (wz 8)]) in VT3.
  pose proof SB3 as SBc. unfold sb_cellsA in SBc. takeZ SBc 1%nat (OS + 8)%Z SBV. clear SBc.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pad_segBW S sp2 f OS BUF N lo _ gp (wz TPV_A) v0 v1 v2 e2 e3 e4 e5 e6 e7 (wz (W - N)) (wz (W - N)) (wz (f + 32)) v3 v4 v5 v6 j4 j5 F2 fc m3);
                   [ lia| lia| lia| lia| exact AL16| lia| exact SP2R| lia| lia| lia| lia| exact SHZ3| exact SHV3| exact FRl3| exact SBV| exact VT3| exact MI3]|].
  cbv beta. intros ms4 <-. apply evt_done.
  assert (HULL3 : os_hullA m3 OS).
  { split; [| unfold shad, SHB; exact SHBY3]. pose proof SB3 as SBc. pose proof WID3 as WIDc. pose proof HX3 as HXc. pose proof HY3 as HYc. unfold sb_cellsA in SBc.
    glueZ WIDc HYc. glueZ HXc WIDc. glueZ SBc HXc. destruct (rw_cells_forget asegs m3 OS _ SBc) as (bo3 & H3). exists bo3. exact H3. }
  pose proof (ACCT Σ1 m3 ART3 LV1 SP1 PRES3) as ACC3.
  assert (CLS3 : 0 < N -> rng_class RT Σ1 BUF N).
  { intros HC. destruct SK as [(RB & B1 & B2 & _)|[(B1 & B2)|[(fB & kB & INB & B1 & B2)|(pB & nB & INP & B1 & B2)]]].
    - right; right; right. unfold SEGTOP_A. lia.
    - right; right; left. rewrite SP1. clear - SP2R SP2M B1 B2 LOW LOR NR. unfold STACK_WIN, USTACK_TOP in *. lia.
    - right; left. exists fB, kB. split; [rewrite FRS1; right; exact INB| lia].
    - left. exists pB, nB. split; [rewrite LV1; exact INP| lia].     }
  assert (SEP3 : (BUF + CAP <= lo /\ (BUF + CAP <= OS \/ OS + 288 <= BUF)) \/ sp2 <= BUF).
  { destruct SK as [(RB & B1 & B2 & _)|[(B1 & B2)|[(fB & kB & INB & B1 & B2)|(pB & nB & INP & B1 & B2)]]].
    - left. split; [clear - SP2R SP2M B2 LOW'; lia| exact SEP].
    - right. lia.
    - left. split; [| exact SEP]. pose proof (fframe_ranges RT AF Σ m fB kB ART0 INB) as (_ & Y1 & _). unfold STACK_WIN in Y1. clear - SP2R SP2M Y1 B2 LOW LOR. lia.
    - left. split; [| exact SEP]. pose proof (af_live_range RT AF Σ m pB nB ART0 INP) as (_ & Y1 & _). unfold STACK_WIN in Y1. clear - SP2R SP2M Y1 B2 LOW LOR. lia.     }
  eapply (XSP Σ1 K OS BUF N CAP sp2 lo fO kO pb1 pp1 ep1 dum1 bs); [exact FDO| exact MST| exact INO1| exact FLO| rewrite <- EFSZ; exact FHI| exact AL16
    | unfold sb_cellsX; unfold sb_cellsA in SB3; exact SB3| exact PI1| unfold shad, SHB; exact SHBY3
    | exact SRC3| lia| lia| lia| lia| | exact ACC3| exact CLS3| exact SEP3| exact ART3| exact MI3| exact ST3| rewrite SP1; ul| ul| ul
    | clear - SP2R SP2M SP2M; Z.div_mod_to_equations; lia|].
  { destruct SK as [(RB & B1 & B2 & _)|[(B1 & B2)|[(fB & kB & INB & B1 & B2)|(pB & nB & INP & B1 & B2)]]]; [unfold SEGTOP_A in *; lia| unfold USTACK_TOP in *; lia| |].
    - pose proof (fframe_ranges RT AF Σ m fB kB ART0 INB) as (_ & Y1 & _). unfold STACK_WIN in Y1. clear - SP2R SP2M Y1 B2 LOW LOR SP0R. unfold USTACK_TOP in *. lia.
    - pose proof (af_live_range RT AF Σ m pB nB ART0 INP) as (_ & Y1 & _). unfold STACK_WIN in Y1. clear - SP2R SP2M Y1 B2 LOW LOR SP0R. unfold USTACK_TOP in *. lia. }
  intros x0 x1 x2 d1 d2 d3 d4 d5 d6 d7 x3 x4 x5 x6 m4 pb' pp' ep' dum' ART4 MI4 ST4 SB4 PI4 SHBY4' PRES4. rewrite (ret_pc_even 0xb13d0) by lia.
  apply (aevt_evt RT AF PMc MST). zstep. if_cases KB; zify_cond KB; [exfalso; clear - SP2R SP2M KB; lia|]. apply evt_done.
  assert (AG4 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) sp2 x /\ ~ (OS + 40 <= x < OS + 128)) -> agree_on P m3 m4).
  { intros P HP a Ha. destruct (HP _ Ha) as [H1 H2]. apply PRES4; [exact H1| cbn [outside]; split; [exact H2| exact I]]. }
  assert (CL1 : forall sp' x, (sp2 <= x < S /\ sp' <= sp2) \/ (fO <= x < fO + FSZ - 8) \/ (fO / 8 + 2147450880 <= x < (fO + FSZ) / 8 + 2147450880)
                             \/ (f <= x < f + 120) \/ (f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 16) -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) sp' x).
  { intros sp' x [[H1 H2]|[H|[H|[H|H]]]]; [left; ul| right; right; right; left| do 4 right| right; right; right; left| do 4 right].
    - exists fO, kO. rewrite <- EFSZ. split; [exact INO1| exact H].
    - exists fO, kO. rewrite <- EFSZ. split; [exact INO1| unfold shad, SHB; exact H].
    - exists f, 1%nat. split; [exact INF1| change (fs_size 1) with 128; lia].
    - exists f, 1%nat. split; [exact INF1| unfold shad, SHB; change (fs_size 1) with 128; clear - SP2R SP2M H FD0; Z.div_mod_to_equations; lia]. }
  Local Ltac by4 H AG := eapply rw_cells_agree_nw; [exact H|]; apply AG; intros x Hx; cbn [sb_cellsA fa_saved cells_size csize Nat.add length app map pad_sh12 repeat] in Hx.
  assert (FRl4 : rw_cells asegs m4 sp2 [C8 (wz ((OS + 160) / 8 + 2147450880)); C8 (wz BUF); C8 (wz (OS / 8)); C8 (wz (BUF + N)); CB 8 j4; CB 8 j5; C8 (wz f)])
    by (by4 FRl3 AG4; split; [apply (CL1 sp2); left; lia| clear - SP2R SP2M Hx FLO FHI FTOP LOW LOR; lia]).
  assert (FRs4 : rw_cells asegs m4 (S - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)) by (by4 FRs3 AG4; split; [apply (CL1 sp2); left; lia| clear - SP2R SP2M Hx FLO FHI FTOP LOW LOR; lia]).
  assert (STp4 : stk asegs m4 (sp2 + 56) (S - 104)).
  { eapply stk_agree_nw; [exact STp3|]. apply AG4. intros x Hx. cbv beta in Hx. split; [apply (CL1 sp2); left; lia| clear - SP2R SP2M Hx FLO FHI FTOP LOW LOR; lia]. }
  assert (WID4 : rw_cells asegs m4 (OS + 160) [C8 (wz W)]) by (by4 WID3 AG4; split; [apply (CL1 sp2); right; left; lia| lia]).
  lazymatch type of HX3 with rw_cells _ _ _ ?cs => assert (HX4 : rw_cells asegs m4 (OS + 128) cs) by (by4 HX3 AG4; split; [apply (CL1 sp2); right; left; lia| lia]) end.
  lazymatch type of HY3 with rw_cells _ _ _ ?cs => assert (HY4 : rw_cells asegs m4 (OS + 168) cs) by (by4 HY3 AG4; split; [apply (CL1 sp2); right; left; lia| lia]) end.
  assert (FH4 : rw_cells asegs m4 f [C8 (wz 0x41b58ab3); C8 (wz 0x16a1c); C8 (wz 0xb1134)]) by (by4 FH3 AG4; split; [apply (CL1 sp2); right; right; right; left; lia| clear - SP2R SP2M Hx FDJ FLO FHI; lia]).
  assert (LS4 : length (skipn 12 lS) = 4%nat) by (rewrite length_skipn, LS; reflexivity).
  assert (FS4 : rw_cells asegs m4 (f / 8 + 2147450880) (map C1 pad_sh12 ++ map (fun l => CB 1 l) (skipn 12 lS))).
  { eapply rw_cells_agree_nw; [exact FS3|]. apply AG4. intros x Hx. rewrite cells_size_app, cells_size_map_C1p, cells_size_map_CB1, LS4 in Hx.
    cbn [length pad_sh12 app repeat Nat.add] in Hx. split; [apply (CL1 sp2); do 4 right; lia| clear - SP2R SP2M Hx FSO1 FLO FHI; lia]. }
  pose proof SHBY4' as SHBY4. unfold shad, SHB in SHBY4. unfold sb_cellsX in SB4. change (rw_cells asegs m4 OS (sb_cellsA pb' (wz pp') (wz ep') dum')) in SB4.
  assert (PRES4' : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) S (bv_unsigned a) -> outside [(OS + 40, OS + 128); (OS + 160, OS + 168)] (bv_unsigned a) -> m4 a = m a).
  { intros a Ha Ho. rewrite <- (PRES3 a Ha ltac:(cbn [outside] in Ho |- *; split; [lia| exact I])). apply PRES4; [| cbn [outside] in Ho |- *; split; [lia| exact I]].
    apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LV1; auto| rewrite FRS1; intros e He; right; exact He| lia]. }
  exact (EXIT m4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 pb' pp' ep' dum' _ _ PI4 ART4 MI4 ST4 FRl4 STp4 FRs4 SB4 HX4 WID4 HY4 SHBY4 FH4 FS4 PRES4').
Qed.
End Pad.
