(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep ZBridge.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac Startup_glue Sj_stage1_kit Pj_loc_kit Pj_os_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_new Sj_num_akit Sj_num_amem Sj_num_aframe Atp_fzwA Pj_lftoi1A Pj_rtkA Pj_defsA Pj_cpsA Pj_os_defsA Pj_os_put1A Pj_os_put2A Pj_os_put3A.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import StoreFast.
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
Definition PJ_PAD_STACK_A : Z := 192 + 64 + 16 + RT_STACK.
Definition pad_cpsA : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (OS BUF N CAP S lo fO FILL : Z) (kO : nat) (pb : word) (dum bs : list byte)
         (ra gp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  fdfs_only PMc -> mat_stable PMc ->
  In (fO, kO) (rt_frames RT Σ) -> fO <= OS -> OS + 288 <= fO + fs_size kO - 8 -> OS mod 16 = 0 ->
  rw_cells bsegs m OS (sb_cellsA pb (wz 0) (wz 0) dum) -> rw_cells bsegs m (OS + 160) [C8 (wz 0)] -> os_hullA m OS ->
  rw_cells bsegs m BUF [CB (Z.to_nat CAP) bs] -> 0 <= N <= CAP -> 0 < BUF -> BUF + CAP <= lo -> acc bsegs m BUF N -> buf_clsA RT Σ fO kO BUF CAP ->
  (BUF + CAP <= OS \/ OS + 288 <= BUF) -> 0 <= FILL < 256 ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo S -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + PJ_PAD_STACK_A <= S ->
  S + 16 <= USTACK_TOP -> S mod 32 = 0 ->
  Z.of_nat (length (rt_frames RT Σ)) + 1 <= FRAMES_TOT -> 1 <= rt_credit RT Σ ->
  (forall (Σ' : rts RT) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m' (pb' pp' ep' : word) (dum' : list byte),
     ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' lo S -> os_hullA m' OS ->
     rw_cells bsegs m' OS (sb_cellsA pb' pp' ep' dum') -> rw_cells bsegs m' (OS + 160) [C8 (wz 0)] ->
     rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_credit RT Σ - 1 <= rt_credit RT Σ' ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) S [(OS + 40, OS + 128); (OS + 160, OS + 168)] m m' ->
     aevt RT PMc Σ' K (MS (mkR ra (wz S) gp (wz TPV_A) t0' t1' t2' s0 s1 (wz OS) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                         F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt RT PMc Σ K (MS (mkR ra (wz S) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz OS) (wz BUF) (wz BUF) (wz (BUF + N)) (wz (OS + 136)) (wz FILL) a6 a7
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (wz PJ_PADOUT_A) fc None m (seg_rom bsegs)).
End Stmt.

Section Pad.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis RC2 : rt_contracts2 RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis ROA : forall Σ m, ART RT Σ m -> pj_os_roA m.
Hypothesis XSP : xsputn_cpsA RT PMc.

Lemma vt_accA : forall Σ m, ART RT Σ m -> acc bsegs m PJ_NULSB_VT_A 24 /\ acc bsegs m PJ_WIDEN_SLOT_A 8.
Proof using AF.
  intros Σ m H. split; (apply (acc_lit RT AF Σ m _ _ H); unfold ACC_LITS, PJ_NULSB_VT_A, PJ_WIDEN_SLOT_A; cbn [In]; repeat (first [left; reflexivity | right])).
Qed.
Local Notation VTACC := vt_accA.

Local Ltac ul := unfold PJ_PAD_STACK_A, PJ_OS_XSPUTN_STACK_A, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Theorem pad_okA : pad_cpsA RT PMc.
Proof using AF RC RC2 FDO MST ROA XSP.
  unfold pad_cpsA. intros until m. intros FDO' MST' INF FLO FHI AL16 SB WID HULL BUFC NR B0 BLO ACC BCL SEP FIR ART0 MI ST LOW LOR SPT S32 FRB CRB HK.
  pose proof (af_frames_range RT AF Σ m fO kO ART0 INF) as (F0 & FTOP & _ & FLIVE).
  pose proof (af_frames_align RT AF Σ m fO kO ART0 INF) as (_ & FSEG).
  pose proof (proj2 (af_fshadow_apart RT AF Σ m fO kO ART0 INF) fO kO INF) as FSELF.
  pose proof (fframe_ranges RT AF Σ m fO kO ART0 INF) as (_ & _ & _ & _ & SHT).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  unfold PJ_PAD_STACK_A, PJ_OS_XSPUTN_STACK_A in *. unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *. remember (fs_size kO) as FSZ eqn:EFSZ.
  assert (S0 : 0 <= S - 192) by (destruct ST; lia).
  assert (US : bv_unsigned (wz S) = S) by (apply unsigned_lit; lia).
  assert (US2 : bv_unsigned (wz (S - 192)) = S - 192) by (apply unsigned_lit; lia).
  assert (EO : bv_unsigned (wz OS) = OS) by (apply unsigned_lit; lia).
  assert (LBS : length bs = Z.to_nat CAP) by (destruct BUFC as [[[L _] _] _]; exact L).
  destruct HULL as [(bo & FO) SHBY].

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pad_walk0 S lo OS BUF N FILL ra gp (wz TPV_A) t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a6 a7 t3 t4 t5 t6 F fc m ST);
                   [lia| lia| lia| exact S32| lia| lia| lia| lia| lia| lia| exact (af_client_consts RT AF Σ m ART0)| exact MI]|].
  cbv beta. intros ms1 (m1 & a1' & a2' & j0 & j1 & j2 & j3 & j4 & j5 & j6 & j8 & j9 & j10 & -> & MU1 & WM1 & MI1 & ST1 & FRl1 & STp1 & FRs1). apply evt_done.
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 (S - 192) ART0 ltac:(ul)); [| exact WM1].
    intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. ul. }
  assert (PRES1 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) S (bv_unsigned a) -> m1 a = m a).
  { intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. destruct (aclient_split_c RT AF Σ m S _ ART0 Ha); ul. }

  unfold entry_st.
  eapply (aevt_smalloc1 RT PMc FDO MST RC2 Σ); [reflexivity| unfold FRAMES_MAX2, FRAMES_TOT in *; lia| lia| exact ART1| exact MI1| | intros Efr0; exfalso; rewrite Efr0 in INF; exact INF |].
  { unfold call_ok. rewrite US2. split; [exact ST1|]. split; [ul|]. split; [ul|]. split; [ul| Z.div_mod_to_equations; lia]. }
  intros Σ1 f w0 w1 w2 c1 c2 c3 c4 c5 c6 c7 w3 w4 w5 w6 F1 m2 (ART2 & MI2 & WM2 & ST2) PRES2 WRF WRS FRS1 LV1 SP1 CR1 FPOS F64 FTOP1.
  rewrite US2 in ST2, PRES2. rewrite (ret_pc_even 0xb1a28) by lia.
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
  assert (FD8 : 0xd9c00 <= f / 8) by (unfold SEGTOP_A in FSEG1; clear - FSEG1; Z.div_mod_to_equations; lia).
  assert (LOW' : 0x7fff7f800000 <= lo) by (clear - SP0W LOW; lia). unfold SEGTOP_A, STACK_WIN, USTACK_TOP in *.

  assert (AG02 : forall (P : Z -> Prop), (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) S x /\ ~ (S - 192 <= x < S)) -> agree_on P m m2).
  { intros P HP a Ha. destruct (HP _ Ha) as [H1 H2]. rewrite (PRES2 a); [exact (PRES1 a H1)|].
    apply (aclient_mono _ _ _ _ _ _ _ H1); [auto| auto| lia]. }
  assert (AG12 : forall (P : Z -> Prop), (forall x, P x -> S - 192 <= x < S) -> agree_on P m1 m2).
  { intros P HP a Ha. apply PRES2. left. pose proof (HP _ Ha). ul. }
  assert (CL : forall sp' x, (fO <= x < fO + FSZ - 8) \/ (fO / 8 + 2147450880 <= x < (fO + FSZ) / 8 + 2147450880) \/ (BUF <= x < BUF + CAP) ->
            aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x).
  { intros sp' x [H|[H|H]]; [right; right; right; left| do 4 right|]; [exists fO, kO; rewrite <- EFSZ; split; [exact INF| exact H]
      | exists fO, kO; rewrite <- EFSZ; split; [exact INF| unfold shad, SHB; exact H]|].
    destruct BCL as [(p & k & Hin & P1 & P2)|(B1 & B2)]; [right; right; left; exists p, k; split; [exact Hin| lia]|].
    right; right; right; left. exists fO, kO. rewrite <- EFSZ. rewrite <- EFSZ in B2. split; [exact INF| lia]. }
  assert (FRl2 : rw_cells bsegs m2 (S - 192) (pad_locals0 j0 j1 j2 j3 j4 j5 j6 (BUF + N) j8 j9 j10)).
  { eapply rw_cells_agree_nw; [exact FRl1|]. apply AG12. intros x Hx. unfold pad_locals0 in Hx. cbn [cells_size csize Nat.add] in Hx. lia. }
  assert (FRs2 : rw_cells bsegs m2 (S - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { eapply rw_cells_agree_nw; [exact FRs1|]. apply AG12. intros x Hx. unfold fa_saved in Hx. cbn [cells_size csize Nat.add] in Hx. lia. }
  assert (STp2 : stk bsegs m2 (S - 192 + 88) (S - 104)) by (eapply stk_agree_nw; [exact STp1|]; apply AG12; intros x Hx; cbv beta in Hx; lia).
  assert (SB2 : rw_cells bsegs m2 OS (sb_cellsA pb (wz 0) (wz 0) dum)).
  { eapply rw_cells_agree_nw; [exact SB|]. apply AG02. intros x Hx. unfold sb_cellsA in Hx. cbn [cells_size csize Nat.add] in Hx.
    split; [apply (CL S); left; lia| clear - Hx FHI FTOP LOW LOR; lia]. }
  assert (WID2 : rw_cells bsegs m2 (OS + 160) [C8 (wz 0)]).
  { eapply rw_cells_agree_nw; [exact WID|]. apply AG02. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [apply (CL S); left; lia| clear - Hx FHI FTOP LOW LOR; lia]. }
  assert (FO2 : rw_cells bsegs m2 OS [CB 288 bo]).
  { eapply rw_cells_agree_nw; [exact FO|]. apply AG02. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [apply (CL S); left; lia| clear - Hx FHI FTOP LOW LOR; lia]. }
  assert (SHBY2 : bytes_at bsegs m2 (shad OS) (repeat z8 36)).
  { eapply bytes_at_agree; [exact SHBY|]. apply AG02. intros x Hx. rewrite repeat_length in Hx. unfold shad, SHB in *.
    split; [apply (CL S); right; left| clear - Hx FLO FHI SHT LOW LOR]; Z.div_mod_to_equations; lia. }
  assert (BUFC2 : rw_cells bsegs m2 BUF [CB (Z.to_nat CAP) bs]).
  { eapply rw_cells_agree_nw; [exact BUFC|]. apply AG02. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [apply (CL S); right; right; lia| clear - Hx BLO LOR NR; lia]. }
  assert (PRES2' : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) S (bv_unsigned a) -> m2 a = m a).
  { intros a Ha. apply AG02 with (P := fun x => x = bv_unsigned a); [| reflexivity]. intros x ->. split; [exact Ha|].
    destruct (aclient_split_c RT AF Σ m S _ ART0 Ha); ul. }
  clear PRES1 PRES2 AG12 AG02 FRl1 FRs1 STp1 ST1 MI1 ART1 MU1 WM1 SB WID FO SHBY BUFC.

  destruct (wr_at_rw_CB m2 f 24 (wr_at_sub m2 f 120 f 24 WRF ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jH & FH2).
  change (Z.to_nat 24) with 24%nat in FH2.
  apply (rw_cells_split_CB bsegs _ _ [] 24 _ [] [8; 8; 8]%nat) in FH2; [| reflexivity]. cbn [mk_CB_cells app] in FH2. forget_junk FH2.
  destruct (wr_at_rw_CB m2 (f / 8 + 2147450880) 16 WRS ltac:(lia)) as (jS & FS2).
  change (Z.to_nat 16) with 16%nat in FS2.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1]%nat) in FS2; [| reflexivity]. cbn [mk_CB_cells app] in FS2.
  lazymatch type of FS2 with rw_cells _ _ _ ?cs =>
    let ls := eval cbv in (map (fun c => match c with CB _ l => l | _ => [] end) cs) in
    change (rw_cells bsegs m2 (f / 8 + 2147450880) (map (fun l => CB 1 l) ls)) in FS2; set (lS := ls) in FS2;
    assert (LS : length lS = 16%nat) by reflexivity; clearbody lS
  end.

  apply (rw_cells_split_CB bsegs _ _ [] 288 _ [] [128; 32; 8; 120]%nat) in FO2; [| reflexivity]. cbn [mk_CB_cells app] in FO2. forget_junk FO2.
  takeZ FO2 1%nat (OS + 128)%Z FOa. clear FOa. takeZ FO2 1%nat (OS + 160)%Z HX2. takeZ FO2 1%nat (OS + 168)%Z FOb. clear FOb. rename FO2 into HY2.

  assert (CSEP : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) S a -> ~ (f <= a < f + 120) /\ ~ (f / 8 + 2147450880 <= a < f / 8 + 2147450880 + 16)).
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

  assert (EXIT : forall (mx : mem) (xra xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt0 xt1 xt2 xt3 xt4 xt5 xt6 : word) (Fx : bvmap 5 word) (pb' pp' ep' : word) (dum' hx hy : list byte),
    ART RT Σ1 mx -> mem_inv bsegs mx -> stk bsegs mx lo (S - 192) ->
    rw_cells bsegs mx (S - 192) [CB 8 j0; CB 8 j1; CB 8 j2; C8 (wz ((OS + 160) / 8 + 2147450880)); C8 (wz (OS + 160)); C8 (wz BUF); C8 (wz (OS / 8)); C8 (wz (BUF + N)); CB 8 j8; CB 8 j9; C8 (wz f)] ->
    stk bsegs mx (S - 192 + 88) (S - 104) -> rw_cells bsegs mx (S - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells bsegs mx OS (sb_cellsA pb' pp' ep' dum') -> rw_cells bsegs mx (OS + 128) [CB 32 hx] -> rw_cells bsegs mx (OS + 160) [C8 (wz 0)] ->
    rw_cells bsegs mx (OS + 168) [CB 120 hy] -> bytes_at bsegs mx (OS / 8 + 2147450880) (repeat z8 36) ->
    rw_cells bsegs mx f [C8 (wz 0x41b58ab3); C8 (wz 0x16a74); C8 (wz 0xb19a4)] ->
    rw_cells bsegs mx (f / 8 + 2147450880) (map C1 pad_sh12 ++ map (fun l => CB 1 l) (skipn 12 lS)) ->
    (forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) S (bv_unsigned a) -> outside [(OS + 40, OS + 128); (OS + 160, OS + 168)] (bv_unsigned a) -> mx a = m a) ->
    aevt RT PMc Σ1 K (MS (mkR xra (wz (S - 192)) gp (wz TPV_A) xt0 xt1 xt2 (wz S) (wz (S - 192)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                            (wz f) (wz OS) (wz 2147450880) (wz N) (wz 0) (wz f) (wz BUF) (wz 0) (wz 0) (wz (f / 8 + 2147450880)) xt3 xt4 xt5 xt6)
                       Fx (wz 0xb1c64) fc None mx (seg_rom bsegs))).
  { intros mx xra xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt0 xt1 xt2 xt3 xt4 xt5 xt6 Fx pb' pp' ep' dum' hx hy ARTx MIx STx FRlx STpx FRsx SBx HXx WIDx HYx SHx FHx FSx PRESx.
    takeZ FHx 1%nat (f + 8)%Z FH0. clear FHx.
    apply (aevt_evt RT AF PMc MST).
    takeZ FRlx 3%nat (S - 192 + 24)%Z Lpre. takeZ FRlx 2%nat (S - 192 + 40)%Z L0.
    eapply evt_cut; [eapply (pad_exit1 S (S - 192) f lo OS N BUF xra gp (wz TPV_A) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 _ pad_sh12 (skipn 12 lS) Fx fc mx);
                     [reflexivity| rewrite length_skipn, LS; reflexivity| lia| lia| lia| lia| exact FSELF1| lia| lia| | | lia| lia| lia| lia
                     | | exact L0| exact WIDx| exact FH0| exact FSx| exact MIx]|].
    { clear - FDJ FLO FHI. lia. }
    { clear - FSO1 FLO FHI. lia. }
    { change 288 with (8 * Z.of_nat 36). apply (shz_of_zero_run mx OS 36); [clear - AL16; Z.div_mod_to_equations; lia| lia| exact SHx]. }
    cbv beta. intros ms4 (m4 & -> & MU4 & WM4 & MI4 & WID4 & FH4 & FS4).
    assert (AG4 : forall P : Z -> Prop, (forall x, P x -> ~ (OS + 160 <= x < OS + 168) /\ ~ (f <= x < f + 8) /\ ~ (f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 16)) -> agree_on P mx m4).
    { intros P HP a Ha. apply MU4. cbn [outside]. destruct (HP _ Ha) as (H1 & H2 & H3). split; [exact H1| split; [exact H2| split; [exact H3| exact I]]]. }
    assert (ART4 : ART RT Σ1 m4).
    { apply (art_client_write RT AF Σ1 mx m4 (S - 192) ARTx ltac:(ul)); [| exact WM4]. intros a Ha. apply MU4. cbn [outside].
      split; [intros Hin; apply Ha; right; right; right; left; exists fO, kO; split; [exact INO1| lia]|].
      split; [intros Hin; apply Ha; right; right; right; left; exists f, 1%nat; split; [exact INF1| change (fs_size 1) with 128; lia]|].
      split; [| exact I]. intros Hin; apply Ha. do 4 right. exists f, 1%nat. split; [exact INF1|]. unfold shad, SHB. change (fs_size 1) with 128. clear - Hin FD0. Z.div_mod_to_equations. lia. }
    destruct (af_frame_release RT AF Σ1 m4 f 1%nat (rt_frames RT Σ) ART4 FRS1) as (Σ3 & fl & FLC & NAC & FL0 & FLW & FW & REL).
    change (fs_size 1) with 128 in FW. replace (f + 128 - 8) with (f + 120) in FW by lia. rewrite SP1 in FLW.
    assert (FRl4 : rw_cells bsegs m4 (S - 192 + 40) [C8 (wz BUF); C8 (wz (OS / 8)); C8 (wz (BUF + N)); CB 8 j8; CB 8 j9; C8 (wz f)]).
    { eapply rw_cells_agree_nw; [exact FRlx|]. apply AG4. intros x Hx. cbn [cells_size csize Nat.add] in Hx. clear - Hx FLO FHI FTOP LOW LOR FR1' SHT1. lia. }
    assert (Lm4 : rw_cells bsegs m4 (S - 192 + 24) [C8 (wz ((OS + 160) / 8 + 2147450880)); C8 (wz (OS + 160))]).
    { eapply rw_cells_agree_nw; [exact L0|]. apply AG4. intros x Hx. cbn [cells_size csize Nat.add] in Hx. clear - Hx FLO FHI FTOP LOW LOR FR1' SHT1. lia. }
    assert (L04 : rw_cells bsegs m4 (S - 192) [CB 8 j0; CB 8 j1; CB 8 j2]).
    { eapply rw_cells_agree_nw; [exact Lpre|]. apply AG4. intros x Hx. cbn [cells_size csize Nat.add] in Hx. clear - Hx FLO FHI FTOP LOW LOR FR1' SHT1. lia. }
    glueZ Lm4 FRl4. glueZ L04 Lm4.
    assert (STp4 : stk bsegs m4 (S - 192 + 88) (S - 104)) by (eapply stk_agree_nw; [exact STpx|]; apply AG4; intros x Hx; cbv beta in Hx; clear - Hx FLO FHI FTOP LOW LOR FR1' SHT1; lia).
    assert (FRs4 : rw_cells bsegs m4 (S - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
    { eapply rw_cells_agree_nw; [exact FRsx|]. apply AG4. intros x Hx. unfold fa_saved in Hx. cbn [cells_size csize Nat.add] in Hx. clear - Hx FLO FHI FTOP LOW LOR FR1' SHT1. lia. }
    assert (ST4 : stk bsegs m4 lo (S - 192)) by (eapply stk_agree_nw; [exact STx|]; apply AG4; intros x Hx; cbv beta in Hx; clear - Hx FLO FHI FTOP LOW LOR FR1' SHT1; Z.div_mod_to_equations; lia).
    eapply evt_cut; [eapply (pad_exit2 S (S - 192) f fl lo OS xra gp (wz TPV_A) xt0 xt1 xt2 (wz (-11)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 _ _ _ _ _ _ _ _ xt3 xt4 xt5 xt6
                               ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                               [CB 8 j0; CB 8 j1; CB 8 j2; C8 (wz ((OS + 160) / 8 + 2147450880)); C8 (wz (OS + 160)); C8 (wz BUF); C8 (wz (OS / 8)); C8 (wz (BUF + N)); CB 8 j8; CB 8 j9; C8 (wz f)] Fx fc m4);
                     [lia| lia| exact FL0| ul| lia| lia| ul| lia| reflexivity| lia| lia| exact ST4| exact L04| exact STp4| exact FRs4| exact FW| exact FLC| exact MI4]|].
    cbv beta. intros ms5 (m5 & -> & MU5 & WM5 & MI5 & ST5 & FLC5).
    destruct (REL m5 MU5 WM5 FLC5) as (ART5 & FRS5 & LV5 & SP5 & CR5 & AL5 & AM5).
    apply evt_done. apply (aevt_switch RT PMc Σ1 Σ3 K _ AL5 AM5).

    assert (AG5 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) S x /\ ~ (OS + 160 <= x < OS + 168)) -> agree_on P mx m5).
    { intros P HP a Ha. destruct (HP _ Ha) as [H1 H2]. pose proof (CSEP _ H1) as [C1 C2]. rewrite (MU5 a), (MU4 a); [reflexivity| |].
      - cbn [outside]. clear - H2 C1 C2. repeat split; try exact I; lia.
      - cbn [outside]. split; [| exact I]. intros E. apply NAC. rewrite LV1, FRS1. replace fl with (bv_unsigned a) by lia.
        destruct H1 as [H|[H|[H|[H|H]]]]; [exfalso; clear - H E FLW LOW LOR; ul| right; left; exact H| right; right; left; exact H
          | right; right; right; left; destruct H as (f9 & k9 & Hin & Hr); exists f9, k9; split; [right; exact Hin| exact Hr]
          | do 4 right; destruct H as (f9 & k9 & Hin & Hr); exists f9, k9; split; [right; exact Hin| exact Hr]]. }
    eapply (HK Σ3 xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 Fx m5 pb' pp' ep' dum' ART5 MI5 ST5);
      [| | | rewrite LV5, LV1; reflexivity| exact FRS5| rewrite SP5, SP1; reflexivity| rewrite CR5, CR1; lia|].
    - split.
      + assert (SB5 : rw_cells bsegs m5 OS (sb_cellsA pb' pp' ep' dum')).
        { eapply rw_cells_agree_nw; [exact SBx|]. apply AG5. intros x Hx. unfold sb_cellsA in Hx. cbn [cells_size csize Nat.add] in Hx. split; [apply (CL S); left; lia| lia]. }
        assert (HX5 : rw_cells bsegs m5 (OS + 128) [CB 32 hx]).
        { eapply rw_cells_agree_nw; [exact HXx|]. apply AG5. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [apply (CL S); left; lia| lia]. }
        assert (WID5 : rw_cells bsegs m5 (OS + 160) [C8 (wz 0)]).
        { eapply rw_cells_agree_nw; [exact WID4|]. apply (agree_of_munch _ _ _ _ MU5). intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbn [outside]. split; [| exact I].
          intros E. apply NAC. replace fl with x by lia. right; right; right; left. exists fO, kO. split; [exact INO1| rewrite <- EFSZ; lia]. }
        assert (HY5 : rw_cells bsegs m5 (OS + 168) [CB 120 hy]).
        { eapply rw_cells_agree_nw; [exact HYx|]. apply AG5. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [apply (CL S); left; lia| lia]. }
        unfold sb_cellsA in SB5. glueZ WID5 HY5. glueZ HX5 WID5. glueZ SB5 HX5.
        destruct (rw_cells_forget bsegs m5 OS _ SB5) as (bo5 & H5). exists bo5. exact H5.
      + eapply bytes_at_agree; [exact SHx|]. apply AG5. intros x Hx. rewrite repeat_length in Hx. unfold shad, SHB in Hx.
        split; [apply (CL S); right; left; clear - Hx FLO FHI F0; Z.div_mod_to_equations; lia| clear - Hx FLO FHI F0 FSELF; unfold shad, SHB in *; Z.div_mod_to_equations; lia].
    - eapply rw_cells_agree_nw; [exact SBx|]. apply AG5. intros x Hx. unfold sb_cellsA in Hx. cbn [cells_size csize Nat.add] in Hx. split; [apply (CL S); left; lia| lia].
    - eapply rw_cells_agree_nw; [exact WID4|]. apply (agree_of_munch _ _ _ _ MU5). intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbn [outside]. split; [| exact I].
      intros E. apply NAC. replace fl with x by lia. right; right; right; left. exists fO, kO. split; [exact INO1| rewrite <- EFSZ; lia].
    - intros a Ha Ho. rewrite <- (PRESx a Ha Ho). apply (AG5 (fun x => x = bv_unsigned a)); [| reflexivity]. intros x ->. split; [exact Ha|].
      cbn [outside] in Ho. lia. }

  apply (aevt_evt RT AF PMc MST). unfold SHB.
  lazymatch type of FH2 with rw_cells _ _ _ [CB 8 ?h0; CB 8 ?h1; CB 8 ?h2] =>
  eapply evt_cut; [eapply (pad_segA S f OS BUF N FILL lo gp (wz TPV_A) w0 w1 w2 c1 c2 c3 c4 c5 c6 c7 s2 s7 s9 s11 w3 w4 w5 w6 j0 j1 j2 j3 j4 j5 j6 j8 j9 j10 h0 h1 h2 lS F1 fc m2 LS);
                   [lia| lia| exact FD8| lia| exact FSELF1| lia| lia| exact AL16| | | | | exact LOW'| lia| lia| lia| lia| lia| lia
                   | exact SHBY2| exact FRl2| exact WID2| exact FH2| exact FS2| exact MI2]|] end.
  { clear - FLO FHI SHT LOW. unfold shad, SHB in *. Z.div_mod_to_equations. lia. }
  { clear - FDJ FLO FHI. lia. }
  { clear - OSF1 FLO FHI. Z.div_mod_to_equations. lia. }
  { clear - FSO1 FLO FHI. lia. }
  cbv beta. intros ms3 (m3 & -> & MU3 & WM3 & MI3 & FRl3 & WID3 & FH3 & FS3). apply evt_done.
  assert (AG3 : forall P : Z -> Prop, (forall x, P x -> ~ (S - 192 <= x < S - 104) /\ ~ (f <= x < f + 24) /\ ~ (f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 16)) -> agree_on P m2 m3).
  { intros P HP a Ha. apply MU3. cbn [outside]. destruct (HP _ Ha) as (H1 & H2 & H3). split; [exact H1| split; [exact H2| split; [exact H3| exact I]]]. }
  assert (ART3 : ART RT Σ1 m3).
  { apply (art_client_write RT AF Σ1 m2 m3 (S - 192) ART2 ltac:(ul)); [| exact WM3]. intros a Ha. apply MU3. cbn [outside].
    split; [intros Hin; apply Ha; left; ul|].
    split; [intros Hin; apply Ha; right; right; right; left; exists f, 1%nat; split; [exact INF1| change (fs_size 1) with 128; lia]|].
    split; [| exact I]. intros Hin; apply Ha. do 4 right. exists f, 1%nat. split; [exact INF1|]. unfold shad, SHB. change (fs_size 1) with 128. clear - Hin FD0. Z.div_mod_to_equations. lia. }
  assert (PRES3 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) S (bv_unsigned a) -> m3 a = m a).
  { intros a Ha. rewrite <- (PRES2' a Ha). apply MU3. pose proof (CSEP _ Ha) as [C1 C2]. destruct (aclient_split_c RT AF Σ m S _ ART0 Ha) as [X|X]; cbn [outside];
      (split; [| split; [clear - C1; lia| split; [exact C2| exact I]]]); clear - X LOW LOR; ul. }
  Local Ltac by3 H AG := eapply rw_cells_agree_nw; [exact H|]; apply AG; intros x Hx; cbn [sb_cellsA fa_saved cells_size csize Nat.add] in Hx.
  assert (FRs3 : rw_cells bsegs m3 (S - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)) by (by3 FRs2 AG3; clear - Hx FR1' SHT1 LOW LOR; lia).
  assert (STp3 : stk bsegs m3 (S - 192 + 88) (S - 104)) by (eapply stk_agree_nw; [exact STp2|]; apply AG3; intros x Hx; cbv beta in Hx; clear - Hx FR1' SHT1 LOW LOR; lia).
  assert (ST3 : stk bsegs m3 lo (S - 192)) by (eapply stk_agree_nw; [exact ST2|]; apply AG3; intros x Hx; cbv beta in Hx; clear - Hx FR1' SHT1 LOW LOR; lia).
  assert (SB3 : rw_cells bsegs m3 OS (sb_cellsA pb (wz 0) (wz 0) dum)) by (by3 SB2 AG3; clear - Hx FLO FHI FTOP LOW LOR FDJ FSO1; lia).
  lazymatch type of HX2 with rw_cells _ _ _ ?cs => assert (HX3 : rw_cells bsegs m3 (OS + 128) cs) by (by3 HX2 AG3; clear - Hx FLO FHI FTOP LOW LOR FDJ FSO1; lia) end.
  lazymatch type of HY2 with rw_cells _ _ _ ?cs => assert (HY3 : rw_cells bsegs m3 (OS + 168) cs) by (by3 HY2 AG3; clear - Hx FLO FHI FTOP LOW LOR FDJ FSO1; lia) end.
  assert (BUFC3 : rw_cells bsegs m3 BUF [CB (Z.to_nat CAP) bs]).
  { eapply rw_cells_agree_nw; [exact BUFC2|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. rewrite (PRES3 a); [symmetry; exact (PRES2' a ltac:(apply (CL S); right; right; lia))|].
    apply (CL S); right; right; lia. }
  unfold id in SHBY2.
  assert (SHBY3 : bytes_at bsegs m3 (OS / 8 + 2147450880) (repeat z8 36)).
  { eapply bytes_at_agree; [exact SHBY2|]. apply AG3. intros x Hx. rewrite repeat_length in Hx. unfold shad, SHB in *.
    clear - Hx FLO FHI F0 SHT LOW LOR OSF1 FDJ. split; [| split]; Z.div_mod_to_equations; lia. }
  assert (PRES3' : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) S (bv_unsigned a) -> outside [(OS + 40, OS + 128); (OS + 160, OS + 168)] (bv_unsigned a) -> m3 a = m a)
    by (intros a Ha _; exact (PRES3 a Ha)).
  clear AG3 MU3 WM3 FRl2 WID2 FH2 FS2 FRs2 STp2 ST2 SB2 HX2 HY2 BUFC2 SHBY2 MI2 WM2.
  destruct (Z.eq_dec N 0) as [N0|N1].
  -
    apply (aevt_evt RT AF PMc MST). zstep. if_cases KN; zify_cond KN; [| exfalso; lia]. apply evt_done.
    exact (EXIT m3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 pb (wz 0) (wz 0) dum _ _ ART3 MI3 ST3 FRl3 STp3 FRs3 SB3 HX3 WID3 HY3 SHBY3 FH3 FS3 PRES3').
  -
    assert (SHZ3 : shz m3 OS 288).
    { change 288 with (8 * Z.of_nat 36). apply (shz_of_zero_run m3 OS 36); [clear - AL16; Z.div_mod_to_equations; lia| lia| exact SHBY3]. }
    assert (SHV3 : shz m3 PJ_NULSB_VT_A 24).
    { pose proof (shz_of_acc m3 PJ_NULSB_VT_A 24 (proj1 (VTACC Σ1 m3 ART3)) eq_refl ltac:(unfold PJ_NULSB_VT_A; lia)) as X. exact X. }
    pose proof (ROA Σ1 m3 ART3) as (VT3 & _).
    pose proof SB3 as SBc. unfold sb_cellsA in SBc. takeZ SBc 1%nat (OS + 8)%Z SBV. clear SBc.
    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut; [eapply (pad_segB S f OS BUF N lo gp (wz TPV_A) w0 w1 w2 c5 c6 c7 w3 w4 w5 w6 j0 j1 j2 j8 j9 F1 fc m3);
                     [lia| lia| lia| lia| exact AL16| lia| lia| lia| lia| lia| exact SHZ3| exact SHV3| exact FRl3| exact SBV| exact VT3| exact MI3]|].
    cbv beta. intros ms4 <-. apply evt_done.
    assert (HULL3 : os_hullA m3 OS).
    { split; [| unfold shad, SHB; exact SHBY3]. pose proof SB3 as SBc. pose proof WID3 as WIDc. pose proof HX3 as HXc. pose proof HY3 as HYc. unfold sb_cellsA in SBc.
      glueZ WIDc HYc. glueZ HXc WIDc. glueZ SBc HXc. destruct (rw_cells_forget bsegs m3 OS _ SBc) as (bo3 & H3). exists bo3. exact H3. }
    assert (ACC3 : acc bsegs m3 BUF N).
    { destruct BCL as [(p & k & Hin & P1 & P2)|(B1 & B2)].
      - apply (acc_sub bsegs m3 p k); [exact (proj2 (af_acc_live RT AF Σ1 m3 p k ART3 ltac:(rewrite LV1; exact Hin)))| lia| lia].
      - apply (acc_agreeP m m3 BUF N ACC). intros a Ha. apply PRES3. do 4 right. exists fO, kO. split; [exact INF|]. rewrite <- EFSZ in *. unfold shad, SHB in *.
        clear - Ha B1 B2 NR. Z.div_mod_to_equations. lia. }
    assert (BCL1 : buf_clsA RT Σ1 fO kO BUF CAP) by (unfold buf_clsA; rewrite LV1; exact BCL).
    eapply (XSP Σ1 K OS BUF N CAP (S - 192) lo fO kO pb dum bs); [exact FDO| exact MST| exact INO1| exact FLO| rewrite <- EFSZ; exact FHI| exact AL16| exact SB3| exact HULL3
      | exact (ROA Σ1 m3 ART3)| exact BUFC3| lia| lia| lia| exact ACC3| exact BCL1| exact SEP| exact ART3| exact MI3| exact ST3| rewrite SP1; ul| ul| ul
      | clear - S32; Z.div_mod_to_equations; lia|].
    intros x0 x1 x2 d1 d2 d3 d4 d5 d6 d7 x3 x4 x5 x6 F4 m4 pb' pp' ep' dum' ART4 MI4 ST4 HULL4 SB4 PRES4. rewrite (ret_pc_even 0xb1c60) by lia.
    apply (aevt_evt RT AF PMc MST). zstep. if_cases KB; zify_cond KB; [exfalso; clear - KB; lia|]. apply evt_done.
    assert (AG4 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) (S - 192) x /\ ~ (OS + 40 <= x < OS + 128)) -> agree_on P m3 m4).
    { intros P HP a Ha. destruct (HP _ Ha) as [H1 H2]. apply PRES4; [exact H1| cbn [outside]; split; [exact H2| exact I]]. }
    assert (CL1 : forall sp' x, (S - 192 <= x < S /\ sp' <= S - 192) \/ (fO <= x < fO + FSZ - 8) \/ (fO / 8 + 2147450880 <= x < (fO + FSZ) / 8 + 2147450880)
                               \/ (f <= x < f + 120) \/ (f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 16) -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) sp' x).
    { intros sp' x [[H1 H2]|[H|[H|[H|H]]]]; [left; ul| right; right; right; left| do 4 right| right; right; right; left| do 4 right].
      - exists fO, kO. rewrite <- EFSZ. split; [exact INO1| exact H].
      - exists fO, kO. rewrite <- EFSZ. split; [exact INO1| unfold shad, SHB; exact H].
      - exists f, 1%nat. split; [exact INF1| change (fs_size 1) with 128; lia].
      - exists f, 1%nat. split; [exact INF1| unfold shad, SHB; change (fs_size 1) with 128; clear - H FD0; Z.div_mod_to_equations; lia]. }
    Local Ltac by4 H AG := eapply rw_cells_agree_nw; [exact H|]; apply AG; intros x Hx; cbn [sb_cellsA fa_saved cells_size csize Nat.add length app map pad_sh12 repeat] in Hx.
    assert (FRl4 : rw_cells bsegs m4 (S - 192) [CB 8 j0; CB 8 j1; CB 8 j2; C8 (wz ((OS + 160) / 8 + 2147450880)); C8 (wz (OS + 160)); C8 (wz BUF); C8 (wz (OS / 8)); C8 (wz (BUF + N)); CB 8 j8; CB 8 j9; C8 (wz f)])
      by (by4 FRl3 AG4; split; [apply (CL1 (S - 192)); left; lia| clear - Hx FLO FHI FTOP LOW LOR; lia]).
    assert (FRs4 : rw_cells bsegs m4 (S - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)) by (by4 FRs3 AG4; split; [apply (CL1 (S - 192)); left; lia| clear - Hx FLO FHI FTOP LOW LOR; lia]).
    assert (STp4 : stk bsegs m4 (S - 192 + 88) (S - 104)).
    { eapply stk_agree_nw; [exact STp3|]. apply AG4. intros x Hx. cbv beta in Hx. split; [apply (CL1 (S - 192)); left; lia| clear - Hx FLO FHI FTOP LOW LOR; lia]. }
    assert (WID4 : rw_cells bsegs m4 (OS + 160) [C8 (wz 0)]) by (by4 WID3 AG4; split; [apply (CL1 (S - 192)); right; left; lia| lia]).
    lazymatch type of HX3 with rw_cells _ _ _ ?cs => assert (HX4 : rw_cells bsegs m4 (OS + 128) cs) by (by4 HX3 AG4; split; [apply (CL1 (S - 192)); right; left; lia| lia]) end.
    lazymatch type of HY3 with rw_cells _ _ _ ?cs => assert (HY4 : rw_cells bsegs m4 (OS + 168) cs) by (by4 HY3 AG4; split; [apply (CL1 (S - 192)); right; left; lia| lia]) end.
    assert (FH4 : rw_cells bsegs m4 f [C8 (wz 0x41b58ab3); C8 (wz 0x16a74); C8 (wz 0xb19a4)]) by (by4 FH3 AG4; split; [apply (CL1 (S - 192)); right; right; right; left; lia| clear - Hx FDJ FLO FHI; lia]).
    assert (LS4 : length (skipn 12 lS) = 4%nat) by (rewrite length_skipn, LS; reflexivity).
    assert (FS4 : rw_cells bsegs m4 (f / 8 + 2147450880) (map C1 pad_sh12 ++ map (fun l => CB 1 l) (skipn 12 lS))).
    { eapply rw_cells_agree_nw; [exact FS3|]. apply AG4. intros x Hx. rewrite cells_size_app, cells_size_map_C1p, cells_size_map_CB1, LS4 in Hx.
      cbn [length pad_sh12 app repeat Nat.add] in Hx. split; [apply (CL1 (S - 192)); do 4 right; lia| clear - Hx FSO1 FLO FHI; lia]. }
    destruct HULL4 as [_ SHBY4]. unfold shad, SHB in SHBY4.
    assert (PRES4' : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) S (bv_unsigned a) -> outside [(OS + 40, OS + 128); (OS + 160, OS + 168)] (bv_unsigned a) -> m4 a = m a).
    { intros a Ha Ho. rewrite <- (PRES3 a Ha). apply PRES4; [| cbn [outside] in Ho |- *; split; [lia| exact I]].
      apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LV1; auto| rewrite FRS1; intros e He; right; exact He| lia]. }
    exact (EXIT m4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F4 pb' pp' ep' dum' _ _ ART4 MI4 ST4 FRl4 STp4 FRs4 SB4 HX4 WID4 HY4 SHBY4 FH4 FS4 PRES4').
Qed.
End Pad.
