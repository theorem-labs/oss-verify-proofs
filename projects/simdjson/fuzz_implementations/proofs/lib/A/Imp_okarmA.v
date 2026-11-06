(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep ZBridge.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel ImpModel.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Startup_glue Sj_stage1_kit Pj_loc_kit Pj_os_kit.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A Require Import Layout Shadow RT_iface RT_iface2 RT_iface3 IcptSpec D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps
     Sj_hkit Sj_new Sj_num_akit Sj_num_amem Sj_num_aframe Atp_fzwA Atp_hkit4A Pj_lftoi1A Pj_rtkA Pj_defsA Pj_hdefsA Pj_cpsA Pj_os_defsA Pj_loc_getA
     Imp_hdefsA Imp_ifaceA Imp_oss_defsA Imp_okarm1A.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A Require Import Imp_ios_defsA.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition okclI (S1 f : Z) (L : list (Z * Z)) (x : Z) : Prop :=
  (S1 <= x < USTACK_TOP) \/ (f <= x < f + 2040) \/ (shad f <= x < shad f + 256) \/ (PJ_LOC_LO_A <= x < PJ_LOC_HI_A) \/ in_live L x.

Lemma cells_size_map_C1o : forall bs : list byte, cells_size (map C1 bs) = length bs.
Proof. induction bs as [|b bs IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.
Lemma cells_bytes_map_C1o : forall l : list byte, cells_bytes (map C1 l) = l.
Proof. induction l as [|b l IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.
Lemma imp_sh_parts : forall (m : mem) A a b c, rw_cells asegs m A (map C1 (imp_sh a b c)) ->
  rw_cells asegs m (A + 4) (map C1 (repeat (Z_to_bv 8 a) 11)) /\ rw_cells asegs m (A + 20) (map C1 (repeat (Z_to_bv 8 0) 68))
  /\ rw_cells asegs m (A + 104) (map C1 (repeat (Z_to_bv 8 b) 33)) /\ rw_cells asegs m (A + 146) (map C1 (repeat (Z_to_bv 8 c) 3)).
Proof.
  intros m A a b c H. unfold imp_sh in H. rewrite !map_app in H.
  apply rw_cells_app in H. destruct H as [_ H]. rewrite cells_size_map_C1o, repeat_length in H.
  apply rw_cells_app in H. destruct H as [H1 H]. rewrite cells_size_map_C1o, repeat_length in H.
  apply rw_cells_app in H. destruct H as [_ H]. rewrite cells_size_map_C1o, repeat_length in H.
  apply rw_cells_app in H. destruct H as [H2 H]. rewrite cells_size_map_C1o, repeat_length in H.
  apply rw_cells_app in H. destruct H as [_ H]. rewrite cells_size_map_C1o, repeat_length in H.
  apply rw_cells_app in H. destruct H as [H3 H]. rewrite cells_size_map_C1o, repeat_length in H.
  apply rw_cells_app in H. destruct H as [_ H]. rewrite cells_size_map_C1o, repeat_length in H.
  apply rw_cells_app in H. destruct H as [H4 _].
  split; [replace (A + 4) with (A + Z.of_nat 4) by lia; exact H1|].
  split; [replace (A + 20) with (A + Z.of_nat 4 + Z.of_nat 11 + Z.of_nat 5) by lia; exact H2|].
  split; [replace (A + 104) with (A + Z.of_nat 4 + Z.of_nat 11 + Z.of_nat 5 + Z.of_nat 68 + Z.of_nat 16) by lia; exact H3|].
  replace (A + 146) with (A + Z.of_nat 4 + Z.of_nat 11 + Z.of_nat 5 + Z.of_nat 68 + Z.of_nat 16 + Z.of_nat 33 + Z.of_nat 9) by lia; exact H4.
Qed.
Lemma run_bytes : forall (m : mem) A (b : byte) n, rw_cells asegs m A (map C1 (repeat b n)) -> bytes_at asegs m A (repeat b n).
Proof. intros m A b n H. pose proof (rw_cells_bytes_at asegs m A _ H) as X. rewrite cells_bytes_map_C1o in X. exact X. Qed.

Lemma ok_walk4 : forall (S1 usp f buf size cap : Z) (gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s10 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < f -> f + 2048 < 2^63 -> 0 <= buf < 2^64 -> 0 <= size < 2^64 -> 0 <= cap < 2^64 ->
  rw_cells asegs m (f + 96) [C8 (wz buf); C8 (wz size); C8 (wz cap)] ->
  mem_inv asegs m ->
  evt asegs (eq (MS (mkR (wz 0xb5144) (wz S1) gp (wz TPV_A) t0 t1 t2 (wz usp) (wz S1) (wz (f + 832)) (wz buf) (wz size) a3 a4 a5 a6 a7
                        (wz (-8)) (wz (shad f)) (wz 1) (wz (f + 32)) (wz (f + 160)) s7 (wz SHB) (wz (f + 832)) s10 (wz (f + 192)) t3 t4 t5 t6)
                   F (wz OSS_PUT_A) fc None m (seg_rom asegs)))
    (MS (mkR (wz 0xb5134) (wz S1) gp (wz TPV_A) t0 t1 t2 (wz usp) (wz S1) a0 a1 a2 a3 a4 a5 a6 a7
             (wz (-8)) (wz (shad f)) (wz 1) (wz (f + 32)) (wz (f + 160)) s7 (wz SHB) (wz (f + 832)) s10 (wz (f + 192)) t3 t4 t5 t6)
        F (wz 0xb5134) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros F0 FH BR SR CR SC MI. unfold OSS_PUT_A in *.
  assert (E32 : bv_unsigned (Z_to_bv 64 (f + 32)) = f + 32) by (apply unsigned_lit; lia).
  zstep. zstep. zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma ok_walk5 : forall (S1 usp f buf size cap szw dw : Z) (gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < f -> f + 2048 < 2^63 -> 0 < buf < 2^64 -> 0 <= size < 2^64 -> 0 <= cap < 2^64 -> 0 <= S1 -> S1 + 336 < 2^63 -> (f + 2048 <= S1) ->
  rw_cells asegs m (f + 96) [C8 (wz buf); C8 (wz size); C8 (wz cap)] ->
  rw_cells asegs m (S1 + 80) (imp_locals f (shad f) szw dw) ->
  mem_inv asegs m ->
  evt asegs (fun ms =>
      (buf = f + 32 /\ ms = MS (mkR (wz 0xb5144) (wz S1) gp (wz TPV_A) t0 t1 t2 (wz usp) (wz S1) (wz buf) a1 a2 a3 a4 a5 a6 a7
                                   (wz (-8)) (wz (shad f)) (wz 1) (wz (f + 32)) (wz (f + 160)) s7 (wz SHB) (wz (f + 832)) s10 (wz dw) t3 t4 t5 t6)
                              F (wz 0xb5158) fc None m (seg_rom asegs))
      \/ (buf <> f + 32 /\ ms = MS (mkR (wz 0xb5158) (wz S1) gp (wz TPV_A) t0 t1 t2 (wz usp) (wz S1) (wz buf) a1 a2 a3 a4 a5 a6 a7
                                      (wz (-8)) (wz (shad f)) (wz 1) (wz (f + 32)) (wz (f + 160)) s7 (wz SHB) (wz (f + 832)) s10 (wz dw) t3 t4 t5 t6)
                                 F (wz OPDELARR_A) fc None m (seg_rom asegs)))
    (MS (mkR (wz 0xb5144) (wz S1) gp (wz TPV_A) t0 t1 t2 (wz usp) (wz S1) a0 a1 a2 a3 a4 a5 a6 a7
             (wz (-8)) (wz (shad f)) (wz 1) (wz (f + 32)) (wz (f + 160)) s7 (wz SHB) (wz (f + 832)) s10 s11 t3 t4 t5 t6)
        F (wz 0xb5144) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros F0 FH BR SR CR S0 S1H FS1 SC LOC MI. unfold OPDELARR_A, imp_locals in *.
  assert (E32 : bv_unsigned (Z_to_bv 64 (f + 32)) = f + 32) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 S1) = S1) by (apply unsigned_lit; lia).
  replace (f + 832 + 16) with (f + 848) in LOC by lia. replace (f + 832 + 8) with (f + 840) in LOC by lia. replace (f + 832 + 112) with (f + 944) in LOC by lia.
  zstep. zstep.
  zstep. if_cases K; zify_cond K.
  - apply evt_done. left. split; [lia| cbv delta [mkR]; reflexivity].
  - zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
    zstep. apply evt_done. right. split; [lia| cbv delta [mkR]; reflexivity].
Qed.

Lemma rw_cells_C1_read1 : forall (m : mem) A (b : byte) rest,
  rw_cells asegs m A (C1 b :: rest) -> ov_read_bytes asegs m (wa A) 1 = Some [b].
Proof.
  intros m A b rest [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb.
  pose proof (bytes_at_read asegs m A _ 0 1 Hb ltac:(lia)) as R.
  rewrite Z.add_0_r in R. rewrite R; [reflexivity|]. cbn. lia.
Qed.

Lemma ok_walk8b : forall (S1 usp f szw dw capw capm dat : Z) (gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s10 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < f -> f + 2048 < 2^63 -> 0 <= capw < 2^64 -> 0 <= dat < 2^64 ->
  rw_cells asegs m (f + 904) [C8 (wz capw); C8 (wz capm); C8 (wz dat)] ->
  mem_inv asegs m ->
  evt asegs (eq (MS (mkR (wz 0xb5270) (wz S1) gp (wz TPV_A) t0 t1 t2 (wz usp) (wz S1) (wz dat) (wz (Z.land capw 18446744073709551614)) a2 a3 a4 a5 a6 a7
                        (wz (-8)) (wz (shad f)) (wz OSS_VTT_A) (wz szw) (wz (f + 160)) s7 (wz SHB) (wz (f + 832)) s10 (wz dw) t3 t4 t5 t6)
                   F (wz OPDEL_A) fc None m (seg_rom asegs)))
    (MS (mkR (wz 0xb51d0) (wz S1) gp (wz TPV_A) t0 t1 t2 (wz usp) (wz S1) a0 a1 a2 a3 a4 a5 a6 a7
             (wz (-8)) (wz (shad f)) (wz OSS_VTT_A) (wz szw) (wz (f + 160)) s7 (wz SHB) (wz (f + 832)) s10 (wz dw) t3 t4 t5 t6)
        F (wz 0xb5260) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros F0 FH CR DR REP MI. unfold OPDEL_A, OSS_VTT_A in *.
  assert (EO : bv_unsigned (Z_to_bv 64 (f + 832)) = f + 832) by (apply unsigned_lit; lia).
  zstep. zstep. zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma u8_litI : forall x, bv_unsigned (Z_to_bv 8 x) = x mod 256.
Proof. intros x. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma locx3_agreeI : forall m m' : mem, locx3 m -> agree_on (fun a => PJ_LOC_LO_A <= a < PJ_LOC_HI_A) m m' -> locx3 m'.
Proof.
  intros m m' (H1 & H2 & H3) AG. unfold locx3, LOC_CVC, LOC_CVW, PJ_LOC_LO_A, PJ_LOC_HI_A in *.
  split; [| split]; (eapply rw_cells_agree_nw; [eassumption|]; intros a Ha; apply AG; cbv beta in Ha; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ha; lia).
Qed.

Section Okarm.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis RC2 : rt_contracts2 RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis ROWS : forall Σ m, ART RT Σ m -> imp_rowsA m.
Hypothesis CTOR : oss_ctorA_cps RT PMc.
Hypothesis SER : ser_cpsA RT PMc TAPE_MAX_DEPTH.
Hypothesis PUT : putA_cps RT PMc.
Hypothesis STR : strA_cps RT PMc.
Hypothesis LOCD : locdtor_evtA.
Hypothesis IOSD : ios_dtorA_cps RT PMc.

Local Ltac ul := unfold IMP_OKARM_STACK_A, PJ_SER_STACK_A, ser_needA, PJ_TC_STACK_A, OSS_CTOR_STACK_A, OSS_PUT_STACK_A, OSS_XSPUTN_STACK_A, OSS_OV_STACK_A, OSS_PB_STACK_A,
                           OSS_STR_STACK_A, OSS_IOS_DTOR_STACK_A, PJ_IOS_DTOR_STACK_A, PJ_LOC_STACK_A in *;
                 unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, LIVE_MAX in *; lia.
Local Ltac outW Ho := cbn [outside] in Ho |- *; repeat split; try exact I; lia.

Theorem imp_okarm_okA : imp_okarm_cpsA RT PMc.
Proof using AF RC RC2 FDO MST ROWS CTOR SER PUT STR LOCD IOSD.
  intros Σ K E S1 usp szw dw ra gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s7 s10 s11 t3 t4 t5 t6 Fr fc m j20 jsb jel jos jtmp
    FDO' MST' OK KF ESB EDOC LV DR0 LB0 LX0 NL0 LOCKW0 IOS0 SRET LOC SZW DW FB0 FEL FOUT FO0 FTMP FS0 ART0 MI0 ST0 LOQ UT S32 USP FRM FRS LVB CR0 HK.
  destruct E as [lo f kF SB DOC TAPE NT SBUF NS tws sbs len L].
  cbn [pa_lo pa_F pa_kF pa_SB pa_DOC pa_TAPE pa_NT pa_SBUF pa_NS pa_tws pa_sbs pa_len pa_L] in *. subst kF SB DOC.
  pose proof (ok_sb _ OK) as (SB32 & _ & _). pose proof (ok_frame _ OK) as (F64 & FSEG & FLO). pose proof (ok_lo _ OK) as LOW.
  pose proof (ok_len _ OK) as LEN. pose proof (ok_Lpos _ OK) as LPOS. pose proof (ok_wfS _ OK) as WFS.
  pose proof (ok_tape _ OK) as (_ & TN8 & _ & _ & INT). pose proof (ok_sbuf _ OK) as (_ & SNS & _ & _ & INS).
  cbn [pa_lo pa_F pa_kF pa_SB pa_DOC pa_TAPE pa_NT pa_SBUF pa_NS pa_tws pa_sbs pa_len pa_L] in SB32, F64, FSEG, FLO, LOW, LEN, LPOS, WFS, TN8, INT, SNS, INS.
  change (fs_size 5) with 2048 in FLO.
  unfold tape_wfS in WFS. destruct WFS as (N2 & SNB & _ & _ & ELS).
  pose proof LV as (LVE & INF & SPLO). cbn [pa_lo pa_F pa_kF pa_SB pa_L sbchunkA sbA0 sa_heap app] in LVE, INF, SPLO. unfold STACK_WIN in SPLO.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (fframe_ranges RT AF Σ m f 5 ART0 INF) as (FPOS & FR1 & _ & SHB0 & SHT).
  pose proof (proj2 (af_fshadow_apart RT AF Σ m f 5%nat ART0 INF) f 5%nat INF) as FSELF.
  pose proof (af_frames_hi RT AF Σ m f 5%nat ART0 INF) as FRHI.
  change (fs_size 5) with 2048 in FR1, SHT, FSELF, FRHI.
  assert (SHF : shad (f + 2048) = shad f + 256) by (unfold shad; Z.div_mod_to_equations; lia).
  rewrite SHF in SHT, FSELF. unfold SEGTOP_A in FSEG.
  assert (FD0 : 0 <= f / 8) by (apply Z.div_pos; lia).
  assert (SHLO : 0x7fff8000 <= shad f) by (unfold shad, SHB in *; lia).
  assert (EU : bv_unsigned (Z_to_bv 64 S1) = S1) by (apply unsigned_lit; ul). assert (LOS1 : lo + 64 <= S1) by ul.
  pose proof (PJ_CAPMAX_bound len LEN) as CAPB. pose proof (pj_psi_root len (f + 32) LEN) as PSI0. pose proof (os_psi_root len (f + 832) LEN) as OPSI0.

  assert (OIN : oss_inA f 5%nat (f + 832)) by (unfold oss_inA; change (fs_size 5) with 2048; split; [lia| split; [lia| Z.div_mod_to_equations; lia]]).

  assert (LRNG : forall p k, In (p, k) L -> 0 < p /\ p + k <= lo /\ (f + 2048 <= p \/ p + k <= f)
            /\ (p + k <= shad f \/ shad f + 256 <= p) /\ (p + k <= 0x10000 \/ 0x6d2000 <= p)).
  { intros p k Hin. rewrite <- LVE in Hin.
    pose proof (af_live_range RT AF Σ m p k ART0 Hin) as (Y0 & Y1 & Y2).
    pose proof (proj2 (proj2 (proj2 (af_frames_range RT AF Σ m f 5%nat ART0 INF))) p k Hin) as Y3.
    pose proof (proj1 (af_fshadow_apart RT AF Σ m f 5%nat ART0 INF) p k Hin) as Y4.
    change (fs_size 5) with 2048 in Y3, Y4. rewrite SHF in Y4. unfold SEGTOP_A, STACK_WIN in Y1, Y2. lia. }

  assert (CLA : forall (Σx : rts RT) x, rt_frames RT Σx = [(f, 5%nat)] -> (forall e, In e L -> In e (rt_live RT Σx)) ->
            okclI S1 f L x -> aclient (rt_live RT Σx) (rt_frames RT Σx) S1 x).
  { intros Σx x FRSx INCL [H|[H|[H|[H|H]]]].
    - left. exact H.
    - right; right; right; left. exists f, 5%nat. rewrite FRSx. split; [left; reflexivity| change (fs_size 5) with 2048; lia].
    - right; right; right; right. exists f, 5%nat. rewrite FRSx. split; [left; reflexivity| change (fs_size 5) with 2048; rewrite SHF; lia].
    - right; left. apply client_static_intro. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in H. lia.
    - right; right; left. destruct H as (p & k & Hin & Hr). exists p, k. split; [exact (INCL _ Hin)| exact Hr]. }
  assert (INCL0 : forall e, In e L -> In e (rt_live RT Σ)) by (intros e He; rewrite LVE; exact He).

  assert (CLW : forall (Σx : rts RT) (mx my : mem) W, rt_frames RT Σx = [(f, 5%nat)] -> (forall e, In e L -> In e (rt_live RT Σx)) -> munch W mx my ->
            Forall (fun iv => forall x, fst iv <= x < snd iv -> okclI S1 f L x) W ->
            agree_on (fun a => ~ aclient (rt_live RT Σx) (rt_frames RT Σx) S1 a) mx my).
  { intros Σx mx my W FRSx INCL MU HW a Ha. apply MU. clear MU. induction W as [|[lo' hi'] W IH]; [exact I|].
    apply Forall_cons_iff in HW. destruct HW as [H1 HW]. cbn [outside fst snd] in *. split; [| exact (IH HW)].
    intros Hin. apply Ha. apply (CLA Σx _ FRSx INCL). apply H1. exact Hin. }

  unfold imp_sh_pro in FS0. pose proof (imp_sh_parts m (shad f) (-8) (-8) (-8) FS0) as (_ & RUN68 & _ & _).
  assert (ACC_IMPLS : forall mx, rw_cells asegs mx (shad f + 20) (map C1 (repeat (Z_to_bv 8 0) 68)) -> acc asegs mx (f + 160) 544).
  { intros mx H. change 544 with (8 * Z.of_nat 68). apply (acc_zero_run asegs mx (f + 160) 68); [Z.div_mod_to_equations; lia| lia|].
    replace (shad (f + 160)) with (shad f + 20) by (unfold shad; Z.div_mod_to_equations; lia). exact (run_bytes mx _ _ _ H). }
  unfold imp_regsA.

  apply (aevt_evt RT AF PMc MST). zstep. zstep. zstep. zstep. zstep. apply evt_done.
  replace (f + 160 + 88) with (f + 248) by lia.
  pose proof SRET as SR. takeZ SR 2%nat (S1 + 208) SR16.
  pose proof (rw_cells_bytes_at asegs m _ _ SR16) as BY0. cbn [cells_bytes cbytes app] in BY0.
  apply (rw_cells_split_CB asegs _ _ [] 24 jel [] [16; 4; 4]%nat) in FEL; [| reflexivity]. cbn [mk_CB_cells app] in FEL. forget_junk FEL.
  rewrite app_nil_r in BY0. set (bs16 := le8 (Z_to_bv 64 (f + 192)) ++ le8 (Z_to_bv 64 1)) in BY0.
  assert (LB16 : length bs16 = 16%nat) by (subst bs16; rewrite length_app, !length_le8; reflexivity).
  assert (CS0 : checked_src RT Σ m (wz S1) lo (S1 + 192) (Z.of_nat (length bs16))).
  { rewrite LB16. unfold checked_src. rewrite EU. split; [| right; lia]. intros _. split.
    - apply (af_acc_stack RT AF Σ m (S1 + 192) 16 ART0); ul.
    - right; right; left. ul. }
  assert (CD0 : checked_dst RT Σ m (wz S1) (f + 248) (Z.of_nat (length bs16))).
  { rewrite LB16. unfold checked_dst. rewrite EU. split; [| split].
    - intros _. split; [apply (acc_sub asegs m (f + 160) 544); [exact (ACC_IMPLS m RUN68)| lia| lia]|].
      right; left. exists f, 5%nat. change (fs_size 5) with 2048. split; [exact INF| lia].
    - intros i Hi. right; right; right; left. exists f, 5%nat. change (fs_size 5) with 2048. split; [exact INF| lia].
    - apply (rw_cells_wr_at asegs m _ _ 16 FEL). cbn. lia. }
  assert (COK0 : call_ok RT Σ m (wz S1) lo).
  { unfold call_ok. rewrite EU. split; [exact ST0|]. split; [exact SPLO|]. split; [ul|]. split; [ul| clear - S32; Z.div_mod_to_equations; lia]. }
  eapply (aevt_memcpyP RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc m (f + 248) (S1 + 192) bs16 lo
            eq_refl eq_refl ltac:(rewrite LB16; reflexivity) ltac:(ul) ltac:(ul) ltac:(rewrite LB16; cbn; lia) BY0 CS0 CD0 ltac:(rewrite LB16; cbn; lia) ART0 MI0 COK0).
  intros x0 x1 x2 e1 e2 e3 e4 e5 e6 e7 x3 x4 x5 x6 F1 m1 (ART1 & MI1 & WM1 & ST1) PRES1 BY1. rewrite EU in ST1, PRES1. rewrite LB16 in PRES1. change (Z.of_nat 16) with 16 in PRES1.
  rewrite (ret_pc_even 0xb5030) by lia.

  assert (AG01 : forall P : Z -> Prop, (forall x, P x -> okclI S1 f L x /\ ~ (f + 248 <= x < f + 248 + 16)) -> agree_on P m m1).
  { intros P HP a Ha. destruct (HP _ Ha) as [H1 H2]. apply PRES1; [exact (CLA Σ _ FRS INCL0 H1)| exact H2]. }
  Local Ltac byAG H AG := eapply rw_cells_agree_nw; [exact H|]; apply AG; intros x Hx;
                          cbn [imp_locals cells_size csize Nat.add length app map repeat] in Hx; rewrite ?cells_size_map_C1o, ?imp_sh_length in Hx.

  pose proof (rw_cells_CB_intro m1 (f + 248) bs16 BY1 ltac:(rewrite LB16; apply (wr_at_transport asegs m m1 (f + 248) 16); [apply (rw_cells_wr_at asegs m _ _ 16 FEL); cbn; lia| exact WM1])) as EL1.
  rewrite LB16 in EL1.
  apply (rw_cells_recastI m1 (f + 248) _ [C8 (wz (f + 192)); C8 (wz 1)]) in EL1; [| cbn; repeat split; reflexivity| subst bs16; cbn [cells_bytes cbytes app]; rewrite ?app_nil_r; reflexivity| reflexivity].
  takeZ FEL 1%nat (f + 264) FE16. clear FE16.
  lazymatch type of FEL with rw_cells _ _ _ ?cs => assert (FEL1 : rw_cells asegs m1 (f + 264) cs) by (byAG FEL AG01; split; [right; left; lia| lia]) end.
  pose proof (rw_cells_joinA _ _ _ _ _ EL1 FEL1 ltac:(cbn; lia)) as ELT1. cbn [app] in ELT1. clear EL1 FEL1 FEL.
  assert (FS1 : rw_cells asegs m1 (shad f) (map C1 (imp_sh (-8) (-8) (-8)))) by (byAG FS0 AG01; split; [right; right; left; lia| clear - Hx FSELF; lia]).
  assert (ST1' : stk asegs m1 lo S1) by exact ST1.
  assert (PRES1' : forall a : word, aclient L [(f, 5%nat)] S1 (bv_unsigned a) -> outside (imp_okarm_WA (mkPJA lo f 5%nat (f + 32) (f + 192) TAPE NT SBUF NS tws sbs len L)) (bv_unsigned a) -> m1 a = m a).
  { intros a Ha Ho. apply PRES1; [rewrite LVE, FRS; exact Ha|]. cbn [imp_okarm_WA pa_F outside] in Ho. lia. }

  apply (aevt_evt RT AF PMc MST).
  lazymatch type of ELT1 with rw_cells _ _ _ [_; _; CB 4 ?ja; CB 4 ?jb] =>
  eapply evt_cut; [eapply (ok_walk1 S1 usp f gp x0 x1 x2 e1 e2 e3 e4 e5 e6 e7 s4 s5 s7 s10 x3 x4 x5 x6 ja jb (-8) (-8) F1 fc m1);
                   [lia| ul| lia| ul| clear - FSELF; lia| exact ELT1| exact FS1| exact MI1]|] end.
  cbv beta. intros ms2 (m2 & -> & MU2 & WM2 & MI2 & EL2 & FS2). zstep. apply evt_done.
  assert (ART2 : ART RT Σ m2).
  { apply (art_client_write RT AF Σ m1 m2 S1 ART1 ltac:(ul)); [| exact WM2]. eapply (CLW Σ); [exact FRS| exact INCL0| exact MU2|].
    constructor; [intros x Hx; cbn [fst snd] in Hx; right; left; lia|]. constructor; [intros x Hx; cbn [fst snd] in Hx; right; right; left; lia|]. constructor. }
  assert (AG12 : forall P : Z -> Prop, (forall x, P x -> ~ (f + 264 <= x < f + 268) /\ ~ (shad f + 104 <= x < shad f + 137)) -> agree_on P m1 m2).
  { intros P HP a Ha. apply MU2. cbn [outside]. destruct (HP _ Ha) as [H1 H2]. split; [exact H1| split; [exact H2| exact I]]. }
  assert (ST2 : stk asegs m2 lo S1) by (apply (stk_agree asegs m1 m2 _ _ ST1); [| exact WM2]; apply AG12; intros x Hx; unfold STACK_WIN in SHT; clear - Hx FLO LOS1 SHT SPLO; split; lia).
  assert (FO2 : rw_cells asegs m2 (f + 832) [CB 264 jos]).
  { eapply rw_cells_agree_nw; [| apply AG12]; [byAG FO0 AG01; split; [right; left; lia| lia]|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. clear - Hx FSELF. lia. }
  pose proof (imp_sh_parts m2 (shad f) (-8) 0 (-8) FS2) as (_ & RUN68b & RUN33 & _).
  assert (SH2 : OSHADOWA m2 (f + 832)).
  { unfold OSHADOWA. replace (shad (f + 832)) with (shad f + 104) by (unfold shad; Z.div_mod_to_equations; lia). exact (run_bytes m2 _ _ _ RUN33). }
  assert (LB2 : LOCBA m2).
  { apply (LOCBA_agree m m2 LB0). eapply agree_trans; [apply AG01| apply AG12]; intros x Hx; unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx;
      [split; [right; right; right; left; unfold PJ_LOC_LO_A, PJ_LOC_HI_A; lia| clear - Hx FSEG; lia]| clear - Hx FSEG SHLO; lia]. }
  assert (PRES2 : forall a : word, aclient L [(f, 5%nat)] S1 (bv_unsigned a) -> outside (imp_okarm_WA (mkPJA lo f 5%nat (f + 32) (f + 192) TAPE NT SBUF NS tws sbs len L)) (bv_unsigned a) -> m2 a = m a).
  { intros a Ha Ho. rewrite <- (PRES1' a Ha Ho). apply MU2. cbn [imp_okarm_WA pa_F outside] in Ho |- *. clear - Ho. repeat split; try exact I; lia. }

  eapply (CTOR Σ K len lo (f + 832) S1 f 5%nat jos _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc m2
            FDO MST INF OIN SPLO LOW FO2 SH2 LB2 LEN ART2 MI2 ST2 ltac:(ul) ltac:(ul) ltac:(clear - S32; Z.div_mod_to_equations; lia)).
  intros u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F3 m3 ART3 MI3 ST3 OSSI3 SH3 LB3 PRES3.
  rewrite (ret_pc_even 0xb50c0) by lia.

  assert (AG23 : forall P : Z -> Prop, (forall x, P x -> okclI S1 f L x /\ ~ (f + 832 <= x < f + 832 + 264)) -> agree_on P m2 m3).
  { intros P HP a Ha. destruct (HP _ Ha) as [H1 H2]. apply PRES3; [exact (CLA Σ _ FRS INCL0 H1)| cbn [outside]; split; [exact H2| exact I]]. }
  assert (EL3 : rw_cells asegs m3 (f + 248) [C8 (wz (f + 192)); C8 (wz 1); C4 (wz 0); CB 4 jk1])
    by (eapply rw_cells_agree_nw; [exact EL2|]; apply AG23; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [right; left; lia| lia]).
  assert (LOC3 : rw_cells asegs m3 (S1 + 80) (imp_locals f (shad f) szw dw)).
  { eapply rw_cells_agree_nw; [| eapply agree_trans; [apply AG12| apply AG23]]; [byAG LOC AG01; split; [left; ul| ul]| |];
      intros x Hx; rewrite imp_locals_size in Hx; [clear - Hx FLO LOS1 SHT SPLO; unfold STACK_WIN in *; split; lia| split; [left; ul| ul]]. }
  assert (FS3 : rw_cells asegs m3 (shad f) (map C1 (imp_sh (-8) 0 (-8)))).
  { eapply rw_cells_agree_nw; [exact FS2|]. apply AG23. intros x Hx. rewrite cells_size_map_C1o, imp_sh_length in Hx. split; [right; right; left; lia| clear - Hx FSELF; lia]. }
  assert (FB3 : rw_cells asegs m3 (f + 32) [CB 88 jsb]).
  { eapply rw_cells_agree_nw; [| eapply agree_trans; [apply AG12| apply AG23]]; [byAG FB0 AG01; split; [right; left; lia| lia]| |];
      intros x Hx; cbn [cells_size csize Nat.add] in Hx; [clear - Hx FSELF; split; lia| split; [right; left; lia| lia]]. }
  assert (FOUT3 : rw_cells asegs m3 (f + 272) [C8 (wz 0); C8 (wz 0); C8 (wz 0)]).
  { eapply rw_cells_agree_nw; [| eapply agree_trans; [apply AG12| apply AG23]]; [byAG FOUT AG01; split; [right; left; lia| lia]| |];
      intros x Hx; cbn [cells_size csize Nat.add] in Hx; [clear - Hx FSELF; split; lia| split; [right; left; lia| lia]]. }
  assert (FTMP3 : rw_cells asegs m3 (f + 1168) [CB 24 jtmp]).
  { eapply rw_cells_agree_nw; [| eapply agree_trans; [apply AG12| apply AG23]]; [byAG FTMP AG01; split; [right; left; lia| lia]| |];
      intros x Hx; cbn [cells_size csize Nat.add] in Hx; [clear - Hx FSELF; split; lia| split; [right; left; lia| lia]]. }
  assert (DRC : forall x, docrep_rng (mkPJA lo f 5%nat (f + 32) (f + 192) TAPE NT SBUF NS tws sbs len L) x ->
            (f + 192 <= x < f + 208) \/ (shad f + 24 <= x < shad f + 26) \/ in_live L x).
  { intros x Hx. unfold docrep_rng in Hx. cbn [pa_DOC pa_TAPE pa_SBUF pa_tws pa_sbs] in Hx.
    replace (shad (f + 192)) with (shad f + 24) in Hx by (unfold shad; Z.div_mod_to_equations; lia).
    destruct Hx as [H|[H|[H|H]]]; [left; lia| right; left; lia| right; right| right; right].
    - exists TAPE, NT. split; [exact INT| lia].
    - exists SBUF, NS. split; [exact INS| lia]. }
  assert (DR3 : DOCREPA (mkPJA lo f 5%nat (f + 32) (f + 192) TAPE NT SBUF NS tws sbs len L) m3).
  { apply (DOCREPA_agree _ m m3 DR0). eapply agree_trans; [apply AG01| eapply agree_trans; [apply AG12| apply AG23]]; intros x Hx;
      (destruct (DRC x Hx) as [H|[H|(p & k & Hin & Hr)]]; [| | pose proof (LRNG p k Hin) as LR]).
    - split; [right; left; lia| lia]. - split; [right; right; left; lia| clear - H FSELF; lia]. - split; [do 4 right; exists p, k; split; [exact Hin| lia]| clear - LR Hr; lia].
    - clear - H FSELF; split; lia. - clear - H FSELF; split; lia. - clear - LR Hr; split; lia.
    - split; [right; left; lia| lia]. - split; [right; right; left; lia| clear - H FSELF; lia]. - split; [do 4 right; exists p, k; split; [exact Hin| lia]| clear - LR Hr; lia]. }
  assert (LX3 : locx3 m3).
  { apply (locx3_agreeI m m3 LX0). eapply agree_trans; [apply AG01| eapply agree_trans; [apply AG12| apply AG23]]; intros x Hx; unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx;
      [split; [right; right; right; left; unfold PJ_LOC_LO_A, PJ_LOC_HI_A; lia| clear - Hx FSEG; lia]| clear - Hx FSEG SHLO; split; lia
      | split; [right; right; right; left; unfold PJ_LOC_LO_A, PJ_LOC_HI_A; lia| clear - Hx FSEG; lia]]. }
  assert (PRES3' : forall a : word, aclient L [(f, 5%nat)] S1 (bv_unsigned a) -> outside (imp_okarm_WA (mkPJA lo f 5%nat (f + 32) (f + 192) TAPE NT SBUF NS tws sbs len L)) (bv_unsigned a) -> m3 a = m a).
  { intros a Ha Ho. rewrite <- (PRES2 a Ha Ho). apply PRES3; [rewrite LVE, FRS; exact Ha|]. cbn [imp_okarm_WA pa_F outside] in Ho |- *. clear - Ho. lia. }
  clear AG01 AG12 PRES1 PRES1' PRES2 ART1 MI1 ST1 ST1' FS1 ELT1 BY1 WM1 EL2 FS2 MU2 WM2 MI2 ST2 ART2 FO2 RUN68b RUN33 SH2 LB2 SR SR16 BY0 CS0 CD0 COK0.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (ok_walk2 S1 usp f szw dw gp u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s4 s5 s7 s10 u3 u4 u5 u6 jk1 0 (-8) F3 fc m3);
                   [lia| ul| lia| ul| clear - FSELF; lia| ul| ul| ul| clear - SHT SPLO LOS1; unfold STACK_WIN in *; lia| exact EL3| exact LOC3| exact FS3| exact MI3]|].
  cbv beta. intros ms4 (m4 & -> & MU4 & WM4 & MI4 & FS4). apply evt_done.
  assert (ART4 : ART RT Σ m4).
  { apply (art_client_write RT AF Σ m3 m4 S1 ART3 ltac:(ul)); [| exact WM4]. eapply (CLW Σ); [exact FRS| exact INCL0| exact MU4|].
    constructor; [intros x Hx; cbn [fst snd] in Hx; right; right; left; lia|]. constructor. }
  assert (AG34 : forall P : Z -> Prop, (forall x, P x -> ~ (shad f + 4 <= x < shad f + 15)) -> agree_on P m3 m4).
  { intros P HP a Ha. apply MU4. cbn [outside]. split; [exact (HP _ Ha)| exact I]. }
  assert (ST4 : stk asegs m4 lo S1) by (apply (stk_agree asegs m3 m4 _ _ ST3); [| exact WM4]; apply AG34; intros x Hx; clear - Hx SHT SPLO; unfold STACK_WIN in *; lia).
  assert (FB4 : rw_cells asegs m4 (f + 32) [CB 88 jsb]) by (eapply rw_cells_agree_nw; [exact FB3|]; apply AG34; intros x Hx; cbn [cells_size csize Nat.add] in Hx; clear - Hx FSELF; lia).
  assert (PRES4' : forall a : word, aclient L [(f, 5%nat)] S1 (bv_unsigned a) -> outside (imp_okarm_WA (mkPJA lo f 5%nat (f + 32) (f + 192) TAPE NT SBUF NS tws sbs len L)) (bv_unsigned a) -> m4 a = m a).
  { intros a Ha Ho. rewrite <- (PRES3' a Ha Ho). apply MU4. cbn [imp_okarm_WA pa_F outside] in Ho |- *. clear - Ho. lia. }
  pose proof (imp_sh_parts m4 (shad f) 0 0 (-8) FS4) as (RUN11 & RUN68c & _ & _).

  assert (CD4 : checked_dst RT Σ m4 (wz S1) (f + 32) 64).
  { unfold checked_dst. rewrite EU. split; [| split].
    - intros _. split.
      + apply (acc_sub asegs m4 (f + 32) 88); [| lia| lia]. change 88 with (8 * Z.of_nat 11).
        apply (acc_zero_run asegs m4 (f + 32) 11); [Z.div_mod_to_equations; lia| lia|].
        replace (shad (f + 32)) with (shad f + 4) by (unfold shad; Z.div_mod_to_equations; lia). exact (run_bytes m4 _ _ _ RUN11).
      + right; left. exists f, 5%nat. change (fs_size 5) with 2048. split; [exact INF| lia].
    - intros i Hi. right; right; right; left. exists f, 5%nat. change (fs_size 5) with 2048. split; [exact INF| lia].
    - apply (rw_cells_wr_at asegs m4 (f + 32) [CB 88 jsb] 64 FB4). cbn. lia. }
  assert (COK4 : call_ok RT Σ m4 (wz S1) lo).
  { unfold call_ok. rewrite EU. split; [exact ST4|]. split; [exact SPLO|]. split; [ul|]. split; [ul| clear - S32; Z.div_mod_to_equations; lia]. }
  eapply (aevt_memsetP RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc m4 (f + 32) 64 z8 lo eq_refl eq_refl eq_refl
            ltac:(ul) ltac:(lia) CD4 ART4 MI4 COK4).
  intros v0 v1 v2 g1 g2 g3 g4 g5 g6 g7 v3 v4 v5 v6 F5 m5 (ART5 & MI5 & WM5 & ST5) PRES5 BY5. rewrite EU in ST5, PRES5.
  rewrite (ret_pc_even 0xb5108) by lia. change (Z.to_nat 64) with 64%nat in BY5.
  assert (AG45 : forall P : Z -> Prop, (forall x, P x -> okclI S1 f L x /\ ~ (f + 32 <= x < f + 32 + 64)) -> agree_on P m4 m5).
  { intros P HP a Ha. destruct (HP _ Ha) as (H1 & H2). apply PRES5; [exact (CLA Σ _ FRS INCL0 H1)| exact H2]. }
  assert (FS5 : rw_cells asegs m5 (shad f) (map C1 (imp_sh 0 0 (-8)))).
  { eapply rw_cells_agree_nw; [exact FS4|]. apply AG45. intros x Hx. rewrite cells_size_map_C1o, imp_sh_length in Hx. split; [right; right; left; lia| clear - Hx FSELF; lia]. }
  assert (LOC5 : rw_cells asegs m5 (S1 + 80) (imp_locals f (shad f) szw dw)).
  { eapply rw_cells_agree_nw; [exact LOC3|]. eapply agree_trans; [apply AG34| apply AG45]; intros x Hx; rewrite imp_locals_size in Hx;
      [clear - Hx SHT SPLO LOS1 FLO; unfold STACK_WIN in *; lia| split; [left; ul| ul]]. }
  assert (PRES5' : forall a : word, aclient L [(f, 5%nat)] S1 (bv_unsigned a) -> outside (imp_okarm_WA (mkPJA lo f 5%nat (f + 32) (f + 192) TAPE NT SBUF NS tws sbs len L)) (bv_unsigned a) -> m5 a = m a).
  { intros a Ha Ho. rewrite <- (PRES4' a Ha Ho). apply PRES5; [rewrite LVE, FRS; exact Ha|]. cbn [imp_okarm_WA pa_F outside] in Ho. clear - Ho. lia. }

  destruct (wr_at_rw_CB m5 (f + 32) 88 (wr_at_transport asegs m4 m5 _ _ (rw_cells_wr_at asegs m4 (f + 32) [CB 88 jsb] 88 FB4 ltac:(cbn; lia)) WM5) ltac:(lia)) as (jsb5 & FB5).
  change (Z.to_nat 88) with 88%nat in FB5.
  pose proof FB5 as SC5. apply (rw_cells_split_CB asegs _ _ [] 88 _ [] [64; 8; 8; 8]%nat) in SC5; [| reflexivity]. cbn [mk_CB_cells app] in SC5. forget_junk SC5.
  lazymatch type of SC5 with rw_cells _ _ _ (?c0 :: ?rest) => change (c0 :: rest) with ([c0] ++ rest) in SC5 end.
  apply Sj_stage1_kit.rw_cells_app in SC5. destruct SC5 as [ARR5 SC5]. cbn [cells_size csize Nat.add] in SC5.
  replace (f + 32 + Z.of_nat 64) with (f + 96) in SC5 by lia.
  clear AG23 PRES3 PRES3' PRES4' ART3 MI3 ST3 LOC3 FS3 FB3 ART4 MI4 ST4 FB4 FS4 MU4 WM4 CD4 COK4 RUN11 RUN68c.

  apply (aevt_evt RT AF PMc MST).
  lazymatch type of SC5 with rw_cells _ _ _ [CB 8 ?x0; CB 8 ?x1; CB 8 ?x2] =>
    eapply evt_cut; [eapply (ok_walk3 S1 usp f szw dw gp v0 v1 v2 g1 g2 g3 g4 g5 g6 g7 s7 s10 v3 v4 v5 v6 x0 x1 x2 0 (-8) F5 fc m5);
                     [lia| ul| lia| ul| clear - FSELF; lia| ul| ul| ul| clear - SHT SPLO LOS1; unfold STACK_WIN in *; lia| exact SC5| exact LOC5| exact FS5| exact MI5]|]
  end.
  cbv beta. intros ms6 (m6 & -> & MU6 & WM6 & MI6 & SC6). apply evt_done.
  assert (ART6 : ART RT Σ m6).
  { apply (art_client_write RT AF Σ m5 m6 S1 ART5 ltac:(ul)); [| exact WM6]. eapply (CLW Σ); [exact FRS| exact INCL0| exact MU6|].
    constructor; [intros x Hx; cbn [fst snd] in Hx; right; left; lia|]. constructor. }
  assert (AG56 : forall P : Z -> Prop, (forall x, P x -> ~ (f + 96 <= x < f + 120)) -> agree_on P m5 m6).
  { intros P HP a Ha. apply MU6. cbn [outside]. split; [exact (HP _ Ha)| exact I]. }
  assert (ST6 : stk asegs m6 lo S1) by (apply (stk_agree asegs m5 m6 _ _ ST5); [| exact WM6]; apply AG56; intros x Hx; lia).
  lazymatch type of ARR5 with rw_cells _ _ _ [CB 64 ?ji] =>
    assert (ARR6 : rw_cells asegs m6 (f + 32) [CB 64 ji]) by (eapply rw_cells_agree_nw; [exact ARR5|]; apply AG56; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia)
  end.
  pose proof (imp_sh_parts m5 (shad f) 0 0 (-8) FS5) as (RUN11 & _ & _ & _).
  assert (I6 : SBINVA (mkPJA lo f 5%nat (f + 32) (f + 192) TAPE NT SBUF NS tws sbs len L) m6 (sbA0 (f + 32))).
  { unfold SBINVA. cbn [pa_SB pa_len pa_lo sa_buf sa_size sa_cap sa_heap sa_k sbA0].
    replace (f + 32 + 64) with (f + 96) by lia. change (Z.to_nat 64) with 64%nat. change (64 * 2 ^ 0) with 64.
    split; [exact SC6|]. split; [lia|]. split; [eexists; exact ARR6|]. split; [eexists; exact ARR6|].
    split; [replace (shad (f + 32)) with (shad f + 4) by (unfold shad; Z.div_mod_to_equations; lia);
            apply (bytes_at_agree asegs m5 m6); [exact (run_bytes m5 _ _ _ RUN11)| apply AG56; intros x Hx; rewrite repeat_length in Hx; clear - Hx FSELF; lia]|].
    split; [lia|]. repeat split; reflexivity. }
  assert (FS6 : rw_cells asegs m6 (shad f) (map C1 (imp_sh 0 0 (-8)))).
  { eapply rw_cells_agree_nw; [exact FS5|]. apply AG56. intros x Hx. rewrite cells_size_map_C1o, imp_sh_length in Hx. clear - Hx FSELF; lia. }
  assert (DR6 : DOCREPA (mkPJA lo f 5%nat (f + 32) (f + 192) TAPE NT SBUF NS tws sbs len L) m6).
  { apply (DOCREPA_agree _ m3 m6 DR3). eapply agree_trans; [apply AG34| eapply agree_trans; [apply AG45| apply AG56]]; intros x Hx;
      (destruct (DRC x Hx) as [H|[H|(p & k & Hin & Hr)]]; [| | pose proof (LRNG p k Hin) as LR]); try (clear - H FSELF; lia); try (clear - LR Hr; lia).
    - split; [right; left; lia| lia]. - split; [right; right; left; lia| clear - H FSELF; lia]. - split; [do 4 right; exists p, k; split; [exact Hin| lia]| clear - LR Hr; lia]. }
  assert (LB6 : LOCBA m6).
  { apply (LOCBA_agree m3 m6 LB3). eapply agree_trans; [apply AG34| eapply agree_trans; [apply AG45| apply AG56]]; intros x Hx; unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx;
      [clear - Hx FSEG SHLO; lia| split; [right; right; right; left; unfold PJ_LOC_LO_A, PJ_LOC_HI_A; lia| clear - Hx FSEG; lia]| clear - Hx FSEG; lia]. }
  assert (LX6 : locx3 m6).
  { apply (locx3_agreeI m3 m6 LX3). eapply agree_trans; [apply AG34| eapply agree_trans; [apply AG45| apply AG56]]; intros x Hx; unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx;
      [clear - Hx FSEG SHLO; lia| split; [right; right; right; left; unfold PJ_LOC_LO_A, PJ_LOC_HI_A; lia| clear - Hx FSEG; lia]| clear - Hx FSEG; lia]. }
  assert (OSSI6 : OSSINVA m6 (f + 832) len (ossA0 (f + 832)) 0xFFFFFFFF).
  { destruct OSSI3 as [SBI3 IOS3]. split.
    - apply (SBINVA'_agree m3 m6 _ _ _ SBI3). eapply agree_trans; [apply AG34| eapply agree_trans; [apply AG45| apply AG56]]; intros x Hx; unfold sbinv_rngI in Hx; cbn [oa_heap oa_data oa_cap ossA0] in Hx;
        [clear - Hx FSELF; lia| split; [right; left; lia| lia]| lia].
    - apply (IOSINVA_agree m3 m6 _ _ IOS3). eapply agree_trans; [apply AG34| eapply agree_trans; [apply AG45| apply AG56]]; intros x Hx;
        [clear - Hx FSELF; lia| split; [right; left; lia| lia]| lia]. }
  assert (SH6 : OSHADOWA m6 (f + 832)).
  { apply (OSHADOWA_agree m3 m6 _ SH3). replace (shad (f + 832)) with (shad f + 104) by (unfold shad; Z.div_mod_to_equations; lia).
    eapply agree_trans; [apply AG34| eapply agree_trans; [apply AG45| apply AG56]]; intros x Hx; [lia| split; [right; right; left; lia| clear - Hx FSELF; lia]| clear - Hx FSELF; lia]. }
  assert (EL6 : rw_cells asegs m6 (f + 248) [C8 (wz (f + 192)); C8 (wz 1); C4 (wz 0); CB 4 jk1]).
  { eapply rw_cells_agree_nw; [exact EL3|]. eapply agree_trans; [apply AG34| eapply agree_trans; [apply AG45| apply AG56]]; intros x Hx; cbn [cells_size csize Nat.add] in Hx;
      [clear - Hx FSELF; lia| split; [right; left; lia| lia]| lia]. }
  assert (FOUT6 : rw_cells asegs m6 (f + 272) [C8 (wz 0); C8 (wz 0); C8 (wz 0)]).
  { eapply rw_cells_agree_nw; [exact FOUT3|]. eapply agree_trans; [apply AG34| eapply agree_trans; [apply AG45| apply AG56]]; intros x Hx; cbn [cells_size csize Nat.add] in Hx;
      [clear - Hx FSELF; lia| split; [right; left; lia| lia]| lia]. }
  assert (FTMP6 : rw_cells asegs m6 (f + 1168) [CB 24 jtmp]).
  { eapply rw_cells_agree_nw; [exact FTMP3|]. eapply agree_trans; [apply AG34| eapply agree_trans; [apply AG45| apply AG56]]; intros x Hx; cbn [cells_size csize Nat.add] in Hx;
      [clear - Hx FSELF; lia| split; [right; left; lia| lia]| lia]. }
  assert (LOC6 : rw_cells asegs m6 (S1 + 80) (imp_locals f (shad f) szw dw)).
  { eapply rw_cells_agree_nw; [exact LOC5|]. apply AG56. intros x Hx. rewrite imp_locals_size in Hx. clear - Hx FLO LOS1. lia. }
  assert (PRES6' : forall a : word, aclient L [(f, 5%nat)] S1 (bv_unsigned a) -> outside (imp_okarm_WA (mkPJA lo f 5%nat (f + 32) (f + 192) TAPE NT SBUF NS tws sbs len L)) (bv_unsigned a) -> m6 a = m a).
  { intros a Ha Ho. rewrite <- (PRES5' a Ha Ho). apply MU6. cbn [imp_okarm_WA pa_F outside] in Ho |- *. clear - Ho. lia. }
  assert (CR6 : 2 * (Z.of_nat (length tws) - 1 - 1) + pj_psi len (sbA0 (f + 32)) <= rt_credit RT Σ) by (unfold imp_okarm_costA, IMP_PUT_COST_A in CR0; lia).
  assert (FC3 : fcount 3 (rt_frames RT Σ) + Z.of_nat TAPE_MAX_DEPTH + 1 <= FRAMES_MAX3).
  { rewrite FRS, fcount_cons, fcount_nil. unfold TAPE_MAX_DEPTH, FRAMES_MAX3. change (Z.of_nat 1024) with 1024. cbn. lia. }
  assert (FT : Z.of_nat (length (rt_frames RT Σ)) + 2 * Z.of_nat TAPE_MAX_DEPTH + 2 <= FRAMES_TOT).
  { rewrite FRS. unfold TAPE_MAX_DEPTH, FRAMES_TOT. change (Z.of_nat 1024) with 1024. change (Z.of_nat (length [(f, 5%nat)])) with 1. lia. }
  clear AG34 AG45 AG56 PRES5 PRES5' ART5 MI5 ST5 WM5 BY5 FB5 ARR5 SC5 FS5 LOC5 MU6 WM6 RUN11 OSSI3 SH3 LB3 LX3 DR3 EL3 FOUT3 FTMP3.

  eapply (SER Σ K (mkPJA lo f 5%nat (f + 32) (f + 192) TAPE NT SBUF NS tws sbs len L) (sbA0 (f + 32)) 1 (Z.of_nat (length tws) - 1) 0 (Z.of_nat (length sbs)) S1
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F5 fc m6 FDO MST OK LV I6 DR6 ELS ltac:(lia) ltac:(cbn [pa_tws]; lia) ltac:(lia) ltac:(cbn [pa_sbs]; lia)
            ltac:(unfold sb_acc1A; cbn [sa_size sbA0]; lia) ART6 MI6 ST6 ltac:(cbn [pa_lo]; unfold TAPE_MAX_DEPTH; ul) ltac:(ul) ltac:(clear - S32; Z.div_mod_to_equations; lia) FRM FC3 FT ltac:(cbn [pa_L]; unfold IMP_OKARM_LIVE_A in LVB; lia) CR6).
  intros Σ7 st' y0 y1 y2 d0 d1 d2 d3 d4 d5 d6 d7 y3 y4 y5 y6 F7 fc7 m7 FRM7 ART7 MI7 ST7 I7 DR7 SACC7 LV7 FRS7 SP7 CR7 PRES7.
  cbn [pa_lo pa_F pa_kF pa_SB pa_DOC pa_TAPE pa_NT pa_SBUF pa_NS pa_tws pa_sbs pa_len pa_L] in ST7, LV7, CR7, PRES7, SACC7.
  rewrite (ret_pc_even 0xb5134) by lia.
  pose proof LV7 as (LVE7 & INF7 & _). rewrite FRS in FRS7.
  assert (INCL7 : forall e, In e L -> In e (rt_live RT Σ7)) by (intros e He; rewrite LVE7; apply in_or_app; right; exact He).
  pose proof (pj_psi_nonneg _ m7 st' OK I7) as PSI7. cbn [pa_len] in PSI7.
  pose proof I7 as (SC7 & SZC7 & (bs7 & BUF7) & (ji7 & ARR7) & SHB7 & (K7 & KC7 & KM7) & HB7). cbn [pa_SB pa_len pa_lo] in SC7, BUF7, ARR7, SHB7, KM7, HB7.
  replace (f + 32 + 64) with (f + 96) in SC7 by lia.
  pose proof (SBINVA_cap_pos _ m7 st' I7) as CAP64.
  assert (BUFR : 0 < sa_buf st' /\ sa_buf st' + sa_cap st' <= lo /\ (sa_heap st' = true -> f + 2048 <= sa_buf st' \/ sa_buf st' + sa_cap st' <= f) /\ (sa_heap st' = false -> sa_buf st' = f + 32)).
  { destruct (sa_heap st') eqn:HP.
    - destruct HB7 as (B1 & B2 & B3). pose proof (proj2 (proj2 (proj2 (af_frames_range RT AF Σ7 m7 f 5%nat ART7 INF7))) (sa_buf st') (sa_cap st')
                                                       ltac:(rewrite LVE7; unfold sbchunkA; rewrite HP; left; reflexivity)) as Y. change (fs_size 5) with 2048 in Y.
      split; [lia|]. split; [lia|]. split; [intros _; lia| intros; congruence].
    - destruct HB7 as (B1 & B2 & _). split; [lia|]. split; [lia|]. split; [intros; congruence| intros _; exact B1]. }
  destruct BUFR as (BUFP & BUFLO & BHEAP & BINL).
  assert (OUTB : sa_size st' <= PJ_OUTMAX len).
  { pose proof (sb_accA_out _ st' (Z.of_nat (length tws) - 1) (Z.of_nat (length sbs)) OK ltac:(cbn [pa_tws]; lia) ltac:(cbn [pa_sbs]; lia) SACC7) as X. cbn [pa_len] in X. exact X. }
  assert (LPOS7 : forall p n, In (p, n) (sbchunkA st' ++ L) -> 0 < n).
  { intros p n Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [| exact (LPOS p n Hin)].
    unfold sbchunkA in Hin. destruct (sa_heap st'); [| destruct Hin]. destruct Hin as [E|[]]. injection E as <- <-. lia. }
  assert (AG67 : forall P : Z -> Prop, (forall x, P x -> okclI S1 f L x /\ ~ (f + 32 <= x < f + 32 + 88)) -> agree_on P m6 m7).
  { intros P HP a Ha. destruct (HP _ Ha) as (H1 & H2). apply PRES7; [| cbn [outside]; split; [exact H2| exact I]].
    rewrite FRS. pose proof (CLA Σ _ FRS INCL0 H1) as C. rewrite LVE, FRS in C. exact C. }
  assert (FS7 : rw_cells asegs m7 (shad f) (map C1 (imp_sh 0 0 (-8)))).
  { eapply rw_cells_agree_nw; [exact FS6|]. apply AG67. intros x Hx. rewrite cells_size_map_C1o, imp_sh_length in Hx. split; [right; right; left; lia| clear - Hx FSELF; lia]. }
  assert (LOC7 : rw_cells asegs m7 (S1 + 80) (imp_locals f (shad f) szw dw)).
  { eapply rw_cells_agree_nw; [exact LOC6|]. apply AG67. intros x Hx. rewrite imp_locals_size in Hx. split; [left; ul| clear - Hx FLO LOS1; lia]. }
  assert (LB7 : LOCBA m7).
  { apply (LOCBA_agree m6 m7 LB6). apply AG67. intros x Hx. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx. split; [right; right; right; left; unfold PJ_LOC_LO_A, PJ_LOC_HI_A; lia| clear - Hx FSEG; lia]. }
  assert (LX7 : locx3 m7).
  { apply (locx3_agreeI m6 m7 LX6). apply AG67. intros x Hx. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx. split; [right; right; right; left; unfold PJ_LOC_LO_A, PJ_LOC_HI_A; lia| clear - Hx FSEG; lia]. }
  assert (OSSI7 : OSSINVA m7 (f + 832) len (ossA0 (f + 832)) 0xFFFFFFFF).
  { destruct OSSI6 as [SBI6 IOS6]. split.
    - apply (SBINVA'_agree m6 m7 _ _ _ SBI6). apply AG67. intros x Hx. unfold sbinv_rngI in Hx. cbn [oa_heap oa_data oa_cap ossA0] in Hx. split; [right; left; lia| lia].
    - apply (IOSINVA_agree m6 m7 _ _ IOS6). apply AG67. intros x Hx. split; [right; left; lia| lia]. }
  assert (SH7 : OSHADOWA m7 (f + 832)).
  { apply (OSHADOWA_agree m6 m7 _ SH6). replace (shad (f + 832)) with (shad f + 104) by (unfold shad; Z.div_mod_to_equations; lia).
    apply AG67. intros x Hx. split; [right; right; left; lia| clear - Hx FSELF; lia]. }
  assert (EL7 : rw_cells asegs m7 (f + 248) [C8 (wz (f + 192)); C8 (wz 1); C4 (wz 0); CB 4 jk1]).
  { eapply rw_cells_agree_nw; [exact EL6|]. apply AG67. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [right; left; lia| lia]. }
  assert (FOUT7 : rw_cells asegs m7 (f + 272) [C8 (wz 0); C8 (wz 0); C8 (wz 0)]).
  { eapply rw_cells_agree_nw; [exact FOUT6|]. apply AG67. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [right; left; lia| lia]. }
  assert (FTMP7 : rw_cells asegs m7 (f + 1168) [CB 24 jtmp]).
  { eapply rw_cells_agree_nw; [exact FTMP6|]. apply AG67. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [right; left; lia| lia]. }
  assert (PRES7' : forall a : word, aclient L [(f, 5%nat)] S1 (bv_unsigned a) -> outside (imp_okarm_WA (mkPJA lo f 5%nat (f + 32) (f + 192) TAPE NT SBUF NS tws sbs len L)) (bv_unsigned a) -> m7 a = m a).
  { intros a Ha Ho. rewrite <- (PRES6' a Ha Ho). apply PRES7; [rewrite FRS; exact Ha|]. cbn [imp_okarm_WA pa_F outside] in Ho |- *. clear - Ho. repeat split; try exact I; lia. }
  assert (ACC7 : acc asegs m7 (sa_buf st') (sa_size st')).
  { apply (acc_sub asegs m7 (sa_buf st') (sa_cap st')); [| lia| lia]. exact (SBINVA_acc RT AF Σ7 _ m7 st' OK LV7 ART7 I7). }
  assert (BCLS : (exists p k, In (p, k) (sbchunkA st' ++ L) /\ p <= sa_buf st' /\ sa_buf st' + sa_cap st' <= p + k) \/ (f <= sa_buf st' /\ sa_buf st' + sa_cap st' <= f + fs_size 5 - 8)).
  { destruct (sa_heap st') eqn:HP.
    - left. exists (sa_buf st'), (sa_cap st'). split; [unfold sbchunkA; rewrite HP; left; reflexivity| lia].
    - right. rewrite (BINL eq_refl). destruct HB7 as (_ & -> & _). change (fs_size 5) with 2048. lia. }
  assert (BSEP : sa_buf st' + sa_cap st' <= f + 832 \/ f + 832 + 264 <= sa_buf st').
  { destruct (sa_heap st') eqn:HP; [destruct (BHEAP eq_refl); lia|]. rewrite (BINL eq_refl). destruct HB7 as (_ & -> & _). lia. }
  assert (BR : 0 <= sa_buf st' < 2^64 /\ 0 <= sa_size st' < 2^64 /\ 0 <= sa_cap st' < 2^64) by ul.
  assert (CRED7 : 2 + os_psi len (ossA0 (f + 832)) <= rt_credit RT Σ7) by (unfold imp_okarm_costA, IMP_PUT_COST_A in CR0; clear - CR0 CR7 PSI7 PSI0 OPSI0; lia).
  clear AG67 PRES6' PRES7 ART6 MI6 ST6 FS6 LOC6 LB6 LX6 OSSI6 SH6 EL6 FOUT6 FTMP6 SC6 ARR6 I6 DR6 CR6.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (ok_walk4 S1 usp f (sa_buf st') (sa_size st') (sa_cap st') gp y0 y1 y2 d0 d1 d2 d3 d4 d5 d6 d7 s7 s10 y3 y4 y5 y6 F7 fc7 m7);
                   [lia| ul| lia| lia| lia| exact SC7| exact MI7]|].
  cbv beta. intros ms8 <-. apply evt_done.

  eapply (PUT Σ7 K (sbchunkA st' ++ L) (ossA0 (f + 832)) len lo (f + 832) S1 (sa_buf st') (sa_size st') (sa_cap st') f 5%nat bs7
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F7 fc7 m7 FDO MST
            ltac:(cbn [oachunk oa_heap ossA0]; exact LVE7) LPOS7 ltac:(rewrite FRS7; left; reflexivity) OIN ltac:(rewrite SP7; exact SPLO) LOW
            OSSI7 SH7 LB7 LEN BUF7 SZC7 BUFP BUFLO ACC7 BCLS BSEP ltac:(cbn [oa_w ossA0]; lia)
            ART7 MI7 ST7 ltac:(ul) ltac:(ul) ltac:(clear - S32; Z.div_mod_to_equations; lia)
            ltac:(rewrite FRS7; cbn; unfold FRAMES_MAX2; lia) ltac:(rewrite FRS7; discriminate)
            ltac:(rewrite length_app; unfold sbchunkA; unfold IMP_OKARM_LIVE_A in LVB; destruct (sa_heap st'); cbn [length]; lia) CRED7).
  intros Σ8 st8 w0 w1 w2 c1 c2 c3 c4 c5 c6 c7 w3 w4 w5 w6 F8 m8 ART8 MI8 ST8 OSSI8 W8EQ SH8 LB8 LV8 FRS8 SP8 CR8 PRES8.
  rewrite (ret_pc_even 0xb5144) by lia. rewrite FRS7 in FRS8, PRES8. cbn [oa_w ossA0] in W8EQ. rewrite Z.add_0_l in W8EQ.
  assert (AG78 : forall P : Z -> Prop, (forall x, P x -> okclI S1 f L x /\ ~ (f + 832 <= x < f + 832 + 264)) -> agree_on P m7 m8).
  { intros P HP a Ha. destruct (HP _ Ha) as (H1 & H2). apply PRES8; [| cbn [outside]; split; [exact H2| exact I]].
    pose proof (CLA Σ7 _ FRS7 INCL7 H1) as C. rewrite LVE7, FRS7 in C. exact C. }
  assert (SC8 : rw_cells asegs m8 (f + 96) [C8 (wz (sa_buf st')); C8 (wz (sa_size st')); C8 (wz (sa_cap st'))]).
  { eapply rw_cells_agree_nw; [exact SC7|]. apply AG78. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [right; left; lia| lia]. }
  assert (FB8 : exists bb, rw_cells asegs m8 (f + 32) [CB 88 bb]).
  { assert (ARR8 : rw_cells asegs m8 (f + 32) [CB 64 ji7]) by (eapply rw_cells_agree_nw; [exact ARR7|]; apply AG78; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [right; left; lia| lia]).
    assert (FB8' : rw_cells asegs m8 (f + 32) ([CB 64 ji7] ++ [C8 (wz (sa_buf st')); C8 (wz (sa_size st')); C8 (wz (sa_cap st'))])).
    { apply Sj_stage1_kit.rw_cells_app. split; [exact ARR8|]. cbn [cells_size csize Nat.add]. replace (f + 32 + Z.of_nat 64) with (f + 96) by lia. exact SC8. }
    exact (rw_cells_forget asegs m8 (f + 32) _ FB8'). }
  destruct FB8 as (bb8 & FB8).
  assert (FS8 : rw_cells asegs m8 (shad f) (map C1 (imp_sh 0 0 (-8)))).
  { eapply rw_cells_agree_nw; [exact FS7|]. apply AG78. intros x Hx. rewrite cells_size_map_C1o, imp_sh_length in Hx. split; [right; right; left; lia| clear - Hx FSELF; lia]. }
  assert (LOC8 : rw_cells asegs m8 (S1 + 80) (imp_locals f (shad f) szw dw)).
  { eapply rw_cells_agree_nw; [exact LOC7|]. apply AG78. intros x Hx. rewrite imp_locals_size in Hx. split; [left; ul| clear - Hx FLO LOS1; lia]. }
  assert (LX8 : locx3 m8).
  { apply (locx3_agreeI m7 m8 LX7). apply AG78. intros x Hx. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx. split; [right; right; right; left; unfold PJ_LOC_LO_A, PJ_LOC_HI_A; lia| clear - Hx FSEG; lia]. }
  assert (EL8 : rw_cells asegs m8 (f + 248) [C8 (wz (f + 192)); C8 (wz 1); C4 (wz 0); CB 4 jk1]).
  { eapply rw_cells_agree_nw; [exact EL7|]. apply AG78. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [right; left; lia| lia]. }
  assert (FOUT8 : rw_cells asegs m8 (f + 272) [C8 (wz 0); C8 (wz 0); C8 (wz 0)]).
  { eapply rw_cells_agree_nw; [exact FOUT7|]. apply AG78. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [right; left; lia| lia]. }
  assert (FTMP8 : rw_cells asegs m8 (f + 1168) [CB 24 jtmp]).
  { eapply rw_cells_agree_nw; [exact FTMP7|]. apply AG78. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [right; left; lia| lia]. }
  assert (PRES8' : forall a : word, aclient L [(f, 5%nat)] S1 (bv_unsigned a) -> outside (imp_okarm_WA (mkPJA lo f 5%nat (f + 32) (f + 192) TAPE NT SBUF NS tws sbs len L)) (bv_unsigned a) -> m8 a = m a).
  { intros a Ha Ho. rewrite <- (PRES7' a Ha Ho). apply PRES8; [| cbn [imp_okarm_WA pa_F outside] in Ho |- *; clear - Ho; repeat split; try exact I; lia].
    apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; apply in_or_app; right; exact He| intros e He; exact He| lia]. }

  pose proof OSSI8 as [(_ & _ & NUM8) _]. pose proof (OSNUMA_cap24 len st8 NUM8) as CAP24. pose proof (OSNUMA_k len st8 LEN NUM8) as K23.
  pose proof NUM8 as (WB8 & _ & CAPB8 & _).
  assert (LPOS8 : forall p n, In (p, n) (oachunk st8 ++ sbchunkA st' ++ L) -> 0 < n).
  { intros p n Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [| exact (LPOS7 p n Hin)].
    unfold oachunk in Hin. destruct (oa_heap st8); [| destruct Hin]. destruct Hin as [E|[]]. injection E as <- <-. lia. }
  assert (CRED8 : rt_credit RT Σ - imp_okarm_costA (Z.of_nat (length tws)) + str_costA (oa_w st8) <= rt_credit RT Σ8).
  { assert (SC : str_costA (oa_w st8) <= 2 * oa_cap st8 + 14 + PJ_GROWC).
    { unfold str_costA. destruct (Z.leb_spec (oa_w st8) 22) as [Hle|Hgt]; [pose proof PJ_GROWC_val; lia|].
      pose proof (imp_S_range (oa_w st8) ltac:(lia)) as (R1 & _ & _). pose proof (mcost_le_growc (imp_S (oa_w st8)) ltac:(lia)) as MC.
      unfold oa_lim in WB8. destruct (oa_heap st8); lia. }
    assert (KP : 0 <= oa_k st8 * PJ_GROWC <= 22 * PJ_GROWC) by (rewrite PJ_GROWC_val; clear - K23; nia).
    unfold os_psi, ossA0, IMP_SCAP0 in CR8. cbn [oa_cap oa_k] in CR8.
    unfold imp_okarm_costA, IMP_PUT_COST_A in *. rewrite PJ_GROWC_val in *. clear - CR0 CR7 CR8 PSI7 PSI0 SC KP CAPB8 CAPB CAP24. nia. }
  clear AG78 PRES7' PRES8 ART7 MI7 ST7 FS7 LOC7 LB7 LX7 OSSI7 SH7 EL7 FOUT7 FTMP7 SC7 ARR7 ACC7 BCLS BSEP CRED7 CR7 CR8 PSI7.

  assert (TAIL8 : forall (Σz : rts RT) (mz : mem) (ocp : option (Z * Z)) (ra' q0 q1 q2 p0 p1 p2 p3 p4 p5 p6 p7 q3 q4 q5 q6 sbv : word) (Fz : bvmap 5 word)
                         (bb j0 jmid j124 j260 jt : list byte),
    rt_live RT Σz = ocp_chunks ocp ++ L -> rt_frames RT Σz = [(f, 5%nat)] -> rt_sp0 RT Σz = rt_sp0 RT Σ ->
    rt_credit RT Σ - imp_okarm_costA (Z.of_nat (length tws)) <= rt_credit RT Σz ->
    (forall p k, In (p, k) (ocp_chunks ocp) -> 0 < k) ->
    ART RT Σz mz -> mem_inv asegs mz -> stk asegs mz lo S1 ->
    rw_cells asegs mz (f + 832) [CB 8 j0; C8 sbv; C8 (wz PJ_LOC_IMP_A); CB 88 jmid] ->
    rw_cells asegs mz (f + 944) (ios_cellsI (f + 832) 0x20 j124 j260) ->
    OSHADOWA mz (f + 832) -> LOCBA mz -> locx3 mz ->
    rw_cells asegs mz (shad f) (map C1 (imp_sh (-8) 0 (-8))) ->
    rw_cells asegs mz (S1 + 80) (imp_locals f (shad f) szw dw) ->
    imp_outA mz f ocp ->
    rw_cells asegs mz (f + 1168) [CB 24 jt] ->
    rw_cells asegs mz (f + 248) [C8 (wz (f + 192)); C8 (wz 1); C4 (wz 0); CB 4 jk1] ->
    rw_cells asegs mz (f + 32) [CB 88 bb] ->
    (forall a : word, aclient L [(f, 5%nat)] S1 (bv_unsigned a) -> outside (imp_okarm_WA (mkPJA lo f 5%nat (f + 32) (f + 192) TAPE NT SBUF NS tws sbs len L)) (bv_unsigned a) -> mz a = m a) ->
    aevt RT PMc Σz K (MS (mkR ra' (wz S1) gp (wz TPV_A) q0 q1 q2 (wz usp) (wz S1) p0 p1 p2 p3 p4 p5 p6 p7 (wz (-8)) (wz (shad f)) (wz OSS_VTT_A) (wz szw) (wz (f + 160)) s7 (wz SHB) (wz (f + 832)) s10 (wz dw) q3 q4 q5 q6)
                         Fz (wz 0xb5270) fc7 None mz (seg_rom asegs))).
  { intros Σz mz ocp ra' q0 q1 q2 p0 p1 p2 p3 p4 p5 p6 p7 q3 q4 q5 q6 sbv Fz bb j0 jmid j124 j260 jt LVz FRSz SPz CRz OCPP ARTz MIz STz FOz IOSz SHz LBz LXz FSz LOCz OUTz FTMPz ELz FBz PRESz.
    assert (INCLz : forall e, In e L -> In e (rt_live RT Σz)) by (intros e He; rewrite LVz; apply in_or_app; right; exact He).
    assert (INFz : In (f, 5%nat) (rt_frames RT Σz)) by (rewrite FRSz; left; reflexivity).
    assert (SPLOz : rt_sp0 RT Σz - STACK_WIN <= lo) by (unfold STACK_WIN; rewrite SPz; exact SPLO).
    assert (CLAz : forall x, okclI S1 f L x -> aclient (rt_live RT Σz) (rt_frames RT Σz) S1 x) by (intros x Hx; exact (CLA Σz _ FRSz INCLz Hx)).
    pose proof (ROWS Σz mz ARTz) as (V1 & _).
    pose proof FOz as FOq. takeZ FOq 1%nat (f + 840) FOa. takeZ FOq 1%nat (f + 848) VSBz. takeZ FOq 1%nat (f + 856) IMPz. rename FOq into JMz.

    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut; [eapply (ok_walk9 S1 usp f szw dw ra' gp q0 q1 q2 p0 p1 p2 p3 p4 p5 p6 p7 (wz OSS_VTT_A) (wz szw) s7 s10 q3 q4 q5 q6 sbv Fz fc7 mz);
                     [lia| ul| ul| ul| ul| exact VSBz| exact LOCz| exact V1| exact MIz]|].
    cbv beta. intros ms15 (m15 & -> & MU15 & WM15 & MI15 & VSB15).
    assert (ART15 : ART RT Σz m15).
    { apply (art_client_write RT AF Σz mz m15 S1 ARTz ltac:(unfold STACK_WIN in *; clear - SPLOz LOS1; lia)); [| exact WM15]. intros a Ha. apply MU15. cbn [outside].
      split; [intros Hin; apply Ha; apply CLAz; right; left; lia| exact I]. }
    assert (AGz15 : forall P : Z -> Prop, (forall x, P x -> ~ (f + 840 <= x < f + 848)) -> agree_on P mz m15).
    { intros P HP a Ha. apply MU15. cbn [outside]. split; [exact (HP _ Ha)| exact I]. }
    Local Ltac by15 H AG := eapply rw_cells_agree_nw; [exact H|]; apply AG; intros x Hx; cbn [cells_size csize Nat.add] in Hx; rewrite ?cells_size_map_C1o, ?imp_sh_length, ?imp_locals_size, ?ios_cellsI_size in Hx.
    assert (ST15 : stk asegs m15 lo S1) by (apply (stk_agree asegs mz m15 _ _ STz); [| exact WM15]; apply AGz15; intros x Hx; clear - Hx FLO LOS1; lia).
    assert (IMP15 : rw_cells asegs m15 (f + 848) [C8 (wz PJ_LOC_IMP_A)]) by (by15 IMPz AGz15; lia).
    assert (LB15 : LOCBA m15) by (apply (LOCBA_agree mz m15 LBz); apply AGz15; intros x Hx; unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx; clear - Hx FSEG; lia).
    assert (LX15 : locx3 m15) by (apply (locx3_agreeI mz m15 LXz); apply AGz15; intros x Hx; unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx; clear - Hx FSEG; lia).
    assert (LOC15 : rw_cells asegs m15 (S1 + 80) (imp_locals f (shad f) szw dw)) by (by15 LOCz AGz15; clear - Hx FLO LOS1; lia).
    assert (IOS15 : rw_cells asegs m15 (f + 832 + 112) (ios_cellsI (f + 832) 0x20 j124 j260)) by (replace (f + 832 + 112) with (f + 944) by lia; by15 IOSz AGz15; lia).
    assert (SH15 : OSHADOWA m15 (f + 832)).
    { apply (OSHADOWA_agree mz m15 _ SHz). replace (shad (f + 832)) with (shad f + 104) by (unfold shad; Z.div_mod_to_equations; lia). apply AGz15. intros x Hx. clear - Hx FSELF. lia. }

    eapply evt_cut; [eapply LOCD; [exact IMP15| exact LB15| exact MI15]|].
    cbv beta. intros ms16 (o0 & o1 & o2 & i0 & i1 & i2 & i3 & i4 & i5 & i6 & i7 & o3 & o4 & o5 & o6 & ->). rewrite (ret_pc_even 0xb5288) by lia.

    eapply evt_cut; [eapply (ok_walk10 S1 usp f szw dw gp o0 o1 o2 i0 i1 i2 i3 i4 i5 i6 i7 (wz OSS_VTT_A) (wz szw) s7 s10 o3 o4 o5 o6 Fz fc7 m15); [lia| ul| ul| ul| exact LOC15| exact MI15]|].
    cbv beta. intros ms17 <-. apply evt_done.

    replace (Z_to_bv 64 (f + 944)) with (Z_to_bv 64 (f + 832 + 112)) by (f_equal; lia). change IMP_IOS_DTOR_A with OSS_IOS_DTOR_A.
    eapply (IOSD Σz K lo (f + 832) S1 f 0x20 5%nat j124 j260 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fz fc7 m15 FDO MST INFz OIN SPLOz LOW IOS15 SH15 LB15);
      [unfold unwind_ok; rewrite EU, unsigned_lit by ul; right; right; lia| exact ART15| exact MI15| exact ST15| ul| ul| clear - S32; Z.div_mod_to_equations; lia|].
    intros o0' o1' o2' g0' g1' g2' g3' g4' g5' g6' g7' o3' o4' o5' o6' F16 m16 ART16 MI16 ST16 SH16 (j152 & IOSJ16) PRES16.
    rewrite (ret_pc_even 0xb529c) by lia.
    assert (AG1516 : forall P : Z -> Prop, (forall x, P x -> okclI S1 f L x /\ ~ (f + 944 <= x < f + 952)) -> agree_on P m15 m16).
    { intros P HP a Ha. destruct (HP _ Ha) as [H1 H2]. apply PRES16; [exact (CLAz _ H1)| cbn [outside]; split; [clear - H2; lia| exact I]]. }
    assert (FS16 : rw_cells asegs m16 (shad f) (map C1 (imp_sh (-8) 0 (-8)))).
    { eapply rw_cells_agree_nw; [exact FSz|]. eapply agree_trans; [apply AGz15| apply AG1516]; intros x Hx; rewrite cells_size_map_C1o, imp_sh_length in Hx; [clear - Hx FSELF; lia| split; [right; right; left; lia| clear - Hx FSELF; lia]]. }

    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut; [eapply (ok_walk11 S1 usp f dw gp o0' o1' o2' g0' g1' g2' g3' g4' g5' g6' g7' (wz OSS_VTT_A) (wz szw) s7 s10 o3' o4' o5' o6' (-8) (-8) F16 fc7 m16);
                     [lia| ul| lia| ul| exact FS16| exact MI16]|].
    cbv beta. intros ms18 (m17 & -> & MU17 & WM17 & MI17 & FS17). apply evt_done.
    assert (ART17 : ART RT Σz m17).
    { apply (art_client_write RT AF Σz m16 m17 S1 ART16 ltac:(unfold STACK_WIN in *; clear - SPLOz LOS1; lia)); [| exact WM17]. intros a Ha. apply MU17. cbn [outside].
      split; [intros Hin; apply Ha; apply CLAz; right; right; left; lia| exact I]. }
    assert (AG1517 : forall P : Z -> Prop, (forall x, P x -> okclI S1 f L x /\ ~ (f + 944 <= x < f + 952) /\ ~ (shad f + 104 <= x < shad f + 137)) -> agree_on P m15 m17).
    { intros P HP. eapply agree_trans; [apply AG1516; intros x Hx; destruct (HP _ Hx) as (H1 & H2 & _); split; [exact H1| exact H2]|].
      intros a Ha. apply MU17. cbn [outside]. split; [exact (proj2 (proj2 (HP _ Ha)))| exact I]. }
    assert (AGz17 : forall P : Z -> Prop, (forall x, P x -> okclI S1 f L x /\ ~ (f + 840 <= x < f + 848) /\ ~ (f + 944 <= x < f + 952) /\ ~ (shad f + 104 <= x < shad f + 137)) -> agree_on P mz m17).
    { intros P HP. eapply agree_trans; [apply AGz15; intros x Hx; exact (proj1 (proj2 (HP _ Hx)))|]. apply AG1517. intros x Hx. destruct (HP _ Hx) as (H1 & _ & H3 & H4). split; [exact H1| split; [exact H3| exact H4]]. }
    Local Ltac by17 H AG := eapply rw_cells_agree_nw; [exact H|]; apply AG; intros x Hx; cbn [cells_size csize Nat.add] in Hx; rewrite ?cells_size_map_C1o, ?imp_sh_length, ?imp_locals_size, ?ios_cellsI_size in Hx.
    unfold imp_regsA in HK.
    eapply HK.
    - exact FRM7.
    - exact ART17.
    - exact MI17.
    - apply (stk_agree asegs m16 m17 _ _ ST16); [| exact WM17]. intros a Ha. apply MU17. cbn [outside]. split; [clear - Ha SHT SPLO FLO; unfold STACK_WIN in *; lia| exact I].
    - rewrite LVz, LVE. reflexivity.
    - rewrite FRSz, FRS. reflexivity.
    - exact SPz.
    - exact CRz.
    - unfold rt_pres_fp. cbn [pa_F]. rewrite LVE, FRS. intros a Ha Ho.
      rewrite <- (PRESz a Ha Ho). cbn [imp_okarm_WA pa_F outside] in Ho.
      rewrite (MU17 a) by (cbn [outside]; split; [clear - Ho; lia| exact I]).
      rewrite (PRES16 a) by first [rewrite LVz, FRSz; apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; apply in_or_app; right; exact He| intros e He; exact He| lia]
                                 | cbn [outside]; split; [clear - Ho; lia| exact I]].
      apply MU15. cbn [outside]. split; [clear - Ho; lia| exact I].
    - apply (LOCBA_agree mz m17 LBz). apply AGz17. intros x Hx. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx. split; [right; right; right; left; unfold PJ_LOC_LO_A, PJ_LOC_HI_A; lia| clear - Hx FSEG SHLO; repeat split; lia].
    - apply (locx3_agreeI mz m17 LXz). apply AGz17. intros x Hx. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx. split; [right; right; right; left; unfold PJ_LOC_LO_A, PJ_LOC_HI_A; lia| clear - Hx FSEG SHLO; repeat split; lia].
    - destruct ocp as [[DATA SZ]|]; unfold imp_outA in OUTz |- *.
      + destruct OUTz as (Lq & Hq & REST). exists Lq. split; [| exact REST]. by17 Hq AGz17. unfold out_longA in Hx. cbn [cells_size csize Nat.add] in Hx. split; [right; left; lia| clear - Hx FSELF; repeat split; lia].
      + destruct OUTz as (bq & jq & Hq & REST). exists bq, jq. split; [| exact REST]. by17 Hq AGz17. unfold out_shortA in Hx. cbn [cells_size csize Nat.add] in Hx. split; [right; left; lia| clear - Hx FSELF; repeat split; lia].
    - assert (P0 : rw_cells asegs m17 (f + 832) [CB 8 j0]) by (by17 FOa AGz17; split; [right; left; lia| clear - Hx FSELF; repeat split; lia]).
      assert (P1 : rw_cells asegs m17 (f + 840) [C8 (wz OSS_SBB_VPTR_A)]).
      { eapply rw_cells_agree_nw; [exact VSB15|]. apply AG1517. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [right; left; lia| clear - Hx FSELF; split; lia]. }
      assert (P2 : rw_cells asegs m17 (f + 848) [C8 (wz PJ_LOC_IMP_A)]) by (by17 IMPz AGz17; split; [right; left; lia| clear - Hx FSELF; repeat split; lia]).
      assert (P3 : rw_cells asegs m17 (f + 856) [CB 88 jmid]) by (by17 JMz AGz17; split; [right; left; lia| clear - Hx FSELF; repeat split; lia]).
      assert (P4 : rw_cells asegs m17 (f + 944) [CB 152 j152]).
      { replace (f + 832 + 112) with (f + 944) in IOSJ16 by lia. eapply rw_cells_agree_nw; [exact IOSJ16|]. intros a Ha. apply MU17. cbn [cells_size csize Nat.add] in Ha. cbn [outside]. split; [clear - Ha FSELF; lia| exact I]. }
      pose proof (rw_cells_joinA _ _ _ _ _ P0 P1 ltac:(cbn; lia)) as K1. pose proof (rw_cells_joinA _ _ _ _ _ K1 P2 ltac:(cbn; lia)) as K2.
      pose proof (rw_cells_joinA _ _ _ _ _ K2 P3 ltac:(cbn; lia)) as K3. pose proof (rw_cells_joinA _ _ _ _ _ K3 P4 ltac:(cbn; lia)) as K4. cbn [app] in K4.
      destruct (rw_cells_forget asegs m17 _ _ K4) as [jos' JOS]. cbn [cells_size csize Nat.add] in JOS.
      assert (Q1 : rw_cells asegs m17 (f + 32) [CB 88 bb]) by (by17 FBz AGz17; split; [right; left; lia| clear - Hx FSELF; repeat split; lia]).
      assert (Q2 : rw_cells asegs m17 (f + 248) [C8 (wz (f + 192)); C8 (wz 1); C4 (wz 0); CB 4 jk1]) by (by17 ELz AGz17; split; [right; left; lia| clear - Hx FSELF; repeat split; lia]).
      destruct (rw_cells_forget asegs m17 _ _ Q2) as [jel' JEL]. cbn [cells_size csize Nat.add] in JEL.
      assert (Q4 : rw_cells asegs m17 (f + 1168) [CB 24 jt]) by (by17 FTMPz AGz17; split; [right; left; lia| clear - Hx FSELF; repeat split; lia]).
      exists bb, jel', jos', jt. split; [exact Q1| split; [exact JEL| split; [exact JOS| exact Q4]]].
    - exact FS17. }

  assert (TAIL5 : forall (Σy : rts RT) (my : mem) (st : ossA) (ra' q0 q1 q2 p0 p1 p2 p3 p4 p5 p6 p7 q3 q4 q5 q6 : word) (Fy : bvmap 5 word) (bb : list byte),
    rt_live RT Σy = oachunk st ++ L -> rt_frames RT Σy = [(f, 5%nat)] -> rt_sp0 RT Σy = rt_sp0 RT Σ ->
    rt_credit RT Σ - imp_okarm_costA (Z.of_nat (length tws)) + str_costA (oa_w st) <= rt_credit RT Σy ->
    ART RT Σy my -> mem_inv asegs my -> stk asegs my lo S1 ->
    OSSINVA my (f + 832) len st 0x20 -> oa_w st <= PJ_OUTMAX len -> OSHADOWA my (f + 832) -> LOCBA my -> locx3 my ->
    rw_cells asegs my (shad f) (map C1 (imp_sh 0 0 (-8))) ->
    rw_cells asegs my (S1 + 80) (imp_locals f (shad f) szw dw) ->
    rw_cells asegs my (f + 272) [C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
    rw_cells asegs my (f + 1168) [CB 24 jtmp] ->
    rw_cells asegs my (f + 248) [C8 (wz (f + 192)); C8 (wz 1); C4 (wz 0); CB 4 jk1] ->
    rw_cells asegs my (f + 32) [CB 88 bb] ->
    (forall a : word, aclient L [(f, 5%nat)] S1 (bv_unsigned a) -> outside (imp_okarm_WA (mkPJA lo f 5%nat (f + 32) (f + 192) TAPE NT SBUF NS tws sbs len L)) (bv_unsigned a) -> my a = m a) ->
    aevt RT PMc Σy K (MS (mkR ra' (wz S1) gp (wz TPV_A) q0 q1 q2 (wz usp) (wz S1) p0 p1 p2 p3 p4 p5 p6 p7 (wz (-8)) (wz (shad f)) (wz 1) (wz (f + 32)) (wz (f + 160)) s7 (wz SHB) (wz (f + 832)) s10 (wz dw) q3 q4 q5 q6)
                         Fy (wz 0xb5158) fc7 None my (seg_rom asegs))).
  { intros Σy my st ra' q0 q1 q2 p0 p1 p2 p3 p4 p5 p6 p7 q3 q4 q5 q6 Fy bb LVy FRSy SPy CRy ARTy MIy STy OSSIy OUTy SHy LBy LXy FSy LOCy FOUTy FTMPy ELy FBy PRESy.
    assert (INCLy : forall e, In e L -> In e (rt_live RT Σy)) by (intros e He; rewrite LVy; apply in_or_app; right; exact He).
    assert (INFy : In (f, 5%nat) (rt_frames RT Σy)) by (rewrite FRSy; left; reflexivity).
    assert (SPLOy : rt_sp0 RT Σy - STACK_WIN <= lo) by (unfold STACK_WIN; rewrite SPy; exact SPLO).
    pose proof OSSIy as [(PUTCy & REPy & NUMy) IOSy]. pose proof (OSNUMA_cap24 len st NUMy) as CAP24y. pose proof NUMy as (WBy & K0y & CAPBy & HBy).
    assert (LPOSy : forall p n, In (p, n) (oachunk st ++ L) -> 0 < n).
    { intros p n Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [| exact (LPOS p n Hin)].
      unfold oachunk in Hin. destruct (oa_heap st); [| destruct Hin]. destruct Hin as [E|[]]. injection E as <- <-. lia. }

    assert (OAR : oa_heap st = true -> 0 < oa_data st /\ oa_data st + oa_cap st <= lo /\ (f + 2048 <= oa_data st \/ oa_data st + oa_cap st <= f)
                  /\ (oa_data st + oa_cap st <= shad f \/ shad f + 256 <= oa_data st)).
    { intros HH. assert (Hin : In (oa_data st, oa_cap st) (rt_live RT Σy)) by (rewrite LVy; unfold oachunk; rewrite HH; left; reflexivity).
      pose proof (af_live_range RT AF Σy my _ _ ARTy Hin) as (Y0 & Y1 & _).
      pose proof (proj2 (proj2 (proj2 (af_frames_range RT AF Σy my f 5%nat ARTy INFy))) _ _ Hin) as Y3.
      pose proof (proj1 (af_fshadow_apart RT AF Σy my f 5%nat ARTy INFy) _ _ Hin) as Y4.
      change (fs_size 5) with 2048 in Y3, Y4. rewrite SHF in Y4. rewrite SPy in Y1. unfold STACK_WIN in Y1. lia. }
    assert (CLAy : forall x, okclI S1 f L x \/ (oa_heap st = true /\ oa_data st <= x < oa_data st + oa_cap st) -> aclient (rt_live RT Σy) (rt_frames RT Σy) S1 x).
    { intros x [H|(HH & H)]; [exact (CLA Σy _ FRSy INCLy H)|]. right; right; left. exists (oa_data st), (oa_cap st). split; [rewrite LVy; unfold oachunk; rewrite HH; left; reflexivity| lia]. }

    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut; [eapply (ok_walk6 S1 usp f szw dw ra' gp q0 q1 q2 p0 p1 p2 p3 p4 p5 p6 p7 (wz 1) (wz (f + 32)) s7 s10 q3 q4 q5 q6 0 Fy fc7 my);
                     [lia| ul| lia| ul| clear - FSELF; lia| ul| ul| ul| clear - SHT SPLO LOS1; unfold STACK_WIN in *; lia| exact LOCy| exact FSy| exact MIy]|].
    cbv beta. intros ms10 (m10 & -> & MU10 & WM10 & MI10 & FS10). apply evt_done.
    assert (ART10 : ART RT Σy m10).
    { apply (art_client_write RT AF Σy my m10 S1 ARTy ltac:(unfold STACK_WIN in *; ul)); [| exact WM10]. eapply (CLW Σy); [exact FRSy| exact INCLy| exact MU10|].
      constructor; [intros x Hx; cbn [fst snd] in Hx; right; right; left; lia|]. constructor; [intros x Hx; cbn [fst snd] in Hx; right; right; left; lia|]. constructor. }
    assert (AG910 : forall P : Z -> Prop, (forall x, P x -> ~ (shad f + 4 <= x < shad f + 15) /\ ~ (shad f + 146 <= x < shad f + 149)) -> agree_on P my m10).
    { intros P HP a Ha. apply MU10. cbn [outside]. destruct (HP _ Ha) as [H1 H2]. split; [exact H1| split; [exact H2| exact I]]. }
    assert (ST10 : stk asegs m10 lo S1) by (apply (stk_agree asegs my m10 _ _ STy); [| exact WM10]; apply AG910; intros x Hx; clear - Hx SHT SPLO; unfold STACK_WIN in *; split; lia).
    assert (SBI10 : SBINVA' m10 (f + 832) len st).
    { apply (SBINVA'_agree my m10 _ _ _ (conj PUTCy (conj REPy NUMy))). apply AG910. intros x Hx. unfold sbinv_rngI in Hx.
      destruct Hx as [Hx|(HH & Hx)]; [clear - Hx FSELF; split; lia| destruct (OAR HH) as (_ & _ & _ & Y4); clear - Hx Y4; split; lia]. }
    assert (IOS10 : IOSINVA m10 (f + 832) 0x20) by (apply (IOSINVA_agree my m10 _ _ IOSy); apply AG910; intros x Hx; clear - Hx FSELF; split; lia).
    assert (SH10 : OSHADOWA m10 (f + 832)).
    { apply (OSHADOWA_agree my m10 _ SHy). replace (shad (f + 832)) with (shad f + 104) by (unfold shad; Z.div_mod_to_equations; lia). apply AG910. intros x Hx. split; lia. }
    assert (LB10 : LOCBA m10) by (apply (LOCBA_agree my m10 LBy); apply AG910; intros x Hx; unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx; clear - Hx FSEG SHLO; split; lia).
    assert (LX10 : locx3 m10) by (apply (locx3_agreeI my m10 LXy); apply AG910; intros x Hx; unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx; clear - Hx FSEG SHLO; split; lia).
    assert (LOC10 : rw_cells asegs m10 (S1 + 80) (imp_locals f (shad f) szw dw)).
    { eapply rw_cells_agree_nw; [exact LOCy|]. apply AG910. intros x Hx. rewrite imp_locals_size in Hx. clear - Hx SHT SPLO LOS1 FLO; unfold STACK_WIN in *; split; lia. }
    assert (FOUT10 : rw_cells asegs m10 (f + 272) [C8 (wz 0); C8 (wz 0); C8 (wz 0)]).
    { eapply rw_cells_agree_nw; [exact FOUTy|]. apply AG910. intros x Hx. cbn [cells_size csize Nat.add] in Hx. clear - Hx FSELF; split; lia. }
    assert (FTMP10 : rw_cells asegs m10 (f + 1168) [CB 24 jtmp]).
    { eapply rw_cells_agree_nw; [exact FTMPy|]. apply AG910. intros x Hx. cbn [cells_size csize Nat.add] in Hx. clear - Hx FSELF; split; lia. }
    assert (EL10 : rw_cells asegs m10 (f + 248) [C8 (wz (f + 192)); C8 (wz 1); C4 (wz 0); CB 4 jk1]).
    { eapply rw_cells_agree_nw; [exact ELy|]. apply AG910. intros x Hx. cbn [cells_size csize Nat.add] in Hx. clear - Hx FSELF; split; lia. }
    assert (FB10 : rw_cells asegs m10 (f + 32) [CB 88 bb]).
    { eapply rw_cells_agree_nw; [exact FBy|]. apply AG910. intros x Hx. cbn [cells_size csize Nat.add] in Hx. clear - Hx FSELF; split; lia. }
    assert (PRES10' : forall a : word, aclient L [(f, 5%nat)] S1 (bv_unsigned a) -> outside (imp_okarm_WA (mkPJA lo f 5%nat (f + 32) (f + 192) TAPE NT SBUF NS tws sbs len L)) (bv_unsigned a) -> m10 a = m a).
    { intros a Ha Ho. rewrite <- (PRESy a Ha Ho). apply MU10. cbn [imp_okarm_WA pa_F outside] in Ho |- *. clear - Ho. repeat split; try exact I; lia. }
    pose proof (imp_sh_parts m10 (shad f) (-8) 0 0 FS10) as (_ & _ & _ & RUN3).
    assert (SHR10 : bytes_at asegs m10 (shad (f + 1168)) [z8; z8; z8]).
    { replace (shad (f + 1168)) with (shad f + 146) by (unfold shad; Z.div_mod_to_equations; lia). exact (run_bytes m10 _ _ _ RUN3). }
    assert (CRy' : str_costA (oa_w st) <= rt_credit RT Σy) by (clear - CRy CR0; lia).
    clear AG910 MU10 WM10 ARTy MIy STy OSSIy PUTCy REPy SHy LBy LXy FSy LOCy FOUTy FTMPy ELy FBy PRESy RUN3.

    replace (Z_to_bv 64 (f + 840)) with (Z_to_bv 64 (f + 832 + 8)) by (f_equal; lia). change IMP_STR_A with OSS_STR_A.
    eapply (STR Σy K L st len lo (f + 832) S1 (f + 1168) f 5%nat jtmp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fy fc7 m10 FDO MST
              LVy LPOS INFy OIN SPLOy LOW SBI10 SH10 LEN OUTy ltac:(lia) ltac:(change (fs_size 5) with 2048; lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) ltac:(right; lia)
              FTMP10 SHR10 ART10 MI10 ST10 ltac:(ul) ltac:(ul) ltac:(clear - S32; Z.div_mod_to_equations; lia)
              ltac:(rewrite LVy, length_app; unfold oachunk; unfold IMP_OKARM_LIVE_A in LVB; destruct (oa_heap st); cbn [length]; lia) CRy').
    intros Σ11 ocp n0 n1 n2 h0 h1 h2 h3 h4 h5 h6 h7 n3 n4 n5 n6 F11 m11 ART11 MI11 ST11 RES11 OCPB HM11 SHR11 SH11 LV11 FRS11 SP11 CR11 PRES11.
    rewrite (ret_pc_even 0xb519c) by lia. rewrite FRSy in FRS11, PRES11.
    assert (INCL11 : forall e, In e L -> In e (rt_live RT Σ11)) by (intros e He; rewrite LV11; apply in_or_app; right; exact (INCLy e He)).
    assert (SPLO11 : rt_sp0 RT Σ11 - STACK_WIN <= lo) by (rewrite SP11; exact SPLOy).
    assert (OCPPOS : forall p k, In (p, k) (ocp_chunks ocp) -> 0 < k).
    { intros p k Hin. destruct ocp as [[DATA SZ]|]; [| destruct Hin]. destruct Hin as [E|[]]. injection E as <- <-.
      destruct RES11 as (W23 & ESZ & _). pose proof (imp_S_range (oa_w st) W23). lia. }
    assert (LPOS11 : forall p n, In (p, n) (rt_live RT Σ11) -> 0 < n).
    { intros p n Hin. rewrite LV11, LVy in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [exact (OCPPOS p n Hin)| exact (LPOSy p n Hin)]. }
    assert (CLA11 : forall x, okclI S1 f L x \/ (oa_heap st = true /\ oa_data st <= x < oa_data st + oa_cap st) -> aclient (rt_live RT Σ11) (rt_frames RT Σ11) S1 x).
    { intros x Hx. pose proof (CLAy x Hx) as C. rewrite FRSy in C. rewrite FRS11.
      apply (aclient_mono _ _ _ _ _ _ _ C); [intros e He; rewrite LV11; apply in_or_app; right; exact He| intros e He; exact He| lia]. }
    assert (AG1011 : forall P : Z -> Prop, (forall x, P x -> (okclI S1 f L x \/ (oa_heap st = true /\ oa_data st <= x < oa_data st + oa_cap st)) /\ ~ (f + 1168 <= x < f + 1192) /\ ~ (f + 928 <= x < f + 936)) -> agree_on P m10 m11).
    { intros P HP a Ha. destruct (HP _ Ha) as (H1 & H2 & H3). apply PRES11; [pose proof (CLAy _ H1) as C; rewrite FRSy in C; exact C|].
      cbn [outside]. replace (f + 1168 + 24) with (f + 1192) by lia. replace (f + 832 + 96) with (f + 928) by lia. replace (f + 832 + 104) with (f + 936) by lia.
      split; [exact H2| split; [exact H3| exact I]]. }
    assert (FS11 : rw_cells asegs m11 (shad f) (map C1 (imp_sh (-8) 0 0))).
    { eapply rw_cells_agree_nw; [exact FS10|]. apply AG1011. intros x Hx. rewrite cells_size_map_C1o, imp_sh_length in Hx. split; [left; right; right; left; lia| clear - Hx FSELF; split; lia]. }
    assert (LOC11 : rw_cells asegs m11 (S1 + 80) (imp_locals f (shad f) szw dw)).
    { eapply rw_cells_agree_nw; [exact LOC10|]. apply AG1011. intros x Hx. rewrite imp_locals_size in Hx. split; [left; left; ul| clear - Hx FLO LOS1; split; lia]. }
    assert (FOUT11 : rw_cells asegs m11 (f + 272) [C8 (wz 0); C8 (wz 0); C8 (wz 0)]).
    { eapply rw_cells_agree_nw; [exact FOUT10|]. apply AG1011. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; right; left; lia| split; lia]. }
    assert (EL11 : rw_cells asegs m11 (f + 248) [C8 (wz (f + 192)); C8 (wz 1); C4 (wz 0); CB 4 jk1]).
    { eapply rw_cells_agree_nw; [exact EL10|]. apply AG1011. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; right; left; lia| split; lia]. }
    assert (FB11 : rw_cells asegs m11 (f + 32) [CB 88 bb]).
    { eapply rw_cells_agree_nw; [exact FB10|]. apply AG1011. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; right; left; lia| split; lia]. }
    assert (LB11 : LOCBA m11).
    { apply (LOCBA_agree m10 m11 LB10). apply AG1011. intros x Hx. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx. split; [left; right; right; right; left; unfold PJ_LOC_LO_A, PJ_LOC_HI_A; lia| clear - Hx FSEG; split; lia]. }
    assert (LX11 : locx3 m11).
    { apply (locx3_agreeI m10 m11 LX10). apply AG1011. intros x Hx. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx. split; [left; right; right; right; left; unfold PJ_LOC_LO_A, PJ_LOC_HI_A; lia| clear - Hx FSEG; split; lia]. }
    destruct SBI10 as (PUTC10 & REP10 & _). destruct PUTC10 as (SBC10 & _ & (j108 & MODE10)). destruct IOS10 as [VP10 (j124 & j260 & IOSC10)].
    replace (f + 832 + 8) with (f + 840) in SBC10 by lia. replace (f + 832 + 104) with (f + 936) in MODE10 by lia. replace (f + 832 + 112) with (f + 944) in IOSC10 by lia. replace (f + 832 + 96) with (f + 928) in HM11 by lia.
    assert (SBC11 : rw_cells asegs m11 (f + 840) (sb_cellsA st)).
    { eapply rw_cells_agree_nw; [exact SBC10|]. apply AG1011. intros x Hx. rewrite sb_cellsA_size in Hx. split; [left; right; left; lia| split; lia]. }
    assert (MODE11 : rw_cells asegs m11 (f + 936) [CB 4 mode16; CB 4 j108]).
    { eapply rw_cells_agree_nw; [exact MODE10|]. apply AG1011. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; right; left; lia| split; lia]. }
    assert (VP11 : rw_cells asegs m11 (f + 832) [C8 (wz OSS_OS_VPTR_A)]).
    { eapply rw_cells_agree_nw; [exact VP10|]. apply AG1011. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; right; left; lia| split; lia]. }
    assert (IOSC11 : rw_cells asegs m11 (f + 944) (ios_cellsI (f + 832) 0x20 j124 j260)).
    { eapply rw_cells_agree_nw; [exact IOSC10|]. apply AG1011. intros x Hx. rewrite ios_cellsI_size in Hx. split; [left; right; left; lia| split; lia]. }
    assert (REP11 : STRREPA m11 (f + 832) st).
    { apply (STRREPA_agree m10 m11 _ _ REP10); [lia|]. apply AG1011. intros x Hx. unfold strrep_rng in Hx.
      destruct Hx as [Hx|(HH & Hx)]; [split; [left; right; left; lia| split; lia]|]. destruct (OAR HH) as (_ & Y1 & Y2 & _). split; [right; split; [exact HH| lia]| clear - Hx Y1 Y2 FLO; split; lia]. }
    assert (PRES11' : forall a : word, aclient L [(f, 5%nat)] S1 (bv_unsigned a) -> outside (imp_okarm_WA (mkPJA lo f 5%nat (f + 32) (f + 192) TAPE NT SBUF NS tws sbs len L)) (bv_unsigned a) -> m11 a = m a).
    { intros a Ha Ho. rewrite <- (PRES10' a Ha Ho). apply PRES11; [| cbn [imp_okarm_WA pa_F outside] in Ho |- *; clear - Ho; repeat split; try exact I; lia].
      apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact INCLy| intros e He; exact He| lia]. }

    assert (RC11 : exists cs, rw_cells asegs m11 (f + 1168) cs /\ cells_size cs = 24%nat /\ (forall mq : mem, rw_cells asegs mq (f + 272) cs -> imp_outA mq f ocp)).
    { destruct ocp as [[DATA SZ]|].
      - destruct RES11 as (W23 & ESZ & RR & _ & D0 & D16). pose proof (imp_S_range (oa_w st) W23) as (R1 & R2 & _).
        exists [C8 (wz (SZ + 1)); C8 (wz (oa_w st)); C8 (wz DATA)]. split; [exact RR|]. split; [reflexivity|].
        intros mq Hq. exists (oa_w st). split; [exact Hq|]. unfold PJ_CAPMAX in CAPB.
        split; [rewrite land1_mod2; rewrite ESZ; clear - R2; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|]. split; [exact D16| lia].
      - destruct RES11 as (W22 & j23 & RR). exists [C1 (Z_to_bv 8 (2 * oa_w st)); CB 23 j23]. split; [exact RR|]. split; [reflexivity|].
        intros mq Hq. exists (Z_to_bv 8 (2 * oa_w st)), j23. split; [exact Hq|]. rewrite u8_litI. rewrite Z.mod_small by lia. apply short_byte0. }
    destruct RC11 as (cs & RCS11 & CSZ & OUTK).
    pose proof (rw_cells_bytes_at asegs m11 _ _ RCS11) as BYR.
    assert (LBR : length (cells_bytes cs) = 24%nat) by (rewrite (cells_bytes_length cs (proj1 (proj1 RCS11))); exact CSZ).
    pose proof (imp_sh_parts m11 (shad f) (-8) 0 0 FS11) as (_ & RUN68d & _ & _).
    clear AG1011 PRES10' PRES11 ART10 MI10 ST10 SH10 LB10 LX10 LOC10 FOUT10 FTMP10 EL10 FB10 FS10 SBC10 MODE10 VP10 IOSC10 REP10 SHR10 RES11.

    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut; [eapply (ok_walk7 S1 usp f szw dw gp n0 n1 n2 h0 h1 h2 h3 h4 h5 h6 h7 (wz 1) (wz (f + 32)) s7 s10 n3 n4 n5 n6 F11 fc7 m11);
                     [lia| ul| lia| ul| ul| ul| exact FOUT11| exact LOC11| exact MI11]|].
    cbv beta. intros ms12 <-. apply evt_done.

    assert (CS11 : checked_src RT Σ11 m11 (wz S1) lo (f + 1168) (Z.of_nat (length (cells_bytes cs)))).
    { rewrite LBR. unfold checked_src. rewrite EU. split; [| left; lia]. intros _. split.
      - change (Z.of_nat 24) with (8 * Z.of_nat 3). apply (acc_zero_run asegs m11 (f + 1168) 3); [Z.div_mod_to_equations; lia| lia| exact SHR11].
      - right; left. exists f, 5%nat. change (fs_size 5) with 2048. split; [rewrite FRS11; left; reflexivity| lia]. }
    assert (CD11 : checked_dst RT Σ11 m11 (wz S1) (f + 272) (Z.of_nat (length (cells_bytes cs)))).
    { rewrite LBR. unfold checked_dst. rewrite EU. split; [| split].
      - intros _. split; [apply (acc_sub asegs m11 (f + 160) 544); [exact (ACC_IMPLS m11 RUN68d)| lia| lia]|].
        right; left. exists f, 5%nat. change (fs_size 5) with 2048. split; [rewrite FRS11; left; reflexivity| lia].
      - intros i Hi. right; right; right; left. exists f, 5%nat. change (fs_size 5) with 2048. split; [rewrite FRS11; left; reflexivity| lia].
      - apply (rw_cells_wr_at asegs m11 _ _ 24 FOUT11). cbn. lia. }
    assert (COK11 : call_ok RT Σ11 m11 (wz S1) lo).
    { unfold call_ok. rewrite EU. split; [exact ST11|]. split; [exact SPLO11|]. split; [ul|]. split; [ul| clear - S32; Z.div_mod_to_equations; lia]. }
    eapply (aevt_memcpyP RT RC PMc FDO MST Σ11 K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F11 fc7 m11 (f + 272) (f + 1168) (cells_bytes cs) lo
              eq_refl eq_refl ltac:(rewrite LBR; reflexivity) ltac:(ul) ltac:(ul) ltac:(rewrite LBR; cbn; lia) BYR CS11 CD11 ltac:(rewrite LBR; cbn; lia) ART11 MI11 COK11).
    intros r0 r1 r2 k1 k2 k3 k4 k5 k6 k7 r3 r4 r5 r6 F12 m12 (ART12 & MI12 & WM12 & ST12) PRES12 BY12. rewrite EU in ST12, PRES12. rewrite LBR in PRES12. change (Z.of_nat 24) with 24 in PRES12.
    rewrite (ret_pc_even 0xb51d0) by lia.
    assert (AG1112 : forall P : Z -> Prop, (forall x, P x -> (okclI S1 f L x \/ (oa_heap st = true /\ oa_data st <= x < oa_data st + oa_cap st)) /\ ~ (f + 272 <= x < f + 272 + 24)) -> agree_on P m11 m12).
    { intros P HP a Ha. destruct (HP _ Ha) as [H1 H2]. apply PRES12; [exact (CLA11 _ H1)| exact H2]. }
    assert (OUT12 : imp_outA m12 f ocp).
    { apply OUTK. pose proof (rw_cells_CB_intro m12 (f + 272) _ BY12 ltac:(rewrite LBR; apply (wr_at_transport asegs m11 m12 (f + 272) 24); [apply (rw_cells_wr_at asegs m11 _ _ 24 FOUT11); cbn; lia| exact WM12])) as X.
      rewrite LBR in X. apply (rw_cells_recastI m12 (f + 272) _ cs) in X; [exact X| exact (proj1 (proj1 RCS11))| cbn [cells_bytes cbytes app]; rewrite app_nil_r; reflexivity| cbn; rewrite CSZ; reflexivity]. }
    assert (FS12 : rw_cells asegs m12 (shad f) (map C1 (imp_sh (-8) 0 0))).
    { eapply rw_cells_agree_nw; [exact FS11|]. apply AG1112. intros x Hx. rewrite cells_size_map_C1o, imp_sh_length in Hx. split; [left; right; right; left; lia| clear - Hx FSELF; lia]. }
    assert (LOC12 : rw_cells asegs m12 (S1 + 80) (imp_locals f (shad f) szw dw)).
    { eapply rw_cells_agree_nw; [exact LOC11|]. apply AG1112. intros x Hx. rewrite imp_locals_size in Hx. split; [left; left; ul| clear - Hx FLO LOS1; lia]. }
    assert (EL12 : rw_cells asegs m12 (f + 248) [C8 (wz (f + 192)); C8 (wz 1); C4 (wz 0); CB 4 jk1]).
    { eapply rw_cells_agree_nw; [exact EL11|]. apply AG1112. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; right; left; lia| lia]. }
    assert (FB12 : rw_cells asegs m12 (f + 32) [CB 88 bb]).
    { eapply rw_cells_agree_nw; [exact FB11|]. apply AG1112. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; right; left; lia| lia]. }
    assert (FTMP12 : exists jt, rw_cells asegs m12 (f + 1168) [CB 24 jt]).
    { assert (X : rw_cells asegs m12 (f + 1168) cs) by (eapply rw_cells_agree_nw; [exact RCS11|]; apply AG1112; intros x Hx; rewrite CSZ in Hx; split; [left; right; left; lia| lia]).
      destruct (rw_cells_forget asegs m12 _ _ X) as [jt X']. rewrite CSZ in X'. exists jt. exact X'. }
    destruct FTMP12 as [jt FTMP12].
    assert (LB12 : LOCBA m12).
    { apply (LOCBA_agree m11 m12 LB11). apply AG1112. intros x Hx. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx. split; [left; right; right; right; left; unfold PJ_LOC_LO_A, PJ_LOC_HI_A; lia| clear - Hx FSEG; lia]. }
    assert (LX12 : locx3 m12).
    { apply (locx3_agreeI m11 m12 LX11). apply AG1112. intros x Hx. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx. split; [left; right; right; right; left; unfold PJ_LOC_LO_A, PJ_LOC_HI_A; lia| clear - Hx FSEG; lia]. }
    assert (SBC12 : rw_cells asegs m12 (f + 840) (sb_cellsA st)).
    { eapply rw_cells_agree_nw; [exact SBC11|]. apply AG1112. intros x Hx. rewrite sb_cellsA_size in Hx. split; [left; right; left; lia| lia]. }
    assert (MODE12 : rw_cells asegs m12 (f + 936) [CB 4 mode16; CB 4 j108]).
    { eapply rw_cells_agree_nw; [exact MODE11|]. apply AG1112. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; right; left; lia| lia]. }
    assert (HM12 : rw_cells asegs m12 (f + 928) [C8 (wz (oa_data st + oa_w st))]).
    { eapply rw_cells_agree_nw; [exact HM11|]. apply AG1112. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; right; left; lia| lia]. }
    assert (VP12 : rw_cells asegs m12 (f + 832) [C8 (wz OSS_OS_VPTR_A)]).
    { eapply rw_cells_agree_nw; [exact VP11|]. apply AG1112. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; right; left; lia| lia]. }
    assert (IOSC12 : rw_cells asegs m12 (f + 944) (ios_cellsI (f + 832) 0x20 j124 j260)).
    { eapply rw_cells_agree_nw; [exact IOSC11|]. apply AG1112. intros x Hx. rewrite ios_cellsI_size in Hx. split; [left; right; left; lia| lia]. }
    assert (REP12 : STRREPA m12 (f + 832) st).
    { apply (STRREPA_agree m11 m12 _ _ REP11); [lia|]. apply AG1112. intros x Hx. unfold strrep_rng in Hx.
      destruct Hx as [Hx|(HH & Hx)]; [split; [left; right; left; lia| lia]|]. destruct (OAR HH) as (_ & Y1 & Y2 & _). split; [right; split; [exact HH| lia]| clear - Hx Y1 Y2 FLO; lia]. }
    assert (SH12 : OSHADOWA m12 (f + 832)).
    { apply (OSHADOWA_agree m11 m12 _ SH11). replace (shad (f + 832)) with (shad f + 104) by (unfold shad; Z.div_mod_to_equations; lia). apply AG1112. intros x Hx. split; [left; right; right; left; lia| clear - Hx FSELF; lia]. }
    assert (PRES12' : forall a : word, aclient L [(f, 5%nat)] S1 (bv_unsigned a) -> outside (imp_okarm_WA (mkPJA lo f 5%nat (f + 32) (f + 192) TAPE NT SBUF NS tws sbs len L)) (bv_unsigned a) -> m12 a = m a).
    { intros a Ha Ho. rewrite <- (PRES11' a Ha Ho). apply PRES12; [| cbn [imp_okarm_WA pa_F outside] in Ho |- *; clear - Ho; lia].
      apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact INCL11| intros e He; rewrite FRS11; exact He| lia]. }
    clear AG1112 PRES11' PRES12 BY12 BYR CS11 CD11 COK11 ART11 MI11 ST11 FS11 LOC11 FOUT11 EL11 FB11 LB11 LX11 SBC11 MODE11 VP11 IOSC11 REP11 HM11 SH11 SHR11 RCS11 RUN68d OUTK.

    pose proof (ROWS Σ11 m12 ART12) as (V1 & V2 & V3 & _).
    pose proof (acc_lit RT AF Σ11 m12 0x16fb88 40 ART12 ltac:(unfold ACC_LITS; repeat (first [left; reflexivity | right]))) as ACV.
    pose proof (acc_lit RT AF Σ11 m12 0x16fb38 8 ART12 ltac:(unfold ACC_LITS; repeat (first [left; reflexivity | right]))) as ACB.
    assert (VSEP : forall x, (shad 0x16fb88 <= x <= shad (0x16fb88 + 40) \/ shad 0x16fb38 <= x <= shad (0x16fb38 + 8)) -> outside (ok_W8 f) x).
    { intros x Hx. unfold shad, SHB in Hx. cbn in Hx. unfold ok_W8. cbn [outside]. unfold shad, SHB. clear - Hx FRHI FSEG. repeat split; try exact I; Z.div_mod_to_equations; lia. }
    assert (SHZV : forall m', munch (ok_W8 f) m12 m' -> wmono asegs m12 m' -> shz m' OSS_VTT_A 40).
    { intros m' MU' _. unfold OSS_VTT_A. apply (shz_of_acc m' 0x16fb88 40); [| reflexivity| lia]. apply (acc_agree_at m12 m' 0x16fb88 40 ACV ltac:(lia)).
      apply (agree_of_munch _ _ _ _ MU'). intros x Hx. apply VSEP. left. exact Hx. }
    assert (SHZB : forall m', munch (ok_W8 f) m12 m' -> wmono asegs m12 m' -> shz m' OSS_VBOFF_A 8).
    { intros m' MU' _. unfold OSS_VBOFF_A. apply (shz_of_acc m' 0x16fb38 8); [| reflexivity| lia]. apply (acc_agree_at m12 m' 0x16fb38 8 ACB ltac:(lia)).
      apply (agree_of_munch _ _ _ _ MU'). intros x Hx. apply VSEP. right. exact Hx. }
    assert (SHZO : forall m', munch (ok_W8 f) m12 m' -> wmono asegs m12 m' -> shz m' (f + 832) 264).
    { intros m' MU' _. change 264 with (8 * Z.of_nat 33). apply (shz_of_zero_run m' (f + 832) 33); [clear - F64; Z.div_mod_to_equations; lia| lia|].
      apply (OSHADOWA_agree m12 m' _ SH12). apply (agree_of_munch _ _ _ _ MU'). intros x Hx. replace (shad (f + 832)) with (shad f + 104) in Hx by (unfold shad; Z.div_mod_to_equations; lia).
      unfold ok_W8. cbn [outside]. clear - Hx FSELF. repeat split; try exact I; lia. }

    assert (RD72 : exists b72 : byte, (forall m', munch (ok_W8 f) m12 m' -> wmono asegs m12 m' -> ov_read_bytes asegs m' (wa (f + 904)) 1 = Some [b72])
                                      /\ Z.land (bv_unsigned b72) 1 = (if oa_heap st then 1 else 0)).
    { assert (AGR : forall m', munch (ok_W8 f) m12 m' -> agree_on (strrep_rng (f + 832) st) m12 m').
      { intros m' MU'. apply (agree_of_munch _ _ _ _ MU'). intros x Hx. unfold strrep_rng in Hx. unfold ok_W8. cbn [outside].
        destruct Hx as [Hx|(HH & Hx)]; [clear - Hx FSELF; repeat split; try exact I; lia|]. destruct (OAR HH) as (_ & _ & Y2 & Y4). clear - Hx Y2 Y4. repeat split; try exact I; lia. }
      unfold STRREPA in REP12. destruct (oa_heap st) eqn:HP.
      - destruct REP12 as (RW & _ & _ & _ & C16). exists (Z_to_bv 8 (bv_unsigned (wz (oa_cap st + 1)))). split.
        + intros m' MU' _. assert (RW' : rw_cells asegs m' (f + 832 + 72) [C8 (wz (oa_cap st + 1)); C8 (wz (oa_cap st - 1)); C8 (wz (oa_data st))]).
          { eapply rw_cells_agree_nw; [exact RW|]. eapply agree_sub; [apply (AGR m' MU')|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. unfold strrep_rng. left. lia. }
          replace (f + 904) with (f + 832 + 72) by lia. exact (rw_cells_C8_read1_g asegs m' _ _ _ RW').
        + rewrite u8_litI. rewrite unsigned_lit by ul. apply long_byte0. clear - C16. Z.div_mod_to_equations. lia.
      - destruct REP12 as (RW & _ & _). exists (Z_to_bv 8 44). split; [| reflexivity].
        intros m' MU' _. assert (RW' : rw_cells asegs m' (f + 832 + 72) [C1 (Z_to_bv 8 44)]).
        { eapply rw_cells_agree_nw; [exact RW|]. eapply agree_sub; [apply (AGR m' MU')|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. unfold strrep_rng. left. lia. }
        replace (f + 904) with (f + 832 + 72) by lia. exact (rw_cells_C1_read1 m' _ _ _ RW'). }
    destruct RD72 as (b72 & RD72 & LAND).
    pose proof SBC12 as SBREST12. unfold sb_cellsA in SBREST12. takeZ SBREST12 1%nat (f + 848) SBV12.
    pose proof IOSC12 as IOSR12. unfold ios_cellsI in IOSR12. takeZ IOSR12 1%nat (f + 952) VIOS12.
    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut; [eapply (ok_walk8 S1 usp f szw dw gp r0 r1 r2 (wz (f + 272)) k1 k2 k3 k4 k5 k6 k7 s7 s10 r3 r4 r5 r6 0 b72 F12 fc7 m12);
                     [ul| ul| exact SHLO| ul| clear - FSELF; lia| exact F64| ul| ul| ul| clear - SHT SPLO LOS1; unfold STACK_WIN in *; lia
                     | exact SHZV| exact SHZB| exact SHZO| exact RD72| exact VP12| exact SBV12| exact VIOS12| exact FS12| exact V1| exact V2| exact V3| exact MI12]|].
    cbv beta. intros ms13 (m13 & -> & MU13 & WM13 & MI13 & VP13 & VSB13 & VIOS13 & FS13). apply evt_done.
    assert (ART13 : ART RT Σ11 m13).
    { apply (art_client_write RT AF Σ11 m12 m13 S1 ART12 ltac:(unfold STACK_WIN in *; clear - SPLO11 LOS1; lia)); [| exact WM13]. intros a Ha. apply MU13. unfold ok_W8. cbn [outside].
      assert (CF : forall x, f <= x < f + 2040 -> aclient (rt_live RT Σ11) (rt_frames RT Σ11) S1 x) by (intros x Hx; apply CLA11; left; right; left; exact Hx).
      assert (CS : forall x, shad f <= x < shad f + 256 -> aclient (rt_live RT Σ11) (rt_frames RT Σ11) S1 x) by (intros x Hx; apply CLA11; left; right; right; left; exact Hx).
      repeat split; try exact I; intros Hin; apply Ha; first [apply CF; lia | apply CS; lia]. }
    assert (AG1213 : forall P : Z -> Prop, (forall x, P x -> ~ (shad f + 146 <= x < shad f + 149) /\ ~ (f + 832 <= x < f + 848) /\ ~ (f + 944 <= x < f + 952)) -> agree_on P m12 m13).
    { intros P HP a Ha. apply MU13. unfold ok_W8. cbn [outside]. destruct (HP _ Ha) as (H1 & H2 & H3). repeat split; try exact I; lia. }
    assert (ST13 : stk asegs m13 lo S1) by (apply (stk_agree asegs m12 m13 _ _ ST12); [| exact WM13]; apply AG1213; intros x Hx; clear - Hx SHT SPLO FLO LOS1; unfold STACK_WIN in *; repeat split; lia).
    assert (SBREST13 : rw_cells asegs m13 (f + 848) [C8 (wz OSS_CLASSIC_A); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz (oa_data st)); C8 (wz (oa_data st + oa_w st)); C8 (wz (oa_data st + oa_lim st))]).
    { eapply rw_cells_agree_nw; [exact SBREST12|]. apply AG1213. intros x Hx. cbn [cells_size csize Nat.add] in Hx. clear - Hx FSELF. repeat split; lia. }
    assert (IOSR13 : rw_cells asegs m13 (f + 952) [C4 (wz 0x1002); CB 4 j124; C8 (wz 6); C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz (f + 832 + 8)); C8 (wz OSS_CLASSIC_A);
                                                  C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 0x20); CB 4 j260]).
    { eapply rw_cells_agree_nw; [exact IOSR12|]. apply AG1213. intros x Hx. cbn [cells_size csize Nat.add] in Hx. clear - Hx FSELF. repeat split; lia. }
    pose proof (rw_cells_joinA _ _ _ _ _ VIOS13 IOSR13 ltac:(cbn; lia)) as IOSC13. cbn [app] in IOSC13. clear IOSR13.
    change (rw_cells asegs m13 (f + 944) (ios_cellsI (f + 832) 0x20 j124 j260)) in IOSC13.
    Local Ltac by13 H AG := eapply rw_cells_agree_nw; [exact H|]; apply AG; intros x Hx; cbn [cells_size csize Nat.add] in Hx; rewrite ?cells_size_map_C1o, ?imp_sh_length, ?imp_locals_size in Hx.
    assert (LOC13 : rw_cells asegs m13 (S1 + 80) (imp_locals f (shad f) szw dw)) by (by13 LOC12 AG1213; clear - Hx SHT SPLO FLO LOS1; unfold STACK_WIN in *; repeat split; lia).
    assert (EL13 : rw_cells asegs m13 (f + 248) [C8 (wz (f + 192)); C8 (wz 1); C4 (wz 0); CB 4 jk1]) by (by13 EL12 AG1213; clear - Hx FSELF; repeat split; lia).
    assert (FB13 : rw_cells asegs m13 (f + 32) [CB 88 bb]) by (by13 FB12 AG1213; clear - Hx FSELF; repeat split; lia).
    assert (FTMP13 : rw_cells asegs m13 (f + 1168) [CB 24 jt]) by (by13 FTMP12 AG1213; clear - Hx FSELF; repeat split; lia).
    assert (MODE13 : rw_cells asegs m13 (f + 936) [CB 4 mode16; CB 4 j108]) by (by13 MODE12 AG1213; clear - Hx FSELF; repeat split; lia).
    assert (HM13 : rw_cells asegs m13 (f + 928) [C8 (wz (oa_data st + oa_w st))]) by (by13 HM12 AG1213; clear - Hx FSELF; repeat split; lia).
    assert (LB13 : LOCBA m13) by (apply (LOCBA_agree m12 m13 LB12); apply AG1213; intros x Hx; unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx; clear - Hx FSEG SHLO; repeat split; lia).
    assert (LX13 : locx3 m13) by (apply (locx3_agreeI m12 m13 LX12); apply AG1213; intros x Hx; unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx; clear - Hx FSEG SHLO; repeat split; lia).
    assert (SH13 : OSHADOWA m13 (f + 832)).
    { apply (OSHADOWA_agree m12 m13 _ SH12). replace (shad (f + 832)) with (shad f + 104) by (unfold shad; Z.div_mod_to_equations; lia). apply AG1213. intros x Hx. clear - Hx FSELF. repeat split; lia. }
    assert (REP13 : STRREPA m13 (f + 832) st).
    { apply (STRREPA_agree m12 m13 _ _ REP12); [lia|]. apply AG1213. intros x Hx. unfold strrep_rng in Hx.
      destruct Hx as [Hx|(HH & Hx)]; [clear - Hx FSELF; repeat split; lia|]. destruct (OAR HH) as (_ & _ & Y2 & Y4). clear - Hx Y2 Y4. repeat split; lia. }
    assert (OUT13 : imp_outA m13 f ocp).
    { destruct ocp as [[DATA SZ]|]; unfold imp_outA in OUT12 |- *.
      - destruct OUT12 as (Lq & Hq & REST). exists Lq. split; [| exact REST]. by13 Hq AG1213. clear - Hx FSELF. unfold out_longA in Hx. cbn [cells_size csize Nat.add] in Hx. repeat split; lia.
      - destruct OUT12 as (bq & jq & Hq & REST). exists bq, jq. split; [| exact REST]. by13 Hq AG1213. clear - Hx FSELF. unfold out_shortA in Hx. cbn [cells_size csize Nat.add] in Hx. repeat split; lia. }
    assert (PRES13' : forall a : word, aclient L [(f, 5%nat)] S1 (bv_unsigned a) -> outside (imp_okarm_WA (mkPJA lo f 5%nat (f + 32) (f + 192) TAPE NT SBUF NS tws sbs len L)) (bv_unsigned a) -> m13 a = m a).
    { intros a Ha Ho. rewrite <- (PRES12' a Ha Ho). apply MU13. unfold ok_W8. cbn [imp_okarm_WA pa_F outside] in Ho |- *. clear - Ho. repeat split; try exact I; lia. }
    assert (CR13 : rt_credit RT Σ - imp_okarm_costA (Z.of_nat (length tws)) <= rt_credit RT Σ11) by (clear - CRy CR11; lia).
    clear AG1213 PRES12' ART12 MI12 ST12 WM12 FS12 LOC12 EL12 FB12 FTMP12 LB12 LX12 SBC12 SBREST12 MODE12 HM12 VP12 IOSC12 VIOS12 IOSR12 REP12 SH12 OUT12 SHZV SHZB SHZO RD72 ACV ACB VSEP V1 V2 V3.

    rewrite LAND. unfold STRREPA in REP13. destruct (oa_heap st) eqn:HP.
    -
      destruct REP13 as (RW13 & _ & D0 & D16 & C16). replace (f + 832 + 72) with (f + 904) in RW13 by lia.
      apply (aevt_evt RT AF PMc MST). zstep. if_false.
      eapply evt_cut; [eapply (ok_walk8b S1 usp f szw dw (oa_cap st + 1) (oa_cap st - 1) (oa_data st) gp r0 r1 r2 (wz OSS_SB_VPTR_A) (wz 1) (wz 0) k3 k4 k5 k6 k7 s7 s10 r3 r4 r5 r6 F12 fc7 m13);
                       [lia| ul| ul| destruct (OAR eq_refl); ul| exact RW13| exact MI13]|].
      cbv beta. intros ms14 <-. apply evt_done.
      assert (INO : In (oa_data st, oa_cap st) (rt_live RT Σ11)) by (rewrite LV11, LVy; apply in_or_app; right; unfold oachunk; rewrite HP; left; reflexivity).
      eapply (aevt_opdel RT AF RC PMc FDO MST Σ11 K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F12 fc7 m13 (oa_data st) (oa_cap st) lo INO eq_refl ART13 MI13).
      { unfold call_ok. rewrite EU. split; [exact ST13|]. split; [exact SPLO11|]. split; [ul|]. split; [ul| clear - S32; Z.div_mod_to_equations; lia]. }
      { unfold unwind_ok. rewrite EU, unsigned_lit by ul. right; right. lia. }
      intros Σ14 v z0 z1 z2 i1 i2 i3 i4 i5 i6 i7 z3 z4 z5 z6 F14 m14 (ART14 & MI14 & ST14) PRES14 LV14 FRS14 SP14 CR14.
      rewrite EU in ST14, PRES14. rewrite (ret_pc_even 0xb5270) by lia. rewrite FRS11 in FRS14, PRES14.
      assert (LV14' : rt_live RT Σ14 = ocp_chunks ocp ++ L).
      { rewrite LV14, LV11, LVy. unfold oachunk. rewrite HP. apply (live_remove_mid (ocp_chunks ocp) L).
        pose proof (live_starts_nodup RT AF Σ11 m13 ART13 LPOS11) as ND. rewrite LV11, LVy in ND. unfold oachunk in ND. rewrite HP in ND. exact ND. }
      rewrite LV14' in PRES14.
      assert (AG1314 : forall P : Z -> Prop, (forall x, P x -> okclI S1 f L x) -> agree_on P m13 m14).
      { intros P HPP a Ha. apply PRES14. pose proof (CLA Σ14 _ FRS14 ltac:(intros e He; rewrite LV14'; apply in_or_app; right; exact He) (HPP _ Ha)) as C. rewrite LV14', FRS14 in C. exact C. }
      Local Ltac by14 H AG := eapply rw_cells_agree_nw; [exact H|]; apply AG; intros x Hx; cbn [cells_size csize Nat.add] in Hx; rewrite ?cells_size_map_C1o, ?imp_sh_length, ?imp_locals_size, ?ios_cellsI_size in Hx.

      assert (FO14 : exists j0 jmid, rw_cells asegs m14 (f + 832) [CB 8 j0; C8 (wz OSS_SB_VPTR_A); C8 (wz PJ_LOC_IMP_A); CB 88 jmid]).
      { assert (P0 : rw_cells asegs m14 (f + 832) [C8 (wz OSS_OS_VPTR_A)]) by (by14 VP13 AG1314; right; left; lia).
        assert (P1 : rw_cells asegs m14 (f + 840) [C8 (wz OSS_SB_VPTR_A)]) by (by14 VSB13 AG1314; right; left; lia).
        assert (P2 : rw_cells asegs m14 (f + 848) [C8 (wz OSS_CLASSIC_A); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz (oa_data st)); C8 (wz (oa_data st + oa_w st)); C8 (wz (oa_data st + oa_lim st))]) by (by14 SBREST13 AG1314; right; left; lia).
        assert (P3 : rw_cells asegs m14 (f + 904) [C8 (wz (oa_cap st + 1)); C8 (wz (oa_cap st - 1)); C8 (wz (oa_data st))]) by (by14 RW13 AG1314; right; left; lia).
        assert (P4 : rw_cells asegs m14 (f + 928) [C8 (wz (oa_data st + oa_w st))]) by (by14 HM13 AG1314; right; left; lia).
        assert (P5 : rw_cells asegs m14 (f + 936) [CB 4 mode16; CB 4 j108]) by (by14 MODE13 AG1314; right; left; lia).
        takeZ P2 1%nat (f + 856) P2'.
        pose proof (rw_cells_joinA _ _ _ _ _ P2 P3 ltac:(cbn; lia)) as J1. pose proof (rw_cells_joinA _ _ _ _ _ J1 P4 ltac:(cbn; lia)) as J2. pose proof (rw_cells_joinA _ _ _ _ _ J2 P5 ltac:(cbn; lia)) as J3.
        cbn [app] in J3. destruct (rw_cells_forget asegs m14 _ _ J3) as [jmid JM]. cbn [cells_size csize Nat.add] in JM.
        destruct (rw_cells_forget asegs m14 _ _ P0) as [j0 J0]. cbn [cells_size csize Nat.add] in J0.
        exists j0, jmid. unfold OSS_CLASSIC_A in P2'.
        pose proof (rw_cells_joinA _ _ _ _ _ J0 P1 ltac:(cbn; lia)) as K1. pose proof (rw_cells_joinA _ _ _ _ _ K1 P2' ltac:(cbn; lia)) as K2. pose proof (rw_cells_joinA _ _ _ _ _ K2 JM ltac:(cbn; lia)) as K3.
        cbn [app] in K3. exact K3. }
      destruct FO14 as (j0 & jmid & FO14).
      apply (TAIL8 Σ14 m14 ocp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (wz OSS_SB_VPTR_A) F14 bb j0 jmid j124 j260 jt);
        [exact LV14'| exact FRS14| rewrite SP14, SP11; exact SPy| rewrite CR14; exact CR13| exact OCPPOS| exact ART14| exact MI14| exact ST14| exact FO14| | | | | | | | | | |].
      + by14 IOSC13 AG1314. right; left; lia.
      + apply (OSHADOWA_agree m13 m14 _ SH13). replace (shad (f + 832)) with (shad f + 104) by (unfold shad; Z.div_mod_to_equations; lia). apply AG1314. intros x Hx. right; right; left; lia.
      + apply (LOCBA_agree m13 m14 LB13). apply AG1314. intros x Hx. right; right; right; left. exact Hx.
      + apply (locx3_agreeI m13 m14 LX13). apply AG1314. intros x Hx. right; right; right; left. exact Hx.
      + by14 FS13 AG1314. right; right; left; lia.
      + by14 LOC13 AG1314. left; ul.
      + destruct ocp as [[DATA SZ]|]; unfold imp_outA in OUT13 |- *.
        * destruct OUT13 as (Lq & Hq & REST). exists Lq. split; [| exact REST]. by14 Hq AG1314. unfold out_longA in Hx. cbn [cells_size csize Nat.add] in Hx. right; left; lia.
        * destruct OUT13 as (bq & jq & Hq & REST). exists bq, jq. split; [| exact REST]. by14 Hq AG1314. unfold out_shortA in Hx. cbn [cells_size csize Nat.add] in Hx. right; left; lia.
      + by14 FTMP13 AG1314. right; left; lia.
      + by14 EL13 AG1314. right; left; lia.
      + by14 FB13 AG1314. right; left; lia.
      + intros a Ha Ho. rewrite <- (PRES13' a Ha Ho). apply PRES14. apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; apply in_or_app; right; exact He| intros e He; exact He| lia].
    -
      destruct REP13 as (RW13 & (bs23 & R23) & ED). replace (f + 832 + 72) with (f + 904) in RW13 by lia. replace (f + 832 + 73) with (f + 905) in R23 by lia.
      apply (aevt_evt RT AF PMc MST). zstep. if_true. apply evt_done.
      assert (FO13 : exists j0 jmid, rw_cells asegs m13 (f + 832) [CB 8 j0; C8 (wz OSS_SB_VPTR_A); C8 (wz PJ_LOC_IMP_A); CB 88 jmid]).
      { pose proof SBREST13 as P2. takeZ P2 1%nat (f + 856) P2'.
        pose proof (rw_cells_joinA _ _ _ _ _ P2 RW13 ltac:(cbn; lia)) as J0. pose proof (rw_cells_joinA _ _ _ _ _ J0 R23 ltac:(cbn; lia)) as J1.
        pose proof (rw_cells_joinA _ _ _ _ _ J1 HM13 ltac:(cbn; lia)) as J2. pose proof (rw_cells_joinA _ _ _ _ _ J2 MODE13 ltac:(cbn; lia)) as J3.
        cbn [app] in J3. destruct (rw_cells_forget asegs m13 _ _ J3) as [jmid JM]. cbn [cells_size csize Nat.add] in JM.
        destruct (rw_cells_forget asegs m13 _ _ VP13) as [j0 J00]. cbn [cells_size csize Nat.add] in J00.
        exists j0, jmid. unfold OSS_CLASSIC_A in P2'.
        pose proof (rw_cells_joinA _ _ _ _ _ J00 VSB13 ltac:(cbn; lia)) as K1. pose proof (rw_cells_joinA _ _ _ _ _ K1 P2' ltac:(cbn; lia)) as K2. pose proof (rw_cells_joinA _ _ _ _ _ K2 JM ltac:(cbn; lia)) as K3.
        cbn [app] in K3. exact K3. }
      destruct FO13 as (j0 & jmid & FO13).
      apply (TAIL8 Σ11 m13 ocp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (wz OSS_SB_VPTR_A) F12 bb j0 jmid j124 j260 jt);
        [rewrite LV11, LVy; unfold oachunk; rewrite HP; reflexivity| exact FRS11| rewrite SP11; exact SPy| exact CR13| exact OCPPOS| exact ART13| exact MI13| exact ST13| exact FO13
        | exact IOSC13| exact SH13| exact LB13| exact LX13| exact FS13| exact LOC13| exact OUT13| exact FTMP13| exact EL13| exact FB13| exact PRES13']. }

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (ok_walk5 S1 usp f (sa_buf st') (sa_size st') (sa_cap st') szw dw gp w0 w1 w2 (wz (f + 832)) c1 c2 c3 c4 c5 c6 c7 s7 s10 (wz (f + 192)) w3 w4 w5 w6 F8 fc7 m8);
                   [lia| ul| lia| lia| lia| ul| ul| ul| exact SC8| exact LOC8| exact MI8]|].
  cbv beta. intros ms9 [(EB & ->)|(NB & ->)]; apply evt_done.
  -
    destruct (sa_heap st') eqn:HP; [destruct (BHEAP eq_refl); exfalso; lia|].
    apply (TAIL5 Σ8 m8 st8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F8 bb8);
      [rewrite LV8; unfold sbchunkA; rewrite HP; reflexivity| exact FRS8| rewrite SP8; exact SP7| exact CRED8| exact ART8| exact MI8| exact ST8
      | exact OSSI8| rewrite W8EQ; exact OUTB| exact SH8| exact LB8| exact LX8| exact FS8| exact LOC8| exact FOUT8| exact FTMP8| exact EL8| exact FB8| exact PRES8'].
  -
    destruct (sa_heap st') eqn:HP; [| exfalso; exact (NB (BINL eq_refl))].
    assert (INB : In (sa_buf st', sa_cap st') (rt_live RT Σ8)) by (rewrite LV8; apply in_or_app; right; unfold sbchunkA; rewrite HP; left; reflexivity).
    eapply (aevt_delarr RT AF RC PMc FDO MST Σ8 K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F8 fc7 m8 (sa_buf st') (sa_cap st') lo INB eq_refl ART8 MI8).
    { unfold call_ok. rewrite EU, SP8, SP7. split; [exact ST8|]. split; [exact SPLO|]. split; [ul|]. split; [ul| clear - S32; Z.div_mod_to_equations; lia]. }
    { unfold unwind_ok. rewrite EU, unsigned_lit by ul. right; right. lia. }
    intros Σ9 v q0 q1 q2 p1 p2 p3 p4 p5 p6 p7 q3 q4 q5 q6 F9 m9 (ART9 & MI9 & ST9) PRES9 LV9 FRS9 SP9 CR9.
    rewrite EU in ST9, PRES9. rewrite (ret_pc_even 0xb5158) by lia. rewrite FRS8 in FRS9, PRES9.
    assert (LV9' : rt_live RT Σ9 = oachunk st8 ++ L).
    { rewrite LV9, LV8. unfold sbchunkA. rewrite HP. apply (live_remove_mid (oachunk st8) L).
      pose proof (live_starts_nodup RT AF Σ8 m8 ART8 ltac:(rewrite LV8; exact LPOS8)) as ND. rewrite LV8 in ND. unfold sbchunkA in ND. rewrite HP in ND. exact ND. }
    rewrite LV9' in PRES9.
    assert (AG89 : forall P : Z -> Prop, (forall x, P x -> okclI S1 f L x \/ (oa_heap st8 = true /\ oa_data st8 <= x < oa_data st8 + oa_cap st8)) -> agree_on P m8 m9).
    { intros P HPP a Ha. apply PRES9. destruct (HPP _ Ha) as [H|(HH & H)].
      - pose proof (CLA Σ9 _ FRS9 ltac:(intros e He; rewrite LV9'; apply in_or_app; right; exact He) H) as C. rewrite LV9', FRS9 in C. exact C.
      - right; right; left. exists (oa_data st8), (oa_cap st8). split; [unfold oachunk; rewrite HH; left; reflexivity| lia]. }
    apply (TAIL5 Σ9 m9 st8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F9 bb8);
      [exact LV9'| exact FRS9| rewrite SP9, SP8; exact SP7| rewrite CR9; exact CRED8| exact ART9| exact MI9| exact ST9| | | | | | | | | | | |].
    + destruct OSSI8 as [SBI8 IOS8]. split.
      * apply (SBINVA'_agree m8 m9 _ _ _ SBI8). apply AG89. intros x Hx. unfold sbinv_rngI in Hx. destruct Hx as [Hx|Hx]; [left; right; left; lia| right; exact Hx].
      * apply (IOSINVA_agree m8 m9 _ _ IOS8). apply AG89. intros x Hx. left; right; left; lia.
    + rewrite W8EQ; exact OUTB.
    + apply (OSHADOWA_agree m8 m9 _ SH8). replace (shad (f + 832)) with (shad f + 104) by (unfold shad; Z.div_mod_to_equations; lia). apply AG89. intros x Hx. left; right; right; left; lia.
    + apply (LOCBA_agree m8 m9 LB8). apply AG89. intros x Hx. left; right; right; right; left. exact Hx.
    + apply (locx3_agreeI m8 m9 LX8). apply AG89. intros x Hx. left; right; right; right; left. exact Hx.
    + eapply rw_cells_agree_nw; [exact FS8|]. apply AG89. intros x Hx. rewrite cells_size_map_C1o, imp_sh_length in Hx. left; right; right; left; lia.
    + eapply rw_cells_agree_nw; [exact LOC8|]. apply AG89. intros x Hx. rewrite imp_locals_size in Hx. left; left; ul.
    + eapply rw_cells_agree_nw; [exact FOUT8|]. apply AG89. intros x Hx. cbn [cells_size csize Nat.add] in Hx. left; right; left; lia.
    + eapply rw_cells_agree_nw; [exact FTMP8|]. apply AG89. intros x Hx. cbn [cells_size csize Nat.add] in Hx. left; right; left; lia.
    + eapply rw_cells_agree_nw; [exact EL8|]. apply AG89. intros x Hx. cbn [cells_size csize Nat.add] in Hx. left; right; left; lia.
    + eapply rw_cells_agree_nw; [exact FB8|]. apply AG89. intros x Hx. cbn [cells_size csize Nat.add] in Hx. left; right; left; lia.
    + intros a Ha Ho. rewrite <- (PRES8' a Ha Ho). apply PRES9. apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; apply in_or_app; right; exact He| intros e He; exact He| lia].
Qed.
End Okarm.
