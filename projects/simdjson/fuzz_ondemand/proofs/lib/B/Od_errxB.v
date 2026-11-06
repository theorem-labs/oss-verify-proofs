(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_stage1_kit Sj_num_kit Atp_h_defs Od_kit.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Layout RT_iface RT_iface2 RT_anndefs D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps
  Sj_hkit Sj_hkit2 Sj_new Sj_num_akit Sj_num_amem Od_hbaseA Atp_h_defsA Od_defsB Od_hkit0A Od_deldtorA Od_lkitB Od_tailwB Od_bodyB
  Od_tailB Od_exitwB Od_exitB Od_errxwB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition xe_locals (F : Z) (fl c136 c368 : word) (j0 j144 j176 j256 j376 j432 : list byte) : list cell :=
  [CB 112 j0; C8 fl; C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 F); C8 c136; CB 24 j144;
   C8 (Z_to_bv 64 (F + 96)); CB 72 j176; C8 (Z_to_bv 64 (F / 8 + 2147450880)); CB 112 j256; C8 c368; CB 56 j376; CB 8 j432].

Section Errx.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis RTF : rt_contracts_f RT.
Hypothesis DELA : del_cps RT e_delarr.
Hypothesis DTOR : deldtor_cps RT.
Hypothesis VDES : vdestroy_cpsA RT.
Hypothesis AFV : forall Σ m, ART RT Σ m -> vt_dpi m.

Notation aevt := (aevt RT PMc).
Local Ltac ul := unfold ATPA_DESTROY_STACK, OD_NEED in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.

Lemma od_tail_sb : forall (Σ : rts RT) (K : config -> Prop) (usp S1 F lo IMPL idx oc ia nidx noc nia SB CAP A cap size : Z)
    (els : list (Z * Z)) (L0 : list (Z * Z))
    (cra cgp cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s8 s9 t3 t4 t5 t6 : word) FR fc (m : mem)
    (j0 j136 j256 j432 h0 l12 l13 l14 l15 l16 l17 l18 pre8 mid rest : list byte),
  S1 mod 32 = 0 -> usp - 560 <= S1 <= usp - 544 -> usp mod 16 = 0 -> usp + 16 <= USTACK_TOP ->
  rt_sp0 RT Σ - STACK_WIN <= lo -> lo + OD_NEED <= S1 -> frm0 fc ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo S1 ->
  rt_frames RT Σ = [(F, 3%nat)] ->
  rt_live RT Σ = (ia, nia) :: (oc, noc) :: (idx, nidx) :: (IMPL, 96) :: (SB, CAP) :: vblockA A cap size ++ L0 ->
  0 < nia -> 0 < noc -> 0 < nidx -> 0 < CAP -> (forall p n, In (p, n) L0 -> 0 < n) -> IMPL mod 8 = 0 ->
  rw_cells bsegs m S1 [CB 120 j0] ->
  rw_cells bsegs m (S1 + 120) [C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 F)] ->
  rw_cells bsegs m (S1 + 136) [CB 112 j136] ->
  rw_cells bsegs m (S1 + 248) [C8 (Z_to_bv 64 (F / 8 + 2147450880))] ->
  rw_cells bsegs m (S1 + 256) [CB 176 j256] ->
  rw_cells bsegs m (S1 + 432) [CB 8 j432] ->
  stk bsegs m (S1 + 440) (usp - 104) ->
  rw_cells bsegs m (usp - 104) (fa_saved cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11) ->
  rw_cells bsegs m F [CB 8 h0] ->
  rw_cells bsegs m (F + 104) [C8 (Z_to_bv 64 IMPL)] ->
  rw_cells bsegs m (F + 144) [C8 (Z_to_bv 64 SB)] ->
  vrepA m (F + 32) A cap size els -> 1 <= cap -> 1 <= size ->
  wr_at bsegs m (F / 8 + 2147450880) 64 ->
  rw_cells bsegs m (F / 8 + 2147450880 + 4) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m (F / 8 + 2147450880 + 12) [CB 1 l12; CB 1 l13; CB 1 l14; CB 1 l15; CB 1 l16; CB 1 l17; CB 1 l18] ->
  rw_cells bsegs m IMPL (dl_cells (Z_to_bv 64 OD_DPI_VPTR) pre8 (Z_to_bv 64 idx) mid (Z_to_bv 64 oc) (Z_to_bv 64 ia) rest) ->
  od_ret_k RT PMc K usp lo cra cgp cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 L0 (rt_sp0 RT Σ) (rt_credit RT Σ) m ->
  aevt Σ K (ex_regs 0x96ff0 ra S1 cgp (Z_to_bv 64 0x656e70) t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (F + 96)) s3 F s5 s6 s8 s9 t3 t4 t5 t6 FR fc m).
Proof using AF FDO MST RTF DELA DTOR VDES AFV.
  intros until rest.
  intros S32 S1R U16 UT LOW LOR FRM ART0 MI0 ST0 FRS LV NIA NOC NIDX NS0 LPOS IM8 LCa LCf LCb LC248 LCm LC4 STp FRs FH PIM PSB VR CAP1 SZ1 WRS SHv SHp DPI HK.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  assert (INF : In (F, 3%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  pose proof (af_frames_range RT AF Σ m F 3 ART0 INF) as (F0 & FR1 & _ & FLV).
  pose proof (af_frames_align RT AF Σ m F 3 ART0 INF) as (F64 & FSEG).
  pose proof (fframe_ranges RT AF Σ m F 3 ART0 INF) as (_ & _ & _ & SHB0 & SHT).
  pose proof (af_fshadow_apart RT AF Σ m F 3 ART0 INF) as (FSL & FSF). pose proof (FSF F 3%nat INF) as FSELF.
  change (fs_size 3) with 512 in *.
  assert (SHF : shad (F + 512) = shad F + 64) by (unfold shad; clear - F64; Z.div_mod_to_equations; lia).
  rewrite SHF in *. unfold shad, SHB in SHB0, SHT, FSELF, FSL.
  assert (INI : In (IMPL, 96) (rt_live RT Σ)) by (rewrite LV; do 3 right; left; reflexivity).
  assert (INS : In (SB, CAP) (rt_live RT Σ)) by (rewrite LV; do 4 right; left; reflexivity).
  pose proof (af_live_range RT AF Σ m SB CAP ART0 INS) as (SB0 & SB1 & _).
  pose proof (af_live_range RT AF Σ m IMPL 96 ART0 INI) as (IM0 & IM1 & _).
  pose proof (FLV IMPL 96 INI) as FIM. pose proof (FSL IMPL 96 INI) as SIM.
  assert (EU : bv_unsigned (Z_to_bv 64 S1) = S1) by (apply unsigned_lit; ul).
  assert (EUS : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; ul).
  assert (LPX : lposx (vblockA A cap size ++ L0)).
  { apply lposx_app; [| apply lposx_of_pos; exact LPOS]. unfold vblockA. destruct (cap =? 0) eqn:CZ; [apply Z.eqb_eq in CZ; lia|].
    apply lposx_ann_block. lia. }
  destruct (pos_prefix_facts RT AF Σ m [(ia, nia); (oc, noc); (idx, nidx); (IMPL, 96); (SB, CAP)] [] (vblockA A cap size ++ L0) ART0 LV
              ltac:(intros e [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [snd]; lia) LPX) as (ND5 & NDL).
  assert (N5 : ia <> SB /\ oc <> SB /\ idx <> SB /\ IMPL <> SB).
  { cbn [map fst] in ND5. apply NoDup_cons_iff in ND5. destruct ND5 as [X1 Y1]. apply NoDup_cons_iff in Y1. destruct Y1 as [X2 Y2].
    apply NoDup_cons_iff in Y2. destruct Y2 as [X3 Y3]. apply NoDup_cons_iff in Y3. destruct Y3 as [X4 Y4].
    cbn [In] in X1, X2, X3, X4. clear - X1 X2 X3 X4. repeat split; intros EQ; rewrite EQ in *; tauto. }
  destruct N5 as (NS1 & NS2 & NS3 & NS4).
  assert (LVR : live_remove SB (rt_live RT Σ) = (ia, nia) :: (oc, noc) :: (idx, nidx) :: (IMPL, 96) :: vblockA A cap size ++ L0).
  { rewrite LV. rewrite (live_remove_one SB CAP [(ia, nia); (oc, noc); (idx, nidx); (IMPL, 96)] [] (vblockA A cap size ++ L0));
      [reflexivity| intros e [<-|[<-|[<-|[<-|[]]]]]; cbn [fst]; assumption | intros e []
      | intros e He EQ; exact (NDL (SB, CAP) e ltac:(do 4 right; left; reflexivity) He (eq_sym EQ))]. }
  assert (L0IN : forall e, In e L0 -> In e (rt_live RT Σ)) by (intros e He; rewrite LV; do 5 right; apply in_or_app; right; exact He).
  assert (CALLER : forall x, aclient L0 [] usp x -> ~ (F <= x < F + 512)).
  { intros x [H|[H|[H|[H|H]]]].
    - clear - H FR1 LOW LOR S1R. ul.
    - pose proof (client_static_range x H) as CR. clear - CR FSEG. ul.
    - destruct H as (p & n & Hin & Hp). pose proof (FLV p n (L0IN _ Hin)) as D1. clear - Hp D1. lia.
    - destruct H as (f & k & [] & _).
    - destruct H as (f & k & [] & _). }
  destruct VR as (VSZ & VSC & VCAP & VA0 & VAT & VS & VB).
  destruct VB as [(B1 & B2)|(_ & A16 & APOS & VEL)]; [lia|].
  assert (INV : In (A, 16 * size) (vblockA A cap size)).
  { unfold vblockA. destruct (cap =? 0) eqn:CZ; [apply Z.eqb_eq in CZ; lia|]. apply ann_block_vis. }
  assert (INVL : In (A, 16 * size) (rt_live RT Σ)) by (rewrite LV; do 5 right; apply in_or_app; left; exact INV).
  pose proof (FLV A (16 * size) INVL) as FAV.
  pose proof (af_live_range RT AF Σ m A (16 * size) ART0 INVL) as (_ & AV1 & _).
  pose proof (velts_size els) as VSZE. unfold zlength in VSZ.
  assert (GS : F + 512 <= lo /\ F / 8 + 2147450880 + 64 <= lo /\ A + 16 * size <= lo /\ lo <= S1 /\ S1 + 544 <= usp /\ usp <= USTACK_TOP /\ SB + CAP <= lo /\ IMPL + 96 <= lo
               /\ 0x679000 <= lo /\ 0x679000 <= F)
    by (clear - FR1 LOW LOR SHT AV1 S1R UT SB1 IM1 SP0R SP0W FSEG F0 SB0 NS0; ul).
  unfold fa_saved, dl_cells in *.

  assert (FP1 : fp_ok RT Σ lo [(F + 144, F + 152)]).
  { apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; right; left. exists F, 3%nat. split; [exact INF|].
    change (fs_size 3) with 512. clear. lia. }
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { eapply (od_walkE3 usp S1 F SB ra cgp (Z_to_bv 64 0x656e70) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s8 s9 t3 t4 t5 t6 FR fc m);
      [clear - GS; lia| clear - GS; lia| clear - GS; ul| clear - GS; lia| clear - GS; lia| clear - SB0 NS0 GS; ul| exact PSB| exact MI0]. }
  cbv beta. intros ms1 (m1 & -> & MU1 & WM1 & MI1 & PSB1).
  apply evt_done.
  pose proof (art_of_munch RT AF Σ m m1 lo _ ART0 LOW FP1 MU1 WM1) as ART1.
  assert (AG1 : agree_on (fun x => ~ (F + 144 <= x < F + 152)) m m1)
    by (apply (agree_of_munch _ _ _ _ MU1); intros x Hx; cbn [outside]; split; [exact Hx| exact I]).
  assert (ST1 : stk bsegs m1 lo S1).
  { apply (stk_agree bsegs m m1 _ _ ST0); [| exact WM1]. eapply agree_sub; [exact AG1|]. intros x Hx. cbv beta in *. clear - Hx GS. lia. }
  assert (STp1 : stk bsegs m1 (S1 + 440) (usp - 104)).
  { apply (stk_agree bsegs m m1 _ _ STp); [| exact WM1]. eapply agree_sub; [exact AG1|]. intros x Hx. cbv beta in *. clear - Hx GS. lia. }
  clear ST0 STp PSB.
  rt_transport_with m m1 AG1 WM1 ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?VSZE in Hx; cbv beta;
      tl_dispatch Hx F A ltac:(first [clear - Hx GS; lia | clear - Hx FIM; lia]) ltac:(clear - Hx; lia) ltac:(clear - Hx FSELF; lia)
                         ltac:(clear - Hx FAV VSZ; lia)).
  assert (CP1 : forall a : word, aclient L0 [] usp (bv_unsigned a) -> m1 a = m a).
  { intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. pose proof (CALLER _ Ha) as N1. clear - N1. lia. }
  clear AG1 MU1 FP1 MI0 ART0.
  unfold ex_regs.
  eapply (aevt_delarr RT PMc FDO MST DELA Σ K) with (p := SB) (n := CAP) (lo := lo);
    [ exact INS | reflexivity | reflexivity | exact ART1 | exact MI1
    | unfold call_ok; rewrite EU; split; [exact ST1|]; split; [exact LOW|]; split; [clear - LOR; ul|]; split; [clear - GS; ul| clear - S32; Z.div_mod_to_equations; lia]
    | unfold unwind_ok; rewrite EU, EUS; right; right; clear - GS; lia | exact FRM | ].
  intros Σ2 v2 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 fc2 m2 FRM2 (ART2 & MI2 & ST2) PR2 LV2 FRS2 SP2 CR2.
  rewrite EU in ST2, PR2. rewrite LVR in LV2.
  assert (L0IN2 : forall e, In e L0 -> In e (rt_live RT Σ2)) by (intros e He; rewrite LV2; do 4 right; apply in_or_app; right; exact He).
  assert (INV2 : In (A, 16 * size) (rt_live RT Σ2)) by (rewrite LV2; do 4 right; apply in_or_app; left; exact INV).
  assert (INI2 : In (IMPL, 96) (rt_live RT Σ2)) by (rewrite LV2; do 3 right; left; reflexivity).
  assert (AG2 : agree_on (fun x => aclient (rt_live RT Σ2) (rt_frames RT Σ) S1 x) m1 m2) by (intros a Ha; exact (PR2 a Ha)).
  assert (CP2 : forall a : word, aclient L0 [] usp (bv_unsigned a) -> m2 a = m a).
  { intros a Ha. rewrite <- (CP1 a Ha). apply PR2. eapply aclient_mono; [exact Ha| exact L0IN2| intros e []| clear - GS; lia]. }
  clear CP1.
  assert (ACS2 : forall x, S1 <= x < USTACK_TOP -> aclient (rt_live RT Σ2) (rt_frames RT Σ) S1 x) by (intros x Hx; left; exact Hx).
  assert (ACF2 : forall x, F <= x < F + 504 -> aclient (rt_live RT Σ2) (rt_frames RT Σ) S1 x).
  { intros x Hx. right; right; right; left. exists F, 3%nat. split; [exact INF|]. change (fs_size 3) with 512. clear - Hx. lia. }
  assert (ACH2 : forall x, F / 8 + 2147450880 <= x < F / 8 + 2147450880 + 64 -> aclient (rt_live RT Σ2) (rt_frames RT Σ) S1 x).
  { intros x Hx. right; right; right; right. exists F, 3%nat. split; [exact INF|]. change (fs_size 3) with 512. rewrite SHF. unfold shad, SHB. clear - Hx. lia. }
  assert (ACV2 : forall x, A <= x < A + 16 * size -> aclient (rt_live RT Σ2) (rt_frames RT Σ) S1 x).
  { intros x Hx. right; right; left. exists A, (16 * size). split; [exact INV2| clear - Hx; lia]. }
  assert (ACI2 : forall x, IMPL <= x < IMPL + 96 -> aclient (rt_live RT Σ2) (rt_frames RT Σ) S1 x).
  { intros x Hx. right; right; left. exists IMPL, 96. split; [exact INI2| clear - Hx; lia]. }
  clear ST1 PSB1.
  rt_transport_nw m1 m2 AG2 ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?VSZE in Hx; cbv beta;
      tl_dispatch Hx F A ltac:(first [apply ACS2; clear - Hx GS; lia | apply ACI2; clear - Hx; lia]) ltac:(apply ACF2; clear - Hx; lia)
                         ltac:(apply ACH2; clear - Hx; lia) ltac:(apply ACV2; clear - Hx VSZ; lia)).
  replace (ret_pc (Z_to_bv 64 0x97000)) with (Z_to_bv 64 0x97000) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  clear AG2 PR2 ACS2 ACF2 ACH2 ACV2 ACI2 ART1 MI1 WM1.

  assert (INF2 : In (F, 3%nat) (rt_frames RT Σ2)) by (rewrite FRS2; exact INF).
  assert (LOW2 : rt_sp0 RT Σ2 - STACK_WIN <= lo) by (rewrite SP2; exact LOW).
  assert (FP3 : fp_ok RT Σ2 lo [(F + 104, F + 112)]).
  { apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; right; left. exists F, 3%nat. split; [exact INF2|].
    change (fs_size 3) with 512. clear. lia. }
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { eapply (od_walkE4 usp S1 F IMPL (Z_to_bv 64 0x97000) cgp (Z_to_bv 64 0x656e70) u0 u1 u2 v2 b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 (F + 96)) s3 s5 s6 s8 s9 u3 u4 u5 u6 F2 fc2 m2);
      [clear - GS; lia| clear - GS; lia| clear - GS; ul| clear - GS; lia| clear - GS; lia| clear - IM0 GS; ul| exact PIM| exact MI2]. }
  cbv beta. intros ms3 (m3 & -> & MU3 & WM3 & MI3 & PIM3).
  apply evt_done.
  pose proof (art_of_munch RT AF Σ2 m2 m3 lo _ ART2 LOW2 FP3 MU3 WM3) as ART3.
  assert (AG3 : agree_on (fun x => ~ (F + 104 <= x < F + 112)) m2 m3)
    by (apply (agree_of_munch _ _ _ _ MU3); intros x Hx; cbn [outside]; split; [exact Hx| exact I]).
  assert (ST3 : stk bsegs m3 lo S1).
  { apply (stk_agree bsegs m2 m3 _ _ ST2); [| exact WM3]. eapply agree_sub; [exact AG3|]. intros x Hx. cbv beta in *. clear - Hx GS. lia. }
  assert (STp3 : stk bsegs m3 (S1 + 440) (usp - 104)).
  { apply (stk_agree bsegs m2 m3 _ _ STp1); [| exact WM3]. eapply agree_sub; [exact AG3|]. intros x Hx. cbv beta in *. clear - Hx GS. lia. }
  clear ST2 STp1 PIM.
  rt_transport_with m2 m3 AG3 WM3 ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?VSZE in Hx; cbv beta;
      tl_dispatch Hx F A ltac:(first [clear - Hx GS; lia | clear - Hx FIM; lia]) ltac:(clear - Hx; lia) ltac:(clear - Hx FSELF; lia)
                         ltac:(clear - Hx FAV VSZ; lia)).
  assert (CP3 : forall a : word, aclient L0 [] usp (bv_unsigned a) -> m3 a = m a).
  { intros a Ha. rewrite <- (CP2 a Ha). apply MU3. cbn [outside]. split; [| exact I]. pose proof (CALLER _ Ha) as N1. clear - N1. lia. }
  clear CP2 AG3 MU3 FP3 MI2 ART2.
  assert (VR3 : vrepA m3 (F + 32) A cap size els).
  { unfold vrepA, zlength. split; [exact VSZ|]. split; [exact VSC|]. split; [exact VCAP|]. split; [exact VA0|]. split; [exact VAT|].
    split; [exact VS|]. right. split; [exact CAP1|]. split; [exact A16|]. split; [exact APOS| exact VEL]. }
  rewrite FRS in FRS2.
  eapply (od_tail RT AF PMc FDO MST RTF DTOR VDES AFV Σ2 K usp S1 F lo IMPL idx oc ia nidx noc nia A cap size els L0
            cra cgp cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11);
    [ exact S32 | exact S1R | exact U16 | exact UT | exact LOW2 | exact LOR | exact FRM2 | exact ART3 | exact MI3 | exact ST3
    | exact FRS2 | exact LV2 | exact NIA | exact NOC | exact NIDX | exact LPOS | exact IM8
    | exact LCa | exact LCf | exact LCb | exact LC248 | exact LCm | exact LC4 | exact STp3 | exact FRs | exact FH
    | exact VR3 | exact CAP1 | exact SZ1 | exact WRS | exact SHv | exact SHp | exact DPI | ].
  unfold od_ret_k in *. intros Σ' r0 r1 r2 q1 q2 q3 q4 q5 q6 q7 r3 r4 r5 r6 F' fc' m' FRM' ART' MI' ST' PR' LV' FRS' SP' CR'.
  apply HK; [exact FRM'| exact ART'| exact MI'| exact ST'| | exact LV'| exact FRS'| rewrite SP'; exact SP2| rewrite CR'; exact CR2].
  intros a Ha Ho. rewrite (PR' a Ha Ho). exact (CP3 a Ha).
Qed.

Lemma od_errx_core : forall (Σ : rts RT) (K : config -> Prop) (usp S1 F lo IMPL IDX OC IA NIDX SB CAP COPY NCOPY A cap size err fl : Z)
    (els : list (Z * Z)) (L0 LC : list (Z * Z))
    (cra cgp cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s8 s9 t3 t4 t5 t6 c136 c368 : word) FR fc (m : mem)
    (j0 j144 j176 j256 j376 j432 h0 jd pre8 mid rest : list byte),
  S1 mod 32 = 0 -> usp - 560 <= S1 <= usp - 544 -> usp mod 16 = 0 -> usp + 16 <= USTACK_TOP ->
  rt_sp0 RT Σ - STACK_WIN <= lo -> lo + OD_NEED <= S1 -> frm0 fc ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo S1 ->
  rt_frames RT Σ = [(F, 3%nat)] ->
  rt_live RT Σ = (IA, 1024) :: (OC, 8192) :: (IDX, NIDX) :: (IMPL, 96) :: (SB, CAP) :: LC ++ vblockA A cap size ++ L0 ->
  ((LC = [(COPY, NCOPY)] /\ 0 < NCOPY /\ fl = 0 /\ c136 = Z_to_bv 64 COPY) \/ (LC = [] /\ 0 < fl < 2^63)) ->
  0 < NIDX -> 0 < CAP -> (forall p n, In (p, n) L0 -> 0 < n) -> IMPL mod 8 = 0 ->
  rw_cells bsegs m S1 (xe_locals F (Z_to_bv 64 fl) c136 c368 j0 j144 j176 j256 j376 j432) ->
  stk bsegs m (S1 + 440) (usp - 104) ->
  rw_cells bsegs m (usp - 104) (fa_saved cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11) ->
  rw_cells bsegs m F [CB 8 h0] ->
  rw_cells bsegs m (F + 104) [C8 (Z_to_bv 64 IMPL)] ->
  rw_cells bsegs m (F + 144) [C8 (Z_to_bv 64 SB)] ->
  rw_cells bsegs m (F + 192) [CB 64 jd] ->
  vrepA m (F + 32) A cap size els -> 1 <= cap -> 1 <= size ->
  wr_at bsegs m (F / 8 + 2147450880) 64 ->
  rw_cells bsegs m (F / 8 + 2147450880 + 4) (map C1 (repeat (Z_to_bv 8 0) 3)) ->
  rw_cells bsegs m (F / 8 + 2147450880 + 12) (map C1 (repeat (Z_to_bv 8 0) 7)) ->
  rw_cells bsegs m (F / 8 + 2147450880 + 24) (map C1 (repeat (Z_to_bv 8 0) 8)) ->
  rw_cells bsegs m IMPL (dl_cells (Z_to_bv 64 OD_DPI_VPTR) pre8 (Z_to_bv 64 IDX) mid (Z_to_bv 64 OC) (Z_to_bv 64 IA) rest) ->
  0 < err < 64 ->
  od_ret_k RT PMc K usp lo cra cgp cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 L0 (rt_sp0 RT Σ) (rt_credit RT Σ) m ->
  aevt Σ K (ex_regs OD_ERRX ra S1 cgp (Z_to_bv 64 0x656e70) t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 err) s3 F s5 s6 s8 s9 t3 t4 t5 t6 FR fc m).
Proof using AF FDO MST RTF DELA DTOR VDES AFV.
  intros until rest.
  intros S32 S1R U16 UT LOW LOR FRM ART0 MI0 ST0 FRS LV HLC NIDX0 NS0 LPOS IM8 LOC STp FRs FH PIM PSB DOC VR CAP1 SZ1 WRS SHv SHp0 SHD DPI ERR HK.
  cbn [map repeat] in SHv, SHp0, SHD.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  assert (INF : In (F, 3%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  pose proof (af_frames_range RT AF Σ m F 3 ART0 INF) as (F0 & FR1 & _ & FLV).
  pose proof (af_frames_align RT AF Σ m F 3 ART0 INF) as (F64 & FSEG).
  pose proof (fframe_ranges RT AF Σ m F 3 ART0 INF) as (_ & _ & _ & SHB0 & SHT).
  pose proof (af_fshadow_apart RT AF Σ m F 3 ART0 INF) as (FSL & FSF). pose proof (FSF F 3%nat INF) as FSELF.
  change (fs_size 3) with 512 in *.
  assert (SHF : shad (F + 512) = shad F + 64) by (unfold shad; clear - F64; Z.div_mod_to_equations; lia).
  rewrite SHF in *. unfold shad, SHB in SHB0, SHT, FSELF, FSL.
  assert (INI : In (IMPL, 96) (rt_live RT Σ)) by (rewrite LV; do 3 right; left; reflexivity).
  assert (INS : In (SB, CAP) (rt_live RT Σ)) by (rewrite LV; do 4 right; left; reflexivity).
  pose proof (af_live_range RT AF Σ m SB CAP ART0 INS) as (SB0 & SB1 & _).
  pose proof (af_live_range RT AF Σ m IMPL 96 ART0 INI) as (IM0 & IM1 & _).
  pose proof (FLV IMPL 96 INI) as FIM. pose proof (FSL IMPL 96 INI) as SIM.
  assert (EU : bv_unsigned (Z_to_bv 64 S1) = S1) by (apply unsigned_lit; ul).
  assert (EUS : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; ul).
  assert (L0IN : forall e, In e L0 -> In e (rt_live RT Σ)).
  { intros e He. rewrite LV. do 5 right. apply in_or_app. right. apply in_or_app. right. exact He. }
  assert (CALLER : forall x, aclient L0 [] usp x ->
            ~ (F <= x < F + 512) /\ ~ (F / 8 + 2147450880 <= x < F / 8 + 2147450880 + 64) /\ ~ (lo <= x < usp)).
  { intros x [H|[H|[H|[H|H]]]].
    - clear - H FR1 SHT LOW LOR S1R. ul.
    - pose proof (client_static_range x H) as CR. clear - CR FSEG SHB0 SP0R LOW. ul.
    - destruct H as (p & n & Hin & Hp). pose proof (L0IN _ Hin) as HinL.
      pose proof (FLV p n HinL) as D1. pose proof (FSL p n HinL) as D2. pose proof (af_live_range RT AF Σ m p n ART0 HinL) as (_ & D3 & _).
      clear - Hp D1 D2 D3 LOW. lia.
    - destruct H as (f & k & [] & _).
    - destruct H as (f & k & [] & _). }

  destruct VR as (VSZ & VSC & VCAP & VA0 & VAT & VS & VB).
  destruct VB as [(B1 & B2)|(_ & A16 & APOS & VEL)]; [lia|].
  assert (INV : In (A, 16 * size) (vblockA A cap size)).
  { unfold vblockA. destruct (cap =? 0) eqn:CZ; [apply Z.eqb_eq in CZ; lia|]. apply ann_block_vis. }
  assert (INVL : In (A, 16 * size) (rt_live RT Σ)).
  { rewrite LV. do 5 right. apply in_or_app. right. apply in_or_app. left. exact INV. }
  pose proof (FLV A (16 * size) INVL) as FAV. pose proof (FSL A (16 * size) INVL) as SAV.
  pose proof (af_live_range RT AF Σ m A (16 * size) ART0 INVL) as (_ & AV1 & _).
  pose proof (velts_size els) as VSZE. unfold zlength in VSZ.
  assert (GS : F + 512 <= lo /\ F / 8 + 2147450880 + 64 <= lo /\ A + 16 * size <= lo /\ lo <= S1 /\ S1 + 544 <= usp /\ usp <= USTACK_TOP /\ SB + CAP <= lo /\ IMPL + 96 <= lo
               /\ 0x679000 <= lo /\ 0x679000 <= F)
    by (clear - FR1 LOW LOR SHT AV1 S1R UT SB1 IM1 SP0R SP0W FSEG F0 SB0 NS0; ul).

  unfold xe_locals, fa_saved, dl_cells in *.
  pose proof (rw_cells_pick 1 1 m _ (S1 + 112) _ LOC ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as C112.
  pose proof (rw_cells_pick 2 2 m _ (S1 + 120) _ LOC ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as LCf.
  pose proof (rw_cells_pick 4 1 m _ (S1 + 136) _ LOC ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as C136.
  pose proof (rw_cells_pick 6 1 m _ (S1 + 168) _ LOC ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as C168.
  pose proof (rw_cells_pick 8 1 m _ (S1 + 248) _ LOC ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as LC248.
  pose proof (rw_cells_pick 10 1 m _ (S1 + 368) _ LOC ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as C368.
  pose proof (rw_cells_pick 0 2 m _ S1 _ LOC ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as LCa.
  pose proof (rw_cells_pick 4 4 m _ (S1 + 136) _ LOC ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as LCb.
  pose proof (rw_cells_pick 9 3 m _ (S1 + 256) _ LOC ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as LCm.
  pose proof (rw_cells_pick 12 1 m _ (S1 + 432) _ LOC ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as LC4.
  cbn [firstn skipn] in C112, LCf, C136, C168, LC248, C368, LCa, LCb, LCm, LC4.
  destruct (rw_cells_junk m S1 _ 120%nat LCa eq_refl) as (ja & LCa'). clear LCa.
  destruct (rw_cells_junk m (S1 + 136) _ 112%nat LCb eq_refl) as (jb & LCb'). clear LCb.
  destruct (rw_cells_junk m (S1 + 256) _ 176%nat LCm eq_refl) as (jm & LCm'). clear LCm.
  assert (SHp : rw_cells bsegs m (F / 8 + 2147450880 + 12)
                  [CB 1 [Z_to_bv 8 0]; CB 1 [Z_to_bv 8 0]; CB 1 [Z_to_bv 8 0]; CB 1 [Z_to_bv 8 0]; CB 1 [Z_to_bv 8 0]; CB 1 [Z_to_bv 8 0]; CB 1 [Z_to_bv 8 0]]).
  { apply (rw_cells_recell bsegs m _ _ _ SHp0); [cbn [cells_wf cell_wf length]; repeat split; reflexivity| reflexivity| reflexivity]. }
  clear SHp0 LOC.
  pose proof (rw_cells_wr_at bsegs m (F + 192) _ 64 DOC ltac:(cbn; lia)) as DOCW.
  pose proof (wr_at_sub m (F + 192) 64 (F + 248) 4 DOCW ltac:(lia) ltac:(lia) ltac:(lia)) as DOCE.
  pose proof (wr_at_sub m (F + 192) 64 (F + 192) 49 DOCW ltac:(lia) ltac:(lia) ltac:(lia)) as DOCM.
  pose proof (rw_cells_bytes_at bsegs m _ _ SHD) as SHDB. cbn [cells_bytes cbytes app] in SHDB.
  clear DOC DOCW.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { eapply (od_walkE1 usp S1 F ra cgp (Z_to_bv 64 0x656e70) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 err) s3 s5 s6 s8 s9 t3 t4 t5 t6 FR fc m). exact MI0. }
  cbv beta. intros ms1 ->. apply evt_done.
  unfold ex_regs.
  assert (SHE : shad (F + 192) = F / 8 + 2147450880 + 24) by (unfold shad, SHB; clear - F64; Z.div_mod_to_equations; lia).
  eapply (aevt_memset RT RTF PMc FDO MST Σ K) with (d := F + 192) (n := 49) (cb := Z_to_bv 8 0) (lo := lo);
    [ reflexivity | reflexivity | reflexivity | clear - GS; ul | clear; lia
    | | exact ART0 | exact MI0
    | unfold call_ok; rewrite EU; split; [exact ST0|]; split; [exact LOW|]; split; [clear - LOR; ul|]; split; [clear - GS; ul| clear - S32; Z.div_mod_to_equations; lia]
    | exact FRM | ].
  { unfold checked_dst. rewrite EU. split; [| split; [| exact DOCM]].
    - intros _. split.
      + apply (acc_sub bsegs m (F + 192) (8 * Z.of_nat 8) (F + 192) 49); [| clear; lia| clear; lia].
        apply acc_zero_run; [clear - F64; Z.div_mod_to_equations; lia| clear - GS; lia|]. rewrite SHE. exact SHDB.
      + right; left. exists F, 3%nat. split; [exact INF|]. change (fs_size 3) with 512. clear. lia.
    - intros i Hi. right; right; right; left. exists F, 3%nat. split; [exact INF|]. change (fs_size 3) with 512. clear - Hi. lia. }
  intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F1 fc1 m1 FRM1 (ART1 & MI1 & WM1 & ST1) PR1 _.
  rewrite EU in ST1, PR1.
  assert (AG1 : agree_on (fun x => aclient (rt_live RT Σ) (rt_frames RT Σ) S1 x /\ ~ (F + 192 <= x < F + 192 + 49)) m m1)
    by (intros a [H1 H2]; exact (PR1 a H1 H2)).
  assert (ACS : forall x, S1 <= x < USTACK_TOP -> aclient (rt_live RT Σ) (rt_frames RT Σ) S1 x) by (intros x Hx; left; exact Hx).
  assert (ACF : forall x, F <= x < F + 504 -> aclient (rt_live RT Σ) (rt_frames RT Σ) S1 x).
  { intros x Hx. right; right; right; left. exists F, 3%nat. split; [exact INF|]. change (fs_size 3) with 512. clear - Hx. lia. }
  assert (ACH : forall x, F / 8 + 2147450880 <= x < F / 8 + 2147450880 + 64 -> aclient (rt_live RT Σ) (rt_frames RT Σ) S1 x).
  { intros x Hx. right; right; right; right. exists F, 3%nat. split; [exact INF|]. change (fs_size 3) with 512. rewrite SHF. unfold shad, SHB. clear - Hx. lia. }
  assert (ACV : forall x, A <= x < A + 16 * size -> aclient (rt_live RT Σ) (rt_frames RT Σ) S1 x).
  { intros x Hx. right; right; left. exists A, (16 * size). split; [exact INVL| clear - Hx; lia]. }
  assert (ACI : forall x, IMPL <= x < IMPL + 96 -> aclient (rt_live RT Σ) (rt_frames RT Σ) S1 x).
  { intros x Hx. right; right; left. exists IMPL, 96. split; [exact INI| clear - Hx; lia]. }
  assert (STp1 : stk bsegs m1 (S1 + 440) (usp - 104)).
  { apply (stk_agree bsegs m m1 _ _ STp); [| exact WM1]. eapply agree_sub; [exact AG1|]. intros x Hx. cbv beta in *.
    split; [apply ACS; clear - Hx GS; lia| clear - Hx GS; lia]. }
  clear STp ST0 SHDB DOCM.
  rt_transport_with m m1 AG1 WM1 ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?VSZE in Hx; cbv beta;
      tl_dispatch Hx F A ltac:(first [split; [apply ACS; clear - Hx GS; lia| clear - Hx GS; lia] | split; [apply ACI; clear - Hx; lia| clear - Hx FIM; lia]])
                         ltac:(split; [apply ACF; clear - Hx; lia| clear - Hx; lia])
                         ltac:(split; [apply ACH; clear - Hx; lia| clear - Hx FSELF; lia])
                         ltac:(split; [apply ACV; clear - Hx VSZ; lia| clear - Hx FAV VSZ; lia])).
  assert (CP1 : forall a : word, aclient L0 [] usp (bv_unsigned a) -> m1 a = m a).
  { intros a Ha. pose proof (CALLER _ Ha) as (N1 & _). apply PR1; [| clear - N1; lia].
    eapply aclient_mono; [exact Ha| exact L0IN| intros e []| clear - GS; lia]. }
  clear AG1 PR1 MI0.
  replace (ret_pc (Z_to_bv 64 0x97278)) with (Z_to_bv 64 0x97278) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  destruct (wr_at_rw_CB m1 (F + 248) 4 DOCE ltac:(lia)) as (je & DOCC). change (Z.to_nat 4) with 4%nat in DOCC. clear DOCE.

  assert (FP2 : fp_ok RT Σ lo [(F + 248, F + 252); (F / 8 + 2147450880 + 24, F / 8 + 2147450880 + 32)]).
  { apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn [fst snd].
    - right; right; left. exists F, 3%nat. split; [exact INF|]. change (fs_size 3) with 512. clear. lia.
    - right; right; right. exists F, 3%nat. split; [exact INF|]. change (fs_size 3) with 512. rewrite SHF. unfold shad, SHB. clear. lia. }
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { eapply (od_walkE2 usp S1 F err (Z_to_bv 64 0x97278) cgp (Z_to_bv 64 0x656e70) t0' t1' t2' (Z_to_bv 64 (F + 192)) a1' a2' a3' a4' a5' a6' a7' s3 s5 s6 s8 s9
              t3' t4' t5' t6' (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0)
              je c136 (Z_to_bv 64 fl) c368 F1 fc1 m1);
      [clear - GS; lia| clear - GS; lia| clear - GS; ul| clear - GS; lia| clear - GS; lia| clear - GS; lia| exact FSELF| exact ERR
      | exact DOCC| exact C168| exact C368| exact C136| exact C112| exact LC248| exact SHD| exact MI1]. }
  cbv beta. intros ms2 (m2 & -> & MU2 & WM2 & MI2 & SHD2). cbn [map repeat] in SHD2.
  apply evt_done.
  pose proof (art_of_munch RT AF Σ m1 m2 lo _ ART1 LOW FP2 MU2 WM2) as ART2.
  assert (AG2 : agree_on (fun x => ~ (F + 248 <= x < F + 252) /\ ~ (F / 8 + 2147450880 + 24 <= x < F / 8 + 2147450880 + 32)) m1 m2)
    by (apply (agree_of_munch _ _ _ _ MU2); intros x (H1 & H2); cbn [outside]; split; [exact H1| split; [exact H2| exact I]]).
  assert (ST2 : stk bsegs m2 lo S1).
  { apply (stk_agree bsegs m1 m2 _ _ ST1); [| exact WM2]. eapply agree_sub; [exact AG2|]. intros x Hx. cbv beta in *. clear - Hx GS. lia. }
  assert (STp2 : stk bsegs m2 (S1 + 440) (usp - 104)).
  { apply (stk_agree bsegs m1 m2 _ _ STp1); [| exact WM2]. eapply agree_sub; [exact AG2|]. intros x Hx. cbv beta in *. clear - Hx GS. lia. }
  clear ST1 STp1 DOCC C168 C368 C136 C112 SHD.
  rt_transport_with m1 m2 AG2 WM2 ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?VSZE in Hx; cbv beta;
      tl_dispatch Hx F A ltac:(first [clear - Hx GS; lia | clear - Hx GS FIM SIM; lia]) ltac:(clear - Hx GS FSELF; lia) ltac:(clear - Hx GS FSELF; lia)
                         ltac:(clear - Hx GS FAV SAV VSZ; lia)).
  assert (CP2 : forall a : word, aclient L0 [] usp (bv_unsigned a) -> m2 a = m a).
  { intros a Ha. rewrite <- (CP1 a Ha). apply MU2. cbn [outside]. pose proof (CALLER _ Ha) as (N1 & N2 & N3). clear - N1 N2 N3 GS. lia. }
  clear CP1 AG2 MU2 FP2 MI1 ART1 WM1 WM2.

  assert (HR : forall (mT : mem) sp0 cr, sp0 = rt_sp0 RT Σ -> cr = rt_credit RT Σ ->
            (forall a : word, aclient L0 [] usp (bv_unsigned a) -> mT a = m a) ->
            od_ret_k RT PMc K usp lo cra cgp cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 L0 sp0 cr mT).
  { intros mT sp0 cr -> -> CPT. unfold od_ret_k in *.
    intros Σ' r0 r1 r2 q1 q2 q3 q4 q5 q6 q7 r3 r4 r5 r6 F' fc' m' FRM' ART' MI' ST' PR' LV' FRS' SP' CR'.
    apply HK; [exact FRM'| exact ART'| exact MI'| exact ST'| | exact LV'| exact FRS'| exact SP'| exact CR'].
    intros a Ha Ho. rewrite (PR' a Ha Ho). exact (CPT a Ha). }
  clear HK.
  destruct HLC as [(-> & NC0 & -> & ->)|(-> & FL0)]; cbn [app] in LV.
  -
    assert (LPX : lposx (vblockA A cap size ++ L0)).
    { apply lposx_app; [| apply lposx_of_pos; exact LPOS]. unfold vblockA. destruct (cap =? 0) eqn:CZ; [apply Z.eqb_eq in CZ; lia|].
      apply lposx_ann_block. lia. }
    destruct (pos_prefix_facts RT AF Σ m2 [(IA, 1024); (OC, 8192); (IDX, NIDX); (IMPL, 96); (SB, CAP); (COPY, NCOPY)] []
                (vblockA A cap size ++ L0) ART2 LV
                ltac:(intros e [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [snd]; lia) LPX) as (ND6 & NDL).
    assert (N6 : IA <> COPY /\ OC <> COPY /\ IDX <> COPY /\ IMPL <> COPY /\ SB <> COPY).
    { cbn [map fst] in ND6. apply NoDup_cons_iff in ND6. destruct ND6 as [X1 Y1]. apply NoDup_cons_iff in Y1. destruct Y1 as [X2 Y2].
      apply NoDup_cons_iff in Y2. destruct Y2 as [X3 Y3]. apply NoDup_cons_iff in Y3. destruct Y3 as [X4 Y4].
      apply NoDup_cons_iff in Y4. destruct Y4 as [X5 Y5].
      cbn [In] in X1, X2, X3, X4, X5. clear - X1 X2 X3 X4 X5. repeat split; intros EQ; rewrite EQ in *; tauto. }
    destruct N6 as (NC1 & NC2 & NC3 & NC4 & NC5).
    assert (LVR1 : live_remove COPY (rt_live RT Σ)
                   = (IA, 1024) :: (OC, 8192) :: (IDX, NIDX) :: (IMPL, 96) :: (SB, CAP) :: vblockA A cap size ++ L0).
    { rewrite LV.
      rewrite (live_remove_one COPY NCOPY [(IA, 1024); (OC, 8192); (IDX, NIDX); (IMPL, 96); (SB, CAP)] [] (vblockA A cap size ++ L0));
        [reflexivity| intros e [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst]; assumption | intros e []
        | intros e He EQ; exact (NDL (COPY, NCOPY) e ltac:(do 5 right; left; reflexivity) He (eq_sym EQ))]. }
    assert (INC : In (COPY, NCOPY) (rt_live RT Σ)) by (rewrite LV; do 5 right; left; reflexivity).
    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut.
    { eapply (od_walkE2c usp S1 F COPY (Z_to_bv 64 0x97278) cgp (Z_to_bv 64 0x656e70) t0' t1' t2' (Z_to_bv 64 (-8)) a3' a4' c368 a6' a7'
                (Z_to_bv 64 (F + 96)) s3 s5 s6 s8 s9 t3' t4' t5' t6' F1 fc1 m2). exact MI2. }
    cbv beta. intros ms3 ->. apply evt_done.
    unfold ex_regs.
    eapply (aevt_delarr RT PMc FDO MST DELA Σ K) with (p := COPY) (n := NCOPY) (lo := lo);
      [ exact INC | reflexivity | reflexivity | exact ART2 | exact MI2
      | unfold call_ok; rewrite EU; split; [exact ST2|]; split; [exact LOW|]; split; [clear - LOR; ul|]; split; [clear - GS; ul| clear - S32; Z.div_mod_to_equations; lia]
      | unfold unwind_ok; rewrite EU, EUS; right; right; clear - GS; lia | exact FRM1 | ].
    intros Σ3 v3 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F3 fc3 m3 FRM3 (ART3 & MI3 & ST3) PR3 LV3 FRS3 SP3 CR3.
    rewrite EU in ST3, PR3. rewrite LVR1 in LV3. rewrite FRS in FRS3.
    assert (L0IN3 : forall e, In e L0 -> In e (rt_live RT Σ3)) by (intros e He; rewrite LV3; do 5 right; apply in_or_app; right; exact He).
    assert (INV3 : In (A, 16 * size) (rt_live RT Σ3)) by (rewrite LV3; do 5 right; apply in_or_app; left; exact INV).
    assert (INI3 : In (IMPL, 96) (rt_live RT Σ3)) by (rewrite LV3; do 3 right; left; reflexivity).
    assert (AG3 : agree_on (fun x => aclient (rt_live RT Σ3) (rt_frames RT Σ) S1 x) m2 m3) by (intros a Ha; exact (PR3 a Ha)).
    assert (CP3 : forall a : word, aclient L0 [] usp (bv_unsigned a) -> m3 a = m a).
    { intros a Ha. rewrite <- (CP2 a Ha). apply PR3. eapply aclient_mono; [exact Ha| exact L0IN3| intros e []| clear - GS; lia]. }
    clear CP2.
    assert (ACS3 : forall x, S1 <= x < USTACK_TOP -> aclient (rt_live RT Σ3) (rt_frames RT Σ) S1 x) by (intros x Hx; left; exact Hx).
    assert (ACF3 : forall x, F <= x < F + 504 -> aclient (rt_live RT Σ3) (rt_frames RT Σ) S1 x).
    { intros x Hx. right; right; right; left. exists F, 3%nat. split; [exact INF|]. change (fs_size 3) with 512. clear - Hx. lia. }
    assert (ACH3 : forall x, F / 8 + 2147450880 <= x < F / 8 + 2147450880 + 64 -> aclient (rt_live RT Σ3) (rt_frames RT Σ) S1 x).
    { intros x Hx. right; right; right; right. exists F, 3%nat. split; [exact INF|]. change (fs_size 3) with 512. rewrite SHF. unfold shad, SHB. clear - Hx. lia. }
    assert (ACV3 : forall x, A <= x < A + 16 * size -> aclient (rt_live RT Σ3) (rt_frames RT Σ) S1 x).
    { intros x Hx. right; right; left. exists A, (16 * size). split; [exact INV3| clear - Hx; lia]. }
    assert (ACI3 : forall x, IMPL <= x < IMPL + 96 -> aclient (rt_live RT Σ3) (rt_frames RT Σ) S1 x).
    { intros x Hx. right; right; left. exists IMPL, 96. split; [exact INI3| clear - Hx; lia]. }
    clear ST2.
    rt_transport_nw m2 m3 AG3 ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?VSZE in Hx; cbv beta;
        tl_dispatch Hx F A ltac:(first [apply ACS3; clear - Hx GS; lia | apply ACI3; clear - Hx; lia]) ltac:(apply ACF3; clear - Hx; lia)
                           ltac:(apply ACH3; clear - Hx; lia) ltac:(apply ACV3; clear - Hx VSZ; lia)).
    replace (ret_pc (Z_to_bv 64 0x96ff0)) with (Z_to_bv 64 0x96ff0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (VR3 : vrepA m3 (F + 32) A cap size els).
    { unfold vrepA, zlength. split; [exact VSZ|]. split; [exact VSC|]. split; [exact VCAP|]. split; [exact VA0|]. split; [exact VAT|].
      split; [exact VS|]. right. split; [exact CAP1|]. split; [exact A16|]. split; [exact APOS| exact VEL]. }
    assert (LOW3 : rt_sp0 RT Σ3 - STACK_WIN <= lo) by (rewrite SP3; exact LOW).
    eapply (od_tail_sb Σ3 K usp S1 F lo IMPL IDX OC IA NIDX 8192 1024 SB CAP A cap size els L0
              cra cgp cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11);
      [ exact S32 | exact S1R | exact U16 | exact UT | exact LOW3 | exact LOR | exact FRM3 | exact ART3 | exact MI3 | exact ST3
      | exact FRS3 | exact LV3 | clear; lia | clear; lia | exact NIDX0 | exact NS0 | exact LPOS | exact IM8
      | exact LCa' | exact LCf | exact LCb' | exact LC248 | exact LCm' | exact LC4 | exact STp2 | exact FRs | exact FH | exact PIM | exact PSB
      | exact VR3 | exact CAP1 | exact SZ1 | exact WRS | exact SHv | exact SHp | exact DPI
      | exact (HR m3 _ _ SP3 CR3 CP3) ].
  -
    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut.
    { eapply (od_walkE2n usp S1 F fl (Z_to_bv 64 0x97278) cgp (Z_to_bv 64 0x656e70) t0' t1' t2' c136 (Z_to_bv 64 (-8)) a3' a4' c368 a6' a7'
                (Z_to_bv 64 (F + 96)) s3 s5 s6 s8 s9 t3' t4' t5' t6' F1 fc1 m2); [exact FL0| exact MI2]. }
    cbv beta. intros ms3 ->. apply evt_done.
    assert (VR2 : vrepA m2 (F + 32) A cap size els).
    { unfold vrepA, zlength. split; [exact VSZ|]. split; [exact VSC|]. split; [exact VCAP|]. split; [exact VA0|]. split; [exact VAT|].
      split; [exact VS|]. right. split; [exact CAP1|]. split; [exact A16|]. split; [exact APOS| exact VEL]. }
    eapply (od_tail_sb Σ K usp S1 F lo IMPL IDX OC IA NIDX 8192 1024 SB CAP A cap size els L0
              cra cgp cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11);
      [ exact S32 | exact S1R | exact U16 | exact UT | exact LOW | exact LOR | exact FRM1 | exact ART2 | exact MI2 | exact ST2
      | exact FRS | exact LV | clear; lia | clear; lia | exact NIDX0 | exact NS0 | exact LPOS | exact IM8
      | exact LCa' | exact LCf | exact LCb' | exact LC248 | exact LCm' | exact LC4 | exact STp2 | exact FRs | exact FH | exact PIM | exact PSB
      | exact VR2 | exact CAP1 | exact SZ1 | exact WRS | exact SHv | exact SHp | exact DPI
      | exact (HR m2 _ _ eq_refl eq_refl CP2) ].
Qed.

End Errx.
