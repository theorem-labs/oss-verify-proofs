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
  Od_tailB Od_exitwB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma rw_cells_pick : forall (n k : nat) (m : mem) A B cs, rw_cells bsegs m A cs ->
  B = A + Z.of_nat (cells_size (firstn n cs)) -> rw_cells bsegs m B (firstn k (skipn n cs)).
Proof.
  intros n k m A B cs H ->. rewrite <- (firstn_skipn n cs) in H at 1. apply Sj_stage1_kit.rw_cells_app in H. destruct H as [_ H].
  rewrite <- (firstn_skipn k (skipn n cs)) in H at 1. apply Sj_stage1_kit.rw_cells_app in H. exact (proj1 H).
Qed.

Ltac readdr_ass :=
  match goal with H : rw_cells _ ?m ?b _ |- rw_cells _ ?m ?a _ => replace a with b by (clear; lia); exact H end.
Ltac join_cells :=
  lazymatch goal with
  | |- rw_cells _ _ _ (_ ++ _) => apply Sj_stage1_kit.rw_cells_app; split; [readdr_ass| cbn [cells_size csize Nat.add]; join_cells]
  | |- rw_cells _ _ _ _ => readdr_ass
  end.

Lemma rw_cells_junk : forall (m : mem) A cs (n : nat), rw_cells bsegs m A cs -> cells_size cs = n ->
  exists j, rw_cells bsegs m A [CB n j].
Proof.
  intros m A cs n H <-. pose proof (rw_cells_wr_at bsegs m A cs _ H (Z.le_refl _)) as W.
  destruct (wr_at_rw_CB m A _ W ltac:(lia)) as (j & Hj). rewrite Nat2Z.id in Hj. exists j. exact Hj.
Qed.

Definition xl_locals (F COPY : Z) (j0 j80 j144 j176 j256 j432 : list byte) : list cell :=
  [CB 72 j0; C8 (Z_to_bv 64 (F + 104)); CB 32 j80; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 COPY); CB 24 j144;
   C8 (Z_to_bv 64 (F + 96)); CB 72 j176; C8 (Z_to_bv 64 (F / 8 + 2147450880)); CB 176 j256; CB 8 j432].

Section Exit.
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

Lemma od_exit_core : forall (Σ : rts RT) (K : config -> Prop) (usp S1 F lo IMPL IDX OC IA NIDX SB CAP COPY NCOPY A cap size : Z)
    (els : list (Z * Z)) (L0 : list (Z * Z))
    (cra cgp cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s11 t3 t4 t5 t6 : word) FR fc (m : mem)
    (j0 j80 j144 j176 j256 j432 h0 pre8 mid rest : list byte),
  S1 mod 32 = 0 -> usp - 560 <= S1 <= usp - 544 -> usp mod 16 = 0 -> usp + 16 <= USTACK_TOP ->
  rt_sp0 RT Σ - STACK_WIN <= lo -> lo + OD_NEED <= S1 -> frm0 fc ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo S1 ->
  rt_frames RT Σ = [(F, 3%nat)] ->
  rt_live RT Σ = (IA, 1024) :: (OC, 8192) :: (IDX, NIDX) :: (IMPL, 96) :: (SB, CAP) :: (COPY, NCOPY) :: vblockA A cap size ++ L0 ->
  0 < NIDX -> 0 < CAP -> 0 < NCOPY -> (forall p n, In (p, n) L0 -> 0 < n) -> IMPL mod 8 = 0 ->
  rw_cells bsegs m S1 (xl_locals F COPY j0 j80 j144 j176 j256 j432) ->
  stk bsegs m (S1 + 440) (usp - 104) ->
  rw_cells bsegs m (usp - 104) (fa_saved cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11) ->
  rw_cells bsegs m F [CB 8 h0] ->
  rw_cells bsegs m (F + 104) [C8 (Z_to_bv 64 IMPL)] ->
  rw_cells bsegs m (F + 144) [C8 (Z_to_bv 64 SB)] ->
  vrepA m (F + 32) A cap size els -> 1 <= cap -> 1 <= size ->
  wr_at bsegs m (F / 8 + 2147450880) 64 ->
  rw_cells bsegs m (F / 8 + 2147450880 + 4) (map C1 (repeat (Z_to_bv 8 0) 3)) ->
  rw_cells bsegs m (F / 8 + 2147450880 + 12) (map C1 (repeat (Z_to_bv 8 0) 7)) ->
  rw_cells bsegs m (F / 8 + 2147450880 + 24) (map C1 (repeat (Z_to_bv 8 0) 8)) ->
  rw_cells bsegs m IMPL (dl_cells (Z_to_bv 64 OD_DPI_VPTR) pre8 (Z_to_bv 64 IDX) mid (Z_to_bv 64 OC) (Z_to_bv 64 IA) rest) ->
  od_ret_k RT PMc K usp lo cra cgp cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 L0 (rt_sp0 RT Σ) (rt_credit RT Σ) m ->
  aevt Σ K (tx_regs OD_EXIT ra S1 cgp (Z_to_bv 64 0x656e70) t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 F s11 t3 t4 t5 t6 FR fc m).
Proof using AF FDO MST RTF DELA DTOR VDES AFV.
  intros until rest.
  intros S32 S1R U16 UT LOW LOR FRM ART0 MI0 ST0 FRS LV NIDX0 NS0 NC0 LPOS IM8 LOC STp FRs FH PIM PSB VR CAP1 SZ1 WRS SHv SHp0 SHD DPI HK.
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
  assert (INC : In (COPY, NCOPY) (rt_live RT Σ)) by (rewrite LV; do 5 right; left; reflexivity).
  pose proof (af_live_range RT AF Σ m SB CAP ART0 INS) as (SB0 & SB1 & _).
  pose proof (af_live_range RT AF Σ m COPY NCOPY ART0 INC) as (CP0 & CP1 & _).
  pose proof (af_live_range RT AF Σ m IMPL 96 ART0 INI) as (IM0 & IM1 & _).
  pose proof (FLV IMPL 96 INI) as FIM. pose proof (FSL IMPL 96 INI) as SIM.
  assert (EU : bv_unsigned (Z_to_bv 64 S1) = S1) by (apply unsigned_lit; ul).
  assert (EUS : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; ul).

  assert (LPX : lposx (vblockA A cap size ++ L0)).
  { apply lposx_app; [| apply lposx_of_pos; exact LPOS]. unfold vblockA. destruct (cap =? 0) eqn:CZ; [apply Z.eqb_eq in CZ; lia|].
    apply lposx_ann_block. lia. }
  destruct (pos_prefix_facts RT AF Σ m [(IA, 1024); (OC, 8192); (IDX, NIDX); (IMPL, 96); (SB, CAP); (COPY, NCOPY)] []
              (vblockA A cap size ++ L0) ART0 LV
              ltac:(intros e [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [snd]; lia) LPX) as (ND6 & NDL).
  assert (N6 : (IA <> SB /\ OC <> SB /\ IDX <> SB /\ IMPL <> SB) /\ (IA <> COPY /\ OC <> COPY /\ IDX <> COPY /\ IMPL <> COPY /\ SB <> COPY)).
  { cbn [map fst] in ND6. apply NoDup_cons_iff in ND6. destruct ND6 as [X1 Y1]. apply NoDup_cons_iff in Y1. destruct Y1 as [X2 Y2].
    apply NoDup_cons_iff in Y2. destruct Y2 as [X3 Y3]. apply NoDup_cons_iff in Y3. destruct Y3 as [X4 Y4].
    apply NoDup_cons_iff in Y4. destruct Y4 as [X5 Y5].
    cbn [In] in X1, X2, X3, X4, X5. clear - X1 X2 X3 X4 X5. repeat split; intros EQ; rewrite EQ in *; tauto. }
  destruct N6 as ((NS1 & NS2 & NS3 & NS4) & (NC1 & NC2 & NC3 & NC4 & NC5)).
  assert (LVR1 : live_remove COPY (rt_live RT Σ)
                 = (IA, 1024) :: (OC, 8192) :: (IDX, NIDX) :: (IMPL, 96) :: (SB, CAP) :: vblockA A cap size ++ L0).
  { rewrite LV.
    rewrite (live_remove_one COPY NCOPY [(IA, 1024); (OC, 8192); (IDX, NIDX); (IMPL, 96); (SB, CAP)] [] (vblockA A cap size ++ L0));
      [reflexivity| intros e [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst]; assumption | intros e []
      | intros e He EQ; exact (NDL (COPY, NCOPY) e ltac:(do 5 right; left; reflexivity) He (eq_sym EQ))]. }
  assert (LVR2 : live_remove SB ((IA, 1024) :: (OC, 8192) :: (IDX, NIDX) :: (IMPL, 96) :: (SB, CAP) :: vblockA A cap size ++ L0)
                 = (IA, 1024) :: (OC, 8192) :: (IDX, NIDX) :: (IMPL, 96) :: vblockA A cap size ++ L0).
  { rewrite (live_remove_one SB CAP [(IA, 1024); (OC, 8192); (IDX, NIDX); (IMPL, 96)] [] (vblockA A cap size ++ L0));
      [reflexivity| intros e [<-|[<-|[<-|[<-|[]]]]]; cbn [fst]; assumption | intros e []
      | intros e He EQ; exact (NDL (SB, CAP) e ltac:(do 4 right; left; reflexivity) He (eq_sym EQ))]. }
  assert (L0IN : forall e, In e L0 -> In e (rt_live RT Σ)) by (intros e He; rewrite LV; do 6 right; apply in_or_app; right; exact He).
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
  assert (INVL : In (A, 16 * size) (rt_live RT Σ)) by (rewrite LV; do 6 right; apply in_or_app; left; exact INV).
  pose proof (FLV A (16 * size) INVL) as FAV. pose proof (FSL A (16 * size) INVL) as SAV.
  pose proof (af_live_range RT AF Σ m A (16 * size) ART0 INVL) as (_ & AV1 & _).
  pose proof (velts_size els) as VSZE. unfold zlength in VSZ.
  assert (GS : F + 512 <= lo /\ F / 8 + 2147450880 + 64 <= lo /\ A + 16 * size <= lo /\ lo <= S1 /\ S1 + 544 <= usp /\ usp <= USTACK_TOP /\ SB + CAP <= lo /\ IMPL + 96 <= lo
               /\ 0x679000 <= lo /\ 0x679000 <= F /\ COPY + NCOPY <= lo)
    by (clear - FR1 LOW LOR SHT AV1 S1R UT SB1 IM1 CP1 SP0R SP0W FSEG F0 SB0 NS0; ul).

  unfold xl_locals, fa_saved, dl_cells in *.
  pose proof (rw_cells_pick 1 1 m _ (S1 + 72) _ LOC ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as C72.
  pose proof (rw_cells_pick 3 1 m _ (S1 + 112) _ LOC ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as C112.
  pose proof (rw_cells_pick 4 2 m _ (S1 + 120) _ LOC ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as LCf.
  pose proof (rw_cells_pick 6 1 m _ (S1 + 136) _ LOC ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as C136.
  pose proof (rw_cells_pick 8 1 m _ (S1 + 168) _ LOC ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as C168.
  pose proof (rw_cells_pick 10 1 m _ (S1 + 248) _ LOC ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as LC248.
  pose proof (rw_cells_pick 0 4 m _ S1 _ LOC ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as LCa.
  pose proof (rw_cells_pick 6 4 m _ (S1 + 136) _ LOC ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as LCb.
  pose proof (rw_cells_pick 11 1 m _ (S1 + 256) _ LOC ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as LCm.
  pose proof (rw_cells_pick 12 1 m _ (S1 + 432) _ LOC ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as LC4.
  cbn [firstn skipn] in C72, C112, LCf, C136, C168, LC248, LCa, LCb, LCm, LC4.
  destruct (rw_cells_junk m S1 _ 120%nat LCa eq_refl) as (ja & LCa'). clear LCa.
  destruct (rw_cells_junk m (S1 + 136) _ 112%nat LCb eq_refl) as (jb & LCb'). clear LCb.
  assert (SHp : rw_cells bsegs m (F / 8 + 2147450880 + 12)
                  [CB 1 [Z_to_bv 8 0]; CB 1 [Z_to_bv 8 0]; CB 1 [Z_to_bv 8 0]; CB 1 [Z_to_bv 8 0]; CB 1 [Z_to_bv 8 0]; CB 1 [Z_to_bv 8 0]; CB 1 [Z_to_bv 8 0]]).
  { apply (rw_cells_recell bsegs m _ _ _ SHp0); [cbn [cells_wf cell_wf length]; repeat split; reflexivity| reflexivity| reflexivity]. }
  clear SHp0 LOC.

  assert (FP1 : fp_ok RT Σ lo [(F / 8 + 2147450880 + 24, F / 8 + 2147450880 + 32)]).
  { apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; right; right. exists F, 3%nat. split; [exact INF|].
    change (fs_size 3) with 512. rewrite SHF. unfold shad, SHB. clear. lia. }
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { eapply (od_walkX1 usp S1 F COPY ra cgp (Z_to_bv 64 0x656e70) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s11 t3 t4 t5 t6
              (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) FR fc m);
      [clear - GS; lia| clear - GS; lia| clear - GS; ul| clear - GS; lia| clear - GS; lia| clear - CP0 NC0 GS; ul| exact LC248| exact C112| exact C136| exact SHD| exact MI0]. }
  cbv beta. intros ms2 (m2 & -> & MU2 & WM2 & MI2 & SHD2). cbn [map repeat] in SHD2.
  apply evt_done.
  pose proof (art_of_munch RT AF Σ m m2 lo _ ART0 LOW FP1 MU2 WM2) as ART2.
  assert (AG2 : agree_on (fun x => ~ (F / 8 + 2147450880 + 24 <= x < F / 8 + 2147450880 + 32)) m m2)
    by (apply (agree_of_munch _ _ _ _ MU2); intros x Hx; cbn [outside]; split; [exact Hx| exact I]).
  assert (ST2 : stk bsegs m2 lo S1).
  { apply (stk_agree bsegs m m2 _ _ ST0); [| exact WM2]. eapply agree_sub; [exact AG2|]. intros x Hx. cbv beta in *. clear - Hx GS. lia. }
  assert (STp2 : stk bsegs m2 (S1 + 440) (usp - 104)).
  { apply (stk_agree bsegs m m2 _ _ STp); [| exact WM2]. eapply agree_sub; [exact AG2|]. intros x Hx. cbv beta in *. clear - Hx GS. lia. }
  clear ST0 STp SHD C112 C136.
  rt_transport_with m m2 AG2 WM2 ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?VSZE in Hx; cbv beta;
      tl_dispatch Hx F A ltac:(first [clear - Hx GS; lia | clear - Hx SIM; lia]) ltac:(clear - Hx FSELF; lia) ltac:(clear - Hx; lia)
                         ltac:(clear - Hx SAV VSZ; lia)).
  assert (CP2 : forall a : word, aclient L0 [] usp (bv_unsigned a) -> m2 a = m a).
  { intros a Ha. apply MU2. cbn [outside]. split; [| exact I]. pose proof (CALLER _ Ha) as (_ & N2 & _). clear - N2. lia. }
  clear AG2 MU2 FP1 MI0 ART0.
  unfold tx_regs.
  eapply (aevt_delarr RT PMc FDO MST DELA Σ K) with (p := COPY) (n := NCOPY) (lo := lo);
    [ exact INC | reflexivity | reflexivity | exact ART2 | exact MI2
    | unfold call_ok; rewrite EU; split; [exact ST2|]; split; [exact LOW|]; split; [clear - LOR; ul|]; split; [clear - GS; ul| clear - S32; Z.div_mod_to_equations; lia]
    | unfold unwind_ok; rewrite EU, EUS; right; right; clear - GS; lia | exact FRM | ].
  intros Σ3 v3 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F3 fc3 m3 FRM3 (ART3 & MI3 & ST3) PR3 LV3 FRS3 SP3 CR3.
  rewrite EU in ST3, PR3. rewrite LVR1 in LV3.
  assert (L0IN3 : forall e, In e L0 -> In e (rt_live RT Σ3)) by (intros e He; rewrite LV3; do 5 right; apply in_or_app; right; exact He).
  assert (INV3 : In (A, 16 * size) (rt_live RT Σ3)) by (rewrite LV3; do 5 right; apply in_or_app; left; exact INV).
  assert (INI3 : In (IMPL, 96) (rt_live RT Σ3)) by (rewrite LV3; do 3 right; left; reflexivity).
  assert (INS3 : In (SB, CAP) (rt_live RT Σ3)) by (rewrite LV3; do 4 right; left; reflexivity).
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
  replace (ret_pc (Z_to_bv 64 0x9b9b0)) with (Z_to_bv 64 0x9b9b0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  clear AG3 PR3 ACS3 ACF3 ACH3 ACV3 ACI3 ART2 MI2 WM2.

  assert (INF3 : In (F, 3%nat) (rt_frames RT Σ3)) by (rewrite FRS3; exact INF).
  assert (LOW3 : rt_sp0 RT Σ3 - STACK_WIN <= lo) by (rewrite SP3; exact LOW).
  assert (FP3 : fp_ok RT Σ3 lo [(F + 144, F + 152)]).
  { apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; right; left. exists F, 3%nat. split; [exact INF3|].
    change (fs_size 3) with 512. clear. lia. }
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { eapply (od_walkX2 usp S1 F SB (Z_to_bv 64 0x9b9b0) cgp (Z_to_bv 64 0x656e70) t0' t1' t2' v3 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s8 s9 s11 t3' t4' t5' t6' F3 fc3 m3);
      [clear - GS; lia| clear - GS; lia| clear - GS; ul| clear - GS; lia| clear - GS; lia| clear - SB0 NS0 GS; ul| exact C168| exact C72| exact PSB| exact MI3]. }
  cbv beta. intros ms4 (m4 & -> & MU4 & WM4 & MI4 & PSB4).
  apply evt_done.
  pose proof (art_of_munch RT AF Σ3 m3 m4 lo _ ART3 LOW3 FP3 MU4 WM4) as ART4.
  assert (AG4 : agree_on (fun x => ~ (F + 144 <= x < F + 152)) m3 m4)
    by (apply (agree_of_munch _ _ _ _ MU4); intros x Hx; cbn [outside]; split; [exact Hx| exact I]).
  assert (ST4 : stk bsegs m4 lo S1).
  { apply (stk_agree bsegs m3 m4 _ _ ST3); [| exact WM4]. eapply agree_sub; [exact AG4|]. intros x Hx. cbv beta in *. clear - Hx GS. lia. }
  assert (STp4 : stk bsegs m4 (S1 + 440) (usp - 104)).
  { apply (stk_agree bsegs m3 m4 _ _ STp2); [| exact WM4]. eapply agree_sub; [exact AG4|]. intros x Hx. cbv beta in *. clear - Hx GS. lia. }
  clear ST3 STp2 PSB C168 C72.
  rt_transport_with m3 m4 AG4 WM4 ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?VSZE in Hx; cbv beta;
      tl_dispatch Hx F A ltac:(first [clear - Hx GS; lia | clear - Hx FIM; lia]) ltac:(clear - Hx; lia) ltac:(clear - Hx FSELF; lia)
                         ltac:(clear - Hx FAV VSZ; lia)).
  assert (CP4 : forall a : word, aclient L0 [] usp (bv_unsigned a) -> m4 a = m a).
  { intros a Ha. rewrite <- (CP3 a Ha). apply MU4. cbn [outside]. split; [| exact I]. pose proof (CALLER _ Ha) as (N1 & _). clear - N1. lia. }
  clear CP3 AG4 MU4 FP3 MI3 ART3.
  unfold tx_regs.
  eapply (aevt_delarr RT PMc FDO MST DELA Σ3 K) with (p := SB) (n := CAP) (lo := lo);
    [ exact INS3 | reflexivity | reflexivity | exact ART4 | exact MI4
    | unfold call_ok; rewrite EU; split; [exact ST4|]; split; [exact LOW3|]; split; [clear - LOR; ul|]; split; [clear - GS; ul| clear - S32; Z.div_mod_to_equations; lia]
    | unfold unwind_ok; rewrite EU, EUS; right; right; clear - GS; lia | exact FRM3 | ].
  intros Σ5 v5 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F5 fc5 m5 FRM5 (ART5 & MI5 & ST5) PR5 LV5 FRS5 SP5 CR5.
  rewrite EU in ST5, PR5. rewrite LV3, LVR2 in LV5. rewrite FRS3 in PR5, FRS5.
  assert (L0IN5 : forall e, In e L0 -> In e (rt_live RT Σ5)) by (intros e He; rewrite LV5; do 4 right; apply in_or_app; right; exact He).
  assert (INV5 : In (A, 16 * size) (rt_live RT Σ5)) by (rewrite LV5; do 4 right; apply in_or_app; left; exact INV).
  assert (INI5 : In (IMPL, 96) (rt_live RT Σ5)) by (rewrite LV5; do 3 right; left; reflexivity).
  assert (AG5 : agree_on (fun x => aclient (rt_live RT Σ5) (rt_frames RT Σ) S1 x) m4 m5) by (intros a Ha; exact (PR5 a Ha)).
  assert (CP5 : forall a : word, aclient L0 [] usp (bv_unsigned a) -> m5 a = m a).
  { intros a Ha. rewrite <- (CP4 a Ha). apply PR5. eapply aclient_mono; [exact Ha| exact L0IN5| intros e []| clear - GS; lia]. }
  clear CP4.
  assert (ACS5 : forall x, S1 <= x < USTACK_TOP -> aclient (rt_live RT Σ5) (rt_frames RT Σ) S1 x) by (intros x Hx; left; exact Hx).
  assert (ACF5 : forall x, F <= x < F + 504 -> aclient (rt_live RT Σ5) (rt_frames RT Σ) S1 x).
  { intros x Hx. right; right; right; left. exists F, 3%nat. split; [exact INF|]. change (fs_size 3) with 512. clear - Hx. lia. }
  assert (ACH5 : forall x, F / 8 + 2147450880 <= x < F / 8 + 2147450880 + 64 -> aclient (rt_live RT Σ5) (rt_frames RT Σ) S1 x).
  { intros x Hx. right; right; right; right. exists F, 3%nat. split; [exact INF|]. change (fs_size 3) with 512. rewrite SHF. unfold shad, SHB. clear - Hx. lia. }
  assert (ACV5 : forall x, A <= x < A + 16 * size -> aclient (rt_live RT Σ5) (rt_frames RT Σ) S1 x).
  { intros x Hx. right; right; left. exists A, (16 * size). split; [exact INV5| clear - Hx; lia]. }
  assert (ACI5 : forall x, IMPL <= x < IMPL + 96 -> aclient (rt_live RT Σ5) (rt_frames RT Σ) S1 x).
  { intros x Hx. right; right; left. exists IMPL, 96. split; [exact INI5| clear - Hx; lia]. }
  clear ST4 PSB4.
  rt_transport_nw m4 m5 AG5 ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?VSZE in Hx; cbv beta;
      tl_dispatch Hx F A ltac:(first [apply ACS5; clear - Hx GS; lia | apply ACI5; clear - Hx; lia]) ltac:(apply ACF5; clear - Hx; lia)
                         ltac:(apply ACH5; clear - Hx; lia) ltac:(apply ACV5; clear - Hx VSZ; lia)).
  replace (ret_pc (Z_to_bv 64 0x9b9c8)) with (Z_to_bv 64 0x9b9c8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  clear AG5 PR5 ACS5 ACF5 ACH5 ACV5 ACI5 ART4 MI4 WM4.

  assert (INF5 : In (F, 3%nat) (rt_frames RT Σ5)) by (rewrite FRS5; exact INF).
  assert (LOW5 : rt_sp0 RT Σ5 - STACK_WIN <= lo) by (rewrite SP5; exact LOW3).
  assert (FP5 : fp_ok RT Σ5 lo [(F + 104, F + 112)]).
  { apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; right; left. exists F, 3%nat. split; [exact INF5|].
    change (fs_size 3) with 512. clear. lia. }
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { eapply (od_walkX3 usp S1 F IMPL (Z_to_bv 64 0x9b9c8) cgp (Z_to_bv 64 0x656e70) u0 u1 u2 v5 b1 b2 b3 b4 b5 b6 b7 s3 s4 s5 s6 s8 s9 s11 u3 u4 u5 u6 F5 fc5 m5);
      [clear - GS; lia| clear - GS; lia| clear - GS; ul| clear - GS; lia| clear - GS; lia| clear - IM0 GS; ul| exact PIM| exact MI5]. }
  cbv beta. intros ms6 (m6 & -> & MU6 & WM6 & MI6 & PIM6).
  apply evt_done.
  pose proof (art_of_munch RT AF Σ5 m5 m6 lo _ ART5 LOW5 FP5 MU6 WM6) as ART6.
  assert (AG6 : agree_on (fun x => ~ (F + 104 <= x < F + 112)) m5 m6)
    by (apply (agree_of_munch _ _ _ _ MU6); intros x Hx; cbn [outside]; split; [exact Hx| exact I]).
  assert (ST6 : stk bsegs m6 lo S1).
  { apply (stk_agree bsegs m5 m6 _ _ ST5); [| exact WM6]. eapply agree_sub; [exact AG6|]. intros x Hx. cbv beta in *. clear - Hx GS. lia. }
  assert (STp6 : stk bsegs m6 (S1 + 440) (usp - 104)).
  { apply (stk_agree bsegs m5 m6 _ _ STp4); [| exact WM6]. eapply agree_sub; [exact AG6|]. intros x Hx. cbv beta in *. clear - Hx GS. lia. }
  clear ST5 STp4 PIM.
  rt_transport_with m5 m6 AG6 WM6 ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?VSZE in Hx; cbv beta;
      tl_dispatch Hx F A ltac:(first [clear - Hx GS; lia | clear - Hx FIM; lia]) ltac:(clear - Hx; lia) ltac:(clear - Hx FSELF; lia)
                         ltac:(clear - Hx FAV VSZ; lia)).
  assert (CP6 : forall a : word, aclient L0 [] usp (bv_unsigned a) -> m6 a = m a).
  { intros a Ha. rewrite <- (CP5 a Ha). apply MU6. cbn [outside]. split; [| exact I]. pose proof (CALLER _ Ha) as (N1 & _). clear - N1. lia. }
  clear CP5 AG6 MU6 FP5 MI5 ART5.

  assert (VR6 : vrepA m6 (F + 32) A cap size els).
  { unfold vrepA, zlength. split; [exact VSZ|]. split; [exact VSC|]. split; [exact VCAP|]. split; [exact VA0|]. split; [exact VAT|].
    split; [exact VS|]. right. split; [exact CAP1|]. split; [exact A16|]. split; [exact APOS| exact VEL]. }
  rewrite FRS in FRS5.
  eapply (od_tail RT AF PMc FDO MST RTF DTOR VDES AFV Σ5 K usp S1 F lo IMPL IDX OC IA NIDX 8192 1024 A cap size els L0
            cra cgp cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11);
    [ exact S32 | exact S1R | exact U16 | exact UT | exact LOW5 | exact LOR | exact FRM5 | exact ART6 | exact MI6 | exact ST6
    | exact FRS5 | exact LV5 | clear; lia | clear; lia | exact NIDX0 | exact LPOS | exact IM8
    | exact LCa' | exact LCf | exact LCb' | exact LC248 | exact LCm | exact LC4 | exact STp6 | exact FRs | exact FH
    | exact VR6 | exact CAP1 | exact SZ1 | exact WRS | exact SHv | exact SHp | exact DPI | ].
  unfold od_ret_k in *. intros Σ' r0 r1 r2 q1 q2 q3 q4 q5 q6 q7 r3 r4 r5 r6 F' fc' m' FRM' ART' MI' ST' PR' LV' FRS' SP' CR'.
  apply HK; [exact FRM'| exact ART'| exact MI'| exact ST'| | exact LV'| exact FRS'| rewrite SP', SP5; exact SP3| rewrite CR', CR5; exact CR3].
  intros a Ha Ho. rewrite (PR' a Ha Ho). exact (CP6 a Ha).
Qed.

End Exit.
