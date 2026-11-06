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
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Layout Shadow RT_iface RT_iface2 RT_anndefs D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps
  Sj_hkit Sj_hkit2 Sj_new Sj_num_akit Sj_num_amem Od_hbaseA Atp_h_defsA Od_defsA Od_cpsA Od_hkit0A Od_deldtorA Od_lkitA Od_tailwA Od_bodyA
  Od_tailA Od_exitwA Od_arm_dblcA Od_beginA Od_topA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma rw_cells_pick : forall (n k : nat) (m : mem) A B cs, rw_cells asegs m A cs ->
  B = A + Z.of_nat (cells_size (firstn n cs)) -> rw_cells asegs m B (firstn k (skipn n cs)).
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

Lemma rw_cells_junk : forall (m : mem) A cs (n : nat), rw_cells asegs m A cs -> cells_size cs = n ->
  exists j, rw_cells asegs m A [CB n j].
Proof.
  intros m A cs n H <-. pose proof (rw_cells_wr_at asegs m A cs _ H (Z.le_refl _)) as W.
  destruct (wr_at_rw_CB m A _ W ltac:(lia)) as (j & Hj). rewrite Nat2Z.id in Hj. exists j. exact Hj.
Qed.

Section Exit.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
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

Lemma lib_fp_static : forall x, in_ranges LIB_FP x -> client_static x /\ 0x647c00 <= x < 0x647d88.
Proof.
  intros x (l & h & Hin & Hr). unfold LIB_FP in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin|Hin]; [inversion Hin; subst l h; split; [apply client_static_intro; lia| lia]|]). destruct Hin.
Qed.

Lemma LIB_agree : forall m m', LIB m -> agree_on (in_ranges LIB_FP) m m' -> LIB m'.
Proof using LIB_loc. intros m m' H AG. apply (LIB_loc m m' H). intros a Ha. apply AG. exact Ha. Qed.

Theorem od_exit : od_exitp_stmt RT LIB PMc.
Proof using LIB_loc AF FDO MST RTF DELA DTOR VDES AFV.
  unfold od_exitp_stmt.
  intros Σ0 Σ K E mL m0 A cap size IA OC els L0 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 cb st vs6 v224 v248 v304 v312 v328 v344.
  intros xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1.
  intros G R OUT EL0 SP0 HCB FRM INV HK.
  pose proof (od_oka_of_rt RT AF Σ E mL G R) as OK.
  od_open_inv INV.
  pose proof (od_art_cur RT AF Σ E mL m1 G R MU WM) as ART1.
  pose proof R as [ART0 FRS INC INS INI INX LOW SHP SHD KEEP WML].
  pose proof OUT as [(j352 & j400 & OHI) OPAD OSAV (h0 & OHDR) OVEC (CAP1 & SZ1) OWRS OSHV OSHP OSHD (pre8 & mid & rest & LPRE & LMID & LREST & ODL) LV LPOS OLIB OPRES].
  clear ITER IDXA IDXL IDXF BUFRO PBL SBW VT GOT OK.
  og_env G. rewrite ETP in *.
  pose proof (og_Fsh _ G) as (_ & FSD). pose proof (og_F_sb _ G) as F_S. pose proof (og_Fs_sb _ G) as FS_S.
  pose proof (og_sb _ G) as (_ & _ & _ & SBD). pose proof (og_copy _ G) as (_ & _ & _ & _ & CPD).
  set (usp := oa_USP E) in *. set (S1a := oa_S1 E) in *. set (F := oa_F E) in *. set (lo := o_lo E) in *.
  set (SB := o_SB E) in *. set (CAP := o_CAP E) in *. set (COPY := o_COPY E) in *. set (IMPL := o_IMPL E) in *.
  set (IDX := o_IDX E) in *. set (NCOPY := o_BUF E - COPY + o_len E + 64) in *.
  assert (NC0 : 64 <= NCOPY) by (unfold NCOPY; clear - CPB NR; lia).
  assert (NI0 : 0 < 4 * Z.of_nat (o_icap E)) by (clear - ICAP NR; lia).
  assert (NS0 : 0 < CAP) by (clear - CAPR NR; lia).
  pose proof (af_sp0_range RT AF Σ m1 ART1) as SP0R. pose proof (af_sp0_win RT AF Σ m1 ART1) as SP0W.
  assert (INF : In (F, 3%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  pose proof (af_frames_range RT AF Σ m1 F 3 ART1 INF) as (F0 & FR1 & _ & FLV).
  pose proof (af_frames_align RT AF Σ m1 F 3 ART1 INF) as (_ & FSEG).
  pose proof (fframe_ranges RT AF Σ m1 F 3 ART1 INF) as (_ & _ & _ & SHB0 & SHT).
  pose proof (af_fshadow_apart RT AF Σ m1 F 3 ART1 INF) as (FSL & FSF). pose proof (FSF F 3%nat INF) as FSELF.
  change (fs_size 3) with 512 in *.
  assert (SHF : shad (F + 512) = shad F + 64) by (unfold shad; clear - F64; Z.div_mod_to_equations; lia).
  rewrite SHF in *. unfold shad, SHB in SHB0, SHT, FSELF, FSL.

  assert (LPX : lposx (vblockA A cap size ++ L0)).
  { apply lposx_app; [| apply lposx_of_pos; exact LPOS]. unfold vblockA. destruct (cap =? 0) eqn:CZ; [apply Z.eqb_eq in CZ; lia|].
    apply lposx_ann_block. lia. }
  destruct (pos_prefix_facts RT AF Σ m1 [(IA, 1024); (OC, 8192); (IDX, 4 * Z.of_nat (o_icap E)); (IMPL, 96); (SB, CAP); (COPY, NCOPY)] []
              (vblockA A cap size ++ L0) ART1 LV
              ltac:(intros e [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [snd]; lia) LPX) as (ND6 & NDL).
  assert (N6 : (IA <> SB /\ OC <> SB /\ IDX <> SB /\ IMPL <> SB) /\ (IA <> COPY /\ OC <> COPY /\ IDX <> COPY /\ IMPL <> COPY /\ SB <> COPY)).
  { cbn [map fst] in ND6. apply NoDup_cons_iff in ND6. destruct ND6 as [X1 Y1]. apply NoDup_cons_iff in Y1. destruct Y1 as [X2 Y2].
    apply NoDup_cons_iff in Y2. destruct Y2 as [X3 Y3]. apply NoDup_cons_iff in Y3. destruct Y3 as [X4 Y4].
    apply NoDup_cons_iff in Y4. destruct Y4 as [X5 Y5].
    cbn [In] in X1, X2, X3, X4, X5. clear - X1 X2 X3 X4 X5. repeat split; intros EQ; rewrite EQ in *; tauto. }
  destruct N6 as ((NS1 & NS2 & NS3 & NS4) & (NC1 & NC2 & NC3 & NC4 & NC5)).
  assert (LVR1 : live_remove COPY (rt_live RT Σ)
                 = (IA, 1024) :: (OC, 8192) :: (IDX, 4 * Z.of_nat (o_icap E)) :: (IMPL, 96) :: (SB, CAP) :: vblockA A cap size ++ L0).
  { rewrite LV.
    rewrite (live_remove_one COPY NCOPY [(IA, 1024); (OC, 8192); (IDX, 4 * Z.of_nat (o_icap E)); (IMPL, 96); (SB, CAP)] [] (vblockA A cap size ++ L0));
      [reflexivity| intros e [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst]; assumption | intros e []
      | intros e He EQ; exact (NDL (COPY, NCOPY) e ltac:(do 5 right; left; reflexivity) He (eq_sym EQ))]. }
  assert (LVR2 : live_remove SB ((IA, 1024) :: (OC, 8192) :: (IDX, 4 * Z.of_nat (o_icap E)) :: (IMPL, 96) :: (SB, CAP) :: vblockA A cap size ++ L0)
                 = (IA, 1024) :: (OC, 8192) :: (IDX, 4 * Z.of_nat (o_icap E)) :: (IMPL, 96) :: vblockA A cap size ++ L0).
  { rewrite (live_remove_one SB CAP [(IA, 1024); (OC, 8192); (IDX, 4 * Z.of_nat (o_icap E)); (IMPL, 96)] [] (vblockA A cap size ++ L0));
      [reflexivity| intros e [<-|[<-|[<-|[<-|[]]]]]; cbn [fst]; assumption | intros e []
      | intros e He EQ; exact (NDL (SB, CAP) e ltac:(do 4 right; left; reflexivity) He (eq_sym EQ))]. }

  destruct OVEC as (VSZ & VSC & VCAP & VA0 & VAT & VS & VB).
  destruct VB as [(B1 & B2)|(_ & A16 & APOS & VEL)]; [lia|].
  assert (INV : In (A, 16 * size) (vblockA A cap size)).
  { unfold vblockA. destruct (cap =? 0) eqn:CZ; [apply Z.eqb_eq in CZ; lia|]. apply ann_block_vis. }
  assert (INVL : In (A, 16 * size) (rt_live RT Σ)) by (rewrite LV; do 6 right; apply in_or_app; left; exact INV).
  pose proof (FLV A (16 * size) INVL) as FAV.
  pose proof (af_live_range RT AF Σ m1 A (16 * size) ART1 INVL) as (_ & AV1 & _).
  pose proof (velts_size els) as VSZE. unfold zlength in VSZ.
  pose proof (FSL A (16 * size) INVL) as SAV.
  assert (SBA : SB + CAP <= A \/ A + 16 * size <= SB).
  { apply (af_live_disj RT AF Σ m1 SB CAP A (16 * size) [(IA, 1024); (OC, 8192); (IDX, 4 * Z.of_nat (o_icap E)); (IMPL, 96)]
             ((COPY, NCOPY) :: vblockA A cap size ++ L0) ART1 LV). apply in_or_app. right. right. apply in_or_app. left. exact INV. }
  pose proof (FLV IMPL 96 INI) as FIM. pose proof (FSL IMPL 96 INI) as SIM.
  pose proof (af_live_range RT AF Σ m1 IMPL 96 ART1 INI) as (_ & IM1 & _).
  assert (GS : F + 512 <= lo /\ F / 8 + 2147450880 + 64 <= lo /\ A + 16 * size <= lo /\ lo <= S1a /\ S1a + 512 <= usp /\ usp <= USTACK_TOP /\ SB + CAP <= lo /\ IMPL + 96 <= lo)
    by (clear - FR1 LOW LOR SHT AV1 S1R USPT FR FSH SBR IMR; ul).

  assert (WML1 : wmono asegs mL m1) by exact (wmono_trans asegs _ _ _ WML WM).
  assert (AGL : agree_on (fun x => aclient (rt_live RT Σ) (rt_frames RT Σ) (S1a + 352) x /\ outside (od_Wk E) x) mL m1).
  { intros a [Ha Ho]. rewrite (MU a (od_client_outside RT AF Σ E mL (o_m0 E) _ G R ART0 Ha Ho)). exact (KEEP a Ha Ho). }
  assert (ACS : forall x, S1a + 352 <= x < usp -> aclient (rt_live RT Σ) (rt_frames RT Σ) (S1a + 352) x /\ outside (od_Wk E) x).
  { intros x Hx. split; [left; clear - Hx GS; lia|]. unfold od_Wk. cbn [outside]. fold F SB CAP. clear - Hx GS. lia. }
  assert (ACF : forall x, F <= x < F + 192 -> aclient (rt_live RT Σ) (rt_frames RT Σ) (S1a + 352) x /\ outside (od_Wk E) x).
  { intros x Hx. split; [right; right; right; left; exists F, 3%nat; split; [exact INF|]; change (fs_size 3) with 512; clear - Hx; lia|].
    unfold od_Wk. cbn [outside]. fold F SB CAP. clear - Hx F_S. lia. }
  assert (ACH : forall x, F / 8 + 2147450880 <= x < F / 8 + 2147450880 + 64 -> aclient (rt_live RT Σ) (rt_frames RT Σ) (S1a + 352) x /\ outside (od_Wk E) x).
  { intros x Hx. split; [right; right; right; right; exists F, 3%nat; split; [exact INF|]; change (fs_size 3) with 512; rewrite SHF; unfold shad, SHB; clear - Hx; lia|].
    unfold od_Wk. cbn [outside]. fold F SB CAP. clear - Hx FSD FS_S. lia. }
  assert (ACV : forall x, A <= x < A + 16 * size -> aclient (rt_live RT Σ) (rt_frames RT Σ) (S1a + 352) x /\ outside (od_Wk E) x).
  { intros x Hx. split; [right; right; left; exists A, (16 * size); split; [exact INVL| clear - Hx; lia]|].
    unfold od_Wk. cbn [outside]. fold F SB CAP. clear - Hx FAV SBA. lia. }
  assert (OPAD1 : stk asegs m1 (S1a + 408) (usp - 104)).
  { apply (stk_agree asegs mL m1 _ _ OPAD); [| exact WML1]. eapply agree_sub; [exact AGL|]. intros x Hx. cbv beta in *. apply ACS. clear - Hx. lia. }
  clear OPAD. unfold fa_saved in OSAV. cbn [map repeat] in OSHV, OSHP, OSHD.
  rt_transport_with mL m1 AGL WML1 ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?VSZE in Hx; cbv beta;
      tl_dispatch Hx F A ltac:(apply ACS; clear - Hx S1R; lia) ltac:(apply ACF; clear - Hx; lia)
                         ltac:(apply ACH; clear - Hx; lia) ltac:(apply ACV; clear - Hx VSZ; lia)).

  pose proof (rw_cells_pick 4 1 m1 _ (S1a + 160) _ FR128 ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as C160.
  pose proof (rw_cells_pick 7 1 m1 _ (S1a + 240) _ FR184 ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as C240.
  pose proof (rw_cells_pick 3 1 m1 _ (S1a + 208) _ FR184 ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as C208.
  pose proof (rw_cells_pick 1 2 m1 _ (S1a + 192) _ FR184 ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as LCf.
  pose proof (rw_cells_pick 4 1 m1 _ (S1a + 216) _ FR184 ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as LC216.
  pose proof (rw_cells_pick 1 1 m1 _ (F + 104) _ PARS ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as PIM.
  pose proof (rw_cells_pick 6 1 m1 _ (F + 144) _ PARS ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as PSB.
  cbn [firstn skipn] in C160, C240, C208, LCf, LC216, PIM, PSB.
  assert (LCa : exists j, rw_cells asegs m1 S1a [CB 192 j]).
  { pose proof (rw_cells_pick 0 1 m1 _ (S1a + 184) _ FR184 ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as X. cbn [firstn skipn] in X.
    refine (rw_cells_junk m1 S1a (_ ++ _ ++ _ ++ _ ++ _ ++ _) 192%nat _ _); [join_cells| reflexivity]. }
  destruct LCa as (ja & LCa).
  destruct (rw_cells_junk m1 (S1a + 208) _ 8%nat C208 eq_refl) as (j208 & LCb).
  assert (LCm : exists j, rw_cells asegs m1 (S1a + 224) [CB 176 j]).
  { pose proof (rw_cells_pick 5 16 m1 _ (S1a + 224) _ FR184 ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as X. cbn [firstn skipn] in X.
    pose proof (rw_cells_pick 0 1 m1 _ (S1a + 352) _ OHI ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as Y. cbn [firstn skipn] in Y.
    refine (rw_cells_junk m1 (S1a + 224) (_ ++ _) 176%nat _ _);
      [apply Sj_stage1_kit.rw_cells_app; split; [exact X| cbn [cells_size csize Nat.add]; readdr_ass]| reflexivity]. }
  destruct LCm as (jm & LCm).
  pose proof (rw_cells_pick 1 1 m1 _ (S1a + 400) _ OHI ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as LC4. cbn [firstn skipn] in LC4.
  assert (DPL : rw_cells asegs m1 IMPL (dl_cells (Z_to_bv 64 OD_DPI_VPTR) pre8 (Z_to_bv 64 IDX) mid (Z_to_bv 64 OC) (Z_to_bv 64 IA) rest)).
  { rewrite VPT in ODL. apply (rw_cells_recell asegs m1 IMPL _ _ DPI); [| exact ODL| reflexivity].
    unfold dl_cells. cbn [cells_wf cell_wf]. rewrite LPRE, LMID, LREST. repeat split; reflexivity. }
  clear FR0 FR32 FR104 FR128 FR176 FR184 PARS DPI OHI ODL.

  assert (L0IN : forall e, In e L0 -> In e (rt_live RT Σ)) by (intros e He; rewrite LV; do 6 right; apply in_or_app; right; exact He).
  assert (CALLER : forall x, aclient L0 [] usp x ->
            ~ (F <= x < F + 512) /\ ~ (F / 8 + 2147450880 <= x < F / 8 + 2147450880 + 64) /\ ~ (SB <= x < SB + CAP) /\ ~ (lo <= x < usp)).
  { intros x [H|[H|[H|[H|H]]]].
    - clear - H GS. lia.
    - pose proof (client_static_range x H) as CR. clear - CR FB SHB0 SBD LOB. ul.
    - destruct H as (p & n & Hin & Hp). pose proof (L0IN _ Hin) as HinL.
      pose proof (FLV p n HinL) as D1. pose proof (FSL p n HinL) as D2. pose proof (af_live_range RT AF Σ m1 p n ART1 HinL) as (_ & D3 & _).
      assert (D4 : SB + CAP <= p \/ p + n <= SB).
      { apply (af_live_disj RT AF Σ m1 SB CAP p n [(IA, 1024); (OC, 8192); (IDX, 4 * Z.of_nat (o_icap E)); (IMPL, 96)]
                 ((COPY, NCOPY) :: vblockA A cap size ++ L0) ART1 LV). apply in_or_app. right. right. apply in_or_app. right. exact Hin. }
      clear - Hp D1 D2 D3 D4 LOW. lia.
    - destruct H as (f & k & [] & _).
    - destruct H as (f & k & [] & _). }
  assert (CP1 : forall a : word, aclient L0 [] usp (bv_unsigned a) -> m1 a = mL a).
  { intros a Ha. apply AGL. pose proof (CALLER _ Ha) as (C1 & _ & C3 & _). split.
    - eapply aclient_mono; [exact Ha| exact L0IN| intros e []| clear - GS; lia].
    - unfold od_Wk. cbn [outside]. fold F SB CAP. clear - C1 C3. lia. }
  clear AGL ACS ACF ACH ACV KEEP MU WM WML WML1 SHP SHD ART0 FSD F_S FS_S SBD CPD.

  assert (FP1 : fp_ok RT Σ lo [(F / 8 + 2147450880 + 24, F / 8 + 2147450880 + 32)]).
  { apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; right; right. exists F, 3%nat. split; [exact INF|].
    change (fs_size 3) with 512. rewrite SHF. unfold shad, SHB. clear. lia. }
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { eapply (od_walkX1 usp S1a F COPY xra (o_gp E) (Z_to_bv 64 0x6488f0) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6
              (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) xF xfc m1);
      [clear - GS LOB; ul| clear - GS; lia| clear - GS; ul| exact FB| clear - GS; lia| clear - CP0 CPB BUFR GS NR; ul| exact C240| exact C160| exact OSHD| exact MI]. }
  cbv beta. intros ms2 (m2 & -> & MU2 & WM2 & MI2 & SHD2). cbn [map repeat] in SHD2.
  apply evt_done.
  pose proof (art_of_munch RT AF Σ m1 m2 lo _ ART1 LOW FP1 MU2 WM2) as ART2.
  assert (AG2 : agree_on (fun x => ~ (F / 8 + 2147450880 + 24 <= x < F / 8 + 2147450880 + 32)) m1 m2)
    by (apply (agree_of_munch _ _ _ _ MU2); intros x Hx; cbn [outside]; split; [exact Hx| exact I]).
  assert (ST2 : stk asegs m2 lo S1a).
  { apply (stk_agree asegs m1 m2 _ _ ST); [| exact WM2]. eapply agree_sub; [exact AG2|]. intros x Hx. cbv beta in *. clear - Hx GS. lia. }
  assert (OPAD2 : stk asegs m2 (S1a + 408) (usp - 104)).
  { apply (stk_agree asegs m1 m2 _ _ OPAD1); [| exact WM2]. eapply agree_sub; [exact AG2|]. intros x Hx. cbv beta in *. clear - Hx GS. lia. }
  clear ST OPAD1 OSHD C240 C160.
  unfold dl_cells in DPL.
  rt_transport_with m1 m2 AG2 WM2 ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?VSZE in Hx; cbv beta;
      tl_dispatch Hx F A ltac:(first [clear - Hx GS; lia | clear - Hx SIM; lia]) ltac:(clear - Hx FSELF; lia) ltac:(clear - Hx; lia)
                         ltac:(clear - Hx SAV VSZ; lia)).
  assert (CP2 : forall a : word, aclient L0 [] usp (bv_unsigned a) -> m2 a = mL a).
  { intros a Ha. rewrite <- (CP1 a Ha). apply MU2. cbn [outside]. split; [| exact I]. pose proof (CALLER _ Ha) as (_ & C2 & _). clear - C2. lia. }
  clear CP1 AG2 MU2 FP1 MI ART1.
  unfold tx_regs.
  assert (EU : bv_unsigned (Z_to_bv 64 S1a) = S1a) by (apply unsigned_lit; clear - GS LOB; ul).
  assert (EUS : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; clear - GS LOB; ul).
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
  assert (AG3 : agree_on (fun x => aclient (rt_live RT Σ3) (rt_frames RT Σ) S1a x) m2 m3) by (intros a Ha; exact (PR3 a Ha)).
  assert (CP3 : forall a : word, aclient L0 [] usp (bv_unsigned a) -> m3 a = mL a).
  { intros a Ha. rewrite <- (CP2 a Ha). apply PR3. eapply aclient_mono; [exact Ha| exact L0IN3| intros e []| clear - GS; lia]. }
  clear CP2.
  assert (ACS3 : forall x, S1a <= x < USTACK_TOP -> aclient (rt_live RT Σ3) (rt_frames RT Σ) S1a x) by (intros x Hx; left; exact Hx).
  assert (ACF3 : forall x, F <= x < F + 504 -> aclient (rt_live RT Σ3) (rt_frames RT Σ) S1a x).
  { intros x Hx. right; right; right; left. exists F, 3%nat. split; [exact INF|]. change (fs_size 3) with 512. clear - Hx. lia. }
  assert (ACH3 : forall x, F / 8 + 2147450880 <= x < F / 8 + 2147450880 + 64 -> aclient (rt_live RT Σ3) (rt_frames RT Σ) S1a x).
  { intros x Hx. right; right; right; right. exists F, 3%nat. split; [exact INF|]. change (fs_size 3) with 512. rewrite SHF. unfold shad, SHB. clear - Hx. lia. }
  assert (ACV3 : forall x, A <= x < A + 16 * size -> aclient (rt_live RT Σ3) (rt_frames RT Σ) S1a x).
  { intros x Hx. right; right; left. exists A, (16 * size). split; [exact INV3| clear - Hx; lia]. }
  assert (ACI3 : forall x, IMPL <= x < IMPL + 96 -> aclient (rt_live RT Σ3) (rt_frames RT Σ) S1a x).
  { intros x Hx. right; right; left. exists IMPL, 96. split; [exact INI3| clear - Hx; lia]. }
  clear ST2.
  rt_transport_nw m2 m3 AG3 ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?VSZE in Hx; cbv beta;
      tl_dispatch Hx F A ltac:(first [apply ACS3; clear - Hx GS; lia | apply ACI3; clear - Hx; lia]) ltac:(apply ACF3; clear - Hx; lia)
                         ltac:(apply ACH3; clear - Hx; lia) ltac:(apply ACV3; clear - Hx VSZ; lia)).
  replace (ret_pc (Z_to_bv 64 0x99d38)) with (Z_to_bv 64 0x99d38) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  clear AG3 PR3 ACS3 ACF3 ACH3 ACV3 ACI3 ART2 MI2 WM2.

  assert (INF3 : In (F, 3%nat) (rt_frames RT Σ3)) by (rewrite FRS3; exact INF).
  assert (LOW3 : rt_sp0 RT Σ3 - STACK_WIN <= lo) by (rewrite SP3; exact LOW).
  assert (FP3 : fp_ok RT Σ3 lo [(F + 144, F + 152)]).
  { apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; right; left. exists F, 3%nat. split; [exact INF3|].
    change (fs_size 3) with 512. clear. lia. }
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { eapply (od_walkX2 usp S1a F SB (Z_to_bv 64 0x99d38) (o_gp E) (Z_to_bv 64 0x6488f0) t0' t1' t2' v3 a1' a2' a3' a4' a5' a6' a7' xs2 xs5 xs6 xs7 xs9 xs10 xs11 t3' t4' t5' t6' F3 fc3 m3);
      [clear - GS LOB; ul| clear - GS; lia| clear - GS; ul| exact FB| clear - GS; lia| clear - SB0 NS0 GS; ul| exact C208| exact PSB| exact MI3]. }
  cbv beta. intros ms4 (m4 & a1x & -> & MU4 & WM4 & MI4 & PSB4).
  apply evt_done.
  pose proof (art_of_munch RT AF Σ3 m3 m4 lo _ ART3 LOW3 FP3 MU4 WM4) as ART4.
  assert (AG4 : agree_on (fun x => ~ (F + 144 <= x < F + 152)) m3 m4)
    by (apply (agree_of_munch _ _ _ _ MU4); intros x Hx; cbn [outside]; split; [exact Hx| exact I]).
  assert (ST4 : stk asegs m4 lo S1a).
  { apply (stk_agree asegs m3 m4 _ _ ST3); [| exact WM4]. eapply agree_sub; [exact AG4|]. intros x Hx. cbv beta in *. clear - Hx GS. lia. }
  assert (OPAD4 : stk asegs m4 (S1a + 408) (usp - 104)).
  { apply (stk_agree asegs m3 m4 _ _ OPAD2); [| exact WM4]. eapply agree_sub; [exact AG4|]. intros x Hx. cbv beta in *. clear - Hx GS. lia. }
  clear ST3 OPAD2 PSB C208.
  rt_transport_with m3 m4 AG4 WM4 ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?VSZE in Hx; cbv beta;
      tl_dispatch Hx F A ltac:(first [clear - Hx GS; lia | clear - Hx FIM; lia]) ltac:(clear - Hx; lia) ltac:(clear - Hx FSELF; lia)
                         ltac:(clear - Hx FAV VSZ; lia)).
  assert (CP4 : forall a : word, aclient L0 [] usp (bv_unsigned a) -> m4 a = mL a).
  { intros a Ha. rewrite <- (CP3 a Ha). apply MU4. cbn [outside]. split; [| exact I]. pose proof (CALLER _ Ha) as (C1 & _). clear - C1. lia. }
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
  assert (AG5 : agree_on (fun x => aclient (rt_live RT Σ5) (rt_frames RT Σ) S1a x) m4 m5) by (intros a Ha; exact (PR5 a Ha)).
  assert (CP5 : forall a : word, aclient L0 [] usp (bv_unsigned a) -> m5 a = mL a).
  { intros a Ha. rewrite <- (CP4 a Ha). apply PR5. eapply aclient_mono; [exact Ha| exact L0IN5| intros e []| clear - GS; lia]. }
  clear CP4.
  assert (ACS5 : forall x, S1a <= x < USTACK_TOP -> aclient (rt_live RT Σ5) (rt_frames RT Σ) S1a x) by (intros x Hx; left; exact Hx).
  assert (ACF5 : forall x, F <= x < F + 504 -> aclient (rt_live RT Σ5) (rt_frames RT Σ) S1a x).
  { intros x Hx. right; right; right; left. exists F, 3%nat. split; [exact INF|]. change (fs_size 3) with 512. clear - Hx. lia. }
  assert (ACH5 : forall x, F / 8 + 2147450880 <= x < F / 8 + 2147450880 + 64 -> aclient (rt_live RT Σ5) (rt_frames RT Σ) S1a x).
  { intros x Hx. right; right; right; right. exists F, 3%nat. split; [exact INF|]. change (fs_size 3) with 512. rewrite SHF. unfold shad, SHB. clear - Hx. lia. }
  assert (ACV5 : forall x, A <= x < A + 16 * size -> aclient (rt_live RT Σ5) (rt_frames RT Σ) S1a x).
  { intros x Hx. right; right; left. exists A, (16 * size). split; [exact INV5| clear - Hx; lia]. }
  assert (ACI5 : forall x, IMPL <= x < IMPL + 96 -> aclient (rt_live RT Σ5) (rt_frames RT Σ) S1a x).
  { intros x Hx. right; right; left. exists IMPL, 96. split; [exact INI5| clear - Hx; lia]. }
  clear ST4 PSB4.
  rt_transport_nw m4 m5 AG5 ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?VSZE in Hx; cbv beta;
      tl_dispatch Hx F A ltac:(first [apply ACS5; clear - Hx GS; lia | apply ACI5; clear - Hx; lia]) ltac:(apply ACF5; clear - Hx; lia)
                         ltac:(apply ACH5; clear - Hx; lia) ltac:(apply ACV5; clear - Hx VSZ; lia)).
  replace (ret_pc (Z_to_bv 64 OD_TAIL)) with (Z_to_bv 64 OD_TAIL) by (symmetry; apply ret_pc_even; [unfold OD_TAIL; lia| reflexivity]).
  clear AG5 PR5 ACS5 ACF5 ACH5 ACV5 ACI5 ART4 MI4 WM4.

  assert (SHP5 : rw_cells asegs m5 (F / 8 + 2147450880 + 12)
                   [CB 1 [Z_to_bv 8 0]; CB 1 [Z_to_bv 8 0]; CB 1 [Z_to_bv 8 0]; CB 1 [Z_to_bv 8 0]; CB 1 [Z_to_bv 8 0]; CB 1 [Z_to_bv 8 0]; CB 1 [Z_to_bv 8 0]]).
  { apply (rw_cells_recell asegs m5 _ _ _ OSHP); [cbn [cells_wf cell_wf length]; repeat split; reflexivity| reflexivity| reflexivity]. }
  assert (VR5 : vrepA m5 (F + 32) A cap size els).
  { unfold vrepA, zlength. split; [exact VSZ|]. split; [exact VSC|]. split; [exact VCAP|]. split; [exact VA0|]. split; [exact VAT|].
    split; [exact VS|]. right. split; [exact CAP1|]. split; [exact A16|]. split; [exact APOS| exact VEL]. }
  assert (LOW5 : rt_sp0 RT Σ5 - STACK_WIN <= lo) by (rewrite SP5; exact LOW3).
  rewrite FRS in FRS5.
  eapply (od_tail RT AF PMc FDO MST RTF DTOR VDES AFV Σ5 K usp S1a F lo IMPL IDX OC IA (4 * Z.of_nat (o_icap E)) 8192 1024 A cap size els L0
            cra (o_gp E) cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11);
    [ exact S32 | exact S1R | exact USP16 | clear - USPT; ul | exact LOW5 | exact LOR | exact FRM5 | exact ART5 | exact MI5 | exact ST5
    | exact FRS5 | exact LV5 | clear; lia | clear; lia | exact NI0 | exact LPOS | exact IM8
    | exact LCa | exact LCf | exact LCb | exact LC216 | exact LCm | exact LC4 | exact OPAD4 | exact OSAV | exact OHDR | exact PIM
    | exact VR5 | exact CAP1 | exact SZ1 | exact OWRS | exact OSHV | exact SHP5 | exact DPL | ].

  unfold od_ret_k. intros Σ' r0 r1 r2 q1 q2 q3 q4 q5 q6 q7 r3 r4 r5 r6 F' fc' m' FRM' ART' MI' ST' PR' LV' FRS' SP' CR'.
  apply HK; [exact FRM'| exact ART'| exact MI'| exact ST'| | | rewrite LV'; exact EL0| exact FRS'| rewrite SP', SP5, SP3; exact SP0
            | rewrite CR', CR5, CR3; exact HCB].
  - intros a Ha Ho. rewrite <- EL0 in Ha. rewrite (PR' a Ha I). rewrite (CP5 a Ha). exact (OPRES a Ha Ho).
  - apply (LIB_agree mL m' OLIB). intros a Ha. pose proof (lib_fp_static _ Ha) as (CS & _).
    assert (AC : aclient L0 [] usp (bv_unsigned a)) by (right; left; exact CS).
    rewrite (PR' a AC I). exact (CP5 a AC).
Qed.

End Exit.
