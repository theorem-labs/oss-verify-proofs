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
  Od_tailB Od_exitwB Od_exitB Od_exitiB Od_cpsB Od_beginB Od_top_defsB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

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

Lemma lib_fp_static : forall x, in_ranges LIB_FP x -> client_static x.
Proof.
  intros x (l & h & Hin & Hr). unfold LIB_FP in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin|Hin]; [inversion Hin; subst l h; apply client_static_intro; lia|]). destruct Hin.
Qed.

Lemma LIB_agree : forall m m', LIB m -> agree_on (in_ranges LIB_FP) m m' -> LIB m'.
Proof using LIB_loc. intros m m' H AG. apply (LIB_loc m m' H). intros a Ha. apply AG. exact Ha. Qed.

Lemma od_ret_k_of_fin : forall (K : config -> Prop) (Σ0 : rts RT) (usp lo : Z) (cra gp cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word)
    (m0 mx : mem) (cb sp0 cr : Z),
  od_fin_k RT LIB PMc K Σ0 usp lo cra gp cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 m0 cb ->
  rt_pres_fp (rt_live RT Σ0) [] usp LIB_FP m0 mx -> LIB mx -> sp0 = rt_sp0 RT Σ0 -> cb <= cr ->
  od_ret_k RT PMc K usp lo cra gp cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 (rt_live RT Σ0) sp0 cr mx.
Proof using LIB_loc.
  intros K Σ0 usp lo cra gp cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 m0 mx cb sp0 cr HK OPRES OLIB -> HCB. unfold od_ret_k.
  intros Σ' r0 r1 r2 q1 q2 q3 q4 q5 q6 q7 r3 r4 r5 r6 F' fc' m' FRM' ART' MI' ST' PR' LV' FRS' SP' CR'.
  apply HK; [exact FRM'| exact ART'| exact MI'| exact ST'| | | exact LV'| exact FRS'| exact SP'| rewrite CR'; exact HCB].
  - intros a Ha Ho. rewrite (PR' a Ha I). exact (OPRES a Ha Ho).
  - apply (LIB_agree mx m' OLIB). intros a Ha. pose proof (lib_fp_static _ Ha) as CS.
    exact (PR' a ltac:(right; left; exact CS) I).
Qed.

Theorem od_exit : od_exitp_stmt RT LIB PMc.
Proof using LIB_loc AF FDO MST RTF DELA DTOR VDES AFV.
  unfold od_exitp_stmt.
  intros Σ0 Σ K E mL m0 A cap size IA OC els L0 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 cb st vs v88 v144 v152 v240 v312 v336 v352.
  intros xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs11 xt3 xt4 xt5 xt6 xF xfc m1.
  intros G R OUT EL0 SP0 HCB FRM INV HK.
  pose proof (od_oka_of_rt RT AF Σ E mL G R) as OK.
  pose proof INV as INV0.
  od_open_inv INV.
  clear FR8 FR96 FR240 ITER PARS DPI IDXA IDXL IDXF BUFRO PBL SBW VT GOT MI ST.
  fold (od_W E) in MU.
  pose proof (od_art_cur RT AF Σ E mL m1 G R MU WM) as ART1.
  pose proof R as [ART0 FRS INC INS INI INX LOW SHP SHD KEEP WML].
  pose proof OUT as [OLO0 (j384 & j432 & OHI) OPAD OSAV (h0 & OHDR) OVEC (CAP1 & SZ1) OWRS OSHV OSHP OSHD (pre8 & mid & rest & LPRE & LMID & LREST & ODL) LV LPOS OLIB OPRES].
  og_env G.
  pose proof (og_Fsh _ G) as (_ & FSD). pose proof (og_F_sb _ G) as F_S. pose proof (og_Fs_sb _ G) as FS_S.
  pose proof (og_sb _ G) as (_ & _ & _ & SBD).
  set (usp := oa_USP E) in *. set (S1a := oa_S1 E) in *. set (F := oa_F E) in *. set (lo := o_lo E) in *.
  set (SB := o_SB E) in *. set (CAP := o_CAP E) in *. set (COPY := o_COPY E) in *. set (IMPL := o_IMPL E) in *.
  set (IDX := o_IDX E) in *. set (NCOPY := o_BUF E - COPY + o_len E + 64) in *.
  assert (NS0 : 0 < CAP) by (clear - CAPR NR; lia).
  pose proof (af_sp0_range RT AF Σ m1 ART1) as SP0R. pose proof (af_sp0_win RT AF Σ m1 ART1) as SP0W.
  assert (INF : In (F, 3%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  pose proof (af_frames_range RT AF Σ m1 F 3 ART1 INF) as (F0 & FR1 & _ & FLV).
  pose proof (fframe_ranges RT AF Σ m1 F 3 ART1 INF) as (_ & _ & _ & SHB0 & SHT).
  pose proof (af_fshadow_apart RT AF Σ m1 F 3 ART1 INF) as (FSL & _).
  change (fs_size 3) with 512 in *.
  assert (SHF : shad (F + 512) = shad F + 64) by (unfold shad; clear - F64; Z.div_mod_to_equations; lia).
  rewrite SHF in *. unfold shad, SHB in SHB0, SHT, FSL.

  destruct OVEC as (VSZ & VSC & VCAP & VA0 & VAT & VS & VB).
  destruct VB as [(B1 & B2)|(_ & A16 & APOS & VEL)]; [lia|].
  assert (INV : In (A, 16 * size) (vblockA A cap size)).
  { unfold vblockA. destruct (cap =? 0) eqn:CZ; [apply Z.eqb_eq in CZ; lia|]. apply ann_block_vis. }
  assert (INVL : In (A, 16 * size) (rt_live RT Σ)) by (rewrite LV; do 6 right; apply in_or_app; left; exact INV).
  pose proof (FLV A (16 * size) INVL) as FAV.
  pose proof (af_live_range RT AF Σ m1 A (16 * size) ART1 INVL) as (_ & AV1 & _).
  pose proof (velts_size els) as VSZE. unfold zlength in VSZ.
  assert (SBA : SB + CAP <= A \/ A + 16 * size <= SB).
  { apply (af_live_disj RT AF Σ m1 SB CAP A (16 * size) [(IA, 1024); (OC, 8192); (IDX, 4 * Z.of_nat (o_icap E)); (IMPL, 96)]
             ((COPY, NCOPY) :: vblockA A cap size ++ L0) ART1 LV). apply in_or_app. right. right. apply in_or_app. left. exact INV. }
  assert (GS : F + 512 <= lo /\ F / 8 + 2147450880 + 64 <= lo /\ A + 16 * size <= lo /\ lo <= S1a /\ S1a + 544 <= usp /\ usp <= USTACK_TOP /\ SB + CAP <= lo)
    by (clear - FR1 LOW LOR SHT AV1 S1R USPT FR FSH SBR; ul).

  assert (WML1 : wmono bsegs mL m1) by exact (wmono_trans bsegs _ _ _ WML WM).
  assert (AGL : agree_on (fun x => aclient (rt_live RT Σ) (rt_frames RT Σ) (S1a + 384) x /\ outside (od_Wk E) x) mL m1).
  { intros a [Ha Ho]. rewrite (MU a); [exact (KEEP a Ha Ho)|].
    unfold od_W. unfold od_Wk in Ho. cbn [outside] in *. split; [| exact Ho].
    destruct (aclient_split_c RT AF Σ (o_m0 E) (S1a + 384) (bv_unsigned a) ART0 Ha) as [H|H]; [clear - H; fold S1a; lia|].
    clear - H LOW. fold lo. lia. }
  assert (ACS : forall x, S1a + 384 <= x < usp -> aclient (rt_live RT Σ) (rt_frames RT Σ) (S1a + 384) x /\ outside (od_Wk E) x).
  { intros x Hx. split; [left; clear - Hx GS; lia|]. unfold od_Wk. cbn [outside]. fold F SB CAP. clear - Hx GS. lia. }
  assert (ACF : forall x, F <= x < F + 192 -> aclient (rt_live RT Σ) (rt_frames RT Σ) (S1a + 384) x /\ outside (od_Wk E) x).
  { intros x Hx. split; [right; right; right; left; exists F, 3%nat; split; [exact INF|]; change (fs_size 3) with 512; clear - Hx; lia|].
    unfold od_Wk. cbn [outside]. fold F SB CAP. clear - Hx F_S. lia. }
  assert (ACH : forall x, F / 8 + 2147450880 <= x < F / 8 + 2147450880 + 64 -> aclient (rt_live RT Σ) (rt_frames RT Σ) (S1a + 384) x /\ outside (od_Wk E) x).
  { intros x Hx. split; [right; right; right; right; exists F, 3%nat; split; [exact INF|]; change (fs_size 3) with 512; rewrite SHF; unfold shad, SHB; clear - Hx; lia|].
    unfold od_Wk. cbn [outside]. fold F SB CAP. clear - Hx FSD FS_S. lia. }
  assert (ACV : forall x, A <= x < A + 16 * size -> aclient (rt_live RT Σ) (rt_frames RT Σ) (S1a + 384) x /\ outside (od_Wk E) x).
  { intros x Hx. split; [right; right; left; exists A, (16 * size); split; [exact INVL| clear - Hx; lia]|].
    unfold od_Wk. cbn [outside]. fold F SB CAP. clear - Hx FAV SBA. lia. }
  assert (OPAD1 : stk bsegs m1 (S1a + 440) (usp - 104)).
  { apply (stk_agree bsegs mL m1 _ _ OPAD); [| exact WML1]. eapply agree_sub; [exact AGL|]. intros x Hx. cbv beta in *. apply ACS. clear - Hx. lia. }
  destruct (wr_at_rw_CB m1 S1a 8 (wr_at_transport bsegs mL m1 S1a 8 OLO0 WML1) ltac:(lia)) as (j0 & O0). change (Z.to_nat 8) with 8%nat in O0.
  clear OPAD OLO0. unfold fa_saved in OSAV. cbn [map repeat] in OSHV, OSHP, OSHD.
  rt_transport_with mL m1 AGL WML1 ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?VSZE in Hx; cbv beta;
      tl_dispatch Hx F A ltac:(apply ACS; clear - Hx S1R; lia) ltac:(apply ACF; clear - Hx; lia)
                         ltac:(apply ACH; clear - Hx; lia) ltac:(apply ACV; clear - Hx VSZ; lia)).

  assert (L0IN : forall e, In e L0 -> In e (rt_live RT Σ)) by (intros e He; rewrite LV; do 6 right; apply in_or_app; right; exact He).
  assert (CP1 : forall a : word, aclient L0 [] usp (bv_unsigned a) -> m1 a = mL a).
  { intros a Ha. apply AGL. split.
    - eapply aclient_mono; [exact Ha| exact L0IN| intros e []| clear - GS; lia].
    - unfold od_Wk. cbn [outside]. fold F SB CAP. destruct Ha as [H|[H|[H|[H|H]]]].
      + clear - H GS. lia.
      + pose proof (client_static_range _ H) as CR. clear - CR FB SBD. ul.
      + destruct H as (p & n & Hin & Hp). pose proof (FLV p n (L0IN _ Hin)) as D1.
        assert (D4 : SB + CAP <= p \/ p + n <= SB).
        { apply (af_live_disj RT AF Σ m1 SB CAP p n [(IA, 1024); (OC, 8192); (IDX, 4 * Z.of_nat (o_icap E)); (IMPL, 96)]
                   ((COPY, NCOPY) :: vblockA A cap size ++ L0) ART1 LV). apply in_or_app. right. right. apply in_or_app. right. exact Hin. }
        clear - Hp D1 D4. lia.
      + destruct H as (f & k & [] & _).
      + destruct H as (f & k & [] & _). }

  assert (VR1 : vrepA m1 (F + 32) A cap size els).
  { unfold vrepA, zlength. split; [exact VSZ|]. split; [exact VSC|]. split; [exact VCAP|]. split; [exact VA0|]. split; [exact VAT|].
    split; [exact VS|]. right. split; [exact CAP1|]. split; [exact A16|]. split; [exact APOS| exact VEL]. }
  eapply (od_exit_inv RT AF PMc FDO MST RTF DELA DTOR VDES AFV Σ K E A cap size IA OC els L0 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11
            st vs v88 v144 v152 v240 v312 v336 v352);
    [ exact OK | exact ETP | exact LOW | exact FRM | exact ART1 | exact FRS | exact LV | exact LPOS | exact INV0
    | exact O0 | exact OHI | exact OPAD1 | exact OSAV | exact OHDR | exact VR1 | exact CAP1 | exact SZ1
    | exact OWRS | exact OSHV | exact OSHP | exact OSHD | exact LPRE | exact LMID | exact LREST | exact ODL | ].
  unfold od_ret_k. intros Σ' r0 r1 r2 q1 q2 q3 q4 q5 q6 q7 r3 r4 r5 r6 F' fc' m' FRM' ART' MI' ST' PR' LV' FRS' SP' CR'.
  apply HK; [exact FRM'| exact ART'| exact MI'| exact ST'| | | rewrite LV'; exact EL0| exact FRS'| rewrite SP'; exact SP0
            | rewrite CR'; exact HCB].
  - intros a Ha Ho. rewrite <- EL0 in Ha. rewrite (PR' a Ha I). rewrite (CP1 a Ha). exact (OPRES a Ha Ho).
  - apply (LIB_agree mL m' OLIB). intros a Ha. pose proof (lib_fp_static _ Ha) as CS.
    assert (AC : aclient L0 [] usp (bv_unsigned a)) by (right; left; exact CS).
    rewrite (PR' a AC I). exact (CP1 a AC).
Qed.

End Exit.
