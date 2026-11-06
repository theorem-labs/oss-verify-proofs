(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep Frame.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim SjModel PjModel.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.A Require Import Layout Shadow RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_libiface
     Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_hkit3A Atp_hkit4A Pj_rtkA Pj_defsA Pj_cpsA Pj_ser_defsA Pj_ser_kitA Pj_ser_callsA Pj_ser_intkA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma f3_acc_run : forall (m : mem) (f : Z) (shp : list byte) (g k : nat),
  u8arr asegs m (f / 8 + 2147450880) shp -> (forall j, (j < k)%nat -> nth_error shp (g + j)%nat = Some z8) ->
  8 * (f / 8) = f -> 0 <= f -> acc asegs m (f + 8 * Z.of_nat g) (8 * Z.of_nat k).
Proof.
  intros m f shp g k [HB _] N Ef F0 i Hi. exists z8. split; [| left; reflexivity].
  assert (J : 0 <= i / 8 < Z.of_nat k) by (Z.div_mod_to_equations; lia).
  assert (SH : shad (f + 8 * Z.of_nat g + i) = f / 8 + 2147450880 + Z.of_nat (g + Z.to_nat (i / 8))) by (unfold shad, SHB; Z.div_mod_to_equations; lia).
  assert (Hn : nth_error shp (g + Z.to_nat (i / 8))%nat = Some z8) by (apply N; clear - J; lia).
  rewrite SH. exact (bytes_at_nth1 asegs m _ shp (g + Z.to_nat (i / 8)) z8 HB Hn).
Qed.

Lemma f3_shz5 : forall (m : mem) (f : Z) (shp : list byte) (g : nat),
  u8arr asegs m (f / 8 + 2147450880) shp -> (forall j, (j < 5)%nat -> nth_error shp (g + j)%nat = Some z8) ->
  8 * (f / 8) = f -> 0 <= f -> bytes_at asegs m (shad (f + 8 * Z.of_nat g)) (repeat z8 5).
Proof.
  intros m f shp g [(B0 & B1 & HB) _] N Ef F0.
  assert (L : (g + 5 <= length shp)%nat).
  { destruct (Nat.le_gt_cases (g + 5) (length shp)) as [|C]; [assumption| exfalso].
    pose proof (N 4%nat ltac:(lia)) as X. assert (Y : (g + 4 < length shp)%nat) by (apply nth_error_Some; congruence). lia. }
  assert (SH : shad (f + 8 * Z.of_nat g) = f / 8 + 2147450880 + Z.of_nat g) by (unfold shad, SHB; Z.div_mod_to_equations; lia).
  rewrite SH. split; [lia|]. split; [cbn [repeat length]; lia|].
  intros i Hi. cbn [repeat length] in Hi.
  replace (f / 8 + 2147450880 + Z.of_nat g + Z.of_nat i) with (f / 8 + 2147450880 + Z.of_nat (g + i)) by lia.
  rewrite (HB (g + i)%nat ltac:(lia)), (N i Hi).
  destruct i as [|[|[|[|[|i]]]]]; [reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| lia].
Qed.

Section NCalls.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Notation aevt := (aevt RT PMc).
Local Ltac dlia := Z.div_mod_to_equations; lia.

Section ToChars.
Hypothesis TOCHARS : tochars_cpsA RT PMc.

Lemma ser_tocharsA : forall E D I w168 w224 w232 w240 xs shp isobj Σ st m (K : config -> Prop) (X rpc : Z) (F : bvmap 5 word) (fc : bv 32)
    (xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word),
  pjenvA_ok E -> sctxA E D I -> SERMA RT E I w168 w224 w232 w240 xs shp isobj Σ st m ->
  (forall j, (j < 5)%nat -> nth_error shp (20 + j)%nat = Some z8) ->
  frm0 fc -> CREDA RT E I Σ X st -> 1 <= X -> 0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
  (forall (Σ' : rts RT) (e : Z) (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
     SERMA RT E I w168 w224 w232 w240 xs shp isobj Σ' st m' -> CREDA RT E I Σ' (X - 1) st -> frm0 fc' ->
     si_f I + 160 < e <= si_f I + 187 ->
     aevt Σ' K (SSTA I rpc (wz rpc) yt0 yt1 yt2 (wz e) ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 yt3 yt4 yt5 yt6 F' fc' m')) ->
  aevt Σ K (SSTA I PJ_TOCHARS_A (wz rpc) xt0 xt1 xt2 (wz (si_f I + 160)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
                xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST TOCHARS.
  intros until xt6. intros OK CX HSM SH5 FRM CR X1 RP0 RP2 HK.
  pose proof HSM as [HR HC]. pose proof HR as (ART0 & LV & FR & SP & DR & SBSH & PU & PRES0).
  pose proof HC as (_ & _ & _ & _ & F3S & _ & _ & SHF & SHL & _ & SV & SZ & BUFS & INLS & MI & ST).
  pose proof (SBINVA_of_SERMA RT E D I _ _ _ _ _ _ _ Σ st m OK CX HSM) as INV.
  pose proof (pj_psi_nonneg E m st OK INV) as PSI0.
  pose proof (c_lo E D I CX) as LOQ. unfold ser_needA, PJ_TC_STACK_A, RT_STACK in LOQ. pose proof (c_dd E D I CX) as DD. pose proof (c_qtop E D I CX) as QT.
  pose proof (c_b32 E D I CX) as B32. pose proof (c_sp0 E D I CX) as (W1 & W2). pose proof (c_frl E D I CX) as FRL. pose proof (c_R E D I CX) as R0.
  pose proof (c_f E D I CX) as (F0 & F64 & FSG & FLO). pose proof (env_div8 E D I OK CX) as (_ & EF & Ef & ESB & EFS & Efs & _).
  assert (INF3 : In (si_f I, 3%nat) (rt_frames RT Σ)) by (rewrite FR; left; reflexivity).
  destruct (stk_split asegs m _ (si_f I + 160) _ F3S ltac:(clear; lia)) as [SLO SREST].
  destruct (stk_split asegs m _ (si_f I + 200) _ SREST ltac:(clear; lia)) as [SMID SHI].
  destruct (stk_CB asegs m _ _ SMID ltac:(clear; lia)) as (junk & NBC).
  replace (si_f I + 200 - (si_f I + 160)) with 40 in NBC by (clear; lia).
  pose proof (f3_shz5 m (si_f I) shp 20 SHF SH5 Ef ltac:(clear - F0; lia)) as SHZ5.
  replace (si_f I + 8 * Z.of_nat 20) with (si_f I + 160) in SHZ5 by (clear; lia).
  unfold CREDA in CR.
  eapply (TOCHARS Σ K (si_f I + 160) (si_b I) (pa_lo E) (si_f I) 3%nat (wz rpc) (si_gp I) xt0 xt1 xt2 (wz (si_q I)) (wz (si_b I))
            xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m junk FDO MST INF3);
    [clear; lia| rewrite fs3; clear; lia| clear - F64; dlia| exact NBC| exact SHZ5| exact ART0| exact MI| exact ST| rewrite SP; exact W1
    | unfold si_b, PJ_TC_STACK_A, RT_STACK; clear - LOQ DD; lia| unfold si_b, USTACK_TOP in *; clear - QT DD; lia| clear - B32; unfold si_b in *; dlia| exact FRM
    | rewrite FR; cbn [length]; clear - FRL; lia| clear - CR X1 R0 PSI0; lia|].
  intros Σ' e t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' nb FRM' ART' MI' ST' LV' FR' SP' CR' PRES' HE NB'.
  rewrite (ret_pc_even rpc RP0 RP2). apply (HK Σ' e m' F' fc'); [| unfold CREDA; clear - CR CR'; lia| exact FRM'| clear - HE; lia].

  pose proof (buf_factsA RT AF E D I Σ st m (si_b I) OK CX HR) as (BL & B0 & RCB & CLB & APB).
  pose proof (sb_pureA_ranges E st OK PU) as (_ & _ & _ & R3).
  pose proof (env_rangesA E OK) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FS & B1 & B2 & _ & _ & FL & _).
  pose proof (c_fF E D I CX) as FF. pose proof (c_F_shf E D I CX) as FSH1. pose proof (c_f_shF E D I CX) as FSH2. pose proof (c_F4 E D I CX) as IN4.
  assert (INF4 : In (pa_F E, pa_kF E) (rt_frames RT Σ)) by (rewrite FR; right; exact IN4).
  assert (AGB : forall P : Z -> Prop,
            (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) (si_b I) x /\ ~ (si_f I + 160 <= x < si_f I + 200)) -> agree_on P m m').
  { intros P HP a Ha. destruct (HP _ Ha) as [H1 H2]. apply (PRES' a H1). cbn [outside]. split; [clear - H2; lia| exact Logic.I]. }
  assert (PRESW : rt_pres_fp (pa_L E) (rt_frames RT Σ) (si_b I) [(si_f I + 160, si_f I + 200)] m m').
  { intros a Ha Ho. apply PRES'; [| cbn [outside] in Ho |- *; split; [clear - Ho; lia| exact Logic.I]].
    eapply aclient_mono; [exact Ha| rewrite LV; intros y Hy; apply in_or_app; right; exact Hy| intros y Hy; exact Hy| clear; lia]. }
  eapply (SERMA_after_call RT AF E D I w168 w224 w232 w240 xs shp isobj Σ Σ' st st m m' [(si_f I + 160, si_f I + 200)]);
    [exact OK| exact CX| exact HSM| | | exact PRESW| exact ART'| exact MI'| exact ST'| rewrite LV'; exact LV| exact FR'| exact SP'| exact PU| | | exact SZ| | | ].
  - intros x Hx. unfold serWA in Hx. cbn [outside] in Hx |- *. split; [clear - Hx; lia| exact Logic.I].
  - pose proof (c_f_shf E D I CX) as FSH0.
    intros x Hx. cbn [outside]. split; [| exact Logic.I]. unfold si_b in Hx. clear - Hx FLO LOQ DD FSH0. lia.
  - eapply bytes_at_agree; [exact SBSH|]. apply AGB. intros x Hx. rewrite repeat_length in Hx. split.
    + right; right; right; right. exists (pa_F E), (pa_kF E). split; [exact INF4|]. unfold shad, SHB in Hx |- *. rewrite EFS. clear - Hx ESB EF Efs B1 B2. lia.
    + unfold shad, SHB in Hx. clear - Hx FSH2 ESB EF Efs EFS B1 B2. lia.
  - eapply rw_cells_agree_nw; [exact SV|]. apply AGB. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split.
    + right; right; right; left. exists (pa_F E), (pa_kF E). split; [exact INF4| clear - Hx B1 B2; lia].
    + clear - Hx FF B1 B2. lia.
  - eapply stk_agree_nw; [exact BUFS|]. apply AGB. intros x Hx. split; [apply CLB; exact Hx|].
    destruct (APB x Hx) as (A1 & _). clear - A1. lia.
  - destruct R3 as [(BL' & HP)|(EB & EC & HP)].
    + eapply stk_agree_nw; [exact INLS|]. apply AGB. intros x Hx. split.
      * right; right; right; left. exists (pa_F E), (pa_kF E). split; [exact INF4| clear - Hx B1 B2; lia].
      * clear - Hx FF B1 B2. lia.
    + eapply stk_agree_nw; [exact INLS|]. apply AGB. intros x Hx. split.
      * right; right; right; left. exists (pa_F E), (pa_kF E). split; [exact INF4| clear - Hx B1 B2; lia].
      * clear - Hx FF B1 B2. lia.
  - eapply (stk_merge _ _ _ (si_f I + 160)); [| | clear; lia].
    + eapply stk_agree_nw; [exact SLO|]. apply AGB. intros x Hx. split; [| clear - Hx; lia].
      right; right; right; left. exists (si_f I), 3%nat. split; [exact INF3| rewrite fs3; clear - Hx; lia].
    + eapply (stk_merge _ _ _ (si_f I + 200)); [| | clear; lia].
      * pose proof (stk_of_rw_cells asegs _ _ _ NB') as S. cbn [cells_size csize Nat.add] in S.
        replace (si_f I + 160 + Z.of_nat 40) with (si_f I + 200) in S by (clear; lia). exact S.
      * eapply stk_agree_nw; [exact SHI|]. apply AGB. intros x Hx. split; [| clear - Hx; lia].
        right; right; right; left. exists (si_f I), 3%nat. split; [exact INF3| rewrite fs3; clear - Hx; lia].
Qed.
End ToChars.

Theorem f3copy_okA : f3copy_stmtA RT PMc.
Proof using AF RC FDO MST.
  unfold f3copy_stmtA.
  intros E D I w168 w224 w232 w240 xs shp isobj Σ st m K Dst Src n rpc bs F fc
         xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6
         OK CX HSM BY LEN N1 S1 S2 D1 D2 ACS ACD APT RP0 RP2 HK.
  pose proof HSM as [HR HC]. pose proof HR as (ART0 & LV & FR & SP & DR & SBSH & PU & PRES0).
  pose proof HC as (_ & _ & _ & _ & F3S & _ & _ & SHF & SHL & _ & SV & SZ & BUFS & INLS & MI & ST).
  pose proof (c_lo E D I CX) as LOQ. unfold ser_needA, PJ_TC_STACK_A, RT_STACK in LOQ. pose proof (c_dd E D I CX) as DD. pose proof (c_qtop E D I CX) as QT.
  unfold USTACK_TOP in QT.
  pose proof (c_b32 E D I CX) as B32. pose proof (c_sp0 E D I CX) as (W1 & W2). pose proof (ok_lo E OK) as LOW.
  pose proof (c_f E D I CX) as (F0 & F64 & FSG & FLO).
  assert (INF3 : In (si_f I, 3%nat) (rt_frames RT Σ)) by (rewrite FR; left; reflexivity).
  assert (EU : bv_unsigned (wz (si_b I)) = si_b I) by (apply unsigned_lit; unfold si_b; clear - LOQ DD QT LOW; lia).
  subst n.
  assert (CS : checked_src RT Σ m (wz (si_b I)) (pa_lo E) Src (Z.of_nat (length bs))).
  { unfold checked_src. rewrite EU. split; [| left; clear - S2 FLO; lia]. intros _. split; [exact ACS|].
    right; left. exists (si_f I), 3%nat. split; [exact INF3| rewrite fs3; clear - S1 S2; lia]. }
  assert (CD : checked_dst RT Σ m (wz (si_b I)) Dst (Z.of_nat (length bs))).
  { unfold checked_dst. rewrite EU. split; [| split].
    - intros _. split; [exact ACD|]. right; left. exists (si_f I), 3%nat. split; [exact INF3| rewrite fs3; clear - D1 D2; lia].
    - intros i Hi. right; right; right; left. exists (si_f I), 3%nat. split; [exact INF3| rewrite fs3; clear - D1 D2 Hi; lia].
    - apply (stk_wr_at m _ _ _ _ F3S); clear - D1 D2; lia. }
  assert (COK : call_ok RT Σ m (wz (si_b I)) (pa_lo E)).
  { unfold call_ok. rewrite EU, SP. split; [exact ST|]. split; [exact W1|]. split; [unfold si_b, RT_STACK; clear - LOQ DD; lia|].
    split; [unfold si_b, USTACK_TOP; clear - QT DD; lia| clear - B32; dlia]. }
  eapply (aevt_memcpyP RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m Dst Src bs (pa_lo E)
            eq_refl eq_refl eq_refl); [| | | exact BY| exact CS| exact CD| exact APT| exact ART0| exact MI| exact COK|].
  - clear - D1 D2 F0 FLO LOQ QT LOW. lia.
  - clear - S1 S2 F0 FLO LOQ QT LOW. lia.
  - clear - D1 D2 N1. lia.
  - intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m' (ART' & MI' & WM' & ST') PRES' BY'. rewrite EU in ST', PRES'.
    rewrite (ret_pc_even rpc RP0 RP2). apply HK; [| exact BY'].
    assert (AGB : forall P : Z -> Prop,
              (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) (si_b I) x /\ ~ (Dst <= x < Dst + Z.of_nat (length bs))) -> agree_on P m m').
    { intros P HP a Ha. destruct (HP _ Ha) as [H1 H2]. exact (PRES' a H1 H2). }
    assert (PRESW : rt_pres_fp (pa_L E) (rt_frames RT Σ) (si_b I) [(Dst, Dst + Z.of_nat (length bs))] m m').
    { intros a Ha Ho. apply PRES'; [| cbn [outside] in Ho; exact (proj1 Ho)].
      eapply aclient_mono; [exact Ha| rewrite LV; intros y Hy; apply in_or_app; right; exact Hy| intros y Hy; exact Hy| clear; lia]. }
    pose proof (buf_factsA RT AF E D I Σ st m (si_b I) OK CX HR) as (BL & B0 & RCB & CLB & APB).
    pose proof (sb_pureA_ranges E st OK PU) as (_ & _ & _ & R3).
    pose proof (env_rangesA E OK) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FS & B1 & B2 & _ & _ & FL & _).
    pose proof (env_div8 E D I OK CX) as (_ & EF & Ef & ESB & EFS & Efs & _).
    pose proof (c_fF E D I CX) as FF. pose proof (c_F_shf E D I CX) as FSH1. pose proof (c_f_shF E D I CX) as FSH2. pose proof (c_F4 E D I CX) as IN4.
    pose proof (c_f_shf E D I CX) as FSH0.
    assert (INF4 : In (pa_F E, pa_kF E) (rt_frames RT Σ)) by (rewrite FR; right; exact IN4).
    eapply (SERMA_after_call RT AF E D I w168 w224 w232 w240 xs shp isobj Σ Σ st st m m' [(Dst, Dst + Z.of_nat (length bs))]);
      [exact OK| exact CX| exact HSM| | | exact PRESW| exact ART'| exact MI'| exact ST'| exact LV| reflexivity| reflexivity| exact PU| | | exact SZ| | | ].
    + intros x Hx. unfold serWA in Hx. cbn [outside] in Hx |- *. split; [clear - Hx D1 D2; lia| exact Logic.I].
    + intros x Hx. cbn [outside]. split; [| exact Logic.I]. unfold si_b in Hx. clear - Hx D1 D2 FLO LOQ DD FSH0. lia.
    + eapply bytes_at_agree; [exact SBSH|]. apply AGB. intros x Hx. rewrite repeat_length in Hx. split.
      * right; right; right; right. exists (pa_F E), (pa_kF E). split; [exact INF4|]. unfold shad, SHB in Hx |- *. rewrite EFS. clear - Hx ESB EF Efs B1 B2. lia.
      * unfold shad, SHB in Hx. clear - Hx D1 D2 FSH2 ESB EF Efs EFS B1 B2. lia.
    + eapply rw_cells_agree_nw; [exact SV|]. apply AGB. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split.
      * right; right; right; left. exists (pa_F E), (pa_kF E). split; [exact INF4| clear - Hx B1 B2; lia].
      * clear - Hx D1 D2 FF B1 B2. lia.
    + eapply stk_agree_nw; [exact BUFS|]. apply AGB. intros x Hx. split; [apply CLB; exact Hx|].
      destruct (APB x Hx) as (A1 & _). clear - A1 D1 D2. lia.
    + eapply stk_agree_nw; [exact INLS|]. apply AGB. intros x Hx. split.
      * right; right; right; left. exists (pa_F E), (pa_kF E). split; [exact INF4| clear - Hx B1 B2; lia].
      * clear - Hx D1 D2 FF B1 B2. lia.
    + destruct (stk_split asegs m _ Dst _ F3S ltac:(clear - D1 D2; lia)) as [SLO SREST].
      destruct (stk_split asegs m _ (Dst + Z.of_nat (length bs)) _ SREST ltac:(clear - D1 D2; lia)) as [SMID SHI].
      eapply (stk_merge _ _ _ Dst); [| | clear - D1 D2; lia].
      * eapply stk_agree_nw; [exact SLO|]. apply AGB. intros x Hx. split; [| clear - Hx; lia].
        right; right; right; left. exists (si_f I), 3%nat. split; [exact INF3| rewrite fs3; clear - Hx D2; lia].
      * eapply (stk_merge _ _ _ (Dst + Z.of_nat (length bs))); [apply (stk_of_bytes_wmono m m' _ bs BY' SMID WM')| | clear - D1 D2; lia].
        eapply stk_agree_nw; [exact SHI|]. apply AGB. intros x Hx. split; [| clear - Hx; lia].
        right; right; right; left. exists (si_f I), 3%nat. split; [exact INF3| rewrite fs3; clear - Hx D1; lia].
Qed.

End NCalls.
