(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep Frame.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_libiface Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_hkit3A Atp_hkit4A Pj_rtkA Pj_defsA Pj_cpsA Pj_copyA Pj_ser_trefA Pj_ser_defsA Pj_ser_kitA Pj_ser_callsA Pj_ser_numdefsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma u8arr_write_le1 : forall (m : mem) A bs (i : Z) (v : word) a,
  u8arr bsegs m A bs -> (0 <= i < Z.of_nat (length bs))%Z -> a = wa (A + i) ->
  u8arr bsegs (write_to_mem m a (le1 v)) A (upd bs (Z.to_nat i) (Z_to_bv 8 (bv_unsigned v))).
Proof.
  intros m A bs i v a U Hi ->.
  assert (E1 : le1 v = [Z_to_bv 8 (bv_unsigned v)]) by reflexivity.
  rewrite E1. apply u8arr_write; [exact U| exact Hi].
Qed.
Lemma zb8_m8 : Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-8))) = Z_to_bv 8 248.
Proof. apply bv_eq. reflexivity. Qed.

Lemma f3_acc_run : forall (m : mem) (f : Z) (shp : list byte) (g k : nat),
  u8arr bsegs m (f / 8 + 2147450880) shp -> (forall j, (j < k)%nat -> nth_error shp (g + j)%nat = Some z8) ->
  8 * (f / 8) = f -> 0 <= f -> acc bsegs m (f + 8 * Z.of_nat g) (8 * Z.of_nat k).
Proof.
  intros m f shp g k [HB _] N Ef F0 i Hi. exists z8. split; [| left; reflexivity].
  assert (J : 0 <= i / 8 < Z.of_nat k) by (Z.div_mod_to_equations; lia).
  assert (SH : shad (f + 8 * Z.of_nat g + i) = f / 8 + 2147450880 + Z.of_nat (g + Z.to_nat (i / 8))) by (unfold shad, SHB; Z.div_mod_to_equations; lia).
  assert (Hn : nth_error shp (g + Z.to_nat (i / 8))%nat = Some z8) by (apply N; clear - J; lia).
  rewrite SH. exact (bytes_at_nth1 bsegs m _ shp (g + Z.to_nat (i / 8)) z8 HB Hn).
Qed.

Lemma f3_shz5 : forall (m : mem) (f : Z) (shp : list byte) (g : nat),
  u8arr bsegs m (f / 8 + 2147450880) shp -> (forall j, (j < 5)%nat -> nth_error shp (g + j)%nat = Some z8) ->
  8 * (f / 8) = f -> 0 <= f -> bytes_at bsegs m (shad (f + 8 * Z.of_nat g)) (repeat z8 5).
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

Lemma ser_tocharsA : forall E D I w xs shp isobj Σ st m (K : config -> Prop) (X rpc : Z) (F : bvmap 5 word) (fc : bv 32)
    (xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word),
  pjenvA_ok E -> sctxA E D I -> SERMA RT E I w xs shp isobj Σ st m ->
  (forall j, (j < 5)%nat -> nth_error shp (4 + j)%nat = Some z8) ->
  frm0 fc -> CREDA RT E I Σ X st -> 1 <= X -> 0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
  (forall (Σ' : rts RT) (e : Z) (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
     SERMA RT E I w xs shp isobj Σ' st m' -> CREDA RT E I Σ' (X - 1) st -> frm0 fc' ->
     si_f I + 32 < e <= si_f I + 59 ->
     aevt Σ' K (SSTA I rpc (wz rpc) yt0 yt1 yt2 (wz e) ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 yt3 yt4 yt5 yt6 F' fc' m')) ->
  aevt Σ K (SSTA I PJ_TOCHARS_A (wz rpc) xt0 xt1 xt2 (wz (si_f I + 32)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
                xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST TOCHARS.
  intros until xt6. intros OK CX HSM SH5 FRM CR X1 RP0 RP2 HK.
  pose proof HSM as [HR HC]. pose proof HR as (ART0 & LV & FR & SP & DR & SBSH & PU & PRES0).
  pose proof HC as (_ & _ & _ & _ & F3S & _ & _ & SHF & SHL & _ & SV & SZ & BUFS & INLS & MI & ST).
  pose proof (SBINVA_of_SERMA RT E D I _ _ _ _ Σ st m OK CX HSM) as INV.
  pose proof (pj_psi_nonneg E m st OK INV) as PSI0.
  pose proof (c_lo E D I CX) as LOQ. unfold ser_needA, PJ_TC_STACK_A, RT_STACK in LOQ. pose proof (c_dd E D I CX) as DD. pose proof (c_qtop E D I CX) as QT.
  pose proof (c_b32 E D I CX) as B32. pose proof (c_sp0 E D I CX) as (W1 & W2). pose proof (c_frl E D I CX) as FRL. pose proof (c_R E D I CX) as R0.
  pose proof (c_f E D I CX) as (F0 & F64 & FSG & FLO). pose proof (env_div8 E D I OK CX) as (_ & EF & Ef & ESB & EFS & Efs & _).
  assert (INF3 : In (si_f I, 3%nat) (rt_frames RT Σ)) by (rewrite FR; left; reflexivity).
  destruct (stk_split bsegs m _ (si_f I + 32) _ F3S ltac:(clear; lia)) as [SLO SREST].
  destruct (stk_split bsegs m _ (si_f I + 72) _ SREST ltac:(clear; lia)) as [SMID SHI].
  destruct (stk_CB bsegs m _ _ SMID ltac:(clear; lia)) as (junk & NBC).
  replace (si_f I + 72 - (si_f I + 32)) with 40 in NBC by (clear; lia).
  pose proof (f3_shz5 m (si_f I) shp 4 SHF SH5 Ef ltac:(clear - F0; lia)) as SHZ5.
  replace (si_f I + 8 * Z.of_nat 4) with (si_f I + 32) in SHZ5 by (clear; lia).
  unfold CREDA in CR.
  eapply (TOCHARS Σ K (si_f I + 32) (si_b I) (pa_lo E) (si_f I) 3%nat (wz rpc) (si_gp I) xt0 xt1 xt2 (wz (si_q I)) (wz (si_b I))
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
            (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) (si_b I) x /\ ~ (si_f I + 32 <= x < si_f I + 72)) -> agree_on P m m').
  { intros P HP a Ha. destruct (HP _ Ha) as [H1 H2]. apply (PRES' a H1). cbn [outside]. split; [clear - H2; lia| exact Logic.I]. }
  assert (PRESW : rt_pres_fp (pa_L E) (rt_frames RT Σ) (si_b I) [(si_f I + 32, si_f I + 72)] m m').
  { intros a Ha Ho. apply PRES'; [| cbn [outside] in Ho |- *; split; [clear - Ho; lia| exact Logic.I]].
    eapply aclient_mono; [exact Ha| rewrite LV; intros y Hy; apply in_or_app; right; exact Hy| intros y Hy; exact Hy| clear; lia]. }
  eapply (SERMA_after_call RT AF E D I w xs shp isobj Σ Σ' st st m m' [(si_f I + 32, si_f I + 72)]);
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
  - eapply (stk_merge _ _ _ (si_f I + 32)); [| | clear; lia].
    + eapply stk_agree_nw; [exact SLO|]. apply AGB. intros x Hx. split; [| clear - Hx; lia].
      right; right; right; left. exists (si_f I), 3%nat. split; [exact INF3| rewrite fs3; clear - Hx; lia].
    + eapply (stk_merge _ _ _ (si_f I + 72)); [| | clear; lia].
      * pose proof (stk_of_rw_cells bsegs _ _ _ NB') as S. cbn [cells_size csize Nat.add] in S.
        replace (si_f I + 32 + Z.of_nat 40) with (si_f I + 72) in S by (clear; lia). exact S.
      * eapply stk_agree_nw; [exact SHI|]. apply AGB. intros x Hx. split; [| clear - Hx; lia].
        right; right; right; left. exists (si_f I), 3%nat. split; [exact INF3| rewrite fs3; clear - Hx; lia].
Qed.
End ToChars.

Section Itoa.
Variable hpc : Z.
Hypothesis ITOA : itoa_cpsA RT PMc hpc.

Lemma f3_shz3 : forall (m : mem) (f : Z) (shp : list byte) (g : nat),
  u8arr bsegs m (f / 8 + 2147450880) shp -> (forall j, (j < 3)%nat -> nth_error shp (g + j)%nat = Some z8) ->
  8 * (f / 8) = f -> 0 <= f -> bytes_at bsegs m (shad (f + 8 * Z.of_nat g)) (repeat z8 3).
Proof.
  intros m f shp g [(B0 & B1 & HB) _] N Ef F0.
  assert (L : (g + 3 <= length shp)%nat).
  { destruct (Nat.le_gt_cases (g + 3) (length shp)) as [|C]; [assumption| exfalso].
    pose proof (N 2%nat ltac:(lia)) as X. assert (Y : (g + 2 < length shp)%nat) by (apply nth_error_Some; congruence). lia. }
  assert (SH : shad (f + 8 * Z.of_nat g) = f / 8 + 2147450880 + Z.of_nat g) by (unfold shad, SHB; Z.div_mod_to_equations; lia).
  rewrite SH. split; [lia|]. split; [cbn [repeat length]; lia|].
  intros i Hi. cbn [repeat length] in Hi.
  replace (f / 8 + 2147450880 + Z.of_nat g + Z.of_nat i) with (f / 8 + 2147450880 + Z.of_nat (g + i)) by lia.
  rewrite (HB (g + i)%nat ltac:(lia)), (N i Hi).
  destruct i as [|[|[|i]]]; [reflexivity| reflexivity| reflexivity| lia].
Qed.

Lemma ser_itoaA : forall (g : nat) E D I w xs shp isobj Σ st m (K : config -> Prop) (X rpc v : Z) (F : bvmap 5 word) (fc : bv 32)
    (xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word),
  pjenvA_ok E -> sctxA E D I -> SERMA RT E I w xs shp isobj Σ st m ->
  (forall j, (j < 3)%nat -> nth_error shp (g + j)%nat = Some z8) -> (3 <= g)%nat -> (g <= 35)%nat ->
  CREDA RT E I Σ X st -> 1 <= X -> 0 <= rpc < 2^64 -> rpc mod 2 = 0 -> 0 <= v < 2^64 ->
  (forall (Σ' : rts RT) (e : Z) (m' : mem) (F' : bvmap 5 word) (yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
     SERMA RT E I w xs shp isobj Σ' st m' -> CREDA RT E I Σ' (X - 1) st ->
     si_f I + 8 * Z.of_nat g < e <= si_f I + 8 * Z.of_nat g + 20 ->
     aevt Σ' K (SSTA I rpc (wz rpc) yt0 yt1 yt2 (wz e) ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 yt3 yt4 yt5 yt6 F' fc m')) ->
  aevt Σ K (SSTA I hpc (wz rpc) xt0 xt1 xt2 (wz (si_f I + 8 * Z.of_nat g)) (wz v) xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
                xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST ITOA.
  intros until xt6. intros OK CX HSM SH3 G3 G35 CR X1 RP0 RP2 V64 HK.
  pose proof HSM as [HR HC]. pose proof HR as (ART0 & LV & FR & SP & DR & SBSH & PU & PRES0).
  pose proof HC as (_ & _ & _ & _ & F3S & _ & _ & SHF & SHL & _ & SV & SZ & BUFS & INLS & MI & ST).
  pose proof (SBINVA_of_SERMA RT E D I _ _ _ _ Σ st m OK CX HSM) as INV.
  pose proof (pj_psi_nonneg E m st OK INV) as PSI0.
  pose proof (c_lo E D I CX) as LOQ. unfold ser_needA, PJ_TC_STACK_A, RT_STACK in LOQ. pose proof (c_dd E D I CX) as DD. pose proof (c_qtop E D I CX) as QT.
  pose proof (c_b32 E D I CX) as B32. pose proof (c_sp0 E D I CX) as (W1 & W2). pose proof (c_frl E D I CX) as FRL. pose proof (c_R E D I CX) as R0.
  pose proof (c_f E D I CX) as (F0 & F64 & FSG & FLO). pose proof (env_div8 E D I OK CX) as (_ & EF & Ef & ESB & EFS & Efs & _).
  assert (INF3 : In (si_f I, 3%nat) (rt_frames RT Σ)) by (rewrite FR; left; reflexivity).
  set (DST := si_f I + 8 * Z.of_nat g) in *.
  destruct (stk_split bsegs m _ DST _ F3S ltac:(subst DST; clear - G3 G35; lia)) as [SLO SREST].
  destruct (stk_split bsegs m _ (DST + 24) _ SREST ltac:(subst DST; clear - G3 G35; lia)) as [SMID SHI].
  destruct (stk_CB bsegs m _ _ SMID ltac:(clear; lia)) as (junk & NBC).
  replace (DST + 24 - DST) with 24 in NBC by (clear; lia).
  pose proof (f3_shz3 m (si_f I) shp g SHF SH3 Ef ltac:(clear - F0; lia)) as SHZ3. fold DST in SHZ3.
  unfold CREDA in CR.
  eapply (ITOA Σ K DST (si_b I) (pa_lo E) v (si_f I) 3%nat (wz rpc) (si_gp I) xt0 xt1 xt2 (wz (si_q I)) (wz (si_b I))
            xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m junk FDO MST INF3);
    [subst DST; clear - G3; lia| subst DST; rewrite fs3; clear - G35; lia| subst DST; clear - F64; dlia| exact NBC| exact SHZ3| exact ART0| exact MI| exact ST| rewrite SP; exact W1
    | unfold si_b, PJ_ITOA_STACK_A, RT_STACK; clear - LOQ DD; lia| unfold si_b, USTACK_TOP in *; clear - QT DD; lia| clear - B32; unfold si_b in *; dlia| exact V64
    | rewrite FR; cbn [length]; clear - FRL; lia| clear - CR X1 R0 PSI0; lia|].
  intros Σ' e t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m' nb ART' MI' ST' LV' FR' SP' CR' PRES' HE NB'.
  rewrite (ret_pc_even rpc RP0 RP2). apply (HK Σ' e m' F'); [| unfold CREDA; clear - CR CR'; lia| exact HE].

  pose proof (buf_factsA RT AF E D I Σ st m (si_b I) OK CX HR) as (BL & B0 & RCB & CLB & APB).
  pose proof (sb_pureA_ranges E st OK PU) as (_ & _ & _ & R3).
  pose proof (env_rangesA E OK) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FS & B1 & B2 & _ & _ & FL & _).
  pose proof (c_fF E D I CX) as FF. pose proof (c_F_shf E D I CX) as FSH1. pose proof (c_f_shF E D I CX) as FSH2. pose proof (c_F4 E D I CX) as IN4.
  assert (INF4 : In (pa_F E, pa_kF E) (rt_frames RT Σ)) by (rewrite FR; right; exact IN4).
  assert (AGB : forall P : Z -> Prop,
            (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) (si_b I) x /\ ~ (DST <= x < DST + 24)) -> agree_on P m m').
  { intros P HP a Ha. destruct (HP _ Ha) as [H1 H2]. apply (PRES' a H1). cbn [outside]. split; [clear - H2; lia| exact Logic.I]. }
  assert (PRESW : rt_pres_fp (pa_L E) (rt_frames RT Σ) (si_b I) [(DST, DST + 24)] m m').
  { intros a Ha Ho. apply PRES'; [| cbn [outside] in Ho |- *; split; [clear - Ho; lia| exact Logic.I]].
    eapply aclient_mono; [exact Ha| rewrite LV; intros y Hy; apply in_or_app; right; exact Hy| intros y Hy; exact Hy| clear; lia]. }
  eapply (SERMA_after_call RT AF E D I w xs shp isobj Σ Σ' st st m m' [(DST, DST + 24)]);
    [exact OK| exact CX| exact HSM| | | exact PRESW| exact ART'| exact MI'| exact ST'| rewrite LV'; exact LV| exact FR'| exact SP'| exact PU| | | exact SZ| | | ].
  - intros x Hx. unfold serWA in Hx. cbn [outside] in Hx |- *. split; [subst DST; clear - Hx G3 G35; lia| exact Logic.I].
  - pose proof (c_f_shf E D I CX) as FSH0.
    intros x Hx. cbn [outside]. split; [| exact Logic.I]. unfold si_b in Hx. subst DST. clear - Hx FLO LOQ DD FSH0 G3 G35. lia.
  - eapply bytes_at_agree; [exact SBSH|]. apply AGB. intros x Hx. rewrite repeat_length in Hx. split.
    + right; right; right; right. exists (pa_F E), (pa_kF E). split; [exact INF4|]. unfold shad, SHB in Hx |- *. rewrite EFS. clear - Hx ESB EF Efs B1 B2. lia.
    + unfold shad, SHB in Hx. subst DST. clear - Hx FSH2 ESB EF Efs EFS B1 B2 G3 G35. lia.
  - eapply rw_cells_agree_nw; [exact SV|]. apply AGB. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split.
    + right; right; right; left. exists (pa_F E), (pa_kF E). split; [exact INF4| clear - Hx B1 B2; lia].
    + subst DST. clear - Hx FF B1 B2 G3 G35. lia.
  - eapply stk_agree_nw; [exact BUFS|]. apply AGB. intros x Hx. split; [apply CLB; exact Hx|].
    destruct (APB x Hx) as (A1 & _). subst DST. clear - A1 G3 G35. lia.
  - eapply stk_agree_nw; [exact INLS|]. apply AGB. intros x Hx. split.
    + right; right; right; left. exists (pa_F E), (pa_kF E). split; [exact INF4| clear - Hx B1 B2; lia].
    + subst DST. clear - Hx FF B1 B2 G3 G35. lia.
  - eapply (stk_merge _ _ _ DST); [| | subst DST; clear - G3 G35; lia].
    + eapply stk_agree_nw; [exact SLO|]. apply AGB. intros x Hx. split; [| clear - Hx; lia].
      right; right; right; left. exists (si_f I), 3%nat. split; [exact INF3| rewrite fs3; subst DST; clear - Hx G35; lia].
    + eapply (stk_merge _ _ _ (DST + 24)); [| | subst DST; clear - G3 G35; lia].
      * pose proof (stk_of_rw_cells bsegs _ _ _ NB') as S. cbn [cells_size csize Nat.add] in S.
        replace (DST + Z.of_nat 24) with (DST + 24) in S by (clear; lia). exact S.
      * eapply stk_agree_nw; [exact SHI|]. apply AGB. intros x Hx. split; [| clear - Hx; lia].
        right; right; right; left. exists (si_f I), 3%nat. split; [exact INF3| rewrite fs3; subst DST; clear - Hx G3; lia].
Qed.
End Itoa.

End NCalls.
