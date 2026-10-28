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
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_libiface
     Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_hkit3A Atp_hkit4A Pj_rtkA Pj_defsA Pj_cpsA Pj_copyA Pj_ser_trefA Pj_ser_defsA Pj_ser_kitA Pj_ser_callsA Pj_ser_skitA
     Pj_ser_ncallsA Pj_ser_strA_b Pj_ser_strA_a Pj_ser_strA_e.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_store ::= first [ pj_solve_store0 | pj_store_wr ].
Local Ltac pj_st_eq_leaf ::=
  lazymatch goal with
  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | f_equal; cbn [length sa_buf sa_size sa_cap]; lia]
  | |- _ => reflexivity
  end.
Notation wz z := (Z_to_bv 64 z) (only parsing).
Notation M64M1 := 18446744073709551615 (only parsing).

Lemma lxor_ones64 : forall a, 0 <= a < 2 ^ 64 -> Z.lxor a 18446744073709551615 = 18446744073709551615 - a.
Proof.
  intros a Ha. rewrite (lnot_mod64 a Ha). unfold Z.lnot, Z.pred. change (2 ^ 64) with 18446744073709551616.
  Z.div_mod_to_equations. lia.
Qed.

Section Str.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis GROW : grow_cpsA RT PMc.
Notation aevt := (aevt RT PMc).

Section Pieces.
Variable E : pjenvA.
Variable D : nat.
Variable I : serI.
Variable K : config -> Prop.
Variable isobj : list byte.
Variables (i dp c l A X : Z).
Hypothesis OK : pjenvA_ok E.
Hypothesis CX : sctxA E D I.
Hypothesis Hi : 1 <= i < pa_n E.
Hypothesis HT : pa_T E i = tword t_str c.
Hypothesis HSTR : str_at (pa_S E) (pa_sn E) c l.
Hypothesis Hdp : 0 <= dp <= 15.
Hypothesis BUD : A + (2 + 6 * l) <= PJ_OUTMAX (pa_len E).
Hypothesis X0 : 0 <= X.
Hypothesis HK : av_KA RT PMc E I K isobj i dp X (A + (2 + 6 * l)).

Notation DATA := (pa_SBUF E + c + 4).
Notation sx := (Pj_ser_strA_a.sx E c).
Notation SERML x0 x8 x16 x288 x296 shp Σ st m := (SERMA RT E I (wkC E) (sx x0 x8 x16 x288 x296) shp isobj Σ st m).
Notation BSS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs7 xs11 xt3 xt4 xt5 xt6 F fc m :=
  (SSTA I pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (pa_SB E + 72)) xs3 (Z_to_bv 64 (shad (pa_SB E + 72))) (Z_to_bv 64 l) (Z_to_bv 64 i)
        xs7 (Z_to_bv 64 DATA) (Z_to_bv 64 2147450880) (Z_to_bv 64 dp) xs11 xt3 xt4 xt5 xt6 F fc m).

Notation HSS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xt3 xt4 xt5 xt6 F fc m :=
  (SSTA I pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (pa_SB E + 72)) xs3 (Z_to_bv 64 (shad (pa_SB E + 72))) xs5 (Z_to_bv 64 i)
        (Z_to_bv 64 PJ_NE_TAB_A) (Z_to_bv 64 DATA) (Z_to_bv 64 2147450880) (Z_to_bv 64 dp) (Z_to_bv 64 c) xt3 xt4 xt5 xt6 F fc m).
Definition hx (x0 x8 x16 x208 x288 x296 : word) : xjA :=
  mkXJ x0 x8 x16 (wz (tword t_str c)) (wz (pa_SBUF E)) x208 (wz (shad (pa_SB E + 80))) x288 x296.
Local Ltac slia := repeat match goal with H : _ \/ _ |- _ => clear H end; cbn [sa_size sa_cap sa_buf sa_heap sa_k]; lia.
Local Ltac cbnx := cbn [hx Pj_ser_strA_a.sx Pj_ser_defsA.xj0 Pj_ser_defsA.xj8 Pj_ser_defsA.xj16 Pj_ser_defsA.xj24 Pj_ser_defsA.xj80 Pj_ser_defsA.xj208 Pj_ser_defsA.xj216
                         Pj_ser_defsA.xj288 Pj_ser_defsA.xj296] in *.
Local Ltac sb_shz :=
  lazymatch goal with
  | HREF : SREFA _ _ _ _ _ ?mr, MU : munch _ ?mr ?mm, WM : wmono bsegs ?mr ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let SHZ := fresh "SHZ" in let R64 := fresh "RD64" in let R72 := fresh "RD72" in let R80 := fresh "RD80" in
    pose proof (shz_sb_mu RT AF E D I OK CX _ _ _ mm HREF MU WM) as SHZ;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 64) ltac:(clear; lia)) as R64;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 72) ltac:(clear; lia)) as R72;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 80) ltac:(clear; lia)) as R80; clear SHZ
  end.
Local Ltac open HSM := unfold Pj_ser_strA_a.sx, hx in HSM; ser_open HSM OK; cbnx.
Notation esc_headA := (Pj_ser_strA_e.esc_headA RT AF RC PMc FDO MST GROW E D I K isobj i dp c l A X OK CX Hi HT HSTR Hdp BUD X0 HK).
Notation str_closeA := (Pj_ser_strA_a.str_closeA RT AF RC PMc FDO MST GROW E D I K isobj i dp c l A X OK CX Hi HT HSTR Hdp BUD X0 HK).
Notation str_scan8A := (Pj_ser_strA_b.str_scan8A E D I i dp c l OK CX HSTR).
Notation str_tailA := (Pj_ser_strA_b.str_tailA E D I i dp c l OK CX HSTR).

Lemma copy_finA : forall (k : Z) x0 x8 x16 x288 x296 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
  0 <= k <= l ->
  SERML x0 x8 x16 x288 x296 ser_shpatA Σ st m -> frm0 fc -> sa_size st + k <= sa_cap st -> sa_size st <= A + 1 -> CREDA RT E I Σ X st ->
  aevt Σ K (BSS 0xba1e8 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (sa_size st + k)) (wz (pa_SB E + 80)) (wz k) xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST GROW OK CX Hi HT HSTR Hdp BUD X0 HK.
  intros k x0 x8 x16 x288 x296 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HKL HSM FRM ROOM ACC CR.
  pose proof HSTR as (C0 & L0 & CL & _).
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM. sb_shz.

  astep. astep. unbox FSB; unbox SHSB. step. box_disj. step.
  if_cases Kc; zify_cond Kc; pjnorm_in Kc.
  -
    ser_close HSM2 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (str_closeA x0 x8 x16 x288 x296 Σ (mkSbA buf (size + k) cap hp kk))]; try eassumption; try pj_st_eq; slia.
  -
    ser_close HSM2 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (esc_headA (Z.to_nat (l - k)) k x0 x8 x16 x288 x296 Σ (mkSbA buf (size + k) cap hp kk))]; try eassumption; try pj_st_eq;
      cbn [sa_size]; clear - HKL Kc ACC; lia.
Qed.

Lemma copy_tailA : forall (k : Z) x0 x8 x16 x288 x296 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
  0 <= k <= l ->
  SERML x0 x8 x16 x288 x296 ser_shpatA Σ st m -> frm0 fc -> sa_size st + k <= sa_cap st -> sa_size st <= A + 1 -> CREDA RT E I Σ X st ->
  aevt Σ K (BSS 0xba19c xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (sa_size st + k)) (wz (pa_SB E + 80)) (wz k) xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST GROW OK CX Hi HT HSTR Hdp BUD X0 HK.
  intros k x0 x8 x16 x288 x296 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HKL HSM FRM ROOM ACC CR.
  pose proof HSTR as (C0 & L0 & CL & _).
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). pose proof HSM as HSM0. open HSM. sb_shz.

  step. astep. astep. astep. astep.

  step. step. step. zstep. try (replace (size + buf) with (buf + size) by (clear; lia)).

  gtrap. unzx.

  zstep. zstep. zstep.
  pose proof (sbuf_srcA RT AF E D I _ _ _ isobj Σ _ m (c + 4) k OK CX HSM0 ltac:(clear - C0; lia) ltac:(clear - HKL; lia) ltac:(clear - CL HKL; lia))
    as (src & SRC & SRCL & SAC & SRG & S0' & SLO).
  replace (pa_SBUF E + c + 4) with (pa_SBUF E + (c + 4)) by (clear; lia).
  ser_close HSM2 OK CX. apply evt_done.
  eapply aevt_eq; [| eapply (ser_copyA RT AF RC PMc FDO MST E D I _ _ _ isobj Σ (mkSbA buf size cap hp kk) m K (pa_SBUF E + (c + 4)) k 0xba1e8 src)];
    [pj_st_eq; clear; lia| exact OK| exact CX| exact HSM2| exact SRC| exact SRCL| clear - HKL; lia| cbn [sa_size sa_cap]; exact ROOM
    | intros _; split; [exact SAC| exact SRG]| clear - SR C0; lia| exact SLO| clear; lia| reflexivity|].
  intros m' F' yt0 yt1 yt2 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CPY.
  replace (pa_SBUF E + (c + 4)) with (pa_SBUF E + c + 4) by (clear; lia).
  eapply aevt_eq; [| eapply (copy_finA k x0 x8 x16 x288 x296 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
Qed.

Lemma str_copyA : forall (k : Z) x0 x8 x16 x288 x296 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 : word),
  0 <= k <= l ->
  SERML x0 x8 x16 x288 x296 ser_shpatA Σ st m -> frm0 fc -> sa_size st <= A + 1 -> CREDA RT E I Σ X st ->
  aevt Σ K (BSS 0xba150 xra xt0 xt1 xt2 xa0 (wz (M64M1 - DATA)) xa2 xa3 xa4 xa5 xa6 xa7 xs3 (wz PJ_NE_TAB_A) (wz k) xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST GROW OK CX Hi HT HSTR Hdp BUD X0 HK.
  intros k x0 x8 x16 x288 x296 Σ st m F fc xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 HKL HSM FRM ACC CR.
  pose proof HSTR as (C0 & L0 & CL & _).
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM. sb_shz.

  gtrap. astep. astep. step. astep. step. astep.

  step. step. zstep. step.
  if_cases Kc; zify_cond Kc; pjnorm_in Kc.
  -
    ser_close HSM2 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (copy_tailA k x0 x8 x16 x288 x296 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
  -
    zstep. pjnorm. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 _ ?mm _) =>
    assert (GROWN : forall (z : Z) (ya0 : word), z = Z.max (2 * cap) (size + k) ->
      evt bsegs (fun ms' => aevt Σ K ms')
        (BSS 0xba194 xra xt0 xt1 xt2 ya0 (wz z) xa2 xa3 xa4 xa5 xa6 xa7 (wz (size + k)) (wz (pa_SB E + 80)) (wz k) xt3 xt4 xt5 xt6 F0 fc0 mm)) end.
    { intros z ya0 EZ.

      step. zstep.
      ser_close HSM3 OK CX. apply evt_done.
      eapply aevt_eq; [| eapply (ser_growA RT AF PMc GROW E D I _ _ _ isobj Σ (mkSbA buf size cap hp kk) _ K z X 0xba19c)];
        [pj_st_eq| exact OK| exact CX| exact HSM3| | exact CR| exact X0| clear; lia| reflexivity|].
      { rewrite EZ. eapply (ser_req_okA RT E D I); [exact OK| exact CX| exact HSM3| cbn [sa_cap]; clear - Kc; lia|].
        cbn [sa_size]. clear - ACC BUD HKL. lia. }
      intros Σ' NEW m' F' yt0 yt1 yt2 za0 za1 za2 za3 za4 za5 za6 za7 yt3 yt4 yt5 yt6 HSM4 CR4.
      eapply aevt_eq; [| eapply (copy_tailA k x0 x8 x16 x288 x296 Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW z))]; try eassumption; try pj_st_eq;
        unfold sb_grownA; cbn [sa_size sa_cap sa_buf sa_heap sa_k]; rewrite ?EZ; clear - Kc ACC SZ HKL; lia. }
    if_cases K2; zify_cond K2; pjnorm_in K2.
    + eapply evt_eq; [| eapply (GROWN (size + k))]; [pj_st_eq| clear - K2 Kc; lia].
    +   zstep. eapply evt_eq; [| eapply (GROWN (2 * cap))]; [pj_st_eq| clear - K2 Kc; lia].
Qed.

Lemma str_hjoinA : forall x0 x8 x16 x288 x296 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa1 xa2 xa3 xa6 xa7 xt3 xt4 xt5 xt6 : word),
  SERML x0 x8 x16 x288 x296 ser_shpatA Σ st m -> frm0 fc -> 1 <= sa_size st -> sa_size st <= A + 1 -> CREDA RT E I Σ X st ->
  aevt Σ K (HSS 0xb9c30 xra xt0 xt1 xt2 (wz (sa_buf st + (sa_size st - 1))) xa1 xa2 xa3 (wz (pa_S E c)) (wz (pa_S E (c + 3))) xa6 xa7
               (wz (pa_S E (c + 2))) (wz (pa_S E (c + 1))) xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST GROW OK CX Hi HT HSTR Hdp BUD X0 HK.
  intros x0 x8 x16 x288 x296 Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa3 xa6 xa7 xt3 xt4 xt5 xt6 HSM FRM SZ1 ACC CR.
  pose proof HSTR as (C0 & L0 & CL & LE & _). unfold le32 in LE.
  pose proof (S_rangeA E c OK) as BR0. pose proof (S_rangeA E (c + 1) OK) as BR1. pose proof (S_rangeA E (c + 2) OK) as BR2. pose proof (S_rangeA E (c + 3) OK) as BR3.
  set (b0 := pa_S E c) in *. set (b1 := pa_S E (c + 1)) in *. set (b2 := pa_S E (c + 2)) in *. set (b3 := pa_S E (c + 3)) in *.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM.
  pose proof (buf_factsA RT AF E D I Σ _ _ (si_b I) OK CX HREF) as (_ & _ & _ & _ & APB). cbn [sa_buf sa_cap] in APB.
  pose proof (APB (buf + (size - 1)) ltac:(clear - SZ1 SZ; lia)) as (A1 & A2 & A3 & A4). clear APB.

  zstep. step. step. pj_store_done.

  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  assert (M1 : Z.modulo (Z.shiftl b1 8) 18446744073709551616 = Z.shiftl b1 8) by (rewrite Z.shiftl_mul_pow2 by lia; apply Z.mod_small; clear - BR1; lia).
  assert (M2 : Z.modulo (Z.shiftl b2 16) 18446744073709551616 = Z.shiftl b2 16) by (rewrite Z.shiftl_mul_pow2 by lia; apply Z.mod_small; clear - BR2; lia).
  assert (M3 : Z.modulo (Z.shiftl b3 24) 18446744073709551616 = Z.shiftl b3 24) by (rewrite Z.shiftl_mul_pow2 by lia; apply Z.mod_small; clear - BR3; lia).
  rewrite ?M1, ?M2, ?M3. clear M1 M2 M3.
  rewrite ?pj_land64 by (rewrite Z.shiftl_mul_pow2 by lia; clear - BR1 BR2 BR3; lia).
  rewrite lor4_le32 by lia.
  replace (b0 + 2 ^ 8 * b1 + 2 ^ 16 * b2 + 2 ^ 24 * b3) with l by (clear - LE; lia).

  rewrite (lxor_ones64 DATA) by (change (2 ^ 64) with 18446744073709551616; clear - SR C0 CL L0 LQ QT; lia).

  step. zstep.

  pose proof (shz_sbufA RT AF E D I Σ _ _ _ OK CX HREF MU WM) as SHS.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (shz_tabs mm (tabs_accA RT AF Σ mm (ART_mu RT AF E D I Σ _ _ mm OK CX HREF MU WM))) as SHTB end.
  assert (F1 : l - 8 * 0 < Z.of_nat (S (Z.to_nat l))) by (clear - L0; lia).
  assert (F2 : 0 <= 0) by (clear; lia). assert (F3 : 8 * 0 <= l) by (clear - L0; lia).
  unfold PJ_NE_TAB_A in *.
  eapply evt_eq; [| eapply (str_scan8A (S (Z.to_nat l)) 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 F2 F3 SHS SHTB MI
                               (fun o Ho => sbuf_read_mu RT AF E D I OK CX Σ _ _ _ o HREF MU WM Ho))]; [pj_st_eq|]. clear F1 F2 F3.
  intros k8 ya0 ya2 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 HK8.

  zstep. if_cases Kc; zify_cond Kc; pjnorm_in Kc.
  -
    ser_close HSM2 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (str_copyA k8 x0 x8 x16 x288 x296 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
  -
    assert (F1 : l - k8 <= Z.of_nat (S (Z.to_nat l))) by (clear - HK8 Kc; lia). assert (F2 : 0 <= k8 < l) by (clear - HK8 Kc; lia).
    eapply evt_eq; [| eapply (str_tailA (S (Z.to_nat l)) k8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 F2 SHS SHTB MI
                                 (fun o Ho => sbuf_read_mu RT AF E D I OK CX Σ _ _ _ o HREF MU WM Ho))]; [pj_st_eq|]. clear F1 F2.
    intros k' za0 za2 za3 HK'.
    ser_close HSM2 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (str_copyA k' x0 x8 x16 x288 x296 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; clear - HK' HK8 ACC; cbn [sa_size]; lia.
Qed.

Lemma str_htailA : forall (x0 x8 x16 x208 x288 x296 : word) (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa6 xa7 xt3 xt4 xt5 xt6 : word),
  SERMA RT E I (wkC E) (hx x0 x8 x16 x208 x288 x296) ser_shpatA isobj Σ st m ->
  frm0 fc -> sa_size st + 1 <= sa_cap st -> sa_size st <= A -> CREDA RT E I Σ X st ->
  aevt Σ K (HSS 0xb9bcc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 (wz (pa_S E c)) (wz (pa_S E (c + 3))) xa6 xa7
               (wz (pa_S E (c + 2))) (wz (pa_S E (c + 1))) xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST GROW OK CX Hi HT HSTR Hdp BUD X0 HK.
  intros x0 x8 x16 x208 x288 x296 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa6 xa7 xt3 xt4 xt5 xt6 HSM FRM ROOM ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM.

  step. astep. step. sb_shz. astep. astep. astep. astep.

  step. step. step. zstep. zstep. unbox FSB; unbox SHSB. step. box_disj.

  gtrap. unzx. gtrap.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (acc_buf_mu RT AF E D I OK CX Σ _ _ mm HREF MU WM) as ACCB end.
  cbn [sa_buf sa_cap] in ACCB.
  destruct (acc_read1 _ _ _ (buf + size) ACCB ltac:(clear - ROOM SZ; lia)) as (b & RDB & SOK). clear ACCB.
  change (wa ((buf + size) / 8 + 2147450880)) with (wa (shad (buf + size))) in RDB.

  zstep. pjnorm. zstep. shfold. zstep.
  ser_close HSM2 OK CX.
  destruct (pj_sh_ok_cases b (buf + size) SOK) as [-> | (k & -> & K17 & KM)].
  -
    rewrite sxb_z8. zstep. if_false. apply evt_done.
    eapply aevt_eq; [| eapply (str_hjoinA x0 x8 x16 x288 x296 Σ (mkSbA buf (size + 1) cap hp kk))]; try eassumption; try pj_st_eq; slia.
  -
    rewrite (pj_sxb_small7 k) by (clear - K17; lia). zstep.
    if_cases Kc; zify_cond Kc; [clear Kc| exfalso; pjnorm_in Kc; clear - Kc K17; lia].
    zstep. pjnorm. rewrite pj_land7 by (clear - R0 SZ; lia).
    zstep. if_cases Kc; zify_cond Kc;
      [clear Kc| exfalso; rewrite !pj_signed_small in Kc by (clear - K17; Z.div_mod_to_equations; lia); clear - Kc K17 KM; lia].
    apply evt_done.
    eapply aevt_eq; [| eapply (str_hjoinA x0 x8 x16 x288 x296 Σ (mkSbA buf (size + 1) cap hp kk))]; try eassumption; try pj_st_eq; slia.
Qed.

End Pieces.

Local Ltac hbE E D I OK CX c k :=
  let G := fresh "G" in let G2 := fresh "G" in let RD := fresh "RD" in
  lazymatch goal with
  | HREF : SREFA _ _ _ _ _ ?mr, MU : munch _ ?mr ?mm, WM : wmono bsegs ?mr ?mm, C0 : 0 <= c, CL : c + ?l + 5 <= _, L0 : 0 <= ?l |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (G : 0 <= c + k < pa_sn E) by (clear - C0 CL L0; lia);
    assert (G2 : pa_SBUF E + c + k = pa_SBUF E + (c + k)) by (clear; lia);
    pose proof (read1_at mm _ _ (sbuf_read_mu RT AF E D I OK CX _ _ _ mm _ HREF MU WM G) _ G2) as RD; clear G G2; astep; clear RD
  end.
Local Ltac sb_shzE E D I OK CX :=
  lazymatch goal with
  | HREF : SREFA _ _ _ _ _ ?mr, MU : munch _ ?mr ?mm, WM : wmono bsegs ?mr ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let SHZ := fresh "SHZ" in let R64 := fresh "RD64" in let R72 := fresh "RD72" in let R80 := fresh "RD80" in
    pose proof (shz_sb_mu RT AF E D I OK CX _ _ _ mm HREF MU WM) as SHZ;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 64) ltac:(clear; lia)) as R64;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 72) ltac:(clear; lia)) as R72;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 80) ltac:(clear; lia)) as R80; clear SHZ
  end.

Local Ltac trefE E D I OK CX isobj Σ i Hi rpc HSMc HSMo :=
  ser_close HSMc OK CX;
  eapply evt_cut; [eapply (ser_trefA RT AF E D I _ _ _ isobj Σ _ _ i); [exact OK| exact CX| exact HSMc| clear - Hi; lia]|];
  cbv beta;
  let ms1 := fresh "ms" in let m1 := fresh "m" in let ya4 := fresh "ya4" in
  intros ms1 (m1 & ya4 & -> & HSMo); clear HSMc; rewrite (ret_pc_even rpc) by (clear; lia);
  ser_open HSMo OK.

Theorem str_proofA : str_stmtA RT PMc.
Proof using AF RC FDO MST GROW.
  unfold str_stmtA.
  intros E D I K isobj Σ st m F fc i c l dp A X xs3 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 OK CX HSM FRM Hi HT HSTR Hdp ACC BUD CR X0 HK.
  pose proof HSTR as (C0 & L0 & CL & LE & _).
  pose proof (S_rangeA E c OK) as BR0. pose proof (S_rangeA E (c + 1) OK) as BR1. pose proof (S_rangeA E (c + 2) OK) as BR2. pose proof (S_rangeA E (c + 3) OK) as BR3.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *. unfold PJ_STR_A.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). destruct HSM as [x HSM]. ser_open HSM OK.
  cbn [Pj_ser_defsA.xj0 Pj_ser_defsA.xj8 Pj_ser_defsA.xj16 Pj_ser_defsA.xj24 Pj_ser_defsA.xj80 Pj_ser_defsA.xj208 Pj_ser_defsA.xj216 Pj_ser_defsA.xj288 Pj_ser_defsA.xj296] in *.

  zstep. zstep. zstep.
  trefE E D I OK CX isobj Σ i Hi 0xb9a5c HSM1 HSM2.

  pose proof (shz_tape_mu RT AF E D I OK CX Σ _ _ _ HREF MU WM) as SHTP.
  assert (G : pa_TAPE E <= pa_TAPE E + 8 * i < pa_TAPE E + 8 * pa_n E) by (clear - Hi; lia).
  pose proof (shz_rd _ _ _ SHTP _ G) as RD. clear G SHTP.
  astep. astep. astep. astep. clear RD.

  pose proof (shz_doc_mu RT AF E D I OK CX Σ _ _ _ HREF MU WM) as SHD.
  pose proof (shz_rd _ _ _ SHD (pa_DOC E + 8) ltac:(clear; lia)) as RD8. clear SHD.
  step. zstep. pjnorm. astep. astep. astep.

  pose proof (doc_cells_mu RT AF E D I OK CX Σ _ _ _ HREF MU WM) as DOCC.
  step. gok.

  pose proof (tape_read_mu RT AF E D I OK CX Σ _ _ _ i HREF MU WM ltac:(clear - Hi; lia)) as RDT. rewrite HT in RDT.
  assert (C56 : 0 <= c < 2 ^ 56) by (clear - C0 CL SR L0 LB QT BQ; lia).
  assert (T8 : 0 <= t_str < 256) by (unfold t_str; clear; lia).
  pose proof (tword_range t_str c T8 C56) as TWR.
  step. clear RDT. step. step. zstep.
  rewrite ?(Z.mod_small (tword t_str c) 18446744073709551616) by (clear - TWR; lia).
  unfold MASK56. rewrite ?pj_land64 by (clear - TWR; lia).
  assert (EA : Z.land (tword t_str c) 72057594037927935 = c).
  { rewrite land_mask56 by (clear - TWR; lia). apply tval_tword. exact C56. }
  rewrite !EA.

  zstep. zstep. replace (pa_SBUF E + (c + 4)) with (pa_SBUF E + c + 4) by (clear; lia). gok. gok.

  step. zstep. zstep. clear RD8 DOCC.
  trefE E D I OK CX isobj Σ i Hi 0xb9ac8 HSM2 HSM3.

  pose proof (shz_tape_mu RT AF E D I OK CX Σ _ _ _ HREF MU WM) as SHTP.
  assert (G : pa_TAPE E <= pa_TAPE E + 8 * i < pa_TAPE E + 8 * pa_n E) by (clear - Hi; lia).
  pose proof (shz_rd _ _ _ SHTP _ G) as RD. clear G SHTP.
  astep. astep. astep. astep. clear RD.

  pose proof (shz_doc_mu RT AF E D I OK CX Σ _ _ _ HREF MU WM) as SHD.
  pose proof (shz_rd _ _ _ SHD (pa_DOC E + 8) ltac:(clear; lia)) as RD8. clear SHD.
  astep. astep. clear RD8.

  pose proof (tape_read_mu RT AF E D I OK CX Σ _ _ _ i HREF MU WM ltac:(clear - Hi; lia)) as RDT. rewrite HT in RDT.
  pose proof (doc_cells_mu RT AF E D I OK CX Σ _ _ _ HREF MU WM) as DOCC.
  step. clear RDT. step. clear DOCC. step. zstep.
  rewrite ?(Z.mod_small (tword t_str c) 18446744073709551616) by (clear - TWR; lia).
  unfold MASK56. rewrite ?pj_land64 by (clear - TWR; lia). rewrite !EA. clear EA T8.
  zstep. gok.

  zstep. zstep. zstep. unz. change (Z.lxor 1 0) with 1. gok. gok.

  pose proof (shz_sbufA RT AF E D I Σ _ _ _ OK CX HREF MU WM) as SHS.
  assert (G : pa_SBUF E <= pa_SBUF E + c < pa_SBUF E + pa_sn E) by (clear - C0 CL L0; lia).
  pose proof (shz_rd _ _ _ SHS _ G) as RD. clear G. astep. astep. astep. astep. clear RD.
  assert (G : pa_SBUF E <= pa_SBUF E + c + 3 < pa_SBUF E + pa_sn E) by (clear - C0 CL L0; lia).
  pose proof (shz_rd _ _ _ SHS _ G) as RD. clear G. astep. astep. astep. astep. astep. clear RD. clear SHS.

  step. astep. step. sb_shzE E D I OK CX. astep. astep.

  step. clear RD64 RD72 RD80. sb_shzE E D I OK CX. step. astep. astep. astep. clear RD64 RD72 RD80.

  step. step. step.
  hbE E D I OK CX c 0. hbE E D I OK CX c 1. hbE E D I OK CX c 2. hbE E D I OK CX c 3.
  replace (pa_S E (c + 0)) with (pa_S E c) by (f_equal; clear; lia). pjnorm.

  zstep. step.
  if_cases Kc; zify_cond Kc; pjnorm_in Kc.
  -
    ser_close HSM4 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (str_htailA E D I K isobj i dp c l A X OK CX Hi HT HSTR Hdp BUD X0 HK _ _ _ _ _ _ Σ (mkSbA buf size cap hp kk))];
      try eassumption; try pj_st_eq; cbn [sa_size sa_cap]; clear - Kc ACC; lia.
  -
    zstep. pjnorm. step. step. step. zstep. zstep. zstep. zstep.
    ser_close HSM4 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (ser_growA RT AF PMc GROW E D I _ _ _ isobj Σ (mkSbA buf size cap hp kk) _ K (2 * cap) X 0xb9bb8)];
      [pj_st_eq| exact OK| exact CX| exact HSM4| | exact CR| exact X0| clear; lia| reflexivity|].
    { eapply (ser_req_ok2A RT E D I); [exact OK| exact CX| exact HSM4|]. cbn [sa_cap sa_size] in *. clear - Kc ACC BUD L0. lia. }
    intros Σ' NEW m' F' zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 HSM5 CR5.
    apply (aevt_evt RT AF PMc MST). ser_open HSM5 OK.
    cbn [Pj_ser_defsA.xj0 Pj_ser_defsA.xj8 Pj_ser_defsA.xj16 Pj_ser_defsA.xj24 Pj_ser_defsA.xj80 Pj_ser_defsA.xj208 Pj_ser_defsA.xj216 Pj_ser_defsA.xj288 Pj_ser_defsA.xj296] in *.

    zstep. zstep. zstep. step. step.
    ser_close HSM6 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (str_htailA E D I K isobj i dp c l A X OK CX Hi HT HSTR Hdp BUD X0 HK _ _ _ _ _ _ Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW (2 * cap)))];
      try eassumption; try pj_st_eq; unfold sb_grownA; cbn [sa_size sa_cap sa_buf sa_heap sa_k]; clear - Kc ACC SZ R1; lia.
Qed.

End Str.

Theorem str_okA : forall (RT : rt_sig), art_facts RT -> rt_contracts RT -> forall PMc : Model -> Prop, fdfs_only PMc -> mat_stable PMc ->
  grow_cpsA RT PMc -> str_stmtA RT PMc.
Proof. intros RT AF RC PMc FDO MST GROW. exact (str_proofA RT AF RC PMc FDO MST GROW). Qed.
