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
     Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_hkit3A Atp_hkit4A Pj_rtkA Pj_defsA Pj_cpsA Pj_ser_defsA Pj_ser_kitA Pj_ser_callsA Pj_ser_skitA
     Pj_ser_keyA_b Pj_ser_keyA_a Pj_ser_keyA_e.
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

Section Key.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis GROW : grow_cpsA RT PMc.
Hypothesis TABS : forall Σ m, ART RT Σ m -> acc asegs m PJ_TABS_A PJ_TABS_LEN.
Notation aevt := (aevt RT PMc).

Section Pieces.
Variable E : pjenvA.
Variable D : nat.
Variable I : serI.
Variable K : config -> Prop.
Variable isobj : list byte.
Variables (i c l dp A X : Z).
Hypothesis OK : pjenvA_ok E.
Hypothesis CX : sctxA E D I.
Hypothesis Hi : 1 <= i < pa_n E.
Hypothesis HSTR : str_at (pa_S E) (pa_sn E) c l.
Hypothesis Hdp : 0 <= dp <= 15.
Hypothesis BUD : A + (3 + 6 * l) <= PJ_OUTMAX (pa_len E).
Hypothesis X0 : 0 <= X.
Hypothesis HK : disp_KA RT PMc E I K isobj (i + 1) dp X (A + (3 + 6 * l)).

Notation DATA := (pa_SBUF E + c + 4).
Notation kx := (Pj_ser_keyA_a.kx E c).
Notation SERMK x0 x56 x256 x264 Σ st m :=
  (SERMA RT E I (wz PJ_ESC_TAB_A) (wz (T5A E)) (wz (S64A E)) (wz (S80A E)) (kx x0 x56 x256 x264) ser_shpatA isobj Σ st m).
Notation KST pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs5 xs9 xs10 xs11 xt3 xt4 F fc m :=
  (SSTA I pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
        (Z_to_bv 64 dp) (Z_to_bv 64 (pa_SB E + 72)) xs4 xs5 (Z_to_bv 64 i) (Z_to_bv 64 2147450880) (Z_to_bv 64 PJ_NE_TAB_A) xs9 xs10 xs11
        xt3 xt4 (Z_to_bv 64 (T5A E)) (Z_to_bv 64 (shad (pa_SB E + 72))) F fc m).
Notation esc_headA := (Pj_ser_keyA_e.esc_headA RT AF RC PMc FDO MST GROW TABS E D I K isobj i c l dp A X OK CX Hi HSTR Hdp BUD X0 HK).
Notation key_closeA := (Pj_ser_keyA_a.key_closeA RT AF RC PMc FDO MST GROW TABS E D I K isobj i c l dp A X OK CX Hi HSTR Hdp BUD X0 HK).
Notation key_scan8A := (Pj_ser_keyA_b.key_scan8A E D I i c l dp OK CX HSTR).
Notation key_tailA := (Pj_ser_keyA_b.key_tailA E D I i c l dp OK CX HSTR).
Local Ltac slia := repeat match goal with H : _ \/ _ |- _ => clear H end; cbn [sa_size sa_cap sa_buf sa_heap sa_k]; lia.
Local Ltac sb_shz :=
  lazymatch goal with
  | HREF : SREFA _ _ _ _ _ ?mr, MU : munch _ ?mr ?mm, WM : wmono asegs ?mr ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let SHZ := fresh "SHZ" in let R64 := fresh "RD64" in let R72 := fresh "RD72" in let R80 := fresh "RD80" in
    pose proof (shz_sb_mu RT AF E D I OK CX _ _ _ mm HREF MU WM) as SHZ;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 64) ltac:(clear; lia)) as R64;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 72) ltac:(clear; lia)) as R72;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 80) ltac:(clear; lia)) as R80; clear SHZ
  end.
Local Ltac open HSM := unfold Pj_ser_keyA_a.kx in HSM; ser_open HSM OK; cbn [Pj_ser_defsA.xj0 Pj_ser_defsA.xj56 Pj_ser_defsA.xj64 Pj_ser_defsA.xj96 Pj_ser_defsA.xj192 Pj_ser_defsA.xj200 Pj_ser_defsA.xj208 Pj_ser_defsA.xj256 Pj_ser_defsA.xj264] in *.

Lemma copy_finA : forall (k : Z) x0 x56 x256 x264 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 : word),
  0 <= k <= l ->
  SERMK x0 x56 x256 x264 Σ st m -> frm0 fc -> sa_size st + k <= sa_cap st -> sa_size st <= A + 1 -> CREDA RT E I Σ X st ->
  aevt Σ K (KST 0xb36d8 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (sa_size st + k)) (wz l) xs9 (wz (pa_SB E)) (wz k)
               xt3 xt4 F fc m).
Proof using AF RC FDO MST GROW TABS OK CX Hi HSTR Hdp BUD X0 HK.
  intros k x0 x56 x256 x264 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 HKL HSM FRM ROOM ACC CR.
  pose proof HSTR as (C0 & L0 & CL & _).
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ser_envA OK CX. str_envA_sb OK. apply (aevt_evt RT AF PMc MST). open HSM. sb_shz.

  astep. astep. unbox FSB; unbox SHSB. step. box_disj. step.
  if_cases Kc; zify_cond Kc; pjnorm_in Kc.
  -
    ser_close HSM2 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (key_closeA x0 x56 x256 x264 Σ (mkSbA buf (size + k) cap hp kk))]; try eassumption; try pj_st_eq; slia.
  -
    step. zstep. step. zstep. zstep. zstep. zstep.
    ser_close HSM2 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (esc_headA (Z.to_nat (l - k)) k x0 x56 x256 x264 Σ (mkSbA buf (size + k) cap hp kk))]; try eassumption; try pj_st_eq;
      cbn [sa_size]; clear - HKL Kc ACC; lia.
Qed.

Lemma copy_tailA : forall (k : Z) x0 x56 x256 x264 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 : word),
  0 <= k <= l ->
  SERMK x0 x56 x256 x264 Σ st m -> frm0 fc -> sa_size st + k <= sa_cap st -> sa_size st <= A + 1 -> CREDA RT E I Σ X st ->
  aevt Σ K (KST 0xb3694 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (sa_size st + k)) (wz l) (wz DATA) (wz (pa_SB E)) (wz k)
               xt3 xt4 F fc m).
Proof using AF RC FDO MST GROW TABS OK CX Hi HSTR Hdp BUD X0 HK.
  intros k x0 x56 x256 x264 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 HKL HSM FRM ROOM ACC CR.
  pose proof HSTR as (C0 & L0 & CL & _).
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ser_envA OK CX. str_envA_sb OK. apply (aevt_evt RT AF PMc MST). pose proof HSM as HSM0. open HSM. sb_shz.

  zstep. if_cases Kz; zify_cond Kz; pjnorm_in Kz.
  -
    ser_close HSM2 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (copy_finA k x0 x56 x256 x264 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
  -
    step. astep. astep. astep. astep.

    step. step. step. zstep. zstep. zstep. zstep.
    pose proof (sbuf_srcA RT AF E D I _ _ _ _ _ _ isobj Σ _ m (c + 4) k OK CX HSM0 ltac:(clear - C0; lia) ltac:(clear - HKL; lia) ltac:(clear - CL HKL; lia))
      as (src & SRC & SRCL & SAC & SRG & S0' & SLO).
    ser_close HSM2 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (ser_copyA RT AF RC PMc FDO MST e_asan_memmove E D I _ _ _ _ _ _ isobj Σ (mkSbA buf size cap hp kk) m K (pa_SBUF E + (c + 4)) k 0xb36d0 src)];
      [pj_st_eq| right; reflexivity| exact OK| exact CX| exact HSM2| exact SRC| exact SRCL| clear - Kz HKL; lia| cbn [sa_size sa_cap]; exact ROOM
      | exact SAC| exact SRG| exact S0'| exact SLO| intros EQ; exfalso; clear - EQ; unfold e_asan_memmove, e_asan_memcpy in EQ; lia
      | clear; lia| reflexivity|].
    intros m' F' yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CPY.
    apply (aevt_evt RT AF PMc MST). open HSM4.

    step. step.
    ser_close HSM5 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (copy_finA k x0 x56 x256 x264 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
Qed.

Lemma key_copyA : forall (k : Z) x0 x56 x256 x264 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xt3 xt4 : word),
  0 <= k <= l ->
  SERMK x0 x56 x256 x264 Σ st m -> frm0 fc -> sa_size st <= A + 1 -> CREDA RT E I Σ X st ->
  aevt Σ K (KST 0xb3644 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 (wz l) (wz DATA) (wz (pa_SB E)) (wz k)
               xt3 xt4 F fc m).
Proof using AF RC FDO MST GROW TABS OK CX Hi HSTR Hdp BUD X0 HK.
  intros k x0 x56 x256 x264 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xt3 xt4 HKL HSM FRM ACC CR.
  pose proof HSTR as (C0 & L0 & CL & _).
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ser_envA OK CX. str_envA_sb OK. apply (aevt_evt RT AF PMc MST). open HSM. sb_shz.

  astep. astep. step. astep. astep.

  step. step. step. zstep. step.
  if_cases Kc; zify_cond Kc; pjnorm_in Kc.
  -
    ser_close HSM2 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (copy_tailA k x0 x56 x256 x264 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
  -
    zstep. pjnorm. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 _ ?mm _) =>
    assert (GROWN : forall (z : Z) (ya0 : word), z = Z.max (2 * cap) (size + k) ->
      evt asegs (fun ms' => aevt Σ K ms')
        (KST 0xb3684 xra xt0 xt1 xt2 ya0 (wz z) xa2 xa3 xa4 xa5 xa6 xa7 (wz (size + k)) (wz l) (wz DATA) (wz (pa_SB E)) (wz k)
             xt3 xt4 F0 fc0 mm)) end.
    { intros z ya0 EZ.

      zstep. zstep.
      ser_close HSM3 OK CX. apply evt_done.
      eapply aevt_eq; [| eapply (ser_growA RT AF PMc GROW E D I _ _ _ _ _ _ isobj Σ (mkSbA buf size cap hp kk) _ K z X 0xb368c)];
        [pj_st_eq| exact OK| exact CX| exact HSM3| | exact CR| exact X0| clear; lia| reflexivity|].
      { rewrite EZ. eapply (ser_req_okA RT E D I); [exact OK| exact CX| exact HSM3| cbn [sa_cap]; clear - Kc; lia|].
        cbn [sa_size]. clear - ACC BUD HKL. lia. }
      intros Σ' NEW m' F' yt0 yt1 yt2 za0 za1 za2 za3 za4 za5 za6 za7 yt3 yt4 yt5 yt6 HSM4 CR4.
      apply (aevt_evt RT AF PMc MST). open HSM4.

      step. step.
      ser_close HSM5 OK CX. apply evt_done.
      eapply aevt_eq; [| eapply (copy_tailA k x0 x56 x256 x264 Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW z))]; try eassumption; try pj_st_eq;
        unfold sb_grownA; cbn [sa_size sa_cap sa_buf sa_heap sa_k]; rewrite ?EZ; clear - Kc ACC SZ HKL; lia. }
    if_cases K2; zify_cond K2; pjnorm_in K2.
    + eapply (GROWN (size + k)). clear - K2 Kc; lia.
    +   zstep. eapply (GROWN (2 * cap)). clear - K2 Kc; lia.
Qed.

Lemma key_hjoinA : forall x0 x56 x256 x264 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa1 xa2 xa4 xa5 xa6 xa7 xs9 xt3 xt4 : word),
  SERMK x0 x56 x256 x264 Σ st m -> frm0 fc -> 1 <= sa_size st -> sa_size st <= A + 1 -> CREDA RT E I Σ X st ->
  aevt Σ K (KST 0xb3334 xra xt0 xt1 xt2 (wz (sa_buf st + (sa_size st - 1))) xa1 xa2 (wz (pa_S E c)) xa4 xa5 xa6 xa7
               (wz (pa_SBUF E + c)) (wz (pa_S E (c + 1))) xs9 (wz (pa_S E (c + 2))) (wz (pa_S E (c + 3))) xt3 xt4 F fc m).
Proof using AF RC FDO MST GROW TABS OK CX Hi HSTR Hdp BUD X0 HK.
  intros x0 x56 x256 x264 Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa4 xa5 xa6 xa7 xs9 xt3 xt4 HSM FRM SZ1 ACC CR.
  pose proof HSTR as (C0 & L0 & CL & LE & _). unfold le32 in LE.
  pose proof (S_rangeA E c OK) as BR0. pose proof (S_rangeA E (c + 1) OK) as BR1. pose proof (S_rangeA E (c + 2) OK) as BR2. pose proof (S_rangeA E (c + 3) OK) as BR3.
  set (b0 := pa_S E c) in *. set (b1 := pa_S E (c + 1)) in *. set (b2 := pa_S E (c + 2)) in *. set (b3 := pa_S E (c + 3)) in *.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ser_envA OK CX. str_envA_sb OK. apply (aevt_evt RT AF PMc MST). open HSM.
  pose proof (buf_factsA RT AF E D I Σ _ _ (si_b I) OK CX HREF) as (_ & _ & _ & _ & APB). cbn [sa_buf sa_cap] in APB.
  pose proof (APB (buf + (size - 1)) ltac:(clear - SZ1 SZ; lia)) as (A1 & A2 & A3 & A4). clear APB.

  zstep. zstep. zstep. zstep. step. step. pj_store_done.

  zstep. zstep. zstep. zstep.
  assert (M1 : Z.modulo (Z.shiftl b1 8) 18446744073709551616 = Z.shiftl b1 8) by (rewrite Z.shiftl_mul_pow2 by lia; apply Z.mod_small; clear - BR1; lia).
  assert (M2 : Z.modulo (Z.shiftl b2 16) 18446744073709551616 = Z.shiftl b2 16) by (rewrite Z.shiftl_mul_pow2 by lia; apply Z.mod_small; clear - BR2; lia).
  assert (M3 : Z.modulo (Z.shiftl b3 24) 18446744073709551616 = Z.shiftl b3 24) by (rewrite Z.shiftl_mul_pow2 by lia; apply Z.mod_small; clear - BR3; lia).
  rewrite ?M1, ?M2, ?M3. clear M1 M2 M3.
  rewrite ?pj_land64 by (rewrite Z.shiftl_mul_pow2 by lia; clear - BR1 BR2 BR3; lia).
  rewrite lor4_le32 by lia.
  replace (b0 + 2 ^ 8 * b1 + 2 ^ 16 * b2 + 2 ^ 24 * b3) with l by (clear - LE; lia).
  pose proof (land_m8_range l ltac:(clear - L0 C0 CL SL S0 LQ QT; lia)) as K8R.
  zstep. zstep. step.

  pose proof (shz_sbufA RT AF E D I Σ _ _ _ OK CX HREF MU WM) as SHS.
  pose proof (shz_tabs _ (TABS Σ _ (ART_mu RT AF E D I Σ _ _ _ OK CX HREF MU WM))) as SHTB.
  assert (F1 : l - 8 * 0 < Z.of_nat (S (Z.to_nat l))) by (clear - L0; lia).
  assert (F2 : 0 <= 0) by (clear; lia). assert (F3 : 8 * 0 <= l) by (clear - L0; lia).
  eapply evt_eq; [| eapply (key_scan8A (S (Z.to_nat l)) 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 F2 F3 SHS SHTB MI
                               (fun o Ho => sbuf_read_mu RT AF E D I OK CX Σ _ _ _ o HREF MU WM Ho))]; [pj_st_eq|]. clear F1 F2 F3.
  intros k8 ya0 ya3 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 HK8.

  zstep. if_cases Kc; zify_cond Kc; pjnorm_in Kc.
  -
    ser_close HSM2 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (key_copyA k8 x0 x56 x256 x264 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
  -
    assert (F1 : l - k8 <= Z.of_nat (S (Z.to_nat l))) by (clear - HK8 Kc; lia). assert (F2 : 0 <= k8 < l) by (clear - HK8 Kc; lia).
    eapply evt_eq; [| eapply (key_tailA (S (Z.to_nat l)) k8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 F2 SHS SHTB MI
                                 (fun o Ho => sbuf_read_mu RT AF E D I OK CX Σ _ _ _ o HREF MU WM Ho))]; [pj_st_eq|]. clear F1 F2.
    intros k' za0 za1 HK'.
    ser_close HSM2 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (key_copyA k' x0 x56 x256 x264 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; clear - HK' HK8 ACC; cbn [sa_size]; lia.
Qed.

Lemma key_htailA : forall (x0 x56 x200 x256 x264 : word) (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xs9 xt3 xt4 : word),
  SERMA RT E I (wz PJ_ESC_TAB_A) (wz (T5A E)) (wz (S64A E)) (wz (S80A E))
        (mkXJ x0 (wz c) (wz (pa_SBUF E)) (wz (pa_DOC E / 8)) (wz (shad (pa_SB E + 72))) x200 (wz (shad (pa_SB E + 80))) x256 x264) ser_shpatA isobj Σ st m ->
  frm0 fc -> sa_size st + 1 <= sa_cap st -> sa_size st <= A -> CREDA RT E I Σ X st ->
  aevt Σ K (KST 0xb32e4 xra xt0 xt1 xt2 xa0 xa1 xa2 (wz (pa_S E c)) xa4 xa5 xa6 xa7
               (wz (pa_SBUF E + c)) (wz (pa_S E (c + 1))) xs9 (wz (pa_S E (c + 2))) (wz (pa_S E (c + 3))) xt3 xt4 F fc m).
Proof using AF RC FDO MST GROW TABS OK CX Hi HSTR Hdp BUD X0 HK.
  intros x0 x56 x200 x256 x264 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xs9 xt3 xt4 HSM FRM ROOM ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). ser_open HSM OK.
  cbn [Pj_ser_defsA.xj0 Pj_ser_defsA.xj56 Pj_ser_defsA.xj64 Pj_ser_defsA.xj96 Pj_ser_defsA.xj192 Pj_ser_defsA.xj200 Pj_ser_defsA.xj208 Pj_ser_defsA.xj256 Pj_ser_defsA.xj264] in *.

  step. astep. step. sb_shz. astep. astep. astep. astep.

  step. step. step. zstep. zstep. unbox FSB; unbox SHSB. step. box_disj.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (acc_buf_mu RT AF E D I OK CX Σ _ _ mm HREF MU WM) as ACCB end.
  cbn [sa_buf sa_cap] in ACCB.
  destruct (acc_read1 _ _ _ (buf + size) ACCB ltac:(clear - ROOM SZ; lia)) as (b & RDB & SOK). clear ACCB.
  change (wa ((buf + size) / 8 + 2147450880)) with (wa (shad (buf + size))) in RDB.

  zstep. pjnorm. zstep. shfold. zstep.
  ser_close HSM2 OK CX.
  destruct (pj_sh_ok_cases b (buf + size) SOK) as [-> | (k & -> & K17 & KM)].
  -
    rewrite sxb_z8. zstep. if_true. apply evt_done.
    eapply aevt_eq; [| eapply (key_hjoinA x0 x56 x256 x264 Σ (mkSbA buf (size + 1) cap hp kk))]; try eassumption; try pj_st_eq; slia.
  -
    rewrite (pj_sxb_small7 k) by (clear - K17; lia). zstep.
    if_cases Kc; zify_cond Kc; [exfalso; pjnorm_in Kc; clear - Kc K17; lia| clear Kc].
    zstep. zstep. pjnorm. rewrite pj_land7 by (clear - R0 SZ; lia).
    zstep. if_cases Kc; zify_cond Kc;
      [exfalso; rewrite !pj_signed_small in Kc by (clear - K17; Z.div_mod_to_equations; lia); clear - Kc K17 KM; lia| clear Kc].
    zstep. apply evt_done.
    eapply aevt_eq; [| eapply (key_hjoinA x0 x56 x256 x264 Σ (mkSbA buf (size + 1) cap hp kk))]; try eassumption; try pj_st_eq; slia.
Qed.

End Pieces.

Local Ltac sb_shzE E D I OK CX :=
  lazymatch goal with
  | HREF : SREFA _ _ _ _ _ ?mr, MU : munch _ ?mr ?mm, WM : wmono asegs ?mr ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let SHZ := fresh "SHZ" in let R64 := fresh "RD64" in let R72 := fresh "RD72" in let R80 := fresh "RD80" in
    pose proof (shz_sb_mu RT AF E D I OK CX _ _ _ mm HREF MU WM) as SHZ;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 64) ltac:(clear; lia)) as R64;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 72) ltac:(clear; lia)) as R72;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 80) ltac:(clear; lia)) as R80; clear SHZ
  end.

Local Ltac hbE E D I OK CX c k :=
  let G := fresh "G" in let G2 := fresh "G" in let RD := fresh "RD" in
  lazymatch goal with
  | HREF : SREFA _ _ _ _ _ ?mr, MU : munch _ ?mr ?mm, WM : wmono asegs ?mr ?mm, C0 : 0 <= c, CL : c + ?l + 5 <= _, L0 : 0 <= ?l |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (G : 0 <= c + k < pa_sn E) by (clear - C0 CL L0; lia);
    assert (G2 : pa_SBUF E + c + k = pa_SBUF E + (c + k)) by (clear; lia);
    pose proof (read1_at mm _ _ (sbuf_read_mu RT AF E D I OK CX _ _ _ mm _ HREF MU WM G) _ G2) as RD; clear G G2; astep; clear RD
  end.

Theorem key_proofA : key_stmtA RT PMc.
Proof using AF RC FDO MST GROW TABS.
  unfold key_stmtA.
  intros E D I K isobj Σ st m F fc i c l dp A X xs4 xs5 xra xt0 xt1 xt2 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt6 OK CX HSM FRM Hi HT HSTR Hdp ACC BUD CR X0 HK.
  pose proof HSTR as (C0 & L0 & CL & LE & _).
  pose proof (S_rangeA E c OK) as BR0. pose proof (S_rangeA E (c + 1) OK) as BR1. pose proof (S_rangeA E (c + 2) OK) as BR2. pose proof (S_rangeA E (c + 3) OK) as BR3.
  pose proof (sctx_out E D I OK CX) as OUTB.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ser_envA OK CX. str_envA_sb OK. apply (aevt_evt RT AF PMc MST). ser_open HSM OK. unfold MASK56 in *.

  pose proof (shz_doc_mu RT AF E D I OK CX Σ _ _ _ HREF MU WM) as SHD.
  pose proof (shz_rd _ _ _ SHD (pa_DOC E) ltac:(clear; lia)) as RD.
  pose proof (shz_rd _ _ _ SHD (pa_DOC E + 8) ltac:(clear; lia)) as RD8. clear SHD.
  astep. astep. astep. clear RD.

  pose proof (doc_cells_mu RT AF E D I OK CX Σ _ _ _ HREF MU WM) as DOCC.
  pose proof (shz_tape_mu RT AF E D I OK CX Σ _ _ _ HREF MU WM) as SHTP.
  assert (G : pa_TAPE E <= pa_TAPE E + 8 * i < pa_TAPE E + 8 * pa_n E) by (clear - Hi; lia).
  pose proof (shz_rd _ _ _ SHTP _ G) as RD. clear G SHTP.
  step. zstep. pjnorm. zstep. astep. astep. astep. astep. clear RD.

  step. astep. astep. astep. astep. clear RD8.

  pose proof (tape_read_mu RT AF E D I OK CX Σ _ _ _ i HREF MU WM ltac:(clear - Hi; lia)) as RDT. rewrite HT in RDT.
  assert (C56 : 0 <= c < 2 ^ 56) by (clear - C0 CL SL S0 LQ QT L0; lia).
  assert (T8 : 0 <= t_str < 256) by (unfold t_str; clear; lia).
  pose proof (tword_range t_str c T8 C56) as TWR.
  step. clear RDT. step. step. zstep.
  rewrite ?(Z.mod_small (tword t_str c) 18446744073709551616) by (clear - TWR; lia).
  rewrite ?pj_land64 by (clear - TWR; lia).
  assert (EA : Z.land (tword t_str c) 72057594037927935 = c).
  { rewrite land_mask56 by (clear - TWR; lia). apply tval_tword. exact C56. }
  rewrite !EA. clear EA DOCC T8. zstep.

  pose proof (shz_sbufA RT AF E D I Σ _ _ _ OK CX HREF MU WM) as SHS.
  assert (G : pa_SBUF E <= pa_SBUF E + c < pa_SBUF E + pa_sn E) by (clear - C0 CL L0; lia).
  pose proof (shz_rd _ _ _ SHS _ G) as RD. clear G. astep. astep. astep. astep. clear RD.
  assert (G : pa_SBUF E <= pa_SBUF E + c + 3 < pa_SBUF E + pa_sn E) by (clear - C0 CL L0; lia).
  pose proof (shz_rd _ _ _ SHS _ G) as RD. clear G. astep. astep. astep. astep. astep. clear RD. clear SHS.

  step. astep. step. sb_shzE E D I OK CX. astep. astep. clear RD64 RD72 RD80.

  step. step. step. astep. sb_shzE E D I OK CX. astep. astep. clear RD64 RD72 RD80.

  step. step.
  assert (G : 0 <= c < pa_sn E) by (clear - C0 CL L0; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (sbuf_read_mu RT AF E D I OK CX _ _ _ mm _ HREF MU WM G) as RD end.
  clear G. astep. clear RD.
  hbE E D I OK CX c 1. hbE E D I OK CX c 2. hbE E D I OK CX c 3.

  zstep. step. step.
  if_cases Kc; zify_cond Kc; pjnorm_in Kc.
  -
    ser_close HSM2 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (key_htailA E D I K isobj i c l dp A X OK CX Hi HSTR Hdp BUD X0 HK _ (Z_to_bv 64 0) _ _ _ Σ (mkSbA buf size cap hp kk))];
      try eassumption; try pj_st_eq; cbn [sa_size sa_cap]; clear - Kc ACC; lia.
  -
    zstep. pjnorm. step. zstep. step. zstep. zstep. zstep. zstep.
    ser_close HSM3 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (ser_growA RT AF PMc GROW E D I _ _ _ _ _ _ isobj Σ (mkSbA buf size cap hp kk) _ K (2 * cap) X 0xb32c8)];
      [pj_st_eq| exact OK| exact CX| exact HSM3| | exact CR| exact X0| clear; lia| reflexivity|].
    { eapply (ser_req_ok2A RT E D I); [exact OK| exact CX| exact HSM3|]. cbn [sa_cap sa_size] in *. clear - Kc ACC BUD L0. lia. }
    intros Σ' NEW m' F' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CR4.
    apply (aevt_evt RT AF PMc MST). ser_open HSM4 OK.
    cbn [Pj_ser_defsA.xj0 Pj_ser_defsA.xj56 Pj_ser_defsA.xj64 Pj_ser_defsA.xj96 Pj_ser_defsA.xj192 Pj_ser_defsA.xj200 Pj_ser_defsA.xj208 Pj_ser_defsA.xj256 Pj_ser_defsA.xj264] in *.

    zstep. zstep. zstep. step. zstep. step. step.
    ser_close HSM5 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (key_htailA E D I K isobj i c l dp A X OK CX Hi HSTR Hdp BUD X0 HK _ (Z_to_bv 64 0) _ _ _ Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW (2 * cap)))];
      try eassumption; try pj_st_eq; unfold sb_grownA; cbn [sa_size sa_cap sa_buf sa_heap sa_k]; clear - Kc ACC SZ R1; lia.
Qed.

End Key.

Theorem key_okA : forall (RT : rt_sig), art_facts RT -> rt_contracts RT -> forall PMc : Model -> Prop, fdfs_only PMc -> mat_stable PMc ->
  grow_cpsA RT PMc -> key_stmtA RT PMc.
Proof.
  intros RT AF RC PMc FDO MST GROW. exact (key_proofA RT AF RC PMc FDO MST GROW (tabs_accA RT AF)).
Qed.
