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
     Pj_ser_keyA_a.
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

Section KeyE.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis GROW : grow_cpsA RT PMc.
Hypothesis TABS : forall Σ m, ART RT Σ m -> acc asegs m PJ_TABS_A PJ_TABS_LEN.
Notation aevt := (aevt RT PMc).

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
Notation kesc_botA_K := (Pj_ser_keyA_a.kesc_botA_K RT PMc E I K isobj i c l dp A X).
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

Section Esc.
  Variable t : Z.
  Hypothesis KB : kesc_botA_K t.
  Hypothesis HT : 0 <= t < l.
  Notation q_tailA := (Pj_ser_keyA_a.q_tailA RT AF RC PMc FDO MST GROW TABS E D I K isobj i c l dp A X OK CX Hi HSTR Hdp BUD X0 HK t KB HT).
  Notation b_tailA := (Pj_ser_keyA_a.b_tailA RT AF RC PMc FDO MST GROW TABS E D I K isobj i c l dp A X OK CX Hi HSTR Hdp BUD X0 HK t KB HT).

  Local Ltac entry2 TL buf size cap hp kk HSM ACC CR Kc :=

    step; step; step; zstep; step;
    if_cases Kc; zify_cond Kc; pjnorm_in Kc;
    [
      let HSM2 := fresh "HSM2" in ser_close HSM2 OK CX; apply evt_done;
      eapply aevt_eq; [| TL (mkSbA buf size cap hp kk)]; try eassumption; try pj_st_eq; slia
    |
      zstep; pjnorm; zstep; zstep ].

  Lemma esc_quoteA : forall x0 x56 x256 x264 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 : word),
    SERMK x0 x56 x256 x264 Σ st m -> frm0 fc -> sa_size st <= A + 1 + 6 * t -> CREDA RT E I Σ X st ->
    aevt Σ K (KST 0xb372c xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 (wz (l - t)) (wz (DATA + t)) (wz (pa_SB E)) (wz (DATA + t)) xt3 xt4 F fc m).
  Proof using AF RC FDO MST GROW TABS OK CX Hi HSTR Hdp BUD X0 HK KB HT.
    intros x0 x56 x256 x264 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 HSM FRM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM. sb_shz.

    astep. astep. step. astep. astep.
    entry2 ltac:(fun st => eapply (q_tailA x0 x56 x256 x264 Σ st)) buf size cap hp kk HSM ACC CR Kc.
    lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 _ ?mm _) =>
    assert (GROWN : forall (z : Z) (ya0 : word), z = Z.max (2 * cap) (size + 2) ->
      evt asegs (fun ms' => aevt Σ K ms')
        (KST 0xb376c xra xt0 xt1 xt2 ya0 (wz z) xa2 xa3 xa4 xa5 xa6 xa7 (wz (size + 2)) (wz (l - t)) (wz (DATA + t)) (wz (pa_SB E)) (wz (DATA + t)) xt3 xt4 F0 fc0 mm)) end.
    { intros z ya0 EZ.

      zstep. zstep.
      ser_close HSM3 OK CX. apply evt_done.
      eapply aevt_eq; [| eapply (ser_growA RT AF PMc GROW E D I _ _ _ _ _ _ isobj Σ (mkSbA buf size cap hp kk) _ K z X 0xb3774)];
        [pj_st_eq| exact OK| exact CX| exact HSM3| | exact CR| exact X0| clear; lia| reflexivity|].
      { rewrite EZ. eapply (ser_req_okA RT E D I); [exact OK| exact CX| exact HSM3| cbn [sa_cap]; clear - Kc; lia|].
        cbn [sa_size]. clear - ACC BUD HT. lia. }
      intros Σ' NEW m' F' yt0 yt1 yt2 ya0' ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CR4.
      apply (aevt_evt RT AF PMc MST). open HSM4.

      step. step.
      ser_close HSM5 OK CX. apply evt_done.
      eapply aevt_eq; [| eapply (q_tailA x0 x56 x256 x264 Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW z))]; try eassumption; try pj_st_eq;
        unfold sb_grownA; cbn [sa_size sa_cap sa_buf sa_heap sa_k]; rewrite ?EZ; clear - Kc ACC SZ; lia. }
    if_cases K2; zify_cond K2; pjnorm_in K2.
    - eapply (GROWN (size + 2)). clear - K2 Kc; lia.
    -   zstep. eapply (GROWN (2 * cap)). clear - K2 Kc; lia.
  Qed.

  Lemma esc_bslashA : forall x0 x56 x256 x264 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 : word),
    SERMK x0 x56 x256 x264 Σ st m -> frm0 fc -> sa_size st <= A + 1 + 6 * t -> CREDA RT E I Σ X st ->
    aevt Σ K (KST 0xb37dc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 (wz (l - t)) (wz (DATA + t)) (wz (pa_SB E)) (wz (DATA + t)) xt3 xt4 F fc m).
  Proof using AF RC FDO MST GROW TABS OK CX Hi HSTR Hdp BUD X0 HK KB HT.
    intros x0 x56 x256 x264 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 HSM FRM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM. sb_shz.

    astep. astep. step. astep. astep.
    entry2 ltac:(fun st => eapply (b_tailA x0 x56 x256 x264 Σ st)) buf size cap hp kk HSM ACC CR Kc.
    lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 _ ?mm _) =>
    assert (GROWN : forall (z : Z) (ya0 : word), z = Z.max (2 * cap) (size + 2) ->
      evt asegs (fun ms' => aevt Σ K ms')
        (KST 0xb381c xra xt0 xt1 xt2 ya0 (wz z) xa2 xa3 xa4 xa5 xa6 xa7 (wz (size + 2)) (wz (l - t)) (wz (DATA + t)) (wz (pa_SB E)) (wz (DATA + t)) xt3 xt4 F0 fc0 mm)) end.
    { intros z ya0 EZ.

      zstep. zstep.
      ser_close HSM3 OK CX. apply evt_done.
      eapply aevt_eq; [| eapply (ser_growA RT AF PMc GROW E D I _ _ _ _ _ _ isobj Σ (mkSbA buf size cap hp kk) _ K z X 0xb3824)];
        [pj_st_eq| exact OK| exact CX| exact HSM3| | exact CR| exact X0| clear; lia| reflexivity|].
      { rewrite EZ. eapply (ser_req_okA RT E D I); [exact OK| exact CX| exact HSM3| cbn [sa_cap]; clear - Kc; lia|].
        cbn [sa_size]. clear - ACC BUD HT. lia. }
      intros Σ' NEW m' F' yt0 yt1 yt2 ya0' ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CR4.
      apply (aevt_evt RT AF PMc MST). open HSM4.

      step. step.
      ser_close HSM5 OK CX. apply evt_done.
      eapply aevt_eq; [| eapply (b_tailA x0 x56 x256 x264 Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW z))]; try eassumption; try pj_st_eq;
        unfold sb_grownA; cbn [sa_size sa_cap sa_buf sa_heap sa_k]; rewrite ?EZ; clear - Kc ACC SZ; lia. }
    if_cases K2; zify_cond K2; pjnorm_in K2.
    - eapply (GROWN (size + 2)). clear - K2 Kc; lia.
    -   zstep. eapply (GROWN (2 * cap)). clear - K2 Kc; lia.
  Qed.

  Lemma p_finA : forall x0 x56 x256 x264 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 : word),
    SERMK x0 x56 x256 x264 Σ st m -> frm0 fc -> 1 <= sa_size st -> sa_size st <= A + 1 + 6 * (t + 1) -> CREDA RT E I Σ X st ->
    aevt Σ K (KST 0xb3a84 xra xt0 xt1 xt2 (wz (sa_buf st + (sa_size st - 1))) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 (wz (l - t)) (wz (DATA + t)) (wz (pa_SB E)) (wz (DATA + t)) xt3 xt4 F fc m).
  Proof using AF RC FDO MST GROW TABS OK CX Hi HSTR Hdp BUD X0 HK KB HT.
    intros x0 x56 x256 x264 Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 HSM FRM SZ1 ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf] in *.
    ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM.
    pose proof (buf_factsA RT AF E D I Σ _ _ (si_b I) OK CX HREF) as (_ & _ & _ & _ & APB). cbn [sa_buf sa_cap] in APB.
    pose proof (APB (buf + (size - 1)) ltac:(clear - SZ1 SZ; lia)) as (A1 & A2 & A3 & A4). clear APB.

    step. pj_store_done. step.
    ser_close HSM2 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (KB x0 x56 x256 x264 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
  Qed.

  Lemma p_tailA : forall x0 x56 x256 x264 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 : word),
    SERMK x0 x56 x256 x264 Σ st m -> frm0 fc -> sa_size st + 1 <= sa_cap st -> sa_size st <= A + 1 + 6 * t -> CREDA RT E I Σ X st ->
    aevt Σ K (KST 0xb3a40 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 (wz (l - t)) (wz (DATA + t)) (wz (pa_SB E)) (wz (DATA + t)) xt3 xt4 F fc m).
  Proof using AF RC FDO MST GROW TABS OK CX Hi HSTR Hdp BUD X0 HK KB HT.
    intros x0 x56 x256 x264 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 HSM FRM ROOM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM. sb_shz.

    step. astep. astep. astep. astep.

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
      rewrite sxb_z8. zstep. if_false. apply evt_done.
      eapply aevt_eq; [| eapply (p_finA x0 x56 x256 x264 Σ (mkSbA buf (size + 1) cap hp kk))]; try eassumption; try pj_st_eq; slia.
    -
      rewrite (pj_sxb_small7 k) by (clear - K17; lia). zstep.
      if_cases Kc; zify_cond Kc; [clear Kc| exfalso; pjnorm_in Kc; clear - Kc K17; lia].
      zstep. pjnorm. rewrite pj_land7 by (clear - R0 SZ; lia).
      zstep. if_cases Kc; zify_cond Kc;
        [clear Kc| exfalso; rewrite !pj_signed_small in Kc by (clear - K17; Z.div_mod_to_equations; lia); clear - Kc K17 KM; lia].
      apply evt_done.
      eapply aevt_eq; [| eapply (p_finA x0 x56 x256 x264 Σ (mkSbA buf (size + 1) cap hp kk))]; try eassumption; try pj_st_eq; slia.
  Qed.

  Lemma esc_plainA : forall x0 x56 x256 x264 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 : word),
    SERMK x0 x56 x256 x264 Σ st m -> frm0 fc -> sa_size st <= A + 1 + 6 * t -> CREDA RT E I Σ X st ->
    aevt Σ K (KST 0xb39fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 (wz (l - t)) (wz (DATA + t)) (wz (pa_SB E)) (wz (DATA + t)) xt3 xt4 F fc m).
  Proof using AF RC FDO MST GROW TABS OK CX Hi HSTR Hdp BUD X0 HK KB HT.
    intros x0 x56 x256 x264 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 HSM FRM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM. sb_shz.

    step. astep. astep. astep. astep.

    step. step. step. zstep. step.
    if_cases Kc; zify_cond Kc; pjnorm_in Kc.
    -
      ser_close HSM2 OK CX. apply evt_done.
      eapply aevt_eq; [| eapply (p_tailA x0 x56 x256 x264 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
    -
      zstep. pjnorm. zstep. zstep.
      ser_close HSM3 OK CX. apply evt_done.
      eapply aevt_eq; [| eapply (ser_growA RT AF PMc GROW E D I _ _ _ _ _ _ isobj Σ (mkSbA buf size cap hp kk) _ K (2 * cap) X 0xb3a38)];
        [pj_st_eq| exact OK| exact CX| exact HSM3| | exact CR| exact X0| clear; lia| reflexivity|].
      { eapply (ser_req_ok2A RT E D I); [exact OK| exact CX| exact HSM3|]. cbn [sa_cap sa_size] in *. clear - Kc ACC BUD HT. lia. }
      intros Σ' NEW m' F' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CR4.
      apply (aevt_evt RT AF PMc MST). open HSM4.

      step. step.
      ser_close HSM5 OK CX. apply evt_done.
      eapply aevt_eq; [| eapply (p_tailA x0 x56 x256 x264 Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW (2 * cap)))]; try eassumption; try pj_st_eq;
        unfold sb_grownA; slia.
  Qed.

  Lemma ctl_finA : forall (n : Z) x0 x56 x256 x264 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 : word),
    SERMK x0 x56 x256 x264 Σ st m -> frm0 fc -> sa_size st + n <= sa_cap st -> 0 <= n -> sa_size st + n <= A + 1 + 6 * (t + 1) -> CREDA RT E I Σ X st ->
    aevt Σ K (KST 0xb39e4 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (sa_size st + n)) (wz (l - t)) (wz (DATA + t)) xs9 (wz (DATA + t)) xt3 xt4 F fc m).
  Proof using AF RC FDO MST GROW TABS OK CX Hi HSTR Hdp BUD X0 HK KB HT.
    intros n x0 x56 x256 x264 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 HSM FRM ROOM N0 ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM. sb_shz.

    astep. astep. unbox FSB; unbox SHSB. step. box_disj. step. step.
    ser_close HSM2 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (KB x0 x56 x256 x264 Σ (mkSbA buf (size + n) cap hp kk))]; try eassumption; try pj_st_eq; slia.
  Qed.

  Lemma ctl_tailA : forall (n : Z) x0 x56 x256 x264 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 : word),
    SERMK x0 x56 x256 x264 Σ st m -> frm0 fc -> sa_size st + n <= sa_cap st -> 1 <= n <= 7 -> sa_size st + n <= A + 1 + 6 * (t + 1) -> CREDA RT E I Σ X st ->
    aevt Σ K (KST 0xb39a0 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (sa_size st + n)) (wz (l - t)) (wz (DATA + t)) (wz n) (wz (DATA + t)) xt3 xt4 F fc m).
  Proof using AF RC FDO MST GROW TABS OK CX Hi HSTR Hdp BUD X0 HK KB HT.
    intros n x0 x56 x256 x264 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 HSM FRM ROOM N17 ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ser_envA OK CX. apply (aevt_evt RT AF PMc MST). pose proof HSM as HSM0. open HSM. sb_shz.

    zstep. if_cases Kz; zify_cond Kz; pjnorm_in Kz; [exfalso; clear - Kz N17; lia|].

    step. astep. astep. astep. astep.

    step. step. step. zstep. step. zstep. zstep.

    pose proof (f3_rngA RT E D I _ _ _ _ _ _ isobj Σ _ m (si_f I + 400) n OK CX HSM0 ltac:(clear; lia) ltac:(clear -N17; lia) ltac:(clear -N17; lia))
      as (RC3 & F3a & F3b & (src & SRC & SRCL)).
    pose proof (f3tmp400_accA m (si_f I) SHF Ef ltac:(clear - F0; lia)) as AC8.
    pose proof (buf_factsA RT AF E D I Σ _ _ (si_b I) OK CX HREF) as (_ & _ & _ & _ & APB). cbn [sa_buf sa_cap] in APB.
    assert (APT : buf + size + n <= si_f I + 400 \/ si_f I + 400 + n <= buf + size).
    { apply (apart_of_pointwise (buf + size) n (si_f I + 400) n); [| clear - N17; lia| clear - N17; lia].
      intros y Hy. pose proof (APB y ltac:(clear - Hy ROOM SZ N17; lia)) as (A1 & _). clear - A1 N17. lia. }
    clear APB.
    ser_close HSM2 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (ser_copyA RT AF RC PMc FDO MST e_asan_memcpy E D I _ _ _ _ _ _ isobj Σ (mkSbA buf size cap hp kk) m K (si_f I + 400) n 0xb39dc src)];
      [pj_st_eq| left; reflexivity| exact OK| exact CX| exact HSM2| exact SRC| exact SRCL| clear - N17; lia| cbn [sa_size sa_cap]; exact ROOM
      | eapply acc_sub; [exact AC8| clear; lia| clear - N17; lia]| exact RC3| exact F3a| exact F3b| intros _; cbn [sa_buf sa_size]; exact APT
      | clear; lia| reflexivity|].
    intros m' F' yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CPY.
    apply (aevt_evt RT AF PMc MST). open HSM4.

    step. step.
    ser_close HSM5 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (ctl_finA n x0 x56 x256 x264 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
  Qed.

  Local Ltac escb m b MI BR HB k :=
    let G := fresh "G" in let G2 := fresh "G" in let ER := fresh "ER" in let RD := fresh "RD" in
    pose proof (esc_byte_range (8 * b + k)) as ER;
    assert (G : 0 <= 8 * b + k < 256) by (clear - BR HB; lia);
    assert (G2 : 144988 + 8 * b + k = 144988 + (8 * b + k)) by (clear; lia);
    pose proof (read1_at m _ _ (esc_readA m _ MI G) _ G2) as RD; clear G G2; unfold PJ_ESC_TAB_A in RD; astep; clear RD.

  Lemma esc_ctlA : forall x0 x56 x256 x264 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 : word),
    pa_S E (c + 4 + t) <= 31 ->
    SERMK x0 x56 x256 x264 Σ st m -> frm0 fc -> sa_size st <= A + 1 + 6 * t -> CREDA RT E I Σ X st ->
    aevt Σ K (KST 0xb38b0 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 (wz (l - t)) (wz (DATA + t)) (wz (pa_SB E)) (wz (DATA + t)) xt3 xt4 F fc m).
  Proof using AF RC FDO MST GROW TABS OK CX Hi HSTR Hdp BUD X0 HK KB HT.
    intros x0 x56 x256 x264 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 HB HSM FRM ACC CR.
    pose proof HSTR as (C0 & L0 & CL & _).
    pose proof (S_rangeA E (c + 4 + t) OK) as BR. set (b := pa_S E (c + 4 + t)) in *.
    pose proof (esc_len_range b ltac:(clear - BR HB; lia)) as NR. rewrite <- esc_len_byte in NR. set (n := esc_byte (8 * b)) in *.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM. unfold PJ_ESC_TAB_A in *.

    assert (G : 0 <= c + 4 + t < pa_sn E) by (clear - C0 CL HT; lia).
    assert (G2 : pa_SBUF E + c + 4 + t = pa_SBUF E + (c + 4 + t)) by (clear; lia).
    pose proof (read1_at m _ _ (sbuf_read_mu RT AF E D I OK CX Σ _ _ m _ HREF MU WM G) _ G2) as RD. clear G G2. fold b in RD.
    astep. clear RD.

    zstep. pjnorm. step. zstep.

    pose proof (shz_tabs m (TABS Σ m (ART_mu RT AF E D I Σ _ _ m OK CX HREF MU WM))) as SHTB.
    assert (G : PJ_TABS_A <= 144988 + 8 * b < PJ_TABS_A + PJ_TABS_LEN) by (unfold PJ_TABS_A, PJ_TABS_LEN; clear - BR HB; lia).
    pose proof (shz_rd m _ _ SHTB _ G) as RD. clear G. do 4 astep. clear RD.
    assert (G : PJ_TABS_A <= 144988 + 8 * b + 1 < PJ_TABS_A + PJ_TABS_LEN) by (unfold PJ_TABS_A, PJ_TABS_LEN; clear - BR HB; lia).
    pose proof (shz_rd m _ _ SHTB _ G) as RD. clear G. do 4 astep. clear RD.
    pose proof (esc_byte_range (8 * b)) as ER0. fold n in ER0.
    assert (G : 0 <= 8 * b < 256) by (clear - BR HB; lia).
    pose proof (esc_readA m _ MI G) as RD. clear G. unfold PJ_ESC_TAB_A in RD. fold n in RD. astep. clear RD.
    astep.
    assert (G : PJ_TABS_A <= 144988 + 8 * b + 7 < PJ_TABS_A + PJ_TABS_LEN) by (unfold PJ_TABS_A, PJ_TABS_LEN; clear - BR HB; lia).
    pose proof (shz_rd m _ _ SHTB _ G) as RD. clear G. do 5 astep. clear RD. clear SHTB.

    escb m b MI BR HB 2. escb m b MI BR HB 3. escb m b MI BR HB 4. escb m b MI BR HB 1.
    astep. astep. astep. astep.
    escb m b MI BR HB 5. escb m b MI BR HB 6. astep. escb m b MI BR HB 7.
    do 5 astep.
    repeat match goal with |- context [Z_to_bv 64 (Z.lor ?x ?y)] => let j := fresh "jw" in set (j := Z_to_bv 64 (Z.lor x y)) in *; clearbody j end.
    repeat match goal with |- context [Z_to_bv 64 (Z.shiftr ?x ?y)] => let j := fresh "jw" in set (j := Z_to_bv 64 (Z.shiftr x y)) in *; clearbody j end.

    step. unbox FSB; unbox SHf. step. pj_store_done. step. pj_store_done. step. pj_store_done. box_disj.
    sb_shz.

    astep. astep. step. astep. astep.

    step. step. step. zstep. step.
    if_cases Kc; zify_cond Kc; pjnorm_in Kc.
    -
      ser_close HSM2 OK CX. apply evt_done.
      eapply aevt_eq; [| eapply (ctl_tailA n x0 x56 x256 x264 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
    -
      zstep. pjnorm. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 _ ?mm _) =>
      assert (GROWN : forall (z : Z) (ya0 ya2 ya3 ya4 ya5 ya6 ya7 : word), z = Z.max (2 * cap) (size + n) ->
        evt asegs (fun ms' => aevt Σ K ms')
          (KST 0xb3990 xra xt0 xt1 xt2 ya0 (wz z) ya2 ya3 ya4 ya5 ya6 ya7 (wz (size + n)) (wz (l - t)) (wz (DATA + t)) (wz n) (wz (DATA + t)) xt3 xt4 F0 fc0 mm)) end.
      { intros z ya0 ya2 ya3 ya4 ya5 ya6 ya7 EZ.

        step. zstep.
        ser_close HSM3 OK CX. apply evt_done.
        eapply aevt_eq; [| eapply (ser_growA RT AF PMc GROW E D I _ _ _ _ _ _ isobj Σ (mkSbA buf size cap hp kk) _ K z X 0xb3998)];
          [pj_st_eq| exact OK| exact CX| exact HSM3| | exact CR| exact X0| clear; lia| reflexivity|].
        { rewrite EZ. eapply (ser_req_okA RT E D I); [exact OK| exact CX| exact HSM3| cbn [sa_cap]; clear - Kc; lia|].
          cbn [sa_size]. clear - ACC BUD HT NR. lia. }
        intros Σ' NEW m' F' yt0 yt1 yt2 za0 za1 za2 za3 za4 za5 za6 za7 yt3 yt4 yt5 yt6 HSM4 CR4.
        apply (aevt_evt RT AF PMc MST). open HSM4.

        step. step.
        ser_close HSM5 OK CX. apply evt_done.
        eapply aevt_eq; [| eapply (ctl_tailA n x0 x56 x256 x264 Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW z))]; try eassumption; try pj_st_eq;
          unfold sb_grownA; cbn [sa_size sa_cap sa_buf sa_heap sa_k]; rewrite ?EZ; clear - Kc ACC SZ NR; lia. }
      if_cases K2; zify_cond K2; pjnorm_in K2.
      + eapply (GROWN (size + n)). clear - K2 Kc; lia.
      +   zstep. eapply (GROWN (2 * cap)). clear - K2 Kc; lia.
  Qed.

End Esc.

Definition kesc_head_stmtA (f : nat) : Prop :=
  forall (t : Z) x0 x56 x256 x264 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
         (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 : word),
    l - t <= Z.of_nat f -> 0 <= t < l ->
    SERMK x0 x56 x256 x264 Σ st m -> frm0 fc -> sa_size st <= A + 1 + 6 * t -> CREDA RT E I Σ X st ->
    aevt Σ K (KST 0xb3708 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 (wz (l - t)) (wz (DATA + t)) (wz (pa_SB E)) (wz (DATA + t)) xt3 xt4 F fc m).

Notation key_closeA := (Pj_ser_keyA_a.key_closeA RT AF RC PMc FDO MST GROW TABS E D I K isobj i c l dp A X OK CX Hi HSTR Hdp BUD X0 HK).

Lemma esc_botA : forall f, kesc_head_stmtA f -> forall t, 0 <= t < l -> l - t <= Z.of_nat (S f) -> kesc_botA_K t.
Proof using AF RC FDO MST GROW TABS OK CX Hi HSTR Hdp BUD X0 HK.
  intros f IH t HT HF0. unfold Pj_ser_keyA_a.kesc_botA_K.
  intros x0 x56 x256 x264 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 HSM FRM ACC CR.
  pose proof HSTR as (C0 & L0 & CL & _).
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ser_envA OK CX. str_envA_sb OK. apply (aevt_evt RT AF PMc MST). open HSM.

  zstep. zstep. zstep. zstep.
  ser_close HSM2 OK CX.
  if_cases Kc; zify_cond Kc; pjnorm_in Kc.
  -
    apply evt_done.
    eapply aevt_eq; [| eapply (IH (t + 1) x0 x56 x256 x264 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq;
      cbn [sa_size]; clear - HF0 HT Kc ACC; lia.
  -
    zstep. apply evt_done.
    eapply aevt_eq; [| eapply (key_closeA x0 x56 x256 x264 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq;
      cbn [sa_size]; clear - ACC HT Kc; lia.
Qed.

Lemma esc_headA : forall f, kesc_head_stmtA f.
Proof using AF RC FDO MST GROW TABS OK CX Hi HSTR Hdp BUD X0 HK.
  induction f as [|f IH]; unfold kesc_head_stmtA;
    intros t x0 x56 x256 x264 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 HF0 HT HSM FRM ACC CR; [lia|].
  pose proof (esc_botA f IH t HT HF0) as KB.
  pose proof HSTR as (C0 & L0 & CL & _).
  pose proof (S_rangeA E (c + 4 + t) OK) as BR. set (b := pa_S E (c + 4 + t)) in *.
  pose proof HSM as HSM0.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ser_envA OK CX. str_envA_sb OK. apply (aevt_evt RT AF PMc MST). open HSM.

  pose proof (shz_sbufA RT AF E D I Σ _ _ m OK CX HREF MU WM) as SHS.
  assert (G : pa_SBUF E <= pa_SBUF E + c + 4 + t < pa_SBUF E + pa_sn E) by (clear - C0 CL HT; lia).
  pose proof (shz_rd m _ _ SHS _ G) as RD. clear G.
  astep. astep. astep. astep.

  assert (G : 0 <= c + 4 + t < pa_sn E) by (clear - C0 CL HT; lia).
  assert (G2 : pa_SBUF E + c + 4 + t = pa_SBUF E + (c + 4 + t)) by (clear; lia).
  pose proof (read1_at m _ _ (sbuf_read_mu RT AF E D I OK CX Σ _ _ m _ HREF MU WM G) _ G2) as RD1. clear G G2. fold b in RD1.
  astep. clear RD1.

  zstep. zstep. if_cases K1; zify_cond K1; pjnorm_in K1.
  - clear RD. ser_close HSM2 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (esc_bslashA t KB HT x0 x56 x256 x264 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
  -
    zstep. zstep. if_cases K2; zify_cond K2; pjnorm_in K2.
    +
      zstep. zstep. if_cases K3; zify_cond K3; pjnorm_in K3.
      * clear RD. ser_close HSM2 OK CX. apply evt_done.
        eapply aevt_eq; [| eapply (esc_plainA t KB HT x0 x56 x256 x264 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
      *
        astep. astep. clear RD. ser_close HSM2 OK CX. apply evt_done.
        eapply aevt_eq; [| eapply (esc_ctlA t KB HT x0 x56 x256 x264 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq;
          subst b; clear - K3 ACC; lia.
    + clear RD. ser_close HSM2 OK CX. apply evt_done.
      eapply aevt_eq; [| eapply (esc_quoteA t KB HT x0 x56 x256 x264 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
Qed.

End KeyE.
