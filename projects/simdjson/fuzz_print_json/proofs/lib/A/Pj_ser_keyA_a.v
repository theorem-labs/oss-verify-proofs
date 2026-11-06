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
     Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_hkit3A Atp_hkit4A Pj_rtkA Pj_defsA Pj_cpsA Pj_ser_defsA Pj_ser_kitA Pj_ser_callsA Pj_ser_skitA.
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

Section KeyA.
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

Definition kx (x0 x56 x256 x264 : word) : xjA :=
  mkXJ x0 (wz c) (wz (pa_SBUF E)) (wz (pa_DOC E / 8)) (wz (shad (pa_SB E + 72))) (wz (shad (pa_SB E + 64))) (wz (shad (pa_SB E + 80))) x256 x264.
Notation SERMK x0 x56 x256 x264 Σ st m :=
  (SERMA RT E I (wz PJ_ESC_TAB_A) (wz (T5A E)) (wz (S64A E)) (wz (S80A E)) (kx x0 x56 x256 x264) ser_shpatA isobj Σ st m).

Notation KST pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs5 xs9 xs10 xs11 xt3 xt4 F fc m :=
  (SSTA I pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
        (Z_to_bv 64 dp) (Z_to_bv 64 (pa_SB E + 72)) xs4 xs5 (Z_to_bv 64 i) (Z_to_bv 64 2147450880) (Z_to_bv 64 PJ_NE_TAB_A) xs9 xs10 xs11
        xt3 xt4 (Z_to_bv 64 (T5A E)) (Z_to_bv 64 (shad (pa_SB E + 72))) F fc m).

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
Local Ltac open HSM := unfold kx in HSM; ser_open HSM OK; cbn [Pj_ser_defsA.xj0 Pj_ser_defsA.xj56 Pj_ser_defsA.xj64 Pj_ser_defsA.xj96 Pj_ser_defsA.xj192 Pj_ser_defsA.xj200 Pj_ser_defsA.xj208 Pj_ser_defsA.xj256 Pj_ser_defsA.xj264] in *.

Lemma colon_finA : forall x0 x56 x256 x264 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa1 xa2 xa4 xa5 xa6 xa7 xs5 xs9 xt3 xt4 : word),
  SERMK x0 x56 x256 x264 Σ st m -> frm0 fc -> 1 <= sa_size st -> sa_size st <= A + (3 + 6 * l) -> CREDA RT E I Σ X st ->
  aevt Σ K (KST 0xb3c1c xra xt0 xt1 xt2 (wz (sa_buf st + (sa_size st - 1))) xa1 xa2 (wz (pa_DOC E / 8)) xa4 xa5 xa6 xa7 (wz (pa_SB E + 80)) xs5 xs9 (wz (pa_SB E)) (wz (pa_DOC E)) xt3 xt4 F fc m).
Proof using AF RC FDO MST GROW TABS OK CX Hi HSTR Hdp BUD X0 HK.
  intros x0 x56 x256 x264 Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa4 xa5 xa6 xa7 xs5 xs9 xt3 xt4 HSM FRM SZ1 ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM.
  pose proof (buf_factsA RT AF E D I Σ _ _ (si_b I) OK CX HREF) as (_ & _ & _ & _ & APB). cbn [sa_buf sa_cap] in APB.
  pose proof (APB (buf + (size - 1)) ltac:(clear - SZ1 SZ; lia)) as (A1 & A2 & A3 & A4). clear APB.

  step. step. pj_store_done. zstep.
  ser_close HSM2 OK CX. apply evt_done.
  eapply (HK Σ (mkSbA buf size cap hp kk) _ F fc); [eexists; exact HSM2| exact FRM| cbn [sa_size]; clear - ACC; lia| exact CR].
Qed.

Lemma colon_tailA : forall x0 x56 x256 x264 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs9 xt3 xt4 : word),
  SERMK x0 x56 x256 x264 Σ st m -> frm0 fc -> sa_size st + 1 <= sa_cap st -> sa_size st <= A + 2 + 6 * l -> CREDA RT E I Σ X st ->
  aevt Σ K (KST 0xb3bd0 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (pa_SB E + 80)) xs5 xs9 (wz (pa_SB E)) (wz (pa_DOC E)) xt3 xt4 F fc m).
Proof using AF RC FDO MST GROW TABS OK CX Hi HSTR Hdp BUD X0 HK.
  intros x0 x56 x256 x264 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs9 xt3 xt4 HSM FRM ROOM ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM. sb_shz.

  step. astep. astep. astep. step. astep.

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
    eapply aevt_eq; [| eapply (colon_finA x0 x56 x256 x264 Σ (mkSbA buf (size + 1) cap hp kk))]; try eassumption; try pj_st_eq; slia.
  -
    rewrite (pj_sxb_small7 k) by (clear - K17; lia). zstep.
    if_cases Kc; zify_cond Kc; [exfalso; pjnorm_in Kc; clear - Kc K17; lia| clear Kc].
    zstep. zstep. pjnorm. rewrite pj_land7 by (clear - R0 SZ; lia).
    zstep. if_cases Kc; zify_cond Kc;
      [exfalso; rewrite !pj_signed_small in Kc by (clear - K17; Z.div_mod_to_equations; lia); clear - Kc K17 KM; lia| clear Kc].
    zstep. apply evt_done.
    eapply aevt_eq; [| eapply (colon_finA x0 x56 x256 x264 Σ (mkSbA buf (size + 1) cap hp kk))]; try eassumption; try pj_st_eq; slia.
Qed.

Lemma colonA : forall x0 x56 x256 x264 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs9 xt3 xt4 : word),
  SERMK x0 x56 x256 x264 Σ st m -> frm0 fc -> sa_size st <= A + 2 + 6 * l -> CREDA RT E I Σ X st ->
  aevt Σ K (KST 0xb3b9c xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (pa_SB E + 80)) xs5 xs9 (wz (pa_SB E)) (wz (pa_DOC E)) xt3 xt4 F fc m).
Proof using AF RC FDO MST GROW TABS OK CX Hi HSTR Hdp BUD X0 HK.
  intros x0 x56 x256 x264 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs9 xt3 xt4 HSM FRM ACC CR.
  pose proof HSTR as (C0 & L0 & CL & _).
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM. sb_shz.

  step. astep. astep. step. step. zstep. step.
  if_cases Kc; zify_cond Kc; pjnorm_in Kc.
  -
    ser_close HSM2 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (colon_tailA x0 x56 x256 x264 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
  -
    zstep. pjnorm. zstep. zstep.
    ser_close HSM3 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (ser_growA RT AF PMc GROW E D I _ _ _ _ _ _ isobj Σ (mkSbA buf size cap hp kk) _ K (2 * cap) X 0xb3bc8)];
      [pj_st_eq| exact OK| exact CX| exact HSM3| | exact CR| exact X0| clear; lia| reflexivity|].
    { eapply (ser_req_ok2A RT E D I); [exact OK| exact CX| exact HSM3|]. cbn [sa_cap sa_size] in *. clear - Kc ACC BUD. lia. }
    intros Σ' NEW m' F' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CR4.
    apply (aevt_evt RT AF PMc MST). open HSM4.

    step. step.
    ser_close HSM5 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (colon_tailA x0 x56 x256 x264 Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW (2 * cap)))]; try eassumption; try pj_st_eq;
      unfold sb_grownA; slia.
Qed.

Lemma close_finA : forall x0 x56 x256 x264 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs9 xt3 xt4 : word),
  SERMK x0 x56 x256 x264 Σ st m -> frm0 fc -> 1 <= sa_size st -> sa_size st <= A + 2 + 6 * l -> CREDA RT E I Σ X st ->
  aevt Σ K (KST 0xb3b94 xra xt0 xt1 xt2 (wz (sa_buf st + (sa_size st - 1))) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (pa_SB E + 80)) xs5 xs9 (wz (pa_SB E)) (wz (pa_DOC E)) xt3 xt4 F fc m).
Proof using AF RC FDO MST GROW TABS OK CX Hi HSTR Hdp BUD X0 HK.
  intros x0 x56 x256 x264 Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs9 xt3 xt4 HSM FRM SZ1 ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM.
  pose proof (buf_factsA RT AF E D I Σ _ _ (si_b I) OK CX HREF) as (_ & _ & _ & _ & APB). cbn [sa_buf sa_cap] in APB.
  pose proof (APB (buf + (size - 1)) ltac:(clear - SZ1 SZ; lia)) as (A1 & A2 & A3 & A4). clear APB.

  step. step. pj_store_done.
  ser_close HSM2 OK CX. apply evt_done.
  eapply aevt_eq; [| eapply (colonA x0 x56 x256 x264 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
Qed.

Lemma close_tailA : forall x0 x56 x256 x264 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs8 xt3 xt4 : word),
  SERMK x0 x56 x256 x264 Σ st m -> frm0 fc -> sa_size st + 1 <= sa_cap st -> sa_size st <= A + 1 + 6 * l -> CREDA RT E I Σ X st ->
  aevt Σ K (KST 0xb3b4c xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (pa_SB E + 80)) xs5 xs8 (wz (pa_SB E)) (wz (pa_DOC E)) xt3 xt4 F fc m).
Proof using AF RC FDO MST GROW TABS OK CX Hi HSTR Hdp BUD X0 HK.
  intros x0 x56 x256 x264 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs8 xt3 xt4 HSM FRM ROOM ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM. sb_shz.

  step. astep. astep. astep. astep.

  step. step. step. zstep. zstep. unbox FSB; unbox SHSB. step. box_disj.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (acc_buf_mu RT AF E D I OK CX Σ _ _ mm HREF MU WM) as ACCB end.
  cbn [sa_buf sa_cap] in ACCB.
  destruct (acc_read1 _ _ _ (buf + size) ACCB ltac:(clear - ROOM SZ; lia)) as (b & RDB & SOK).
  change (ov_read_bytes asegs _ (wa ((buf + size) / 8 + 2147450880)) 1 = Some [b]) with (ov_read_bytes asegs mm (wa (shad (buf + size))) 1 = Some [b]) in RDB
    || idtac.
  zstep. pjnorm. zstep. shfold. zstep.
  ser_close HSM2 OK CX.
  destruct (pj_sh_ok_cases b (buf + size) SOK) as [-> | (k & -> & K17 & KM)].
  -
    rewrite sxb_z8. zstep. if_true. apply evt_done.
    eapply aevt_eq; [| eapply (close_finA x0 x56 x256 x264 Σ (mkSbA buf (size + 1) cap hp kk))]; try eassumption; try pj_st_eq; slia.
  -
    rewrite (pj_sxb_small7 k) by (clear - K17; lia). zstep.
    if_cases Kc; zify_cond Kc; [exfalso; pjnorm_in Kc; clear - Kc K17; lia| clear Kc].
    zstep. zstep. pjnorm. rewrite pj_land7 by (clear - R0 SZ; lia).
    zstep. if_cases Kc; zify_cond Kc;
      [exfalso; rewrite !pj_signed_small in Kc by (clear - K17; Z.div_mod_to_equations; lia); clear - Kc K17 KM; lia| clear Kc].
    zstep. apply evt_done.
    eapply aevt_eq; [| eapply (close_finA x0 x56 x256 x264 Σ (mkSbA buf (size + 1) cap hp kk))]; try eassumption; try pj_st_eq; slia.
Qed.

Lemma key_closeA : forall x0 x56 x256 x264 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs5 xs8 xs11 xt3 xt4 : word),
  SERMK x0 x56 x256 x264 Σ st m -> frm0 fc -> sa_size st <= A + 1 + 6 * l -> CREDA RT E I Σ X st ->
  aevt Σ K (KST 0xb3b04 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs5 xs8 (wz (pa_SB E)) xs11 xt3 xt4 F fc m).
Proof using AF RC FDO MST GROW TABS OK CX Hi HSTR Hdp BUD X0 HK.
  intros x0 x56 x256 x264 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs5 xs8 xs11 xt3 xt4 HSM FRM ACC CR.
  pose proof HSTR as (C0 & L0 & CL & _).
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM. sb_shz.

  step. astep. astep. astep. step. step. astep.

  step. step. zstep. step.
  if_cases Kc; zify_cond Kc; pjnorm_in Kc.
  -
    ser_close HSM2 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (close_tailA x0 x56 x256 x264 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
  -
    zstep. pjnorm. zstep. zstep.
    ser_close HSM3 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (ser_growA RT AF PMc GROW E D I _ _ _ _ _ _ isobj Σ (mkSbA buf size cap hp kk) _ K (2 * cap) X 0xb3b44)];
      [pj_st_eq| exact OK| exact CX| exact HSM3| | exact CR| exact X0| clear; lia| reflexivity|].
    { eapply (ser_req_ok2A RT E D I); [exact OK| exact CX| exact HSM3|]. cbn [sa_cap sa_size] in *. clear - Kc ACC BUD. lia. }
    intros Σ' NEW m' F' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CR4.
    apply (aevt_evt RT AF PMc MST). open HSM4.

    step. step.
    ser_close HSM5 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (close_tailA x0 x56 x256 x264 Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW (2 * cap)))]; try eassumption; try pj_st_eq;
      unfold sb_grownA; slia.
Qed.

Definition kesc_botA_K (t : Z) : Prop :=
  forall x0 x56 x256 x264 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
         (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 : word),
    SERMK x0 x56 x256 x264 Σ st m -> frm0 fc -> sa_size st <= A + 1 + 6 * (t + 1) -> CREDA RT E I Σ X st ->
    aevt Σ K (KST 0xb388c xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 (wz (l - t)) (wz (DATA + t)) (wz (pa_SB E)) (wz (DATA + t)) xt3 xt4 F fc m).

Section Esc.
  Variable t : Z.
  Hypothesis KB : kesc_botA_K t.
  Hypothesis HT : 0 <= t < l.

  Lemma two_finA : forall x0 x56 x256 x264 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 : word),
    SERMK x0 x56 x256 x264 Σ st m -> frm0 fc -> sa_size st + 2 <= sa_cap st -> sa_size st + 2 <= A + 1 + 6 * (t + 1) -> CREDA RT E I Σ X st ->
    aevt Σ K (KST 0xb3884 xra xt0 xt1 xt2 (wz (sa_buf st + sa_size st)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (sa_size st + 2)) (wz (l - t)) (wz (DATA + t)) (wz (pa_SB E)) (wz (DATA + t)) xt3 xt4 F fc m).
  Proof using AF RC FDO MST GROW TABS OK CX Hi HSTR Hdp BUD X0 HK KB HT.
    intros x0 x56 x256 x264 Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 HSM FRM ROOM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM.
    pose proof (buf_factsA RT AF E D I Σ _ _ (si_b I) OK CX HREF) as (_ & _ & _ & _ & APB). cbn [sa_buf sa_cap] in APB.
    pose proof (APB (buf + size + 1) ltac:(clear - ROOM SZ; lia)) as (A1 & A2 & A3 & A4). clear APB.

    step. pj_store_done. unbox FSB; unbox SHSB. step. box_disj.
    ser_close HSM2 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (KB x0 x56 x256 x264 Σ (mkSbA buf (size + 2) cap hp kk))]; try eassumption; try pj_st_eq; slia.
  Qed.

  Lemma q_fin2A : forall x0 x56 x256 x264 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 : word),
    SERMK x0 x56 x256 x264 Σ st m -> frm0 fc -> sa_size st + 2 <= sa_cap st -> sa_size st + 2 <= A + 1 + 6 * (t + 1) -> CREDA RT E I Σ X st ->
    aevt Σ K (KST 0xb37cc xra xt0 xt1 xt2 (wz (sa_buf st + sa_size st)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (sa_size st + 2)) (wz (l - t)) (wz (DATA + t)) (wz (pa_SB E)) (wz (DATA + t)) xt3 xt4 F fc m).
  Proof using AF RC FDO MST GROW TABS OK CX Hi HSTR Hdp BUD X0 HK KB HT.
    intros x0 x56 x256 x264 Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 HSM FRM ROOM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM.
    pose proof (buf_factsA RT AF E D I Σ _ _ (si_b I) OK CX HREF) as (_ & _ & _ & _ & APB). cbn [sa_buf sa_cap] in APB.
    pose proof (APB (buf + size) ltac:(clear - ROOM SZ; lia)) as (A1 & A2 & A3 & A4). clear APB.

    step. step. pj_store_done. step. step.
    ser_close HSM2 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (two_finA x0 x56 x256 x264 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
  Qed.
  Lemma b_fin2A : forall x0 x56 x256 x264 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 : word),
    SERMK x0 x56 x256 x264 Σ st m -> frm0 fc -> sa_size st + 2 <= sa_cap st -> sa_size st + 2 <= A + 1 + 6 * (t + 1) -> CREDA RT E I Σ X st ->
    aevt Σ K (KST 0xb387c xra xt0 xt1 xt2 (wz (sa_buf st + sa_size st)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (sa_size st + 2)) (wz (l - t)) (wz (DATA + t)) (wz (pa_SB E)) (wz (DATA + t)) xt3 xt4 F fc m).
  Proof using AF RC FDO MST GROW TABS OK CX Hi HSTR Hdp BUD X0 HK KB HT.
    intros x0 x56 x256 x264 Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 HSM FRM ROOM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM.
    pose proof (buf_factsA RT AF E D I Σ _ _ (si_b I) OK CX HREF) as (_ & _ & _ & _ & APB). cbn [sa_buf sa_cap] in APB.
    pose proof (APB (buf + size) ltac:(clear - ROOM SZ; lia)) as (A1 & A2 & A3 & A4). clear APB.

    step. step. pj_store_done.
    ser_close HSM2 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (two_finA x0 x56 x256 x264 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
  Qed.

  Local Ltac diamond2 FIN x0 x56 x256 x264 Σ buf size cap hp kk HREF MU WM ROOM SZ R0 :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let ACCB := fresh "ACCB" in
      pose proof (acc_buf_mu RT AF E D I OK CX Σ _ _ mm HREF MU WM) as ACCB; cbn [sa_buf sa_cap] in ACCB;
      let b := fresh "b" in let RDB := fresh "RDB" in let SOK := fresh "SOK" in
      destruct (acc_read1 _ _ _ (buf + size + 1) ACCB ltac:(clear - ROOM SZ; lia)) as (b & RDB & SOK); clear ACCB;
      change (wa ((buf + size + 1) / 8 + 2147450880)) with (wa (shad (buf + size + 1))) in RDB;

      zstep; zstep; pjnorm; zstep; shfold; zstep;
      let HSM2 := fresh "HSM2" in ser_close HSM2 OK CX;
      let k := fresh "k" in let K17 := fresh "K17" in let KM := fresh "KM" in let Kc := fresh "Kc" in
      destruct (pj_sh_ok_cases b (buf + size + 1) SOK) as [-> | (k & -> & K17 & KM)];
      [ rewrite sxb_z8; zstep; if_false;
        apply evt_done; eapply aevt_eq; [| eapply (FIN x0 x56 x256 x264 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia
      | rewrite (pj_sxb_small7 k) by (clear - K17; lia); zstep;
        if_cases Kc; zify_cond Kc; [clear Kc| exfalso; pjnorm_in Kc; clear - Kc K17; lia];
        zstep; pjnorm; rewrite pj_land7 by (clear - R0 SZ; lia);
        zstep; if_cases Kc; zify_cond Kc;
          [clear Kc| exfalso; rewrite !pj_signed_small in Kc by (clear - K17; Z.div_mod_to_equations; lia); clear - Kc K17 KM; lia];
        apply evt_done; eapply aevt_eq; [| eapply (FIN x0 x56 x256 x264 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia ]
    end.

  Lemma q_d2A : forall x0 x56 x256 x264 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 : word),
    SERMK x0 x56 x256 x264 Σ st m -> frm0 fc -> sa_size st + 2 <= sa_cap st -> sa_size st + 2 <= A + 1 + 6 * (t + 1) -> CREDA RT E I Σ X st ->
    aevt Σ K (KST 0xb37b8 xra xt0 xt1 xt2 (wz (sa_buf st + sa_size st)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (sa_size st + 2)) (wz (l - t)) (wz (DATA + t)) (wz (pa_SB E)) (wz (DATA + t)) xt3 xt4 F fc m).
  Proof using AF RC FDO MST GROW TABS OK CX Hi HSTR Hdp BUD X0 HK KB HT.
    intros x0 x56 x256 x264 Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 HSM FRM ROOM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM.
    diamond2 q_fin2A x0 x56 x256 x264 Σ buf size cap hp kk HREF MU WM ROOM SZ R0.
  Qed.
  Lemma b_d2A : forall x0 x56 x256 x264 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 : word),
    SERMK x0 x56 x256 x264 Σ st m -> frm0 fc -> sa_size st + 2 <= sa_cap st -> sa_size st + 2 <= A + 1 + 6 * (t + 1) -> CREDA RT E I Σ X st ->
    aevt Σ K (KST 0xb3868 xra xt0 xt1 xt2 (wz (sa_buf st + sa_size st)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (sa_size st + 2)) (wz (l - t)) (wz (DATA + t)) (wz (pa_SB E)) (wz (DATA + t)) xt3 xt4 F fc m).
  Proof using AF RC FDO MST GROW TABS OK CX Hi HSTR Hdp BUD X0 HK KB HT.
    intros x0 x56 x256 x264 Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 HSM FRM ROOM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM.
    diamond2 b_fin2A x0 x56 x256 x264 Σ buf size cap hp kk HREF MU WM ROOM SZ R0.
  Qed.

  Local Ltac tail2 D2 x0 x56 x256 x264 Σ buf size cap hp kk HREF MU WM ROOM SZ R0 :=
    sb_shz;

    step; astep; astep; astep; astep;

    step; step; step; zstep;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let ACCB := fresh "ACCB" in
      pose proof (acc_buf_mu RT AF E D I OK CX Σ _ _ mm HREF MU WM) as ACCB; cbn [sa_buf sa_cap] in ACCB;
      let b := fresh "b" in let RDB := fresh "RDB" in let SOK := fresh "SOK" in
      destruct (acc_read1 _ _ _ (buf + size) ACCB ltac:(clear - ROOM SZ; lia)) as (b & RDB & SOK); clear ACCB;
      change (wa ((buf + size) / 8 + 2147450880)) with (wa (shad (buf + size))) in RDB;

      zstep; pjnorm; zstep; shfold; zstep;
      let HSM2 := fresh "HSM2" in ser_close HSM2 OK CX;
      let k := fresh "k" in let K17 := fresh "K17" in let KM := fresh "KM" in let Kc := fresh "Kc" in
      destruct (pj_sh_ok_cases b (buf + size) SOK) as [-> | (k & -> & K17 & KM)];
      [ rewrite sxb_z8; zstep; if_false;
        apply evt_done; eapply aevt_eq; [| eapply (D2 x0 x56 x256 x264 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia
      | rewrite (pj_sxb_small7 k) by (clear - K17; lia); zstep;
        if_cases Kc; zify_cond Kc; [clear Kc| exfalso; pjnorm_in Kc; clear - Kc K17; lia];
        zstep; pjnorm; rewrite pj_land7 by (clear - R0 SZ; lia);
        zstep; if_cases Kc; zify_cond Kc;
          [clear Kc| exfalso; rewrite !pj_signed_small in Kc by (clear - K17; Z.div_mod_to_equations; lia); clear - Kc K17 KM; lia];
        apply evt_done; eapply aevt_eq; [| eapply (D2 x0 x56 x256 x264 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia ]
    end.

  Lemma q_tailA : forall x0 x56 x256 x264 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 : word),
    SERMK x0 x56 x256 x264 Σ st m -> frm0 fc -> sa_size st + 2 <= sa_cap st -> sa_size st + 2 <= A + 1 + 6 * (t + 1) -> CREDA RT E I Σ X st ->
    aevt Σ K (KST 0xb377c xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (sa_size st + 2)) (wz (l - t)) (wz (DATA + t)) (wz (pa_SB E)) (wz (DATA + t)) xt3 xt4 F fc m).
  Proof using AF RC FDO MST GROW TABS OK CX Hi HSTR Hdp BUD X0 HK KB HT.
    intros x0 x56 x256 x264 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 HSM FRM ROOM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM.
    tail2 q_d2A x0 x56 x256 x264 Σ buf size cap hp kk HREF MU WM ROOM SZ R0.
  Qed.
  Lemma b_tailA : forall x0 x56 x256 x264 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 : word),
    SERMK x0 x56 x256 x264 Σ st m -> frm0 fc -> sa_size st + 2 <= sa_cap st -> sa_size st + 2 <= A + 1 + 6 * (t + 1) -> CREDA RT E I Σ X st ->
    aevt Σ K (KST 0xb382c xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (sa_size st + 2)) (wz (l - t)) (wz (DATA + t)) (wz (pa_SB E)) (wz (DATA + t)) xt3 xt4 F fc m).
  Proof using AF RC FDO MST GROW TABS OK CX Hi HSTR Hdp BUD X0 HK KB HT.
    intros x0 x56 x256 x264 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 HSM FRM ROOM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM.
    tail2 b_d2A x0 x56 x256 x264 Σ buf size cap hp kk HREF MU WM ROOM SZ R0.
  Qed.

End Esc.
End KeyA.
