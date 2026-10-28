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
     Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_hkit3A Atp_hkit4A Pj_rtkA Pj_defsA Pj_cpsA Pj_copyA Pj_ser_trefA Pj_ser_defsA Pj_ser_kitA Pj_ser_callsA Pj_ser_skitA.
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

Ltac gok := let G := fresh "G" in zstep; if_cases G; zify_cond G; [try clear G| gref G].

Ltac unzx := zstep; zstep; zstep; unz; change (Z.lxor 1 0) with 1; gtrap.

Section StrA.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis GROW : grow_cpsA RT PMc.
Notation aevt := (aevt RT PMc).

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

Definition sx (x0 x8 x16 x288 x296 : word) : xjA :=
  mkXJ x0 x8 x16 (wz (tword t_str c)) (wz (pa_SBUF E)) (wz (shad (pa_SB E + 64))) (wz (shad (pa_SB E + 80))) x288 x296.
Notation SERML x0 x8 x16 x288 x296 shp Σ st m := (SERMA RT E I (wkC E) (sx x0 x8 x16 x288 x296) shp isobj Σ st m).

Notation BSS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs7 xs11 xt3 xt4 xt5 xt6 F fc m :=
  (SSTA I pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (pa_SB E + 72)) xs3 (Z_to_bv 64 (shad (pa_SB E + 72))) (Z_to_bv 64 l) (Z_to_bv 64 i)
        xs7 (Z_to_bv 64 DATA) (Z_to_bv 64 2147450880) (Z_to_bv 64 dp) xs11 xt3 xt4 xt5 xt6 F fc m).

Local Ltac slia := repeat match goal with H : _ \/ _ |- _ => clear H end; cbn [sa_size sa_cap sa_buf sa_heap sa_k]; lia.
Local Ltac cbnx := cbn [sx Pj_ser_defsA.xj0 Pj_ser_defsA.xj8 Pj_ser_defsA.xj16 Pj_ser_defsA.xj24 Pj_ser_defsA.xj80 Pj_ser_defsA.xj208 Pj_ser_defsA.xj216
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
Local Ltac open HSM := unfold sx in HSM; ser_open HSM OK; cbnx.

Local Ltac buf_sh a ROOM SZ b RDB SOK :=
  lazymatch goal with HREF : SREFA _ _ _ ?Σc _ ?mr, MU : munch _ ?mr ?mm, WM : wmono bsegs ?mr ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let ACCB := fresh "ACCB" in
    pose proof (acc_buf_mu RT AF E D I OK CX _ _ _ mm HREF MU WM) as ACCB; cbn [sa_buf sa_cap] in ACCB;
    destruct (acc_read1 _ _ _ a ACCB ltac:(clear - ROOM SZ; lia)) as (b & RDB & SOK); clear ACCB;
    change (wa (a / 8 + 2147450880)) with (wa (shad a)) in RDB
  end.

Local Ltac diamond_blt FIN Σ buf size cap hp kk sz' K17 KM R0 SZ :=
  first
  [ rewrite sxb_z8; zstep; try if_false; apply evt_done;
    eapply aevt_eq; [| eapply (FIN Σ (mkSbA buf sz' cap hp kk))]; try eassumption; try pj_st_eq; slia
  | let Kc := fresh "Kc" in
    zstep; if_cases Kc; zify_cond Kc; [clear Kc| exfalso; pjnorm_in Kc; clear - Kc K17; lia];
    zstep; pjnorm; rewrite pj_land7 by (clear - R0 SZ; lia);
    zstep; if_cases Kc; zify_cond Kc;
      [clear Kc| exfalso; rewrite !pj_signed_small in Kc by (clear - K17; Z.div_mod_to_equations; lia); clear - Kc K17 KM; lia];
    apply evt_done; eapply aevt_eq; [| eapply (FIN Σ (mkSbA buf sz' cap hp kk))]; try eassumption; try pj_st_eq; slia ].

Lemma close_finA : forall x0 x8 x16 x288 x296 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 : word),
  SERML x0 x8 x16 x288 x296 ser_shpatA Σ st m -> frm0 fc -> 1 <= sa_size st -> sa_size st <= A + (2 + 6 * l) -> CREDA RT E I Σ X st ->
  aevt Σ K (SSTA I 0xba6e4 xra xt0 xt1 xt2 (wz (sa_buf st + (sa_size st - 1))) xa1 xa2 xa3 xa4 xa5 xa6 xa7
               (wz (pa_SB E + 72)) xs3 (wz (pa_SB E + 64)) (wz (SHFA I)) (wz i) (wz (pa_SB E + 80)) (wz (pa_SB E)) (wz 2147450880) (wz dp) (wz (pa_DOC E))
               xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST GROW OK CX Hi HT HSTR Hdp BUD X0 HK.
  intros x0 x8 x16 x288 x296 Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 HSM FRM SZ1 ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM.
  pose proof (buf_factsA RT AF E D I Σ _ _ (si_b I) OK CX HREF) as (_ & _ & _ & _ & APB). cbn [sa_buf sa_cap] in APB.
  pose proof (APB (buf + (size - 1)) ltac:(clear - SZ1 SZ; lia)) as (A1 & A2 & A3 & A4). clear APB.

  step. step. pj_store_done.
  ser_close HSM2 OK CX. apply evt_done.
  eapply (HK Σ (mkSbA buf size cap hp kk) _ F fc); [eexists; exact HSM2| exact FRM| cbn [sa_size]; clear - ACC; lia| exact CR].
Qed.

Lemma close_tailA : forall x0 x8 x16 x288 x296 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 : word),
  SERML x0 x8 x16 x288 x296 ser_shpatA Σ st m -> frm0 fc -> sa_size st + 1 <= sa_cap st -> sa_size st <= A + 1 + 6 * l -> CREDA RT E I Σ X st ->
  aevt Σ K (SSTA I 0xba690 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               (wz (pa_SB E + 72)) xs3 (wz (shad (pa_SB E + 72))) (wz (SHFA I)) (wz i) (wz (pa_SB E + 80)) (wz (pa_SB E)) (wz 2147450880) (wz dp) (wz (pa_DOC E))
               xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST GROW OK CX Hi HT HSTR Hdp BUD X0 HK.
  intros x0 x8 x16 x288 x296 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 HSM FRM ROOM ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM. sb_shz.

  step. astep. astep. astep. astep.

  step. step. step. zstep. zstep. unbox FSB; unbox SHSB. step. box_disj.

  gtrap. unzx. gtrap.
  buf_sh (buf + size) ROOM SZ b RDB SOK.

  zstep. pjnorm. zstep. shfold. zstep.
  ser_close HSM2 OK CX.
  destruct (pj_sh_ok_cases b (buf + size) SOK) as [-> | (k & -> & K17 & KM)]; [| rewrite (pj_sxb_small7 k) by (clear - K17; lia)];
    diamond_blt (close_finA x0 x8 x16 x288 x296) Σ buf size cap hp kk (size + 1) K17 KM R0 SZ.
Qed.

Lemma str_closeA : forall x0 x8 x16 x288 x296 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs11 xt3 xt4 xt5 xt6 : word),
  SERML x0 x8 x16 x288 x296 ser_shpatA Σ st m -> frm0 fc -> sa_size st <= A + 1 + 6 * l -> CREDA RT E I Σ X st ->
  aevt Σ K (BSS 0xba654 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 (wz (pa_SB E + 80)) xs11 xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST GROW OK CX Hi HT HSTR Hdp BUD X0 HK.
  intros x0 x8 x16 x288 x296 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs11 xt3 xt4 xt5 xt6 HSM FRM ACC CR.
  pose proof HSTR as (C0 & L0 & CL & _).
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM. sb_shz.

  step. astep. astep. astep. step. step. step. astep.

  step. step. zstep. step.
  if_cases Kc; zify_cond Kc; pjnorm_in Kc.
  -
    ser_close HSM2 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (close_tailA x0 x8 x16 x288 x296 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
  -
    zstep. pjnorm. zstep. zstep.
    ser_close HSM3 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (ser_growA RT AF PMc GROW E D I _ _ _ isobj Σ (mkSbA buf size cap hp kk) _ K (2 * cap) X 0xba690)];
      [pj_st_eq| exact OK| exact CX| exact HSM3| | exact CR| exact X0| clear; lia| reflexivity|].
    { eapply (ser_req_ok2A RT E D I); [exact OK| exact CX| exact HSM3|]. cbn [sa_cap sa_size] in *. clear - Kc ACC BUD. lia. }
    intros Σ' NEW m' F' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CR4.
    eapply aevt_eq; [| eapply (close_tailA x0 x8 x16 x288 x296 Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW (2 * cap)))]; try eassumption; try pj_st_eq;
      unfold sb_grownA; slia.
Qed.

Definition esc_botA_K (t : Z) : Prop :=
  forall x0 x8 x16 x288 x296 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
         (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 : word),
    SERML x0 x8 x16 x288 x296 ser_shpatA Σ st m -> frm0 fc -> sa_size st <= A + 1 + 6 * (t + 1) -> CREDA RT E I Σ X st ->
    aevt Σ K (BSS 0xba3d0 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 (wz (pa_SB E + 80)) (wz t) xt3 xt4 xt5 xt6 F fc m).

Section Esc.
  Variable t : Z.
  Hypothesis KB : esc_botA_K t.
  Hypothesis HTL : 0 <= t < l.

  Lemma two_finA : forall x0 x8 x16 x288 x296 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    SERML x0 x8 x16 x288 x296 ser_shpatA Σ st m -> frm0 fc -> sa_size st + 2 <= sa_cap st -> sa_size st + 2 <= A + 1 + 6 * (t + 1) -> CREDA RT E I Σ X st ->
    aevt Σ K (BSS 0xba3cc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (sa_size st + 2)) (wz (pa_SB E + 80)) (wz t) xt3 xt4 xt5 xt6 F fc m).
  Proof using AF RC FDO MST GROW OK CX Hi HT HSTR Hdp BUD X0 HK KB HTL.
    intros x0 x8 x16 x288 x296 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HSM FRM ROOM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM.

    unbox FSB; unbox SHSB. step. box_disj.
    ser_close HSM2 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (KB x0 x8 x16 x288 x296 Σ (mkSbA buf (size + 2) cap hp kk))]; try eassumption; try pj_st_eq; slia.
  Qed.

  Local Ltac fin2 stores x0 x8 x16 x288 x296 Σ buf size cap hp kk HSM FRM ROOM ACC CR :=
    ser_envA OK CX; apply (aevt_evt RT AF PMc MST); open HSM;
    lazymatch goal with HREF : SREFA _ _ _ _ _ _, SZ : 0 <= size <= cap |- _ =>
    let APB := fresh "APB" in
    pose proof (buf_factsA RT AF E D I Σ _ _ (si_b I) OK CX HREF) as (_ & _ & _ & _ & APB); cbn [sa_buf sa_cap] in APB;
    pose proof (APB (buf + size) ltac:(clear - ROOM SZ; lia)) as (?A1 & ?A2 & ?A3 & ?A4);
    pose proof (APB (buf + size + 1) ltac:(clear - ROOM SZ; lia)) as (?B1 & ?B2 & ?B3 & ?B4); clear APB;
    stores;

    zstep; gtrap; sb_shz; astep; astep;
    let HSM2 := fresh "HSM2" in ser_close HSM2 OK CX; apply evt_done;
    eapply aevt_eq; [| eapply (two_finA x0 x8 x16 x288 x296 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia
    end.
  Lemma q_finA : forall x0 x8 x16 x288 x296 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    SERML x0 x8 x16 x288 x296 ser_shpatA Σ st m -> frm0 fc -> sa_size st + 2 <= sa_cap st -> sa_size st + 2 <= A + 1 + 6 * (t + 1) -> CREDA RT E I Σ X st ->
    aevt Σ K (BSS 0xba2d8 xra xt0 xt1 xt2 (wz (sa_buf st + sa_size st)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (sa_size st + 2)) (wz (pa_SB E + 80)) (wz t) xt3 xt4 xt5 xt6 F fc m).
  Proof using AF RC FDO MST GROW OK CX Hi HT HSTR Hdp BUD X0 HK KB HTL.
    intros x0 x8 x16 x288 x296 Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HSM FRM ROOM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    fin2 ltac:(step; step; pj_store_done; step; step; pj_store_done) x0 x8 x16 x288 x296 Σ buf size cap hp kk HSM FRM ROOM ACC CR.
  Qed.
  Lemma b_finA : forall x0 x8 x16 x288 x296 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    SERML x0 x8 x16 x288 x296 ser_shpatA Σ st m -> frm0 fc -> sa_size st + 2 <= sa_cap st -> sa_size st + 2 <= A + 1 + 6 * (t + 1) -> CREDA RT E I Σ X st ->
    aevt Σ K (BSS 0xba3b0 xra xt0 xt1 xt2 (wz (sa_buf st + sa_size st)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (sa_size st + 2)) (wz (pa_SB E + 80)) (wz t) xt3 xt4 xt5 xt6 F fc m).
  Proof using AF RC FDO MST GROW OK CX Hi HT HSTR Hdp BUD X0 HK KB HTL.
    intros x0 x8 x16 x288 x296 Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HSM FRM ROOM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    fin2 ltac:(step; step; pj_store_done; step; pj_store_done) x0 x8 x16 x288 x296 Σ buf size cap hp kk HSM FRM ROOM ACC CR.
  Qed.

  Local Ltac diamond2 FIN x0 x8 x16 x288 x296 Σ buf size cap hp kk HREF MU WM ROOM SZ R0 :=
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
        apply evt_done; eapply aevt_eq; [| eapply (FIN x0 x8 x16 x288 x296 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia
      | rewrite (pj_sxb_small7 k) by (clear - K17; lia); zstep;
        if_cases Kc; zify_cond Kc; [clear Kc| exfalso; pjnorm_in Kc; clear - Kc K17; lia];
        zstep; pjnorm; rewrite pj_land7 by (clear - R0 SZ; lia);
        zstep; if_cases Kc; zify_cond Kc;
          [clear Kc| exfalso; rewrite !pj_signed_small in Kc by (clear - K17; Z.div_mod_to_equations; lia); clear - Kc K17 KM; lia];
        apply evt_done; eapply aevt_eq; [| eapply (FIN x0 x8 x16 x288 x296 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia ]
    end.
  Lemma q_d2A : forall x0 x8 x16 x288 x296 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    SERML x0 x8 x16 x288 x296 ser_shpatA Σ st m -> frm0 fc -> sa_size st + 2 <= sa_cap st -> sa_size st + 2 <= A + 1 + 6 * (t + 1) -> CREDA RT E I Σ X st ->
    aevt Σ K (BSS 0xba2c4 xra xt0 xt1 xt2 (wz (sa_buf st + sa_size st)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (sa_size st + 2)) (wz (pa_SB E + 80)) (wz t) xt3 xt4 xt5 xt6 F fc m).
  Proof using AF RC FDO MST GROW OK CX Hi HT HSTR Hdp BUD X0 HK KB HTL.
    intros x0 x8 x16 x288 x296 Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HSM FRM ROOM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM.
    diamond2 q_finA x0 x8 x16 x288 x296 Σ buf size cap hp kk HREF MU WM ROOM SZ R0.
  Qed.
  Lemma b_d2A : forall x0 x8 x16 x288 x296 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    SERML x0 x8 x16 x288 x296 ser_shpatA Σ st m -> frm0 fc -> sa_size st + 2 <= sa_cap st -> sa_size st + 2 <= A + 1 + 6 * (t + 1) -> CREDA RT E I Σ X st ->
    aevt Σ K (BSS 0xba39c xra xt0 xt1 xt2 (wz (sa_buf st + sa_size st)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (sa_size st + 2)) (wz (pa_SB E + 80)) (wz t) xt3 xt4 xt5 xt6 F fc m).
  Proof using AF RC FDO MST GROW OK CX Hi HT HSTR Hdp BUD X0 HK KB HTL.
    intros x0 x8 x16 x288 x296 Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HSM FRM ROOM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM.
    diamond2 b_finA x0 x8 x16 x288 x296 Σ buf size cap hp kk HREF MU WM ROOM SZ R0.
  Qed.

  Local Ltac tail2 D2 x0 x8 x16 x288 x296 Σ buf size cap hp kk HREF MU WM ROOM SZ R0 :=
    sb_shz;

    step; astep; astep; astep; astep;

    step; step; step; zstep; try (replace (size + buf) with (buf + size) by (clear; lia));

    gtrap; unzx;
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
        apply evt_done; eapply aevt_eq; [| eapply (D2 x0 x8 x16 x288 x296 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia
      | rewrite (pj_sxb_small7 k) by (clear - K17; lia); zstep;
        if_cases Kc; zify_cond Kc; [clear Kc| exfalso; pjnorm_in Kc; clear - Kc K17; lia];
        zstep; pjnorm; rewrite pj_land7 by (clear - R0 SZ; lia);
        zstep; if_cases Kc; zify_cond Kc;
          [clear Kc| exfalso; rewrite !pj_signed_small in Kc by (clear - K17; Z.div_mod_to_equations; lia); clear - Kc K17 KM; lia];
        apply evt_done; eapply aevt_eq; [| eapply (D2 x0 x8 x16 x288 x296 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia ]
    end.
  Lemma q_tailA : forall x0 x8 x16 x288 x296 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    SERML x0 x8 x16 x288 x296 ser_shpatA Σ st m -> frm0 fc -> sa_size st + 2 <= sa_cap st -> sa_size st + 2 <= A + 1 + 6 * (t + 1) -> CREDA RT E I Σ X st ->
    aevt Σ K (BSS 0xba274 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (sa_size st + 2)) (wz (pa_SB E + 80)) (wz t) xt3 xt4 xt5 xt6 F fc m).
  Proof using AF RC FDO MST GROW OK CX Hi HT HSTR Hdp BUD X0 HK KB HTL.
    intros x0 x8 x16 x288 x296 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HSM FRM ROOM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM.
    tail2 q_d2A x0 x8 x16 x288 x296 Σ buf size cap hp kk HREF MU WM ROOM SZ R0.
  Qed.
  Lemma b_tailA : forall x0 x8 x16 x288 x296 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    SERML x0 x8 x16 x288 x296 ser_shpatA Σ st m -> frm0 fc -> sa_size st + 2 <= sa_cap st -> sa_size st + 2 <= A + 1 + 6 * (t + 1) -> CREDA RT E I Σ X st ->
    aevt Σ K (BSS 0xba34c xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (sa_size st + 2)) (wz (pa_SB E + 80)) (wz t) xt3 xt4 xt5 xt6 F fc m).
  Proof using AF RC FDO MST GROW OK CX Hi HT HSTR Hdp BUD X0 HK KB HTL.
    intros x0 x8 x16 x288 x296 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HSM FRM ROOM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM.
    tail2 b_d2A x0 x8 x16 x288 x296 Σ buf size cap hp kk HREF MU WM ROOM SZ R0.
  Qed.
End Esc.
End StrA.
