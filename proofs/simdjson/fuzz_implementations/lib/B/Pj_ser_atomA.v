(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep Frame Image.
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

Definition false_bytes : list byte := map (Z_to_bv 8) [102; 97; 108; 115; 101].
Lemma false_image : ro_bytes_b bsegs PJ_STR_FALSE_A false_bytes = true.
Proof. vm_compute. reflexivity. Qed.
Lemma false_bytes_at : forall (m : mem), mem_inv bsegs m -> bytes_at bsegs m PJ_STR_FALSE_A false_bytes.
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold PJ_STR_FALSE_A; lia| cbn [length false_bytes map]; unfold PJ_STR_FALSE_A; lia|].
  apply ro_bytes_b_sound. exact false_image.
Qed.

Section AtomA.
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
Variables (i dp A X N : Z).
Hypothesis OK : pjenvA_ok E.
Hypothesis CX : sctxA E D I.
Hypothesis Hdp : 0 <= dp <= 15.
Hypothesis BUD : A + N <= PJ_OUTMAX (pa_len E).
Hypothesis X0 : 0 <= X.
Hypothesis HK : av_KA RT PMc E I K isobj i dp X (A + N).

Notation TST pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs8 xt3 xt4 xt5 xt6 F fc m :=
  (SSTA I pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
        (Z_to_bv 64 (pa_SB E + 72)) xs3 xs4 xs5 (Z_to_bv 64 i) (Z_to_bv 64 (pa_SB E + 80)) xs8 (Z_to_bv 64 2147450880) (Z_to_bv 64 dp) (Z_to_bv 64 (pa_DOC E))
        xt3 xt4 xt5 xt6 F fc m).
Notation SERMT x Σ st m := (SERMA RT E I (wkC E) x ser_shpatA isobj Σ st m).
Local Ltac slia := repeat match goal with H : _ \/ _ |- _ => clear H end; cbn [sa_size sa_cap sa_buf sa_heap sa_k]; lia.
Local Ltac sb_shz :=
  lazymatch goal with
  | HREF : SREFA _ _ _ _ _ ?mr, MU : munch _ ?mr ?mm, WM : wmono bsegs ?mr ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let SHZ := fresh "SHZ" in let R64 := fresh "RD64" in let R72 := fresh "RD72" in let R80 := fresh "RD80" in
    pose proof (shz_sb_mu RT AF E D I OK CX _ _ _ mm HREF MU WM) as SHZ;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 64) ltac:(clear; lia)) as R64;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 72) ltac:(clear; lia)) as R72;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 80) ltac:(clear; lia)) as R80; clear SHZ
  end.

Local Ltac buf_sh a HREF MU WM ROOM SZ b RDB SOK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let ACCB := fresh "ACCB" in
    pose proof (acc_buf_mu RT AF E D I OK CX _ _ _ mm HREF MU WM) as ACCB; cbn [sa_buf sa_cap] in ACCB;
    destruct (acc_read1 _ _ _ a ACCB ltac:(clear - ROOM SZ; lia)) as (b & RDB & SOK); clear ACCB;
    change (wa (a / 8 + 2147450880)) with (wa (shad a)) in RDB
  end.

Local Ltac atom4_fin stores x Σ buf size cap hp kk HSM FRM ROOM ACC CR :=
  ser_envA OK CX; apply (aevt_evt RT AF PMc MST); ser_open HSM OK;
  lazymatch goal with
  | HREF : SREFA _ _ _ _ _ _, SZ : 0 <= size <= cap, FSB : boxP (si_f I + 512 <= pa_SB E \/ _), SHSB : boxP (pa_SB E + 96 <= _ \/ _), BL : buf + cap <= pa_lo E |- _ =>
  let APB := fresh "APB" in
  pose proof (buf_factsA RT AF E D I Σ _ _ (si_b I) OK CX HREF) as (_ & _ & _ & _ & APB); cbn [sa_buf sa_cap] in APB;
  pose proof (APB (buf + size) ltac:(clear - ROOM SZ; lia)) as (?A1 & ?A2 & ?A3 & ?A4);
  pose proof (APB (buf + size + 1) ltac:(clear - ROOM SZ; lia)) as (?B1 & ?B2 & ?B3 & ?B4);
  pose proof (APB (buf + size + 2) ltac:(clear - ROOM SZ; lia)) as (?C1 & ?C2 & ?C3 & ?C4);
  pose proof (APB (buf + size + 3) ltac:(clear - ROOM SZ; lia)) as (?D1 & ?D2 & ?D3 & ?D4); clear APB;
  stores;

  zstep; gok;

  sb_shz; astep; astep;
  unbox FSB; unbox SHSB; step; box_disj; step; step; step; step; step;
  let HSM2 := fresh "HSM2" in ser_close HSM2 OK CX; apply evt_done;
  eapply (HK Σ (mkSbA buf (size + 4) cap hp kk) _ _ _); [eexists; exact HSM2| exact FRM| cbn [sa_size]; clear - ACC; lia| exact CR]
  end.

Lemma buf_apart_lowA : forall Σ st m, SREFA RT E I Σ st m -> sa_buf st + sa_cap st <= 0x10000 \/ SEGTOP_A <= sa_buf st.
Proof using AF OK CX.
  intros Σ st m (HA & LV & _ & _ & _ & _ & PU & _).
  pose proof (env_rangesA E OK) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FS & B1 & _).
  destruct PU as [_ HP]. destruct (sa_heap st) eqn:HH.
  - destruct (af_live_range RT AF Σ m (sa_buf st) (sa_cap st) HA) as (_ & _ & R); [| exact R].
    rewrite LV. unfold sbchunkA. rewrite HH. left. reflexivity.
  - destruct HP as (EB & EC & _). rewrite EB. right. lia.
Qed.

Lemma false_tailA : forall (x : xjA) (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs8 xt3 xt4 xt5 xt6 : word),
  N = 5 -> SERMT x Σ st m -> frm0 fc -> sa_size st + 5 <= sa_cap st -> sa_size st <= A -> CREDA RT E I Σ X st ->
  aevt Σ K (TST 0xb92e0 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (shad (pa_SB E + 72))) (wz (sa_size st + 5)) xs5 xs8 xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST GROW OK CX Hdp BUD X0 HK.
  intros x Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs8 xt3 xt4 xt5 xt6 N5 HSM FRM ROOM ACC CR. subst N.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). pose proof HSM as HSM0. ser_open HSM OK. sb_shz. unfold PJ_STR_FALSE_A in *.

  step. astep. astep. astep. astep. astep.

  step. step. step. zstep. try (replace (size + buf) with (buf + size) by (clear; lia)).
  gok. zstep. zstep. zstep. unz. change (Z.lxor 1 0) with 1. gok.

  zstep. zstep. zstep. zstep. zstep.
  pose proof (false_bytes_at m MI) as SRC. unfold PJ_STR_FALSE_A in SRC.
  pose proof (buf_apart_lowA Σ _ m HREF) as APL. cbn [sa_buf sa_cap] in APL. unfold SEGTOP_A in APL.
  assert (AC6 : acc bsegs m 145984 6).
  { apply (acc_lit RT AF Σ m 145984 6 (ART_of_SERMA RT E I _ _ _ isobj Σ _ m HSM0)). unfold ACC_LITS. cbn [In]. repeat (first [left; reflexivity | right]). }
  ser_close HSM2 OK CX. apply evt_done.
  eapply aevt_eq; [| eapply (ser_icopyA RT AF RC PMc FDO MST e_asan_memcpy E D I _ _ _ isobj Σ (mkSbA buf size cap hp kk) m K 145984 5 0xb9340 false_bytes)];
    [pj_st_eq| left; reflexivity| exact OK| exact CX| exact HSM2| exact SRC| reflexivity| clear; lia| cbn [sa_size sa_cap]; exact ROOM
    | eapply acc_sub; [exact AC6| clear; lia| clear; lia]
    | right; right; right; unfold SEGTOP_A; clear; lia
    | clear; lia| clear - LO; lia
    | intros _; cbn [sa_buf sa_size]; clear - APL ROOM SZ; lia
    | clear; lia| reflexivity|].
  intros m' F' yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CPY.
  apply (aevt_evt RT AF PMc MST). ser_open HSM4 OK.

  gok. zstep. gok. sb_shz. astep. astep.

  unbox FSB; unbox SHSB. step. box_disj. step. step. step. step. step. step.
  ser_close HSM5 OK CX. apply evt_done.
  eapply (HK Σ (mkSbA buf (size + 5) cap hp kk) _ _ _); [eexists; exact HSM5| exact FRM| cbn [sa_size]; clear - ACC; lia| exact CR].
Qed.

Theorem false_mainA : forall (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xs3 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
  N = 5 ->
  SERMC RT E I isobj Σ st m -> frm0 fc -> sa_size st <= A -> CREDA RT E I Σ X st ->
  aevt Σ K (TST PJ_FALSE_A xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 (wz (pa_SB E + 64)) (wz (SHFA I)) (wz (pa_SB E)) xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST GROW OK CX Hdp BUD X0 HK.
  intros Σ st m F fc xs3 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 N5 HSM FRM ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *. unfold PJ_FALSE_A.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). ser_open HSM OK.

  zstep. zstep. zstep. gok.

  step. astep. sb_shz. astep. astep. step. astep. astep. astep.

  step. step. zstep. step.
  if_cases Kc; zify_cond Kc; pjnorm_in Kc.
  - ser_close HSM2 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (false_tailA _ Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
  -
    zstep. pjnorm. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 _ ?mm _) =>
    assert (GROWN : forall (z : Z) (yra yt0 yt1 yt2 ya0 ya2 ya3 ya4 ya5 ya6 ya7 ys5 yt3 yt4 yt5 yt6 : word), z = Z.max (2 * cap) (size + 5) ->
      evt bsegs (fun ms' => aevt Σ K ms')
        (TST 0xb92d8 yra yt0 yt1 yt2 ya0 (wz z) ya2 ya3 ya4 ya5 ya6 ya7 (wz (shad (pa_SB E + 72))) (wz (size + 5)) ys5 (wz (pa_SB E)) yt3 yt4 yt5 yt6 F0 fc0 mm)) end.
    { intros z yra yt0 yt1 yt2 ya0 ya2 ya3 ya4 ya5 ya6 ya7 ys5 yt3 yt4 yt5 yt6 EZ.
      zstep. zstep.
      ser_close HSM3 OK CX. apply evt_done.
      eapply aevt_eq; [| eapply (ser_growA RT AF PMc GROW E D I _ _ _ isobj Σ (mkSbA buf size cap hp kk) _ K z X 0xb92e0)];
        [pj_st_eq| exact OK| exact CX| exact HSM3| | exact CR| exact X0| clear; lia| reflexivity|].
      { rewrite EZ. eapply (ser_req_okA RT E D I); [exact OK| exact CX| exact HSM3| cbn [sa_cap]; clear - Kc; lia|].
        cbn [sa_size]. clear - ACC BUD N5. lia. }
      intros Σ' NEW m' F' zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 HSM4 CR4.
      eapply aevt_eq; [| eapply (false_tailA _ Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW z))]; try eassumption; try pj_st_eq;
        unfold sb_grownA; cbn [sa_size sa_cap sa_buf sa_heap sa_k]; rewrite ?EZ; clear - Kc ACC SZ; lia. }
    if_cases K2; zify_cond K2; pjnorm_in K2.
    + eapply evt_eq; [| eapply (GROWN (size + 5))]; [pj_st_eq| clear - K2 Kc; lia].
    + zstep. eapply evt_eq; [| eapply (GROWN (2 * cap))]; [pj_st_eq| clear - K2 Kc; lia].
Qed.

Hypothesis N4 : N = 4.

Lemma true_finA : forall (x : xjA) (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 : word),
  SERMT x Σ st m -> frm0 fc -> sa_size st + 4 <= sa_cap st -> sa_size st <= A -> CREDA RT E I Σ X st ->
  aevt Σ K (TST 0xb95fc xra xt0 xt1 xt2 (wz (sa_buf st + sa_size st)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 (wz (shad (pa_SB E + 72))) (wz (sa_size st + 4)) (wz (pa_SB E))
               xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST GROW OK CX Hdp BUD X0 HK N4.
  intros x Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 HSM FRM ROOM ACC CR. subst N.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  atom4_fin ltac:(do 4 (step; step; pj_store_done)) x Σ buf size cap hp kk HSM FRM ROOM ACC CR.
Qed.

Lemma null_finA : forall (x : xjA) (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 : word),
  SERMT x Σ st m -> frm0 fc -> sa_size st + 4 <= sa_cap st -> sa_size st <= A -> CREDA RT E I Σ X st ->
  aevt Σ K (TST 0xb9710 xra xt0 xt1 xt2 (wz (sa_buf st + sa_size st)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 (wz (shad (pa_SB E + 72))) (wz (sa_size st + 4)) (wz (pa_SB E))
               xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST GROW OK CX Hdp BUD X0 HK N4.
  intros x Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 HSM FRM ROOM ACC CR. subst N.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.

  atom4_fin ltac:(do 3 (step; step; pj_store_done); step; pj_store_done) x Σ buf size cap hp kk HSM FRM ROOM ACC CR.
Qed.

Local Ltac diamond_arms FIN x Σ buf size cap hp kk K17 KM R0 SZ :=
  first
  [ rewrite sxb_z8; zstep; try if_true; apply evt_done;
    eapply aevt_eq; [| eapply (FIN _ Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia
  | let Kc := fresh "Kc" in
    zstep; if_cases Kc; zify_cond Kc; [exfalso; pjnorm_in Kc; clear - Kc K17; lia| clear Kc];
    zstep; zstep; pjnorm; rewrite pj_land7 by (clear - R0 SZ; lia);
    zstep; if_cases Kc; zify_cond Kc;
      [exfalso; rewrite !pj_signed_small in Kc by (clear - K17; Z.div_mod_to_equations; lia); clear - Kc K17 KM; lia| clear Kc];
    zstep; apply evt_done; eapply aevt_eq; [| eapply (FIN _ Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia ].

Local Ltac atom4_d2 FIN x Σ buf size cap hp kk HSM :=
  ser_envA OK CX; apply (aevt_evt RT AF PMc MST); ser_open HSM OK;
  lazymatch goal with
  | HREF : SREFA _ _ _ _ _ ?mr, MU : munch _ ?mr ?mm, WM : wmono bsegs ?mr ?mm, ROOM : size + 4 <= cap, SZ : 0 <= size <= cap, R0 : 0 < buf |- _ =>
    let b := fresh "b" in let RDB := fresh "RDB" in let SOK := fresh "SOK" in
    buf_sh (buf + size + 3) HREF MU WM ROOM SZ b RDB SOK;

    zstep; zstep; pjnorm; zstep; shfold; zstep;
    let HSM2 := fresh "HSM2" in ser_close HSM2 OK CX;
    let k := fresh "k" in let K17 := fresh "K17" in let KM := fresh "KM" in
    destruct (pj_sh_ok_cases b (buf + size + 3) SOK) as [-> | (k & -> & K17 & KM)];
      [| rewrite (pj_sxb_small7 k) by (clear - K17; lia)];
      diamond_arms FIN x Σ buf size cap hp kk K17 KM R0 SZ
  end.

Lemma true_d2A : forall (x : xjA) (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 : word),
  SERMT x Σ st m -> frm0 fc -> sa_size st + 4 <= sa_cap st -> sa_size st <= A -> CREDA RT E I Σ X st ->
  aevt Σ K (TST 0xb95e4 xra xt0 xt1 xt2 (wz (sa_buf st + sa_size st)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 (wz (shad (pa_SB E + 72))) (wz (sa_size st + 4)) (wz (pa_SB E))
               xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST GROW OK CX Hdp BUD X0 HK N4.
  intros x Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 HSM FRM ROOM ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  atom4_d2 true_finA x Σ buf size cap hp kk HSM.
Qed.
Lemma null_d2A : forall (x : xjA) (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 : word),
  SERMT x Σ st m -> frm0 fc -> sa_size st + 4 <= sa_cap st -> sa_size st <= A -> CREDA RT E I Σ X st ->
  aevt Σ K (TST 0xb96f8 xra xt0 xt1 xt2 (wz (sa_buf st + sa_size st)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 (wz (shad (pa_SB E + 72))) (wz (sa_size st + 4)) (wz (pa_SB E))
               xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST GROW OK CX Hdp BUD X0 HK N4.
  intros x Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 HSM FRM ROOM ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  atom4_d2 null_finA x Σ buf size cap hp kk HSM.
Qed.

Local Ltac atom4_tail D2 x Σ buf size cap hp kk HSM :=
  ser_envA OK CX; apply (aevt_evt RT AF PMc MST); ser_open HSM OK; sb_shz;

  step; astep; astep; astep; astep; astep;

  step; step; step; zstep; try (replace (size + buf) with (buf + size) by (clear; lia));
  lazymatch goal with
  | HREF : SREFA _ _ _ _ _ ?mr, MU : munch _ ?mr ?mm, WM : wmono bsegs ?mr ?mm, ROOM : size + 4 <= cap, SZ : 0 <= size <= cap, R0 : 0 < buf |- _ =>

    gok; zstep; zstep; zstep; unz; change (Z.lxor 1 0) with 1; gok;
    let b := fresh "b" in let RDB := fresh "RDB" in let SOK := fresh "SOK" in
    buf_sh (buf + size) HREF MU WM ROOM SZ b RDB SOK;

    zstep; pjnorm; zstep; shfold; zstep;
    let HSM2 := fresh "HSM2" in ser_close HSM2 OK CX;
    let k := fresh "k" in let K17 := fresh "K17" in let KM := fresh "KM" in
    destruct (pj_sh_ok_cases b (buf + size) SOK) as [-> | (k & -> & K17 & KM)];
      [| rewrite (pj_sxb_small7 k) by (clear - K17; lia)];
      diamond_arms D2 x Σ buf size cap hp kk K17 KM R0 SZ
  end.

Lemma true_tailA : forall (x : xjA) (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 : word),
  SERMT x Σ st m -> frm0 fc -> sa_size st + 4 <= sa_cap st -> sa_size st <= A -> CREDA RT E I Σ X st ->
  aevt Σ K (TST 0xb9584 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 (wz (shad (pa_SB E + 72))) (wz (sa_size st + 4)) (wz (pa_SB E)) xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST GROW OK CX Hdp BUD X0 HK N4.
  intros x Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 HSM FRM ROOM ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  atom4_tail true_d2A x Σ buf size cap hp kk HSM.
Qed.
Lemma null_tailA : forall (x : xjA) (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 : word),
  SERMT x Σ st m -> frm0 fc -> sa_size st + 4 <= sa_cap st -> sa_size st <= A -> CREDA RT E I Σ X st ->
  aevt Σ K (TST 0xb9698 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 (wz (shad (pa_SB E + 72))) (wz (sa_size st + 4)) (wz (pa_SB E)) xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST GROW OK CX Hdp BUD X0 HK N4.
  intros x Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 HSM FRM ROOM ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  atom4_tail null_d2A x Σ buf size cap hp kk HSM.
Qed.

Local Ltac atom4_entry TL x Σ buf size cap hp kk HSM ACC CR tail_pc :=
  ser_envA OK CX; apply (aevt_evt RT AF PMc MST); ser_open HSM OK;

  zstep; zstep; zstep; gok;

  step; astep; sb_shz; astep; astep; step; astep; astep; astep;

  step; step; zstep; step;
  let Kc := fresh "Kc" in
  if_cases Kc; zify_cond Kc; pjnorm_in Kc;
  [ let HSM2 := fresh "HSM2" in ser_close HSM2 OK CX; apply evt_done;
    eapply aevt_eq; [| eapply (TL _ Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia
  |
    zstep; pjnorm; zstep; zstep;
    let GROWN := fresh "GROWN" in
    lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 _ ?mm _) =>
    assert (GROWN : forall (z : Z) (yra yt0 yt1 yt2 ya0 ya2 ya3 ya4 ya5 ya6 ya7 ys3 yt3 yt4 yt5 yt6 : word), z = Z.max (2 * cap) (size + 4) ->
      evt bsegs (fun ms' => aevt Σ K ms')
        (TST (tail_pc - 8) yra yt0 yt1 yt2 ya0 (wz z) ya2 ya3 ya4 ya5 ya6 ya7 ys3 (wz (shad (pa_SB E + 72))) (wz (size + 4)) (wz (pa_SB E)) yt3 yt4 yt5 yt6 F0 fc0 mm));
    [ let z := fresh "z" in let EZ := fresh "EZ" in
      intros z ?yra ?yt0 ?yt1 ?yt2 ?ya0 ?ya2 ?ya3 ?ya4 ?ya5 ?ya6 ?ya7 ?ys3 ?yt3 ?yt4 ?yt5 ?yt6 EZ;
      zstep; zstep;
      let HSM3 := fresh "HSM3" in ser_close HSM3 OK CX; apply evt_done;
      eapply aevt_eq; [| eapply (ser_growA RT AF PMc GROW E D I _ _ _ isobj Σ (mkSbA buf size cap hp kk) _ K z X tail_pc)];
        [pj_st_eq| exact OK| exact CX| exact HSM3| | exact CR| exact X0| clear; lia| reflexivity|];
      [ rewrite EZ; eapply (ser_req_okA RT E D I); [exact OK| exact CX| exact HSM3| cbn [sa_cap]; clear - Kc; lia|];
        cbn [sa_size]; clear - ACC BUD N4; lia
      | let HSM4 := fresh "HSM4" in let CR4 := fresh "CR4" in
        intros ?Σ' ?NEW ?m' ?F' ?yt0 ?yt1 ?yt2 ?za0 ?za1 ?za2 ?za3 ?za4 ?za5 ?za6 ?za7 ?yt3 ?yt4 ?yt5 ?yt6 HSM4 CR4;
        eapply aevt_eq; [| eapply (TL _ _ (sb_grownA (mkSbA buf size cap hp kk) _ z))]; try eassumption; try pj_st_eq;
          unfold sb_grownA; cbn [sa_size sa_cap sa_buf sa_heap sa_k]; rewrite ?EZ;
          match goal with SZq : 0 <= size <= cap |- _ => clear - Kc ACC SZq; lia end ]
    | let K2 := fresh "K2" in
      if_cases K2; zify_cond K2; pjnorm_in K2;
      [ eapply evt_eq; [| eapply (GROWN (size + 4))]; [pj_st_eq| clear - K2 Kc; lia]
      | zstep; eapply evt_eq; [| eapply (GROWN (2 * cap))]; [pj_st_eq| clear - K2 Kc; lia] ] ]
    end ].

Theorem true_mainA : forall (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xs3 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
  SERMC RT E I isobj Σ st m -> frm0 fc -> sa_size st <= A -> CREDA RT E I Σ X st ->
  aevt Σ K (TST PJ_TRUE_A xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 (wz (pa_SB E + 64)) (wz (SHFA I)) (wz (pa_SB E)) xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST GROW OK CX Hdp BUD X0 HK N4.
  intros Σ st m F fc xs3 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 HSM FRM ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *. unfold PJ_TRUE_A.
  atom4_entry true_tailA x Σ buf size cap hp kk HSM ACC CR 0xb9584.
Qed.

Theorem null_mainA : forall (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xs3 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
  SERMC RT E I isobj Σ st m -> frm0 fc -> sa_size st <= A -> CREDA RT E I Σ X st ->
  aevt Σ K (TST PJ_NULL_A xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 (wz (pa_SB E + 64)) (wz (SHFA I)) (wz (pa_SB E)) xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST GROW OK CX Hdp BUD X0 HK N4.
  intros Σ st m F fc xs3 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 HSM FRM ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *. unfold PJ_NULL_A.
  atom4_entry null_tailA x Σ buf size cap hp kk HSM ACC CR 0xb9698.
Qed.

End Pieces.

Theorem true_okA : true_stmtA RT PMc.
Proof using AF RC FDO MST GROW.
  unfold true_stmtA, atom_stmtA.
  intros E D I K isobj Σ st m F fc i dp A X xs3 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 OK CX HSM FRM Hdp ACC BUD CR X0 HK.
  eapply (true_mainA E D I K isobj i dp A X 4 OK CX Hdp BUD X0 HK eq_refl); eassumption.
Qed.
Theorem false_okA : false_stmtA RT PMc.
Proof using AF RC FDO MST GROW.
  unfold false_stmtA, atom_stmtA.
  intros E D I K isobj Σ st m F fc i dp A X xs3 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 OK CX HSM FRM Hdp ACC BUD CR X0 HK.
  eapply (false_mainA E D I K isobj i dp A X 5 OK CX Hdp BUD X0 HK); [reflexivity| eassumption ..].
Qed.
Theorem null_okA : null_stmtA RT PMc.
Proof using AF RC FDO MST GROW.
  unfold null_stmtA, atom_stmtA.
  intros E D I K isobj Σ st m F fc i dp A X xs3 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 OK CX HSM FRM Hdp ACC BUD CR X0 HK.
  eapply (null_mainA E D I K isobj i dp A X 4 OK CX Hdp BUD X0 HK eq_refl); eassumption.
Qed.
End AtomA.
