(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep Frame.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer SjPjCont.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 RT_iface4 D_defs D_kit D_clx D_libiface I_lkit
     Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_hkit5A Atp_fzwA Pj_rtkA Pj_defsA Pj_cpsA Pj_copyA Pj_ser_defsA Pj_ser_kitA Pj_ser_callsA Pj_ser_trefA Pj_ser_ckitA
     Pj_ser_objkA Pj_ser_skitA Pj_ser_okitA.
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

Ltac gok := let G := fresh "G" in zstep; if_cases G; zify_cond G; [try clear G| gref G].

Ltac unzx := zstep; zstep; zstep; unz; change (Z.lxor 1 0) with 1; gok.
Ltac unzt := zstep; zstep; zstep; unz; change (Z.lxor 1 0) with 1; gtrap.

Section OKeyA.
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
Variable C : conI.
Variable f : Z.
Variable K : config -> Prop.
Variables (x c l x1 cx A X : Z).
Hypothesis OK : pjenvA_ok E.
Hypothesis CX : cctxA E D C.
Hypothesis OX : octxA E C f.
Hypothesis SER : ser_cpsA RT PMc D.
Hypothesis Hx : 2 <= x /\ x + 1 < x1 /\ x1 <= ci_e C.
Hypothesis HSTR : str_at (pa_S E) (pa_sn E) c l.
Hypothesis EL : elemS (pa_T E) (pa_S E) (pa_sn E) ck_any D (x + 1) x1 (c + l + 5) cx.
Hypothesis CXN : cx <= pa_sn E.
Hypothesis BUD : A + (3 + 6 * l) <= PJ_OUTMAX (pa_len E).
Hypothesis BUD2 : A + (3 + 6 * l) <= 41 * x + 6 * (c + l + 5) + 3.
Hypothesis X2 : 2 * (x1 - (x + 1)) <= X.
Hypothesis X0 : 0 <= X.
Hypothesis HK : forall (Σ' : rts RT) (st' : sbA) (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (y24 y32 y40 y72 y104 y112 y120 y136 y224 y232 : word)
            (yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys6 ys7 ys9 yt3 yt4 yt5 yt6 : word),
    CERMA RT E C (obj_frp E C f (owK E C f y24 y32 y40 (wz (x - 1)) (wz (pa_DOC E + 8)) y72 (wz (pa_DOC E)) (wz 72057594037927935) (wz ((pa_DOC E + 8) / 8 + 2147450880)) y104 y112 y120
                                    (wz (f + 64)) y136 (wz PJ_ESC_TAB_A) (wz PJ_RO184_A) (wz PJ_RO176_A) (wz (pa_SB E)) y224 y232) obj_shpatA) Σ' st' m' ->
    frm0 fc' -> sb_accA st' x1 cx -> CCREDA RT E C Σ' (X - 2 * (x1 - (x + 1))) st' ->
    aevt Σ' K (OST E C 0xbc88c yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 (wz (pa_DOC E)) (wz (18446744073709551615 - PJ_NE_TAB_A)) (wz (x + 1)) ys6 ys7 ys9
                   (wz PJ_NE_TAB_A) (wz (pa_SB E)) yt3 yt4 yt5 yt6 F' fc' m').

Notation DATA := (pa_SBUF E + c + 4).

Definition ok1c (x24 x32 x72 x120 x136 x224 x232 : word) : owA :=
  owK E C f x24 x32 (wz (x + 1)) (wz (x - 1)) (wz (pa_DOC E + 8)) x72 (wz (pa_DOC E)) (wz 72057594037927935) (wz ((pa_DOC E + 8) / 8 + 2147450880))
      (wz (f + 32)) (wz DATA) x120 (wz (f + 64)) x136 (wz PJ_ESC_TAB_A) (wz PJ_RO184_A) (wz PJ_RO176_A) (wz (pa_SB E)) x224 x232.
Notation CERMC x24 x32 x72 x120 x136 x224 x232 shp Σ st m := (CERMA RT E C (obj_frp E C f (ok1c x24 x32 x72 x120 x136 x224 x232) shp) Σ st m).

Notation ok1w x24 x32 x224 x232 := (ok1c x24 x32 (wz (M64M1 - (f + 33))) (wz (PJ_RO184_A + 2)) (wz (PJ_RO176_A + 2)) x224 x232).
Notation CERML x24 x32 x224 x232 shp Σ st m := (CERMA RT E C (obj_frp E C f (ok1w x24 x32 x224 x232) shp) Σ st m).

Notation O1S pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs2 xs7 xt3 xt4 xt5 xt6 F fc m :=
  (OST E C pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 (shad (pa_SB E + 72))) xa7 xs2 (Z_to_bv 64 (M64M1 - PJ_NE_TAB_A)) (Z_to_bv 64 (f + 33)) (Z_to_bv 64 l) xs7
       (Z_to_bv 64 DATA) (Z_to_bv 64 PJ_NE_TAB_A) (Z_to_bv 64 92) xt3 xt4 xt5 xt6 F fc m).
Notation O1N pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs2 xs7 xs9 xt3 xt4 xt5 xt6 F fc m :=
  (OST E C pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 (shad (pa_SB E + 72))) xa7 xs2 (Z_to_bv 64 (M64M1 - PJ_NE_TAB_A)) (Z_to_bv 64 (f + 33)) (Z_to_bv 64 l) xs7
       xs9 (Z_to_bv 64 PJ_NE_TAB_A) (Z_to_bv 64 92) xt3 xt4 xt5 xt6 F fc m).

Notation C1S pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs7 xs9 xt3 xt4 xt5 xt6 F fc m :=
  (OST E C pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 (shad (pa_SB E + 72))) xa7 (Z_to_bv 64 (pa_DOC E)) (Z_to_bv 64 (M64M1 - PJ_NE_TAB_A)) (Z_to_bv 64 (x + 1))
       (Z_to_bv 64 l) xs7 xs9 (Z_to_bv 64 PJ_NE_TAB_A) (Z_to_bv 64 (pa_SB E)) xt3 xt4 xt5 xt6 F fc m).

Local Ltac slia := repeat match goal with H : _ \/ _ |- _ => clear H end; cbn [sa_size sa_cap sa_buf sa_heap sa_k]; lia.

Local Ltac sb_shz :=
  lazymatch goal with
  | HREF : CREFA _ _ _ _ _ ?mr, MU : munch _ ?mr ?mm, WM : wmono bsegs ?mr ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let SHZ := fresh "SHZ" in let R64 := fresh "RD64" in let R72 := fresh "RD72" in let R80 := fresh "RD80" in
    let MUc := omuc OX in
    pose proof (shz_sb_muC RT AF E D C OK CX _ _ _ mm HREF MUc WM) as SHZ;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 64) ltac:(clear; lia)) as R64;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 72) ltac:(clear; lia)) as R72;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 80) ltac:(clear; lia)) as R80; clear SHZ
  end.

Local Ltac shf_fold := match goal with SHF : rw_cells bsegs ?m (?g / 8 + 2147450880) ?cs, SHL : length ?shp = 16%nat |- _ =>
  change (rw_cells bsegs m (g / 8 + 2147450880) cs) with (rw_cells bsegs m (g / 8 + 2147450880) (sh16 shp)) in SHF | _ => idtac end.
Local Ltac open HSM := unfold ok1c in HSM; obj_open HSM OK CX OX.
Local Ltac oclose HSM := shf_fold; obj_close HSM OX.

Local Ltac buf_sh a ROOM SZ b RDB SOK :=
  lazymatch goal with HREF : CREFA _ _ _ ?Σc _ ?mr, WM : wmono bsegs ?mr ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let ACCB := fresh "ACCB" in let MUc := omuc OX in
    pose proof (acc_buf_muC RT AF E D C OK CX Σc _ _ mm HREF MUc WM) as ACCB; cbn [sa_buf sa_cap] in ACCB;
    destruct (acc_read1 _ _ _ a ACCB ltac:(clear - ROOM SZ; lia)) as (b & RDB & SOK); clear ACCB;
    change (wa (a / 8 + 2147450880)) with (wa (shad a)) in RDB
  end.

Local Ltac diamond_bge FIN Σ buf size cap hp kk sz' K17 KM R0 SZ :=
  first
  [ rewrite sxb_z8; zstep; try if_true; apply evt_done;
    eapply aevt_eq; [| eapply (FIN Σ (mkSbA buf sz' cap hp kk))]; try eassumption; try pj_st_eq; slia
  | let Kc := fresh "Kc" in
    zstep; if_cases Kc; zify_cond Kc; [exfalso; pjnorm_in Kc; clear - Kc K17; lia| clear Kc];
    zstep; zstep; pjnorm; rewrite pj_land7 by (clear - R0 SZ; lia);
    zstep; if_cases Kc; zify_cond Kc;
      [exfalso; rewrite !pj_signed_small in Kc by (clear - K17; Z.div_mod_to_equations; lia); clear - Kc K17 KM; lia| clear Kc];
    zstep; apply evt_done; eapply aevt_eq; [| eapply (FIN Σ (mkSbA buf sz' cap hp kk))]; try eassumption; try pj_st_eq; slia ].

Lemma colon_finA : forall x24 x32 x72 x120 x136 x224 x232 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa7 xs7 xs9 xt3 xt4 xt5 xt6 : word),
  CERMC x24 x32 x72 x120 x136 x224 x232 obj_shpatA Σ st m -> frm0 fc -> 1 <= sa_size st -> sa_size st <= A + (3 + 6 * l) -> CCREDA RT E C Σ X st ->
  aevt Σ K (C1S 0xbc874 xra xt0 xt1 xt2 (wz (sa_buf st + (sa_size st - 1))) xa1 xa2 xa3 xa4 xa5 xa7 xs7 xs9 xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST GROW OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK.
  intros x24 x32 x72 x120 x136 x224 x232 Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa7 xs7 xs9 xt3 xt4 xt5 xt6 HSM FRM SZ1 ACC CR.
  pose proof HSTR as (C0 & L0 & CL & _). pose proof (cc_e E D C CX) as (I1 & IE & EN).
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf] in *.
  obj_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM.
  pose proof (obuf_factsA RT AF E D C OK CX f Σ _ _ OX HREF) as (_ & _ & _ & _ & APB). cbn [sa_buf sa_cap] in APB.
  pose proof (APB (buf + (size - 1)) ltac:(clear - SZ1 SZ; lia)) as (A1 & A2 & A3 & A4). clear APB.

  step. step. pj_store_done. zstep. zstep. zstep. zstep.
  oclose HSM2. apply evt_done.
  eapply aevt_eq; [| eapply (cont_call_serA RT AF PMc FDO MST E D C _ Σ (mkSbA buf size cap hp kk) _ K (x + 1) x1 (c + l + 5) cx X 0xbc88c)];
    [pj_st_eq| exact SER| exact OK| exact CX| apply obj_frp_local; exact OX| exact HSM2| exact FRM| exact EL| clear - Hx; lia| clear - Hx EN; lia
    | clear - C0 L0; lia| exact CXN| unfold sb_acc1A; cbn [sa_size]; clear - ACC BUD2; lia| exact CR| exact X2| clear; lia| reflexivity|].
  intros Σ' st' m' F' fc' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 FRM' HSM' ACC' CR'.
  eapply (HK Σ' st' m' F' fc' x24 x32 _ x72 _ _ x120 x136 x224 x232); [exact HSM'| exact FRM'| exact ACC'| exact CR'].
Qed.

Lemma colon_tailA : forall x24 x32 x72 x120 x136 x224 x232 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs7 xs9 xt3 xt4 xt5 xt6 : word),
  CERMC x24 x32 x72 x120 x136 x224 x232 obj_shpatA Σ st m -> frm0 fc -> sa_size st + 1 <= sa_cap st -> sa_size st <= A + 2 + 6 * l -> CCREDA RT E C Σ X st ->
  aevt Σ K (C1S 0xbc814 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs7 xs9 xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST GROW OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK.
  intros x24 x32 x72 x120 x136 x224 x232 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs7 xs9 xt3 xt4 xt5 xt6 HSM FRM ROOM ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  obj_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM. sb_shz.

  step. astep. astep. astep. astep.

  step. step. step. zstep. zstep. unbox FSB; unbox SHSB. step. box_disj.

  gtrap. unzt. gtrap.
  buf_sh (buf + size) ROOM SZ b RDB SOK.

  zstep. pjnorm. zstep. shfold. zstep.
  oclose HSM2.
  destruct (pj_sh_ok_cases b (buf + size) SOK) as [-> | (k & -> & K17 & KM)]; [| rewrite (pj_sxb_small7 k) by (clear - K17; lia)];
    diamond_bge (colon_finA x24 x32 x72 x120 x136 x224 x232) Σ buf size cap hp kk (size + 1) K17 KM R0 SZ.
Qed.

Lemma colonA : forall x24 x32 x72 x120 x136 x224 x232 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs7 xs9 xt3 xt4 xt5 xt6 : word),
  CERMC x24 x32 x72 x120 x136 x224 x232 obj_shpatA Σ st m -> frm0 fc -> sa_size st <= A + 2 + 6 * l -> CCREDA RT E C Σ X st ->
  aevt Σ K (C1S 0xbc7d4 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs7 xs9 xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST GROW OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK.
  intros x24 x32 x72 x120 x136 x224 x232 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs7 xs9 xt3 xt4 xt5 xt6 HSM FRM ACC CR.
  pose proof HSTR as (C0 & L0 & CL & _).
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  obj_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM. sb_shz.

  step. astep. astep. astep. astep.

  step. step. step. zstep. step.
  if_cases Kc; zify_cond Kc; pjnorm_in Kc.
  -
    oclose HSM2. apply evt_done.
    eapply aevt_eq; [| eapply (colon_tailA x24 x32 x72 x120 x136 x224 x232 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
  -
    zstep. pjnorm. zstep. zstep.
    oclose HSM3. apply evt_done.
    eapply aevt_eq; [| eapply (cont_growA RT AF PMc GROW E D C _ Σ (mkSbA buf size cap hp kk) _ K (2 * cap) X 0xbc810)];
      [pj_st_eq| exact OK| exact CX| apply obj_frp_local; exact OX| exact HSM3| | exact CR| exact X0| clear; lia| reflexivity|].
    { eapply (cont_req_ok2A RT E D C); [exact OK| exact CX| exact HSM3|]. cbn [sa_cap sa_size] in *. clear - Kc ACC BUD. lia. }
    intros Σ' NEW m' F' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CR4.
    apply (aevt_evt RT AF PMc MST). open HSM4.

    step.
    oclose HSM5. apply evt_done.
    eapply aevt_eq; [| eapply (colon_tailA x24 x32 x72 x120 x136 x224 x232 Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW (2 * cap)))]; try eassumption; try pj_st_eq;
      unfold sb_grownA; slia.
Qed.

Lemma close_finA : forall x24 x32 x72 x120 x136 x224 x232 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa7 xs7 xs9 xt3 xt4 xt5 xt6 : word),
  CERMC x24 x32 x72 x120 x136 x224 x232 obj_shpatA Σ st m -> frm0 fc -> 1 <= sa_size st -> sa_size st <= A + 2 + 6 * l -> CCREDA RT E C Σ X st ->
  aevt Σ K (C1S 0xbc7cc xra xt0 xt1 xt2 (wz (sa_buf st + (sa_size st - 1))) xa1 xa2 xa3 xa4 xa5 xa7 xs7 xs9 xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST GROW OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK.
  intros x24 x32 x72 x120 x136 x224 x232 Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa7 xs7 xs9 xt3 xt4 xt5 xt6 HSM FRM SZ1 ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf] in *.
  obj_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM.
  pose proof (obuf_factsA RT AF E D C OK CX f Σ _ _ OX HREF) as (_ & _ & _ & _ & APB). cbn [sa_buf sa_cap] in APB.
  pose proof (APB (buf + (size - 1)) ltac:(clear - SZ1 SZ; lia)) as (A1 & A2 & A3 & A4). clear APB.

  step. step. pj_store_done.
  oclose HSM2. apply evt_done.
  eapply aevt_eq; [| eapply (colonA x24 x32 x72 x120 x136 x224 x232 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
Qed.

Lemma close_tailA : forall x24 x32 x72 x120 x136 x224 x232 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs7 xs9 xt3 xt4 xt5 xt6 : word),
  CERMC x24 x32 x72 x120 x136 x224 x232 obj_shpatA Σ st m -> frm0 fc -> sa_size st + 1 <= sa_cap st -> sa_size st <= A + 1 + 6 * l -> CCREDA RT E C Σ X st ->
  aevt Σ K (C1S 0xbc760 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs7 xs9 xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST GROW OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK.
  intros x24 x32 x72 x120 x136 x224 x232 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs7 xs9 xt3 xt4 xt5 xt6 HSM FRM ROOM ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  obj_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM. sb_shz.

  step. astep. astep. astep. astep.

  step. step. step. zstep. zstep. unbox FSB; unbox SHSB. step. box_disj.

  gok. unzx. gok.
  buf_sh (buf + size) ROOM SZ b RDB SOK.

  zstep. pjnorm. zstep. shfold. zstep.
  oclose HSM2.
  destruct (pj_sh_ok_cases b (buf + size) SOK) as [-> | (k & -> & K17 & KM)]; [| rewrite (pj_sxb_small7 k) by (clear - K17; lia)];
    diamond_bge (close_finA x24 x32 x72 x120 x136 x224 x232) Σ buf size cap hp kk (size + 1) K17 KM R0 SZ.
Qed.

Lemma okey_closeA : forall x24 x32 x72 x120 x136 x224 x232 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs2 xs5 xs7 xs9 xs11 xt3 xt4 xt5 xt6 : word),
  CERMC x24 x32 x72 x120 x136 x224 x232 obj_shpatA Σ st m -> frm0 fc -> sa_size st <= A + 1 + 6 * l -> CCREDA RT E C Σ X st ->
  aevt Σ K (OST E C 0xbc714 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 (wz (shad (pa_SB E + 72))) xa7 xs2 (wz (M64M1 - PJ_NE_TAB_A)) xs5 (wz l) xs7
                 xs9 (wz PJ_NE_TAB_A) xs11 xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST GROW OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK.
  intros x24 x32 x72 x120 x136 x224 x232 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs2 xs5 xs7 xs9 xs11 xt3 xt4 xt5 xt6 HSM FRM ACC CR.
  pose proof HSTR as (C0 & L0 & CL & _).
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  obj_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM. sb_shz.

  step. astep. astep. astep. step. step. step. astep.

  step. step. step. zstep. step.
  if_cases Kc; zify_cond Kc; pjnorm_in Kc.
  -
    oclose HSM2. apply evt_done.
    eapply aevt_eq; [| eapply (close_tailA x24 x32 x72 x120 x136 x224 x232 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
  -
    zstep. pjnorm. zstep. zstep.
    oclose HSM3. apply evt_done.
    eapply aevt_eq; [| eapply (cont_growA RT AF PMc GROW E D C _ Σ (mkSbA buf size cap hp kk) _ K (2 * cap) X 0xbc75c)];
      [pj_st_eq| exact OK| exact CX| apply obj_frp_local; exact OX| exact HSM3| | exact CR| exact X0| clear; lia| reflexivity|].
    { eapply (cont_req_ok2A RT E D C); [exact OK| exact CX| exact HSM3|]. cbn [sa_cap sa_size] in *. clear - Kc ACC BUD. lia. }
    intros Σ' NEW m' F' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CR4.
    apply (aevt_evt RT AF PMc MST). open HSM4.

    step.
    oclose HSM5. apply evt_done.
    eapply aevt_eq; [| eapply (close_tailA x24 x32 x72 x120 x136 x224 x232 Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW (2 * cap)))]; try eassumption; try pj_st_eq;
      unfold sb_grownA; slia.
Qed.

Definition esc_botA_K (t : Z) : Prop :=
  forall x24 x32 x224 x232 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
         (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs2 xt3 xt4 xt5 xt6 : word),
    CERML x24 x32 x224 x232 obj_shpatA Σ st m -> frm0 fc -> sa_size st <= A + 1 + 6 * (t + 1) -> CCREDA RT E C Σ X st ->
    aevt Σ K (O1S 0xbc444 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs2 (wz t) xt3 xt4 xt5 xt6 F fc m).

Section Esc.
  Variable t : Z.
  Hypothesis KB : esc_botA_K t.
  Hypothesis HTL : 0 <= t < l.

  Lemma two_finA : forall x24 x32 x224 x232 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xt3 xt4 xt5 xt6 : word),
    CERML x24 x32 x224 x232 obj_shpatA Σ st m -> frm0 fc -> sa_size st + 2 <= sa_cap st -> sa_size st + 2 <= A + 1 + 6 * (t + 1) -> CCREDA RT E C Σ X st ->
    aevt Σ K (O1S 0xbc440 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 (wz (sa_size st + 2)) (wz t) xt3 xt4 xt5 xt6 F fc m).
  Proof using AF RC FDO MST GROW OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK KB HTL.
    intros x24 x32 x224 x232 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xt3 xt4 xt5 xt6 HSM FRM ROOM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    obj_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM.

    unbox FSB; unbox SHSB. step. box_disj.
    oclose HSM2. apply evt_done.
    eapply aevt_eq; [| eapply (KB x24 x32 x224 x232 Σ (mkSbA buf (size + 2) cap hp kk))]; try eassumption; try pj_st_eq; slia.
  Qed.

  Local Ltac fin2 stores x24 x32 x224 x232 Σ buf size cap hp kk HSM FRM ROOM ACC CR :=
    obj_envA OK CX OX; apply (aevt_evt RT AF PMc MST); open HSM;
    lazymatch goal with HREF : CREFA _ _ _ _ _ _, SZ : 0 <= size <= cap |- _ =>
    let APB := fresh "APB" in
    pose proof (obuf_factsA RT AF E D C OK CX f Σ _ _ OX HREF) as (_ & _ & _ & _ & APB); cbn [sa_buf sa_cap] in APB;
    pose proof (APB (buf + size) ltac:(clear - ROOM SZ; lia)) as (?A1 & ?A2 & ?A3 & ?A4);
    pose proof (APB (buf + size + 1) ltac:(clear - ROOM SZ; lia)) as (?B1 & ?B2 & ?B3 & ?B4); clear APB;
    stores;

    zstep; gok; sb_shz; astep; astep;
    let HSM2 := fresh "HSM2" in oclose HSM2; apply evt_done;
    eapply aevt_eq; [| eapply (two_finA x24 x32 x224 x232 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia
    end.
  Lemma q_finA : forall x24 x32 x224 x232 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa7 xt3 xt4 xt5 xt6 : word),
    CERML x24 x32 x224 x232 obj_shpatA Σ st m -> frm0 fc -> sa_size st + 2 <= sa_cap st -> sa_size st + 2 <= A + 1 + 6 * (t + 1) -> CCREDA RT E C Σ X st ->
    aevt Σ K (O1S 0xbc334 xra xt0 xt1 xt2 (wz (sa_buf st + sa_size st)) xa1 xa2 xa3 xa4 xa5 xa7 (wz (sa_size st + 2)) (wz t) xt3 xt4 xt5 xt6 F fc m).
  Proof using AF RC FDO MST GROW OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK KB HTL.
    intros x24 x32 x224 x232 Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa7 xt3 xt4 xt5 xt6 HSM FRM ROOM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    fin2 ltac:(step; pj_store_done; step; step; pj_store_done) x24 x32 x224 x232 Σ buf size cap hp kk HSM FRM ROOM ACC CR.
  Qed.
  Lemma b_finA : forall x24 x32 x224 x232 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa7 xt3 xt4 xt5 xt6 : word),
    CERML x24 x32 x224 x232 obj_shpatA Σ st m -> frm0 fc -> sa_size st + 2 <= sa_cap st -> sa_size st + 2 <= A + 1 + 6 * (t + 1) -> CCREDA RT E C Σ X st ->
    aevt Σ K (O1S 0xbc420 xra xt0 xt1 xt2 (wz (sa_buf st + sa_size st)) xa1 xa2 xa3 xa4 xa5 xa7 (wz (sa_size st + 2)) (wz t) xt3 xt4 xt5 xt6 F fc m).
  Proof using AF RC FDO MST GROW OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK KB HTL.
    intros x24 x32 x224 x232 Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa7 xt3 xt4 xt5 xt6 HSM FRM ROOM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    fin2 ltac:(step; pj_store_done; step; pj_store_done) x24 x32 x224 x232 Σ buf size cap hp kk HSM FRM ROOM ACC CR.
  Qed.

  Local Ltac diamond2 FIN x24 x32 x224 x232 Σ buf size cap hp kk HREF MU WM ROOM SZ R0 :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let ACCB := fresh "ACCB" in
      let MUc := omuc OX in pose proof (acc_buf_muC RT AF E D C OK CX Σ _ _ mm HREF MUc WM) as ACCB; cbn [sa_buf sa_cap] in ACCB;
      let b := fresh "b" in let RDB := fresh "RDB" in let SOK := fresh "SOK" in
      destruct (acc_read1 _ _ _ (buf + size + 1) ACCB ltac:(clear - ROOM SZ; lia)) as (b & RDB & SOK); clear ACCB;
      change (wa ((buf + size + 1) / 8 + 2147450880)) with (wa (shad (buf + size + 1))) in RDB;

      zstep; zstep; pjnorm; zstep; shfold; zstep;
      let HSM2 := fresh "HSM2" in oclose HSM2;
      let k := fresh "k" in let K17 := fresh "K17" in let KM := fresh "KM" in let Kc := fresh "Kc" in
      destruct (pj_sh_ok_cases b (buf + size + 1) SOK) as [-> | (k & -> & K17 & KM)];
      [ rewrite sxb_z8; zstep; if_false;
        apply evt_done; eapply aevt_eq; [| eapply (FIN x24 x32 x224 x232 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia
      | rewrite (pj_sxb_small7 k) by (clear - K17; lia); zstep;
        if_cases Kc; zify_cond Kc; [clear Kc| exfalso; pjnorm_in Kc; clear - Kc K17; lia];
        zstep; pjnorm; rewrite pj_land7 by (clear - R0 SZ; lia);
        zstep; if_cases Kc; zify_cond Kc;
          [clear Kc| exfalso; rewrite !pj_signed_small in Kc by (clear - K17; Z.div_mod_to_equations; lia); clear - Kc K17 KM; lia];
        apply evt_done; eapply aevt_eq; [| eapply (FIN x24 x32 x224 x232 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia ]
    end.
  Lemma q_d2A : forall x24 x32 x224 x232 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa7 xt3 xt4 xt5 xt6 : word),
    CERML x24 x32 x224 x232 obj_shpatA Σ st m -> frm0 fc -> sa_size st + 2 <= sa_cap st -> sa_size st + 2 <= A + 1 + 6 * (t + 1) -> CCREDA RT E C Σ X st ->
    aevt Σ K (O1S 0xbc320 xra xt0 xt1 xt2 (wz (sa_buf st + sa_size st)) xa1 xa2 xa3 xa4 xa5 xa7 (wz (sa_size st + 2)) (wz t) xt3 xt4 xt5 xt6 F fc m).
  Proof using AF RC FDO MST GROW OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK KB HTL.
    intros x24 x32 x224 x232 Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa7 xt3 xt4 xt5 xt6 HSM FRM ROOM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    obj_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM.
    diamond2 q_finA x24 x32 x224 x232 Σ buf size cap hp kk HREF MU WM ROOM SZ R0.
  Qed.
  Lemma b_d2A : forall x24 x32 x224 x232 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa7 xt3 xt4 xt5 xt6 : word),
    CERML x24 x32 x224 x232 obj_shpatA Σ st m -> frm0 fc -> sa_size st + 2 <= sa_cap st -> sa_size st + 2 <= A + 1 + 6 * (t + 1) -> CCREDA RT E C Σ X st ->
    aevt Σ K (O1S 0xbc40c xra xt0 xt1 xt2 (wz (sa_buf st + sa_size st)) xa1 xa2 xa3 xa4 xa5 xa7 (wz (sa_size st + 2)) (wz t) xt3 xt4 xt5 xt6 F fc m).
  Proof using AF RC FDO MST GROW OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK KB HTL.
    intros x24 x32 x224 x232 Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa7 xt3 xt4 xt5 xt6 HSM FRM ROOM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    obj_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM.
    diamond2 b_finA x24 x32 x224 x232 Σ buf size cap hp kk HREF MU WM ROOM SZ R0.
  Qed.

  Local Ltac tail2 D2 x24 x32 x224 x232 Σ buf size cap hp kk HREF MU WM ROOM SZ R0 :=
    sb_shz;

    step; astep; astep; astep; astep;

    step; step; step; zstep; try (replace (size + buf) with (buf + size) by (clear; lia));

    gok; unzx;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let ACCB := fresh "ACCB" in
      let MUc := omuc OX in pose proof (acc_buf_muC RT AF E D C OK CX Σ _ _ mm HREF MUc WM) as ACCB; cbn [sa_buf sa_cap] in ACCB;
      let b := fresh "b" in let RDB := fresh "RDB" in let SOK := fresh "SOK" in
      destruct (acc_read1 _ _ _ (buf + size) ACCB ltac:(clear - ROOM SZ; lia)) as (b & RDB & SOK); clear ACCB;
      change (wa ((buf + size) / 8 + 2147450880)) with (wa (shad (buf + size))) in RDB;

      zstep; pjnorm; zstep; shfold; zstep;
      let HSM2 := fresh "HSM2" in oclose HSM2;
      let k := fresh "k" in let K17 := fresh "K17" in let KM := fresh "KM" in let Kc := fresh "Kc" in
      destruct (pj_sh_ok_cases b (buf + size) SOK) as [-> | (k & -> & K17 & KM)];
      [ rewrite sxb_z8; zstep; if_false;
        apply evt_done; eapply aevt_eq; [| eapply (D2 x24 x32 x224 x232 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia
      | rewrite (pj_sxb_small7 k) by (clear - K17; lia); zstep;
        if_cases Kc; zify_cond Kc; [clear Kc| exfalso; pjnorm_in Kc; clear - Kc K17; lia];
        zstep; pjnorm; rewrite pj_land7 by (clear - R0 SZ; lia);
        zstep; if_cases Kc; zify_cond Kc;
          [clear Kc| exfalso; rewrite !pj_signed_small in Kc by (clear - K17; Z.div_mod_to_equations; lia); clear - Kc K17 KM; lia];
        apply evt_done; eapply aevt_eq; [| eapply (D2 x24 x32 x224 x232 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia ]
    end.
  Lemma q_tailA : forall x24 x32 x224 x232 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xt3 xt4 xt5 xt6 : word),
    CERML x24 x32 x224 x232 obj_shpatA Σ st m -> frm0 fc -> sa_size st + 2 <= sa_cap st -> sa_size st + 2 <= A + 1 + 6 * (t + 1) -> CCREDA RT E C Σ X st ->
    aevt Σ K (O1S 0xbc2c8 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 (wz (sa_size st + 2)) (wz t) xt3 xt4 xt5 xt6 F fc m).
  Proof using AF RC FDO MST GROW OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK KB HTL.
    intros x24 x32 x224 x232 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xt3 xt4 xt5 xt6 HSM FRM ROOM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    obj_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM.
    tail2 q_d2A x24 x32 x224 x232 Σ buf size cap hp kk HREF MU WM ROOM SZ R0.
  Qed.
  Lemma b_tailA : forall x24 x32 x224 x232 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xt3 xt4 xt5 xt6 : word),
    CERML x24 x32 x224 x232 obj_shpatA Σ st m -> frm0 fc -> sa_size st + 2 <= sa_cap st -> sa_size st + 2 <= A + 1 + 6 * (t + 1) -> CCREDA RT E C Σ X st ->
    aevt Σ K (O1S 0xbc3b4 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 (wz (sa_size st + 2)) (wz t) xt3 xt4 xt5 xt6 F fc m).
  Proof using AF RC FDO MST GROW OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK KB HTL.
    intros x24 x32 x224 x232 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xt3 xt4 xt5 xt6 HSM FRM ROOM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    obj_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM.
    tail2 b_d2A x24 x32 x224 x232 Σ buf size cap hp kk HREF MU WM ROOM SZ R0.
  Qed.
End Esc.
End OKeyA.
