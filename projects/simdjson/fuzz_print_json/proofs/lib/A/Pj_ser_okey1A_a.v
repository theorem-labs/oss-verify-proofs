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
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer SjPjCont.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.A Require Import Layout Shadow RT_iface RT_iface2 RT_iface3 RT_iface4 D_defs D_kit D_clx D_libiface I_lkit
     Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_hkit5A Atp_fzwA Pj_rtkA Pj_defsA Pj_cpsA Pj_ser_defsA Pj_ser_kitA Pj_ser_callsA Pj_ser_proA Pj_ser_topA Pj_ser_ckitA
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

Ltac omucx OX := let c := omuc OX in exact c.

Section OKeyA.
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
Hypothesis HK : forall (Σ' : rts RT) (st' : sbA) (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (y48 y56 y64 y224 y232 y240 : word)
            (yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys8 ys9 ys11 yt3 yt4 yt5 yt6 : word),
    CERMA RT E C (obj_frp E C f (owK E C f y48 y56 y64 (wz M56M1) (wz ((pa_DOC E + 8) / 8 + 2147450880)) (wz (pa_DOC E + 8)) (wz (pa_DOC E)) (wz M32M8)
                                    (wz c) (wz (pa_SBUF E)) (wz (x + 1)) (wz (pa_SB E)) (wz PJ_ESC_TAB_A) (wz (x - 1)) (wz (f + 64)) y224 y232 y240) obj_shpatA) Σ' st' m' ->
    frm0 fc' -> sb_accA st' x1 cx -> CCREDA RT E C Σ' (X - 2 * (x1 - (x + 1))) st' ->
    aevt Σ' K (OST E C 0xb6ea4 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 (wz (pa_DOC E)) (wz (pa_SB E + 80)) (wz (x + 1)) (wz PJ_NE_TAB_A) ys8 ys9 (wz (pa_SB E)) ys11
                   yt3 yt4 yt5 yt6 F' fc' m').

Notation DATA := (pa_SBUF E + c + 4).

Definition ok1w (x48 x56 x64 x96 x160 x224 x232 x240 : word) : owA :=
  owK E C f x48 x56 x64 (wz M56M1) (wz ((pa_DOC E + 8) / 8 + 2147450880)) (wz (pa_DOC E + 8)) x96 (wz M32M8) (wz c) (wz (pa_SBUF E)) (wz (x + 1)) (wz (pa_SB E))
      x160 (wz (x - 1)) (wz (f + 64)) x224 x232 x240.
Notation CERMO x48 x56 x64 x96 x160 x224 x232 x240 Σ st m := (CERMA RT E C (obj_frp E C f (ok1w x48 x56 x64 x96 x160 x224 x232 x240) obj_shpatA) Σ st m).

Notation CERML x48 x56 x64 x224 x232 x240 Σ st m := (CERMO x48 x56 x64 (wz (pa_DOC E)) (wz PJ_ESC_TAB_A) x224 x232 x240 Σ st m).

Notation OK1S pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs8 xs10 xs11 xt3 xt4 xt6 F fc m :=
  (OST E C pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (pa_SB E + 80)) (Z_to_bv 64 92) (Z_to_bv 64 PJ_NE_TAB_A) xs8 (Z_to_bv 64 (f + 32)) xs10 xs11
       xt3 xt4 (Z_to_bv 64 (shad (pa_SB E + 72))) xt6 F fc m).

Local Ltac slia := repeat match goal with H : _ \/ _ |- _ => clear H end; cbn [sa_size sa_cap sa_buf sa_heap sa_k]; lia.

Local Ltac sb_shz :=
  lazymatch goal with
  | HREF : CREFA _ _ _ _ _ ?mr, MU : munch _ ?mr ?mm, WM : wmono asegs ?mr ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let SHZ := fresh "SHZ" in let R64 := fresh "RD64" in let R72 := fresh "RD72" in let R80 := fresh "RD80" in
    let MUc := omuc OX in
    pose proof (shz_sb_muC RT AF E D C OK CX _ _ _ mm HREF MUc WM) as SHZ;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 64) ltac:(clear; lia)) as R64;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 72) ltac:(clear; lia)) as R72;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 80) ltac:(clear; lia)) as R80; clear SHZ
  end.

Local Ltac shf_open := match goal with SHF : rw_cells _ _ _ (sh16 _) |- _ => unfold sh16, obj_shpatA in SHF; cbn [map] in SHF | _ => idtac end.
Local Ltac shf_fold := match goal with SHF : rw_cells asegs ?m (?g / 8 + 2147450880) ?cs |- _ =>
  change (rw_cells asegs m (g / 8 + 2147450880) cs) with (rw_cells asegs m (g / 8 + 2147450880) (sh16 obj_shpatA)) in SHF | _ => idtac end.
Local Ltac open HSM := unfold ok1w in HSM; obj_open HSM OK CX OX; shf_open.
Local Ltac oclose HSM := shf_fold; obj_close HSM OX.

Local Ltac buf_sh a ROOM SZ b RDB SOK :=
  lazymatch goal with HREF : CREFA _ _ _ ?Σc _ ?mr, WM : wmono asegs ?mr ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let ACCB := fresh "ACCB" in let MUc := omuc OX in
    pose proof (acc_buf_muC RT AF E D C OK CX Σc _ _ mm HREF MUc WM) as ACCB; cbn [sa_buf sa_cap] in ACCB;
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

Lemma colon_finA : forall x48 x56 x64 x224 x232 x240 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xs9 xs11 xt3 xt4 xt6 : word),
  CERML x48 x56 x64 x224 x232 x240 Σ st m -> frm0 fc -> 1 <= sa_size st -> sa_size st <= A + (3 + 6 * l) -> CCREDA RT E C Σ X st ->
  aevt Σ K (OST E C 0xb6e8c xra xt0 xt1 xt2 (wz (sa_buf st + (sa_size st - 1))) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (pa_DOC E)) (wz (pa_SB E + 80)) (wz (x + 1)) (wz PJ_NE_TAB_A)
                 xs8 xs9 (wz (pa_SB E)) xs11 xt3 xt4 (wz (shad (pa_SB E + 72))) xt6 F fc m).
Proof using AF RC FDO MST GROW TABS OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK.
  intros x48 x56 x64 x224 x232 x240 Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xs9 xs11 xt3 xt4 xt6 HSM FRM SZ1 ACC CR.
  pose proof HSTR as (C0 & L0 & CL & _). pose proof (cc_e E D C CX) as (I1 & IE & EN).
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf] in *.
  ostr_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM.
  pose proof (obuf_factsA RT AF E D C OK CX f Σ _ _ OX HREF) as (_ & _ & _ & _ & APB). cbn [sa_buf sa_cap] in APB.
  pose proof (APB (buf + (size - 1)) ltac:(clear - SZ1 SZ; lia)) as (A1 & A2 & A3 & A4). clear APB.

  step. step. pj_store_done. zstep. zstep. zstep. zstep.
  oclose HSM2. apply evt_done.
  eapply aevt_eq; [| eapply (cont_call_serA RT AF PMc FDO MST E D C _ Σ (mkSbA buf size cap hp kk) _ K (x + 1) x1 (c + l + 5) cx X 0xb6ea4)];
    [pj_st_eq| exact SER| exact OK| exact CX| apply obj_frp_local; exact OX| exact HSM2| exact FRM| exact EL| clear - Hx; lia| clear - Hx EN; lia
    | clear - C0 L0; lia| exact CXN| unfold sb_acc1A; cbn [sa_size]; clear - ACC BUD2; lia| exact CR| exact X2| clear; lia| reflexivity|].
  intros Σ' st' m' F' fc' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 FRM' HSM' ACC' CR'.
  eapply (HK Σ' st' m' F' fc' x48 x56 x64 x224 x232 x240); [exact HSM'| exact FRM'| exact ACC'| exact CR'].
Qed.

Lemma colon_tailA : forall x48 x56 x64 x224 x232 x240 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xs9 xs11 xt3 xt4 xt6 : word),
  CERML x48 x56 x64 x224 x232 x240 Σ st m -> frm0 fc -> sa_size st + 1 <= sa_cap st -> sa_size st <= A + 2 + 6 * l -> CCREDA RT E C Σ X st ->
  aevt Σ K (OST E C 0xb6e48 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (pa_DOC E)) (wz (pa_SB E + 80)) (wz (x + 1)) (wz PJ_NE_TAB_A)
                 xs8 xs9 (wz (pa_SB E)) xs11 xt3 xt4 (wz (shad (pa_SB E + 72))) xt6 F fc m).
Proof using AF RC FDO MST GROW TABS OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK.
  intros x48 x56 x64 x224 x232 x240 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xs9 xs11 xt3 xt4 xt6 HSM FRM ROOM ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ostr_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM. sb_shz.

  step. astep. astep. astep. astep.

  step. step. step. zstep. zstep. unbox FSB; unbox SHSB. step. box_disj.
  buf_sh (buf + size) ROOM SZ b RDB SOK.

  zstep. pjnorm. zstep. shfold. zstep.
  oclose HSM2.
  destruct (pj_sh_ok_cases b (buf + size) SOK) as [-> | (k & -> & K17 & KM)]; [| rewrite (pj_sxb_small7 k) by (clear - K17; lia)];
    diamond_blt (colon_finA x48 x56 x64 x224 x232 x240) Σ buf size cap hp kk (size + 1) K17 KM R0 SZ.
Qed.

Lemma colonA : forall x48 x56 x64 x224 x232 x240 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xs9 xs11 xt3 xt4 xt6 : word),
  CERML x48 x56 x64 x224 x232 x240 Σ st m -> frm0 fc -> sa_size st <= A + 2 + 6 * l -> CCREDA RT E C Σ X st ->
  aevt Σ K (OST E C 0xb6e18 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (pa_DOC E)) (wz (pa_SB E + 80)) (wz (x + 1)) (wz PJ_NE_TAB_A)
                 xs8 xs9 (wz (pa_SB E)) xs11 xt3 xt4 (wz (shad (pa_SB E + 72))) xt6 F fc m).
Proof using AF RC FDO MST GROW TABS OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK.
  intros x48 x56 x64 x224 x232 x240 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xs9 xs11 xt3 xt4 xt6 HSM FRM ACC CR.
  pose proof HSTR as (C0 & L0 & CL & _).
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ostr_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM. sb_shz.

  step. astep. astep. step. step. zstep. step.
  if_cases Kc; zify_cond Kc; pjnorm_in Kc.
  -
    oclose HSM2. apply evt_done.
    eapply aevt_eq; [| eapply (colon_tailA x48 x56 x64 x224 x232 x240 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
  -
    zstep. pjnorm. zstep. zstep.
    oclose HSM3. apply evt_done.
    eapply aevt_eq; [| eapply (cont_growA RT AF PMc GROW E D C _ Σ (mkSbA buf size cap hp kk) _ K (2 * cap) X 0xb6e44)];
      [pj_st_eq| exact OK| exact CX| apply obj_frp_local; exact OX| exact HSM3| | exact CR| exact X0| clear; lia| reflexivity|].
    { eapply (cont_req_ok2A RT E D C); [exact OK| exact CX| exact HSM3|]. cbn [sa_cap sa_size] in *. clear - Kc ACC BUD. lia. }
    intros Σ' NEW m' F' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CR4.
    apply (aevt_evt RT AF PMc MST). open HSM4.

    step.
    oclose HSM5. apply evt_done.
    eapply aevt_eq; [| eapply (colon_tailA x48 x56 x64 x224 x232 x240 Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW (2 * cap)))]; try eassumption; try pj_st_eq;
      unfold sb_grownA; slia.
Qed.

Lemma close_finA : forall x48 x56 x64 x224 x232 x240 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xs9 xs11 xt3 xt4 xt6 : word),
  CERML x48 x56 x64 x224 x232 x240 Σ st m -> frm0 fc -> 1 <= sa_size st -> sa_size st <= A + 2 + 6 * l -> CCREDA RT E C Σ X st ->
  aevt Σ K (OST E C 0xb6e10 xra xt0 xt1 xt2 (wz (sa_buf st + (sa_size st - 1))) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (pa_DOC E)) (wz (pa_SB E + 80)) (wz (x + 1)) (wz PJ_NE_TAB_A)
                 xs8 xs9 (wz (pa_SB E)) xs11 xt3 xt4 (wz (shad (pa_SB E + 72))) xt6 F fc m).
Proof using AF RC FDO MST GROW TABS OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK.
  intros x48 x56 x64 x224 x232 x240 Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xs9 xs11 xt3 xt4 xt6 HSM FRM SZ1 ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf] in *.
  ostr_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM.
  pose proof (obuf_factsA RT AF E D C OK CX f Σ _ _ OX HREF) as (_ & _ & _ & _ & APB). cbn [sa_buf sa_cap] in APB.
  pose proof (APB (buf + (size - 1)) ltac:(clear - SZ1 SZ; lia)) as (A1 & A2 & A3 & A4). clear APB.

  step. step. pj_store_done.
  oclose HSM2. apply evt_done.
  eapply aevt_eq; [| eapply (colonA x48 x56 x64 x224 x232 x240 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
Qed.

Lemma close_tailA : forall x48 x56 x64 x224 x232 x240 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xs9 xs11 xt3 xt4 xt6 : word),
  CERML x48 x56 x64 x224 x232 x240 Σ st m -> frm0 fc -> sa_size st + 1 <= sa_cap st -> sa_size st <= A + 1 + 6 * l -> CCREDA RT E C Σ X st ->
  aevt Σ K (OST E C 0xb6dcc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (pa_DOC E)) (wz (pa_SB E + 80)) (wz (x + 1)) (wz PJ_NE_TAB_A)
                 xs8 xs9 (wz (pa_SB E)) xs11 xt3 xt4 (wz (shad (pa_SB E + 72))) xt6 F fc m).
Proof using AF RC FDO MST GROW TABS OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK.
  intros x48 x56 x64 x224 x232 x240 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xs9 xs11 xt3 xt4 xt6 HSM FRM ROOM ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ostr_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM. sb_shz.

  step. astep. astep. astep. astep.

  step. step. step. zstep. zstep. unbox FSB; unbox SHSB. step. box_disj.
  buf_sh (buf + size) ROOM SZ b RDB SOK.

  zstep. pjnorm. zstep. shfold. zstep.
  oclose HSM2.
  destruct (pj_sh_ok_cases b (buf + size) SOK) as [-> | (k & -> & K17 & KM)]; [| rewrite (pj_sxb_small7 k) by (clear - K17; lia)];
    diamond_blt (close_finA x48 x56 x64 x224 x232 x240) Σ buf size cap hp kk (size + 1) K17 KM R0 SZ.
Qed.

Lemma okey_closeA : forall x48 x56 x64 x224 x232 x240 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs6 xs8 xs10 xs11 xt3 xt4 xt6 : word),
  CERML x48 x56 x64 x224 x232 x240 Σ st m -> frm0 fc -> sa_size st <= A + 1 + 6 * l -> CCREDA RT E C Σ X st ->
  aevt Σ K (OST E C 0xb6d84 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (wz (pa_SB E + 80)) xs6 (wz PJ_NE_TAB_A) xs8 (wz (f + 32)) xs10 xs11
                 xt3 xt4 (wz (shad (pa_SB E + 72))) xt6 F fc m).
Proof using AF RC FDO MST GROW TABS OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK.
  intros x48 x56 x64 x224 x232 x240 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs6 xs8 xs10 xs11 xt3 xt4 xt6 HSM FRM ACC CR.
  pose proof HSTR as (C0 & L0 & CL & _).
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ostr_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM. sb_shz.

  step. astep. astep. astep. step. step. step. astep.

  step. step. zstep. step.
  if_cases Kc; zify_cond Kc; pjnorm_in Kc.
  -
    oclose HSM2. apply evt_done.
    eapply aevt_eq; [| eapply (close_tailA x48 x56 x64 x224 x232 x240 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
  -
    zstep. pjnorm. zstep. zstep.
    oclose HSM3. apply evt_done.
    eapply aevt_eq; [| eapply (cont_growA RT AF PMc GROW E D C _ Σ (mkSbA buf size cap hp kk) _ K (2 * cap) X 0xb6dc8)];
      [pj_st_eq| exact OK| exact CX| apply obj_frp_local; exact OX| exact HSM3| | exact CR| exact X0| clear; lia| reflexivity|].
    { eapply (cont_req_ok2A RT E D C); [exact OK| exact CX| exact HSM3|]. cbn [sa_cap sa_size] in *. clear - Kc ACC BUD. lia. }
    intros Σ' NEW m' F' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CR4.
    apply (aevt_evt RT AF PMc MST). open HSM4.

    step.
    oclose HSM5. apply evt_done.
    eapply aevt_eq; [| eapply (close_tailA x48 x56 x64 x224 x232 x240 Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW (2 * cap)))]; try eassumption; try pj_st_eq;
      unfold sb_grownA; slia.
Qed.

Definition kesc_botA_K (t : Z) : Prop :=
  forall x48 x56 x64 x224 x232 x240 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
         (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 xt6 : word),
    CERML x48 x56 x64 x224 x232 x240 Σ st m -> frm0 fc -> sa_size st <= A + 1 + 6 * (t + 1) -> CCREDA RT E C Σ X st ->
    aevt Σ K (OK1S 0xb6b24 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (DATA + t)) xs9 (wz (DATA + t)) (wz (l - t)) xt3 xt4 xt6 F fc m).

Section Esc.
  Variable t : Z.
  Hypothesis KB : kesc_botA_K t.
  Hypothesis HT : 0 <= t < l.

  Lemma two_finA : forall x48 x56 x64 x224 x232 x240 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
    CERML x48 x56 x64 x224 x232 x240 Σ st m -> frm0 fc -> sa_size st + 2 <= sa_cap st -> sa_size st + 2 <= A + 1 + 6 * (t + 1) -> CCREDA RT E C Σ X st ->
    aevt Σ K (OK1S 0xb6b20 xra xt0 xt1 xt2 (wz (sa_buf st + sa_size st)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (DATA + t)) (wz (sa_size st + 2)) (wz (DATA + t)) (wz (l - t)) xt3 xt4 xt6 F fc m).
  Proof using AF RC FDO MST GROW TABS OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK KB HT.
    intros x48 x56 x64 x224 x232 x240 Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 HSM FRM ROOM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ostr_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM.

    unbox FSB; unbox SHSB. step. box_disj.
    oclose HSM2. apply evt_done.
    eapply aevt_eq; [| eapply (KB x48 x56 x64 x224 x232 x240 Σ (mkSbA buf (size + 2) cap hp kk))]; try eassumption; try pj_st_eq; slia.
  Qed.

  Lemma q_fin2A : forall x48 x56 x64 x224 x232 x240 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
    CERML x48 x56 x64 x224 x232 x240 Σ st m -> frm0 fc -> sa_size st + 2 <= sa_cap st -> sa_size st + 2 <= A + 1 + 6 * (t + 1) -> CCREDA RT E C Σ X st ->
    aevt Σ K (OK1S 0xb6a70 xra xt0 xt1 xt2 (wz (sa_buf st + sa_size st)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (DATA + t)) (wz (sa_size st + 2)) (wz (DATA + t)) (wz (l - t)) xt3 xt4 xt6 F fc m).
  Proof using AF RC FDO MST GROW TABS OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK KB HT.
    intros x48 x56 x64 x224 x232 x240 Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 HSM FRM ROOM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ostr_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM.
    pose proof (obuf_factsA RT AF E D C OK CX f Σ _ _ OX HREF) as (_ & _ & _ & _ & APB). cbn [sa_buf sa_cap] in APB.
    pose proof (APB (buf + size) ltac:(clear - ROOM SZ; lia)) as (A1 & A2 & A3 & A4).
    pose proof (APB (buf + size + 1) ltac:(clear - ROOM SZ; lia)) as (B1 & B2 & B3 & B4). clear APB.

    step. pj_store_done. step. step. pj_store_done. step.
    oclose HSM2. apply evt_done.
    eapply aevt_eq; [| eapply (two_finA x48 x56 x64 x224 x232 x240 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
  Qed.
  Lemma b_fin2A : forall x48 x56 x64 x224 x232 x240 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
    CERML x48 x56 x64 x224 x232 x240 Σ st m -> frm0 fc -> sa_size st + 2 <= sa_cap st -> sa_size st + 2 <= A + 1 + 6 * (t + 1) -> CCREDA RT E C Σ X st ->
    aevt Σ K (OK1S 0xb6b18 xra xt0 xt1 xt2 (wz (sa_buf st + sa_size st)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (DATA + t)) (wz (sa_size st + 2)) (wz (DATA + t)) (wz (l - t)) xt3 xt4 xt6 F fc m).
  Proof using AF RC FDO MST GROW TABS OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK KB HT.
    intros x48 x56 x64 x224 x232 x240 Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 HSM FRM ROOM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ostr_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM.
    pose proof (obuf_factsA RT AF E D C OK CX f Σ _ _ OX HREF) as (_ & _ & _ & _ & APB). cbn [sa_buf sa_cap] in APB.
    pose proof (APB (buf + size) ltac:(clear - ROOM SZ; lia)) as (A1 & A2 & A3 & A4).
    pose proof (APB (buf + size + 1) ltac:(clear - ROOM SZ; lia)) as (B1 & B2 & B3 & B4). clear APB.

    step. pj_store_done. step. pj_store_done.
    oclose HSM2. apply evt_done.
    eapply aevt_eq; [| eapply (two_finA x48 x56 x64 x224 x232 x240 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
  Qed.

  Local Ltac diamond2 FIN x48 x56 x64 x224 x232 x240 Σ buf size cap hp kk HREF MU WM ROOM SZ R0 :=
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
        apply evt_done; eapply aevt_eq; [| eapply (FIN x48 x56 x64 x224 x232 x240 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia
      | rewrite (pj_sxb_small7 k) by (clear - K17; lia); zstep;
        if_cases Kc; zify_cond Kc; [clear Kc| exfalso; pjnorm_in Kc; clear - Kc K17; lia];
        zstep; pjnorm; rewrite pj_land7 by (clear - R0 SZ; lia);
        zstep; if_cases Kc; zify_cond Kc;
          [clear Kc| exfalso; rewrite !pj_signed_small in Kc by (clear - K17; Z.div_mod_to_equations; lia); clear - Kc K17 KM; lia];
        apply evt_done; eapply aevt_eq; [| eapply (FIN x48 x56 x64 x224 x232 x240 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia ]
    end.

  Lemma q_d2A : forall x48 x56 x64 x224 x232 x240 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
    CERML x48 x56 x64 x224 x232 x240 Σ st m -> frm0 fc -> sa_size st + 2 <= sa_cap st -> sa_size st + 2 <= A + 1 + 6 * (t + 1) -> CCREDA RT E C Σ X st ->
    aevt Σ K (OK1S 0xb6a5c xra xt0 xt1 xt2 (wz (sa_buf st + sa_size st)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (DATA + t)) (wz (sa_size st + 2)) (wz (DATA + t)) (wz (l - t)) xt3 xt4 xt6 F fc m).
  Proof using AF RC FDO MST GROW TABS OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK KB HT.
    intros x48 x56 x64 x224 x232 x240 Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 HSM FRM ROOM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ostr_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM.
    diamond2 q_fin2A x48 x56 x64 x224 x232 x240 Σ buf size cap hp kk HREF MU WM ROOM SZ R0.
  Qed.
  Lemma b_d2A : forall x48 x56 x64 x224 x232 x240 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
    CERML x48 x56 x64 x224 x232 x240 Σ st m -> frm0 fc -> sa_size st + 2 <= sa_cap st -> sa_size st + 2 <= A + 1 + 6 * (t + 1) -> CCREDA RT E C Σ X st ->
    aevt Σ K (OK1S 0xb6b04 xra xt0 xt1 xt2 (wz (sa_buf st + sa_size st)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (DATA + t)) (wz (sa_size st + 2)) (wz (DATA + t)) (wz (l - t)) xt3 xt4 xt6 F fc m).
  Proof using AF RC FDO MST GROW TABS OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK KB HT.
    intros x48 x56 x64 x224 x232 x240 Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 HSM FRM ROOM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ostr_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM.
    diamond2 b_fin2A x48 x56 x64 x224 x232 x240 Σ buf size cap hp kk HREF MU WM ROOM SZ R0.
  Qed.

  Local Ltac tail2 D2 x48 x56 x64 x224 x232 x240 Σ buf size cap hp kk HREF MU WM ROOM SZ R0 :=
    sb_shz;

    step; astep; astep; astep; astep;

    step; step; step; zstep;
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
        apply evt_done; eapply aevt_eq; [| eapply (D2 x48 x56 x64 x224 x232 x240 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia
      | rewrite (pj_sxb_small7 k) by (clear - K17; lia); zstep;
        if_cases Kc; zify_cond Kc; [clear Kc| exfalso; pjnorm_in Kc; clear - Kc K17; lia];
        zstep; pjnorm; rewrite pj_land7 by (clear - R0 SZ; lia);
        zstep; if_cases Kc; zify_cond Kc;
          [clear Kc| exfalso; rewrite !pj_signed_small in Kc by (clear - K17; Z.div_mod_to_equations; lia); clear - Kc K17 KM; lia];
        apply evt_done; eapply aevt_eq; [| eapply (D2 x48 x56 x64 x224 x232 x240 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia ]
    end.

  Lemma q_tailA : forall x48 x56 x64 x224 x232 x240 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
    CERML x48 x56 x64 x224 x232 x240 Σ st m -> frm0 fc -> sa_size st + 2 <= sa_cap st -> sa_size st + 2 <= A + 1 + 6 * (t + 1) -> CCREDA RT E C Σ X st ->
    aevt Σ K (OK1S 0xb6a20 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (DATA + t)) (wz (sa_size st + 2)) (wz (DATA + t)) (wz (l - t)) xt3 xt4 xt6 F fc m).
  Proof using AF RC FDO MST GROW TABS OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK KB HT.
    intros x48 x56 x64 x224 x232 x240 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 HSM FRM ROOM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ostr_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM.
    tail2 q_d2A x48 x56 x64 x224 x232 x240 Σ buf size cap hp kk HREF MU WM ROOM SZ R0.
  Qed.
  Lemma b_tailA : forall x48 x56 x64 x224 x232 x240 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
    CERML x48 x56 x64 x224 x232 x240 Σ st m -> frm0 fc -> sa_size st + 2 <= sa_cap st -> sa_size st + 2 <= A + 1 + 6 * (t + 1) -> CCREDA RT E C Σ X st ->
    aevt Σ K (OK1S 0xb6ac8 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (DATA + t)) (wz (sa_size st + 2)) (wz (DATA + t)) (wz (l - t)) xt3 xt4 xt6 F fc m).
  Proof using AF RC FDO MST GROW TABS OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK KB HT.
    intros x48 x56 x64 x224 x232 x240 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 HSM FRM ROOM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ostr_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM.
    tail2 b_d2A x48 x56 x64 x224 x232 x240 Σ buf size cap hp kk HREF MU WM ROOM SZ R0.
  Qed.

End Esc.
End OKeyA.
