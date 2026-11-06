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
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.A Require Import Layout Shadow RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_libiface I_lkit
     Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_hkit5A Atp_fzwA Pj_rtkA Pj_defsA Pj_cpsA Pj_ser_defsA Pj_ser_kitA Pj_ser_callsA Pj_ser_dispA Pj_ser_proA Pj_ser_ckitA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_store ::= first [ pj_solve_store0 | pj_store_wr ].
Local Ltac pj_st_eq_leaf ::=
  lazymatch goal with
  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | f_equal; cbn [length sa_buf sa_size sa_cap Z.b2z]; lia]
  | |- _ => reflexivity
  end.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition ca_savedA (C : conI) : list cell :=
  [C8 (ci_s11 C); C8 (ci_s10 C); C8 (ci_s9 C); C8 (ci_s8 C); C8 (ci_s7 C); C8 (ci_s6 C); C8 (ci_s5 C); C8 (ci_s4 C);
   C8 (ci_s3 C); C8 (ci_s2 C); C8 (ci_s1 C); C8 (ci_s0 C); C8 (ci_ra C)].

Definition arr_frp (E : pjenvA) (C : conI) (v0 v8 : word) (m : mem) : Prop :=
  rw_cells asegs m (ci_b C) [C8 v0; C8 v8; C8 (wz (pa_SB E + 80))] /\ rw_cells asegs m (ci_b C + 24) (ca_savedA C).

Lemma munch_conWA0 : forall E C st m m', ci_R_ C = [] ->
  munch [(ci_b C, ci_q C); (sa_buf st, sa_buf st + sa_cap st); (pa_SB E, pa_SB E + 88)] m m' -> munch (conWA E C st) m m'.
Proof. intros E C st m m' H MU. unfold conWA, cr_R. rewrite H. exact MU. Qed.

Lemma arr_frp_local : forall E C v0 v8, ci_b C + 128 = ci_q C -> frp_local C (arr_frp E C v0 v8).
Proof.
  intros E C v0 v8 HB m m' AG [H1 H2]. split.
  - eapply rw_cells_agree_nw; [exact H1|]. eapply agree_sub; [exact AG|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx.
    exists (ci_b C), (ci_q C). split; [left; reflexivity| lia].
  - eapply rw_cells_agree_nw; [exact H2|]. eapply agree_sub; [exact AG|]. intros x Hx. unfold ca_savedA in Hx. cbn [cells_size csize Nat.add] in Hx.
    exists (ci_b C), (ci_q C). split; [left; reflexivity| lia].
Qed.

Section Arr.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis GROW : grow_cpsA RT PMc.
Variables (E : pjenvA) (D : nat) (C : conI) (K : config -> Prop).
Hypothesis OK : pjenvA_ok E.
Hypothesis CX : cctxA E D C.
Hypothesis HB128 : ci_b C + 128 = ci_q C.
Hypothesis HR0 : ci_R_ C = [].
Hypothesis HFR0 : ci_fr C = ci_fr0 C.
Hypothesis SER : ser_cpsA RT PMc D.

Variable n0 : Z. Variable c0 : Z.
Hypothesis HTY : ty (pa_T E) (ci_i C) = t_arr.
Hypothesis HNX : tnext (pa_T E (ci_i C)) = ci_e C + 1.
Hypothesis HTE : ty (pa_T E) (ci_e C) = t_arr_end.
Hypothesis HT : tilesS (elemS (pa_T E) (pa_S E) (pa_sn E) ck_any D) (ci_i C + 1) (ci_e C) n0 c0 (ci_c' C).
Hypothesis HC0 : 0 <= c0.

Hypothesis KFIN : forall (Σ' : rts RT) (st' : sbA) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
  frm0 fc' -> ART RT Σ' m' -> mem_inv asegs m' -> stk asegs m' (pa_lo E) (ci_q C) ->
  SBINVA E m' st' -> DOCREPA E m' -> sb_accA st' (ci_e C + 1) (ci_c' C) -> pa_live RT Σ' E st' ->
  rt_frames RT Σ' = ci_fr0 C -> rt_sp0 RT Σ' = ci_sp0 C -> ci_R C + pj_psi (pa_len E) st' <= rt_credit RT Σ' ->
  rt_pres_fp (pa_L E) (ci_fr0 C) (ci_q C) [(pa_SB E, pa_SB E + 88)] (ci_m0 C) m' ->
  aevt RT PMc Σ' K (MS (mkR (ci_ra C) (wz (ci_q C)) (ci_gp C) (wz TPV_A) t0' t1' t2' (ci_s0 C) (ci_s1 C) a0' a1' a2' a3' a4' a5' a6' a7'
                         (ci_s2 C) (ci_s3 C) (ci_s4 C) (ci_s5 C) (ci_s6 C) (ci_s7 C) (ci_s8 C) (ci_s9 C) (ci_s10 C) (ci_s11 C) t3' t4' t5' t6')
                    F' (ret_pc (ci_ra C)) fc' None m' (seg_rom asegs)).
Notation aevt := (aevt RT PMc).
Notation e := (ci_e C).
Notation ELEM := (elemS (pa_T E) (pa_S E) (pa_sn E) ck_any D).
Notation AFRP := (arr_frp E C).
Local Ltac slia := repeat match goal with H : _ \/ _ |- _ => clear H end; cbn [sa_size sa_cap sa_buf sa_heap sa_k Z.b2z]; lia.
Local Ltac arr_open HM :=
  cont_open HM OK CX;
  let M := match goal with M : munch _ _ _ |- _ => M end in rewrite HR0 in M; cbn [app] in M;
  let H := match goal with H : arr_frp _ _ _ _ _ |- _ => H end in
  let FRl := fresh "FRl" in let FRs := fresh "FRs" in destruct H as [FRl FRs]; unfold ca_savedA in FRs.

Local Ltac arr_close HM FRl FRs :=
  let HFRP := fresh "HFRP" in
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of FRl with rw_cells _ _ _ [C8 ?v0; C8 ?v8; _] => assert (HFRP : AFRP v0 v8 mm) by (split; [exact FRl| exact FRs]) end end;
  match goal with HREF : CREFA _ ?E' ?C' _ ?st ?mr, M : munch _ ?mr _ |- _ => apply (munch_conWA0 E' C' st _ _ HR0) in M end;
  cont_close HM HFRP OK CX; clear FRl FRs.

Local Ltac muc := match goal with HREF : CREFA _ ?E' ?C' _ ?st ?mr, M : munch _ ?mr ?m |- _ => constr:(munch_conWA0 E' C' st mr m HR0 M) end.

Notation AST pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xt3 xt4 xt5 xt6 F fc m :=
  (MS (mkR xra (wz (ci_b C)) (ci_gp C) (wz TPV_A) xt0 xt1 xt2 (wz (pa_SB E + 72)) (wz (pa_SB E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           xs2 (wz (pa_SB E + 64)) (wz (pa_DOC E)) xs5 xs6 (wz 2147450880) (wz ((pa_SB E + 72) / 8 + 2147450880)) (wz ((pa_SB E + 80) / 8 + 2147450880))
           (wz ((pa_SB E + 64) / 8 + 2147450880)) (wz (SHDOCA E)) xt3 xt4 xt5 xt6)
      F (wz pc) fc None m (seg_rom asegs)).

Lemma arr_close_byteA : forall (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32) (v0 v8 : word)
    (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xt3 xt4 xt5 xt6 : word),
  CERMA RT E C (AFRP v0 v8) Σ st m -> frm0 fc -> 1 <= sa_size st -> sa_size st <= 41 * e + 6 * ci_c' C + 2 ->
  CCREDA RT E C Σ 0 st ->
  aevt Σ K (AST 0xb5fdc xra xt0 xt1 xt2 (wz (sa_buf st + (sa_size st - 1))) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xt3 xt4 xt5 xt6 F fc m).
Proof using AF MST OK CX HB128 HR0 HFR0 KFIN.
  intros Σ st m F fc v0 v8 xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xt3 xt4 xt5 xt6 HSM FRM SZ1 ACC CR.
  pose proof (cc_e E D C CX) as (I1 & IE & EN). pose proof (cc_c' E D C CX) as (CC1 & CC2). pose proof (cc_sp0 E D C CX) as (W1 & W2).
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf] in *.
  cont_envA OK CX. apply (aevt_evt RT AF PMc MST).
  pose proof HSM as HSM0. pose proof (SBINVA_of_CERMA RT E D C _ Σ _ m OK CX HSM) as INV0. pose proof (pa_live_of_CERMA RT E D C _ Σ _ m CX HSM) as PL0.
  arr_open HSM.
  pose proof (buf_factsC RT AF E D C OK CX Σ _ _ HREF) as (_ & _ & _ & _ & APB). cbn [sa_buf sa_cap] in APB.
  pose proof (APB (buf + (size - 1)) ltac:(clear - SZ1 SZ; lia)) as (A1 & A2 & A3). clear APB.
  assert (A1' : ~ (ci_b C <= buf + (size - 1) < ci_q C)) by (intros H; apply A1; exists (ci_b C), (ci_q C); split; [left; reflexivity| exact H]). clear A1.
  pose proof HREF as (_ & LV & FRx & SP & _).
  assert (EU : bv_unsigned (wz (ci_b C)) = ci_b C) by (apply unsigned_lit; clear - LB QT HB128 LO; lia).

  step. step. pj_store_done.

  do 13 zstep. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let MUc := muc in pose proof (CREFA_munch RT AF E D C Σ _ m mm (size) OK CX HREF MUc WM) as HREF1 end.
  pose proof HREF1 as (ART1 & _ & _ & _ & DR1 & SBSH1 & PU1 & PRES1). unfold sb_sized in DR1, SBSH1, PU1, PRES1. cbn [sa_buf sa_size sa_cap sa_heap sa_k] in PRES1.
  pose proof (stk_release asegs _ _ _ _ ST FRl ltac:(clear - LB; lia)) as ST1. cbn [cells_size csize Nat.add] in ST1. change (Z.of_nat 24) with 24 in ST1.
  pose proof (stk_release asegs _ _ _ _ ST1 FRs ltac:(clear - LB; lia)) as ST2. cbn [cells_size csize Nat.add] in ST2. change (Z.of_nat 104) with 104 in ST2.
  replace (ci_b C + 24 + 104) with (ci_q C) in ST2 by (clear - HB128; lia). replace (ci_b C + 128) with (ci_q C) by (clear - HB128; lia).
  apply evt_done.
  apply (KFIN Σ (mkSbA buf size cap hp kk)); [exact FRM| exact ART1| exact MI| exact ST2| | exact DR1| unfold sb_accA; cbn [sa_size]; clear - ACC; lia| | rewrite FRx; exact HFR0| exact SP
    | unfold CCREDA in CR; clear - CR; lia| exact PRES1].
  - unfold SBINVA. cbn [sa_buf sa_size sa_cap sa_heap sa_k]. split; [exact SV|]. split; [clear - SZ SZ1; lia|].
    split. { destruct (stk_CB asegs _ _ _ BUFS ltac:(clear - R1; lia)) as (bs & HBS). exists bs. replace (buf + cap - buf) with cap in HBS by (clear; lia). exact HBS. }
    split. { destruct (stk_CB asegs _ _ _ INLS ltac:(clear; lia)) as (bs & HBS). exists bs. replace (Z.to_nat (pa_SB E + 64 - pa_SB E)) with 64%nat in HBS by (clear; lia). exact HBS. }
    split; [exact SBSH1| exact PU1].
  - exact (pa_live_eq RT _ _ E _ PL0 eq_refl eq_refl eq_refl).
Qed.

Lemma arr_tailA : forall (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32) (v0 v8 : word)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xt3 xt4 xt5 xt6 : word),
  CERMA RT E C (AFRP v0 v8) Σ st m -> frm0 fc -> sa_size st + 1 <= sa_cap st -> sa_size st + 1 <= 41 * e + 6 * ci_c' C + 2 ->
  CCREDA RT E C Σ 0 st ->
  aevt Σ K (AST 0xb5fa8 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xt3 xt4 xt5 xt6 F fc m).
Proof using AF MST OK CX HB128 HR0 HFR0 KFIN.
  intros Σ st m F fc v0 v8 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xt3 xt4 xt5 xt6 HSM FRM ROOM ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  cont_envA OK CX. apply (aevt_evt RT AF PMc MST). arr_open HSM.
  let MUc := muc in pose proof (shz_sb_muC RT AF E D C OK CX Σ _ _ _ HREF MUc WM) as SHZ.
  pose proof (SHZ (pa_SB E + 64) ltac:(clear; lia)) as RD64. pose proof (SHZ (pa_SB E + 72) ltac:(clear; lia)) as RD72. clear SHZ.

  zstep. shz_norm. zstep. if_false. zstep. shz_norm. zstep. if_false.

  step. step. zstep. zstep. step.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let MUc := muc in pose proof (acc_buf_muC RT AF E D C OK CX Σ _ _ mm HREF MUc WM) as ACCB end.
  cbn [sa_buf sa_cap] in ACCB.
  destruct (acc_read1 _ _ _ (buf + size) ACCB ltac:(clear - ROOM SZ; lia)) as (b & RDB & SOK).
  zstep. pjnorm. zstep. zstep.
  arr_close HSM2 FRl FRs.
  destruct (pj_sh_ok_cases b (buf + size) SOK) as [-> | (kq & -> & K17 & KM)]; [rewrite sxb_z8| rewrite (pj_sxb_small7 kq) by (clear - K17; lia)].
  -
    zstep. if_false. apply evt_done.
    eapply aevt_eq; [| eapply (arr_close_byteA Σ (mkSbA buf (size + 1) cap hp kk) _ F fc v0 v8)]; try eassumption; try pj_st_eq; slia.
  -
    zstep. if_cases Kc; zify_cond Kc; [clear Kc| exfalso; pjnorm_in Kc; clear - Kc K17; lia].
    zstep. pjnorm. rewrite pj_land7 by (clear - R0 SZ; lia). zstep.
    if_cases Kc; zify_cond Kc;
      [clear Kc| exfalso; rewrite !pj_signed_small in Kc by (clear - K17; Z.div_mod_to_equations; lia); clear - Kc K17 KM; lia].
    apply evt_done.
    eapply aevt_eq; [| eapply (arr_close_byteA Σ (mkSbA buf (size + 1) cap hp kk) _ F fc v0 v8)]; try eassumption; try pj_st_eq; slia.
Qed.

Lemma arr_endA : forall (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32) (v0 v8 : word)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xt3 xt4 xt5 xt6 : word),
  CERMA RT E C (AFRP v0 v8) Σ st m -> frm0 fc -> sa_size st + 1 <= 41 * e + 6 * ci_c' C + 2 -> CCREDA RT E C Σ 0 st ->
  aevt Σ K (AST 0xb5f78 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xt3 xt4 xt5 xt6 F fc m).
Proof using AF MST GROW OK CX HB128 HR0 HFR0 KFIN.
  intros Σ st m F fc v0 v8 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xt3 xt4 xt5 xt6 HSM FRM ACC CR.
  pose proof (cctx_out E D C OK CX) as OUTB. pose proof (SBINVA_cap_pos E m _ (SBINVA_of_CERMA RT E D C _ Σ _ m OK CX HSM)) as C64.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  cont_envA OK CX. apply (aevt_evt RT AF PMc MST). arr_open HSM.
  let MUc := muc in pose proof (shz_sb_muC RT AF E D C OK CX Σ _ _ _ HREF MUc WM) as SHZ.
  pose proof (SHZ (pa_SB E + 80) ltac:(clear; lia)) as RD80. pose proof (SHZ (pa_SB E + 72) ltac:(clear; lia)) as RD72. clear SHZ.

  zstep. shz_norm. zstep. if_false. zstep. shz_norm. zstep. if_false.

  step. step. step. zstep. step.
  if_cases Kr; zify_cond Kr; pjnorm_in Kr.
  - arr_close HSM2 FRl FRs. apply evt_done.
    eapply aevt_eq; [| eapply (arr_tailA Σ (mkSbA buf size cap hp kk) _ F fc v0 v8)]; try eassumption; try pj_st_eq; slia.
  -
    zstep. pjnorm. step. step.
    arr_close HSM3 FRl FRs. apply evt_done.
    eapply (cont_growA RT AF PMc GROW E D C (AFRP v0 v8) Σ (mkSbA buf size cap hp kk) _ K (2 * cap) 0 0xb5fa8);
      [exact OK| exact CX| apply arr_frp_local; exact HB128| exact HSM3| | exact CR| clear; lia| clear; lia| reflexivity|].
    { eapply (cont_req_ok2A RT E D C _ Σ _ _ OK CX HSM3). cbn [sa_cap]. clear - Kr ACC OUTB. lia. }
    intros Σ' NEW m' F' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CR4.
    eapply (arr_tailA Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW (2 * cap)) m' F' fc v0 v8);
      [exact HSM4| exact FRM| unfold sb_grownA; cbn [sa_size sa_cap]; clear - SZ C64; lia| unfold sb_grownA; cbn [sa_size]; exact ACC| exact CR4].
Qed.

Notation M32 := (wz 4294967295).
Notation MNUM := (wz 67240448).
Notation MCONT := (wz 4294967297).
Definition arr_loop_stmtA (f : nat) : Prop :=
  forall (x cx n : Z) (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
         (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    e - x <= Z.of_nat f -> x < e -> tilesS ELEM x e n cx (ci_c' C) -> 2 <= x -> 0 <= cx ->
    CERMA RT E C (AFRP M32 MCONT) Σ st m -> frm0 fc -> sb_accA st x cx -> CCREDA RT E C Σ (2 * (e - x)) st ->
    aevt Σ K (AST 0xb6044 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz e) (wz x) MNUM xt3 xt4 xt5 xt6 F fc m).

Lemma arr_doneA : forall (cx n : Z) (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32) (v0 v8 : word)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xt3 xt4 xt5 xt6 : word),
  tilesS ELEM e e n cx (ci_c' C) -> CERMA RT E C (AFRP v0 v8) Σ st m -> frm0 fc -> sb_accA st e cx -> CCREDA RT E C Σ 0 st ->
  aevt Σ K (AST 0xb5f78 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xt3 xt4 xt5 xt6 F fc m).
Proof using AF MST GROW OK CX HB128 HR0 HFR0 KFIN.
  intros cx n Σ st m F fc v0 v8 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xt3 xt4 xt5 xt6 Ht HSM FRM ACC CR.
  pose proof (tilesS_diag _ (elemS_lt (pa_T E) (pa_S E) (pa_sn E) ck_any D) _ _ _ _ Ht) as EC.
  unfold sb_accA in ACC.
  eapply arr_endA; [exact HSM| exact FRM| clear - ACC EC; lia| exact CR].
Qed.

Lemma arr_setupA : forall (f : nat), arr_loop_stmtA f ->
  forall (x cx n : Z) (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32) (v0 v8 : word)
         (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xt3 xt4 xt5 xt6 : word),
    e - x <= Z.of_nat f -> x < e -> tilesS ELEM x e n cx (ci_c' C) -> 2 <= x -> 0 <= cx ->
    CERMA RT E C (AFRP v0 v8) Σ st m -> frm0 fc -> sb_accA st x cx -> CCREDA RT E C Σ (2 * (e - x)) st ->
    aevt Σ K (AST 0xb6020 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz e) (wz x) xs6 xt3 xt4 xt5 xt6 F fc m).
Proof using AF MST OK CX HB128 HR0.
  intros f KL x cx n Σ st m F fc v0 v8 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xt3 xt4 xt5 xt6 HF0 HXE Ht HX HCX HSM FRM ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  cont_envA OK CX. apply (aevt_evt RT AF PMc MST). arr_open HSM.

  step. step. step. zstep. lstep. zstep. zstep. zstep. lstep.
  arr_close HSM2 FRl FRs. apply evt_done.
  eapply aevt_eq; [| eapply (KL x cx n Σ (mkSbA buf size cap hp kk) _ F fc)]; try eassumption; try pj_st_eq; slia.
Qed.

Lemma arr_itemA : forall x x' cx cx', ELEM x x' cx cx' -> 1 <= x -> x' <= e ->
  0 <= pa_T E x < 2^64 /\ ae_next (pa_T E x) x x' /\ x < x' /\ cx <= cx'.
Proof using OK CX.
  intros x x' cx cx' HEL HX HXE. pose proof (ok_wfS E OK) as (_ & SN & _). pose proof (pa_n_32 E OK) as N32. pose proof (cc_e E D C CX) as (_ & _ & EN).
  split; [eapply (elemS_word _ _ _ SN); [exact HEL| clear - HX; lia| clear - HXE EN N32; lia]|].
  split; [eapply (elemS_after _ _ _ SN); [exact HEL| clear - HX; lia| clear - HXE EN N32; lia]|].
  split; [exact (elemS_lt _ _ _ _ _ _ _ _ _ HEL)| exact (proj1 (elemS_cur _ _ _ _ _ _ _ _ _ HEL))].
Qed.

Lemma arr_after_loopA : forall (f : nat), arr_loop_stmtA f ->
  forall (x x' cx cx' n : Z) (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
         (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    e - x' <= Z.of_nat f -> ELEM x x' cx cx' -> x' <= e -> tilesS ELEM x' e n cx' (ci_c' C) -> 2 <= x -> 0 <= cx ->
    CERMA RT E C (AFRP M32 MCONT) Σ st m -> frm0 fc -> sb_accA st x' cx' -> CCREDA RT E C Σ (2 * (e - x')) st ->
    aevt Σ K (AST 0xb60c0 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz e) (wz x) MNUM xt3 xt4 xt5 xt6 F fc m).
Proof using AF MST GROW OK CX HB128 HR0 HFR0 KFIN.
  intros f KL x x' cx cx' n Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HF0 HEL HXE Ht HX HCX HSM FRM ACC CR.
  pose proof (arr_itemA x x' cx cx' HEL ltac:(clear - HX; lia) HXE) as (WR & CL & LT & CUR). unfold ae_next in CL.
  pose proof (cc_e E D C CX) as (I1 & IE & EN).
  assert (NEXT : x' <> e -> forall yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6,
    aevt Σ K (AST 0xb6044 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 (wz e) (wz x') MNUM yt3 yt4 yt5 yt6 F fc m)).
  { intros NE; intros. eapply (KL x' cx' n Σ st m F fc); try eassumption; clear - HF0 NE HXE LT HX CUR HCX; lia. }
  assert (DONE : x' = e -> forall yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys6 yt3 yt4 yt5 yt6,
    aevt Σ K (AST 0xb5f78 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 (wz e) (wz x') ys6 yt3 yt4 yt5 yt6 F fc m)).
  { intros EE; intros. rewrite EE in Ht, ACC. eapply (arr_doneA cx' n Σ st m F fc); try eassumption. eapply CCREDA_le; [exact CR| clear - EE; lia]. }
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  cont_envA OK CX. apply (aevt_evt RT AF PMc MST). arr_open HSM.
  let MUc := muc in
  pose proof (doc_cells_muC RT AF E D C OK CX _ _ _ _ HREF MUc WM) as DOCC;
  pose proof (shz_doc_muC RT AF E D C OK CX _ _ _ _ HREF MUc WM (pa_DOC E) ltac:(clear; lia)) as RDD;
  pose proof (shz_tape_muC RT AF E D C OK CX _ _ _ _ HREF MUc WM (pa_TAPE E + 8 * x) ltac:(clear - HX HXE LT EN; lia)) as RDW;
  pose proof (tape_read_muC RT AF E D C OK CX _ _ _ _ x HREF MUc WM ltac:(clear - HX HXE LT EN; lia)) as RDT.
  set (w := pa_T E x) in *. set (t := ttype w) in *.

  zstep. shz_norm. zstep. if_false. step. zstep. zstep. pjnorm. zstep. zstep. pjnorm. zstep. shz_norm. zstep. if_false. step.

  zstep. pjnorm. rewrite shr56_ttype. fold t. zstep. step. step.
  arr_close HSM2 FRl FRs.
  if_cases K1; zify_cond K1; [assert (K1' : 32 < ae_u t) by exact K1| assert (K1' : ae_u t <= 32) by exact K1]; clear K1; rename K1' into K1.
  -
    assert (EX : x' = x + 1) by (clear - CL K1; lia).
    zstep. rewrite <- EX. step.
    if_cases KE; zify_cond KE; pjnorm_in KE; [apply evt_done; apply NEXT; clear - KE; lia| step; apply evt_done; apply DONE; clear - KE; lia].
  -
    zstep. zstep. step.
    if_cases K2; zify_cond K2; [assert (K2' : ae_num t = 0) by exact K2| assert (K2' : ae_num t <> 0) by exact K2]; clear K2; rename K2' into K2.
    +
      arr_open HSM2. step. zstep. zstep. step. arr_close HSM3 FRl FRs.
      if_cases K3; zify_cond K3; [assert (K3' : ae_cont t = 0) by exact K3| assert (K3' : ae_cont t <> 0) by exact K3]; clear K3; rename K3' into K3.
      *
        assert (EX : x' = x + 1) by (clear - CL K1 K2 K3; lia).
        zstep. rewrite <- EX. step.
        if_cases KE; zify_cond KE; pjnorm_in KE; [apply evt_done; apply NEXT; clear - KE; lia| step; apply evt_done; apply DONE; clear - KE; lia].
      *
        assert (EX : x' = Z.land w 4294967295) by (clear - CL K1 K2 K3; lia).
        arr_open HSM3. step. zstep. rewrite <- EX. arr_close HSM4 FRl FRs. step.
        if_cases KE; zify_cond KE; pjnorm_in KE; [apply evt_done; apply NEXT; clear - KE; lia| step; apply evt_done; apply DONE; clear - KE; lia].
    +
      assert (EX : x' = x + 2) by (clear - CL K1 K2; lia).
      zstep. rewrite <- EX. step.
      if_cases KE; zify_cond KE; pjnorm_in KE; [apply evt_done; apply NEXT; clear - KE; lia| step; apply evt_done; apply DONE; clear - KE; lia].
Qed.

Lemma arr_after_firstA : forall (f : nat), arr_loop_stmtA f ->
  forall (x x' cx cx' n : Z) (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32) (v0 v8 : word)
         (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    e - x' <= Z.of_nat f -> ELEM x x' cx cx' -> x' <= e -> tilesS ELEM x' e n cx' (ci_c' C) -> 2 <= x -> 0 <= cx ->
    CERMA RT E C (AFRP v0 v8) Σ st m -> frm0 fc -> sb_accA st x' cx' -> CCREDA RT E C Σ (2 * (e - x')) st ->
    aevt Σ K (AST 0xb5ef0 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz e) (wz (x - 1)) (wz x) xt3 xt4 xt5 xt6 F fc m).
Proof using AF MST GROW OK CX HB128 HR0 HFR0 KFIN.
  intros f KL x x' cx cx' n Σ st m F fc v0 v8 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HF0 HEL HXE Ht HX HCX HSM FRM ACC CR.
  pose proof (arr_itemA x x' cx cx' HEL ltac:(clear - HX; lia) HXE) as (WR & CL & LT & CUR). unfold ae_next in CL.
  pose proof (cc_e E D C CX) as (I1 & IE & EN).
  assert (NEXT : x' <> e -> forall yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys6 yt3 yt4 yt5 yt6,
    aevt Σ K (AST 0xb6020 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 (wz e) (wz x') ys6 yt3 yt4 yt5 yt6 F fc m)).
  { intros NE; intros. eapply (arr_setupA f KL x' cx' n Σ st m F fc); try eassumption; clear - HF0 NE HXE LT HX CUR HCX; lia. }
  assert (DONE : x' = e -> forall yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys6 yt3 yt4 yt5 yt6,
    aevt Σ K (AST 0xb5f78 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 (wz e) (wz x') ys6 yt3 yt4 yt5 yt6 F fc m)).
  { intros EE; intros. rewrite EE in Ht, ACC. eapply (arr_doneA cx' n Σ st m F fc); try eassumption. eapply CCREDA_le; [exact CR| clear - EE; lia]. }
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  cont_envA OK CX. apply (aevt_evt RT AF PMc MST). arr_open HSM.
  let MUc := muc in
  pose proof (doc_cells_muC RT AF E D C OK CX _ _ _ _ HREF MUc WM) as DOCC;
  pose proof (shz_doc_muC RT AF E D C OK CX _ _ _ _ HREF MUc WM (pa_DOC E) ltac:(clear; lia)) as RDD;
  pose proof (shz_tape_muC RT AF E D C OK CX _ _ _ _ HREF MUc WM (pa_TAPE E + 8 * x) ltac:(clear - HX HXE LT EN; lia)) as RDW;
  pose proof (tape_read_muC RT AF E D C OK CX _ _ _ _ x HREF MUc WM ltac:(clear - HX HXE LT EN; lia)) as RDT.
  set (w := pa_T E x) in *. set (t := ttype w) in *.

  zstep. shz_norm. zstep. if_false. step. zstep. zstep. pjnorm. zstep. zstep. pjnorm. zstep. shz_norm. zstep. if_false. step.

  zstep. pjnorm. rewrite shr56_ttype. fold t. zstep. step. step.
  arr_close HSM2 FRl FRs.
  if_cases K1; zify_cond K1; [assert (K1' : 32 < ae_u t) by exact K1| assert (K1' : ae_u t <= 32) by exact K1]; clear K1; rename K1' into K1.
  -
    assert (EX : x' = x - 1 + 2) by (clear - CL K1; lia).
    zstep. rewrite <- EX. step.
    if_cases KE; zify_cond KE; pjnorm_in KE; [apply evt_done; apply NEXT; clear - KE; lia| apply evt_done; apply DONE; clear - KE; lia].
  -
    step. zstep. zstep. zstep. step.
    if_cases K2; zify_cond K2; [assert (K2' : ae_num t = 0) by exact K2| assert (K2' : ae_num t <> 0) by exact K2]; clear K2; rename K2' into K2.
    +
      step. zstep. zstep. zstep. zstep. step.
      if_cases K3; zify_cond K3; [assert (K3' : ae_cont t = 0) by exact K3| assert (K3' : ae_cont t <> 0) by exact K3]; clear K3; rename K3' into K3.
      * assert (EX : x' = x - 1 + 2) by (clear - CL K1 K2 K3; lia).
        zstep. rewrite <- EX. step.
        if_cases KE; zify_cond KE; pjnorm_in KE; [apply evt_done; apply NEXT; clear - KE; lia| apply evt_done; apply DONE; clear - KE; lia].
      *
        assert (EX : x' = Z.land w 4294967295) by (clear - CL K1 K2 K3; lia).
        zstep. zstep. rewrite <- EX. step.
        if_cases KE; zify_cond KE; pjnorm_in KE; [apply evt_done; apply DONE; clear - KE; lia| step; apply evt_done; apply NEXT; clear - KE; lia].
    +
      assert (EX : x' = x - 1 + 3) by (clear - CL K1 K2; lia).
      zstep. rewrite <- EX. step.
      if_cases KE; zify_cond KE; pjnorm_in KE; [apply evt_done; apply DONE; clear - KE; lia| step; apply evt_done; apply NEXT; clear - KE; lia].
Qed.

Lemma arr_loopA : forall f, arr_loop_stmtA f.
Proof using AF FDO MST GROW OK CX HB128 HR0 HFR0 SER KFIN.
  induction f as [|f IH]; unfold arr_loop_stmtA;
    intros x cx n Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HF0 HXE Ht HX HCX HSM FRM ACC CR; [exfalso; clear - HF0 HXE; lia|].
  pose proof (cc_e E D C CX) as (I1 & IE & EN). pose proof (cc_c' E D C CX) as (CC1 & CC2). pose proof (cctx_out E D C OK CX) as OUTB.
  pose proof (SBINVA_cap_pos E m _ (SBINVA_of_CERMA RT E D C _ Σ _ m OK CX HSM)) as C64.
  destruct (tilesS_next _ (elemS_lt (pa_T E) (pa_S E) (pa_sn E) ck_any D) _ _ _ _ _ Ht ltac:(clear - HXE; lia)) as (x' & cx' & HEL & HXE' & Ht').
  pose proof (arr_itemA x x' cx cx' HEL ltac:(clear - HX; lia) HXE') as (_ & _ & LT & CUR).
  pose proof (tilesS_cur _ (pa_sn E) (elemS_cur (pa_T E) (pa_S E) (pa_sn E) ck_any D) _ _ _ _ _ Ht') as (CUR' & _).
  unfold sb_accA in ACC.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.

  assert (TAIL : forall (Σ5 : rts RT) (st5 : sbA) (m5 : mem) (F5 : bvmap 5 word) (yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
    CERMA RT E C (AFRP M32 MCONT) Σ5 st5 m5 -> sa_size st5 = size -> size + 1 <= sa_cap st5 -> CCREDA RT E C Σ5 (2 * (e - x)) st5 ->
    aevt Σ5 K (AST 0xb6074 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 (wz e) (wz x) MNUM yt3 yt4 yt5 yt6 F5 fc m5)).
  { intros Σ5 st5 m5 F5 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM5 ESZ ROOM CR5.
    destruct st5 as [buf5 size5 cap5 hp5 kk5]. cbn [sa_size sa_buf sa_cap] in ESZ, ROOM, CR5. subst size5.
    cont_envA OK CX. apply (aevt_evt RT AF PMc MST). arr_open HSM5.
    let MUc := muc in pose proof (shz_sb_muC RT AF E D C OK CX _ _ _ _ HREF MUc WM) as SHZ.
    pose proof (SHZ (pa_SB E + 64) ltac:(clear; lia)) as RD64. pose proof (SHZ (pa_SB E + 72) ltac:(clear; lia)) as RD72. clear SHZ.

    zstep. shz_norm. zstep. if_false. zstep. shz_norm. zstep. if_false.
    step. step. zstep. zstep. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let MUc := muc in pose proof (acc_buf_muC RT AF E D C OK CX _ _ _ mm HREF MUc WM) as ACCB end.
    pose proof (buf_factsC RT AF E D C OK CX _ _ _ HREF) as (_ & _ & _ & _ & APB). cbn [sa_buf sa_cap] in ACCB, APB.
    pose proof (APB (buf5 + size) ltac:(clear - ROOM SZ; lia)) as (A1 & A2 & A3). clear APB.
    assert (A1' : ~ (ci_b C <= buf5 + size < ci_q C)) by (intros H; apply A1; exists (ci_b C), (ci_q C); split; [left; reflexivity| exact H]). clear A1.
    destruct (acc_read1 _ _ _ (buf5 + size) ACCB ltac:(clear - ROOM SZ; lia)) as (b & RDB & SOK).

    zstep. pjnorm. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (JOIN : forall ya1' ya2',
      evt asegs (fun c5 => aevt Σ5 K c5)
          (AST 0xb60a8 yra yt0 yt1 yt2 (wz (buf5 + size)) ya1' ya2' ya3 ya4 ya5 ya6 ya7 (wz e) (wz x) MNUM yt3 yt4 yt5 yt6 F5 fc mm)) end.
    { intros ya1' ya2'. step. step. pj_store_done. step. step. step. step.
      arr_close HSM6 FRl FRs. apply evt_done.
      eapply (cont_call_serA RT AF PMc FDO MST E D C (AFRP M32 MCONT) Σ5 (mkSbA buf5 (size + 1) cap5 hp5 kk5) _ K x x' cx cx' (2 * (e - x)) 0xb60c0);
        [exact SER| exact OK| exact CX| apply arr_frp_local; exact HB128| exact HSM6| exact FRM| exact HEL| clear - HX; lia| clear - HXE' EN; lia| exact HCX
        | clear - CUR' CC2; lia| unfold sb_acc1A; cbn [sa_size]; clear - ACC; lia| exact CR5| clear - HXE'; lia| clear; lia| reflexivity|].
      intros Σ' st' m' F' fc' zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 FRM' HSM' ACC' CR'.
      eapply (arr_after_loopA f IH x x' cx cx' (n - 1) Σ' st' m' F' fc'); try eassumption; [clear - HF0 LT; lia| eapply CCREDA_le; [exact CR'| clear; lia]]. }
    destruct (pj_sh_ok_cases b (buf5 + size) SOK) as [-> | (kq & -> & K17 & KM)]; [rewrite sxb_z8| rewrite (pj_sxb_small7 kq) by (clear - K17; lia)].
    - zstep. if_false. apply JOIN.
    - zstep. if_cases Kc; zify_cond Kc; [clear Kc| exfalso; pjnorm_in Kc; clear - Kc K17; lia].
      zstep. pjnorm. rewrite pj_land7 by (clear - R0 SZ; lia). zstep.
      if_cases Kc; zify_cond Kc;
        [clear Kc| exfalso; rewrite !pj_signed_small in Kc by (clear - K17; Z.div_mod_to_equations; lia); clear - Kc K17 KM; lia].
      apply JOIN. }
  cont_envA OK CX. apply (aevt_evt RT AF PMc MST). arr_open HSM.
  let MUc := muc in pose proof (shz_sb_muC RT AF E D C OK CX Σ _ _ _ HREF MUc WM) as SHZ.
  pose proof (SHZ (pa_SB E + 80) ltac:(clear; lia)) as RD80. pose proof (SHZ (pa_SB E + 72) ltac:(clear; lia)) as RD72. clear SHZ.

  zstep. shz_norm. zstep. if_false. zstep. shz_norm. zstep. if_false.
  step. step. step. zstep. step.
  if_cases Kr; zify_cond Kr; pjnorm_in Kr.
  - arr_close HSM2 FRl FRs. apply evt_done. eapply (TAIL Σ (mkSbA buf size cap hp kk)); [exact HSM2| reflexivity| cbn [sa_cap]; clear - Kr; lia| exact CR].
  -
    zstep. pjnorm. step. step.
    arr_close HSM3 FRl FRs. apply evt_done.
    eapply (cont_growA RT AF PMc GROW E D C (AFRP M32 MCONT) Σ (mkSbA buf size cap hp kk) _ K (2 * cap) (2 * (e - x)) 0xb6074);
      [exact OK| exact CX| apply arr_frp_local; exact HB128| exact HSM3| | exact CR| clear - HXE; lia| clear; lia| reflexivity|].
    { eapply (cont_req_ok2A RT E D C _ Σ _ _ OK CX HSM3). cbn [sa_cap]. clear - Kr ACC OUTB LT HXE' CUR CUR' CC2 HX HCX EN. lia. }
    intros Σ' NEW m' F' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CR4.
    eapply (TAIL Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW (2 * cap)) m' F'); [exact HSM4| reflexivity| unfold sb_grownA; cbn [sa_cap]; clear - SZ C64; lia| exact CR4].
Qed.

Lemma arr_firstA : forall (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32) (v0 v8 : word)
    (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs6 xs11 xt3 xt4 xt5 xt6 : word),
  CERMA RT E C (AFRP v0 v8) Σ st m -> frm0 fc -> 1 <= sa_size st -> sa_size st <= 41 * (ci_i C - 1) + 6 * c0 + 4 ->
  CCREDA RT E C Σ (2 * (e - ci_i C)) st ->
  aevt Σ K (MS (mkR xra (wz (ci_b C)) (ci_gp C) (wz TPV_A) xt0 xt1 xt2 (wz (pa_SB E + 72)) (wz (pa_SB E)) (wz (sa_buf st + (sa_size st - 1))) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                    xs2 (wz (pa_SB E + 64)) (wz (pa_DOC E)) (wz (ci_i C)) xs6 (wz 2147450880) (wz ((pa_SB E + 72) / 8 + 2147450880))
                    (wz ((pa_SB E + 80) / 8 + 2147450880)) (wz ((pa_SB E + 64) / 8 + 2147450880)) xs11 xt3 xt4 xt5 xt6)
               F (wz 0xb5e48) fc None m (seg_rom asegs)).
Proof using AF FDO MST GROW OK CX HB128 HR0 HFR0 SER HTY HNX HT HC0 KFIN.
  intros Σ st m F fc v0 v8 xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs6 xs11 xt3 xt4 xt5 xt6 HSM FRM SZ1 ACC CR.
  pose proof (cc_e E D C CX) as (I1 & IE & EN). pose proof (cc_c' E D C CX) as (CC1 & CC2).
  pose proof (tilesS_le _ (elemS_lt (pa_T E) (pa_S E) (pa_sn E) ck_any D) _ _ _ _ _ HT) as (LIE & _).
  pose proof (tilesS_cur _ (pa_sn E) (elemS_cur (pa_T E) (pa_S E) (pa_sn E) ck_any D) _ _ _ _ _ HT) as (LCC & _).
  assert (WR : 0 <= pa_T E (ci_i C) < 2^64) by (eapply ttype_range; [exact HTY| unfold t_arr; clear; lia]).
  pose proof HTY as HTY'. unfold SjTape.ty, t_arr in HTY'.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  cont_envA OK CX. apply (aevt_evt RT AF PMc MST). arr_open HSM.
  pose proof (buf_factsC RT AF E D C OK CX Σ _ _ HREF) as (_ & _ & _ & _ & APB). cbn [sa_buf sa_cap] in APB.
  pose proof (APB (buf + (size - 1)) ltac:(clear - SZ1 SZ; lia)) as (A1 & A2 & A3). clear APB.
  assert (A1' : ~ (ci_b C <= buf + (size - 1) < ci_q C)) by (intros H; apply A1; exists (ci_b C), (ci_q C); split; [left; reflexivity| exact H]). clear A1.

  step. step. pj_store_done.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let MUc := muc in
    pose proof (doc_cells_muC RT AF E D C OK CX _ _ _ mm HREF MUc WM) as DOCC;
    pose proof (shz_doc_muC RT AF E D C OK CX _ _ _ mm HREF MUc WM (pa_DOC E) ltac:(clear; lia)) as RDD;
    pose proof (shz_tape_muC RT AF E D C OK CX _ _ _ mm HREF MUc WM (pa_TAPE E + 8 * ci_i C) ltac:(clear - I1 IE EN; lia)) as RDW;
    pose proof (tape_read_muC RT AF E D C OK CX _ _ _ mm (ci_i C) HREF MUc WM ltac:(clear - I1 IE EN; lia)) as RDT end.
  set (w := pa_T E (ci_i C)) in *.

  zstep. pjnorm. zstep. zstep. shz_norm. zstep. if_false. step. zstep. pjnorm. zstep. zstep. pjnorm. zstep. zstep. shz_norm. zstep. if_false. step.

  zstep. zstep. pjnorm. rewrite shr56_ttype, HTY'. zstep. step. step. step.
  if_cases K1; zify_cond K1; [exfalso; cbn in K1; clear - K1; lia| clear K1].

  step. zstep. zstep. zstep. step.
  if_cases K2; zify_cond K2; [clear K2| exfalso; cbn in K2; clear - K2; lia].

  step. zstep. zstep. zstep. zstep. step. step.
  if_cases K3; zify_cond K3; [exfalso; cbn in K3; clear - K3; lia| clear K3].

  zstep. zstep. rewrite land_low32, HNX.
  zstep. arr_close HSM2 FRl FRs. step.
  if_cases KE; zify_cond KE; pjnorm_in KE.
  -
    apply evt_done. rewrite <- KE in HT.
    pose proof (tilesS_diag _ (elemS_lt (pa_T E) (pa_S E) (pa_sn E) ck_any D) _ _ _ _ HT) as EC.
    eapply aevt_eq; [| eapply (arr_endA Σ (mkSbA buf size cap hp kk) _ F fc v0 v8)]; try eassumption; try pj_st_eq;
      [cbn [sa_size]; clear - ACC KE EC LCC CC1; lia| eapply CCREDA_le; [exact CR| clear - IE; lia]].
  -
    destruct (tilesS_next _ (elemS_lt (pa_T E) (pa_S E) (pa_sn E) ck_any D) _ _ _ _ _ HT ltac:(clear - KE; lia)) as (x' & cx' & HEL & HXE' & Ht').
    pose proof (arr_itemA (ci_i C + 1) x' c0 cx' HEL ltac:(clear - I1; lia) HXE') as (_ & _ & LT & CUR).
    pose proof (tilesS_cur _ (pa_sn E) (elemS_cur (pa_T E) (pa_S E) (pa_sn E) ck_any D) _ _ _ _ _ Ht') as (CUR' & _).
    step. step. step. step. apply evt_done.
    eapply (cont_call_serA RT AF PMc FDO MST E D C (AFRP v0 v8) Σ (mkSbA buf size cap hp kk) _ K (ci_i C + 1) x' c0 cx' (2 * (e - ci_i C)) 0xb5ef0);
      [exact SER| exact OK| exact CX| apply arr_frp_local; exact HB128| exact HSM2| exact FRM| exact HEL| clear - I1; lia| clear - HXE' EN; lia| exact HC0
      | clear - CUR' CC2; lia| unfold sb_acc1A; cbn [sa_size]; clear - ACC; lia| exact CR| clear - HXE'; lia| clear; lia| reflexivity|].
    intros Σ' st' m' F' fc' zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 FRM' HSM' ACC' CR'.
    eapply aevt_eq; [| eapply (arr_after_firstA (Z.to_nat (e - x')) (arr_loopA _) (ci_i C + 1) x' c0 cx' (n0 - 1) Σ' st' m' F' fc')]; try eassumption; try pj_st_eq;
      [clear - HXE'; lia| clear - I1; lia| eapply CCREDA_le; [exact CR'| clear; lia]].
Qed.

Lemma arr_headA : forall (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32) (v0 v8 : word)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs6 xs10 xs11 xt3 xt4 xt5 xt6 : word),
  CERMA RT E C (AFRP v0 v8) Σ st m -> frm0 fc -> sa_size st + 1 <= sa_cap st -> sb_acc1A st (ci_i C) c0 -> CCREDA RT E C Σ (2 * (e - ci_i C)) st ->
  aevt Σ K (MS (mkR xra (wz (ci_b C)) (ci_gp C) (wz TPV_A) xt0 xt1 xt2 (wz (pa_SB E + 72)) (wz (pa_SB E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                    xs2 xs3 (wz (pa_DOC E)) (wz (ci_i C)) xs6 (wz 2147450880) (wz ((pa_SB E + 72) / 8 + 2147450880))
                    (wz ((pa_SB E + 80) / 8 + 2147450880)) xs10 xs11 xt3 xt4 xt5 xt6)
               F (wz 0xb5e08) fc None m (seg_rom asegs)).
Proof using AF FDO MST GROW OK CX HB128 HR0 HFR0 SER HTY HNX HT HC0 KFIN.
  intros Σ st m F fc v0 v8 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs6 xs10 xs11 xt3 xt4 xt5 xt6 HSM FRM ROOM ACC CR.
  unfold sb_acc1A in ACC.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  cont_envA OK CX. apply (aevt_evt RT AF PMc MST). arr_open HSM.
  let MUc := muc in pose proof (shz_sb_muC RT AF E D C OK CX Σ _ _ _ HREF MUc WM) as SHZ.
  pose proof (SHZ (pa_SB E + 64) ltac:(clear; lia)) as RD64. pose proof (SHZ (pa_SB E + 72) ltac:(clear; lia)) as RD72. clear SHZ.

  zstep. zstep. pjnorm. zstep. zstep. shz_norm. zstep. if_false. zstep. shz_norm. zstep. if_false.

  step. step. zstep. zstep. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let MUc := muc in pose proof (acc_buf_muC RT AF E D C OK CX Σ _ _ mm HREF MUc WM) as ACCB end.
  cbn [sa_buf sa_cap] in ACCB.
  destruct (acc_read1 _ _ _ (buf + size) ACCB ltac:(clear - ROOM SZ; lia)) as (b & RDB & SOK).

  zstep. pjnorm. zstep. zstep.
  arr_close HSM2 FRl FRs.
  destruct (pj_sh_ok_cases b (buf + size) SOK) as [-> | (kq & -> & K17 & KM)]; [rewrite sxb_z8| rewrite (pj_sxb_small7 kq) by (clear - K17; lia)].
  - zstep. if_false. apply evt_done.
    eapply aevt_eq; [| eapply (arr_firstA Σ (mkSbA buf (size + 1) cap hp kk) _ F fc v0 v8)]; try eassumption; try pj_st_eq; slia.
  -
    zstep. if_cases Kc; zify_cond Kc; [clear Kc| exfalso; pjnorm_in Kc; clear - Kc K17; lia].
    zstep. pjnorm. rewrite pj_land7 by (clear - R0 SZ; lia). zstep.
    if_cases Kc; zify_cond Kc;
      [clear Kc| exfalso; rewrite !pj_signed_small in Kc by (clear - K17; Z.div_mod_to_equations; lia); clear - Kc K17 KM; lia].
    apply evt_done.
    eapply aevt_eq; [| eapply (arr_firstA Σ (mkSbA buf (size + 1) cap hp kk) _ F fc v0 v8)]; try eassumption; try pj_st_eq; slia.
Qed.

Lemma arr_entryA : forall (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  pa_live RT Σ E st -> SBINVA E m st -> DOCREPA E m ->
  ART RT Σ m -> mem_inv asegs m -> stk asegs m (pa_lo E) (ci_q C) -> frm0 fc ->
  rt_frames RT Σ = ci_fr0 C -> rt_sp0 RT Σ = ci_sp0 C -> rt_pres_fp (pa_L E) (ci_fr0 C) (ci_q C) [(pa_SB E, pa_SB E + 88)] (ci_m0 C) m ->
  sb_acc1A st (ci_i C) c0 -> CCREDA RT E C Σ (2 * (e - ci_i C)) st ->
  aevt Σ K (MS (mkR (ci_ra C) (wz (ci_q C)) (ci_gp C) (wz TPV_A) t0 t1 t2 (ci_s0 C) (ci_s1 C) (wz (pa_SB E)) (wz (pa_DOC E)) (wz (ci_i C)) a3 a4 a5 a6 a7
                    (ci_s2 C) (ci_s3 C) (ci_s4 C) (ci_s5 C) (ci_s6 C) (ci_s7 C) (ci_s8 C) (ci_s9 C) (ci_s10 C) (ci_s11 C) t3 t4 t5 t6)
               F (wz PJ_APPEND_ARR_A) fc None m (seg_rom asegs)).
Proof using AF FDO MST GROW OK CX HB128 HR0 HFR0 SER HTY HNX HT HC0 KFIN.
  intros Σ st m F fc t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 PL INV DR ART0 MI ST0 FRM FRS SP0 PRES0 ACC CR.
  pose proof (cctx_out E D C OK CX) as OUTB. pose proof (SBINVA_cap_pos E _ _ INV) as C64.
  pose proof (af_client_consts RT AF Σ _ ART0) as (G1 & G2 & G3 & G4).
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB in G1, G2, G3, G4.
  pose proof INV as (SV & SZ & (bs & BUF) & (ji & INL) & SBSH & PK & PH).
  assert (BUFS : stk asegs m (sa_buf st) (sa_buf st + sa_cap st)).
  { pose proof (stk_of_rw_cells asegs _ _ _ BUF) as S. cbn [cells_size csize Nat.add] in S. rewrite Nat.add_0_r, Z2Nat.id in S by (clear - SZ; lia). exact S. }
  assert (INLS : stk asegs m (pa_SB E) (pa_SB E + 64)).
  { pose proof (stk_of_rw_cells asegs _ _ _ INL) as S. cbn [cells_size csize Nat.add] in S. exact S. }
  clear BUF INL bs ji.
  assert (HREF : CREFA RT E C Σ st m).
  { split; [exact ART0|]. split; [exact (proj1 PL)|]. split; [rewrite HFR0; exact FRS|]. split; [exact SP0|]. split; [exact DR|].
    split; [exact SBSH|]. split; [exact (conj PK PH)| exact PRES0]. }
  pose proof (sb_pureA_ranges E st OK (conj PK PH)) as (R0 & R1 & _ & R3). pose proof (sb_pureA_below E st OK (conj PK PH)) as BL.
  lazymatch type of R3 with ?T => change (boxP T) in R3 end.
  cont_envA OK CX.

  destruct (stk_split asegs _ _ (ci_b C) _ ST0 ltac:(clear - LB BQ; lia)) as [ST STF].
  destruct (stk_split asegs _ _ (ci_b C + 24) _ STF ltac:(clear - BQ; lia)) as [STl STs].
  destruct (stk_CB asegs _ _ _ STl ltac:(clear; lia)) as (jl & FRl). replace (Z.to_nat (ci_b C + 24 - ci_b C)) with 24%nat in FRl by (clear; lia).
  apply (rw_cells_split_CB asegs _ _ [] 24 _ [] [8; 8; 8]%nat) in FRl; [| reflexivity]. cbn [mk_CB_cells app] in FRl.
  repeat match type of FRl with context [CB ?k ?tt] => lazymatch tt with firstn _ _ => idtac end; let j := fresh "j" in set (j := tt) in FRl; clearbody j end.
  destruct (stk_CB asegs _ _ _ STs ltac:(clear - HB128; lia)) as (js & FRs). replace (Z.to_nat (ci_q C - (ci_b C + 24))) with 104%nat in FRs by (clear - HB128; lia).
  apply (rw_cells_split_CB asegs _ _ [] 104 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRs; [| reflexivity]. cbn [mk_CB_cells app] in FRs.
  repeat match type of FRs with context [CB ?k ?tt] => lazymatch tt with firstn _ _ => idtac end; let j := fresh "j" in set (j := tt) in FRs; clearbody j end.
  clear STF STl STs jl js.
  pose proof (munch_refl [(ci_b C, ci_q C); (sa_buf st, sa_buf st + sa_cap st); (pa_SB E, pa_SB E + 88)] m) as MU.
  pose proof (wmono_refl asegs m) as WM. clear SBSH PK PH DR.
  unfold sb_acc1A in ACC.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap sa_heap sa_k] in *.
  assert (EU : bv_unsigned (wz (ci_q C)) = ci_q C) by (apply unsigned_lit; clear - LB BQ LO QT; lia).
  apply (aevt_evt RT AF PMc MST). unfold PJ_APPEND_ARR_A.

  zstep. replace (ci_q C + -128) with (ci_b C) by (clear - HB128; lia).

  do 13 step.

  step. step. step. step. step. zstep. step.

  let MUc := muc in pose proof (shz_sb_muC RT AF E D C OK CX Σ _ _ _ HREF MUc WM) as SHZ.
  pose proof (SHZ (pa_SB E + 80) ltac:(clear; lia)) as RD80. pose proof (SHZ (pa_SB E + 72) ltac:(clear; lia)) as RD72. clear SHZ.
  zstep. pjnorm. zstep. zstep. shz_norm. zstep. if_false. zstep. zstep. pjnorm. zstep. zstep. shz_norm. zstep. if_false.

  step. step. step. zstep. step.
  apply rw_cells_c8ify in FRl. cbn [map c8c Nat.eqb] in FRl.
  if_cases Kr; zify_cond Kr; pjnorm_in Kr.
  - arr_close HSM2 FRl FRs. apply evt_done.
    eapply aevt_eq; [| eapply (arr_headA Σ (mkSbA buf size cap hp kk) _ F fc)]; try eassumption; try pj_st_eq.
  -
    zstep. pjnorm. step. step.
    arr_close HSM3 FRl FRs. apply evt_done.
    lazymatch type of HSM3 with CERMA _ _ _ ?FRP _ _ _ =>
    eapply (cont_growA RT AF PMc GROW E D C FRP Σ (mkSbA buf size cap hp kk) _ K (2 * cap) (2 * (e - ci_i C)) 0xb5e08);
      [exact OK| exact CX| apply arr_frp_local; exact HB128| exact HSM3| | exact CR| pose proof (cc_e E D C CX); clear - H; lia| clear; lia| reflexivity|] end.
    { eapply (cont_req_ok2A RT E D C _ Σ _ _ OK CX HSM3). cbn [sa_cap]. pose proof (cc_e E D C CX). pose proof (cc_c' E D C CX).
      pose proof (tilesS_cur _ (pa_sn E) (elemS_cur (pa_T E) (pa_S E) (pa_sn E) ck_any D) _ _ _ _ _ HT) as (LCC & _). clear - Kr ACC OUTB H H0 LCC HC0. lia. }
    intros Σ' NEW m' F' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CR4.
    eapply (arr_headA Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW (2 * cap)) m' F' fc); [exact HSM4| exact FRM| unfold sb_grownA; cbn [sa_size sa_cap]; clear - SZ C64; lia
      | unfold sb_acc1A, sb_grownA; cbn [sa_size]; exact ACC| exact CR4].
Qed.

End Arr.

Theorem arr_proofA : forall RT, art_facts RT -> forall PMc, grow_cpsA RT PMc -> forall D, ser_cpsA RT PMc D -> cont_cpsA RT PMc false D.
Proof.
  intros RT AF PMc GROW D SER. unfold cont_cpsA.
  intros Σ K E st i e n c c' q ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
         FDO MST OK PL INV DR HTY HNX HTE HT HI HJ HC HC' ACC ART0 MI ST LOQ QT Q16 FRM FR3 FRL LL CR HK.
  unfold itemS in HT.
  pose proof (tilesS_le _ (elemS_lt (pa_T E) (pa_S E) (pa_sn E) ck_any D) _ _ _ _ _ HT) as (LIE & _).
  pose proof (tilesS_cur _ (pa_sn E) (elemS_cur (pa_T E) (pa_S E) (pa_sn E) ck_any D) _ _ _ _ _ HT) as (LCC & LCC2).
  pose proof (pj_psi_nonneg E m st OK INV) as PSI0. pose proof (af_sp0_win RT AF Σ m ART0) as SPW. pose proof PL as (_ & INF4 & SPLO).
  set (C := mkCI q (q - 128) i e c' (rt_credit RT Σ - 2 * (e - i) - pj_psi (pa_len E) st) ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 (rt_frames RT Σ) (rt_frames RT Σ) [] (rt_sp0 RT Σ) m).
  assert (CX : cctxA E D C).
  { unfold cont_needA in LOQ.
    constructor; cbn [C ci_q ci_b ci_i ci_e ci_c' ci_R ci_fr ci_fr0 ci_R_ ci_sp0].
    - clear - Q16. Z.div_mod_to_equations. lia.
    - clear; lia.
    - clear - LOQ; lia.
    - exact QT.
    - split; [exact SPLO| exact SPW].
    - clear - HI LIE HJ; lia.
    - clear - HC HC' LCC; lia.
    - clear - CR PSI0 LIE; lia.
    - exists []. reflexivity.
    - exact INF4.
    - exact FR3.
    - clear - FRL; lia.
    - exact LL.
    - intros a (lo & hi & F0 & _). exfalso. exact F0. }
  change (aevt RT PMc Σ K (MS (mkR (ci_ra C) (Z_to_bv 64 (ci_q C)) (ci_gp C) (Z_to_bv 64 TPV_A) t0 t1 t2 (ci_s0 C) (ci_s1 C)
                                  (Z_to_bv 64 (pa_SB E)) (Z_to_bv 64 (pa_DOC E)) (Z_to_bv 64 (ci_i C)) a3 a4 a5 a6 a7
                                  (ci_s2 C) (ci_s3 C) (ci_s4 C) (ci_s5 C) (ci_s6 C) (ci_s7 C) (ci_s8 C) (ci_s9 C) (ci_s10 C) (ci_s11 C) t3 t4 t5 t6)
                             F (Z_to_bv 64 PJ_APPEND_ARR_A) fc None (ci_m0 C) (seg_rom asegs))).
  eapply (arr_entryA RT AF PMc FDO MST GROW E D C K OK CX ltac:(cbn; clear; lia) eq_refl eq_refl SER n c HTY HNX HT HC);
    [| exact PL| exact INV| exact DR| exact ART0| exact MI| exact ST| exact FRM| reflexivity| reflexivity| intros a _ _; reflexivity| exact ACC
     | unfold CCREDA; cbv delta [C]; cbn [ci_R ci_e ci_i]; clear; lia].

  intros Σ' st' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' FRM' ART' MI' ST' INV' DR' ACC' PL' FRS' SP' CR' PRES'.
  cbn [C ci_q ci_ra ci_gp ci_s0 ci_s1 ci_s2 ci_s3 ci_s4 ci_s5 ci_s6 ci_s7 ci_s8 ci_s9 ci_s10 ci_s11 ci_R ci_fr0 ci_sp0 ci_m0 ci_e ci_c'] in *.
  apply (HK Σ' st'); assumption.
Qed.
