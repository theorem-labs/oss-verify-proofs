(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_rlkit D_libiface D_auxv I_lkit X_aexdefs Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_fzwA Atp_defsA Atp_activewA Atp_pidiA Pj_rtkA Pj_cpsA Pj_defsA Pj_hdefsA Imp_hdefsA Imp_ifaceA Imp_libifaceA Imp_lftoi1A Imp_lftoi2A Imp_lftoi3A Imp_lftoi4A Imp_segdefsA Imp_segA3a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Tail.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PDONE : rts RT -> mem -> Z -> list (Z * Z) -> Prop.
Hypothesis PDT : pdtor_cps RT PDONE.
Hypothesis PDFP : pdone_fpA RT PDONE.
Local Ltac ul := unfold FUZZ_STACK, PID_STACK, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Section WithPM.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Notation aevt := (aevt RT PMc).

Definition imp_fin_k (K : config -> Prop) (Σ0 : rts RT) (v : option Z) (usp lo : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m0 : mem) (cb : Z) : Prop :=
  forall (Σ' : rts RT) (A8 : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m', frm0 fc' ->
    ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' lo usp ->
    rt_pres_fp (rt_live RT Σ0) [] usp IMP_XFP_A m0 m' -> imp_libA (Some A8) m' -> aex6A m' -> (forall B, v = Some B -> A8 = B) ->
    rt_live RT Σ' = xnewA v A8 ++ rt_live RT Σ0 -> rt_frames RT Σ' = [] -> rt_sp0 RT Σ' = rt_sp0 RT Σ0 -> cb <= rt_credit RT Σ' ->
    aevt Σ' K (MS (mkR ra (wz usp) gp tp t0' t1' t2' s0 s1 (wz 0) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc' None m' (seg_rom bsegs)).

Lemma imp_csep : forall (Σ0 Σ : rts RT) (m : mem) (usp sp' f lo : Z),
  ART RT Σ m -> In (f, 5%nat) (rt_frames RT Σ) -> (forall e, In e (rt_live RT Σ0) -> In e (rt_live RT Σ)) -> rt_sp0 RT Σ = rt_sp0 RT Σ0 ->
  impG (rt_sp0 RT Σ0) usp sp' f lo ->
  forall a, aclient (rt_live RT Σ0) [] usp a -> ~ (f <= a < f + 2048) /\ ~ (shad f <= a < shad f + 256) /\ (usp <= a \/ a < lo).
Proof using AF.
  intros Σ0 Σ m usp sp' f lo ARTx INF LVx SPx G a Ha.
  pose proof (af_sp0_range RT AF Σ m ARTx) as SP0R. rewrite SPx in SP0R.
  destruct G as (FSEG & F64 & FTOP & SHB0 & SHT & SEP & LOW & LOR & UT & SPR & SPA & SPW & SPT).
  assert (SHF0 : shad f = f / 8 + SHB) by reflexivity. unfold SHB in SHF0.
  destruct Ha as [H|[H|[H|[H|H]]]].
  - clear - H FTOP SHT LOW LOR SPR. split; [ul|]. split; [ul| left; lia].
  - pose proof (client_static_range _ H) as R. clear - R FSEG SHB0 SP0R LOW. unfold SEGTOP_A, SHB in *. split; [lia|]. split; [lia| right; ul].
  - destruct H as (p & k & Hin & Hr). apply LVx in Hin.
    pose proof (af_frames_range RT AF Σ m f 5%nat ARTx INF) as (_ & _ & _ & FLV). pose proof (FLV p k Hin) as Y1.
    pose proof (proj1 (af_fshadow_apart RT AF Σ m f 5%nat ARTx INF) p k Hin) as Y2.
    pose proof (af_live_range RT AF Σ m p k ARTx Hin) as (_ & Y3 & _). rewrite SPx in Y3.
    change (fs_size 5) with 2048 in *. rewrite SHF0 in *. unfold shad, SHB in Y2. replace ((f + 2048) / 8) with (f / 8 + 256) in Y2 by (Z.div_mod_to_equations; lia).
    clear - Hr Y1 Y2 Y3 LOW. split; [lia|]. split; [lia| right; lia].
  - destruct H as (f9 & k9 & [] & _).
  - destruct H as (f9 & k9 & [] & _).
Qed.

Lemma imp_exitA : forall (Σ0 Σ : rts RT) (K : config -> Prop) (v : option Z) (A8 usp sp' f lo d n : Z)
    (gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word) Fr fc (m0 m : mem) (cb : Z),
  impG (rt_sp0 RT Σ0) usp sp' f lo ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo sp' ->
  rt_frames RT Σ = [(f, 5%nat)] -> rt_live RT Σ = xnewA v A8 ++ rt_live RT Σ0 -> rt_sp0 RT Σ = rt_sp0 RT Σ0 -> cb <= rt_credit RT Σ ->
  In (A8, 8) (rt_live RT Σ) -> (forall B, v = Some B -> A8 = B) ->
  tailB m usp sp' f n d A8 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 ->
  (forall a : word, aclient (rt_live RT Σ0) [] usp (bv_unsigned a) -> outside IMP_XFP_A (bv_unsigned a) -> m a = m0 a) ->
  frm0 fc ->
  imp_fin_k K Σ0 v usp lo cra gp (wz TPV_A) cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 m0 cb ->
  aevt Σ K (dtor_st IMP_PDRET_A (wz IMP_PDRET_A) sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f (f + 160 + 136 * 0 + 8) (-544 + 136 * (3 - 0)) s6 s7 s8 s9 s11
               t3 t4 t5 t6 Fr fc m).
Proof using AF RC FDO MST.
  intros until cb. intros G ARTx MIx STx FRSx LVx SPx CRx A8IN VA TB PRES FRM KFIN.
  pose proof (impG_facts _ _ _ _ _ G) as (F0 & FLO & SH0 & SLO & SLO' & GLO & GLO' & LO64 & LSP & LUSP & SPH & SPH' & SP6 & F8).
  pose proof G as (FSEG & F64 & FTOP & SHB0 & SHT & SEP & LOW & LOR & UT & SPR & SPA & SPW & SPT).
  assert (EU : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  assert (INF : In (f, 5%nat) (rt_frames RT Σ)) by (rewrite FRSx; left; reflexivity).
  assert (LV0x : forall e, In e (rt_live RT Σ0) -> In e (rt_live RT Σ)) by (intros e He; rewrite LVx; apply in_or_app; right; exact He).
  pose proof (imp_csep Σ0 Σ m usp sp' f lo ARTx INF LV0x SPx G) as CSEP.
  assert (SHF0 : shad f = f / 8 + SHB) by reflexivity. unfold SHB in SHF0.
  assert (COK : forall mx, stk bsegs mx lo sp' -> call_ok RT Σ mx (Z_to_bv 64 sp') lo).
  { intros mx STm. unfold call_ok. rewrite EU, SPx. split; [exact STm|]. split; [lia|]. split; [ul|]. split; [ul| clear - SPA; Z.div_mod_to_equations; lia]. }
  assert (ZCL : forall a, tailZ usp sp' f A8 a -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' a).
  { intros a Ha. rewrite FRSx. exact (tailZ_aclient _ usp sp' f A8 a F0 SH0 A8IN ltac:(clear - UT; unfold USTACK_TOP in *; lia) Ha). }

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [apply (imp_walk10c usp sp' f 0 (wz IMP_PDRET_A) gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m); lia|].
  cbv beta. intros ms1 <-. cbn [Z.ltb].

  destruct TB as ((ne & j0 & j8 & j160 & jr & NE & L1 & L2) & STp & SV & (h3 & HD) & SH & LB & AX).
  eapply evt_cut; [apply (imp_walk11a usp sp' f d ne _ _ (wz IMP_PDRET_A) gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6 j0 j8 j160 (Z_to_bv 64 n) Fr fc m);
                   [lia| lia| exact L1| exact MIx]|].
  cbv beta. intros ms2 <-. apply evt_done. unfold dtor_st.

  eapply (aevt_setshadow RT RC PMc FDO MST Σ K 0xf8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc m (shad f + 20) 68 lo);
    [cbn; tauto| reflexivity| reflexivity| lia| | | exact ARTx| exact MIx| exact (COK m STx)|].
  { intros i Hi. exists f, 5%nat. rewrite FRSx. split; [left; reflexivity|]. rewrite SHF0. unfold shad, SHB. change (fs_size 5) with 2048. Z.div_mod_to_equations; lia. }
  { apply (wr_at_sub m (shad f) 156); [| lia| lia| lia].
    eapply (rw_cells_wr_at bsegs m _ _ 156 SH). rewrite cells_size_map_C1'. unfold imp_sh_pro. rewrite imp_sh_length. reflexivity. }
  intros v0 w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 w3 w4 w5 w6 F4 m4 (ART4 & MI4 & WM4 & ST4) PR4 BY4. rewrite EU in ST4, PR4.
  rewrite (ret_pc_even IMP_SSXRET_A) by (unfold IMP_SSXRET_A; lia).
  assert (AG4 : forall P : Z -> Prop, (forall x, P x -> tailZ usp sp' f A8 x /\ ~ (shad f + 20 <= x < shad f + 20 + 68)) -> agree_on P m m4).
  { intros P HP a Ha. destruct (HP _ Ha) as [Z1 Z2]. apply PR4; [exact (ZCL _ Z1)| exact Z2]. }
  assert (L1' : rw_cells bsegs m4 sp' (imp_localsK j0 j8 f (Z_to_bv 64 n) d ne j160)).
  { apply (rw_cells_agree_nw bsegs m m4 _ _ L1). apply AG4. intros x Hx. rewrite imp_localsK_size in Hx. unfold tailZ. split; [left; lia| ul]. }
  assert (L2' : rw_cells bsegs m4 (sp' + 192) [CB 24 jr]).
  { apply (rw_cells_agree_nw bsegs m m4 _ _ L2). apply AG4. intros x Hx. cbn [cells_size csize Nat.add] in Hx. unfold tailZ. split; [left; lia| ul]. }
  assert (STp' : stk bsegs m4 (sp' + 216) (usp - 104)).
  { apply (stk_agree_nw bsegs m m4 _ _ STp). apply AG4. intros x Hx. cbv beta in Hx. unfold tailZ. split; [left; lia| ul]. }
  assert (SV' : rw_cells bsegs m4 (usp - 104) (imp_savedA cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11)).
  { apply (rw_cells_agree_nw bsegs m m4 _ _ SV). apply AG4. intros x Hx. rewrite imp_savedA_size in Hx. unfold tailZ. split; [left; lia| ul]. }
  assert (HD' : rw_cells bsegs m4 f (fz_hdr (C8 (Z_to_bv 64 IMP_MAGIC0)) (C8 (Z_to_bv 64 IMP_HDR_DESC_A)) (C8 (Z_to_bv 64 e_fuzz)) h3)).
  { apply (rw_cells_agree_nw bsegs m m4 _ _ HD). apply AG4. intros x Hx. unfold fz_hdr in Hx. cbn [cells_size csize Nat.add] in Hx. unfold tailZ. split; [right; left; lia| ul]. }
  assert (LB' : imp_libA (Some A8) m4).
  { apply (imp_libA_agree (Some A8) m m4 LB). apply AG4. intros x Hx. split; [unfold tailZ; do 3 right; left; exact Hx|].
    destruct (imp_lib_rng_cases _ _ Hx) as [[CS R]|(B & E & R)]; [pose proof (client_static_range _ CS); ul|].
    injection E as <-. pose proof (af_live_range RT AF Σ m A8 8 ARTx A8IN) as (_ & Y & _).
    pose proof (proj1 (af_fshadow_apart RT AF Σ m f 5%nat ARTx INF) A8 8 A8IN) as Y2. change (fs_size 5) with 2048 in Y2.
    rewrite SHF0 in Y2 |- *. unfold shad, SHB in Y2. clear - R Y Y2. Z.div_mod_to_equations; lia. }
  assert (AX' : aex6A m4).
  { apply (aex6A_agree m m4 AX). apply AG4. intros x Hx. split; [unfold tailZ; do 4 right; exact Hx|].
    destruct Hx as (l & h & Hin & R). unfold IMP_AEX_W in Hin. revert R. aex_lits. cbn [In] in Hin. intros R.
    destruct Hin as [E|[E|[]]]; injection E as <- <-; ul. }
  clear AG4 L1 L2 STp SV HD SH LB AX.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (imp_walk11b usp sp' f d ne _ _ (wz IMP_SSXRET_A) gp w0 w1 w2 v0 e1 e2 e3 e4 e5 e6 e7 s6 s7 s8 s9 s11 w3 w4 w5 w6 h3 j0 j8 j160 (Z_to_bv 64 n) F4 fc m4);
                   [lia| lia| lia| lia| exact HD'| exact L1'| exact MI4]|].
  cbv beta. intros ms5 (m5 & -> & MU5 & WM5 & MI5 & HD5). apply evt_done. unfold dtor_st.
  assert (ART5 : ART RT Σ m5).
  { apply (art_client_write RT AF Σ m4 m5 sp' ART4 ltac:(rewrite SPx; lia)); [| exact WM5].
    intros a Ha. apply MU5. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. rewrite FRSx.
    right; right; right; left. exists f, 5%nat. split; [left; reflexivity| change (fs_size 5) with 2048; lia]. }
  assert (ST5 : stk bsegs m5 lo sp').
  { apply (stk_agree bsegs m4 m5 _ _ ST4); [| exact WM5]. apply (agree_of_munch _ _ _ _ MU5). intros x Hx. cbn [outside]. split; [lia| exact I]. }
  assert (AG5 : forall P : Z -> Prop, (forall x, P x -> ~ (f <= x < f + 8)) -> agree_on P m4 m5).
  { intros P HP a Ha. apply MU5. cbn [outside]. split; [exact (HP _ Ha)| exact I]. }

  eapply (aevt_icall RT PMc).
  { exact (rc_stack_free_5 RT RC Σ PMc (wz IMP_SFRET_A) (wz sp') gp (wz TPV_A) w0 w1 w2 (wz usp) (wz sp') (wz f) (wz 1248) e2 e3 e4 e5 e6 e7
            (wz (f + 160 + 136 * (0 - 1) + 8)) (wz (shad f)) (wz (-544 + 136 * (3 - (0 - 1)))) (wz (-8)) s6 s7 s8 s9 (wz (f + 160))
            s11 w3 w4 w5 w6 F4 fc m5 f [] lo FDO MST eq_refl eq_refl eq_refl FRSx ART5 MI5 (COK m5 ST5)). }
  intros c (Σ6 & v6 & HQ & FRS6 & LV6 & SP6' & CR6). eexists Σ6, _. split; [exact HQ|].
  intros ms' (m6 & RS & (ART6 & MI6 & WM6 & ST6) & PR6).
  apply (ret_stF_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 ms' (fun ms => aevt Σ6 K ms) RS).
  intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F6. rewrite EU in ST6, PR6.
  rewrite (ret_pc_even IMP_SFRET_A) by (unfold IMP_SFRET_A; lia).
  assert (AG6 : forall P : Z -> Prop, (forall x, P x -> (sp' <= x < usp) \/ imp_lib_rng (Some A8) x \/ in_ranges IMP_AEX_W x) -> agree_on P m5 m6).
  { intros P HP a Ha. apply PR6. destruct (HP _ Ha) as [H|[H|H]].
    - left. ul.
    - destruct (imp_lib_rng_cases _ _ H) as [[CS R]|(B & E & R)]; [right; left; exact CS|]. injection E as <-. right; right; left. exists A8, 8. split; [exact A8IN| lia].
    - right; left. destruct H as (l & h & Hin & R). unfold IMP_AEX_W in Hin. revert R. aex_lits. cbn [In] in Hin. intros R.
      destruct Hin as [E|[E|[]]]; injection E as <- <-; apply client_static_intro; lia. }
  assert (AG46 : forall P : Z -> Prop, (forall x, P x -> (sp' <= x < usp) \/ imp_lib_rng (Some A8) x \/ in_ranges IMP_AEX_W x) -> agree_on P m4 m6).
  { intros P HP. eapply agree_trans; [| exact (AG6 P HP)]. apply AG5. intros x Hx. destruct (HP _ Hx) as [H|[H|H]]; [lia| |].
    - destruct (imp_lib_rng_cases _ _ H) as [[CS R]|(B & E & R)]; [pose proof (client_static_range _ CS); ul|]. injection E as <-.
      pose proof (af_frames_range RT AF Σ m f 5%nat ARTx INF) as (_ & _ & _ & FLV). pose proof (FLV A8 8 A8IN). change (fs_size 5) with 2048 in *. lia.
    - destruct H as (l & h & Hin & R). unfold IMP_AEX_W in Hin. revert R. aex_lits. cbn [In] in Hin. intros R. destruct Hin as [E|[E|[]]]; injection E as <- <-; ul. }

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { eapply (imp_walk11c usp sp' f lo _ _ (wz IMP_SFRET_A) gp q0 q1 q2 v6 q3 q4 q5 q6 q7 q8 q9 s6 s7 s8 s9 s11 q10 q11 q12 q13
              cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 (imp_localsK j0 j8 f (Z_to_bv 64 n) d ne j160 ++ [CB 24 jr]) F6 fc m6);
      [lia| lia| rewrite cells_size_app, imp_localsK_size; reflexivity| lia| lia| exact ST6| | | | exact MI6].
    - apply rw_cells_app. split; [| rewrite imp_localsK_size; replace (sp' + Z.of_nat 192) with (sp' + 192) by lia];
        [apply (rw_cells_agree_nw bsegs m4 m6 _ _ L1')| apply (rw_cells_agree_nw bsegs m4 m6 _ _ L2')]; apply AG46; intros x Hx;
        [rewrite imp_localsK_size in Hx| cbn [cells_size csize Nat.add] in Hx]; left; lia.
    - apply (stk_agree_nw bsegs m4 m6 _ _ STp'). apply AG46. intros x Hx. cbv beta in Hx. left. lia.
    - apply (rw_cells_agree_nw bsegs m4 m6 _ _ SV'). apply AG46. intros x Hx. rewrite imp_savedA_size in Hx. left. lia. }
  cbv beta. intros ms7 (RS7 & FC7 & ST7). apply evt_done.
  revert FC7. apply (ret_st_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 ms7 (fun ms => ms_fcsr ms = fc -> aevt Σ6 K ms) RS7).
  intros r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 F7 fc7 FC7. change (fc7 = fc) in FC7. subst fc7.
  apply (KFIN Σ6 A8 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 F7 fc m6 FRM ART6 MI6 ST7);
    [| | | exact VA| rewrite LV6; exact LVx| exact FRS6| rewrite SP6'; exact SPx| rewrite CR6; exact CRx].
  - intros a Ha Ho. pose proof (CSEP _ Ha) as (C1 & C2 & C3). rewrite <- (PRES a Ha Ho). rewrite (PR6 a), (MU5 a), (PR4 a); [reflexivity| | | |].
    + apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact LV0x| intros e []| lia].
    + lia.
    + cbn [outside]. split; [lia| exact I].
    + apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact LV0x| intros e []| lia].
  - apply (imp_libA_agree (Some A8) m4 m6 LB'). apply AG46. intros x Hx. right; left. exact Hx.
  - apply (aex6A_agree m4 m6 AX'). apply AG46. intros x Hx. right; right. exact Hx.
Qed.

Lemma imp_tail0A : forall (Σ0 Σ2 Σ : rts RT) (K : config -> Prop) (v : option Z) (A8 usp sp' f lo d n : Z)
    (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word) Fr fc (m0 m7 m : mem)
    (Lp : list (Z * Z)) (cb : Z),
  impG (rt_sp0 RT Σ0) usp sp' f lo ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo sp' ->
  rt_frames RT Σ = [(f, 5%nat)] -> rt_live RT Σ = Lp ++ (xnewA v A8 ++ rt_live RT Σ0) -> rt_sp0 RT Σ = rt_sp0 RT Σ0 -> cb <= rt_credit RT Σ ->
  In (A8, 8) (xnewA v A8 ++ rt_live RT Σ0) -> (forall B, v = Some B -> A8 = B) ->
  PDONE Σ2 m7 (f + 168) (xnewA v A8 ++ rt_live RT Σ0) -> ART RT Σ2 m7 -> rt_frames RT Σ2 = [(f, 5%nat)] -> rt_live RT Σ = rt_live RT Σ2 ->
  (forall a : word, (f + 168 <= bv_unsigned a < f + 248 \/ shad (f + 168) <= bv_unsigned a < shad (f + 168) + 10 \/ in_live (rt_live RT Σ2) (bv_unsigned a)) ->
                    m a = m7 a) ->
  tailB m usp sp' f n d A8 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 ->
  (forall a : word, aclient (rt_live RT Σ0) [] usp (bv_unsigned a) -> outside IMP_XFP_A (bv_unsigned a) -> m a = m0 a) ->
  frm0 fc ->
  imp_fin_k K Σ0 v usp lo cra gp (wz TPV_A) cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 m0 cb ->
  aevt Σ K (dtor_st e_pdtor (wz IMP_PDRET_A) sp' gp t0 t1 t2 usp (wz (f + 160 + 136 * 0 + 8)) a1 a2 a3 a4 a5 a6 a7 f (f + 160 + 136 * 0 + 8) (-544 + 136 * (3 - 0)) s6 s7 s8 s9 s11
               t3 t4 t5 t6 Fr fc m).
Proof using AF RC PDT PDFP FDO MST.
  intros until cb. intros G ARTx MIx STx FRSx LVx SPx CRx A8IN VA PD ART2 FRS2 LV2 PDA TB PRES FRM KFIN.
  pose proof (impG_facts _ _ _ _ _ G) as (F0 & FLO & SH0 & SLO & SLO' & GLO & GLO' & LO64 & LSP & LUSP & SPH & SPH' & SP6 & F8).
  pose proof G as (FSEG & F64 & FTOP & SHB0 & SHT & SEP & LOW & LOR & UT & SPR & SPA & SPW & SPT).
  assert (EU : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  assert (INF : In (f, 5%nat) (rt_frames RT Σ)) by (rewrite FRSx; left; reflexivity).
  assert (LV0x : forall e, In e (rt_live RT Σ0) -> In e (rt_live RT Σ)) by (intros e He; rewrite LVx; apply in_or_app; right; apply in_or_app; right; exact He).
  pose proof (imp_csep Σ0 Σ m usp sp' f lo ARTx INF LV0x SPx G) as CSEP.
  set (P := f + 160 + 136 * 0 + 8) in *.

  assert (PDx : PDONE Σ m P (xnewA v A8 ++ rt_live RT Σ0)).
  { subst P. replace (f + 160 + 136 * 0 + 8) with (f + 168) by lia.
    apply (PDFP Σ2 Σ m7 m (f + 168) _ PD ART2); [rewrite FRSx, FRS2; reflexivity| exact LV2|]. intros a Ha. apply PDA.
    destruct Ha as [H|[H|H]]; [left; lia| right; left; exact H| right; right; exact H]. }

  unfold dtor_st.
  eapply (aevt_rt RT PMc Σ K _ _
           (PDT Σ PMc (wz IMP_PDRET_A) (wz sp') gp (wz TPV_A) t0 t1 t2 (wz usp) (wz sp') (wz P) a1 a2 a3 a4 a5 a6 a7
                (wz P) (wz (shad f)) (wz (-544 + 136 * (3 - 0))) (wz (-8)) s6 s7 s8 s9 (wz (f + 160)) s11 t3 t4 t5 t6 Fr fc m
                P (xnewA v A8 ++ rt_live RT Σ0) lo
                FDO MST eq_refl eq_refl PDx ARTx MIx ltac:(rewrite EU; exact STx) ltac:(lia) ltac:(rewrite EU; ul) ltac:(rewrite EU; ul)
                ltac:(rewrite EU; clear - SPA; Z.div_mod_to_equations; lia) ltac:(unfold unwind_ok; rewrite EU, !unsigned_lit by ul; right; right; lia) FRM)); [exact FRM|].
  intros c (Σ3 & HA & LV3 & FRS3 & SP3 & CR3). eexists Σ3, _. split; [exact HA|].
  intros ms' (vv & m3 & RS & (ART3 & MI3 & ST3) & PR3) FRM3.
  destruct RS as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F3 & fc3 & ->). cbn [ms_fcsr] in FRM3.
  rewrite EU in ST3, PR3. rewrite (ret_pc_even IMP_PDRET_A) by (unfold IMP_PDRET_A; lia). rewrite FRSx in PR3, FRS3. rewrite SPx in SP3.
  assert (AG3 : agree_on (tailZ usp sp' f A8) m m3).
  { intros a Ha. apply PR3; [exact (tailZ_aclient _ usp sp' f A8 _ F0 SH0 A8IN ltac:(clear - UT; unfold USTACK_TOP in *; lia) Ha)|].
    cbn [outside]. split; [| exact I]. subst P. revert Ha. unfold tailZ. intros Ha.
    destruct Ha as [H|[H|[H|[H|H]]]]; [lia| lia| clear - H SEP F0; unfold shad, SHB in *; lia| |].
    - destruct (imp_lib_rng_cases _ _ H) as [[CS R]|(B & E & R)]; [pose proof (client_static_range _ CS); ul|]. injection E as <-.
      pose proof (af_frames_range RT AF Σ m f 5%nat ARTx INF) as (_ & _ & _ & FLV).
      pose proof (FLV A8 8 ltac:(rewrite LVx; apply in_or_app; right; exact A8IN)). change (fs_size 5) with 2048 in *. lia.
    - destruct H as (l & h & Hin & R). unfold IMP_AEX_W in Hin. revert R. aex_lits. cbn [In] in Hin. intros R. destruct Hin as [E|[E|[]]]; injection E as <- <-; ul. }
  pose proof (tailB_agree m m3 usp sp' f n d A8 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 TB LUSP AG3) as TB3.
  change (aevt Σ3 K (dtor_st IMP_PDRET_A (wz IMP_PDRET_A) sp' gp u0 u1 u2 usp vv b1 b2 b3 b4 b5 b6 b7 f P (-544 + 136 * (3 - 0)) s6 s7 s8 s9 s11 u3 u4 u5 u6 F3 fc3 m3)).
  subst P.
  apply (imp_exitA Σ0 Σ3 K v A8 usp sp' f lo d n gp u0 u1 u2 vv b1 b2 b3 b4 b5 b6 b7 s6 s7 s8 s9 s11 u3 u4 u5 u6 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 F3 fc3 m0 m3 cb G ART3 MI3 ST3);
    [exact FRS3| exact LV3| exact SP3| rewrite CR3; exact CRx| rewrite LV3; exact A8IN| exact VA| exact TB3| | exact FRM3| exact KFIN].
  intros a Ha Ho. rewrite <- (PRES a Ha Ho). apply PR3.
  - apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; apply in_or_app; right; exact He| intros e []| lia].
  - cbn [outside]. split; [| exact I]. pose proof (CSEP _ Ha) as (C1 & _). lia.
Qed.

Lemma imp_outA_agree : forall (m m' : mem) F ocp, imp_outA m F ocp -> agree_on (fun x => F + 272 <= x < F + 296) m m' -> imp_outA m' F ocp.
Proof.
  intros m m' F [[DATA SZ]|] H AG; unfold imp_outA in *.
  - destruct H as (L & H1 & H2). exists L. split; [| exact H2]. apply (rw_cells_agree_nw bsegs m m' _ _ H1). intros a Ha. apply AG. unfold out_longA in Ha. cbn in Ha. lia.
  - destruct H as (b0 & j23 & H1 & H2). exists b0, j23. split; [| exact H2]. apply (rw_cells_agree_nw bsegs m m' _ _ H1). intros a Ha. apply AG. unfold out_shortA in Ha. cbn in Ha. lia.
Qed.

Lemma imp_sh_pro_run68 : forall (m : mem) f, rw_cells bsegs m (shad f) (map C1 imp_sh_pro) -> rw_cells bsegs m (shad f + 20) (map C1 (repeat z8 68)).
Proof.
  intros m f H. unfold imp_sh_pro, imp_sh in H. rewrite !map_app in H.
  apply rw_cells_app in H. destruct H as [_ H]. apply rw_cells_app in H. destruct H as [_ H]. apply rw_cells_app in H. destruct H as [_ H].
  apply rw_cells_app in H. destruct H as [H _]. rewrite !cells_size_map_C1', !repeat_length in H.
  lazymatch type of H with rw_cells _ _ ?a _ => replace a with (shad f + 20) in H by lia end. unfold z8. exact H.
Qed.

Lemma imp_tailA : forall (Σ0 Σ2 Σx : rts RT) (K : config -> Prop) (v : option Z) (A8 usp sp' f lo d n ne : Z)
    (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2x s4x s7x s11x t3 t4 t5 t6 : word) (cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word) Fr fc (m0 m7 m : mem)
    (ocp : option (Z * Z)) (Lp : list (Z * Z)) (cb : Z),
  impG (rt_sp0 RT Σ0) usp sp' f lo ->
  ART RT Σx m -> mem_inv bsegs m -> stk bsegs m lo sp' ->
  rt_frames RT Σx = [(f, 5%nat)] -> rt_live RT Σx = ocp_chunks ocp ++ rt_live RT Σ2 -> rt_live RT Σ2 = Lp ++ (xnewA v A8 ++ rt_live RT Σ0) ->
  rt_sp0 RT Σx = rt_sp0 RT Σ0 -> cb <= rt_credit RT Σx ->
  In (A8, 8) (xnewA v A8 ++ rt_live RT Σ0) -> (forall B, v = Some B -> A8 = B) -> (forall q k, In (q, k) (rt_live RT Σx) -> 0 < k) ->
  PDONE Σ2 m7 (f + 168) (xnewA v A8 ++ rt_live RT Σ0) -> ART RT Σ2 m7 -> rt_frames RT Σ2 = [(f, 5%nat)] ->
  (forall a : word, (f + 168 <= bv_unsigned a < f + 248 \/ shad (f + 168) <= bv_unsigned a < shad (f + 168) + 10 \/ in_live (rt_live RT Σ2) (bv_unsigned a)) ->
                    m a = m7 a) ->
  tailB m usp sp' f n d A8 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 -> slot0A m (f + 296) -> slot0A m (f + 432) -> slot0A m (f + 568) ->
  imp_outA m f ocp ->
  (forall a : word, aclient (rt_live RT Σ0) [] usp (bv_unsigned a) -> outside IMP_XFP_A (bv_unsigned a) -> m a = m0 a) ->
  frm0 fc ->
  imp_fin_k K Σ0 v usp lo cra gp (wz TPV_A) cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 m0 cb ->
  (ne = 0 \/ ne = 1) ->
  aevt Σx K (imp_regsA IMP_OKARM_END_A x1 sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s2x s4x (wz 0) s7x (wz n) (wz ne) (wz 0) s11x t3 t4 t5 t6 Fr fc m).
Proof using AF RC PDT PDFP FDO MST.
  intros until cb. intros G ARTx MIx STx FRSx LVx LV2 SPx CRx A8IN VA LVP PD ART2 FRS2 PDA TB S1 S2 S3 OUT PRES FRM KFIN NE.
  pose proof (impG_facts _ _ _ _ _ G) as (F0 & FLO & SH0 & SLO & SLO' & GLO & GLO' & LO64 & LSP & LUSP & SPH & SPH' & SP6 & F8).
  pose proof G as (FSEG & F64 & FTOP & SHB0 & SHT & SEP & LOW & LOR & UT & SPR & SPA & SPW & SPT).
  assert (EU : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  assert (INF : In (f, 5%nat) (rt_frames RT Σx)) by (rewrite FRSx; left; reflexivity).
  assert (LV2x : forall e, In e (rt_live RT Σ2) -> In e (rt_live RT Σx)) by (intros e He; rewrite LVx; apply in_or_app; right; exact He).
  assert (LV0x : forall e, In e (rt_live RT Σ0) -> In e (rt_live RT Σx)) by (intros e He; apply LV2x; rewrite LV2; apply in_or_app; right; apply in_or_app; right; exact He).
  assert (A8x : In (A8, 8) (rt_live RT Σx)) by (apply LV2x; rewrite LV2; apply in_or_app; right; exact A8IN).
  pose proof (imp_csep Σ0 Σx m usp sp' f lo ARTx INF LV0x SPx G) as CSEP.
  pose proof (af_client_consts RT AF Σx m ARTx) as CC.
  pose proof (af_frames_range RT AF Σx m f 5%nat ARTx INF) as (_ & _ & _ & FLV). change (fs_size 5) with 2048 in FLV.
  assert (SHF0 : shad f = f / 8 + SHB) by reflexivity. unfold SHB in SHF0.
  pose proof TB as ((ne0 & j0 & j8 & j160 & jr & NE0 & L1 & L2) & _ & _ & _ & SH & _).
  pose proof (imp_sh_pro_run68 m f SH) as SH68.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (imp_walk9 usp sp' f d n ne x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2x s4x s7x s11x t3 t4 t5 t6 j0 j8 j160 (wz n) Fr fc m);
                   [lia| lia| lia| lia| lia| unfold shad, SHB in *; lia| exact NE| exact L1| exact MIx]|].
  cbv beta. intros ms1 (a0' & a1' & s11' & ->).

  eapply evt_cut; [eapply (imp_slots321 usp sp' f lo x1 gp t0 t1 t2 a0' a1' a2 a3 a4 a5 a6 a7 (wz 1) s7x (wz n) (wz ne) s11' t3 t4 t5 t6 Fr fc m);
                   [exact STx| lia| lia| lia| lia| lia| lia| lia| exact SEP| exact F8| exact CC| exact S1| exact S2| exact S3| exact SH68| exact MIx]|].
  cbv beta. intros ms2 (m1 & a02 & a12 & a22 & t12 & -> & MU1 & WM1 & MI1 & ST1 & _ & _ & _). apply evt_done.

  assert (WIN : forall a, ~ outside (slots321W sp' f) a -> (sp' - 64 <= a < sp') \/ (f + 312 <= a < f + 648)).
  { intros a Ha. unfold slots321W, slotW in Ha. cbn [outside app] in Ha. lia. }
  assert (AG1 : forall P : Z -> Prop, (forall x, P x -> ~ (sp' - 64 <= x < sp') /\ ~ (f + 312 <= x < f + 648)) -> agree_on P m m1).
  { intros P HP a Ha. apply MU1. destruct (HP _ Ha) as [N1 N2]. unfold slots321W, slotW. cbn [outside app]. repeat split; try exact I; lia. }
  assert (ART1 : ART RT Σx m1).
  { apply (art_client_write RT AF Σx m m1 (sp' - 64) ARTx ltac:(rewrite SPx; lia)); [| exact WM1].
    intros a Ha. apply MU1. unfold slots321W, slotW. cbn [outside app]. rewrite FRSx in Ha.
    assert (C1 : ~ (sp' - 64 <= bv_unsigned a < USTACK_TOP)) by (intros Hc; apply Ha; left; exact Hc).
    assert (C2 : ~ (f <= bv_unsigned a < f + 2040)) by (intros Hc; apply Ha; right; right; right; left; exists f, 5%nat; split; [left; reflexivity| change (fs_size 5) with 2048; lia]).
    unfold USTACK_TOP in *. repeat split; try exact I; lia. }
  assert (TB1 : tailB m1 usp sp' f n d A8 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11).
  { apply (tailB_agree m m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TB LUSP). apply AG1. intros x Hx. unfold tailZ in Hx.
    destruct Hx as [H|[H|[H|[H|H]]]]; [lia| lia| clear - H SEP F0 SLO LO64; unfold shad, SHB in *; lia| |].
    - destruct (imp_lib_rng_cases _ _ H) as [[CS R]|(B & E & R)]; [pose proof (client_static_range _ CS); ul|]. injection E as <-. pose proof (FLV A8 8 A8x).
      pose proof (af_live_range RT AF Σx m A8 8 ARTx A8x) as (_ & Y & _). rewrite SPx in Y. lia.
    - destruct H as (l & h & Hin & R). unfold IMP_AEX_W in Hin. revert R. aex_lits. cbn [In] in Hin. intros R. destruct Hin as [E|[E|[]]]; injection E as <- <-; ul. }
  assert (PDA1 : forall a : word, (f + 168 <= bv_unsigned a < f + 248 \/ shad (f + 168) <= bv_unsigned a < shad (f + 168) + 10 \/ in_live (rt_live RT Σ2) (bv_unsigned a)) -> m1 a = m7 a).
  { intros a Ha. rewrite <- (PDA a Ha). apply (AG1 (fun x => x = bv_unsigned a)); [| reflexivity]. intros x ->.
    destruct Ha as [H|[H|(p & k & Hin & R)]]; [lia| clear - H SEP F0 SLO LO64; unfold shad, SHB in *; Z.div_mod_to_equations; lia|].
    pose proof (FLV p k (LV2x _ Hin)). pose proof (af_live_range RT AF Σx m p k ARTx (LV2x _ Hin)) as (_ & Y & _). rewrite SPx in Y. lia. }
  assert (OUT1 : imp_outA m1 f ocp) by (apply (imp_outA_agree m m1 f ocp OUT); apply AG1; intros x Hx; lia).
  assert (PRES1 : forall a : word, aclient (rt_live RT Σ0) [] usp (bv_unsigned a) -> outside IMP_XFP_A (bv_unsigned a) -> m1 a = m0 a).
  { intros a Ha Ho. rewrite <- (PRES a Ha Ho). apply (AG1 (fun x => x = bv_unsigned a)); [| reflexivity]. intros x ->. pose proof (CSEP _ Ha) as (C1 & C2 & C3). lia. }
  clear AG1 MU1 WM1 TB S1 S2 S3 OUT PRES PDA SH SH68 L1 L2 CC STx MIx.
  destruct ocp as [[DATA SZ]|].
  -
    destruct OUT1 as (L & OC & ODD & SZR & D0 & D16 & LR). cbn [ocp_chunks app] in LVx.
    assert (INx : In (DATA, SZ) (rt_live RT Σx)) by (rewrite LVx; left; reflexivity).
    pose proof (af_live_range RT AF Σx m1 DATA SZ ART1 INx) as (_ & DY & _).
    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut; [eapply (imp_walk10l usp sp' f (wz IMP_PDRET_A) gp t0 t12 t2 a02 a12 a22 a3 a4 a5 a6 a7 (wz 1) s7x (wz n) (wz ne) s11' t3 t4 t5 t6 SZ L DATA Fr fc m1);
                     [lia| lia| exact ODD| exact SZR| rewrite SPx in DY; ul| lia| exact OC| exact MI1]|].
    cbv beta. intros ms3 <-. apply evt_done. unfold dtor_st.
    eapply (aevt_opdel RT AF RC PMc FDO MST Σx K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc m1 DATA SZ lo INx eq_refl ART1 MI1).
    { unfold call_ok. rewrite EU, SPx. split; [exact ST1|]. split; [lia|]. split; [ul|]. split; [ul| clear - SPA; Z.div_mod_to_equations; lia]. }
    { unfold unwind_ok. rewrite EU, !unsigned_lit by ul. right; right; lia. }
    intros Σ' vr w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 w3 w4 w5 w6 F2 m2 (ART2' & MI2 & ST2) PR2 LV' FRS' SP' CR'. rewrite EU in ST2, PR2.
    rewrite (ret_pc_even IMP_ODRET_A) by (unfold IMP_ODRET_A; lia).
    assert (LVE : rt_live RT Σ' = rt_live RT Σ2).
    { rewrite LV'. apply (live_remove_head RT AF Σx m1 DATA SZ (rt_live RT Σ2) ART1 LVx ltac:(lia)). intros q k Hq. apply (LVP q k). rewrite LVx. right. exact Hq. }
    assert (AG2 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ2) [(f, 5%nat)] sp' x) -> agree_on P m1 m2).
    { intros P HP a Ha. apply PR2. rewrite LVE, FRSx. exact (HP _ Ha). }
    assert (A82 : In (A8, 8) (rt_live RT Σ2)) by (rewrite LV2; apply in_or_app; right; exact A8IN).
    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut; [apply (imp_walk10b usp sp' f _ _ (wz IMP_ODRET_A) gp w0 w1 w2 vr e1 e2 e3 e4 e5 e6 e7 (wz 1) s7x (wz n) (wz ne) s11' w3 w4 w5 w6 F2 fc m2)|].
    cbv beta. intros ms4 <-. apply evt_done.
    apply (imp_tail0A Σ0 Σ2 Σ' K v A8 usp sp' f lo d n gp w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 (wz 1) s7x (wz n) (wz ne) s11' w3 w4 w5 w6 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 F2 fc m0 m7 m2 Lp cb G ART2' MI2 ST2);
      [rewrite FRS'; exact FRSx| rewrite LVE; exact LV2| rewrite SP'; exact SPx| rewrite CR'; exact CRx| exact A8IN| exact VA| exact PD| exact ART2| exact FRS2| exact LVE| | | | exact FRM| exact KFIN].
    + intros a Ha. rewrite <- (PDA1 a Ha). apply (AG2 (fun x => x = bv_unsigned a)); [| reflexivity]. intros x ->.
      destruct Ha as [H|[H|H]].
      * right; right; right; left. exists f, 5%nat. split; [left; reflexivity| change (fs_size 5) with 2048; lia].
      * right; right; right; right. exists f, 5%nat. split; [left; reflexivity|]. revert H. unfold shad, SHB. change (fs_size 5) with 2048. intros H. Z.div_mod_to_equations; lia.
      * right; right; left. exact H.
    + apply (tailB_agree m1 m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TB1 LUSP). apply AG2. intros x Hx.
      exact (tailZ_aclient _ usp sp' f A8 x F0 SH0 A82 ltac:(clear - UT; unfold USTACK_TOP in *; lia) Hx).
    + intros a Ha Ho. rewrite <- (PRES1 a Ha Ho). apply (AG2 (fun x => x = bv_unsigned a)); [| reflexivity]. intros x ->.
      apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; rewrite LV2; apply in_or_app; right; apply in_or_app; right; exact He| intros e []| lia].
  -
    destruct OUT1 as (b0 & j23 & OC & EV). cbn [ocp_chunks app] in LVx.
    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut; [eapply (imp_walk10s usp sp' f 0 (wz IMP_PDRET_A) gp t0 t12 t2 a02 a12 a22 a3 a4 a5 a6 a7 (wz 1) s7x (wz n) (wz ne) s11' t3 t4 t5 t6 b0 j23 Fr fc m1);
                     [lia| lia| lia| exact EV| replace (f + 160 + 136 * 0 + 112) with (f + 272) by lia; exact OC| exact MI1]|].
    cbv beta. intros ms3 (a0x & -> & ->). apply evt_done.
    apply (imp_tail0A Σ0 Σ2 Σx K v A8 usp sp' f lo d n gp t0 t12 t2 a12 a22 a3 a4 a5 a6 a7 (wz 1) s7x (wz n) (wz ne) s11' t3 t4 t5 t6 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 Fr fc m0 m7 m1 Lp cb G ART1 MI1 ST1
             FRSx ltac:(rewrite LVx; exact LV2) SPx CRx A8IN VA PD ART2 FRS2 LVx PDA1 TB1 PRES1 FRM KFIN).
Qed.

End WithPM.
End Tail.
