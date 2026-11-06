(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim SjModel PjModel.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2 Sj_new Sj_num_akit Sj_num_amem Sj_h_alloc Sj_stage2_iface Atp_fzwA Atp_setcapA Atp_hkit5A Atp_pid1A Atp_pidiA Atp_activewA Pj_rtkA Pj_defsA Pj_hdefsA Pj_cpsA Pj_lftoi1A Pj_lftoi2A Pj_lftoi4A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition pj_lib : mem -> Prop := pj_libA sj_lib.

Definition sj_lib_rng (x : Z) : Prop :=
  0x6b2540 <= x < 0x6b2548 \/ 0x6b2560 <= x < 0x6b2562 \/ 0x6b25e0 <= x < 0x6b260c \/ 0x6b2640 <= x < 0x6b2642.

Lemma sj_lib_agree : forall m m', sj_lib m -> agree_on sj_lib_rng m m' -> sj_lib m'.
Proof.
  intros m m' [(A & B & C & D)|(A & B & C & D)] AG; [left| right]; unfold lib0, lib1, sj_lib_rng in *;
    (split; [| split; [| split]]; [eapply rw_cells_agree_nw; [exact A|] | eapply rw_cells_agree_nw; [exact B|] | eapply rw_cells_agree_nw; [exact C|] | eapply rw_cells_agree_nw; [exact D|]];
     intros a Ha; apply AG; cbn [cells_size csize Nat.add] in Ha; lia).
Qed.

Lemma sj_lib_rng_fp : forall x, sj_lib_rng x -> in_ranges LIB_FP x.
Proof.
  intros x Hx. unfold sj_lib_rng, LIB_FP, in_ranges in *.
  destruct Hx as [H|[H|[H|H]]].
  - exists 0x6b2540, 0x6b2548. split; [cbn; tauto| lia].
  - exists 0x6b2560, 0x6b2568. split; [cbn; tauto| lia].
  - exists 0x6b25e0, 0x6b2610. split; [cbn; tauto| lia].
  - exists 0x6b2640, 0x6b2648. split; [cbn; tauto| lia].
Qed.

Lemma loc_rng_fp : forall x, PJ_LOC_LO_A <= x < PJ_LOC_HI_A -> in_ranges LIB_FP x.
Proof. intros x Hx. exists PJ_LOC_LO_A, PJ_LOC_HI_A. split; [unfold LIB_FP, PJ_LOC_LO_A, PJ_LOC_HI_A; cbn; tauto| exact Hx]. Qed.

Lemma lock_rng_fp : forall x, PJ_LOCKW_A <= x < PJ_LOCKW_A + 4 -> in_ranges LIB_FP x.
Proof. intros x Hx. exists PJ_LOCKW_A, (PJ_LOCKW_A + 4). split; [unfold LIB_FP, PJ_LOCKW_A; cbn; tauto| exact Hx]. Qed.

Lemma libc_nl_static : forall x, LIBC_NL <= x < LIBC_NL + 1 -> client_static x.
Proof. intros x Hx. apply client_static_intro. unfold LIBC_NL in Hx. lia. Qed.

Lemma pj_lib_agree : forall m m', pj_lib m -> agree_on (in_ranges LIB_FP) m m' -> pj_lib m'.
Proof.
  intros m m' (S & L & W) AG. split; [| split].
  - eapply sj_lib_agree; [exact S|]. eapply agree_sub; [exact AG|]. exact sj_lib_rng_fp.
  - eapply pj_locA_agree; [exact L|]. eapply agree_sub; [exact AG|]. exact loc_rng_fp.
  - eapply lockwA_agree; [exact W|]. eapply agree_sub; [exact AG|]. exact lock_rng_fp.
Qed.

Lemma pj_lib_loc : fp_local LIB_FP pj_lib.
Proof. intros m m' H AG. apply (pj_lib_agree m m' H). intros a Ha. apply AG. exact Ha. Qed.

Lemma cells_size_map_C1 : forall bs : list byte, cells_size (map C1 bs) = length bs.
Proof. induction bs as [|b bs IH]; [reflexivity|]. cbn [map cells_size csize length]. rewrite IH. reflexivity. Qed.

Section Top.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PDONE : rts RT -> mem -> Z -> list (Z * Z) -> Prop.
Hypothesis PDT : pdtor_cps RT PDONE.
Hypothesis PDFP : pdone_fpA RT PDONE.
Hypothesis PID : pj_pid_cpsA RT pj_lib PDONE.
Hypothesis OKARM : forall PMc, pj_okarm_cpsA RT PMc.

Local Ltac ul := unfold FUZZ_STACK, PID_STACK, PJ_OKARM_STACK_A, PJ_SER_STACK_A, ser_needA, PJ_TC_STACK_A in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Section WithPM.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Notation aevt := (aevt RT PMc).

Definition pj_fin_k (K : config -> Prop) (Σ0 : rts RT) (usp lo : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m0 : mem) (cb : Z) : Prop :=
  forall (Σ' : rts RT) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m', frm0 fc' ->
    ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' lo usp ->
    rt_pres_fp (rt_live RT Σ0) [] usp LIB_FP m0 m' -> pj_lib m' ->
    rt_live RT Σ' = rt_live RT Σ0 -> rt_frames RT Σ' = [] -> rt_sp0 RT Σ' = rt_sp0 RT Σ0 -> cb <= rt_credit RT Σ' ->
    aevt Σ' K (MS (mkR ra (wz usp) gp tp t0' t1' t2' s0 s1 (wz 0) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc' None m' (seg_rom bsegs)).

Lemma pj_tail : forall (Σ0 Σx : rts RT) (K : config -> Prop) (usp sp' f lo d n : Z) (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 t3 t4 t5 t6 : word)
    (cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word) (LC : list cell) (h3 t : list byte) F fc (m0 m : mem) (cb : Z),

  0 < f -> f mod 64 = 0 -> f + 1024 <= rt_sp0 RT Σ0 - STACK_WIN -> SEGTOP_A <= f -> 0 <= f / 8 ->
  (f + 1024 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 128 <= f) -> SHB <= f / 8 + 2147450880 -> f / 8 + 2147450880 + 128 + 1 <= rt_sp0 RT Σ0 - STACK_WIN ->
  rt_sp0 RT Σ0 - STACK_WIN <= lo -> lo + FUZZ_STACK <= usp -> usp + 16 <= USTACK_TOP -> usp - 208 <= sp' <= usp - 192 -> sp' mod 32 = 0 ->

  ART RT Σx m -> mem_inv bsegs m -> rt_frames RT Σx = [(f, 4%nat)] -> (forall e, In e (rt_live RT Σ0) -> In e (rt_live RT Σx)) -> rt_sp0 RT Σx = rt_sp0 RT Σ0 -> cb <= rt_credit RT Σx ->
  PDONE Σx m (f + 160) (rt_live RT Σ0) ->

  stk bsegs m lo sp' -> cells_size LC = 88%nat -> rw_cells bsegs m sp' LC -> stk bsegs m (sp' + 88) (usp - 104) ->
  rw_cells bsegs m (usp - 104) (fa_saved cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11) ->
  rw_cells bsegs m f (fz_hdr (C8 (wz 0x41b58ab3)) (C8 (wz 0x13300)) (C8 (wz 0xb15fc)) h3) ->
  rw_cells bsegs m (f / 8 + 2147450880) (pj_shadow1 t) ->
  pj_lib m -> rt_pres_fp (rt_live RT Σ0) [] usp LIB_FP m0 m -> frm0 fc ->
  pj_fin_k K Σ0 usp lo cra gp (wz TPV_A) cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 m0 cb ->
  aevt Σx K (lf_regs e_pdtor (wz 0xb1ad8) sp' gp (wz TPV_A) t0 t1 t2 usp (wz (f + 160)) a1 a2 a3 a4 a5 a6 a7 f n d s7 s8 s9 t3 t4 t5 t6 F fc m).
Proof using AF RC PDT FDO MST.
  intros until cb. intros F0 F64 FTOP FSEG FD SEP SHB0 SHT LOW LOR UT SPR SPA ARTx MIx FRSx LVx SPx CRx PD ST SZ FRl STp FRs FH FS LIBx PRESx FRM KFIN.
  pose proof (af_sp0_range RT AF Σx m ARTx) as SP0R. pose proof (af_sp0_win RT AF Σx m ARTx) as SP0W. rewrite SPx in SP0R, SP0W.
  assert (EU : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; ul).
  assert (INF : In (f, 4%nat) (rt_frames RT Σx)) by (rewrite FRSx; left; reflexivity).

  assert (CSEP : forall a, aclient (rt_live RT Σ0) [] usp a -> ~ (f <= a < f + 1024) /\ ~ (f / 8 + 2147450880 <= a < f / 8 + 2147450880 + 128) /\ (usp <= a \/ a < lo)).
  { intros a Ha. destruct Ha as [H|[H|[H|[H|H]]]].
    - clear - H FTOP SHT LOW LOR SPR. split; [ul|]. split; [ul| left; lia].
    - pose proof (client_static_range _ H) as R. clear - R FSEG SHB0 SP0R LOW. unfold SEGTOP_A, SHB in *. split; [lia|]. split; [lia| right; ul].
    - destruct H as (p & k & Hin & Hr). apply LVx in Hin.
      pose proof (af_frames_range RT AF Σx m f 4%nat ARTx INF) as (_ & _ & _ & FLV). pose proof (FLV p k Hin) as Y1.
      pose proof (proj1 (af_fshadow_apart RT AF Σx m f 4%nat ARTx INF) p k Hin) as Y2.
      pose proof (af_live_range RT AF Σx m p k ARTx Hin) as (_ & Y3 & _). rewrite SPx in Y3.
      change (fs_size 4) with 1024 in *. unfold shad, SHB in Y2. replace ((f + 1024) / 8) with (f / 8 + 128) in Y2 by (Z.div_mod_to_equations; lia).
      clear - Hr Y1 Y2 Y3 LOW. split; [lia|]. split; [lia| right; lia].
    - destruct H as (f9 & k9 & [] & _).
    - destruct H as (f9 & k9 & [] & _). }

  unfold lf_regs.
  eapply (aevt_rt RT PMc Σx K _ _
           (PDT Σx PMc (wz 0xb1ad8) (wz sp') gp (wz TPV_A) t0 t1 t2 (wz usp) (wz sp') (wz (f + 160)) a1 a2 a3 a4 a5 a6 a7
                (wz f) (wz (f + 160)) (wz (f / 8 + 2147450880)) (wz n) (wz d) s7 s8 s9 (wz f) (wz 2147450880) t3 t4 t5 t6 F fc m (f + 160) (rt_live RT Σ0) lo
                FDO MST eq_refl eq_refl PD ARTx MIx ltac:(rewrite EU; exact ST) ltac:(lia) ltac:(rewrite EU; ul) ltac:(rewrite EU; ul)
                ltac:(rewrite EU; Z.div_mod_to_equations; lia) ltac:(unfold unwind_ok; rewrite EU, !unsigned_lit by ul; right; right; lia) FRM)); [exact FRM|].
  intros c (Σ2 & HA & LV2 & FRS2 & SP2 & CR2). eexists Σ2, _. split; [exact HA|].
  intros ms' (v & m2 & RS & (ART2 & MI2 & ST2) & PRES2) FRM2.
  destruct RS as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->). cbn [ms_fcsr] in FRM2.
  rewrite EU in ST2, PRES2. rewrite (ret_pc_even 0xb1ad8) by lia.
  rewrite FRSx in PRES2, FRS2. rewrite SPx in SP2.
  cbn [ms_fcsr] in FRM2.

  assert (AGx : forall (P : Z -> Prop), (forall x, P x -> (sp' <= x < usp /\ ~ (f + 160 <= x < f + 240)) \/ (f <= x < f + 32) \/ (f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 128)) ->
                 agree_on P m m2).
  { intros P HP a Ha. apply PRES2.
    - destruct (HP _ Ha) as [[H1 H2]|[H|H]]; [left; ul| right; right; right; left| right; right; right; right];
        [exists f, 4%nat; split; [left; reflexivity| change (fs_size 4) with 1024; lia]
        | exists f, 4%nat; split; [left; reflexivity| unfold shad, SHB; change (fs_size 4) with 1024; Z.div_mod_to_equations; lia]].
    - cbn [outside]. split; [| exact I]. destruct (HP _ Ha) as [[H1 H2]|[H|H]]; [lia| lia| lia]. }
  assert (FRl2 : rw_cells bsegs m2 sp' LC).
  { eapply rw_cells_agree_nw; [exact FRl|]. apply AGx. intros x Hx. rewrite SZ in Hx. left. split; [lia| ul]. }
  assert (STp2 : stk bsegs m2 (sp' + 88) (usp - 104)).
  { eapply stk_agree_nw; [exact STp|]. apply AGx. intros x Hx. cbv beta in Hx. left. split; [lia| ul]. }
  assert (FRs2 : rw_cells bsegs m2 (usp - 104) (fa_saved cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11)).
  { eapply rw_cells_agree_nw; [exact FRs|]. apply AGx. intros x Hx. unfold fa_saved in Hx. cbn [cells_size csize Nat.add] in Hx. left. split; [lia| ul]. }
  assert (FH2 : rw_cells bsegs m2 f (fz_hdr (C8 (wz 0x41b58ab3)) (C8 (wz 0x13300)) (C8 (wz 0xb15fc)) h3)).
  { eapply rw_cells_agree_nw; [exact FH|]. apply AGx. intros x Hx. unfold fz_hdr in Hx. cbn [cells_size csize Nat.add] in Hx. right; left. lia. }
  assert (FS2 : rw_cells bsegs m2 (f / 8 + 2147450880) (pj_shadow1 t)).
  { eapply rw_cells_agree_nw; [exact FS|]. apply AGx. intros x Hx. unfold pj_shadow1 in Hx. rewrite cells_size_app, cells_size_map_C1, pj_shadow_bytes_length in Hx.
    cbn [cells_size csize Nat.add] in Hx. right; right. lia. }
  assert (LIB2 : pj_lib m2).
  { eapply pj_lib_agree; [exact LIBx|]. intros a Ha. pose proof (client_static_range _ (proj1 (lib_fp_static _ Ha))) as R. apply PRES2.
    - right; left. exact (proj1 (lib_fp_static _ Ha)).
    - cbn [outside]. split; [| exact I]. unfold SEGTOP_A in *. lia. }
  assert (PRES2' : forall a : word, aclient (rt_live RT Σ0) [] usp (bv_unsigned a) -> outside LIB_FP (bv_unsigned a) -> m2 a = m0 a).
  { intros a Ha Ho. rewrite <- (PRESx a Ha Ho). apply PRES2.
    - apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| intros e []| lia].
    - cbn [outside]. split; [| exact I]. pose proof (CSEP _ Ha) as (C1 & _). lia. }
  clear PRES2 AGx FRl STp FRs FH FS LIBx PRESx ST PD.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_walkX1 usp sp' f lo d n (wz 0xb1ad8) gp (wz TPV_A) u0 u1 u2 v b1 b2 b3 b4 b5 b6 b7 s7 s8 s9 u3 u4 u5 u6 h3 t F2 fc2 m2);
                   [lia| lia| lia| lia| exact SEP| ul| exact FH2| exact FS2| exact MI2]|].
  cbv beta. intros ms3 (m3 & -> & MU3 & WM3 & MI3 & FH3 & FS3). apply evt_done. unfold lf_regs.
  assert (ART3 : ART RT Σ2 m3).
  { apply (art_client_write RT AF Σ2 m2 m3 sp' ART2 ltac:(rewrite SP2; ul)); [| exact WM3].
    intros a Ha. apply MU3. cbn [outside]. split; [| split; [| exact I]]; intros Hin; apply Ha; rewrite FRS2.
    - right; right; right; left. exists f, 4%nat. split; [left; reflexivity| change (fs_size 4) with 1024; lia].
    - right; right; right; right. exists f, 4%nat. split; [left; reflexivity| unfold shad, SHB; change (fs_size 4) with 1024; Z.div_mod_to_equations; lia]. }
  assert (ST3 : stk bsegs m3 lo sp').
  { apply (stk_agree bsegs m2 m3 _ _ ST2); [| exact WM3]. apply (agree_of_munch _ _ _ _ MU3). intros x Hx. cbn [outside]. lia. }

  eapply (aevt_setshadow RT RC PMc FDO MST Σ2 K 245 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 m3 (f / 8 + 2147450880) 128 lo);
    [cbn; tauto| reflexivity| reflexivity| lia| | | exact ART3| exact MI3| |].
  { intros i Hi. exists f, 4%nat. rewrite FRS2. split; [left; reflexivity|]. unfold shad, SHB. change (fs_size 4) with 1024. Z.div_mod_to_equations; lia. }
  { eapply (rw_cells_wr_at bsegs m3 _ _ 128 FS3). unfold pj_shadow2. rewrite cells_size_app, cells_size_map_C1, pj_shadow_x_length. reflexivity. }
  { unfold call_ok. rewrite EU. split; [exact ST3|]. split; [rewrite SP2; lia|]. split; [ul|]. split; [ul| Z.div_mod_to_equations; lia]. }
  intros v0 w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 w3 w4 w5 w6 F4 m4 (ART4 & MI4 & WM4 & ST4) PR4 BY4. rewrite EU in ST4, PR4.
  rewrite (ret_pc_even 0xb1b20) by lia.

  destruct (af_frame_release RT AF Σ2 m4 f 4%nat [] ART4 FRS2) as (Σ5 & fl & FLC & NAC & FL0 & FLW & FW & REL).
  change (fs_size 4) with 1024 in FW. replace (f + 1024 - 8) with (f + 1016) in FW by lia. rewrite SP2 in FLW.
  assert (AG4 : forall (P : Z -> Prop), (forall x, P x -> sp' <= x < usp) -> agree_on P m2 m4).
  { intros P HP a Ha. pose proof (HP _ Ha) as H1. rewrite (PR4 a), (MU3 a); [reflexivity| | |].
    - cbn [outside]. split; [ul|]. split; [ul| exact I].
    - left. ul.
    - ul. }
  assert (FRl4 : rw_cells bsegs m4 sp' LC) by (eapply rw_cells_agree_nw; [exact FRl2|]; apply AG4; intros x Hx; rewrite SZ in Hx; lia).
  assert (STp4 : stk bsegs m4 (sp' + 88) (usp - 104)) by (eapply stk_agree_nw; [exact STp2|]; apply AG4; intros x Hx; cbv beta in Hx; lia).
  assert (FRs4 : rw_cells bsegs m4 (usp - 104) (fa_saved cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11))
    by (eapply rw_cells_agree_nw; [exact FRs2|]; apply AG4; intros x Hx; unfold fa_saved in Hx; cbn [cells_size csize Nat.add] in Hx; lia).

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_walkX2 usp sp' f fl lo d n (wz 0xb1b20) gp (wz TPV_A) w0 w1 w2 v0 e1 e2 e3 e4 e5 e6 e7 s7 s8 s9 w3 w4 w5 w6
                             cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 LC F4 fc2 m4);
                   [lia| ul| exact FL0| ul| ul| ul| exact SZ| ul| ul| exact ST4| exact FRl4| exact STp4| exact FRs4| exact FW| exact FLC| exact MI4]|].
  cbv beta. intros ms5 (m5 & RS5 & FC5 & MU5 & WM5 & MI5 & ST5 & FLC5).
  destruct (REL m5 MU5 WM5 FLC5) as (ART5 & FRS5 & LV5 & SP5 & CR5 & AL5 & AM5).
  apply evt_done. apply (aevt_switch RT PMc Σ2 Σ5 K ms5 AL5 AM5).
  revert FC5. apply (ret_st_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 ms5 (fun ms => ms_fcsr ms = fc2 -> aevt Σ5 K ms) RS5).
  intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F5 fc5 FC5. change (fc5 = fc2) in FC5. subst fc5.
  apply (KFIN Σ5 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F5 fc2 m5 FRM2 ART5 MI5 ST5); [| | rewrite LV5; exact LV2| exact FRS5| rewrite SP5; exact SP2| rewrite CR5, CR2; exact CRx].
  - intros a Ha Ho. pose proof (CSEP _ Ha) as (C1 & C2 & C3). rewrite <- (PRES2' a Ha Ho). rewrite (MU5 a), (PR4 a), (MU3 a); [reflexivity| | | |].
    + cbn [outside]. split; [lia|]. split; [lia| exact I].
    + apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LV2; intros e He; exact He| intros e []| lia].
    + lia.
    + cbn [outside]. split; [| exact I]. intros E. apply NAC. rewrite LV2, FRS2. replace fl with (bv_unsigned a) by lia.
      destruct Ha as [H|[H|[H|[H|H]]]]; [exfalso; clear - H E FLW LOW LOR; ul| right; left; exact H
                                        | right; right; left; exact H| destruct H as (? & ? & [] & _)| destruct H as (? & ? & [] & _)].
  - eapply pj_lib_agree; [exact LIB2|]. intros a Ha. pose proof (client_static_range _ (proj1 (lib_fp_static _ Ha))) as R.
    rewrite (MU5 a), (PR4 a), (MU3 a); [reflexivity| | | |].
    + cbn [outside]. unfold SEGTOP_A, SHB in *. split; [lia|]. split; [lia| exact I].
    + right; left. exact (proj1 (lib_fp_static _ Ha)).
    + unfold SEGTOP_A, SHB in *. lia.
    + cbn [outside]. split; [| exact I]. intros E. apply NAC. right; left. replace fl with (bv_unsigned a) by lia. exact (proj1 (lib_fp_static _ Ha)).
Qed.
End WithPM.

Lemma pj_parser_fobj : forall (Σx : rts RT) (mx : mem) (f : Z) (t : list byte),
  rw_cells bsegs mx (f / 8 + 2147450880) (pj_shadow1 t) -> rt_frames RT Σx = [(f, 4%nat)] -> 0 < f -> f mod 64 = 0 ->
  fobj RT Σx mx (f + 160) 80.
Proof.
  intros Σx mx f t FS FRS FPOS F64.
  split; [Z.div_mod_to_equations; lia|]. split; [lia|]. change ((80 + 7) / 8) with 10.
  split; [exists f, 4%nat; rewrite FRS; change (fs_size 4) with 1024; split; [left; reflexivity| lia]|].
  replace (shad (f + 160)) with (f / 8 + 2147450880 + Z.of_nat 20) by (unfold shad, SHB; Z.div_mod_to_equations; lia).
  unfold pj_shadow1, pj_shadow_bytes in FS. cbn [map app repeat] in FS.
  lazymatch type of FS with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?c16 :: ?c17 :: ?c18 :: ?c19 ::
                                        ?d0 :: ?d1 :: ?d2 :: ?d3 :: ?d4 :: ?d5 :: ?d6 :: ?d7 :: ?d8 :: ?d9 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: c15 :: c16 :: c17 :: c18 :: c19 :: d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: d6 :: d7 :: d8 :: d9 :: rest)
      with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15; c16; c17; c18; c19] ++ [d0; d1; d2; d3; d4; d5; d6; d7; d8; d9] ++ rest) in FS end.
  apply Sj_stage1_kit.rw_cells_app in FS. destruct FS as [_ FS]. apply Sj_stage1_kit.rw_cells_app in FS. destruct FS as [FS _].
  cbn [cells_size csize Nat.add] in FS. destruct FS as [[_ HB] _]. exact HB.
Qed.

Lemma pj_doc_shadow : forall (mx : mem) (f : Z) (t : list byte),
  rw_cells bsegs mx (f / 8 + 2147450880) (pj_shadow1 t) -> 0 < f -> f mod 64 = 0 -> bytes_at bsegs mx (shad (f + 184)) [z8; z8].
Proof.
  intros mx f t FS FPOS F64.
  replace (shad (f + 184)) with (f / 8 + 2147450880 + Z.of_nat 23) by (unfold shad, SHB; Z.div_mod_to_equations; lia).
  unfold pj_shadow1, pj_shadow_bytes in FS. cbn [map app repeat] in FS.
  lazymatch type of FS with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?c16 :: ?c17 :: ?c18 :: ?c19 ::
                                        ?c20 :: ?c21 :: ?c22 :: ?d0 :: ?d1 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: c15 :: c16 :: c17 :: c18 :: c19 :: c20 :: c21 :: c22 :: d0 :: d1 :: rest)
      with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15; c16; c17; c18; c19; c20; c21; c22] ++ [d0; d1] ++ rest) in FS end.
  apply Sj_stage1_kit.rw_cells_app in FS. destruct FS as [_ FS]. apply Sj_stage1_kit.rw_cells_app in FS. destruct FS as [FS _].
  cbn [cells_size csize Nat.add] in FS. destruct FS as [[_ HB] _]. exact HB.
Qed.

Lemma pj_shadow_split : forall (mx : mem) (f : Z) (t : list byte),
  rw_cells bsegs mx (f / 8 + 2147450880) (pj_shadow1 t) <->
  rw_cells bsegs mx (shad f) (map C1 pj_shadow_cut) /\ rw_cells bsegs mx (f / 8 + 2147450880 + 80) [CB 48 t].
Proof.
  intros mx f t. unfold pj_shadow1, shad, SHB. change pj_shadow_cut with pj_shadow_bytes.
  rewrite (Sj_stage1_kit.rw_cells_app bsegs mx _ (map C1 pj_shadow_bytes) [CB 48 t]). rewrite cells_size_map_C1, pj_shadow_bytes_length.
  replace (f / 8 + 2147450880 + Z.of_nat 80) with (f / 8 + 2147450880 + 80) by lia. tauto.
Qed.

Lemma pj_pid_cost_bound : forall len, 0 <= len < 2^26 -> pj_pid_costA len + 2^30 + 2^28 + 8 <= FUZZ_COST.
Proof.
  intros len L. change (2^26) with 67108864 in L.
  assert (C : 32 <= Z.max len 32 <= 2^26) by (change (2^26) with 67108864; lia).
  pose proof (al_sbuf_bounds _ C) as B1. pose proof (al_tape_bounds _ C) as B2. pose proof (sc_idx_bounds (Z.max len 32) ltac:(change (2^26) with 67108864; lia)) as B3.
  pose proof (mcost_le (al_sbuf (Z.max len 32)) ltac:(lia)) as M1. pose proof (mcost_le (al_tape (Z.max len 32)) ltac:(lia)) as M2.
  pose proof (mcost_le (sc_idx (Z.max len 32)) ltac:(lia)) as M3.
  pose proof (mcost_small 96 ltac:(lia)) as M4. pose proof (mcost_small 8192 ltac:(lia)) as M5. pose proof (mcost_small 1024 ltac:(lia)) as M6.
  pose proof (mcost_le (len + 64) ltac:(lia)) as M7.
  unfold pj_pid_costA, pid_cost6, S2A_COST, Sj_num_iface.NUMA_CREDIT, FUZZ_COST. change (2^30) with 1073741824. change (2^28) with 268435456. change (3 * 2^31) with 6442450944. lia.
Qed.

Theorem fuzz_one_pjB : fuzz_one_cps RT pj_lib.
Proof using AF RC PDT PDFP PID OKARM.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo
    FDO MST EA0 EA1 ETP D0 BSL BS INLV FRS0 LVPOS LVB CR0 S0C LIB0 IOS NL0 ART0 MI0 ST0 LOW LOR SPT SPA SPLE FRM.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_client_consts RT AF Σ m ART0) as CC0.
  set (usp := bv_unsigned sp) in *. set (n := Z.of_nat (length bs)) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (N0 : 0 <= n < 2^26) by (subst n; lia).
  assert (DR : 0 <= d < 2^64).
  { destruct INLV as [(p & k & Hin & P1 & P2)|(E & DL)]; [| clear - D0 DL; ul].
    pose proof (af_live_range RT AF Σ m p k ART0 Hin) as (R0 & R1 & R2). clear - D0 P1 P2 R1 SP0R N0. ul. }
  match goal with |- cps bsegs _ ?K0 => set (K := K0) end.

  assert (KFIN : pj_fin_k PMc K Σ usp lo ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m (rt_credit RT Σ - FUZZ_COST)).
  { unfold pj_fin_k. intros Σ' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' FRM' ART' MI' ST' PR' LIB' LV' FRS' SP' CR'.
    apply (aevt_done RT PMc). intros c Hc. subst K. cbv beta. split.
    - exists Σ'. split; [| split; [exact LV'| split; [exact FRS'| split; [exact SP'| exact CR']]]].
      eapply ASTA_conseq; [exact Hc|]. intros ms <-. exists m'.
      split; [rewrite ESP; do 16 eexists; reflexivity|]. split; [split; [exact ART'| split; [exact MI'| exact ST']]|].
      split; [rewrite FRS0; exact PR'| exact LIB'].
    - rewrite (asta_eq_fcsr RT Σ' PMc _ c Hc). exact FRM'. }
  eapply cps_conseq; [| intros c [Hc _]; exact Hc| intros c Hc; exact Hc].
  apply (cps_of_aevt RT PMc). subst a0 a1 tp. rewrite ESP. unfold entry_st.

  destruct (pj_prologue usp lo d n ra gp (Z_to_bv 64 TPV_A) t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m
              ST0 ltac:(ul) ltac:(ul) ltac:(ul) SPA CC0 MI0) as (sp' & SPR & SPA' & W0).
  apply (aevt_evt RT AF PMc MST). eapply evt_cut; [exact W0|]. cbv beta.
  intros ms1 (m1 & a1' & a2' & j0 & j1 & j2 & j3 & j4 & j5 & j6 & j7 & jr & -> & MU1 & WM1 & MI1 & ST1 & FRl1 & STp1 & FRs1). apply evt_done. clear W0.
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 sp' ART0 ltac:(ul)); [| exact WM1].
    intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. ul. }
  assert (LIB1 : pj_lib m1).
  { apply (pj_lib_agree m m1 LIB0). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. pose proof (client_static_range _ (proj1 (lib_fp_static x Hx))).
    cbn [outside]. split; [ul| exact I]. }
  assert (BS1 : bytes_at bsegs m1 d bs).
  { apply (bytes_at_agree bsegs m m1 _ _ BS). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbv beta in Hx. cbn [outside]. split; [| exact I].
    destruct INLV as [(p & k & Hin & P1 & P2)| (E & DL)]; [| subst n; rewrite E in Hx; cbn [length] in Hx; lia].
    pose proof (af_live_range RT AF Σ m p k ART0 Hin) as (R0 & R1 & R2). clear - Hx P1 P2 R1 SPR LOW LOR. subst n. ul. }
  assert (PRES1 : forall a : word, aclient (rt_live RT Σ) [] usp (bv_unsigned a) -> outside LIB_FP (bv_unsigned a) -> m1 a = m a).
  { intros a Ha _. apply MU1. cbn [outside]. split; [| exact I]. rewrite <- FRS0 in Ha. destruct (aclient_split_c RT AF Σ m usp _ ART0 Ha); [lia| ul]. }
  assert (EU1 : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; ul).
  clear MU1 WM1 ST0 MI0.

  unfold entry_st.
  eapply (aevt_smalloc4 RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 lo eq_refl);
    [rewrite FRS0; cbn; unfold FRAMES_MAX; lia| unfold FUZZ_COST in CR0; lia| exact ART1| exact MI1| |].
  { unfold call_ok. rewrite EU1. split; [exact ST1|]. split; [ul|]. split; [ul|]. split; [ul| Z.div_mod_to_equations; lia]. }
  intros Σ1 f v0 v1 v2 e1 e2 e3 e4 e5 e6 e7 v3 v4 v5 v6 F1 m2 (ART2 & MI2 & WM2 & ST2) PRES2 WRF WRS FRS1 LV1 SP1 CR1 FPOS F64 FTOP.
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even 0xb1670) by lia. rewrite FRS0 in FRS1.
  change (fs_size 4) with 1024 in *. change (1024 / 8) with 128 in WRS.
  assert (INF1 : In (f, 4%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
  pose proof (fframe_ranges RT AF Σ1 m2 f 4 ART2 INF1) as (_ & FR1' & _ & SHB0 & SHT).
  pose proof (af_fshadow_apart RT AF Σ1 m2 f 4 ART2 INF1) as (FSL & FSF). pose proof (FSF f 4%nat INF1) as FSELF.
  pose proof (af_frames_align RT AF Σ1 m2 f 4 ART2 INF1) as (_ & FSEG). pose proof (af_frames_range RT AF Σ1 m2 f 4 ART2 INF1) as (_ & _ & _ & FLV).
  change (fs_size 4) with 1024 in *. rewrite SP1 in FR1', SHT.
  assert (SHF : shad (f + 1024) = shad f + 128) by (unfold shad; Z.div_mod_to_equations; lia).
  rewrite SHF in *. unfold shad, SHB in SHB0, SHT, FSELF, FSL, FSF, WRS.
  assert (FD0 : 0 <= f / 8) by (apply Z.div_pos; lia).
  assert (SHF0 : shad (f + fs_size 4) = f / 8 + 2147450880 + 128) by (change (fs_size 4) with 1024; unfold shad, SHB; Z.div_mod_to_equations; lia).

  assert (AG12 : forall (P : Z -> Prop), (forall x, P x -> sp' <= x < usp) -> agree_on P m1 m2).
  { intros P HP a Ha. apply PRES2. left. pose proof (HP _ Ha). ul. }
  assert (FRl2 : rw_cells bsegs m2 sp' (pj_locals0 j0 j1 j2 j3 j4 j5 j6 j7 jr)).
  { eapply rw_cells_agree_nw; [exact FRl1|]. apply AG12. intros x Hx. unfold pj_locals0 in Hx. cbn [cells_size csize Nat.add] in Hx. lia. }
  assert (FRs2 : rw_cells bsegs m2 (usp - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { eapply rw_cells_agree_nw; [exact FRs1|]. apply AG12. intros x Hx. unfold fa_saved in Hx. cbn [cells_size csize Nat.add] in Hx. lia. }
  assert (STp2 : stk bsegs m2 (sp' + 88) (usp - 104)) by (eapply stk_agree_nw; [exact STp1|]; apply AG12; intros x Hx; cbv beta in Hx; lia).
  assert (LIB2 : pj_lib m2).
  { apply (pj_lib_agree m1 m2 LIB1). apply (agree_of_pres _ _ _ _ _ _ PRES2). intros x Hx. right; left. exact (proj1 (lib_fp_static x Hx)). }
  assert (BS2 : bytes_at bsegs m2 d bs).
  { apply (bytes_at_agree bsegs m1 m2 _ _ BS1). apply (agree_of_pres _ _ _ _ _ _ PRES2). intros x Hx. cbv beta in Hx.
    destruct INLV as [(p & k & Hin & P1 & P2)| (E & DL)]; [| subst n; rewrite E in Hx; cbn [length] in Hx; lia].
    right; right; left. exists p, k. split; [exact Hin| lia]. }
  assert (PRES2' : forall a : word, aclient (rt_live RT Σ) [] usp (bv_unsigned a) -> outside LIB_FP (bv_unsigned a) -> m2 a = m a).
  { intros a Ha Ho. rewrite <- (PRES1 a Ha Ho). apply PRES2. apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| intros e []| lia]. }
  clear PRES1 PRES2 AG12 FRl1 FRs1 STp1 ST1 MI1 LIB1 BS1 ART1.

  destruct (wr_at_rw_CB m2 f 32 (wr_at_sub m2 f 1016 f 32 WRF ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jH & FH2).
  change (Z.to_nat 32) with 32%nat in FH2.
  apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FH2; [| reflexivity]. cbn [mk_CB_cells app] in FH2.
  destruct (wr_at_rw_CB m2 (f + 160) 80 (wr_at_sub m2 f 1016 (f + 160) 80 WRF ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jP & FP2).
  change (Z.to_nat 80) with 80%nat in FP2.
  apply (rw_cells_split_CB bsegs _ _ [] 80 _ [] [1; 7; 8; 1; 3; 4; 24; 8; 1; 7; 16]%nat) in FP2; [| reflexivity]. cbn [mk_CB_cells app] in FP2.
  destruct (wr_at_rw_CB m2 (f + 32) 88 (wr_at_sub m2 f 1016 (f + 32) 88 WRF ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jB & FB2).
  change (Z.to_nat 88) with 88%nat in FB2.
  destruct (wr_at_rw_CB m2 (f + 272) 288 (wr_at_sub m2 f 1016 (f + 272) 288 WRF ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jO & FO2).
  change (Z.to_nat 288) with 288%nat in FO2.
  destruct (wr_at_rw_CB m2 (f / 8 + 2147450880) 128 WRS ltac:(lia)) as (jS & FS2).
  change (Z.to_nat 128) with 128%nat in FS2.
  apply (rw_cells_split_CB bsegs _ _ [] 128 _ []
           [1;1;1;1;1;1;1;1;1;1; 1;1;1;1;1;1;1;1;1;1; 1;1;1;1;1;1;1;1;1;1; 1;1;1;1;1;1;1;1;1;1; 1;1;1;1;1;1;1;1;1;1; 1;1;1;1;1;1;1;1;1;1; 1;1;1;1;1;1;1;1;1;1; 1;1;1;1;1;1;1;1;1;1; 48]%nat) in FS2; [| reflexivity].
  cbn [mk_CB_cells app] in FS2.
  lazymatch type of FS2 with rw_cells _ _ _ ?cs =>
    lazymatch eval cbv in (rev (tl (rev cs))) with ?cs80 =>
    lazymatch eval cbv in (last cs (CB 0 [])) with CB 48 ?t =>
      let ls := constr:(map (fun c => match c with CB _ l => l | _ => [] end) cs80) in
      let ls' := eval cbv in ls in
      change (rw_cells bsegs m2 (f / 8 + 2147450880) (pj_shadow0 ls' t)) in FS2; set (tS := t) in FS2; clearbody tS; set (lS := ls') in FS2;
      assert (LS : length lS = 80%nat) by reflexivity; clearbody lS
    end end end.
  repeat match type of FH2 with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "h" in set (j := t) in FH2; clearbody j end.
  repeat match type of FP2 with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "q" in set (j := t) in FP2; clearbody j end.
  lazymatch type of FH2 with rw_cells _ _ _ [CB 8 ?x0; CB 8 ?x1; CB 8 ?x2; CB 8 ?x3] => change (rw_cells bsegs m2 f (fz_hdr (CB 8 x0) (CB 8 x1) (CB 8 x2) x3)) in FH2 end.
  lazymatch type of FP2 with rw_cells _ _ _ [CB 1 ?x0; CB 7 ?x1; CB 8 ?x8; CB 1 ?x16; CB 3 ?x17; CB 4 ?x20; CB 24 ?x24; CB 8 ?x48; CB 1 ?x56; CB 7 ?x57; CB 16 ?x64] =>
    change (rw_cells bsegs m2 (f + 160) (fz_parser (CB 1 x0) x1 (CB 8 x8) (CB 1 x16) x17 (CB 4 x20) (CB 24 x24) (CB 8 x48) (CB 1 x56) x57 (CB 16 x64))) in FP2 end.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_walk1 usp sp' f lo d n gp (Z_to_bv 64 TPV_A) v0 v1 v2 e1 e2 e3 e4 e5 e6 e7 s2 s3 s4 s7 s8 s9 s10 v3 v4 v5 v6
                             j0 j1 j2 j3 j4 j5 j6 j7 jr _ _ _ _ tS lS _ _ _ _ _ _ _ _ _ _ _ F1 fc m2 LS);
                   [lia| lia| lia| lia| exact FSELF| ul| ul| lia| ul| lia| subst n; lia| exact FRl2| exact FH2| exact FP2| exact FS2| exact MI2]|].
  cbv beta. intros ms3 (m3 & -> & MU3 & WM3 & MI3 & FRl3 & FH3 & FP3 & FS3). apply evt_done. unfold lf_regs.

  assert (CLW : forall mx my W, munch W mx my -> Forall (fun iv => (sp' <= fst iv /\ snd iv <= usp) \/ (f <= fst iv /\ snd iv <= f + 1016)
                                                                 \/ (f / 8 + 2147450880 <= fst iv /\ snd iv <= f / 8 + 2147450880 + 128)) W ->
                 agree_on (fun a => ~ aclient (rt_live RT Σ1) (rt_frames RT Σ1) sp' a) mx my).
  { intros mx my W MU HW a Ha. apply MU. clear - HW Ha FRS1 SPR SPT FD0. induction W as [|[lo' hi'] W IH]; [exact I|].
    apply Forall_cons_iff in HW. destruct HW as [H1 HW]. cbn [outside fst snd] in *. split; [| exact (IH HW)].
    intros Hin. apply Ha. destruct H1 as [H1|[H1|H1]].
    - left. unfold USTACK_TOP in *. lia.
    - right; right; right; left. exists f, 4%nat. rewrite FRS1. split; [left; reflexivity| change (fs_size 4) with 1024; lia].
    - right; right; right; right. exists f, 4%nat. rewrite FRS1. split; [left; reflexivity| unfold shad, SHB; change (fs_size 4) with 1024; Z.div_mod_to_equations; lia]. }
  assert (ART3 : ART RT Σ1 m3).
  { apply (art_client_write RT AF Σ1 m2 m3 sp' ART2 ltac:(rewrite SP1; ul)); [| exact WM3]. eapply CLW; [exact MU3|].
    unfold pj_W1. repeat constructor; cbn [fst snd]; lia. }
  assert (ST3 : stk bsegs m3 lo sp').
  { apply (stk_agree bsegs m2 m3 _ _ ST2); [| exact WM3]. apply (agree_of_munch _ _ _ _ MU3). intros x Hx. unfold pj_W1. cbn [outside]. repeat split; lia. }

  assert (MSTEP : forall (mx : mem) (t' : list byte) (dd nn : Z), ART RT Σ1 mx -> rw_cells bsegs mx (f / 8 + 2147450880) (pj_shadow1 t') -> wmono bsegs m2 mx ->
            f + 160 <= dd -> dd + nn <= f + 240 -> 0 < nn -> checked_dst RT Σ1 mx (Z_to_bv 64 sp') dd nn).
  { intros mx t' dd nn ARTx FSx WMx D1 D2 NP. destruct (pj_parser_fobj Σ1 mx f t' FSx FRS1 FPOS F64) as (A8 & _ & _ & HB).
    change (Z.to_nat ((80 + 7) / 8)) with 10%nat in HB. unfold checked_dst. rewrite EU1. split; [| split].
    - intros _. split; [apply (acc_sub bsegs mx (f + 160) 80); [exact (acc_zero_run bsegs mx (f + 160) 10 A8 ltac:(lia) HB)| lia| lia]|].
      right; left. exists f, 4%nat. change (fs_size 4) with 1024. split; [exact INF1| lia].
    - intros i Hi. right; right; right; left. exists f, 4%nat. change (fs_size 4) with 1024. split; [exact INF1| lia].
    - apply (wr_at_sub mx f 1016); [exact (wr_at_transport bsegs m2 mx f 1016 WRF WMx)| lia| lia| lia]. }
  assert (COK : forall mx, stk bsegs mx lo sp' -> call_ok RT Σ1 mx (Z_to_bv 64 sp') lo).
  { intros mx STx. unfold call_ok. rewrite EU1, SP1. split; [exact STx|]. split; [ul|]. split; [ul|]. split; [ul| clear - SPA'; Z.div_mod_to_equations; lia]. }
  eapply (aevt_memsetP RT RC PMc FDO MST Σ1 K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc m3 (f + 184) 24 z8 lo eq_refl eq_refl eq_refl
            ltac:(ul) ltac:(lia) (MSTEP m3 tS (f + 184) 24 ART3 FS3 WM3 ltac:(lia) ltac:(lia) ltac:(lia)) ART3 MI3 (COK m3 ST3)).
  intros w0 w1 w2 g1 g2 g3 g4 g5 g6 g7 w3 w4 w5 w6 F4 m4 (ART4 & MI4 & WM4 & ST4) PRES4 BY4. rewrite EU1 in ST4, PRES4.
  rewrite (ret_pc_even 0xb184c) by lia. change (Z.to_nat 24) with 24%nat in BY4.

  assert (RTW : forall mx my dd nn, rt_pres_ex (rt_live RT Σ1) (rt_frames RT Σ1) sp' dd nn mx my -> f <= dd -> dd + nn <= f + 1016 ->
                 forall (P : Z -> Prop), (forall x, P x -> (sp' <= x < usp \/ (f <= x < f + 1016 /\ ~ (dd <= x < dd + nn)) \/ f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 128)) ->
                 agree_on P mx my).
  { intros mx my dd nn PR D1 D2 P HP a Ha. destruct (HP _ Ha) as [H|[[H1 H2]|H]]; apply PR.
    - left. ul. - ul.
    - right; right; right; left. exists f, 4%nat. change (fs_size 4) with 1024. split; [exact INF1| lia]. - exact H2.
    - right; right; right; right. exists f, 4%nat. rewrite SHF0. split; [exact INF1| unfold shad, SHB; lia]. - ul. }
  lazymatch type of FP3 with rw_cells _ _ _ (fz_parser _ ?x1 _ _ ?x17 _ (CB 24 ?x24) (CB 8 ?x48) (CB 1 ?x56) ?x57 (CB 16 ?x64)) =>
    assert (FP4 : rw_cells bsegs m4 (f + 160) (fz_parser (C1 (Z_to_bv 8 0)) x1 (C8 (Z_to_bv 64 0)) (C1 (Z_to_bv 8 0)) x17 (C4 (Z_to_bv 64 12))
                                                        (CB 24 (repeat z8 24)) (CB 8 x48) (CB 1 x56) x57 (CB 16 x64)));
    [ unfold fz_parser in *;
      apply (cells_mid_update m3 m4 (f + 160) [C1 (Z_to_bv 8 0); CB 7 x1; C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 3 x17; C4 (Z_to_bv 64 12)]
               24 x24 (repeat z8 24) [CB 8 x48; CB 1 x56; CB 7 x57; CB 16 x64] FP3); [| exact WM4| | reflexivity];
      [ apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES4); intros x (Hx & Hn); cbn [app cells_size csize Nat.add] in Hx, Hn;
        split; [right; right; right; left; exists f, 4%nat; change (fs_size 4) with 1024; split; [exact INF1| lia]| lia]
      | cbn [cells_size csize Nat.add]; replace (f + 160 + Z.of_nat 24) with (f + 184) by lia; exact BY4 ] |]
  end.
  assert (FS4 : rw_cells bsegs m4 (f / 8 + 2147450880) (pj_shadow1 tS)).
  { eapply rw_cells_agree_nw; [exact FS3|]. eapply RTW; [exact PRES4| lia| lia|]. intros x Hx. unfold pj_shadow1 in Hx.
    rewrite cells_size_app, cells_size_map_C1, pj_shadow_bytes_length in Hx. cbn [cells_size csize Nat.add] in Hx. right; right. lia. }

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_walk2 usp sp' f d n (Z_to_bv 64 0xb184c) gp (Z_to_bv 64 TPV_A) w0 w1 w2 (Z_to_bv 64 (f + 184)) g1 g2 g3 g4 g5 g6 g7 s8 s9 w3 w4 w5 w6
                             _ _ _ _ _ _ _ F4 fc m4 FPOS ltac:(ul) FP4 MI4)|].
  cbv beta. intros ms5 (m5 & -> & MU5 & WM5 & MI5 & FP5). apply evt_done. unfold lf_regs.
  assert (ART5 : ART RT Σ1 m5).
  { apply (art_client_write RT AF Σ1 m4 m5 sp' ART4 ltac:(rewrite SP1; ul)); [| exact WM5]. eapply CLW; [exact MU5|]. repeat constructor; cbn [fst snd]; lia. }
  assert (ST5 : stk bsegs m5 lo sp').
  { apply (stk_agree bsegs m4 m5 _ _ ST4); [| exact WM5]. apply (agree_of_munch _ _ _ _ MU5). intros x Hx. cbn [outside]. repeat split; ul. }
  assert (FS5 : rw_cells bsegs m5 (f / 8 + 2147450880) (pj_shadow1 tS)).
  { eapply rw_cells_agree_nw; [exact FS4|]. apply (agree_of_munch _ _ _ _ MU5). intros x Hx. unfold pj_shadow1 in Hx.
    rewrite cells_size_app, cells_size_map_C1, pj_shadow_bytes_length in Hx. cbn [cells_size csize Nat.add] in Hx. cbn [outside]. split; [lia| exact I]. }

  eapply (aevt_memsetP RT RC PMc FDO MST Σ1 K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F4 fc m5 (f + 224) 16 z8 lo eq_refl eq_refl eq_refl
            ltac:(ul) ltac:(lia) (MSTEP m5 tS (f + 224) 16 ART5 FS5 (wmono_trans _ _ _ _ WM3 (wmono_trans _ _ _ _ WM4 WM5)) ltac:(lia) ltac:(lia) ltac:(lia)) ART5 MI5 (COK m5 ST5)).
  intros x0 x1 x2 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 F6 m6 (ART6 & MI6 & WM6 & ST6) PRES6 BY6. rewrite EU1 in ST6, PRES6.
  rewrite (ret_pc_even 0xb186c) by lia. change (Z.to_nat 16) with 16%nat in BY6.
  lazymatch type of FP5 with rw_cells _ _ _ (fz_parser _ ?x1 _ _ ?x17 _ _ _ _ ?x57 (CB 16 ?x64)) =>
    assert (FP6 : rw_cells bsegs m6 (f + 160) (parser_init x1 x17 x57));
    [ unfold parser_init, fz_parser in *;
      apply (cells_mid_update m5 m6 (f + 160) [C1 (Z_to_bv 8 0); CB 7 x1; C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 3 x17; C4 (Z_to_bv 64 12); CB 24 (repeat z8 24); C8 (Z_to_bv 64 4294967295); C1 (Z_to_bv 8 0); CB 7 x57]
               16 x64 (repeat z8 16) [] FP5); [| exact WM6| | reflexivity];
      [ apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES6); intros x (Hx & Hn); cbn [app cells_size csize Nat.add] in Hx, Hn;
        split; [right; right; right; left; exists f, 4%nat; change (fs_size 4) with 1024; split; [exact INF1| lia]| lia]
      | cbn [cells_size csize Nat.add]; replace (f + 160 + Z.of_nat 64) with (f + 224) by lia; exact BY6 ] |]
  end.
  assert (FS6 : rw_cells bsegs m6 (f / 8 + 2147450880) (pj_shadow1 tS)).
  { eapply rw_cells_agree_nw; [exact FS5|]. eapply RTW; [exact PRES6| lia| lia|]. intros x Hx. unfold pj_shadow1 in Hx.
    rewrite cells_size_app, cells_size_map_C1, pj_shadow_bytes_length in Hx. cbn [cells_size csize Nat.add] in Hx. right; right. lia. }

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_walk3 usp sp' f d n (Z_to_bv 64 0xb186c) gp (Z_to_bv 64 TPV_A) x0 x1 x2 (Z_to_bv 64 (f + 224)) y1 y2 y3 y4 y5 y6 y7 s8 s9 x3 x4 x5 x6 F6 fc m6
                             FPOS ltac:(ul) ltac:(ul) ltac:(ul) MI6)|].
  cbv beta. intros ms7 <-. apply evt_done. unfold lf_regs.

  assert (AG36 : forall (P : Z -> Prop), (forall x, P x -> (sp' <= x < usp \/ (f <= x < f + 1016 /\ ~ (f + 160 <= x < f + 240)) \/ f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 128)) -> agree_on P m3 m6).
  { intros P HP. eapply agree_trans; [| eapply RTW; [exact PRES6| lia| lia| intros x Hx; destruct (HP _ Hx) as [H|[H|H]]; [left; exact H| right; left; split; lia| right; right; exact H]]].
    eapply agree_trans; [| apply (agree_of_munch _ _ _ _ MU5); intros x Hx; destruct (HP _ Hx) as [H|[H|H]]; cbn [outside]; (split; [ul| exact I])].
    eapply RTW; [exact PRES4| lia| lia| intros x Hx; destruct (HP _ Hx) as [H|[H|H]]; [left; exact H| right; left; split; lia| right; right; exact H]]. }
  assert (AG26f : forall (P : Z -> Prop), (forall x, P x -> (f + 32 <= x < f + 160 \/ f + 240 <= x < f + 1016)) -> agree_on P m2 m6).
  { intros P HP. eapply agree_trans; [| apply AG36; intros x Hx; right; left; pose proof (HP _ Hx); lia].
    apply (agree_of_munch _ _ _ _ MU3). intros x Hx. pose proof (HP _ Hx). unfold pj_W1. cbn [outside]. repeat split; ul. }
  assert (FB6 : rw_cells bsegs m6 (f + 32) [CB 88 jB]) by (eapply rw_cells_agree_nw; [exact FB2|]; apply AG26f; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia).
  assert (FO6 : rw_cells bsegs m6 (f + 272) [CB 288 jO]) by (eapply rw_cells_agree_nw; [exact FO2|]; apply AG26f; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia).
  assert (AG26 : forall (P : Z -> Prop), (forall x, P x -> (sp' + 88 <= x < usp)) -> agree_on P m2 m6).
  { intros P HP. eapply agree_trans; [| apply AG36; intros x Hx; left; pose proof (HP _ Hx); lia].
    apply (agree_of_munch _ _ _ _ MU3). intros x Hx. pose proof (HP _ Hx). unfold pj_W1. cbn [outside]. repeat split; ul. }
  assert (FRl6 : rw_cells bsegs m6 sp' (pj_locals1 j0 j1 j2 j3 j4 j5 j6 f jr)).
  { eapply rw_cells_agree_nw; [exact FRl3|]. apply AG36. intros x Hx. unfold pj_locals1 in Hx. cbn [cells_size csize Nat.add] in Hx. left. ul. }
  assert (FH6 : rw_cells bsegs m6 f (fz_hdr (C8 (Z_to_bv 64 0x41b58ab3)) (C8 (Z_to_bv 64 0x13300)) (C8 (Z_to_bv 64 0xb15fc)) h2)).
  { eapply rw_cells_agree_nw; [exact FH3|]. apply AG36. intros x Hx. unfold fz_hdr in Hx. cbn [cells_size csize Nat.add] in Hx. right; left. split; lia. }
  assert (FRs6 : rw_cells bsegs m6 (usp - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { eapply rw_cells_agree_nw; [exact FRs2|]. apply AG26. intros x Hx. unfold fa_saved in Hx. cbn [cells_size csize Nat.add] in Hx. lia. }
  assert (STp6 : stk bsegs m6 (sp' + 88) (usp - 104)) by (eapply stk_agree_nw; [exact STp2|]; apply AG26; intros x Hx; cbv beta in Hx; lia).
  assert (NCL : forall x, (f <= x < f + 1024 \/ f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 128 \/ sp' <= x < usp) ->
                 client_static x \/ in_live (rt_live RT Σ) x -> False).
  { intros x Hx [H|H].
    - pose proof (client_static_range _ H) as R. clear - Hx R FSEG SHB0 SPR LOW LOR SP0R. unfold SEGTOP_A, SHB in *. ul.
    - destruct H as (p & k & Hin & Hr). rewrite <- LV1 in Hin. pose proof (FLV p k Hin) as Y1. pose proof (FSL p k Hin) as Y2.
      pose proof (af_live_range RT AF Σ1 m2 p k ART2 Hin) as (_ & Y3 & _). rewrite SP1 in Y3. clear - Hx Hr Y1 Y2 Y3 LOW LOR SPR. ul. }
  assert (AGW : forall P : Z -> Prop,
            (forall x, P x -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) sp' x /\ ~ (f <= x < f + 1024 \/ f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 128 \/ sp' <= x < usp)) ->
            agree_on P m2 m6).
  { intros P HP a Ha. destruct (HP _ Ha) as [CL NR].
    rewrite (PRES6 a), (MU5 a), (PRES4 a), (MU3 a); [reflexivity| | | | | |].
    - unfold pj_W1. cbn [outside]. repeat split; lia.
    - exact CL. - lia.
    - cbn [outside]. split; [lia| exact I].
    - exact CL. - lia. }
  assert (LIB6 : pj_lib m6).
  { apply (pj_lib_agree m2 m6 LIB2). apply AGW. intros x Hx. split; [right; left; exact (proj1 (lib_fp_static x Hx))|].
    intros E. exact (NCL x E (or_introl (proj1 (lib_fp_static x Hx)))). }
  assert (BS6 : bytes_at bsegs m6 d bs).
  { apply (bytes_at_agree bsegs m2 m6 _ _ BS2). apply AGW. intros x Hx. cbv beta in Hx.
    destruct INLV as [(p & k & Hin & P1 & P2)| (E0 & DL)]; [| subst n; rewrite E0 in Hx; cbn [length] in Hx; lia].
    assert (IL : in_live (rt_live RT Σ) x) by (exists p, k; split; [exact Hin| subst n; lia]).
    split; [right; right; left; rewrite LV1; exact IL| intros E; exact (NCL x E (or_intror IL))]. }
  assert (PRES6' : forall a : word, aclient (rt_live RT Σ) [] usp (bv_unsigned a) -> outside LIB_FP (bv_unsigned a) -> m6 a = m a).
  { intros a Ha Ho. rewrite <- (PRES2' a Ha Ho). apply (AGW (fun x => x = bv_unsigned a)); [| reflexivity]. intros x ->.
    split; [apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LV1; intros e He; exact He| intros e []| lia]|]. intros E.
    destruct Ha as [H|[H|[H|[H|H]]]]; [clear - H E FR1' SHT LOW LOR SPR; ul| exact (NCL _ E (or_introl H))| exact (NCL _ E (or_intror H))
                                      | destruct H as (? & ? & [] & _)| destruct H as (? & ? & [] & _)]. }
  clear AGW AG26 AG26f AG36 PRES6 PRES4 MU3 MU5 WM3 WM4 WM5 WM6 FRl2 FRl3 FH2 FH3 FP2 FP3 FP4 FP5 FS2 FS3 FS4 FS5 FB2 FO2 ART2 ART3 ART4 ART5 MI2 MI3 MI4 MI5 ST2 ST3 ST4 ST5 STp2 FRs2 LIB2 BS2 PRES2' BY4 BY6 CLW RTW MSTEP COK.

  pose proof FRl6 as FRl6'. unfold pj_locals1 in FRl6'.
  lazymatch type of FRl6' with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) with ([c0; c1; c2; c3; c4; c5; c6; c7] ++ rest) in FRl6' end.
  apply Sj_stage1_kit.rw_cells_app in FRl6'. destruct FRl6' as [FRlo6 RESC6]. cbn [cells_size csize Nat.add] in RESC6.
  replace (sp' + Z.of_nat 64) with (sp' + 64) in RESC6 by lia.
  pose proof (pj_parser_fobj Σ1 m6 f tS FS6 FRS1 FPOS F64) as FOBJ6.
  replace (f + 184) with (f + 160 + 24) by lia. subst n.
  lazymatch type of FP6 with rw_cells _ _ _ (parser_init ?x1 ?x17 ?x57) =>
  eapply (aevt_rt RT PMc Σ1 K _ _
           (PID Σ1 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F6 fc m6 (f + 160) (sp' + 64) d bs x1 x17 x57 jr lo
                FDO MST eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl D0 BSL BS6 ltac:(rewrite LV1; exact INLV)
                FOBJ6 FP6 ltac:(rewrite EU1; lia) ltac:(ul) ltac:(clear - SPA'; Z.div_mod_to_equations; lia) RESC6
                ltac:(rewrite LV1; exact LVPOS) ltac:(rewrite LV1; unfold FUZZ_LIVE in LVB; lia) ltac:(rewrite FRS1; cbn; unfold PID_FRAMES, FRAMES_MAX; lia)
                ltac:(pose proof (pj_pid_cost_bound _ N0); lia) LIB6 ART6 MI6 ltac:(rewrite EU1; exact ST6) ltac:(rewrite SP1; lia) ltac:(rewrite EU1; ul)
                ltac:(rewrite EU1; ul) ltac:(rewrite EU1; clear - SPA'; Z.div_mod_to_equations; lia) FRM)); [exact FRM|]
  end.
  intros c PP. cbv beta zeta in PP. destruct PP as (Σ2 & cp & impl & idx & oc & ia & tape & sbuf & HA & LV2 & CP & ALS & FRS2 & SP2 & CR2).
  eexists Σ2, _. split; [exact HA|].
  intros ms' (v & m7 & RS & (ART7 & MI7 & ST7) & PRES7 & (r & j20 & RESC7 & R64 & OKR & RZ) & LIB7 & PD7 & FOBJ7 & DOC7) FRM7.
  destruct RS as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F7 & fc7 & ->). cbn [ms_fcsr] in FRM7.
  rewrite EU1 in ST7, PRES7. rewrite (ret_pc_even 0xb1888) by lia. rewrite FRS1 in FRS2, PRES7. rewrite SP1 in SP2.
  set (n := Z.of_nat (length bs)) in *. replace (f + 160 + 24) with (f + 184) in * by lia.
  assert (INCL2 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ2)) by (intros e He; rewrite LV2, LV1; apply in_or_app; right; do 6 right; exact He).

  assert (AG67 : forall (P : Z -> Prop), (forall x, P x -> (sp' <= x < usp /\ ~ (sp' + 64 <= x < sp' + 88)) \/ (f <= x < f + 1016 /\ ~ (f + 160 <= x < f + 240)) \/ (f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 128)) ->
                 agree_on P m6 m7).
  { intros P HP a Ha. apply PRES7.
    - destruct (HP _ Ha) as [[H1 H2]|[[H1 H2]|H]]; [left; ul| right; right; right; left| right; right; right; right];
        [exists f, 4%nat; split; [left; reflexivity| change (fs_size 4) with 1024; lia]
        | exists f, 4%nat; split; [left; reflexivity| unfold shad, SHB; change (fs_size 4) with 1024; Z.div_mod_to_equations; lia]].
    - unfold pid_XA, SJ_W. cbn [outside]. unfold SEGTOP_A, SHB in FSEG, SHB0.
      destruct (HP _ Ha) as [[H1 H2]|[[H1 H2]|H]]; (repeat split; try exact I); ul. }
  assert (FB7 : rw_cells bsegs m7 (f + 32) [CB 88 jB]) by (eapply rw_cells_agree_nw; [exact FB6|]; apply AG67; intros x Hx; cbn [cells_size csize Nat.add] in Hx; right; left; split; lia).
  assert (FO7 : rw_cells bsegs m7 (f + 272) [CB 288 jO]) by (eapply rw_cells_agree_nw; [exact FO6|]; apply AG67; intros x Hx; cbn [cells_size csize Nat.add] in Hx; right; left; split; lia).
  assert (FRlo7 : rw_cells bsegs m7 sp' [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 8 j6; C8 (Z_to_bv 64 f)]).
  { eapply rw_cells_agree_nw; [exact FRlo6|]. apply AG67. intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. split; [ul| lia]. }
  assert (STp7 : stk bsegs m7 (sp' + 88) (usp - 104)) by (eapply stk_agree_nw; [exact STp6|]; apply AG67; intros x Hx; cbv beta in Hx; left; split; [lia| lia]).
  assert (FRs7 : rw_cells bsegs m7 (usp - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { eapply rw_cells_agree_nw; [exact FRs6|]. apply AG67. intros x Hx. unfold fa_saved in Hx. cbn [cells_size csize Nat.add] in Hx. left. split; [lia| lia]. }
  assert (FH7 : rw_cells bsegs m7 f (fz_hdr (C8 (Z_to_bv 64 0x41b58ab3)) (C8 (Z_to_bv 64 0x13300)) (C8 (Z_to_bv 64 0xb15fc)) h2)).
  { eapply rw_cells_agree_nw; [exact FH6|]. apply AG67. intros x Hx. unfold fz_hdr in Hx. cbn [cells_size csize Nat.add] in Hx. right; left. split; lia. }
  assert (FS7 : rw_cells bsegs m7 (f / 8 + 2147450880) (pj_shadow1 tS)).
  { eapply rw_cells_agree_nw; [exact FS6|]. apply AG67. intros x Hx. unfold pj_shadow1 in Hx. rewrite cells_size_app, cells_size_map_C1, pj_shadow_bytes_length in Hx.
    cbn [cells_size csize Nat.add] in Hx. right; right. lia. }
  assert (PRES7' : forall a : word, aclient (rt_live RT Σ) [] usp (bv_unsigned a) -> outside LIB_FP (bv_unsigned a) -> m7 a = m a).
  { intros a Ha Ho. rewrite <- (PRES6' a Ha Ho). apply PRES7.
    - apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LV1; intros e He; exact He| intros e []| lia].
    - unfold pid_XA. cbn [outside]. split; [| split; [| unfold LIB_FP in Ho; unfold SJ_W; cbn [outside] in Ho |- *; repeat split; try exact I; lia]].
      + intros E. refine (NCL (bv_unsigned a) _ _); [left; clear - E; lia|].
        destruct Ha as [H|[H|[H|[H|H]]]]; [exfalso; clear - H E FR1' LOW LOR SPR; ul| left; exact H| right; exact H| destruct H as (? & ? & [] & _)| destruct H as (? & ? & [] & _)].
      + destruct Ha as [H|[H|[H|[H|H]]]]; [clear - H SPR; lia| | | destruct H as (? & ? & [] & _)| destruct H as (? & ? & [] & _)];
          intros E; refine (NCL (bv_unsigned a) _ _); [right; right; clear - E SPR; lia| left; exact H| right; right; clear - E SPR; lia| right; exact H].
  }
  clear AG67 FRlo6 RESC6 FOBJ6 FP6 FS6 FH6 FB6 FO6 FRl6 FRs6 STp6 ST6 MI6 ART6 LIB6 PRES6'.

  destruct (Z.eq_dec (bv_unsigned r) 0) as [RZ0|RNZ].
  2: {
    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut; [eapply (pj_walkG_err usp sp' f d n _ gp (Z_to_bv 64 TPV_A) u0 u1 u2 v b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 (f + 184)) s8 s9 u3 u4 u5 u6 r j20 F7 fc7 m7
                               FPOS ltac:(ul) ltac:(ul) ltac:(ul) ltac:(pose proof (bv_unsigned_in_range 64 r); lia) RESC7 MI7)|].
    cbv beta. intros ms8 <-. apply evt_done.
    apply (pj_tail PMc FDO MST Σ Σ2 K usp sp' f lo d n gp u0 u1 u2 (Z_to_bv 64 64) b2 b3 b4 b5 b6 b7 (Z_to_bv 64 (f + 184)) s8 s9 u3 u4 u5 u6
             ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ([CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 8 j6; C8 (Z_to_bv 64 f)] ++ res_cellsA (f + 184) r j20)
             h2 tS F7 fc7 m m7 (rt_credit RT Σ - FUZZ_COST));
      [lia| exact F64| exact FR1'| exact FSEG| exact FD0| exact FSELF| exact SHB0| exact SHT| exact LOW| exact LOR| exact SPT| exact SPR| exact SPA'
      | exact ART7| exact MI7| exact FRS2| exact INCL2| exact SP2| | rewrite <- LV1; exact PD7| exact ST7| | | exact STp7| exact FRs7| exact FH7| exact FS7| exact LIB7| exact PRES7'| exact FRM7| exact KFIN].
    - pose proof (pj_pid_cost_bound n N0). subst n. lia.
    - unfold res_cellsA. destruct (bv_eqb r (Z_to_bv 64 0)); reflexivity.
    - apply Sj_stage1_kit.rw_cells_app. split; [exact FRlo7|]. cbn [cells_size csize Nat.add]. replace (sp' + Z.of_nat 64) with (sp' + 64) by lia. exact RESC7. }

  assert (ER : r = Z_to_bv 64 0) by (rewrite <- (Z_to_bv_bv_unsigned r), RZ0; reflexivity). subst r.
  destruct OKR as [K64|(_ & tws & sbs & BT & BSB & WFS & SBR & NT & NS)]; [rewrite unsigned_lit in K64 by lia; exfalso; lia|].
  pose proof (RZ eq_refl) as NPAD.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_walkG_ok usp sp' f d n _ gp (Z_to_bv 64 TPV_A) u0 u1 u2 v b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 (f + 184)) s8 s9 u3 u4 u5 u6 j20 F7 fc7 m7
                             FPOS ltac:(ul) ltac:(ul) ltac:(ul) RESC7 MI7)|].
  cbv beta. intros ms8 <-. apply evt_done. unfold lf_regs.

  set (cap := Z.max n 32) in *.
  assert (CAP : 32 <= cap <= 2^26) by (subst cap; change (2^26) with 67108864; lia).
  pose proof (al_sbuf_bounds _ CAP) as B1. pose proof (al_tape_bounds _ CAP) as B2. pose proof (sc_idx_bounds cap ltac:(lia)) as B3.
  assert (INT : In (tape, al_tape cap) (rt_live RT Σ2)) by (rewrite LV2; apply in_or_app; right; do 4 right; left; reflexivity).
  assert (INS : In (sbuf, al_sbuf cap) (rt_live RT Σ2)) by (rewrite LV2; apply in_or_app; right; do 5 right; left; reflexivity).
  pose proof (af_live_range RT AF Σ2 m7 _ _ ART7 INT) as (_ & TR & _). pose proof (af_live_range RT AF Σ2 m7 _ _ ART7 INS) as (_ & SR & _). rewrite SP2 in TR, SR.
  pose (E := mkPJA lo f 4%nat (f + 32) (f + 184) tape (al_tape cap) sbuf (al_sbuf cap) tws sbs n (rt_live RT Σ2)).
  assert (EOK : pjenvA_ok E).
  { subst E. constructor; cbn [pa_lo pa_F pa_kF pa_SB pa_DOC pa_TAPE pa_NT pa_SBUF pa_NS pa_tws pa_sbs pa_len pa_L].
    - exact WFS. - exact SBR. - unfold SJ_PADMAX in *; lia.
    - unfold SJ_TAPE, SJ_SBUF, sj_cap. fold cap. unfold al_sbuf in NS. lia.
    - unfold al_tape in *. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia| exact INT].
    - split; [lia|]. split; [lia|]. split; [lia|]. split; [lia| exact INS].
    - intros p k Hin. rewrite LV2 in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
      + destruct CP as [(COPY & -> & CPOS & _)| ->]; [destruct Hin as [Hin|[]]; injection Hin as <- <-; lia| destruct Hin].
      + cbn [In] in Hin. destruct Hin as [Hin|[Hin|[Hin|[Hin|[Hin|[Hin|Hin]]]]]]; [injection Hin as <- <-; lia ..| rewrite LV1 in Hin; exact (LVPOS p k Hin)].
    - split; [exact F64|]. split; [exact FSEG| change (fs_size 4) with 1024; lia].
    - change (fs_size 4) with 1024. split; [Z.div_mod_to_equations; lia| lia].
    - change (fs_size 4) with 1024. split; [Z.div_mod_to_equations; lia| lia].
    - lia.
    - ul.
    - unfold al_sbuf, SjModel.roundup64. Z.div_mod_to_equations. lia. }
  assert (ELIVE : pa_live RT Σ2 E (sbA0 (f + 32))) by (subst E; split; [reflexivity| split; [rewrite FRS2; left; reflexivity| cbn [pa_lo]; rewrite SP2; exact LOW]]).
  assert (EDOC : DOCREPA E m7).
  { subst E. split; [exact DOC7|]. split; [exact (pj_doc_shadow m7 f tS FS7 FPOS F64)|]. split; [exact BT| exact BSB]. }
  pose proof FS7 as FS7'. apply pj_shadow_split in FS7'. destruct FS7' as [FSc7 FSt7].
  pose proof FRlo7 as FRlo7'.
  lazymatch type of FRlo7' with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?rest) => change (c0 :: c1 :: c2 :: c3 :: rest) with ([c0; c1; c2] ++ [c3] ++ rest) in FRlo7' end.
  apply Sj_stage1_kit.rw_cells_app in FRlo7'. destruct FRlo7' as [FRa7 FRlo7']. apply Sj_stage1_kit.rw_cells_app in FRlo7'. destruct FRlo7' as [F24 FRb7].
  cbn [cells_size csize Nat.add] in F24, FRb7. replace (sp' + Z.of_nat 24) with (sp' + 24) in F24 by lia. replace (sp' + Z.of_nat 24 + Z.of_nat 8) with (sp' + 32) in FRb7 by lia.
  pose proof RESC7 as RESC7'. unfold res_cellsA in RESC7'. rewrite bv_eqb_refl in RESC7'.
  lazymatch type of RESC7' with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?rest) => change (c0 :: c1 :: c2 :: rest) with ([c0; c1; c2] ++ rest) in RESC7' end.
  apply Sj_stage1_kit.rw_cells_app in RESC7'. destruct RESC7' as [RES3 RES4]. cbn [cells_size csize Nat.add] in RES4. replace (sp' + 64 + Z.of_nat 20) with (sp' + 84) in RES4 by lia.
  assert (NTB : Z.of_nat (length tws) <= n + 98) by (pose proof (roundup64_lt (cap + 3)); lia).
  pose proof (pj_pid_cost_bound n N0) as PCB.
  assert (NL7 : libc_nl m7).
  { apply (libc_nl_agree m m7 NL0). intros a Ha. apply PRES7'; [right; left; exact (libc_nl_static _ Ha)|].
    unfold LIBC_NL in Ha. unfold LIB_FP. cbn [outside]. repeat split; try exact I; lia. }
  assert (IOS7 : io_ssp m7).
  { destruct IOS as (g & _ & G). exists g. split; [exact (proj1 (af_got_lib RT AF Σ2 m7 ART7))|].
    apply (ro_cells_agree bsegs m m7 _ _ G). intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply PRES7'; [right; left; apply client_static_intro; lia|].
    unfold LIB_FP. cbn [outside]. repeat split; try exact I; lia. }
  eapply (OKARM PMc Σ2 K E sp' usp _ gp u0 u1 u2 (Z_to_bv 64 64) b2 b3 b4 b5 b6 b7 (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 (f + 184)) s8 s9 u3 u4 u5 u6 F7 fc7 m7 _ jB jO
            FDO MST EOK eq_refl eq_refl eq_refl ELIVE EDOC (proj1 (proj2 LIB7)) NL7 (proj2 (proj2 LIB7)) IOS7 F24 RES3 FB7 FO7 FSc7 ART7 MI7 ST7 ltac:(subst E; cbn [pa_lo]; ul) ltac:(ul) SPA' ltac:(lia) FRM7 FRS2
            ltac:(subst E; cbn [pa_L]; rewrite LV2, LV1, app_length; cbn [length]; destruct CP as [(COPY & -> & _)| ->]; cbn [length]; unfold FUZZ_LIVE in LVB; lia)
            ltac:(subst E; cbn [pa_tws]; change (2^30) with 1073741824 in *; change (2^28) with 268435456 in *; lia)).
  intros Σ3 ra' z0 z1 z2 o0 o1 o2 o3 o4 o5 o6 o7 k5 k6 k7 k8 k9 z3 z4 z5 z6 F9 fc9 m9 FRM9 ART9 MI9 ST9 LV3 FRS3 SP3 CR3 PRES9 LOCB9 (j24' & jsb' & jos' & F24' & FB9 & FO9) FSc9.
  subst E. cbn [pa_lo pa_F pa_kF pa_SB pa_DOC pa_TAPE pa_NT pa_SBUF pa_NS pa_tws pa_sbs pa_len pa_L] in *. rewrite FRS2 in PRES9.

  assert (AG79 : forall (P : Z -> Prop), (forall x, P x -> (sp' <= x < usp /\ ~ (sp' + 24 <= x < sp' + 32)) \/ (f <= x < f + 32) \/ (f / 8 + 2147450880 + 80 <= x < f / 8 + 2147450880 + 128)) ->
                 agree_on P m7 m9).
  { intros P HP a Ha. apply PRES9.
    - destruct (HP _ Ha) as [[H1 H2]|[H|H]]; [left; ul| right; right; right; left| right; right; right; right];
        [exists f, 4%nat; split; [left; reflexivity| change (fs_size 4) with 1024; lia]
        | exists f, 4%nat; split; [left; reflexivity| unfold shad, SHB; change (fs_size 4) with 1024; Z.div_mod_to_equations; lia]].
    - unfold pj_okarm_W. cbn [pa_SB pa_F outside]. unfold shad, SHB, PJ_LOC_LO_A, PJ_LOC_HI_A.
      destruct (HP _ Ha) as [[H1 H2]|[H|H]]; (repeat split; try exact I); unfold SEGTOP_A, SHB in FSEG, SHB0; try ul. }
  assert (FRa9 : rw_cells bsegs m9 sp' [CB 8 j0; CB 8 j1; CB 8 j2]) by (eapply rw_cells_agree_nw; [exact FRa7|]; apply AG79; intros x Hx; cbn [cells_size csize Nat.add] in Hx; left; split; [ul| lia]).
  assert (FRb9 : rw_cells bsegs m9 (sp' + 32) [CB 8 j4; CB 8 j5; CB 8 j6; C8 (Z_to_bv 64 f)])
    by (eapply rw_cells_agree_nw; [exact FRb7|]; apply AG79; intros x Hx; cbn [cells_size csize Nat.add] in Hx; left; split; [ul| lia]).
  assert (RESC9 : rw_cells bsegs m9 (sp' + 64) (res_cellsA (f + 184) (Z_to_bv 64 0) j20))
    by (eapply rw_cells_agree_nw; [exact RESC7|]; apply AG79; intros x Hx; unfold res_cellsA in Hx; rewrite bv_eqb_refl in Hx; cbn [cells_size csize Nat.add] in Hx; left; split; [ul| lia]).
  assert (STp9 : stk bsegs m9 (sp' + 88) (usp - 104)) by (eapply stk_agree_nw; [exact STp7|]; apply AG79; intros x Hx; cbv beta in Hx; left; split; [lia| lia]).
  assert (FRs9 : rw_cells bsegs m9 (usp - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
    by (eapply rw_cells_agree_nw; [exact FRs7|]; apply AG79; intros x Hx; unfold fa_saved in Hx; cbn [cells_size csize Nat.add] in Hx; left; split; [lia| lia]).
  assert (FH9 : rw_cells bsegs m9 f (fz_hdr (C8 (Z_to_bv 64 0x41b58ab3)) (C8 (Z_to_bv 64 0x13300)) (C8 (Z_to_bv 64 0xb15fc)) h2))
    by (eapply rw_cells_agree_nw; [exact FH7|]; apply AG79; intros x Hx; unfold fz_hdr in Hx; cbn [cells_size csize Nat.add] in Hx; right; left; lia).
  assert (FSt9 : rw_cells bsegs m9 (f / 8 + 2147450880 + 80) [CB 48 tS])
    by (eapply rw_cells_agree_nw; [exact FSt7|]; apply AG79; intros x Hx; cbn [cells_size csize Nat.add] in Hx; right; right; lia).
  assert (FS9 : rw_cells bsegs m9 (f / 8 + 2147450880) (pj_shadow1 tS)) by (apply pj_shadow_split; split; [exact FSc9| exact FSt9]).
  assert (LIB9 : pj_lib m9).
  { split; [| split; [right; exact LOCB9|]].
    - eapply sj_lib_agree; [exact (proj1 LIB7)|]. intros a Ha. apply PRES9.
      + right; left. exact (proj1 (lib_fp_static _ (sj_lib_rng_fp _ Ha))).
      + unfold pj_okarm_W. cbn [pa_SB pa_F outside]. unfold shad, SHB, PJ_LOC_LO_A, PJ_LOC_HI_A. unfold sj_lib_rng in Ha. unfold SEGTOP_A in FSEG.
        repeat split; try exact I; ul.
    - eapply lockwA_agree; [exact (proj2 (proj2 LIB7))|]. intros a Ha. apply PRES9.
      + right; left. exact (proj1 (lib_fp_static _ (lock_rng_fp _ Ha))).
      + unfold pj_okarm_W. cbn [pa_SB pa_F outside]. unfold shad, SHB, PJ_LOC_LO_A, PJ_LOC_HI_A. unfold PJ_LOCKW_A in Ha. unfold SEGTOP_A in FSEG.
        repeat split; try exact I; ul. }
  assert (PRES9' : forall a : word, aclient (rt_live RT Σ) [] usp (bv_unsigned a) -> outside LIB_FP (bv_unsigned a) -> m9 a = m a).
  { intros a Ha Ho. rewrite <- (PRES7' a Ha Ho). apply PRES9.
    - apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact INCL2| intros e []| lia].
    - unfold pj_okarm_W. cbn [pa_SB pa_F outside]. unfold shad, SHB, PJ_LOC_LO_A, PJ_LOC_HI_A.
      assert (NR : ~ (f <= bv_unsigned a < f + 1024 \/ f / 8 + 2147450880 <= bv_unsigned a < f / 8 + 2147450880 + 128 \/ sp' <= bv_unsigned a < usp)).
      { intros E0. destruct Ha as [H|[H|[H|[H|H]]]]; [clear - H E0 FR1' SHT LOW LOR SPR; ul| exact (NCL _ E0 (or_introl H))| exact (NCL _ E0 (or_intror H))
                                                      | destruct H as (? & ? & [] & _)| destruct H as (? & ? & [] & _)]. }
      unfold LIB_FP in Ho. cbn [outside] in Ho. decompose [and] Ho.
      repeat split; try exact I; try (clear - NR SPR; lia). assumption. }
  clear AG79 FRa7 F24 FRb7 RES3 RES4 FB7 FO7 FSc7 FSt7 FS7 FH7 FRlo7 RESC7 STp7 FRs7 PRES7' LIB7 DOC7 FOBJ7 MI7 ST7.

  rewrite <- (Z_to_bv_bv_unsigned k5), <- (Z_to_bv_bv_unsigned k6). unfold shad, SHB.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_walkJ usp sp' f (bv_unsigned k6) (bv_unsigned k5) _ gp (Z_to_bv 64 TPV_A) z0 z1 z2 o0 o1 o2 o3 o4 o5 o6 o7 k7 k8 k9 z3 z4 z5 z6 F9 fc9 m9 FPOS ltac:(ul))|].
  cbv beta. intros ms10 <-. apply evt_done.
  apply (pj_tail PMc FDO MST Σ Σ3 K usp sp' f lo (bv_unsigned k6) (bv_unsigned k5) gp z0 z1 z2 o1 o2 o3 o4 o5 o6 o7 k7 k8 k9 z3 z4 z5 z6
           ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           ([CB 8 j0; CB 8 j1; CB 8 j2] ++ [CB 8 j24'] ++ [CB 8 j4; CB 8 j5; CB 8 j6; C8 (Z_to_bv 64 f)] ++ res_cellsA (f + 184) (Z_to_bv 64 0) j20)
           h2 tS F9 fc9 m m9 (rt_credit RT Σ - FUZZ_COST));
    [lia| exact F64| exact FR1'| exact FSEG| exact FD0| exact FSELF| exact SHB0| exact SHT| exact LOW| exact LOR| exact SPT| exact SPR| exact SPA'
    | exact ART9| exact MI9| rewrite FRS3; exact FRS2| intros e He; rewrite LV3; exact (INCL2 e He)| rewrite SP3; exact SP2| | rewrite <- LV1 | exact ST9| | | exact STp9| exact FRs9| exact FH9| exact FS9| exact LIB9| exact PRES9'| exact FRM9| exact KFIN].
  - change (2^30) with 1073741824 in *. change (2^28) with 268435456 in *. lia.
  - assert (INF2 : In (f, 4%nat) (rt_frames RT Σ2)) by (rewrite FRS2; left; reflexivity).
    pose proof (af_frames_range RT AF Σ2 m7 f 4%nat ART7 INF2) as (_ & _ & _ & FLV2). pose proof (proj1 (af_fshadow_apart RT AF Σ2 m7 f 4%nat ART7 INF2)) as FSL2.
    change (fs_size 4) with 1024 in FLV2, FSL2. rewrite SHF in FSL2. unfold shad, SHB in FSL2.
    apply (PDFP Σ2 Σ3 m7 m9 (f + 160) (rt_live RT Σ1) PD7 ART7); [rewrite FRS3, FRS2; reflexivity| exact LV3|].
    intros a Ha. unfold shad, SHB in Ha. replace ((f + 160) / 8) with (f / 8 + 20) in Ha by (Z.div_mod_to_equations; lia). apply PRES9.
    + destruct Ha as [H|[H|H]]; [right; right; right; left| right; right; right; right| right; right; left; exact H];
        (exists f, 4%nat; split; [left; reflexivity| unfold shad, SHB; change (fs_size 4) with 1024; Z.div_mod_to_equations; lia]).
    + unfold pj_okarm_W. cbn [pa_SB pa_F outside]. unfold shad, SHB, PJ_LOC_LO_A, PJ_LOC_HI_A. unfold SEGTOP_A in FSEG.
      destruct Ha as [H|[H|(p & k & Hin & Hr)]]; [repeat split; try exact I; clear - H FR1' SHT FSELF FSEG LOW LOR SPR; ul| repeat split; try exact I; clear - H FR1' SHT FSELF FSEG SHB0 LOW LOR SPR FD0; ul|].
      pose proof (FLV2 p k Hin) as Y1. pose proof (FSL2 p k Hin) as Y2. pose proof (af_live_range RT AF Σ2 m7 p k ART7 Hin) as (_ & Y3 & Y4). rewrite SP2 in Y3.
      unfold SEGTOP_A in Y4. repeat split; try exact I; clear - Hr Y1 Y2 Y3 Y4 LOW LOR SPR; ul.
  - unfold res_cellsA. rewrite bv_eqb_refl. reflexivity.
  - apply Sj_stage1_kit.rw_cells_app. split; [exact FRa9|]. cbn [cells_size csize Nat.add]. replace (sp' + Z.of_nat 24) with (sp' + 24) by lia.
    apply Sj_stage1_kit.rw_cells_app. split; [exact F24'|]. cbn [cells_size csize Nat.add]. replace (sp' + 24 + Z.of_nat 8) with (sp' + 32) by lia.
    apply Sj_stage1_kit.rw_cells_app. split; [exact FRb9|]. cbn [cells_size csize Nat.add]. replace (sp' + 32 + Z.of_nat 32) with (sp' + 64) by lia. exact RESC9.
Qed.

End Top.
