(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk LibIface BnContract.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LxLin LxState LxMem LxStep LxCheck LxSem LxWf LxSoundVal LxSoundMem LxSoundMem2
     LxOrder LxOrderWf LxSoundStep LxSoundMatch LxSoundExplore LxGlue LxFinal LxInstP LxInstU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import LXL LXS LXM LXI LXC LXSEM LXWF LXSV LXSM LXF.
Open Scope Z_scope.

Theorem lx_lib_stmt_in : forall (UP : uenv) (Un : unitT) (ENTRY NMAX : Z) (HULL : Z * Z) (LIBR SNAP : list (Z * Z)) (CAN : Z),
  LXG.uenv_okb UP = true -> LXG.glue_okb UP HULL LIBR SNAP = true ->
  ue_scells UP = [(CAN, SYM_SC0)] ->
  un_env Un = UP -> un_snap Un = SNAP ->
  In (entry_cut ENTRY NMAX []) (un_cuts Un) ->
  In (entry_cut ENTRY NMAX SNAP) (un_cuts Un) ->
  check_unit Un = true -> un_total Un = true ->
  cbd_stmt (ue_segs UP) (ue_cbd_pc UP) (ue_cbd_fr UP) ->
  lib_stmt (ue_segs UP) ENTRY (ue_fr UP) NMAX HULL LIBR SNAP (ue_ro UP) CAN.
Proof.
  intros UP Un0 ENTRY NMAX HULL LIBR SNAP CAN HUOK HGOK HSC EU0 SU0 CA CB CHK0 TOT0 HCBD.
  pose proof (LXG.uenv_okb_sound UP HUOK) as UOK. pose proof (LXG.glue_okb_sound UP HULL LIBR SNAP HGOK) as GOK.
  unfold lib_stmt.
  intros fx regs mem rom ret sp data n Hx1 Hret4 Hx2 Hx10 Hx11 Hn Hd1 Hd2 Hd3 Hs1 Hs2 Hs3 Hdisj Himg Hnoseg Hpay Hst Hro Hcan [Hstat Hhull] Hfrm.
  assert (G2 : LXG.greg regs 2 = bv_unsigned sp) by (unfold LXG.greg; rewrite Hx2; reflexivity).
  assert (G10 : LXG.greg regs 10 = bv_unsigned data) by (unfold LXG.greg; rewrite Hx10; reflexivity).
  assert (G1 : LXG.greg regs 1 = bv_unsigned ret) by (unfold LXG.greg; rewrite Hx1; reflexivity).
  assert (RO' : ro_ok (ue_segs UP) (ue_ro UP) mem) by exact Hro.
  (* [comment removed for export] *)
  assert (UNIT : exists Un abs0, un_env Un = UP /\ un_snap Un = SNAP /\ check_unit Un = true /\ un_total Un = true /\
                 In (entry_cut ENTRY NMAX abs0) (un_cuts Un) /\
                 ((abs0 = [] /\ statics_pristine LIBR mem) \/ (abs0 = SNAP /\ statics_snap SNAP mem))).
  { destruct Hstat as [HP | HS].
    - exists Un0, []. repeat split; try assumption. left; split; [reflexivity | exact HP].
    - exists Un0, SNAP. repeat split; try assumption. right; split; [reflexivity | exact HS]. }
  clear CA CB CHK0 TOT0 SU0 EU0 Hstat Un0.
  destruct UNIT as (Un & abs0 & EU & SU & CHK & TOT & HIN & HABS). subst UP.
  destruct Hcan as [c Hc].
  pose proof (LXG.entry_scells (un_env Un) UOK regs n c mem
                ltac:(intros a x Hin; rewrite HSC in Hin; destruct Hin as [Hin|[]]; injection Hin; intros _ <-; exact Hc)) as SCOK.
  pose proof (LXG.entry_R (un_env Un) HULL LIBR SNAP UOK GOK fx regs mem rom n (bv_unsigned c) ENTRY NMAX abs0) as ER.
  cbv zeta in ER. rewrite G2, G10, G1 in ER.
  specialize (ER Hx11 Hn Hret4 Hd1 Hd2 Hd3 Hs1 Hs2 Hs3 Hdisj Hnoseg Hpay Hst RO' HABS Hhull Hfrm).
  destruct (LXSE.unit_sound Un (LXG.rho_entry regs n (bv_unsigned c)) mem UOK SCOK
              (apply_cbd_sound (un_env Un) (LXG.rho_entry regs n (bv_unsigned c)) mem UOK HCBD)
              CHK TOT (LXG.rho_entry regs n (bv_unsigned c)) (@mkst fx regs (Z_to_bv 64 ENTRY) mem rom))
    as (ms' & S & rho' & MS & EXIT & HR').
  { exists (entry_cut ENTRY NMAX abs0). split; [exact HIN | exact ER]. }
  destruct (LXG.exit_post (un_env Un) HULL LIBR SNAP UOK GOK (LXG.rho_entry regs n (bv_unsigned c)) mem fx regs mem n (bv_unsigned c) Un S rho' ms'
              eq_refl eq_refl eq_refl SU Hhull EXIT HR') as (fx' & regs' & mem' & Ems' & KEEP & A0 & FRAME & STAT & FRM').
  exists fx', regs', mem'.
  rewrite Ems' in MS. pose proof (msteps_rom _ _ _ MS) as ROM. cbn [ms_rom mkst] in ROM. rewrite ROM in MS.
  rewrite Hx1 in MS. rewrite G2 in FRAME.
  split; [exact MS|]. split; [exact KEEP|]. split; [exact A0|]. split; [exact FRAME|]. split; [exact STAT | exact FRM'].
Qed.

(* [comment removed for export] *)
Theorem lib_P_of_unit : forall Un : unitT,
  un_env Un = UP -> un_snap Un = SNAP_P ->
  In (entry_cut ENTRY_P NMAX_P []) (un_cuts Un) -> In (entry_cut ENTRY_P NMAX_P SNAP_P) (un_cuts Un) ->
  check_unit Un = true -> un_total Un = true ->
  cbd_stmt_P -> lib_stmt_P.
Proof.
  intros Un E S CA CB CHK TOT HCBD.
  exact (lx_lib_stmt_in UP Un ENTRY_P NMAX_P LIBR_HULL_P LIBR_P SNAP_P CANARY_P uenv_okb_P glue_okb_P eq_refl E S CA CB CHK TOT HCBD).
Qed.

Theorem lib_U_of_unit : forall Un : unitT,
  un_env Un = UU -> un_snap Un = SNAP_U ->
  In (entry_cut ENTRY_U NMAX_U []) (un_cuts Un) -> In (entry_cut ENTRY_U NMAX_U SNAP_U) (un_cuts Un) ->
  check_unit Un = true -> un_total Un = true ->
  cbd_stmt_U -> lib_stmt_U.
Proof.
  intros Un E S CA CB CHK TOT HCBD.
  exact (lx_lib_stmt_in UU Un ENTRY_U NMAX_U LIBR_HULL_U LIBR_U SNAP_U CANARY_U uenv_okb_U glue_okb_U eq_refl E S CA CB CHK TOT HCBD).
Qed.
