(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec CatExec CatSim SeqExec StepTac StoreOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Frame RefMemcpyLib DriverCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.SeqExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.StoreOk OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.Hoare OSSVerify.Proofs.fast_float.from_chars.lib.Common.Frame OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefMemcpyLib OSSVerify.Proofs.fast_float.from_chars.lib.Common.DriverCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout.ArgvEnv.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxSubst FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Arr.
From OSSVerify.Proofs.fast_float.from_chars.lib Require UDrvData UDrvMain.
From OSSVerify.Proofs.fast_float.from_chars.lib Require UOpenCert.
From OSSVerify.Proofs.fast_float.from_chars.lib Require UDrvCall UDrvCall2 UDrvExit UbStdioDefs UbExitBase UbStartup UbStartupDefs.
Import OSSVerify.Proofs.fast_float.from_chars.lib.UDrvData OSSVerify.Proofs.fast_float.from_chars.lib.UDrvMain OSSVerify.Proofs.fast_float.from_chars.lib.UOpenCert.UDrvMain2 OSSVerify.Proofs.fast_float.from_chars.lib.UDrvCall OSSVerify.Proofs.fast_float.from_chars.lib.UDrvCall2 OSSVerify.Proofs.fast_float.from_chars.lib.UDrvExit OSSVerify.Proofs.fast_float.from_chars.lib.UbStdioDefs OSSVerify.Proofs.fast_float.from_chars.lib.UbExitBase OSSVerify.Proofs.fast_float.from_chars.lib.UbStartup OSSVerify.Proofs.fast_float.from_chars.lib.UbStartupDefs.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import UUsageCert UOpenCert UCantCert UUsage3 UUsage4 UCant2 Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section UCc.
Variable sp0 : word.
Variables av ev : list (list byte).
Variables uid tid hw : word.
Variable rdraw : EntryDraw.
Variable regs : bvmap 5 word.
Variable mem : word -> option byte.
Hypothesis Hsp : valid_sp sp0.
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
Hypothesis ME : main_entry sp0 av ev uid tid hw rdraw regs mem.
Hypothesis Hargc2 : length av = 2%nat.
Variable model : Model.
Hypothesis Hh : m_halted model = None.
Hypothesis Hl : m_vm_lazy model = [].
Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

Let E := E_main sp0 av ev tid (canary rdraw) regs.

#[using="Hsp"] Lemma SL2 : 0x7fff80000000 <= bv_unsigned sp0. Proof. LiaFast.lf_pins (fun (Hsp : LiaFast.U) => LiaFast.u0). exact (sp0_lo sp0 Hsp). Qed.
#[using="Hsp"] Lemma SH2 : bv_unsigned sp0 <= 0x800000000000. Proof. LiaFast.lf_pins (fun (Hsp : LiaFast.U) => LiaFast.u0). exact (sp0_hi sp0 Hsp). Qed.

#[using="Hargc2"] Lemma lden_sp0c : forall E' c, (forall x, (x < 200)%positive -> E' x = E x) -> -65536 <= c <= 0 ->
  lden E' (laddc SP0 c) = Z_to_bv 64 (bv_unsigned sp0 + c).
Proof. LiaFast.lf_pins (fun (Hargc2 : LiaFast.U) => LiaFast.u0). intros E' c HE Hc. rewrite lden_laddc. unfold SP0. rewrite lden_lvar, HE by lia. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mf_seg2 : forall E' S ms ms', agree 200 E E' -> shape (s_rgs S) = shape (s_rgs P_main2) ->
  (forall x, outside E' (s_rgs S) x -> ms_mem ms' x = ms_mem ms x) ->
  (forall x, outside E (s_rgs P_main2) x -> ms_mem ms x = mem x) ->
  (forall x, outside E (s_rgs P_main2) x -> ms_mem ms' x = mem x).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E' S ms ms' Ha Hs Hfr Hmf x Hx. rewrite Hfr; [exact (Hmf x Hx)|].
  apply (outside_shape E' (s_rgs P_main2)); [exact Hs|]. exact (proj1 (outside_agree 200 E E' _ x bases_main2 Ha) Hx).
Qed.

(* [comment removed for export] *)
#[using="Hsp Hargc2"] Lemma mf_sw2 : forall ms ms' su bufp bufsz, sw_post (ms_mem ms) su 0x66bd8 bufp bufsz (ms_mem ms') ->
  bv_unsigned sp0 - 65536 <= su - 112 -> su <= bv_unsigned sp0 ->
  (forall x, outside E (s_rgs P_main2) x -> ms_mem ms x = mem x) ->
  (forall x, outside E (s_rgs P_main2) x -> ms_mem ms' x = mem x).
Proof. LiaFast.lf_pins (fun (Hsp Hargc2 : LiaFast.U) => LiaFast.u0).
  intros ms ms' su bufp bufsz Hpost Hs1 Hs2 MF x Hx. pose proof SL2. pose proof SH2.
  pose proof (outside_nth_c E _ x 0 (laddc SP0 (-65536)) 65536 RW TEmpty Hx eq_refl ltac:(unfold two64; lia)) as X0r. cbn [RGz rg_base] in X0r.
  pose proof (outside_nth_c E _ x 5 (lconst 0x66bd8) 232 RI TEmpty Hx eq_refl ltac:(unfold two64; lia)) as X5r. cbn [RGz rg_base] in X5r.
  rewrite lden_laddc in X0r. unfold SP0 in X0r. rewrite lden_lvar in X0r. change (E 1%positive) with sp0 in X0r.
  rewrite u_small64 in X0r by (unfold two64; lia). rewrite u_lconst in X5r by lia.
  rewrite (swp_agree _ _ _ _ _ _ Hpost x); [exact (MF x Hx) | lia | lia | lia].
Qed.

#[using="Hargc2"] Lemma agree_next : forall E1 E2 (L : sst), agree 200 E E1 -> (200 <= s_next L)%positive -> agree (s_next L) E1 E2 -> agree 200 E E2.
Proof. LiaFast.lf_pins (fun (Hargc2 : LiaFast.U) => LiaFast.u0). intros E1 E2 L H1 Hn H2 x Hx. rewrite (H1 x Hx). apply H2. lia. Qed.

#[using="uid hw Hsp Hva Hve Htid ME Hargc2 Hh Hl Hfd2"] Theorem cant_Cb : forall E1 ms1, agree 200 E E1 -> sden PSEGS E1 U4bc ms1 -> ms_rom ms1 = seg_rom PSEGS ->
  (forall x, outside E (s_rgs P_main2) x -> ms_mem ms1 x = mem x) ->
  realizes PSEGS (mkCfg ms1 model) (t_emit (W 2 SUFc) (TEXIT model)).
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Htid ME Hargc2 Hh Hl Hfd2 : LiaFast.U) => LiaFast.u0).
  intros E1 ms1 Ha1 Hd1 Hrom1 Hmf1. pose proof SL2 as SL. pose proof SH2 as SH.
  apply (rzc_fx_explore_frame PSEGS DCFG TBL_P IMG_P 4000 S1 U4bc LCbc E1 ms1 model _ TBL_P_ok IMG_P_ok certCbc Hd1
           ltac:(vm_compute; reflexivity) Hh Hl).
  intros L E2 ms2 HIn Hd2 Ha2 Hrom2 Hfr2. rewrite LCbc_one in HIn. destruct HIn as [<-|[]].
  assert (Ha2' : agree 200 E E2) by exact (agree_next E1 E2 U4bc Ha1 ltac:(vm_compute; congruence) Ha2).
  assert (HE2 : forall x, (x < 200)%positive -> E2 x = E x) by (intros x Hx; symmetry; exact (Ha2' x Hx)).
  assert (HS2 : lden E2 SP0 = sp0) by (unfold SP0; rewrite lden_lvar, HE2 by lia; reflexivity).
  assert (MF2 : forall x, outside E (s_rgs P_main2) x -> ms_mem ms2 x = mem x)
    by exact (mf_seg2 E1 U4bc ms1 ms2 Ha1 ltac:(vm_compute; reflexivity) Hfr2 Hmf1).
  rewrite Hrom1 in Hrom2.
  (* [comment removed for export] *)
  assert (R1 : getr (ms_regs ms2) 1 = Z_to_bv 64 0x561c8) by (apply (getr_leaf_c PSEGS E2 L4bc); [exact Hd2 | vm_compute; reflexivity]).
  assert (R2 : getr (ms_regs ms2) 2 = Z_to_bv 64 (bv_unsigned sp0 - 576)).
  { rewrite (getr_leaf PSEGS E2 L4bc ms2 2 (laddc SP0 (-576)) Hd2) by (vm_compute; reflexivity). apply lden_sp0c; [exact HE2 | lia]. }
  assert (R10 : getr (ms_regs ms2) 10 = Z_to_bv 64 0x66bd8) by (apply (getr_leaf_c PSEGS E2 L4bc); [exact Hd2 | vm_compute; reflexivity]).
  assert (R11 : getr (ms_regs ms2) 11 = Z_to_bv 64 0) by (apply (getr_leaf_c PSEGS E2 L4bc); [exact Hd2 | vm_compute; reflexivity]).
  assert (R12 : getr (ms_regs ms2) 12 = Z_to_bv 64 0) by (apply (getr_leaf_c PSEGS E2 L4bc); [exact Hd2 | vm_compute; reflexivity]).
  assert (F40 : rdn PSEGS (ms_mem ms2) (Z_to_bv 64 (0x66bd8 + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 - 559)))).
  { rewrite (rdn_trk_c E2 L4bc ms2 5 0x66bd8 40 8 (bvs_of (laddc SP0 (-559)) 8) Hd2
               ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
    rewrite bvs_of_den_lin, (lden_sp0c E2 (-559) HE2) by lia. reflexivity. }
  assert (F56 : rdn PSEGS (ms_mem ms2) (Z_to_bv 64 (0x66bd8 + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 - 560)))).
  { rewrite (rdn_trk_c E2 L4bc ms2 5 0x66bd8 56 8 (bvs_of (laddc SP0 (-560)) 8) Hd2
               ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
    rewrite bvs_of_den_lin, (lden_sp0c E2 (-560) HE2) by lia. reflexivity. }
  assert (F88 : rdn PSEGS (ms_mem ms2) (Z_to_bv 64 (0x66bd8 + 88)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 - 560)))).
  { rewrite (rdn_trk_c E2 L4bc ms2 5 0x66bd8 88 8 (bvs_of (laddc SP0 (-560)) 8) Hd2
               ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
    rewrite bvs_of_den_lin, (lden_sp0c E2 (-560) HE2) by lia. reflexivity. }
  assert (F96 : rdn PSEGS (ms_mem ms2) (Z_to_bv 64 (0x66bd8 + 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 80))).
  { rewrite (rdn_trk_c E2 L4bc ms2 5 0x66bd8 96 8 [BK 80; BK 0; BK 0; BK 0; BK 0; BK 0; BK 0; BK 0] Hd2
               ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). reflexivity. }
  assert (F120 : rdn PSEGS (ms_mem ms2) (Z_to_bv 64 (0x66bd8 + 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 2))).
  { rewrite (rdn_img_c E2 L4bc ms2 5 0x66bd8 120 4 Hd2 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
               ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vmz) ltac:(vm_compute; reflexivity)). bvlit. }
  assert (F48 : rdn PSEGS (ms_mem ms2) (Z_to_bv 64 (0x66bd8 + 48)) 8 = Some (repeat (Z_to_bv 8 0) 8)).
  { rewrite (rdn_trk_c E2 L4bc ms2 5 0x66bd8 48 8 [BK 0; BK 0; BK 0; BK 0; BK 0; BK 0; BK 0; BK 0] Hd2
               ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). reflexivity. }
  assert (SWF : sw_file (ms_mem ms2) 0x66bd8 (bv_unsigned sp0 - 560) (bv_unsigned sp0 - 559) 2 (Z_to_bv 64 (bv_unsigned sp0 - 560)) (Z_to_bv 64 80)).
  { constructor; assumption. }
  assert (SSP : ssp_cells (ms_mem ms2) (lden E2 (lvar 5))).
  { split.
    - replace (Z_to_bv 64 0x65b58) with (Z_to_bv 64 (0x65a18 + 320)) by reflexivity.
      rewrite (rdn_img_c E2 L4bc ms2 3 0x65a18 320 8 Hd2 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(left; vm_compute; reflexivity) ltac:(lia) ltac:(vmz) ltac:(vm_compute; reflexivity)). bvlit.
    - replace (Z_to_bv 64 0x97c00) with (Z_to_bv 64 (0x97c00 + 0)) by reflexivity.
      rewrite (rdn_trk_c E2 L4bc ms2 8 0x97c00 0 8 (bvs_of (lvar 5) 8) Hd2
                 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
      rewrite bvs_of_den_lin. reflexivity. }
  assert (RDP : rdn PSEGS (ms_mem ms2) (Z_to_bv 64 (bv_unsigned sp0 - 560)) (length SUFc) = Some SUFc).
  { replace (bv_unsigned sp0 - 560) with (bv_unsigned sp0 + -65536 + 64976) by lia.
    rewrite (rdn_trk_sp sp0 SL SH E2 L4bc ms2 0 (-65536) 64976 (length SUFc) [BK 10] Hd2
               ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) HS2 ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). bvlit. }
  assert (FRM : frame_in E2 L4bc 0 64848 112 (bv_unsigned sp0 - 576 - 112)).
  { apply (frame_sp sp0 SL SH E2 L4bc 0 (-65536)); [vm_compute; lia | vm_compute; reflexivity | exact HS2 | lia | vm_compute; reflexivity | lia | vmz | lia]. }
  assert (HWF : state_wf (sw_template L4bc (bv_unsigned (Z_to_bv 64 0x561c8)) 0 64848 5 (laddc SP0 (-560)) (lconst 80) (lconst 0)) = true).
  { rewrite u_small64 by (unfold two64; lia). rewrite U5bc_eq. exact wf5bc. }
  apply (rzc_conseq PSEGS DCFG _ (t_emit (map (WriteEv (Z_to_bv 64 2)) (SUFc ++ [])) (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model)))));
    [| unfold TEXIT; apply tail_1].
  apply (fx_stdio_write E2 L4bc ms2 model _ (bv_unsigned sp0 - 576) 0x66bd8 (bv_unsigned sp0 - 560) (bv_unsigned sp0 - 559) 2
           (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (bv_unsigned sp0 - 560)) (Z_to_bv 64 80) (lden E2 (lvar 5)) (Z_to_bv 64 0x561c8) SUFc []
           0 64848 5 (rgn L4bc 5) (laddc SP0 (-560)) (lconst 80) (lconst 0)
           Hd2 eq_refl eq_refl Hrom2 hok4bc HWF FRM (rgn_eq L4bc 5 ltac:(vm_compute; lia)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
           ltac:(vm_compute; reflexivity) R2 R10 R11 R12 R1); try lia.
  + exact SWF.
  + exact SSP.
  + exact F48.
  + exact Hfd2.
  + exact Hh.
  + exact Hl.
  + unfold TASK_SIZE. lia.
  + unfold SUFc. cbn [length]. lia.
  + vm_compute. reflexivity.
  + unfold SUFc. cbn [length]. lia.
  + unfold SUFc. cbn [length]. lia.
  + left. rewrite !u_small64 by (unfold two64; lia). lia.
  + rewrite !u_small64 by (unfold two64; lia). unfold TASK_SIZE; lia.
  + exact RDP.
  + reflexivity.
  + vm_compute. reflexivity.
  + apply t_emit_has_nil.
  + apply (lden_sp0c E2 (-560) HE2). lia.
  + apply lden_lconst.
  + apply lden_lconst.
  + vm_compute. reflexivity.
  + vm_compute. reflexivity.
  + intros E' ms' Ha' Hd' Hpost Hrom'.
    rewrite u_small64 in Hd' by (unfold two64; lia). rewrite U5bc_eq in Hd'.
    assert (Ha3 : agree 200 E E') by exact (agree_next E2 E' L4bc Ha2' ltac:(vm_compute; congruence) Ha').
    assert (MF3 : forall x, outside E (s_rgs P_main2) x -> ms_mem ms' x = mem x)
      by exact (mf_sw2 ms2 ms' _ _ _ Hpost ltac:(lia) ltac:(lia) MF2).
    rewrite Hrom2 in Hrom'.
    apply (rzc_fx_explore_frame PSEGS DCFG TBL_P IMG_P 4000 S1 U5bc LDbc E' ms' model _ TBL_P_ok IMG_P_ok certDbc Hd'
             ltac:(vm_compute; reflexivity) Hh Hl).
    intros L E3 ms3 HIn Hd3 Ha4 Hrom3 Hfr3. rewrite LDbc_one in HIn. destruct HIn as [<-|[]].
    assert (Ha4' : agree 200 E E3) by exact (agree_next E' E3 U5bc Ha3 ltac:(vm_compute; congruence) Ha4).
    assert (HE3 : forall x, (x < 200)%positive -> E3 x = E x) by (intros x Hx; symmetry; exact (Ha4' x Hx)).
    assert (MF4 : forall x, outside E (s_rgs P_main2) x -> ms_mem ms3 x = mem x)
      by exact (mf_seg2 E' U5bc ms' ms3 Ha3 ltac:(vm_compute; reflexivity) Hfr3 MF3).
    rewrite Hrom' in Hrom3.
    apply (fx_exit E3 L5bc ms3 model (Z_to_bv 64 2) [] Hd3 eq_refl eq_refl Hrom3).
    apply (exit_pre_gen sp0 tid SL SH Htid E3 L5bc ms3 model (-128) 0 3 5 6 7 21 65264 (rg_cont (rgn L5bc 5)) (rg_cont (rgn L5bc 7)) RI Hd3).
    * unfold SP0. rewrite lden_lvar, HE3 by lia. reflexivity.
    * unfold T. rewrite lden_lvar, HE3 by lia. reflexivity.
    * lia.
    * exact (exit_glob_of_MF2 sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve Htid ME Hargc2 (ms_mem ms3) MF4).
    * exact Hh.
    * exact Hl.
    * vm_compute. reflexivity.
    * vm_compute. reflexivity.
    * vm_compute. reflexivity.
    * vm_compute. reflexivity.
    * vm_compute. reflexivity.
    * unfold c5_clean. repeat split; vm_compute; reflexivity.
    * vm_compute. reflexivity.
    * vm_compute. reflexivity.
    * vm_compute. reflexivity.
    * vm_compute. reflexivity.
    * apply (frame_sp sp0 SL SH E3 L5bc 0 (-65536)); [vm_compute; lia | vm_compute; reflexivity | | lia | vm_compute; reflexivity | lia | vmz | lia].
      unfold SP0. rewrite lden_lvar, HE3 by lia. reflexivity.
Qed.
End UCc.
