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
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import UDrvData UDrvMain UDrvCall UDrvCall2 UDrvExit UbStdioDefs UbExitBase UbStartup UbStartupDefs UUsageCert UUsage2 Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section UC.
Variable sp0 : word.
Variables av ev : list (list byte).
Variables uid tid hw : word.
Variable rdraw : EntryDraw.
Variable regs : bvmap 5 word.
Variable mem : word -> option byte.
Hypothesis Hsp : valid_sp sp0.
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Hfits : entry_stack_fits sp0 av ev.
Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
Hypothesis ME : main_entry sp0 av ev uid tid hw rdraw regs mem.
Hypothesis Hargc : length av <> 2%nat.
Variable model : Model.
Hypothesis Hh : m_halted model = None.
Hypothesis Hl : m_vm_lazy model = [].
Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

Let E := E_main sp0 av ev tid (canary rdraw) regs.
Definition TEXIT (md : Model) : TSet := t_exit (exit_code 2) (m_fs md).

#[using="Type"] Lemma bases_U4b : bases_wf (s_next U4b) (s_rgs U4b) = true. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma shape_U4b : shape (s_rgs U4b) = shape (s_rgs P_main1). Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma bases_U5b : bases_wf (s_next U5b) (s_rgs U5b) = true. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma shape_U5b : shape (s_rgs U5b) = shape (s_rgs P_main1). Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve Htid ME Hargc Hh Hl"] Lemma exit_pre_usage : forall E3 ms3, sden PSEGS E3 L5b ms3 -> (forall x, (x < 200)%positive -> E3 x = E x) ->
  (forall x, outside E (s_rgs P_main1) x -> ms_mem ms3 x = mem x) ->
  exit_pre (ms_regs ms3) (ms_mem ms3) model (Z_to_bv 64 2) [].
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Htid ME Hargc Hh Hl : LiaFast.U) => LiaFast.u0).
  intros E3 ms3 Hd3 HE3 Hmf4.
  pose proof (sp0_lo sp0 Hsp) as SL. pose proof (sp0_hi sp0 Hsp) as SH.
  assert (HA0 : bv_unsigned (lden E3 (rg_base L5b_R0)) = bv_unsigned sp0 - 65536).
  { replace (rg_base L5b_R0) with (laddc SP0 (-65536)) by (vm_compute; reflexivity).
    rewrite lden_laddc. unfold SP0. rewrite lden_lvar, HE3 by lia. apply u_small64. unfold two64; lia. }
  apply (exit_pre_gen sp0 tid SL SH Htid E3 L5b ms3 model (-48) 0 3 5 6 7 21 65344 (rg_cont L5b_R5) (rg_cont L5b_R7) RI Hd3).
  - unfold SP0. rewrite lden_lvar, HE3 by lia. reflexivity.
  - unfold T. rewrite lden_lvar, HE3 by lia. reflexivity.
  - lia.
  - exact (exit_glob_of_MF sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve Htid ME Hargc (ms_mem ms3) Hmf4).
  - exact Hh.
  - exact Hl.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - unfold c5_clean. repeat split; vm_compute; reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - exists L5b_R0. split; [exact L5b_R0_eq|]. rewrite HA0.
    replace (rg_kind L5b_R0) with RW by (vm_compute; reflexivity). rszv.
    split; [lia|]. split; [reflexivity|]. lia.
Qed.

#[using="uid hw Hsp Hva Hve Htid ME Hargc Hh Hl Hfd2"] Theorem usage_Cb : forall E1 ms1, agree 200 E E1 -> sden PSEGS E1 U4b ms1 -> ms_rom ms1 = seg_rom PSEGS ->
  (forall x, outside E (s_rgs P_main1) x -> ms_mem ms1 x = mem x) ->
  realizes PSEGS (mkCfg ms1 model) (t_emit (W 2 SUF) (TEXIT model)).
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Htid ME Hargc Hh Hl Hfd2 : LiaFast.U) => LiaFast.u0).
  intros E1 ms1 Ha1 Hd1 Hrom1 Hmf1.
  apply (rzc_fx_seg PSEGS DCFG TBL_P IMG_P 4000 S1 U4b LCb P_main1 E mem E1 ms1 model _ TBL_P_ok IMG_P_ok certCb Hd1 bases_U4b
           shape_U4b (bases_main1' ) Ha1 Hmf1 Hh Hl).
  intros L E2 ms2 HIn Hd2 Ha2 Hrom2 Hmf2. rewrite LCb_one in HIn. destruct HIn as [<-|[]].
  assert (Ha2' : agree 200 E E2).
  { intros x Hx. rewrite (Ha1 x Hx). apply Ha2. assert (HN : (200 <= s_next U4b)%positive) by (unfold Pos.le; vm_compute; intros Hc; discriminate Hc). lia. }
  assert (HE2 : forall x, (x < 200)%positive -> E2 x = E x) by (intros x Hx; symmetry; exact (Ha2' x Hx)).
  rewrite Hrom1 in Hrom2.
  pose proof (sp0_lo sp0 Hsp) as SL. pose proof (sp0_hi sp0 Hsp) as SH.
  (* [comment removed for export] *)
  assert (R1 : getr (ms_regs ms2) 1 = Z_to_bv 64 0x561c8) by (apply (getr_leaf_c PSEGS E2 L4b); [exact Hd2 | vm_compute; reflexivity]).
  assert (R2 : getr (ms_regs ms2) 2 = Z_to_bv 64 (bv_unsigned sp0 - 576)).
  { rewrite (getr_leaf PSEGS E2 L4b ms2 2 (laddc SP0 (-576)) Hd2) by (vm_compute; reflexivity).
    rewrite lden_laddc. unfold SP0. rewrite lden_lvar, HE2 by lia. reflexivity. }
  assert (R10 : getr (ms_regs ms2) 10 = Z_to_bv 64 0x66bd8) by (apply (getr_leaf_c PSEGS E2 L4b); [exact Hd2 | vm_compute; reflexivity]).
  assert (R11 : getr (ms_regs ms2) 11 = Z_to_bv 64 0) by (apply (getr_leaf_c PSEGS E2 L4b); [exact Hd2 | vm_compute; reflexivity]).
  assert (R12 : getr (ms_regs ms2) 12 = Z_to_bv 64 0) by (apply (getr_leaf_c PSEGS E2 L4b); [exact Hd2 | vm_compute; reflexivity]).
  (* [comment removed for export] *)
  assert (HA5 : bv_unsigned (lden E2 (rg_base L4b_R5)) = 0x66bd8).
  { replace (rg_base L4b_R5) with (lconst 0x66bd8) by (vm_compute; reflexivity). apply u_lconst. lia. }
  assert (HR5 : rg_ok PSEGS E2 (ms_mem ms2) L4b_R5) by exact (sden_rg _ _ _ _ _ _ Hd2 L4b_R5_eq).
  assert (S5 : forall E0, rsz E0 L4b_R5 = 232) by (intros E0; rszv; reflexivity).
  assert (K5 : rg_kind L4b_R5 = RI) by (vm_compute; reflexivity).
  assert (F40 : rdn PSEGS (ms_mem ms2) (Z_to_bv 64 (0x66bd8 + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 - 553)))).
  { rewrite <- HA5. rewrite (rg_rdn_gb PSEGS E2 _ L4b_R5 40 8 (bvs_of (laddc SP0 (-553)) 8) HR5 ltac:(lia) ltac:(vm_compute; reflexivity)).
    rewrite bvs_of_den_lin, lden_laddc. unfold SP0. rewrite lden_lvar, HE2 by lia. unfold word_to_le_bytes. reflexivity. }
  assert (F56 : rdn PSEGS (ms_mem ms2) (Z_to_bv 64 (0x66bd8 + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 - 560)))).
  { rewrite <- HA5. rewrite (rg_rdn_gb PSEGS E2 _ L4b_R5 56 8 (bvs_of (laddc SP0 (-560)) 8) HR5 ltac:(lia) ltac:(vm_compute; reflexivity)).
    rewrite bvs_of_den_lin, lden_laddc. unfold SP0. rewrite lden_lvar, HE2 by lia. unfold word_to_le_bytes. reflexivity. }
  assert (F88 : rdn PSEGS (ms_mem ms2) (Z_to_bv 64 (0x66bd8 + 88)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 - 560)))).
  { rewrite <- HA5. rewrite (rg_rdn_gb PSEGS E2 _ L4b_R5 88 8 (bvs_of (laddc SP0 (-560)) 8) HR5 ltac:(lia) ltac:(vm_compute; reflexivity)).
    rewrite bvs_of_den_lin, lden_laddc. unfold SP0. rewrite lden_lvar, HE2 by lia. unfold word_to_le_bytes. reflexivity. }
  assert (F96 : rdn PSEGS (ms_mem ms2) (Z_to_bv 64 (0x66bd8 + 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 80))).
  { rewrite <- HA5. rewrite (rg_rdn_gb PSEGS E2 _ L4b_R5 96 8 [BK 80; BK 0; BK 0; BK 0; BK 0; BK 0; BK 0; BK 0] HR5 ltac:(lia) ltac:(vm_compute; reflexivity)).
    reflexivity. }
  assert (F120 : rdn PSEGS (ms_mem ms2) (Z_to_bv 64 (0x66bd8 + 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 2))).
  { rewrite <- HA5. rewrite (rg_rdn_img PSEGS E2 _ L4b_R5 120 4 HR5 (or_intror K5) ltac:(lia) ltac:(rewrite S5; lia)).
    - rewrite HA5. vm_compute. reflexivity.
    - intros j Hj. do 4 (destruct j as [|j]; [vm_compute; reflexivity|]). lia. }
  assert (F48 : rdn PSEGS (ms_mem ms2) (Z_to_bv 64 (0x66bd8 + 48)) 8 = Some (repeat (Z_to_bv 8 0) 8)).
  { rewrite <- HA5. rewrite (rg_rdn_gb PSEGS E2 _ L4b_R5 48 8 (repeat (BK 0) 8) HR5 ltac:(lia) ltac:(vm_compute; reflexivity)). reflexivity. }
  assert (SWF : sw_file (ms_mem ms2) 0x66bd8 (bv_unsigned sp0 - 560) (bv_unsigned sp0 - 553) 2 (Z_to_bv 64 (bv_unsigned sp0 - 560)) (Z_to_bv 64 80)).
  { constructor; assumption. }
  assert (SSP : ssp_cells (ms_mem ms2) (lden E2 (lvar 5))).
  { split.
    - assert (HR3 : rg_ok PSEGS E2 (ms_mem ms2) L4b_R3) by exact (sden_rg _ _ _ _ _ _ Hd2 L4b_R3_eq).
      assert (HA3 : bv_unsigned (lden E2 (rg_base L4b_R3)) = 0x65a18).
      { replace (rg_base L4b_R3) with (lconst 0x65a18) by (vm_compute; reflexivity). apply u_lconst. lia. }
      assert (S3 : forall E0, rsz E0 L4b_R3 = 344) by (intros E0; rszv; reflexivity).
      assert (K3 : rg_kind L4b_R3 = RO) by (vm_compute; reflexivity).
      replace (Z_to_bv 64 0x65b58) with (Z_to_bv 64 (bv_unsigned (lden E2 (rg_base L4b_R3)) + 320)) by (rewrite HA3; reflexivity).
      rewrite (rg_rdn_img PSEGS E2 _ L4b_R3 320 8 HR3 (or_introl K3) ltac:(lia) ltac:(rewrite S3; lia)).
      + rewrite HA3. vm_compute; try (f_equal; repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]); try reflexivity).
      + intros j Hj. do 8 (destruct j as [|j]; [vm_compute; reflexivity|]). lia.
    - assert (HR8 : rg_ok PSEGS E2 (ms_mem ms2) L4b_R8) by exact (sden_rg _ _ _ _ _ _ Hd2 L4b_R8_eq).
      assert (HA8 : bv_unsigned (lden E2 (rg_base L4b_R8)) = 0x97c00).
      { replace (rg_base L4b_R8) with (lconst 0x97c00) by (vm_compute; reflexivity). apply u_lconst. lia. }
      replace (Z_to_bv 64 0x97c00) with (Z_to_bv 64 (bv_unsigned (lden E2 (rg_base L4b_R8)) + 0)) by (rewrite HA8; reflexivity).
      rewrite (rg_rdn_gb PSEGS E2 _ L4b_R8 0 8 (bvs_of (lvar 5) 8) HR8 ltac:(lia) ltac:(vm_compute; reflexivity)).
      rewrite bvs_of_den_lin. reflexivity. }
  assert (HR0 : rg_ok PSEGS E2 (ms_mem ms2) L4b_R0) by exact (sden_rg _ _ _ _ _ _ Hd2 L4b_R0_eq).
  assert (HA0 : bv_unsigned (lden E2 (rg_base L4b_R0)) = bv_unsigned sp0 - 65536).
  { replace (rg_base L4b_R0) with (laddc SP0 (-65536)) by (vm_compute; reflexivity).
    rewrite lden_laddc. unfold SP0. rewrite lden_lvar, HE2 by lia. apply u_small64. unfold two64; lia. }
  assert (RDP : rdn PSEGS (ms_mem ms2) (Z_to_bv 64 (bv_unsigned sp0 - 560)) (length SUF) = Some SUF).
  { replace (Z_to_bv 64 (bv_unsigned sp0 - 560)) with (Z_to_bv 64 (bv_unsigned (lden E2 (rg_base L4b_R0)) + 64976)) by (rewrite HA0; f_equal; lia).
    rewrite (rg_rdn_gb PSEGS E2 _ L4b_R0 64976 (length SUF) [BK 32; BK 73; BK 78; BK 80; BK 85; BK 84; BK 10] HR0 ltac:(lia) ltac:(vm_compute; reflexivity)).
    vm_compute; try (f_equal; repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]); try reflexivity). }
  assert (FRM : frame_in E2 L4b 0 64848 112 (bv_unsigned sp0 - 576 - 112)).
  { exists L4b_R0. split; [exact L4b_R0_eq|]. rewrite HA0.
    replace (rg_kind L4b_R0) with RW by (vm_compute; reflexivity). rszv.
    split; [lia|]. split; [reflexivity|]. lia. }
  assert (HWF : state_wf (sw_template L4b (bv_unsigned (Z_to_bv 64 0x561c8)) 0 64848 5 (laddc SP0 (-560)) (lconst 80) (lconst 0)) = true).
  { rewrite u_small64 by (unfold two64; lia). rewrite U5b_eq. exact wf5b. }
  assert (LB : lden E2 (laddc SP0 (-560)) = Z_to_bv 64 (bv_unsigned sp0 - 560)).
  { rewrite lden_laddc. unfold SP0. rewrite lden_lvar, HE2 by lia. reflexivity. }
  apply (rzc_conseq PSEGS DCFG _ (t_emit (map (WriteEv (Z_to_bv 64 2)) (SUF ++ [])) (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model)))));
    [| unfold W, TEXIT; cbn [map]; replace (exit_code 2) with (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) by (apply bv_eq; reflexivity);
       rewrite app_nil_r; apply t_emit_cong; apply t_emit_nil_eq; apply t_emit_has_nil].
  apply (fx_stdio_write E2 L4b ms2 model _ (bv_unsigned sp0 - 576) 0x66bd8 (bv_unsigned sp0 - 560) (bv_unsigned sp0 - 553) 2
           (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (bv_unsigned sp0 - 560)) (Z_to_bv 64 80) (lden E2 (lvar 5)) (Z_to_bv 64 0x561c8) SUF []
           0 64848 5 L4b_R5 (laddc SP0 (-560)) (lconst 80) (lconst 0)
           Hd2 eq_refl eq_refl Hrom2 hok4b HWF FRM L4b_R5_eq ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(rewrite K5; reflexivity)
           R2 R10 R11 R12 R1); try lia.
  + exact SWF.
  + exact SSP.
  + exact F48.
  + exact Hfd2.
  + exact Hh.
  + exact Hl.
  + unfold TASK_SIZE. lia.
  + replace (length SUF) with 7%nat by reflexivity. lia.
  + reflexivity.
  + replace (length SUF) with 7%nat by reflexivity. cbn. lia.
  + replace (length SUF) with 7%nat by reflexivity. cbn. lia.
  + left. rewrite !u_small64 by (unfold two64; lia). lia.
  + rewrite !u_small64 by (unfold two64; lia). unfold TASK_SIZE; lia.
  + exact RDP.
  + reflexivity.
  + vm_compute. reflexivity.
  + apply t_emit_has_nil.
  + exact LB.
  + apply lden_lconst.
  + apply lden_lconst.
  + vm_compute. reflexivity.
  + vm_compute. reflexivity.
  + intros E' ms' Ha' Hd' Hpost Hrom'.
    rewrite u_small64 in Hd' by (unfold two64; lia). rewrite U5b_eq in Hd'.
    assert (Ha3 : agree 200 E E').
    { assert (HN : (200 <= s_next L4b)%positive) by (unfold Pos.le; vm_compute; intros Hc; discriminate Hc).
      intros x Hx. rewrite (Ha2' x Hx). apply Ha'. lia. }
    assert (Hmf3 : forall x, outside E (s_rgs P_main1) x -> ms_mem ms' x = mem x).
    { intros x Hx.
      pose proof (outside_nth_c E _ x 0 (laddc SP0 (-65536)) 65536 RW TEmpty Hx eq_refl ltac:(unfold two64; lia)) as X0r. cbn [RGz rg_base] in X0r.
      pose proof (outside_nth_c E _ x 5 (lconst 0x66bd8) 232 RI TEmpty Hx eq_refl ltac:(unfold two64; lia)) as X5r. cbn [RGz rg_base] in X5r.
      rewrite lden_laddc in X0r. unfold SP0 in X0r. rewrite lden_lvar in X0r. change (E 1%positive) with sp0 in X0r.
      rewrite u_small64 in X0r by (unfold two64; lia). rewrite u_lconst in X5r by lia.
      rewrite (swp_agree _ _ _ _ _ _ Hpost x); [exact (Hmf2 x Hx) | lia | lia | lia]. }
    rewrite Hrom2 in Hrom'.
    apply (rzc_fx_seg PSEGS DCFG TBL_P IMG_P 4000 S1 U5b LDb P_main1 E mem E' ms' model _ TBL_P_ok IMG_P_ok certDb Hd' bases_U5b
             shape_U5b bases_main1' Ha3 Hmf3 Hh Hl).
    intros L E3 ms3 HIn Hd3 Ha4 Hrom3 Hmf4. rewrite LDb_one in HIn. destruct HIn as [<-|[]].
    assert (Ha4' : agree 200 E E3).
    { intros x Hx. rewrite (Ha3 x Hx). apply Ha4. assert (HN : (200 <= s_next U5b)%positive) by (unfold Pos.le; vm_compute; intros Hc; discriminate Hc). lia. }
    assert (HE3 : forall x, (x < 200)%positive -> E3 x = E x) by (intros x Hx; symmetry; exact (Ha4' x Hx)).
    rewrite Hrom' in Hrom3.
    apply (fx_exit E3 L5b ms3 model (Z_to_bv 64 2) [] Hd3 eq_refl eq_refl Hrom3).
    exact (exit_pre_usage E3 ms3 Hd3 HE3 Hmf4).
Qed.
End UC.
