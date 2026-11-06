(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
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
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Frame.
From OSSVerify.Proofs.fast_float.from_chars.lib Require PDrvData PDrvMain.
From OSSVerify.Proofs.fast_float.from_chars.lib Require POpenCert.
From OSSVerify.Proofs.fast_float.from_chars.lib Require PDrvCall PDrvCall2 PDrvExit RefStdioDefs RefStartup RefStartupDefs PUsageCert POpenCert PCantCert Spec.
Import OSSVerify.Proofs.fast_float.from_chars.lib.PDrvData OSSVerify.Proofs.fast_float.from_chars.lib.PDrvMain OSSVerify.Proofs.fast_float.from_chars.lib.POpenCert.PDrvMain2 OSSVerify.Proofs.fast_float.from_chars.lib.PDrvCall OSSVerify.Proofs.fast_float.from_chars.lib.PDrvCall2 OSSVerify.Proofs.fast_float.from_chars.lib.PDrvExit OSSVerify.Proofs.fast_float.from_chars.lib.RefStdioDefs OSSVerify.Proofs.fast_float.from_chars.lib.RefStartup OSSVerify.Proofs.fast_float.from_chars.lib.RefStartupDefs OSSVerify.Proofs.fast_float.from_chars.lib.PUsageCert OSSVerify.Proofs.fast_float.from_chars.lib.POpenCert OSSVerify.Proofs.fast_float.from_chars.lib.PCantCert OSSVerify.Proofs.fast_float.from_chars.lib.Spec.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac vmz := vm_compute; first [lia | congruence | reflexivity | (intros Hc; discriminate Hc)].

Definition PREc : list byte := s2b "cli: cannot open "%string.
Definition SUFc : list byte := [Z_to_bv 8 10].

Section UBc.
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
Hypothesis Hargc2 : length av = 2%nat.
Variable model : Model.
Hypothesis Hh : m_halted model = None.
Hypothesis Hl : m_vm_lazy model = [].
Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Variable TX : TSet.
Hypothesis HTX : TX [].

Let E := E_main sp0 av ev tid (canary rdraw) regs.
Local Notation p1 := (cat_argv_ptr sp0 av ev 1).
Local Notation a1s := (nth 1 av []).

Hypothesis KCbc : forall E' ms', agree 200 E E' -> sden PSEGS E' U4bc ms' -> ms_rom ms' = seg_rom PSEGS ->
  (forall x, outside E (s_rgs P_main2) x -> ms_mem ms' x = mem x) -> (63 < Z.of_nat (length a1s))%Z ->
  realizes PSEGS (mkCfg ms' model) (t_emit (W 2 SUFc) TX).
Hypothesis KCac : forall E' ms', agree 200 E E' -> sden PSEGS E' U4ac ms' -> ms_rom ms' = seg_rom PSEGS ->
  (forall x, outside E (s_rgs P_main2) x -> ms_mem ms' x = mem x) ->
  (exists rest, length rest = (63 - length a1s)%nat /\ u8arr PSEGS (ms_mem ms') (bv_unsigned sp0 - 543) (a1s ++ rest)) ->
  (Z.of_nat (length a1s) <= 63)%Z ->
  realizes PSEGS (mkCfg ms' model) (t_emit (W 2 (PREc ++ a1s ++ SUFc)) TX).

#[using="Type"] Lemma bases_U2 : bases_wf (s_next U_c2) (s_rgs U_c2) = true. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma shape_U2 : shape (s_rgs U_c2) = shape (s_rgs P_main2). Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma bases_L2 : bases_wf (s_next L2c) (s_rgs L2c) = true. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma shape_L2 : shape (s_rgs L2c) = shape (s_rgs P_main2). Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma bases_main2 : bases_wf (s_next P_main2) (s_rgs P_main2) = true. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.

#[using="uid hw Hsp Hva Hve Hfits Htid ME Hargc2 Hh Hl Hfd2 KCbc KCac"] Theorem cant_B : forall E1 ms1, agree 200 E E1 -> sden PSEGS E1 U_c2 ms1 -> ms_rom ms1 = seg_rom PSEGS ->
  (forall x, outside E (s_rgs P_main2) x -> ms_mem ms1 x = mem x) ->
  realizes PSEGS (mkCfg ms1 model) (t_emit (W 2 (PREc ++ a1s ++ SUFc)) TX).
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Hfits Htid ME Hargc2 Hh Hl Hfd2 KCbc KCac : LiaFast.U) => LiaFast.u0).
  intros E1 ms1 Ha1 Hd1 Hrom1 Hmf1.
  apply (rzc_fx_seg PSEGS DCFG TBL_P IMG_P 4000 S2 U_c2 LB1c P_main2 E mem E1 ms1 model _ TBL_P_ok IMG_P_ok certB1c Hd1 bases_U2
           shape_U2 bases_main2 Ha1 Hmf1 Hh Hl).
  intros L E2 ms2 HIn Hd2 Ha2 Hrom2 Hmf2. rewrite LB1c_one in HIn. destruct HIn as [<-|[]].
  assert (Ha2' : agree 200 E E2).
  { intros x Hx. rewrite (Ha1 x Hx). apply Ha2. assert (HN : (200 <= s_next U_c2)%positive) by (unfold Pos.le; vm_compute; intros Hc; discriminate Hc). lia. }
  apply (rzc_fx_seg PSEGS DCFG TBL_P IMG_P 4000 S2 L2c LB2c P_main2 E mem E2 ms2 model _ TBL_P_ok IMG_P_ok certB2c Hd2 bases_L2
           shape_L2 bases_main2 Ha2' Hmf2 Hh Hl).
  intros L E3 ms3 HIn Hd3 Ha3 Hrom3 Hmf3. rewrite LB2c_two in HIn.
  assert (Ha3' : agree 200 E E3).
  { intros x Hx. rewrite (Ha2' x Hx). apply Ha3. assert (HN : (200 <= s_next L2c)%positive) by (unfold Pos.le; vm_compute; intros Hc; discriminate Hc). lia. }
  assert (HE3 : forall x, (x < 200)%positive -> E3 x = E x) by (intros x Hx; symmetry; exact (Ha3' x Hx)).
  rewrite Hrom2, Hrom1 in Hrom3.
  destruct HIn as [<-|[<-|[]]].
  - (* [comment removed for export] *)
    pose proof (p1_bounds sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2) as (B1 & B2 & B3).
    pose proof (sp0_lo sp0 Hsp) as SL. pose proof (sp0_hi sp0 Hsp) as SH.
    set (K := length a1s).
    pose proof (valid_argv_str_len av 1 Hva ltac:(lia)) as HKb. fold K in HKb.
    (* [comment removed for export] *)
    assert (HK63 : 63 < Z.of_nat K).
    { assert (Hf : In (FCond BC_GEU (lconst 63) (lvar 8) false) (s_facts L3bc)) by (vm_compute; tauto).
      pose proof (sden_fact PSEGS E3 L3bc ms3 _ Hd3 Hf) as HF. cbn [fact_ok branch_taken] in HF.
      rewrite lden_lconst, lden_lvar, HE3 in HF by lia. change (E 8%positive) with (Z_to_bv 64 (Z.of_nat K)) in HF.
      destruct (bv_ltu (Z_to_bv 64 63) (Z_to_bv 64 (Z.of_nat K))) eqn:HL; [|discriminate].
      unfold bv_ltu in HL. apply Z.ltb_lt in HL. rewrite !u_small64 in HL by (unfold two64; lia). lia. }
    (* [comment removed for export] *)
    assert (R1 : getr (ms_regs ms3) 1 = Z_to_bv 64 0x55000) by (apply (getr_leaf_c PSEGS E3 L3bc); [exact Hd3 | vm_compute; reflexivity]).
    assert (R2 : getr (ms_regs ms3) 2 = Z_to_bv 64 (bv_unsigned sp0 - 1120)).
    { rewrite (getr_leaf PSEGS E3 L3bc ms3 2 (laddc SP0 (-1120)) Hd3) by (vm_compute; reflexivity).
      rewrite lden_laddc. unfold SP0. rewrite lden_lvar, HE3 by lia. reflexivity. }
    assert (R10 : getr (ms_regs ms3) 10 = Z_to_bv 64 0x64e20) by (apply (getr_leaf_c PSEGS E3 L3bc); [exact Hd3 | vm_compute; reflexivity]).
    assert (R11 : getr (ms_regs ms3) 11 = p1).
    { rewrite (getr_leaf PSEGS E3 L3bc ms3 11 (lvar 4) Hd3) by (vm_compute; reflexivity). rewrite lden_lvar, HE3 by lia. exact (E_P1 sp0 av ev tid rdraw regs Hargc2). }
    assert (R12 : getr (ms_regs ms3) 12 = Z_to_bv 64 (Z.of_nat K)).
    { rewrite (getr_leaf PSEGS E3 L3bc ms3 12 (lvar 8) Hd3) by (vm_compute; reflexivity). rewrite lden_lvar, HE3 by lia. reflexivity. }
    (* [comment removed for export] *)
    assert (HA5 : bv_unsigned (lden E3 (rg_base (rgn L3bc 5))) = 0x64e20).
    { replace (rg_base (rgn L3bc 5)) with (lconst 0x64e20) by (vm_compute; reflexivity). apply u_lconst. lia. }
    assert (HR5 : rg_ok PSEGS E3 (ms_mem ms3) (rgn L3bc 5)) by exact (sden_rg _ _ _ _ _ _ Hd3 (rgn_eq L3bc 5 ltac:(vm_compute; lia))).
    assert (HIB : forall j, (0 <= j < 8)%nat -> True) by auto.
    assert (F40 : rdn PSEGS (ms_mem ms3) (Z_to_bv 64 (0x64e20 + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 - 543)))).
    { rewrite <- HA5. rewrite (rg_rdn_gb PSEGS E3 _ (rgn L3bc 5) 40 8 (bvs_of (laddc SP0 (-543)) 8) HR5 ltac:(lia) ltac:(vm_compute; reflexivity)).
      rewrite bvs_of_den_lin, lden_laddc. unfold SP0. rewrite lden_lvar, HE3 by lia. unfold word_to_le_bytes. reflexivity. }
    assert (F56 : rdn PSEGS (ms_mem ms3) (Z_to_bv 64 (0x64e20 + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 - 560)))).
    { rewrite <- HA5. rewrite (rg_rdn_gb PSEGS E3 _ (rgn L3bc 5) 56 8 (bvs_of (laddc SP0 (-560)) 8) HR5 ltac:(lia) ltac:(vm_compute; reflexivity)).
      rewrite bvs_of_den_lin, lden_laddc. unfold SP0. rewrite lden_lvar, HE3 by lia. unfold word_to_le_bytes. reflexivity. }
    assert (F88 : rdn PSEGS (ms_mem ms3) (Z_to_bv 64 (0x64e20 + 88)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 - 560)))).
    { rewrite <- HA5. rewrite (rg_rdn_gb PSEGS E3 _ (rgn L3bc 5) 88 8 (bvs_of (laddc SP0 (-560)) 8) HR5 ltac:(lia) ltac:(vm_compute; reflexivity)).
      rewrite bvs_of_den_lin, lden_laddc. unfold SP0. rewrite lden_lvar, HE3 by lia. unfold word_to_le_bytes. reflexivity. }
    assert (F96 : rdn PSEGS (ms_mem ms3) (Z_to_bv 64 (0x64e20 + 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 80))).
    { rewrite <- HA5. rewrite (rg_rdn_gb PSEGS E3 _ (rgn L3bc 5) 96 8 [BK 80; BK 0; BK 0; BK 0; BK 0; BK 0; BK 0; BK 0] HR5 ltac:(lia) ltac:(vm_compute; reflexivity)).
      reflexivity. }
    assert (F120 : rdn PSEGS (ms_mem ms3) (Z_to_bv 64 (0x64e20 + 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 2))).
    { assert (S5 : forall E0, rsz E0 (rgn L3bc 5) = 232) by (intros E0; rszv; reflexivity).
      assert (K5 : rg_kind (rgn L3bc 5) = RI) by (vm_compute; reflexivity).
      rewrite <- HA5. rewrite (rg_rdn_img PSEGS E3 _ (rgn L3bc 5) 120 4 HR5 (or_intror K5) ltac:(lia) ltac:(rewrite S5; lia)).
      - rewrite HA5. vm_compute. reflexivity.
      - intros j Hj. do 4 (destruct j as [|j]; [vm_compute; reflexivity|]). lia. }
    assert (F48 : rdn PSEGS (ms_mem ms3) (Z_to_bv 64 (0x64e20 + 48)) 8 = Some (repeat (Z_to_bv 8 0) 8)).
    { assert (S5 : forall E0, rsz E0 (rgn L3bc 5) = 232) by (intros E0; rszv; reflexivity).
      assert (K5 : rg_kind (rgn L3bc 5) = RI) by (vm_compute; reflexivity).
      rewrite <- HA5. rewrite (rg_rdn_img PSEGS E3 _ (rgn L3bc 5) 48 8 HR5 (or_intror K5) ltac:(lia) ltac:(rewrite S5; lia)).
      - rewrite HA5. vm_compute. reflexivity.
      - intros j Hj. do 8 (destruct j as [|j]; [vm_compute; reflexivity|]). lia. }
    assert (SWF : sw_file (ms_mem ms3) 0x64e20 (bv_unsigned sp0 - 560) (bv_unsigned sp0 - 543) 2 (Z_to_bv 64 (bv_unsigned sp0 - 560)) (Z_to_bv 64 80)).
    { constructor; assumption. }
    assert (SSP : ssp_cells (ms_mem ms3) (lden E3 (lvar 5))).
    { split.
      - assert (HR3 : rg_ok PSEGS E3 (ms_mem ms3) (rgn L3bc 3)) by exact (sden_rg _ _ _ _ _ _ Hd3 (rgn_eq L3bc 3 ltac:(vm_compute; lia))).
        assert (HA3 : bv_unsigned (lden E3 (rg_base (rgn L3bc 3))) = 0x63c60).
        { replace (rg_base (rgn L3bc 3)) with (lconst 0x63c60) by (vm_compute; reflexivity). apply u_lconst. lia. }
        assert (S3 : forall E0, rsz E0 (rgn L3bc 3) = 344) by (intros E0; rszv; reflexivity).
        assert (K3 : rg_kind (rgn L3bc 3) = RO) by (vm_compute; reflexivity).
        replace (Z_to_bv 64 0x63da0) with (Z_to_bv 64 (bv_unsigned (lden E3 (rg_base (rgn L3bc 3))) + 320)) by (rewrite HA3; reflexivity).
        rewrite (rg_rdn_img PSEGS E3 _ (rgn L3bc 3) 320 8 HR3 (or_introl K3) ltac:(lia) ltac:(rewrite S3; lia)).
        + rewrite HA3. vm_compute; try (f_equal; repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]); try reflexivity).
        + intros j Hj. do 8 (destruct j as [|j]; [vm_compute; reflexivity|]). lia.
      - assert (HR8 : rg_ok PSEGS E3 (ms_mem ms3) (rgn L3bc 8)) by exact (sden_rg _ _ _ _ _ _ Hd3 (rgn_eq L3bc 8 ltac:(vm_compute; lia))).
        assert (HA8 : bv_unsigned (lden E3 (rg_base (rgn L3bc 8))) = 0x95e40).
        { replace (rg_base (rgn L3bc 8)) with (lconst 0x95e40) by (vm_compute; reflexivity). apply u_lconst. lia. }
        replace (Z_to_bv 64 0x95e40) with (Z_to_bv 64 (bv_unsigned (lden E3 (rg_base (rgn L3bc 8))) + 0)) by (rewrite HA8; reflexivity).
        rewrite (rg_rdn_gb PSEGS E3 _ (rgn L3bc 8) 0 8 (bvs_of (lvar 5) 8) HR8 ltac:(lia) ltac:(vm_compute; reflexivity)).
        rewrite bvs_of_den_lin. reflexivity. }
    assert (RDP : rdn PSEGS (ms_mem ms3) (Z_to_bv 64 (bv_unsigned sp0 - 560)) (length PREc) = Some PREc).
    { assert (HR0 : rg_ok PSEGS E3 (ms_mem ms3) (rgn L3bc 0)) by exact (sden_rg _ _ _ _ _ _ Hd3 (rgn_eq L3bc 0 ltac:(vm_compute; lia))).
      assert (HA0 : bv_unsigned (lden E3 (rg_base (rgn L3bc 0))) = bv_unsigned sp0 - 65536).
      { replace (rg_base (rgn L3bc 0)) with (laddc SP0 (-65536)) by (vm_compute; reflexivity).
        rewrite lden_laddc. unfold SP0. rewrite lden_lvar, HE3 by lia. apply u_small64. unfold two64; lia. }
      replace (Z_to_bv 64 (bv_unsigned sp0 - 560)) with (Z_to_bv 64 (bv_unsigned (lden E3 (rg_base (rgn L3bc 0))) + 64976)) by (rewrite HA0; f_equal; lia).
      rewrite (rg_rdn_gb PSEGS E3 _ (rgn L3bc 0) 64976 (length PREc) [BK 99; BK 108; BK 105; BK 58; BK 32; BK 99; BK 97; BK 110; BK 110; BK 111; BK 116; BK 32; BK 111; BK 112; BK 101; BK 110; BK 32] HR0 ltac:(lia) ltac:(vm_compute; reflexivity)).
      vm_compute; try (f_equal; repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]); try reflexivity). }
    assert (RDE : rdn PSEGS (ms_mem ms3) p1 K = Some a1s).
    { pose proof (rdn_ext_rd1 PSEGS (ms_mem ms3) mem (bv_unsigned p1) K) as RX. rewrite Z_to_bv_bv_unsigned in RX.
      rewrite RX; [| lia | unfold two64; lia |].
      - rewrite (main_entry_rdn_above sp0 av ev uid tid hw rdraw regs mem ME) by lia.
        change (wrap_mem RPH sp0 av ev uid hw rdraw) with (wmem RPH sp0 av ev uid hw rdraw).
        rewrite (rdn_wmem_stack PSEGS RPH sp0 av ev uid hw rdraw) by lia.
        exact (read_argv_str_k RPH PSEGS sp0 av ev 1 uid hw rdraw ltac:(lia)
                 (bsb_nw RPH sp0 av ev uid hw rdraw Hva Hve SH)).
      - intros i Hi. unfold rd1. rewrite Hmf3; [reflexivity|].
        apply (outside_main2_hi sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2); rewrite u_small64 by (unfold two64; lia); lia. }
    assert (FRM : frame_in E3 L3bc 0 64304 112 (bv_unsigned sp0 - 1120 - 112)).
    { exists (rgn L3bc 0). split; [exact (rgn_eq L3bc 0 ltac:(vm_compute; lia))|].
      replace (rg_base (rgn L3bc 0)) with (laddc SP0 (-65536)) by (vm_compute; reflexivity).
      replace (rg_kind (rgn L3bc 0)) with RW by (vm_compute; reflexivity). rszv.
      rewrite lden_laddc. unfold SP0. rewrite lden_lvar, HE3 by lia. change (E 1%positive) with sp0.
      rewrite u_small64 by (unfold two64; lia). split; [lia|]. split; [reflexivity|]. lia. }
    (* [comment removed for export] *)
    assert (HT : bv_unsigned p1 + Z.of_nat K <= TASK_SIZE).
    { pose proof (argv1_top sp0 av ev uid hw rdraw Hsp Hva Hve Hargc2 Hfits) as AT. fold K in AT. lia. }
    apply (rzc_conseq PSEGS DCFG _ (t_emit (W 2 (PREc ++ a1s)) (t_emit (W 2 SUFc) TX))); [| unfold W; replace (map (WriteEv (Z_to_bv 64 2)) (PREc ++ a1s ++ SUFc)) with (map (WriteEv (Z_to_bv 64 2)) (PREc ++ a1s) ++ map (WriteEv (Z_to_bv 64 2)) SUFc) by (rewrite <- map_app, app_assoc; reflexivity); apply t_emit_app].
    assert (HWF : state_wf (sw_template L3bc (bv_unsigned (Z_to_bv 64 0x55000)) 0 64304 5 (laddc SP0 (-560)) (lconst 80) (lvar 8)) = true).
    { rewrite u_small64 by (unfold two64; lia). rewrite U4bc_eq. exact wf4bc. }
    assert (LB : lden E3 (laddc SP0 (-560)) = Z_to_bv 64 (bv_unsigned sp0 - 560)).
    { rewrite lden_laddc. unfold SP0. rewrite lden_lvar, HE3 by lia. reflexivity. }
    assert (LR : lden E3 (lvar 8) = Z_to_bv 64 (Z.of_nat K)) by (rewrite lden_lvar, HE3 by lia; reflexivity).
    apply (fx_stdio_write E3 L3bc ms3 model (t_emit (W 2 SUFc) TX) (bv_unsigned sp0 - 1120) 0x64e20 (bv_unsigned sp0 - 560) (bv_unsigned sp0 - 543) 2
             p1 (Z_to_bv 64 (Z.of_nat K)) (Z_to_bv 64 (bv_unsigned sp0 - 560)) (Z_to_bv 64 80) (lden E3 (lvar 5)) (Z_to_bv 64 0x55000) PREc a1s
             0 64304 5 (rgn L3bc 5) (laddc SP0 (-560)) (lconst 80) (lvar 8)
             Hd3 eq_refl eq_refl Hrom3 hok3bc HWF FRM (rgn_eq L3bc 5 ltac:(vm_compute; lia)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             R2 R10 R11 R12 R1); try lia.
    + exact SWF.
    + exact SSP.
    + exact F48.
    + exact Hfd2.
    + exact Hh.
    + exact Hl.
    + replace (length PREc) with 17%nat by reflexivity. lia.
    + rewrite u_small64 by (unfold two64; lia). reflexivity.
    + replace (length PREc) with 17%nat by reflexivity. lia.
    + replace (length PREc) with 17%nat by reflexivity. lia.
    + rewrite u_small64 by (unfold two64; lia). exact HT.
    + exact RDP.
    + exact RDE.
    + vm_compute. reflexivity.
    + apply t_emit_has_nil.
    + exact LB.
    + apply lden_lconst.
    + exact LR.
    + vm_compute. reflexivity.
    + vm_compute. reflexivity.
    + intros E' ms' Ha' Hd' Hpost Hrom'.
      apply (KCbc E' ms').
      * assert (HN : (200 <= s_next L3bc)%positive) by (unfold Pos.le; vm_compute; intros Hc; discriminate Hc).
        intros x Hx. rewrite (Ha3' x Hx). apply Ha'. lia.
      * rewrite u_small64 in Hd' by (unfold two64; lia). rewrite U4bc_eq in Hd'. exact Hd'.
      * rewrite Hrom'. exact Hrom3.
      * intros x Hx.
        pose proof (outside_nth_c E _ x 0 (laddc SP0 (-65536)) 65536 RW TEmpty Hx eq_refl ltac:(unfold two64; lia)) as X0r. cbn [RGz rg_base] in X0r.
        pose proof (outside_nth_c E _ x 5 (lconst 0x64e20) 232 RI TEmpty Hx eq_refl ltac:(unfold two64; lia)) as X5r. cbn [RGz rg_base] in X5r.
        rewrite lden_laddc in X0r. unfold SP0 in X0r. rewrite lden_lvar in X0r. change (E 1%positive) with sp0 in X0r.
        rewrite u_small64 in X0r by (unfold two64; lia). rewrite u_lconst in X5r by lia.
        rewrite (swp_agree _ _ _ _ _ _ Hpost x); [exact (Hmf3 x Hx) | lia | lia | lia].
      * exact HK63.
  - (* [comment removed for export] *)
    pose proof (p1_bounds sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2) as (B1 & B2 & B3).
    pose proof (sp0_lo sp0 Hsp) as SL. pose proof (sp0_hi sp0 Hsp) as SH.
    set (K := length a1s).
    pose proof (valid_argv_str_len av 1 Hva ltac:(lia)) as HKb. fold K in HKb.
    assert (HK63 : Z.of_nat K <= 63).
    { assert (Hf : In (FCond BC_GEU (lconst 63) (lvar 8) true) (s_facts L3ac)) by (vm_compute; tauto).
      pose proof (sden_fact PSEGS E3 L3ac ms3 _ Hd3 Hf) as HF. cbn [fact_ok branch_taken] in HF.
      rewrite lden_lconst, lden_lvar, HE3 in HF by lia. change (E 8%positive) with (Z_to_bv 64 (Z.of_nat K)) in HF.
      destruct (bv_ltu (Z_to_bv 64 63) (Z_to_bv 64 (Z.of_nat K))) eqn:HL; [discriminate|].
      unfold bv_ltu in HL. apply Z.ltb_ge in HL. rewrite !u_small64 in HL by (unfold two64; lia). lia. }
    (* [comment removed for export] *)
    assert (R1 : getr (ms_regs ms3) 1 = Z_to_bv 64 0x53e98) by (apply (getr_leaf_c PSEGS E3 L3ac); [exact Hd3 | vm_compute; reflexivity]).
    assert (R10 : getr (ms_regs ms3) 10 = Z_to_bv 64 (bv_unsigned sp0 - 543)).
    { rewrite (getr_leaf PSEGS E3 L3ac ms3 10 (laddc SP0 (-543)) Hd3) by (vm_compute; reflexivity).
      rewrite lden_laddc. unfold SP0. rewrite lden_lvar, HE3 by lia. reflexivity. }
    assert (R11 : getr (ms_regs ms3) 11 = p1).
    { rewrite (getr_leaf PSEGS E3 L3ac ms3 11 (lvar 4) Hd3) by (vm_compute; reflexivity). rewrite lden_lvar, HE3 by lia. exact (E_P1 sp0 av ev tid rdraw regs Hargc2). }
    assert (R12 : getr (ms_regs ms3) 12 = Z_to_bv 64 (Z.of_nat K)).
    { rewrite (getr_leaf PSEGS E3 L3ac ms3 12 (lvar 8) Hd3) by (vm_compute; reflexivity). rewrite lden_lvar, HE3 by lia. reflexivity. }
    (* [comment removed for export] *)
    destruct (u8arr_of_rg E3 L3ac ms3 0 (rgn L3ac 0) 64993 63 Hd3 (rgn_eq L3ac 0 ltac:(vm_compute; lia)) ltac:(vm_compute; reflexivity) ltac:(lia)
                ltac:(vmz)) as (old63 & Hlold63 & Hu863).
    replace (rg_base (rgn L3ac 0)) with (laddc SP0 (-65536)) in Hu863 by (vm_compute; reflexivity). rewrite lden_laddc in Hu863. unfold SP0 in Hu863. rewrite lden_lvar, HE3 in Hu863 by lia. change (E 1%positive) with sp0 in Hu863.
    rewrite u_small64 in Hu863 by (unfold two64; lia).
    rewrite <- (firstn_skipn K old63) in Hu863. apply u8arr_app in Hu863 as [Hu8 Hu8r].
    replace (bv_unsigned sp0 + -65536 + 64993) with (bv_unsigned sp0 - 543) in Hu8, Hu8r by lia.
    set (old := firstn K old63) in *. set (rest := skipn K old63) in *.
    assert (Hlold : length old = K) by (unfold old; rewrite firstn_length; lia).
    assert (Hlrest : length rest = (63 - K)%nat) by (unfold rest; rewrite skipn_length; lia).
    (* [comment removed for export] *)
    assert (RDE : rdn PSEGS (ms_mem ms3) (Z_to_bv 64 (bv_unsigned p1)) (length a1s) = Some a1s).
    { rewrite Z_to_bv_bv_unsigned.
      pose proof (rdn_ext_rd1 PSEGS (ms_mem ms3) mem (bv_unsigned p1) K) as RX. rewrite Z_to_bv_bv_unsigned in RX.
      fold K. rewrite RX; [| lia | unfold two64; lia |].
      - rewrite (main_entry_rdn_above sp0 av ev uid tid hw rdraw regs mem ME) by lia.
        change (wrap_mem RPH sp0 av ev uid hw rdraw) with (wmem RPH sp0 av ev uid hw rdraw).
        rewrite (rdn_wmem_stack PSEGS RPH sp0 av ev uid hw rdraw) by lia.
        exact (read_argv_str_k RPH PSEGS sp0 av ev 1 uid hw rdraw ltac:(lia)
                 (bsb_nw RPH sp0 av ev uid hw rdraw Hva Hve SH)).
      - intros i Hi. unfold rd1. rewrite Hmf3; [reflexivity|].
        apply (outside_main2_hi sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2); rewrite u_small64 by (unfold two64; lia); lia. }
    pose proof (bytes_at_of_rdn (ms_mem ms3) (bv_unsigned p1) a1s ltac:(lia) ltac:(unfold two64; lia) RDE) as Hbs.
    (* [comment removed for export] *)
    pose proof (fx_weaken PSEGS E3 L3ac ms3 RG3ac (split_ws 22 0 65056) Hd3 wk3ac L3ac'_wf) as Hd3'. fold L3ac' in Hd3'.
    (* [comment removed for export] *)
    assert (HE4 : E 4%positive = p1) by exact (E_P1 sp0 av ev tid rdraw regs Hargc2).
    assert (NOFP : Forall (fun R => bv_unsigned (lden E3 (rg_base R)) + rsz E3 R <= bv_unsigned sp0 - 543 \/
                                     bv_unsigned sp0 - 480 <= bv_unsigned (lden E3 (rg_base R))) RG3ac).
    { unfold RG3ac. repeat (apply Forall_cons; [rsz_simpl; cbn [RGz rg_base rg_size];
        rewrite ?u_lin0 by lia; rewrite ?u_lin1, ?u_lin2; rewrite ?HE3 by lia;
        change (E 1%positive) with sp0; rewrite ?HE4; change (E 8%positive) with (Z_to_bv 64 (Z.of_nat K));
        rewrite ?u_small64 by (unfold two64; lia); lia |]).
      apply Forall_nil. }
    assert (Hu8' : u8arr PSEGS (ms_mem ms3) (bv_unsigned (Z_to_bv 64 (bv_unsigned sp0 - 543))) old)
      by (rewrite u_small64 by (unfold two64; lia); exact Hu8).
    apply (fx_memcpy E3 L3ac' ms3 model _ (Z_to_bv 64 (bv_unsigned sp0 - 543)) p1 (Z.of_nat K) a1s old [] (laddc SP0 (-543))
             Hd3' eq_refl eq_refl hok3ac Hrom3 R10 R11 R12 ltac:(rewrite R1; vm_compute; reflexivity) Hbs Hu8' ltac:(fold K; lia) ltac:(fold K; reflexivity));
      [ rewrite u_small64 by (unfold two64; lia); lia
      | rewrite u_small64 by (unfold two64; lia); unfold two64 in *; lia
      | unfold two64 in *; lia
      | rewrite lden_laddc; unfold SP0; rewrite lden_lvar, HE3 by lia; reflexivity
      | | exact Hh | exact Hl | ].
    + intros i R x Hi Hin Hx. exfalso. unfold in_rg in Hin. rewrite u_small64 in Hx by (unfold two64; lia).
      cbn [s_rgs L3ac' with_rgs] in Hi. pose proof (nth_error_In _ _ Hi) as HI. rewrite Forall_forall in NOFP.
      destruct (NOFP R HI) as [Hc|Hc]; lia.
    + intros E' ms' Ha' Hd' Hout Hgrow Hbs' Hrom'.
      apply (KCac E' ms').
      * assert (HN : (200 <= s_next L3ac')%positive) by (unfold Pos.le; vm_compute; intros Hc; discriminate Hc).
        intros x Hx. rewrite (Ha3' x Hx). apply Ha'. lia.
      * rewrite R1 in Hd'. replace (bv_unsigned (Z_to_bv 64 0x53e98)) with 0x53e98 in Hd' by (vm_compute; reflexivity).
        rewrite U4ac_eq in Hd'. exact Hd'.
      * rewrite Hrom'. exact Hrom3.
      * intros x Hx. rewrite Hout; [exact (Hmf3 x Hx)|]. rewrite u_small64 by (unfold two64; lia).
        pose proof (outside_nth_c E _ x 0 (laddc SP0 (-65536)) 65536 RW TEmpty Hx eq_refl ltac:(unfold two64; lia)) as X0r. cbn [RGz rg_base] in X0r.
        rewrite lden_laddc in X0r. unfold SP0 in X0r. rewrite lden_lvar in X0r. change (E 1%positive) with sp0 in X0r.
        rewrite u_small64 in X0r by (unfold two64; lia). lia.
      * exists rest. split; [exact Hlrest|]. apply u8arr_app. split.
        -- rewrite u_small64 in Hbs' by (unfold two64; lia). split; [exact Hbs'|].
           destruct Hu8 as [_ Hw]. rewrite Hlold in Hw. fold K. eapply OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.wr_at_transport; [exact Hw|]. exact Hgrow.
        -- apply (u8arr_ext (ms_mem ms3)); [fold K; rewrite Hlold in Hu8r; exact Hu8r|]. intros x Hx. rewrite Hlrest in Hx. apply Hout.
           rewrite u_small64 by (unfold two64; lia). fold K in Hx |- *. lia.
      * exact HK63.
Qed.
End UBc.
