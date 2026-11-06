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
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import UDrvData UDrvMain UDrvCall UDrvCall2 UDrvExit UbStdioDefs UbExitBase UbStartup UbStartupDefs.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import UUsageCert UUsageCert2 UUsage2 UUsage3 Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma tail_1 : forall (bs : list byte) fs,
  t_eq (t_emit (map (WriteEv (Z_to_bv 64 2)) (bs ++ [])) (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) fs)))
       (t_emit (W 2 bs) (t_exit (exit_code 2) fs)).
Proof.
  intros bs fs. rewrite app_nil_r. unfold W. replace (exit_code 2) with (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) by (apply bv_eq; reflexivity).
  apply t_emit_cong. cbn [map]. apply t_emit_nil_eq. apply t_emit_has_nil.
Qed.

Lemma tail_2 : forall (bs : list byte) fs,
  t_eq (t_emit (map (WriteEv (Z_to_bv 64 2)) bs) (t_emit (map (WriteEv (Z_to_bv 64 2)) ([] ++ []))
          (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) fs))))
       (t_emit (W 2 bs) (t_exit (exit_code 2) fs)).
Proof.
  intros bs fs. unfold W. replace (exit_code 2) with (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) by (apply bv_eq; reflexivity).
  apply t_emit_cong. cbn [map app]. eapply t_eq_trans; [apply t_emit_nil_eq; apply t_emit_has_nil|].
  apply t_emit_nil_eq. apply t_emit_has_nil.
Qed.

Lemma outside_not_in_rg : forall E rgs x i R, outside E rgs x -> nth_error rgs i = Some R -> in_rg E R x -> False.
Proof. intros E rgs x i R H Hi Hin. pose proof (outside_nth E rgs x i R H Hi). unfold in_rg in Hin. lia. Qed.

Lemma u_lin_negx : forall E c x, 0 <= c - bv_unsigned (E x) < 2^64 ->
  bv_unsigned (lden E (LIN c [(x, 18446744073709551615)])) = c - bv_unsigned (E x).
Proof.
  intros E c x H. unfold lden, lz. cbn [l_c l_t tsum]. unfold vz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616.
  replace (c + (18446744073709551615 * bv_unsigned (E x) + 0)) with ((c - bv_unsigned (E x)) + bv_unsigned (E x) * 18446744073709551616) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma mod_sp : forall (s k c : Z), 0 <= s + c - 18446744073709551616 + k < 2^64 ->
  (c + s + k) mod 2^64 = s + c - 18446744073709551616 + k.
Proof.
  intros s k c H. replace (c + s + k) with ((s + c - 18446744073709551616 + k) + 1 * 18446744073709551616) by lia.
  change (2^64) with 18446744073709551616. rewrite Z_mod_plus_full. apply Z.mod_small. exact H.
Qed.

Ltac vmz := vm_compute; first [lia | congruence | reflexivity | (intros Hc; discriminate Hc)].

Section UCa.
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
Local Notation a0s := (nth 0 av []).

#[using="Hsp"] Lemma SL : 0x7fff80000000 <= bv_unsigned sp0. Proof. LiaFast.lf_pins (fun (Hsp : LiaFast.U) => LiaFast.u0). exact (sp0_lo sp0 Hsp). Qed.
#[using="Hsp"] Lemma SH : bv_unsigned sp0 <= 0x800000000000. Proof. LiaFast.lf_pins (fun (Hsp : LiaFast.U) => LiaFast.u0). exact (sp0_hi sp0 Hsp). Qed.

#[using="Hsp Hargc"] Lemma u_sp0 : forall E' c, (forall x, (x < 200)%positive -> E' x = E x) -> -65536 <= c <= 0 ->
  bv_unsigned (lden E' (laddc SP0 c)) = bv_unsigned sp0 + c.
Proof. LiaFast.lf_pins (fun (Hsp Hargc : LiaFast.U) => LiaFast.u0).
  intros E' c HE Hc. pose proof SL. pose proof SH. rewrite lden_laddc. unfold SP0. rewrite lden_lvar, HE by lia.
  apply u_small64. unfold two64; lia.
Qed.

#[using="Hargc"] Lemma lden_sp0 : forall E' c, (forall x, (x < 200)%positive -> E' x = E x) -> -65536 <= c <= 0 ->
  lden E' (laddc SP0 c) = Z_to_bv 64 (bv_unsigned sp0 + c).
Proof. LiaFast.lf_pins (fun (Hargc : LiaFast.U) => LiaFast.u0). intros E' c HE Hc. rewrite lden_laddc. unfold SP0. rewrite lden_lvar, HE by lia. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Hsp Hargc"] Lemma outside_split_main1 : forall E' rgs x, agree 200 E E' -> shape rgs = shape (s_rgs U4a) ->
  outside E (s_rgs P_main1) x -> outside E' rgs x.
Proof. LiaFast.lf_pins (fun (Hsp Hargc : LiaFast.U) => LiaFast.u0).
  intros E' rgs x Ha Hs H. pose proof SL as Q1. pose proof SH as Q2.
  assert (HE : forall y, (y < 200)%positive -> E' y = E y) by (intros y Hy; symmetry; exact (Ha y Hy)).
  apply (outside_agree 200 E E' _ x bases_main1' Ha) in H.
  apply (outside_shape E' (RGz (laddc SP0 (-65536)) 64983 RW TEmpty :: tl (s_rgs P_main1) ++ [RGz (laddc SP0 (-480)) 480 RW TEmpty]));
    [rewrite Hs; vm_compute; reflexivity|].
  change (s_rgs P_main1) with (RGz (laddc SP0 (-65536)) 65536 RW TEmpty :: tl (s_rgs P_main1)) in H.
  pose proof (Forall_inv H) as H0. pose proof (Forall_inv_tail H) as Ht. cbv beta in H0. rsz_simpl_in H0; cbn [RGz rg_base rg_size] in H0.
  rewrite (u_sp0 E' (-65536) HE) in H0 by lia.
  constructor; [rsz_simpl; cbn [RGz rg_base rg_size]; rewrite (u_sp0 E' (-65536) HE) by lia; lia|].
  apply Forall_app. split; [exact Ht|]. constructor; [|constructor].
  rsz_simpl; cbn [RGz rg_base rg_size]. rewrite (u_sp0 E' (-480) HE) by lia. lia.
Qed.

#[using="uid hw Hsp Hva Hve Hargc"] Lemma window_outside : forall E' rgs x, agree 200 E E' -> shape rgs = shape (s_rgs U4a) ->
  bv_unsigned sp0 - 553 <= bv_unsigned x < bv_unsigned sp0 - 480 -> outside E' rgs x.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Hargc : LiaFast.U) => LiaFast.u0).
  intros E' rgs x Ha Hs Hx. pose proof SL. pose proof SH.
  pose proof (p0_bounds sp0 av ev uid hw rdraw Hsp Hva Hve) as (B1 & B2 & B3).
  assert (HE : forall y, (y < 200)%positive -> E' y = E y) by (intros y Hy; symmetry; exact (Ha y Hy)).
  apply (outside_shape E' (s_rgs U4a)); [exact Hs|].
  unfold outside. cbn [s_rgs U4a].
  repeat (apply Forall_cons; [rsz_simpl; cbn [RGz rg_base rg_size];
      rewrite ?u_lin0 by lia; rewrite ?u_lin1, ?u_lin2; rewrite ?HE by lia;
      change (E 1%positive) with sp0; change (E 3%positive) with (cat_argv_ptr sp0 av ev 0);
      change (E 7%positive) with (Z_to_bv 64 (Z.of_nat (length a0s)));
      rewrite ?u_small64 by (unfold two64; lia);
      pose proof (valid_argv_str_len av 0 Hva ltac:(pose proof (valid_argv_nonempty av Hva); lia));
      rewrite ?Z.mod_small by (unfold two64 in *; lia); lia |]).
  apply Forall_nil.
Qed.

#[using="Type"] Lemma shape_U4a : shape (s_rgs U4a) = shape (s_rgs U4a). Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma bases_U4a : bases_wf (s_next U4a) (s_rgs U4a) = true. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Hsp Hargc"] Lemma mf_seg : forall E' S ms ms', agree 200 E E' -> shape (s_rgs S) = shape (s_rgs U4a) ->
  (forall x, outside E' (s_rgs S) x -> ms_mem ms' x = ms_mem ms x) ->
  (forall x, outside E (s_rgs P_main1) x -> ms_mem ms x = mem x) ->
  (forall x, outside E (s_rgs P_main1) x -> ms_mem ms' x = mem x).
Proof. LiaFast.lf_pins (fun (Hsp Hargc : LiaFast.U) => LiaFast.u0). intros E' S ms ms' Ha Hs Hfr Hmf x Hx. rewrite Hfr; [exact (Hmf x Hx)|]. exact (outside_split_main1 E' _ x Ha Hs Hx). Qed.

#[using="uid hw Hsp Hva Hve Htid ME Hargc Hh Hl Hfd2"] Theorem usage_Ca : forall E1 ms1, agree 200 E E1 -> sden PSEGS E1 U4a ms1 -> ms_rom ms1 = seg_rom PSEGS ->
  (forall x, outside E (s_rgs P_main1) x -> ms_mem ms1 x = mem x) ->
  (exists rest, length rest = (73 - length a0s)%nat /\ u8arr PSEGS (ms_mem ms1) (bv_unsigned sp0 - 553) (a0s ++ rest)) ->
  (Z.of_nat (length a0s) <= 73)%Z ->
  realizes PSEGS (mkCfg ms1 model) (t_emit (W 2 (PRE ++ a0s ++ SUF)) (TEXIT model)).
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Htid ME Hargc Hh Hl Hfd2 : LiaFast.U) => LiaFast.u0).
  intros E1 ms1 Ha1 Hd1 Hrom1 Hmf1 (rest & Hlr & Hwin) HK73.
  pose proof SL as SL. pose proof SH as SH.
  pose proof (p0_bounds sp0 av ev uid hw rdraw Hsp Hva Hve) as (B1 & B2 & B3).
  set (K := length a0s) in *.
  pose proof (valid_argv_str_len av 0 Hva ltac:(pose proof (valid_argv_nonempty av Hva); lia)) as HKb. fold K in HKb.
  apply (rzc_fx_explore_frame PSEGS DCFG TBL_P IMG_P 4000 S2 U4a LCa E1 ms1 model _ TBL_P_ok IMG_P_ok certCa Hd1 bases_U4a Hh Hl).
  intros L E2 ms2 HIn Hd2 Ha2 Hrom2 Hfr2. rewrite LCa_two in HIn.
  assert (Ha2' : agree 200 E E2).
  { intros x Hx. rewrite (Ha1 x Hx). apply Ha2. assert (HN : (200 <= s_next U4a)%positive) by (unfold Pos.le; vm_compute; intros Hc; discriminate Hc). lia. }
  assert (HE2 : forall x, (x < 200)%positive -> E2 x = E x) by (intros x Hx; symmetry; exact (Ha2' x Hx)).
  assert (MF2 : forall x, outside E (s_rgs P_main1) x -> ms_mem ms2 x = mem x) by exact (mf_seg E1 U4a ms1 ms2 Ha1 eq_refl Hfr2 Hmf1).
  assert (WIN2 : u8arr PSEGS (ms_mem ms2) (bv_unsigned sp0 - 553) (a0s ++ rest)).
  { apply (u8arr_ext (ms_mem ms1)); [exact Hwin|]. intros x Hx. apply Hfr2. apply (window_outside E1 _ x Ha1 eq_refl).
    rewrite length_app, Hlr in Hx. fold K in Hx. lia. }
  rewrite Hrom1 in Hrom2.
  destruct HIn as [<-|[<-|[]]].
  - (* [comment removed for export] *)
    assert (HS2 : lden E2 SP0 = sp0) by (unfold SP0; rewrite lden_lvar, HE2 by lia; reflexivity).
    assert (HK66 : 66 < Z.of_nat K).
    { assert (Hf : In (FCond BC_GEU (LIN 73 [(7%positive, 18446744073709551615)]) (lconst 7) false) (s_facts L4a1)) by (vm_compute; tauto).
      pose proof (sden_fact PSEGS E2 L4a1 ms2 _ Hd2 Hf) as HF. cbn [fact_ok branch_taken] in HF.
      rewrite lden_lconst in HF.
      destruct (bv_ltu (lden E2 (LIN 73 [(7%positive, 18446744073709551615)])) (Z_to_bv 64 7)) eqn:HL; [|discriminate].
      assert (HE7 : bv_unsigned (E2 7%positive) = Z.of_nat K).
      { rewrite HE2 by lia. change (E 7%positive) with (Z_to_bv 64 (Z.of_nat K)). apply u_small64. unfold two64; lia. }
      unfold bv_ltu in HL. apply Z.ltb_lt in HL. rewrite u_lin_negx in HL by lia. rewrite HE7 in HL.
      rewrite u_small64 in HL by (unfold two64; lia). lia. }
    assert (R1 : getr (ms_regs ms2) 1 = Z_to_bv 64 0x56398) by (apply (getr_leaf_c PSEGS E2 L4a1); [exact Hd2 | vm_compute; reflexivity]).
    assert (R2 : getr (ms_regs ms2) 2 = Z_to_bv 64 (bv_unsigned sp0 - 1120)).
    { rewrite (getr_leaf PSEGS E2 L4a1 ms2 2 (laddc SP0 (-1120)) Hd2) by (vm_compute; reflexivity). apply lden_sp0; [exact HE2 | lia]. }
    assert (R10 : getr (ms_regs ms2) 10 = Z_to_bv 64 0x66bd8) by (apply (getr_leaf_c PSEGS E2 L4a1); [exact Hd2 | vm_compute; reflexivity]).
    assert (R11 : getr (ms_regs ms2) 11 = Z_to_bv 64 0x10f45) by (apply (getr_leaf_c PSEGS E2 L4a1); [exact Hd2 | vm_compute; reflexivity]).
    assert (R12 : getr (ms_regs ms2) 12 = Z_to_bv 64 7) by (apply (getr_leaf_c PSEGS E2 L4a1); [exact Hd2 | vm_compute; reflexivity]).
    (* [comment removed for export] *)
    assert (F40 : rdn PSEGS (ms_mem ms2) (Z_to_bv 64 (0x66bd8 + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 - 553 + Z.of_nat K)))).
    { rewrite (rdn_trk_c E2 L4a1 ms2 5 0x66bd8 40 8 (bvs_of (LIN 18446744073709551063 [(1%positive, 1); (7%positive, 1)]) 8) Hd2
                 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
      rewrite bvs_of_den_lin, u_lin2, !HE2 by lia. change (E 1%positive) with sp0. change (E 7%positive) with (Z_to_bv 64 (Z.of_nat K)).
      rewrite (u_small64 (Z.of_nat K)) by (unfold two64; lia). rewrite mod_sp by lia. unfold word_to_le_bytes.
      rewrite u_small64 by (unfold two64; lia). f_equal. f_equal. lia. }
    assert (F56 : rdn PSEGS (ms_mem ms2) (Z_to_bv 64 (0x66bd8 + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 - 560)))).
    { rewrite (rdn_trk_c E2 L4a1 ms2 5 0x66bd8 56 8 (bvs_of (laddc SP0 (-560)) 8) Hd2
                 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
      rewrite bvs_of_den_lin, (lden_sp0 E2 (-560) HE2) by lia. reflexivity. }
    assert (F88 : rdn PSEGS (ms_mem ms2) (Z_to_bv 64 (0x66bd8 + 88)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 - 560)))).
    { rewrite (rdn_trk_c E2 L4a1 ms2 5 0x66bd8 88 8 (bvs_of (laddc SP0 (-560)) 8) Hd2
                 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
      rewrite bvs_of_den_lin, (lden_sp0 E2 (-560) HE2) by lia. reflexivity. }
    assert (F96 : rdn PSEGS (ms_mem ms2) (Z_to_bv 64 (0x66bd8 + 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 80))).
    { rewrite (rdn_trk_c E2 L4a1 ms2 5 0x66bd8 96 8 [BK 80; BK 0; BK 0; BK 0; BK 0; BK 0; BK 0; BK 0] Hd2
                 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). reflexivity. }
    assert (F120 : rdn PSEGS (ms_mem ms2) (Z_to_bv 64 (0x66bd8 + 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 2))).
    { rewrite (rdn_img_c E2 L4a1 ms2 5 0x66bd8 120 4 Hd2 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vmz) ltac:(vm_compute; reflexivity)). bvlit. }
    assert (F48 : rdn PSEGS (ms_mem ms2) (Z_to_bv 64 (0x66bd8 + 48)) 8 = Some (repeat (Z_to_bv 8 0) 8)).
    { rewrite (rdn_img_c E2 L4a1 ms2 5 0x66bd8 48 8 Hd2 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vmz) ltac:(vm_compute; reflexivity)). bvlit. }
    assert (SWF : sw_file (ms_mem ms2) 0x66bd8 (bv_unsigned sp0 - 560) (bv_unsigned sp0 - 553 + Z.of_nat K) 2 (Z_to_bv 64 (bv_unsigned sp0 - 560)) (Z_to_bv 64 80)).
    { constructor; assumption. }
    assert (SSP : ssp_cells (ms_mem ms2) (lden E2 (lvar 5))).
    { split.
      - replace (Z_to_bv 64 0x65b58) with (Z_to_bv 64 (0x65a18 + 320)) by reflexivity.
        rewrite (rdn_img_c E2 L4a1 ms2 3 0x65a18 320 8 Hd2 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                   ltac:(left; vm_compute; reflexivity) ltac:(lia) ltac:(vmz) ltac:(vm_compute; reflexivity)). bvlit.
      - replace (Z_to_bv 64 0x97c00) with (Z_to_bv 64 (0x97c00 + 0)) by reflexivity.
        rewrite (rdn_trk_c E2 L4a1 ms2 8 0x97c00 0 8 (bvs_of (lvar 5) 8) Hd2
                   ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
        rewrite bvs_of_den_lin. reflexivity. }
    (* [comment removed for export] *)
    assert (BPRE : bytes_at PSEGS (ms_mem ms2) (bv_unsigned sp0 - 560) PRE).
    { apply bytes_at_of_rdn; [lia | unfold two64; cbn; lia|].
      replace (bv_unsigned sp0 - 560) with (bv_unsigned sp0 + -65536 + 64976) by lia.
      rewrite (rdn_trk_sp sp0 SL SH E2 L4a1 ms2 0 (-65536) 64976 (length PRE) [BK 117; BK 115; BK 97; BK 103; BK 101; BK 58; BK 32] Hd2
                 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) HS2 ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). bvlit. }
    assert (BA0 : bytes_at PSEGS (ms_mem ms2) (bv_unsigned sp0 - 553) a0s) by (apply u8arr_app in WIN2; exact (proj1 (proj1 WIN2))).
    assert (RDP : rdn PSEGS (ms_mem ms2) (Z_to_bv 64 (bv_unsigned sp0 - 560)) (length (PRE ++ a0s)) = Some (PRE ++ a0s)).
    { apply rdn_of_bytes_at. apply bytes_at_app. split; [exact BPRE|]. replace (bv_unsigned sp0 - 560 + Z.of_nat (length PRE)) with (bv_unsigned sp0 - 553) by (cbn; lia). exact BA0. }
    assert (RDE : rdn PSEGS (ms_mem ms2) (Z_to_bv 64 0x10f45) (length SUF) = Some SUF).
    { replace (Z_to_bv 64 0x10f45) with (Z_to_bv 64 (0x10f35 + 16)) by reflexivity.
      rewrite (rdn_img_c E2 L4a1 ms2 13 0x10f35 16 (length SUF) Hd2 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(left; vm_compute; reflexivity) ltac:(lia) ltac:(vmz) ltac:(vm_compute; reflexivity)). bvlit. }
    assert (FRM : frame_in E2 L4a1 0 64304 112 (bv_unsigned sp0 - 1120 - 112)).
    { apply (frame_sp sp0 SL SH E2 L4a1 0 (-65536)); [vm_compute; lia | vm_compute; reflexivity | exact HS2 | lia | vm_compute; reflexivity | lia | vmz | lia]. }
    assert (HWF : state_wf (sw_template L4a1 (bv_unsigned (Z_to_bv 64 0x56398)) 0 64304 5 (laddc SP0 (-560)) (lconst 80) (lconst 7)) = true).
    { rewrite u_small64 by (unfold two64; lia). rewrite U5a1_eq. exact wf5a1. }
    apply (rzc_conseq PSEGS DCFG _ (t_emit (map (WriteEv (Z_to_bv 64 2)) ((PRE ++ a0s) ++ SUF)) (t_emit (map (WriteEv (Z_to_bv 64 2)) ([] ++ []))
             (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model))))));
      [| rewrite <- app_assoc; unfold TEXIT; apply tail_2].
    apply (fx_stdio_write E2 L4a1 ms2 model _ (bv_unsigned sp0 - 1120) 0x66bd8 (bv_unsigned sp0 - 560) (bv_unsigned sp0 - 553 + Z.of_nat K) 2
             (Z_to_bv 64 0x10f45) (Z_to_bv 64 7) (Z_to_bv 64 (bv_unsigned sp0 - 560)) (Z_to_bv 64 80) (lden E2 (lvar 5)) (Z_to_bv 64 0x56398) (PRE ++ a0s) SUF
             0 64304 5 (rgn L4a1 5) (laddc SP0 (-560)) (lconst 80) (lconst 7)
             Hd2 eq_refl eq_refl Hrom2 hok4a1 HWF FRM (rgn_eq L4a1 5 ltac:(vm_compute; lia)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity) R2 R10 R11 R12 R1); try lia.
    + exact SWF.
    + exact SSP.
    + exact F48.
    + exact Hfd2.
    + exact Hh.
    + exact Hl.
    + unfold TASK_SIZE. lia.
    + rewrite length_app. replace (length PRE) with 7%nat by reflexivity. fold K. lia.
    + vm_compute. reflexivity.
    + rewrite length_app. replace (length PRE) with 7%nat by reflexivity. replace (length SUF) with 7%nat by reflexivity. fold K. lia.
    + rewrite length_app. replace (length PRE) with 7%nat by reflexivity. replace (length SUF) with 7%nat by reflexivity. fold K. lia.
    + left. rewrite !u_small64 by (unfold two64; lia). lia.
    + rewrite !u_small64 by (unfold two64; lia). unfold TASK_SIZE. lia.
    + exact RDP.
    + exact RDE.
    + vm_compute. reflexivity.
    + apply t_emit_has_nil.
    + apply (lden_sp0 E2 (-560) HE2). lia.
    + apply lden_lconst.
    + apply lden_lconst.
    + vm_compute. reflexivity.
    + vm_compute. reflexivity.
    + intros E' ms' Ha' Hd' Hpost Hrom'.
      rewrite u_small64 in Hd' by (unfold two64; lia). rewrite U5a1_eq in Hd'.
      assert (Ha3 : agree 200 E E').
      { assert (HN : (200 <= s_next L4a1)%positive) by (unfold Pos.le; vm_compute; intros Hc; discriminate Hc).
        intros x Hx. rewrite (Ha2' x Hx). apply Ha'. lia. }
      assert (MF3 : forall x, outside E (s_rgs P_main1) x -> ms_mem ms' x = mem x).
      { intros x Hx.
        pose proof (outside_nth_c E _ x 0 (laddc SP0 (-65536)) 65536 RW TEmpty Hx eq_refl ltac:(unfold two64; lia)) as X0r. cbn [RGz rg_base] in X0r.
        pose proof (outside_nth_c E _ x 5 (lconst 0x66bd8) 232 RI TEmpty Hx eq_refl ltac:(unfold two64; lia)) as X5r. cbn [RGz rg_base] in X5r.
        rewrite (u_sp0 E (-65536) (fun _ _ => eq_refl)) in X0r by lia. rewrite u_lconst in X5r by lia.
        rewrite (swp_agree _ _ _ _ _ _ Hpost x); [exact (MF2 x Hx) | lia | lia | lia]. }
      rewrite Hrom2 in Hrom'.
      apply (rzc_fx_explore_frame PSEGS DCFG TBL_P IMG_P 4000 S1 U5a1 LDa1 E' ms' model _ TBL_P_ok IMG_P_ok certDa1 Hd'
               ltac:(vm_compute; reflexivity) Hh Hl).
      intros L E3 ms3 HIn Hd3 Ha4 Hrom3 Hfr3. rewrite LDa1_one in HIn. destruct HIn as [<-|[]].
      assert (Ha4' : agree 200 E E3).
      { intros x Hx. rewrite (Ha3 x Hx). apply Ha4. assert (HN : (200 <= s_next U5a1)%positive) by (unfold Pos.le; vm_compute; intros Hc; discriminate Hc). lia. }
      assert (HE3 : forall x, (x < 200)%positive -> E3 x = E x) by (intros x Hx; symmetry; exact (Ha4' x Hx)).
      assert (HS3 : lden E3 SP0 = sp0) by (unfold SP0; rewrite lden_lvar, HE3 by lia; reflexivity).
      assert (MF4 : forall x, outside E (s_rgs P_main1) x -> ms_mem ms3 x = mem x)
        by exact (mf_seg E' U5a1 ms' ms3 Ha3 ltac:(vm_compute; reflexivity) Hfr3 MF3).
      rewrite Hrom' in Hrom3.
      (* [comment removed for export] *)
      assert (Q1 : getr (ms_regs ms3) 1 = Z_to_bv 64 0x561c8) by (apply (getr_leaf_c PSEGS E3 L6a1); [exact Hd3 | vm_compute; reflexivity]).
      assert (Q2 : getr (ms_regs ms3) 2 = Z_to_bv 64 (bv_unsigned sp0 - 576)).
      { rewrite (getr_leaf PSEGS E3 L6a1 ms3 2 (laddc SP0 (-576)) Hd3) by (vm_compute; reflexivity). apply lden_sp0; [exact HE3 | lia]. }
      assert (Q10 : getr (ms_regs ms3) 10 = Z_to_bv 64 0x66bd8) by (apply (getr_leaf_c PSEGS E3 L6a1); [exact Hd3 | vm_compute; reflexivity]).
      assert (Q11 : getr (ms_regs ms3) 11 = Z_to_bv 64 0) by (apply (getr_leaf_c PSEGS E3 L6a1); [exact Hd3 | vm_compute; reflexivity]).
      assert (Q12 : getr (ms_regs ms3) 12 = Z_to_bv 64 0) by (apply (getr_leaf_c PSEGS E3 L6a1); [exact Hd3 | vm_compute; reflexivity]).
      assert (G40 : rdn PSEGS (ms_mem ms3) (Z_to_bv 64 (0x66bd8 + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 - 560)))).
      { rewrite (rdn_trk_c E3 L6a1 ms3 5 0x66bd8 40 8 (bvs_of (laddc SP0 (-560)) 8) Hd3
                   ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
        rewrite bvs_of_den_lin, (lden_sp0 E3 (-560) HE3) by lia. reflexivity. }
      assert (G56 : rdn PSEGS (ms_mem ms3) (Z_to_bv 64 (0x66bd8 + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 - 560)))).
      { rewrite (rdn_trk_c E3 L6a1 ms3 5 0x66bd8 56 8 (bvs_of (laddc SP0 (-560)) 8) Hd3
                   ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
        rewrite bvs_of_den_lin, (lden_sp0 E3 (-560) HE3) by lia. reflexivity. }
      assert (G88 : rdn PSEGS (ms_mem ms3) (Z_to_bv 64 (0x66bd8 + 88)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 - 560)))).
      { rewrite (rdn_trk_c E3 L6a1 ms3 5 0x66bd8 88 8 (bvs_of (laddc SP0 (-560)) 8) Hd3
                   ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
        rewrite bvs_of_den_lin, (lden_sp0 E3 (-560) HE3) by lia. reflexivity. }
      assert (G96 : rdn PSEGS (ms_mem ms3) (Z_to_bv 64 (0x66bd8 + 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 80))).
      { rewrite (rdn_trk_c E3 L6a1 ms3 5 0x66bd8 96 8 [BK 80; BK 0; BK 0; BK 0; BK 0; BK 0; BK 0; BK 0] Hd3
                   ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). reflexivity. }
      assert (G120 : rdn PSEGS (ms_mem ms3) (Z_to_bv 64 (0x66bd8 + 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 2))).
      { rewrite (rdn_img_c E3 L6a1 ms3 5 0x66bd8 120 4 Hd3 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                   ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vmz) ltac:(vm_compute; reflexivity)). bvlit. }
      assert (G48 : rdn PSEGS (ms_mem ms3) (Z_to_bv 64 (0x66bd8 + 48)) 8 = Some (repeat (Z_to_bv 8 0) 8)).
      { rewrite (rdn_trk_c E3 L6a1 ms3 5 0x66bd8 48 8 [BK 0; BK 0; BK 0; BK 0; BK 0; BK 0; BK 0; BK 0] Hd3
                   ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). reflexivity. }
      assert (SWF3 : sw_file (ms_mem ms3) 0x66bd8 (bv_unsigned sp0 - 560) (bv_unsigned sp0 - 560) 2 (Z_to_bv 64 (bv_unsigned sp0 - 560)) (Z_to_bv 64 80)).
      { constructor; assumption. }
      assert (SSP3 : ssp_cells (ms_mem ms3) (lden E3 (lvar 5))).
      { split.
        - replace (Z_to_bv 64 0x65b58) with (Z_to_bv 64 (0x65a18 + 320)) by reflexivity.
          rewrite (rdn_img_c E3 L6a1 ms3 3 0x65a18 320 8 Hd3 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                     ltac:(left; vm_compute; reflexivity) ltac:(lia) ltac:(vmz) ltac:(vm_compute; reflexivity)). bvlit.
        - replace (Z_to_bv 64 0x97c00) with (Z_to_bv 64 (0x97c00 + 0)) by reflexivity.
          rewrite (rdn_trk_c E3 L6a1 ms3 8 0x97c00 0 8 (bvs_of (lvar 5) 8) Hd3
                     ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
          rewrite bvs_of_den_lin. reflexivity. }
      assert (FRM3 : frame_in E3 L6a1 0 64848 112 (bv_unsigned sp0 - 576 - 112)).
      { apply (frame_sp sp0 SL SH E3 L6a1 0 (-65536)); [vm_compute; lia | vm_compute; reflexivity | exact HS3 | lia | vm_compute; reflexivity | lia | vmz | lia]. }
      assert (HWF3 : state_wf (sw_template L6a1 (bv_unsigned (Z_to_bv 64 0x561c8)) 0 64848 5 (laddc SP0 (-560)) (lconst 80) (lconst 0)) = true).
      { rewrite u_small64 by (unfold two64; lia). rewrite U6a1_eq. exact wf6a1. }
      apply (fx_stdio_write E3 L6a1 ms3 model _ (bv_unsigned sp0 - 576) 0x66bd8 (bv_unsigned sp0 - 560) (bv_unsigned sp0 - 560) 2
               (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (bv_unsigned sp0 - 560)) (Z_to_bv 64 80) (lden E3 (lvar 5)) (Z_to_bv 64 0x561c8) [] []
               0 64848 5 (rgn L6a1 5) (laddc SP0 (-560)) (lconst 80) (lconst 0)
               Hd3 eq_refl eq_refl Hrom3 hok6a1 HWF3 FRM3 (rgn_eq L6a1 5 ltac:(vm_compute; lia)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) Q2 Q10 Q11 Q12 Q1); try lia.
      * exact SWF3.
      * exact SSP3.
      * exact G48.
      * exact Hfd2.
      * exact Hh.
      * exact Hl.
      * unfold TASK_SIZE. lia.
      * cbn [length]. lia.
      * vm_compute. reflexivity.
      * cbn [length]. lia.
      * cbn [length]. lia.
      * left. rewrite !u_small64 by (unfold two64; lia). lia.
      * rewrite !u_small64 by (unfold two64; lia). unfold TASK_SIZE. lia.
      * reflexivity.
      * reflexivity.
      * vm_compute. reflexivity.
      * apply t_emit_has_nil.
      * apply (lden_sp0 E3 (-560) HE3). lia.
      * apply lden_lconst.
      * apply lden_lconst.
      * vm_compute. reflexivity.
      * vm_compute. reflexivity.
      * intros E4 ms4 Ha5 Hd4 Hpost4 Hrom4.
        rewrite u_small64 in Hd4 by (unfold two64; lia). rewrite U6a1_eq in Hd4.
        assert (Ha5' : agree 200 E E4).
        { assert (HN : (200 <= s_next L6a1)%positive) by (unfold Pos.le; vm_compute; intros Hc; discriminate Hc).
          intros x Hx. rewrite (Ha4' x Hx). apply Ha5. lia. }
        assert (MF5 : forall x, outside E (s_rgs P_main1) x -> ms_mem ms4 x = mem x).
        { intros x Hx.
          pose proof (outside_nth_c E _ x 0 (laddc SP0 (-65536)) 65536 RW TEmpty Hx eq_refl ltac:(unfold two64; lia)) as X0r. cbn [RGz rg_base] in X0r.
          pose proof (outside_nth_c E _ x 5 (lconst 0x66bd8) 232 RI TEmpty Hx eq_refl ltac:(unfold two64; lia)) as X5r. cbn [RGz rg_base] in X5r.
          rewrite (u_sp0 E (-65536) (fun _ _ => eq_refl)) in X0r by lia. rewrite u_lconst in X5r by lia.
          rewrite (swp_agree _ _ _ _ _ _ Hpost4 x); [exact (MF4 x Hx) | lia | lia | lia]. }
        rewrite Hrom3 in Hrom4.
        apply (rzc_fx_explore_frame PSEGS DCFG TBL_P IMG_P 4000 S1 U6a1 LEa1 E4 ms4 model _ TBL_P_ok IMG_P_ok certEa1 Hd4
                 ltac:(vm_compute; reflexivity) Hh Hl).
        intros L E5 ms5 HIn Hd5 Ha6 Hrom5 Hfr5. rewrite LEa1_one in HIn. destruct HIn as [<-|[]].
        assert (Ha6' : agree 200 E E5).
        { intros x Hx. rewrite (Ha5' x Hx). apply Ha6. assert (HN : (200 <= s_next U6a1)%positive) by (unfold Pos.le; vm_compute; intros Hc; discriminate Hc). lia. }
        assert (HE5 : forall x, (x < 200)%positive -> E5 x = E x) by (intros x Hx; symmetry; exact (Ha6' x Hx)).
        assert (MF6 : forall x, outside E (s_rgs P_main1) x -> ms_mem ms5 x = mem x)
          by exact (mf_seg E4 U6a1 ms4 ms5 Ha5' ltac:(vm_compute; reflexivity) Hfr5 MF5).
        rewrite Hrom4 in Hrom5.
        apply (fx_exit E5 L7a1 ms5 model (Z_to_bv 64 2) [] Hd5 eq_refl eq_refl Hrom5).
        apply (exit_pre_gen sp0 tid SL SH Htid E5 L7a1 ms5 model (-48) 22 3 5 6 7 21 288 (rg_cont (rgn L7a1 5)) (rg_cont (rgn L7a1 7)) RI Hd5).
        -- unfold SP0. rewrite lden_lvar, HE5 by lia. reflexivity.
        -- unfold T. rewrite lden_lvar, HE5 by lia. reflexivity.
        -- lia.
        -- exact (exit_glob_of_MF sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve Htid ME Hargc (ms_mem ms5) MF6).
        -- exact Hh.
        -- exact Hl.
        -- vm_compute. reflexivity.
        -- vm_compute. reflexivity.
        -- vm_compute. reflexivity.
        -- vm_compute. reflexivity.
        -- vm_compute. reflexivity.
        -- unfold c5_clean. repeat split; vm_compute; reflexivity.
        -- vm_compute. reflexivity.
        -- vm_compute. reflexivity.
        -- vm_compute. reflexivity.
        -- vm_compute. reflexivity.
        -- apply (frame_sp sp0 SL SH E5 L7a1 22 (-480)); [vm_compute; lia | vm_compute; reflexivity | | lia | vm_compute; reflexivity | lia | vmz | lia].
           unfold SP0. rewrite lden_lvar, HE5 by lia. reflexivity.
  - (* [comment removed for export] *)
    assert (HS2 : lden E2 SP0 = sp0) by (unfold SP0; rewrite lden_lvar, HE2 by lia; reflexivity).
    assert (HE7 : bv_unsigned (E2 7%positive) = Z.of_nat K).
    { rewrite HE2 by lia. change (E 7%positive) with (Z_to_bv 64 (Z.of_nat K)). apply u_small64. unfold two64; lia. }
    assert (HK66 : Z.of_nat K <= 66).
    { assert (Hf : In (FCond BC_GEU (LIN 73 [(7%positive, 18446744073709551615)]) (lconst 7) true) (s_facts L4a2)) by (vm_compute; tauto).
      pose proof (sden_fact PSEGS E2 L4a2 ms2 _ Hd2 Hf) as HF. cbn [fact_ok branch_taken] in HF.
      rewrite lden_lconst in HF.
      destruct (bv_ltu (lden E2 (LIN 73 [(7%positive, 18446744073709551615)])) (Z_to_bv 64 7)) eqn:HL; [discriminate|].
      unfold bv_ltu in HL. apply Z.ltb_ge in HL. rewrite u_lin_negx in HL by lia. rewrite HE7 in HL.
      rewrite u_small64 in HL by (unfold two64; lia). lia. }
    assert (HDST : lden E2 RES2 = Z_to_bv 64 (bv_unsigned sp0 - 553 + Z.of_nat K)).
    { apply bv_eq. rewrite u_small64 by (unfold two64; lia).
      replace RES2 with (LIN 18446744073709551063 [(1%positive, 1); (7%positive, 1)]) by (vm_compute; reflexivity).
      rewrite u_lin2, HE7. rewrite HE2 by lia. change (E 1%positive) with sp0. rewrite mod_sp by lia. lia. }
    assert (R1 : getr (ms_regs ms2) 1 = Z_to_bv 64 0x55c50) by (apply (getr_leaf_c PSEGS E2 L4a2); [exact Hd2 | vm_compute; reflexivity]).
    assert (R10 : getr (ms_regs ms2) 10 = Z_to_bv 64 (bv_unsigned sp0 - 553 + Z.of_nat K)).
    { rewrite (getr_leaf PSEGS E2 L4a2 ms2 10 RES2 Hd2) by (vm_compute; reflexivity). exact HDST. }
    assert (R11 : getr (ms_regs ms2) 11 = Z_to_bv 64 0x10f45) by (apply (getr_leaf_c PSEGS E2 L4a2); [exact Hd2 | vm_compute; reflexivity]).
    assert (R12 : getr (ms_regs ms2) 12 = Z_to_bv 64 7) by (apply (getr_leaf_c PSEGS E2 L4a2); [exact Hd2 | vm_compute; reflexivity]).
    assert (RDE : rdn PSEGS (ms_mem ms2) (Z_to_bv 64 0x10f45) (length SUF) = Some SUF).
    { replace (Z_to_bv 64 0x10f45) with (Z_to_bv 64 (0x10f35 + 16)) by reflexivity.
      rewrite (rdn_img_c E2 L4a2 ms2 13 0x10f35 16 (length SUF) Hd2 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(left; vm_compute; reflexivity) ltac:(lia) ltac:(vmz) ltac:(vm_compute; reflexivity)). bvlit. }
    assert (BSUF : bytes_at PSEGS (ms_mem ms2) (bv_unsigned (Z_to_bv 64 0x10f45)) SUF).
    { rewrite u_small64 by (unfold two64; lia). apply bytes_at_of_rdn; [lia | unfold two64; cbn; lia | exact RDE]. }
    apply u8arr_app in WIN2 as [WA0 WREST].
    rewrite <- (firstn_skipn 7 rest) in WREST. apply u8arr_app in WREST as [WOLD WTAIL].
    assert (Hl7 : length (firstn 7 rest) = 7%nat) by (rewrite length_firstn; lia).
    apply (fx_memcpy E2 L4a2 ms2 model _ (Z_to_bv 64 (bv_unsigned sp0 - 553 + Z.of_nat K)) (Z_to_bv 64 0x10f45) 7 SUF (firstn 7 rest) [] RES2
             Hd2 eq_refl eq_refl hok4a2 Hrom2 R10 R11 R12 ltac:(rewrite R1; vm_compute; reflexivity) BSUF).
    + rewrite u_small64 by (unfold two64; lia). fold K in WOLD. exact WOLD.
    + rewrite Hl7. reflexivity.
    + reflexivity.
    + rewrite !u_small64 by (unfold two64; lia). right. lia.
    + rewrite u_small64 by (unfold two64; lia). lia.
    + rewrite u_small64 by (unfold two64; lia). lia.
    + exact HDST.
    + intros i R x Hi Hin Hx. exfalso. rewrite u_small64 in Hx by (unfold two64; lia).
      apply (outside_not_in_rg E2 (s_rgs L4a2) x i R); [|exact Hi|exact Hin].
      apply (window_outside E2 (s_rgs L4a2) x Ha2' ltac:(vm_compute; reflexivity)). lia.
    + exact Hh.
    + exact Hl.
    + intros E' ms' Ha' Hd' Hout Hgrow Hbs' Hrom'.
      rewrite R1 in Hd'. replace (bv_unsigned (Z_to_bv 64 0x55c50)) with 0x55c50 in Hd' by (vm_compute; reflexivity). rewrite U5a2_eq in Hd'.
      assert (Ha3 : agree 200 E E').
      { assert (HN : (200 <= s_next L4a2)%positive) by (unfold Pos.le; vm_compute; intros Hc; discriminate Hc).
        intros x Hx. rewrite (Ha2' x Hx). apply Ha'. lia. }
      assert (MF3 : forall x, outside E (s_rgs P_main1) x -> ms_mem ms' x = mem x).
      { intros x Hx. rewrite Hout; [exact (MF2 x Hx)|]. rewrite u_small64 by (unfold two64; lia).
        pose proof (outside_nth_c E _ x 0 (laddc SP0 (-65536)) 65536 RW TEmpty Hx eq_refl ltac:(unfold two64; lia)) as X0r. cbn [RGz rg_base] in X0r.
        rewrite (u_sp0 E (-65536) (fun _ _ => eq_refl)) in X0r by lia. lia. }
      assert (BA0 : bytes_at PSEGS (ms_mem ms') (bv_unsigned sp0 - 553) a0s).
      { apply (bytes_at_ext_m (ms_mem ms2)); [exact (proj1 WA0)|]. intros x Hx. apply Hout. rewrite u_small64 by (unfold two64; lia).
        fold K in Hx. lia. }
      assert (BSF : bytes_at PSEGS (ms_mem ms') (bv_unsigned sp0 - 553 + Z.of_nat K) SUF).
      { rewrite u_small64 in Hbs' by (unfold two64; lia). exact Hbs'. }
      rewrite Hrom2 in Hrom'.
      apply (rzc_fx_explore_frame PSEGS DCFG TBL_P IMG_P 4000 S1 U5a2 LDa2 E' ms' model _ TBL_P_ok IMG_P_ok certDa2 Hd'
               ltac:(vm_compute; reflexivity) Hh Hl).
      intros L E3 ms3 HIn Hd3 Ha4 Hrom3 Hfr3. rewrite LDa2_one in HIn. destruct HIn as [<-|[]].
      assert (Ha4' : agree 200 E E3).
      { intros x Hx. rewrite (Ha3 x Hx). apply Ha4. assert (HN : (200 <= s_next U5a2)%positive) by (unfold Pos.le; vm_compute; intros Hc; discriminate Hc). lia. }
      assert (HE3 : forall x, (x < 200)%positive -> E3 x = E x) by (intros x Hx; symmetry; exact (Ha4' x Hx)).
      assert (HS3 : lden E3 SP0 = sp0) by (unfold SP0; rewrite lden_lvar, HE3 by lia; reflexivity).
      assert (HE73 : bv_unsigned (E3 7%positive) = Z.of_nat K).
      { rewrite HE3 by lia. change (E 7%positive) with (Z_to_bv 64 (Z.of_nat K)). apply u_small64. unfold two64; lia. }
      assert (MF4 : forall x, outside E (s_rgs P_main1) x -> ms_mem ms3 x = mem x)
        by exact (mf_seg E' U5a2 ms' ms3 Ha3 ltac:(vm_compute; reflexivity) Hfr3 MF3).
      assert (BMSG : bytes_at PSEGS (ms_mem ms3) (bv_unsigned sp0 - 553) (a0s ++ SUF)).
      { apply (bytes_at_ext_m (ms_mem ms')); [apply bytes_at_app; split; [exact BA0 | fold K; exact BSF]|].
        intros x Hx. apply Hfr3. apply (window_outside E' (s_rgs U5a2) x Ha3 ltac:(vm_compute; reflexivity)).
        rewrite length_app in Hx. replace (length SUF) with 7%nat in Hx by reflexivity. fold K in Hx. lia. }
      rewrite Hrom' in Hrom3.
      (* [comment removed for export] *)
      assert (Q1 : getr (ms_regs ms3) 1 = Z_to_bv 64 0x561c8) by (apply (getr_leaf_c PSEGS E3 L6a2); [exact Hd3 | vm_compute; reflexivity]).
      assert (Q2 : getr (ms_regs ms3) 2 = Z_to_bv 64 (bv_unsigned sp0 - 576)).
      { rewrite (getr_leaf PSEGS E3 L6a2 ms3 2 (laddc SP0 (-576)) Hd3) by (vm_compute; reflexivity). apply lden_sp0; [exact HE3 | lia]. }
      assert (Q10 : getr (ms_regs ms3) 10 = Z_to_bv 64 0x66bd8) by (apply (getr_leaf_c PSEGS E3 L6a2); [exact Hd3 | vm_compute; reflexivity]).
      assert (Q11 : getr (ms_regs ms3) 11 = Z_to_bv 64 0) by (apply (getr_leaf_c PSEGS E3 L6a2); [exact Hd3 | vm_compute; reflexivity]).
      assert (Q12 : getr (ms_regs ms3) 12 = Z_to_bv 64 0) by (apply (getr_leaf_c PSEGS E3 L6a2); [exact Hd3 | vm_compute; reflexivity]).
      assert (G40 : rdn PSEGS (ms_mem ms3) (Z_to_bv 64 (0x66bd8 + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 - 546 + Z.of_nat K)))).
      { rewrite (rdn_trk_c E3 L6a2 ms3 5 0x66bd8 40 8 (bvs_of (LIN 18446744073709551070 [(1%positive, 1); (7%positive, 1)]) 8) Hd3
                   ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
        rewrite bvs_of_den_lin, u_lin2, HE73. rewrite HE3 by lia. change (E 1%positive) with sp0.
        rewrite mod_sp by lia. unfold word_to_le_bytes. rewrite u_small64 by (unfold two64; lia). f_equal. f_equal. lia. }
      assert (G56 : rdn PSEGS (ms_mem ms3) (Z_to_bv 64 (0x66bd8 + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 - 560)))).
      { rewrite (rdn_trk_c E3 L6a2 ms3 5 0x66bd8 56 8 (bvs_of (laddc SP0 (-560)) 8) Hd3
                   ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
        rewrite bvs_of_den_lin, (lden_sp0 E3 (-560) HE3) by lia. reflexivity. }
      assert (G88 : rdn PSEGS (ms_mem ms3) (Z_to_bv 64 (0x66bd8 + 88)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 - 560)))).
      { rewrite (rdn_trk_c E3 L6a2 ms3 5 0x66bd8 88 8 (bvs_of (laddc SP0 (-560)) 8) Hd3
                   ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
        rewrite bvs_of_den_lin, (lden_sp0 E3 (-560) HE3) by lia. reflexivity. }
      assert (G96 : rdn PSEGS (ms_mem ms3) (Z_to_bv 64 (0x66bd8 + 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 80))).
      { rewrite (rdn_trk_c E3 L6a2 ms3 5 0x66bd8 96 8 [BK 80; BK 0; BK 0; BK 0; BK 0; BK 0; BK 0; BK 0] Hd3
                   ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). reflexivity. }
      assert (G120 : rdn PSEGS (ms_mem ms3) (Z_to_bv 64 (0x66bd8 + 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 2))).
      { rewrite (rdn_img_c E3 L6a2 ms3 5 0x66bd8 120 4 Hd3 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                   ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vmz) ltac:(vm_compute; reflexivity)). bvlit. }
      assert (G48 : rdn PSEGS (ms_mem ms3) (Z_to_bv 64 (0x66bd8 + 48)) 8 = Some (repeat (Z_to_bv 8 0) 8)).
      { rewrite (rdn_img_c E3 L6a2 ms3 5 0x66bd8 48 8 Hd3 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                   ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vmz) ltac:(vm_compute; reflexivity)). bvlit. }
      assert (SWF3 : sw_file (ms_mem ms3) 0x66bd8 (bv_unsigned sp0 - 560) (bv_unsigned sp0 - 546 + Z.of_nat K) 2 (Z_to_bv 64 (bv_unsigned sp0 - 560)) (Z_to_bv 64 80)).
      { constructor; assumption. }
      assert (SSP3 : ssp_cells (ms_mem ms3) (lden E3 (lvar 5))).
      { split.
        - replace (Z_to_bv 64 0x65b58) with (Z_to_bv 64 (0x65a18 + 320)) by reflexivity.
          rewrite (rdn_img_c E3 L6a2 ms3 3 0x65a18 320 8 Hd3 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                     ltac:(left; vm_compute; reflexivity) ltac:(lia) ltac:(vmz) ltac:(vm_compute; reflexivity)). bvlit.
        - replace (Z_to_bv 64 0x97c00) with (Z_to_bv 64 (0x97c00 + 0)) by reflexivity.
          rewrite (rdn_trk_c E3 L6a2 ms3 8 0x97c00 0 8 (bvs_of (lvar 5) 8) Hd3
                     ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
          rewrite bvs_of_den_lin. reflexivity. }
      assert (BPRE : bytes_at PSEGS (ms_mem ms3) (bv_unsigned sp0 - 560) PRE).
      { apply bytes_at_of_rdn; [lia | unfold two64; cbn; lia|].
        replace (bv_unsigned sp0 - 560) with (bv_unsigned sp0 + -65536 + 64976) by lia.
        rewrite (rdn_trk_sp sp0 SL SH E3 L6a2 ms3 0 (-65536) 64976 (length PRE) [BK 117; BK 115; BK 97; BK 103; BK 101; BK 58; BK 32] Hd3
                   ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) HS3 ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). bvlit. }
      assert (RDP : rdn PSEGS (ms_mem ms3) (Z_to_bv 64 (bv_unsigned sp0 - 560)) (length (PRE ++ a0s ++ SUF)) = Some (PRE ++ a0s ++ SUF)).
      { apply rdn_of_bytes_at. apply bytes_at_app. split; [exact BPRE|].
        replace (bv_unsigned sp0 - 560 + Z.of_nat (length PRE)) with (bv_unsigned sp0 - 553) by (cbn; lia). exact BMSG. }
      assert (FRM3 : frame_in E3 L6a2 0 64848 112 (bv_unsigned sp0 - 576 - 112)).
      { apply (frame_sp sp0 SL SH E3 L6a2 0 (-65536)); [vm_compute; lia | vm_compute; reflexivity | exact HS3 | lia | vm_compute; reflexivity | lia | vmz | lia]. }
      assert (HWF3 : state_wf (sw_template L6a2 (bv_unsigned (Z_to_bv 64 0x561c8)) 0 64848 5 (laddc SP0 (-560)) (lconst 80) (lconst 0)) = true).
      { rewrite u_small64 by (unfold two64; lia). rewrite U6a2_eq. exact wf6a2. }
      assert (HLM : length (PRE ++ a0s ++ SUF) = (14 + K)%nat).
      { rewrite !length_app. replace (length PRE) with 7%nat by reflexivity. replace (length SUF) with 7%nat by reflexivity. fold K. lia. }
      apply (rzc_conseq PSEGS DCFG _ (t_emit (map (WriteEv (Z_to_bv 64 2)) ((PRE ++ a0s ++ SUF) ++ []))
               (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model)))));
        [| unfold TEXIT; apply tail_1].
      apply (fx_stdio_write E3 L6a2 ms3 model _ (bv_unsigned sp0 - 576) 0x66bd8 (bv_unsigned sp0 - 560) (bv_unsigned sp0 - 546 + Z.of_nat K) 2
               (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (bv_unsigned sp0 - 560)) (Z_to_bv 64 80) (lden E3 (lvar 5)) (Z_to_bv 64 0x561c8) (PRE ++ a0s ++ SUF) []
               0 64848 5 (rgn L6a2 5) (laddc SP0 (-560)) (lconst 80) (lconst 0)
               Hd3 eq_refl eq_refl Hrom3 hok6a2 HWF3 FRM3 (rgn_eq L6a2 5 ltac:(vm_compute; lia)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) Q2 Q10 Q11 Q12 Q1); try lia.
      * exact SWF3.
      * exact SSP3.
      * exact G48.
      * exact Hfd2.
      * exact Hh.
      * exact Hl.
      * unfold TASK_SIZE. lia.
      * vm_compute. reflexivity.
      * rewrite HLM. cbn [length]. lia.
      * rewrite HLM. cbn [length]. lia.
      * left. rewrite !u_small64 by (unfold two64; lia). lia.
      * rewrite !u_small64 by (unfold two64; lia). unfold TASK_SIZE. lia.
      * exact RDP.
      * reflexivity.
      * vm_compute. reflexivity.
      * apply t_emit_has_nil.
      * apply (lden_sp0 E3 (-560) HE3). lia.
      * apply lden_lconst.
      * apply lden_lconst.
      * vm_compute. reflexivity.
      * vm_compute. reflexivity.
      * intros E4 ms4 Ha5 Hd4 Hpost4 Hrom4.
        rewrite u_small64 in Hd4 by (unfold two64; lia). rewrite U6a2_eq in Hd4.
        assert (Ha5' : agree 200 E E4).
        { assert (HN : (200 <= s_next L6a2)%positive) by (unfold Pos.le; vm_compute; intros Hc; discriminate Hc).
          intros x Hx. rewrite (Ha4' x Hx). apply Ha5. lia. }
        assert (MF5 : forall x, outside E (s_rgs P_main1) x -> ms_mem ms4 x = mem x).
        { intros x Hx.
          pose proof (outside_nth_c E _ x 0 (laddc SP0 (-65536)) 65536 RW TEmpty Hx eq_refl ltac:(unfold two64; lia)) as X0r. cbn [RGz rg_base] in X0r.
          pose proof (outside_nth_c E _ x 5 (lconst 0x66bd8) 232 RI TEmpty Hx eq_refl ltac:(unfold two64; lia)) as X5r. cbn [RGz rg_base] in X5r.
          rewrite (u_sp0 E (-65536) (fun _ _ => eq_refl)) in X0r by lia. rewrite u_lconst in X5r by lia.
          rewrite (swp_agree _ _ _ _ _ _ Hpost4 x); [exact (MF4 x Hx) | lia | lia | lia]. }
        rewrite Hrom3 in Hrom4.
        apply (rzc_fx_explore_frame PSEGS DCFG TBL_P IMG_P 4000 S1 U6a2 LEa2 E4 ms4 model _ TBL_P_ok IMG_P_ok certEa2 Hd4
                 ltac:(vm_compute; reflexivity) Hh Hl).
        intros L E5 ms5 HIn Hd5 Ha6 Hrom5 Hfr5. rewrite LEa2_one in HIn. destruct HIn as [<-|[]].
        assert (Ha6' : agree 200 E E5).
        { intros x Hx. rewrite (Ha5' x Hx). apply Ha6. assert (HN : (200 <= s_next U6a2)%positive) by (unfold Pos.le; vm_compute; intros Hc; discriminate Hc). lia. }
        assert (HE5 : forall x, (x < 200)%positive -> E5 x = E x) by (intros x Hx; symmetry; exact (Ha6' x Hx)).
        assert (MF6 : forall x, outside E (s_rgs P_main1) x -> ms_mem ms5 x = mem x)
          by exact (mf_seg E4 U6a2 ms4 ms5 Ha5' ltac:(vm_compute; reflexivity) Hfr5 MF5).
        rewrite Hrom4 in Hrom5.
        apply (fx_exit E5 L7a2 ms5 model (Z_to_bv 64 2) [] Hd5 eq_refl eq_refl Hrom5).
        apply (exit_pre_gen sp0 tid SL SH Htid E5 L7a2 ms5 model (-48) 22 3 5 6 7 21 288 (rg_cont (rgn L7a2 5)) (rg_cont (rgn L7a2 7)) RI Hd5).
        -- unfold SP0. rewrite lden_lvar, HE5 by lia. reflexivity.
        -- unfold T. rewrite lden_lvar, HE5 by lia. reflexivity.
        -- lia.
        -- exact (exit_glob_of_MF sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve Htid ME Hargc (ms_mem ms5) MF6).
        -- exact Hh.
        -- exact Hl.
        -- vm_compute. reflexivity.
        -- vm_compute. reflexivity.
        -- vm_compute. reflexivity.
        -- vm_compute. reflexivity.
        -- vm_compute. reflexivity.
        -- unfold c5_clean. repeat split; vm_compute; reflexivity.
        -- vm_compute. reflexivity.
        -- vm_compute. reflexivity.
        -- vm_compute. reflexivity.
        -- vm_compute. reflexivity.
        -- apply (frame_sp sp0 SL SH E5 L7a2 22 (-480)); [vm_compute; lia | vm_compute; reflexivity | | lia | vm_compute; reflexivity | lia | vmz | lia].
           unfold SP0. rewrite lden_lvar, HE5 by lia. reflexivity.
Qed.
End UCa.
