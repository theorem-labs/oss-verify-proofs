(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec CatExec CatSim SeqExec StepTac StoreOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Frame RefMemcpyLib DriverCfg.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.SeqExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.StoreOk OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.Hoare OSSVerify.Proofs.fast_float.from_chars.lib.Common.Frame OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefMemcpyLib OSSVerify.Proofs.fast_float.from_chars.lib.Common.DriverCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxSubst FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib Require UDrvData UDrvMain.
From OSSVerify.Proofs.fast_float.from_chars.lib Require UOpenCert.
From OSSVerify.Proofs.fast_float.from_chars.lib Require UDrvCall UDrvExit UbMemchr UbStartup UbStartupDefs UUsageCert UOpenCert UCantCert.
Import OSSVerify.Proofs.fast_float.from_chars.lib.UDrvData OSSVerify.Proofs.fast_float.from_chars.lib.UDrvMain OSSVerify.Proofs.fast_float.from_chars.lib.UOpenCert.UDrvMain2 OSSVerify.Proofs.fast_float.from_chars.lib.UDrvCall OSSVerify.Proofs.fast_float.from_chars.lib.UDrvExit OSSVerify.Proofs.fast_float.from_chars.lib.UbMemchr OSSVerify.Proofs.fast_float.from_chars.lib.UbStartup OSSVerify.Proofs.fast_float.from_chars.lib.UbStartupDefs OSSVerify.Proofs.fast_float.from_chars.lib.UUsageCert OSSVerify.Proofs.fast_float.from_chars.lib.UOpenCert OSSVerify.Proofs.fast_float.from_chars.lib.UCantCert.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section UAc.
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
Variable T : TSet.

Let E := E_main sp0 av ev tid (canary rdraw) regs.
Local Notation p1 := (cat_argv_ptr sp0 av ev 1).

(* [comment removed for export] *)
Hypothesis KB : forall E' ms', agree 200 E E' -> sden PSEGS E' U_c2 ms' -> ms_rom ms' = seg_rom PSEGS ->
  (forall x, outside E (s_rgs P_main2) x -> ms_mem ms' x = mem x) -> realizes PSEGS (mkCfg ms' model) T.

#[using="uid hw Hsp Hva Hve ME Hargc2 Hh Hl KB"] Theorem cant_A : forall E0 ms0, agree 200 E E0 -> sden PSEGS E0 U_oe ms0 -> ms_rom ms0 = seg_rom PSEGS ->
  (forall x, outside E (s_rgs P_main2) x -> ms_mem ms0 x = mem x) -> realizes PSEGS (mkCfg ms0 model) T.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve ME Hargc2 Hh Hl KB : LiaFast.U) => LiaFast.u0).
  intros E0 ms0 Ha0 Hd0 Hrom0 Hmf0.
  apply (rzc_fx_explore_frame PSEGS DCFG TBL_P IMG_P 4000 S1 U_oe LC1 E0 ms0 model T TBL_P_ok IMG_P_ok certC1 Hd0 ltac:(vm_compute; reflexivity) Hh Hl).
  intros L E1 ms1 HIn Hd1 Ha1' Hrom1 Hfr1'. rewrite LC1_one in HIn. destruct HIn as [<-|[]].
  assert (Ha1 : agree 200 E E1).
  { intros x Hx. rewrite (Ha0 x Hx). apply Ha1'. assert (HN : (200 <= s_next U_oe)%positive) by (unfold Pos.le; vm_compute; intros Hc; discriminate Hc). lia. }
  assert (Hfr1 : forall x, outside E (s_rgs P_main2) x -> ms_mem ms1 x = mem x).
  { intros x Hx. rewrite Hfr1'; [exact (Hmf0 x Hx)|].
    apply (outside_shape E0 (s_rgs P_main2)); [vm_compute; reflexivity|]. exact (proj1 (outside_agree 200 E E0 _ x bases_main2 Ha0) Hx). }
  rewrite Hrom0 in Hrom1.
  pose proof (p1_bounds sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2) as (B1 & B2 & B3).
  pose proof (sp0_lo sp0 Hsp) as SL. pose proof (sp0_hi sp0 Hsp) as SH.
  destruct (argv1_window sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2) as (buf & Hbuf & Hpre & Hwin & Hbnd).
  assert (HE1 : forall x, (x < 200)%positive -> E1 x = E x) by (intros x Hx; symmetry; exact (Ha1 x Hx)).
  (* [comment removed for export] *)
  assert (R1 : getr (ms_regs ms1) 1 = Z_to_bv 64 0x56868) by (apply (getr_leaf_c PSEGS E1 Lc1); [exact Hd1 | vm_compute; reflexivity]).
  assert (R2 : getr (ms_regs ms1) 2 = Z_to_bv 64 (bv_unsigned sp0 - 1120)).
  { rewrite (getr_leaf PSEGS E1 Lc1 ms1 2 (laddc SP0 (-1120)) Hd1) by (vm_compute; reflexivity).
    rewrite lden_laddc. unfold SP0. rewrite lden_lvar, HE1 by lia. reflexivity. }
  assert (R10 : getr (ms_regs ms1) 10 = p1).
  { rewrite (getr_leaf PSEGS E1 Lc1 ms1 10 (lvar 4) Hd1) by (vm_compute; reflexivity). rewrite lden_lvar, HE1 by lia. exact (E_P1 sp0 av ev tid rdraw regs Hargc2). }
  assert (R11 : getr (ms_regs ms1) 11 = Z_to_bv 64 0x7fffffff) by (apply (getr_leaf_c PSEGS E1 Lc1); [exact Hd1 | vm_compute; reflexivity]).
  set (K := length (nth 1 av [])).
  pose proof (valid_argv_str_len av 1 Hva ltac:(lia)) as HKb. fold K in HKb.
  pose proof (valid_argv_str_nz av 1 Hva ltac:(lia)) as HKnz.
  assert (HL : (S K <= length buf)%nat).
  { pose proof (f_equal (@length byte) Hpre) as Q. rewrite length_firstn, length_app in Q. cbn [length] in Q. unfold K1 in Q. fold K in Q. lia. }
  (* [comment removed for export] *)
  assert (Hbuf1 : rdn PSEGS (ms_mem ms1) p1 (length buf) = Some buf).
  { rewrite <- Hbuf. pose proof (rdn_ext_rd1 PSEGS (ms_mem ms1) mem (bv_unsigned p1) (length buf)) as RX.
    rewrite Z_to_bv_bv_unsigned in RX. apply RX; [lia | unfold two64; lia |]. clear RX.
    intros i Hi. destruct (Z.eq_dec i (Z.of_nat K)) as [->|Hne].
    - (* [comment removed for export] *)
      assert (NB : nth_error buf K = Some (Z_to_bv 8 0)).
      { rewrite <- (firstn_skipn (S K) buf). rewrite nth_error_app1 by (rewrite length_firstn; lia).
        unfold K1 in Hpre. fold K in Hpre. rewrite Hpre. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
      pose proof (rdn_rd1 PSEGS mem (bv_unsigned p1) (length buf) buf ltac:(lia) ltac:(unfold two64; lia)
                    ltac:(rewrite Z_to_bv_bv_unsigned; exact Hbuf) K _ NB) as N1.
      assert (HR2 : nth_error (s_rgs Lc1) 2 = Some (RGz (ladd P1 X1) 1 RW (put_bytes TEmpty 0 [BK 0]))) by (vm_compute; reflexivity).
      pose proof (sden_tracked PSEGS E1 Lc1 ms1 2 _ 0 (BK 0) Hd1 HR2 ltac:(lia) ltac:(vm_compute; reflexivity)) as N2.
      cbn [RGz rg_base bden] in N2. rewrite Z.add_0_r in N2.
      assert (HW : lwf 200 (ladd P1 X1) = true) by (vm_compute; reflexivity).
      assert (HAg : agree 200 E1 E) by (intros x Hx; exact (HE1 x Hx)).
      rewrite (lden_agree 200 E1 E _ HW HAg) in N2.
      pose proof (u_P1X1 sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2) as U. fold E in U. rewrite U in N2. fold K in N2.
      rewrite N1, N2. reflexivity.
    - unfold rd1. rewrite Hfr1; [reflexivity|]. apply (outside_main2_hi sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2).
      + rewrite u_small64 by (unfold two64; lia). lia.
      + rewrite u_small64 by (unfold two64; lia). fold K. lia. }
  assert (NBk : forall j, (j < K)%nat -> nth j buf (Z_to_bv 8 0) = nth j (nth 1 av []) (Z_to_bv 8 0)).
  { intros j Hj. rewrite <- (firstn_skipn (S K) buf). rewrite app_nth1 by (rewrite length_firstn; lia).
    unfold K1 in Hpre. fold K in Hpre. rewrite Hpre. rewrite app_nth1 by lia. reflexivity. }
  assert (MC : mchrH (ms_mem ms1) p1 buf (Z.of_nat K) 0x7fffffff).
  { constructor.
    - exact Hbuf1.
    - unfold K1 in Hwin. fold K in Hwin. lia.
    - lia.
    - lia.
    - rewrite Nat2Z.id. rewrite <- (firstn_skipn (S K) buf). rewrite app_nth1 by (rewrite length_firstn; lia).
      unfold K1 in Hpre. fold K in Hpre. rewrite Hpre. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
    - intros j Hj. rewrite Nat2Z.id in Hj. rewrite (NBk j Hj). intros Hc. apply HKnz.
      assert (Hb : nth j (nth 1 av []) (Z_to_bv 8 0) = Z_to_bv 8 0).
      { apply bv_eq. rewrite Hc. reflexivity. }
      rewrite <- Hb. apply nth_In. exact Hj.
    - lia.
    - lia.
    - intros i Hi. rewrite Hfr1; [exact (rodata_clear_main2 sp0 av ev uid tid hw rdraw regs mem Hsp ME Hargc2 i Hi)|].
      apply (outside_main2_rodata sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2). rewrite u_small64 by (unfold two64; lia). lia. }
  assert (HOK : havoc_ok Lc1 [(0%nat, 64384, 32)] (Some X1) = true) by (vm_compute; reflexivity).
  assert (FRM : frame_in E1 Lc1 0 64384 32 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp0 - 1120)) - 32)).
  { exists (rgn Lc1 0). split; [exact (rgn_eq Lc1 0 ltac:(vm_compute; lia))|].
    rewrite u_small64 by (unfold two64; lia). replace (rg_base (rgn Lc1 0)) with (laddc SP0 (-65536)) by (vm_compute; reflexivity).
    replace (rg_kind (rgn Lc1 0)) with RW by (vm_compute; reflexivity). rszv.
    rewrite lden_laddc. unfold SP0. rewrite lden_lvar, HE1 by lia. change (E 1%positive) with sp0.
    rewrite u_small64 by (unfold two64; lia). split; [lia|]. split; [reflexivity|]. lia. }
  apply (fx_strnlen E1 Lc1 ms1 model T p1 (Z_to_bv 64 (bv_unsigned sp0 - 1120)) (Z_to_bv 64 0x56868) buf (Z.of_nat K) 0x7fffffff 0 64384 X1
           Hd1 eq_refl eq_refl HOK FRM R1 R2 R10 R11 MC); [lia | rewrite u_small64 by (unfold two64; lia); lia
           | right; rewrite u_small64 by (unfold two64; lia); lia | vm_compute; reflexivity
           | unfold X1; rewrite lden_lvar, HE1 by lia; reflexivity | exact Hh | exact Hl |].
  intros E' ms' Ha' Hd' Hfm Hrom'.
  apply (KB E' ms').
  - assert (HN : (200 <= s_next Lc1)%positive) by (unfold Pos.le; vm_compute; intros Hc; discriminate Hc).
    intros x Hx. rewrite (Ha1 x Hx). apply Ha'. lia.
  - replace (bv_unsigned (Z_to_bv 64 0x56868)) with 0x56868 in Hd' by (vm_compute; reflexivity). rewrite U_c2_eq in Hd'. exact Hd'.
  - rewrite Hrom'. exact Hrom1.
  - intros x Hx. destruct Hfm as [Hout _]. rewrite Hout; [exact (Hfr1 x Hx)|].
    split; [|exact I]. unfold in_rng. intros Hin.
    unfold outside in Hx. cbn [s_rgs P_main2 RG_main2 RG_hi2 app] in Hx. apply Forall_cons_iff in Hx as [Hx0 _].
    rsz_simpl_in Hx0; cbn [RGz rg_base rg_size] in Hx0. rewrite lden_laddc in Hx0. unfold SP0 in Hx0. rewrite lden_lvar in Hx0.
    change (E 1%positive) with sp0 in Hx0. rewrite u_small64 in Hx0 by (unfold two64; lia).
    rewrite (u_small64 (bv_unsigned sp0 - 1120)) in Hin by (unfold two64; lia).
    rewrite (u_small64 (bv_unsigned sp0 - 1120 - 32)) in Hin by (unfold two64; lia). lia.
Qed.
End UAc.
