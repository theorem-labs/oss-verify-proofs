(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
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
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import PDrvData PDrvMain PDrvCall RefMemchr RefStartup RefStartupDefs PUsageCert.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.


Section UA.
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
Hypothesis Hargc : length av <> 2%nat.
Variable model : Model.
Hypothesis Hh : m_halted model = None.
Hypothesis Hl : m_vm_lazy model = [].
Variable T : TSet.

Let E := E_main sp0 av ev tid (canary rdraw) regs.
Local Notation p0 := (cat_argv_ptr sp0 av ev 0).

(* [comment removed for export] *)
Hypothesis KB : forall E' ms', agree 200 E E' -> sden PSEGS E' U2 ms' -> ms_rom ms' = seg_rom PSEGS ->
  (forall x, outside E (s_rgs P_main1) x -> ms_mem ms' x = mem x) -> realizes PSEGS (mkCfg ms' model) T.

#[using="Type"] Lemma bases_main1 : bases_wf (s_next P_main1) (s_rgs P_main1) = true. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.




#[using="sp0 av ev uid tid hw rdraw Hsp Hva Hve Htid ME Hargc Hh Hl E KB"] Theorem usage_A : realizes PSEGS (mkCfg (mkst (fx := fx0) regs (Z_to_bv 64 0x22638) mem (seg_rom PSEGS)) model) T.
Proof. LiaFast.lf_pins (fun (sp0 av ev uid tid hw rdraw Hsp Hva Hve Htid ME Hargc Hh Hl E KB : LiaFast.U) => LiaFast.u0).
  pose proof (handoff1 sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve Htid ME Hargc) as Hd0.
  apply (rzc_fx_explore_frame PSEGS DCFG TBL_P IMG_P 4000 S1 P_main1 LA E _ model T TBL_P_ok IMG_P_ok certA Hd0 bases_main1 Hh Hl).
  intros L E1 ms1 HIn Hd1 Ha1 Hrom1 Hfr1. rewrite LA_one in HIn. destruct HIn as [<-|[]].
  cbn [ms_rom mkst] in Hrom1. cbn [ms_mem mkst] in Hfr1.
  pose proof (p0_bounds sp0 av ev uid hw rdraw Hsp Hva Hve) as (B1 & B2 & B3).
  pose proof (sp0_lo sp0 Hsp) as SL. pose proof (sp0_hi sp0 Hsp) as SH.
  destruct (argv0_window sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc) as (buf & Hbuf & Hpre & Hwin & Hbnd).
  assert (HE1 : forall x, (x < 200)%positive -> E1 x = E x) by (intros x Hx; symmetry; exact (Ha1 x Hx)).
  (* [comment removed for export] *)
  assert (R1 : getr (ms_regs ms1) 1 = Z_to_bv 64 0x54ab0) by (apply (getr_leaf_c PSEGS E1 L1); [exact Hd1 | vm_compute; reflexivity]).
  assert (R2 : getr (ms_regs ms1) 2 = Z_to_bv 64 (bv_unsigned sp0 - 1120)).
  { rewrite (getr_leaf PSEGS E1 L1 ms1 2 (laddc SP0 (-1120)) Hd1) by (vm_compute; reflexivity).
    rewrite lden_laddc. unfold SP0. rewrite lden_lvar, HE1 by lia. reflexivity. }
  assert (R10 : getr (ms_regs ms1) 10 = p0).
  { rewrite (getr_leaf PSEGS E1 L1 ms1 10 (lvar 3) Hd1) by (vm_compute; reflexivity). rewrite lden_lvar, HE1 by lia. reflexivity. }
  assert (R11 : getr (ms_regs ms1) 11 = Z_to_bv 64 0x7fffffff) by (apply (getr_leaf_c PSEGS E1 L1); [exact Hd1 | vm_compute; reflexivity]).
  set (K := length (nth 0 av [])).
  pose proof (valid_argv_str_len av 0 Hva ltac:(pose proof (valid_argv_nonempty av Hva); lia)) as HKb. fold K in HKb.
  pose proof (valid_argv_str_nz av 0 Hva ltac:(pose proof (valid_argv_nonempty av Hva); lia)) as HKnz.
  assert (HL : (S K <= length buf)%nat).
  { pose proof (f_equal (@length byte) Hpre) as Q. rewrite length_firstn, length_app in Q. cbn [length] in Q. unfold K0 in Q. fold K in Q. lia. }
  (* [comment removed for export] *)
  assert (Hbuf1 : rdn PSEGS (ms_mem ms1) p0 (length buf) = Some buf).
  { rewrite <- Hbuf. pose proof (rdn_ext_rd1 PSEGS (ms_mem ms1) mem (bv_unsigned p0) (length buf)) as RX.
    rewrite Z_to_bv_bv_unsigned in RX. apply RX; [lia | unfold two64; lia |]. clear RX.
    intros i Hi. destruct (Z.eq_dec i (Z.of_nat K)) as [->|Hne].
    - (* [comment removed for export] *)
      assert (NB : nth_error buf K = Some (Z_to_bv 8 0)).
      { rewrite <- (firstn_skipn (S K) buf). rewrite nth_error_app1 by (rewrite length_firstn; lia).
        unfold K0 in Hpre. fold K in Hpre. rewrite Hpre. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
      pose proof (rdn_rd1 PSEGS mem (bv_unsigned p0) (length buf) buf ltac:(lia) ltac:(unfold two64; lia)
                    ltac:(rewrite Z_to_bv_bv_unsigned; exact Hbuf) K _ NB) as N1.
      assert (HR2 : nth_error (s_rgs L1) 2 = Some (RGz (ladd P0 X0) 1 RW (put_bytes TEmpty 0 [BK 0]))) by (vm_compute; reflexivity).
      pose proof (sden_tracked PSEGS E1 L1 ms1 2 _ 0 (BK 0) Hd1 HR2 ltac:(lia) ltac:(vm_compute; reflexivity)) as N2.
      cbn [RGz rg_base bden] in N2. rewrite Z.add_0_r in N2.
      assert (HW : lwf 200 (ladd P0 X0) = true) by (vm_compute; reflexivity).
      assert (HAg : agree 200 E1 E) by (intros x Hx; exact (HE1 x Hx)).
      rewrite (lden_agree 200 E1 E _ HW HAg) in N2.
      pose proof (u_P0X0 sp0 av ev uid tid hw rdraw regs Hsp Hva Hve) as U. fold E in U. rewrite U in N2. fold K in N2.
      rewrite N1, N2. reflexivity.
    - unfold rd1. rewrite Hfr1; [reflexivity|]. apply (outside_main1_hi sp0 av ev uid tid hw rdraw regs Hsp Hva Hve Hargc).
      + rewrite u_small64 by (unfold two64; lia). lia.
      + rewrite u_small64 by (unfold two64; lia). fold K. lia. }
  assert (NBk : forall j, (j < K)%nat -> nth j buf (Z_to_bv 8 0) = nth j (nth 0 av []) (Z_to_bv 8 0)).
  { intros j Hj. rewrite <- (firstn_skipn (S K) buf). rewrite app_nth1 by (rewrite length_firstn; lia).
    unfold K0 in Hpre. fold K in Hpre. rewrite Hpre. rewrite app_nth1 by lia. reflexivity. }
  assert (MC : mchrH (ms_mem ms1) p0 buf (Z.of_nat K) 0x7fffffff).
  { constructor.
    - exact Hbuf1.
    - unfold K0 in Hwin. fold K in Hwin. lia.
    - lia.
    - lia.
    - rewrite Nat2Z.id. rewrite <- (firstn_skipn (S K) buf). rewrite app_nth1 by (rewrite length_firstn; lia).
      unfold K0 in Hpre. fold K in Hpre. rewrite Hpre. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
    - intros j Hj. rewrite Nat2Z.id in Hj. rewrite (NBk j Hj). intros Hc. apply HKnz.
      assert (Hb : nth j (nth 0 av []) (Z_to_bv 8 0) = Z_to_bv 8 0).
      { apply bv_eq. rewrite Hc. reflexivity. }
      rewrite <- Hb. apply nth_In. exact Hj.
    - lia.
    - lia.
    - intros i Hi. rewrite Hfr1; [exact (rodata_clear_main sp0 av ev uid tid hw rdraw regs mem Hsp ME Hargc i Hi)|].
      apply (outside_main1_rodata sp0 av ev uid tid hw rdraw regs Hsp Hva Hve Hargc). rewrite u_small64 by (unfold two64; lia). lia. }
  assert (HOK : havoc_ok L1 [(0%nat, 64384, 32)] (Some X0) = true) by (vm_compute; reflexivity).
  assert (FRM : frame_in E1 L1 0 64384 32 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp0 - 1120)) - 32)).
  { exists L1_R0. split; [exact L1_R0_eq|].
    rewrite u_small64 by (unfold two64; lia). rewrite L1_R0_base.
    replace (rg_kind L1_R0) with RW by (vm_compute; reflexivity). rszv.
    rewrite lden_laddc. unfold SP0. rewrite lden_lvar, HE1 by lia. change (E 1%positive) with sp0.
    rewrite u_small64 by (unfold two64; lia). split; [lia|]. split; [reflexivity|]. lia. }
  apply (fx_strnlen E1 L1 ms1 model T p0 (Z_to_bv 64 (bv_unsigned sp0 - 1120)) (Z_to_bv 64 0x54ab0) buf (Z.of_nat K) 0x7fffffff 0 64384 X0
           Hd1 eq_refl eq_refl HOK FRM R1 R2 R10 R11 MC); [lia | rewrite u_small64 by (unfold two64; lia); lia
           | right; rewrite u_small64 by (unfold two64; lia); lia | vm_compute; reflexivity
           | unfold X0; rewrite lden_lvar, HE1 by lia; reflexivity | exact Hh | exact Hl |].
  intros E' ms' Ha' Hd' Hfm Hrom'.
  apply (KB E' ms').
  - assert (HN : (200 <= s_next L1)%positive) by (unfold Pos.le; vm_compute; intros Hc; discriminate Hc).
    intros x Hx. rewrite (Ha1 x Hx). apply Ha'. lia.
  - replace (bv_unsigned (Z_to_bv 64 0x54ab0)) with 0x54ab0 in Hd' by (vm_compute; reflexivity). rewrite U2_eq in Hd'. exact Hd'.
  - rewrite Hrom'. exact Hrom1.
  - intros x Hx. destruct Hfm as [Hout _]. rewrite Hout; [exact (Hfr1 x Hx)|].
    split; [|exact I]. unfold in_rng. intros Hin.
    unfold outside in Hx. cbn [s_rgs P_main1 RG_main1 RG_hi1 app] in Hx. apply Forall_cons_iff in Hx as [Hx0 _].
    rsz_simpl_in Hx0; cbn [RGz rg_base rg_size] in Hx0. rewrite lden_laddc in Hx0. unfold SP0 in Hx0. rewrite lden_lvar in Hx0.
    change (E 1%positive) with sp0 in Hx0. rewrite u_small64 in Hx0 by (unfold two64; lia).
    rewrite (u_small64 (bv_unsigned sp0 - 1120)) in Hin by (unfold two64; lia).
    rewrite (u_small64 (bv_unsigned sp0 - 1120 - 32)) in Hin by (unfold two64; lia). lia.
Qed.
End UA.
