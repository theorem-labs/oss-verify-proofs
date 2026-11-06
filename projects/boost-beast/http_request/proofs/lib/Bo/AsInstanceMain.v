(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.boost_beast.http_request.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Mem Cells Step Frame Arr CellsX TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import PropExec HeapCeil LazyRestrict LazySR.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface AsIface5 AsIface6 AsIface7 AsIface8 AsTRList AsStack0 AsDriverLaws AsPrintfFirst AF_atexit AXFuzz_stmt AsDrvDefs AsMainPre AsInstance FakeStackRep.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit BothImages BothPlanImages BoStartupHSF BoMainState BoMainFacts BoMainLazy BoMainCells BoMainIface BoMainIfaceConst BoMainIfacePre BoMainIfacePre2 BoMainIfaceArgs BoMainIfaceDepot BoMainIfaceFS BoMainIfaceAlloc.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AsMainSyms.
Import ListNotations. Import AX2. Import AP. Import APS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma main_ceil_range : forall sp0 : word, valid_sp sp0 -> 0x7fff7f800000 <= bv_unsigned sp0 - 8388608 <= 0x7fffff800000.
Proof. intros sp0 [V1 [V2 _]]. unfold sp_window_lo, sp_window_hi in V1, V2. lia. Qed.
Definition main_ceil (sp0 : word) (V : valid_sp sp0) : HeapCeil := mkHeapCeil (bv_unsigned sp0 - 8388608) (main_ceil_range sp0 V).
Lemma main_ceil_eq : forall sp0 V, @hceil (main_ceil sp0 V) = bv_unsigned sp0 - 8388608.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record mctx : Type := MCTX {
  k_sp0 : word; k_brk0 : word; k_rdraw : EntryDraw; k_inp : ProcInput;
  k_h : nat; k_ch : acs; k_E : env; k_R : bvmap 5 word; k_FULL : word -> option byte; k_model : Model;
  k_Vsp : valid_sp k_sp0;
  k_Vbrk : valid_brk BSEGS2 k_brk0;
  k_Vav : valid_argv (in_argv k_inp);
  k_Vev : valid_envp (in_envp k_inp);
  k_Vfit : entry_stack_fits k_sp0 (in_argv k_inp) (in_envp k_inp);
  k_Hh : HSF_both k_h = Some k_ch;
  k_HC : cs_ok BSEGS2 BOTH_H AsanInit.LIMIT
           (SINV0 BPH2 k_sp0 k_rdraw k_brk0 (in_argv k_inp) (in_envp k_inp) (in_uid k_inp) (in_hwcap k_inp))
           (argH0 BPH2 k_sp0 k_rdraw (in_argv k_inp) (in_envp k_inp) (in_uid k_inp) (in_hwcap k_inp)) (in_fs k_inp) k_E k_ch k_R k_FULL k_model }.

(* [comment removed for export] *)
Definition KX (k : mctx) : pm_syms := Xof (hole_granted (k_h k)) (k_E k).
Definition KVM (k : mctx) : word -> option byte := pm_vmem (bv_unsigned (k_sp0 k)) (bv_unsigned (k_brk0 k)) (KX k) (k_FULL k).
Definition Kcfg (k : mctx) : config := cfg_of BSEGS2 (k_R k) A_MAIN (k_FULL k) (k_model k).
Definition KCEIL (k : mctx) : HeapCeil := main_ceil (k_sp0 k) (k_Vsp k).
Definition KL0 (k : mctx) : list (word * word) := zz2ww (PM_LAZY (bv_unsigned (k_sp0 k)) (KX k)).
Definition KS (k : mctx) : list (word * word) := zz2ww (PM_S (bv_unsigned (k_sp0 k)) (bv_unsigned (k_brk0 k)) (KX k)).
Definition KZr0 (k : mctx) : list (word * word) := zz2ww (PM_ZR (bv_unsigned (k_sp0 k)) (KX k)).

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Kit.
  Variable KH : mctx -> asr.
  Variable KS0 : forall k : mctx, as_St (KH k).
  Variable KB : mctx -> Z.
  Hypothesis K_rt : forall k, @asan_rt_hyps (KCEIL k) (KH k).
  Hypothesis K_dl : forall k, asan_driver_laws (KH k).
  Hypothesis K_rtx : forall k, @asan_rt_hyps5 (KCEIL k) (KH k) /\ @asan_rt_hyps5x (KCEIL k) (KH k) /\ @asan_rt_hyps6 (KCEIL k) /\ @asan_rt_hyps7 (KCEIL k) (KH k)
                               /\ asan_rt_hyps8 (KH k) /\ incl TRLIST (as_TR (KH k)).   (* [comment removed for export] *)
  Hypothesis K_live : forall k, ADRV_LIVE <= as_LIVE_MAX (KH k) /\ ADRV_CNT <= as_LIVE_CNT_MAX (KH k).
  Hypothesis K_vis : forall k, as_VIS (KH k) (KS0 k) (cfg_ms (Kcfg k)) = mkst (k_R k) (Z_to_bv 64 A_MAIN) (KVM k) (seg_rom bsegs).
  Hypothesis K_krel : forall k, as_AKREL (KH k) (KS0 k) (Kcfg k).
  Hypothesis K_rfs : forall k, as_RFS (KH k) [] (KVM k).
  Hypothesis K_heap : forall k, as_RHEAP (KH k) (KS0 k) [] (KVM k).
  Hypothesis K_aux : forall k, as_rauxv_ok (KH k) (KVM k) (KB k) /\ bv_unsigned (k_sp0 k) <= KB k < 2 ^ 64.
  Hypothesis K_al : forall k, AMAIN_COST (KH k) <= as_AL (KH k) (KS0 k).
  Hypothesis K_tr : forall k, adrv_traces (KH k).

  Theorem instance_of_kit : as_instance_stmt P_main.
  Proof.
    intros sp0 brk0 mbase rdraw inp c P.
    destruct (P_main_open sp0 brk0 mbase rdraw inp c P) as (h & ch & E & R & FULL & model & Vsp & Vbrk & Vav & Vev & Vfit & Hh & HC & Hc & HF & PMx & SOK & LZ & PG & MC & VMEQ).
    set (k := MCTX sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC).
    destruct (BoMainIfacePre2.pre_can sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as [can Hcan].
    exists (KCEIL k), (KH k), (KS0 k), R, (KVM k), (KB k), (ps_tid (KX k)), can.
    split; [exact (K_rt k)|]. split; [exact (K_dl k)|]. split; [exact (K_rtx k)|]. split; [exact (K_live k)|].
    assert (Hcfg : c = Kcfg k) by exact Hc.
    split.
    2:{ rewrite Hcfg. cbn [Kcfg cfg_of cfg_model]. exact (BoMainIfacePre.pre_fs sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC). }
    pose proof (BoMainIfacePre.pre_regs sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as (R1 & R2 & R4 & R10 & R11).
    pose proof Vsp as [V1 [V2 _]]. unfold sp_window_lo, sp_window_hi in V1, V2.
    rewrite Hcfg. unfold Kcfg, cfg_of. cbn [cfg_ms cfg_model].
    split.
    - (* [comment removed for export] *) exact (K_vis k).
    - (* [comment removed for export] *) exact (K_krel k).
    - exact R1.
    - exact R2.
    - exact R4.
    - exact R10.
    - exact R11.
    - exact Vsp.
    - (* [comment removed for export] *) cbn [KCEIL main_ceil hceil k k_sp0]. lia.
    - (* [comment removed for export] *) apply (BoMainIfacePre.pre_stk sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC); unfold AMLO, ATR_STACK; cbn [KCEIL main_ceil hceil k k_sp0]; lia.
    - (* [comment removed for export] *) apply (BoMainIfacePre2.pre_sh0 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC (KCEIL k) eq_refl).
      pose proof (BoMainIface.pd_facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as (PD1 & PD2 & PD3).
      unfold AMLO, ATR_STACK. lia.
    - (* [comment removed for export] *) exact (BoMainIfaceArgs.pre_args sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC).
    - exact (BoMainIfacePre.pre_inv sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC).
    - exact (BoMainIfacePre2.pre_relro sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC).
    - exact (BoMainIfacePre2.pre_glb sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC).
    - exact (BoMainIfaceConst.aconst_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC).
    - exact (BoMainIfacePre2.pre_cells sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC).
    - (* [comment removed for export] *) exact (BoMainIfacePre2.pre_prist sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC).
    - (* [comment removed for export] *) exact (BoMainIfacePre2.pre_axtab sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC).
    - exact (BoMainIfacePre2.pre_out sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC).
    - exact (BoMainIfacePre2.pre_tid sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC).
    - exact (BoMainIfacePre.pre_errno sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC).
    - exact Hcan.
    - (* [comment removed for export] *) exact (K_rfs k).
    - (* [comment removed for export] *) exact (BoMainIfacePre2.pre_latch0 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC).
    - (* [comment removed for export] *) exact (K_heap k).
    - (* [comment removed for export] *) exact (K_aux k).
    - (* [comment removed for export] *) exact (K_al k).
    - (* [comment removed for export] *) exact (K_tr k).
    - (* [comment removed for export] *) exact (BoMainIfacePre.pre_fds sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC).
  Qed.
End Kit.
