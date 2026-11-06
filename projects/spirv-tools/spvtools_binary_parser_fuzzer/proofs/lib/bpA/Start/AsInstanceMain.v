(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HMem HCells HStep HLFrame HArr CellsX TacX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPropExec HeapCeil LazyRestrict LazySR.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsStack0 AsDriverLaws RtA_Iface DvA_FuzzStmt AsDrvDefs AsMainPre AsInstance FakeStackRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit AsImages AsPlanImages AsStartupHSF AsMainState AsMainFacts AsMainLazy AsMainCells AsMainIface AsMainIfaceConst AsMainIfacePre AsMainIfaceArgs AsMainIfaceDepot AsMainIfaceFS AsMainIfaceAlloc.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AsMainSyms.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require AsMainIfaceDStat.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require LbA_RtOwn.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtA_Td.
Import ListNotations. Import AX2. Import AP. Import APS.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma main_ceil_range : forall sp0 : word, valid_sp sp0 -> 0x7fff7f800000 <= bv_unsigned sp0 - 8388608 <= 0x7fffff800000.
Proof. intros sp0 [V1 [V2 _]]. unfold sp_window_lo, sp_window_hi in V1, V2. lia. Qed.
Definition main_ceil (sp0 : word) (V : valid_sp sp0) : HeapCeil := mkHeapCeil (bv_unsigned sp0 - 8388608) (main_ceil_range sp0 V).

Record mctx : Type := MCTX {
  k_sp0 : word; k_brk0 : word; k_rdraw : EntryDraw; k_inp : ProcInput;
  k_h : nat; k_ch : acs; k_E : env; k_R : bvmap 5 word; k_FULL : word -> option byte; k_model : Model;
  k_Vsp : valid_sp k_sp0;
  k_Vbrk : valid_brk ASEGS k_brk0;
  k_Vav : valid_argv (in_argv k_inp);
  k_Vev : valid_envp (in_envp k_inp);
  k_Vfit : entry_stack_fits k_sp0 (in_argv k_inp) (in_envp k_inp);
  k_Hh : HSF_asan k_h = Some k_ch;
  k_HC : cs_ok ASEGS ASAN_H AsanInit.LIMIT
           (SINV0 APH k_sp0 k_rdraw k_brk0 (in_argv k_inp) (in_envp k_inp) (in_uid k_inp) (in_hwcap k_inp))
           (argH0 APH k_sp0 k_rdraw (in_argv k_inp) (in_envp k_inp) (in_uid k_inp) (in_hwcap k_inp)) (in_fs k_inp) k_E k_ch k_R k_FULL k_model }.

Definition KX (k : mctx) : pm_syms := Xof (hole_granted (k_h k)) (k_E k).
Definition KVM (k : mctx) : word -> option byte := pm_vmem (bv_unsigned (k_sp0 k)) (bv_unsigned (k_brk0 k)) (KX k) (k_FULL k).
Definition Kcfg (k : mctx) : config := cfg_of ASEGS (k_R k) A_MAIN (k_FULL k) (k_model k).
Definition KCEIL (k : mctx) : HeapCeil := main_ceil (k_sp0 k) (k_Vsp k).
Definition KL0 (k : mctx) : list (word * word) := zz2ww (PM_LAZY (bv_unsigned (k_sp0 k)) (KX k)).
Definition KS (k : mctx) : list (word * word) := zz2ww (PM_S (bv_unsigned (k_sp0 k)) (bv_unsigned (k_brk0 k)) (KX k)).
Definition KZr0 (k : mctx) : list (word * word) := zz2ww (PM_ZR (bv_unsigned (k_sp0 k)) (KX k)).

Section Kit.
  Variable P : fuzz_params.
  Variable KH : mctx -> asr.
  Variable KS0 : forall k : mctx, as_St (KH k).
  Variable KB : mctx -> Z.
  Hypothesis K_rt : forall k, @asan_rt_hyps_bp (KCEIL k) (KH k).
  Hypothesis K_dl : forall k, asan_driver_laws (KH k).
  Hypothesis K_own : forall k, @LbA_RtOwn.rt_own (KCEIL k) (KH k).
  Hypothesis K_td : forall k, @RtA_Td.td_law (KCEIL k) (KH k).
  Hypothesis K_live : forall k, ADRV_LIVE <= as_LIVE_MAX (KH k) /\ ADRV_CNT <= as_LIVE_CNT_MAX (KH k).
  Hypothesis K_vis : forall k, as_VIS (KH k) (KS0 k) (cfg_ms (Kcfg k)) = mkst (k_R k) (Z_to_bv 64 A_MAIN) (KVM k) (seg_rom asegs).
  Hypothesis K_krel : forall k, as_AKREL (KH k) (KS0 k) (Kcfg k).
  Hypothesis K_rfs : forall k, as_RFS (KH k) [] (KVM k).
  Hypothesis K_heap : forall k, as_RHEAP (KH k) (KS0 k) [] (KVM k).
  Hypothesis K_aux : forall k, as_rauxv_ok (KH k) (KVM k) (KB k) /\ bv_unsigned (k_sp0 k) <= KB k < 2 ^ 64.
  Hypothesis K_al : forall k, AMAIN_COST (KH k) P <= as_AL (KH k) (KS0 k).
  Hypothesis K_tr : forall k, adrv_traces (KH k) P.

  Theorem instance_of_kit : as_instance_stmt P_main P.
  Proof.
    intros sp0 brk0 mbase rdraw inp c PM.
    destruct (P_main_open sp0 brk0 mbase rdraw inp c PM) as (h & ch & E & R & FULL & model & Vsp & Vbrk & Vav & Vev & Vfit & Hh & HC & Hc & HF & PMx & SOK & LZ & PG & MC & VMEQ).
    set (k := MCTX sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC).
    destruct (AsMainIfacePre.pre_can sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as [can Hcan].
    exists (KCEIL k), (KH k), (KS0 k), R, (KVM k), (KB k), (ps_tid (KX k)), can.
    split; [exact (K_rt k)|]. split; [exact (K_dl k)|]. split; [exact (K_own k)|]. split; [exact (K_td k)|]. split; [exact (K_live k)|].
    assert (Hcfg : c = Kcfg k) by exact Hc.
    split.
    2:{ rewrite Hcfg. cbn [Kcfg cfg_of cfg_model]. exact (AsMainIfacePre.pre_fs sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC). }
    pose proof (AsMainIfacePre.pre_regs sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as (R1 & R2 & R4 & R10 & R11).
    pose proof Vsp as [V1 [V2 _]]. unfold sp_window_lo, sp_window_hi in V1, V2.
    rewrite Hcfg. unfold Kcfg, cfg_of. cbn [cfg_ms cfg_model].
    split.
    -   exact (K_vis k).
    -   exact (K_krel k).
    - exact R1.
    - exact R2.
    - exact R4.
    - exact R10.
    - exact R11.
    - exact Vsp.
    -   cbn [KCEIL main_ceil hceil k k_sp0]. lia.
    -   apply (AsMainIfacePre.pre_stk sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC); unfold AMLO, ATR_STACK; cbn [KCEIL main_ceil hceil k k_sp0]; lia.
    -   apply (AsMainIfacePre.pre_sh0 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC (KCEIL k) eq_refl).
      pose proof (AsMainIface.pd_facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as (PD1 & PD2 & PD3).
      unfold AMLO, ATR_STACK. lia.
    -   exact (AsMainIfaceArgs.pre_args sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC).
    - exact (AsMainIfacePre.pre_inv sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC).
    - exact (AsMainIfacePre.pre_relro sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC).
    - exact (AsMainIfacePre.pre_glb sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC).
    - exact (AsMainIfaceConst.aconst_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC).
    - exact (AsMainIfacePre.pre_cells sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC).
    - exact (AsMainIfacePre.pre_out sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC).
    - exact (AsMainIfacePre.pre_tid sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC).
    - exact (AsMainIfacePre.pre_errno sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC).
    - exact Hcan.
    -   exact (K_rfs k).
    - exact (AsMainIfacePre.pre_latch sp0 brk0 h E FULL).
    -   exact (K_heap k).
    -   exact (K_aux k).
    -   exact (K_al k).
    -   exact (K_tr k).
    -   exact (AsMainIfacePre.pre_fds sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC).
    -   exact (AsMainIfaceDStat.pre_dstat sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC).
  Qed.
End Kit.
