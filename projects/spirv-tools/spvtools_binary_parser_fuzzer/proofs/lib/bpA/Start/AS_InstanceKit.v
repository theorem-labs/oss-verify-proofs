(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HMem HCells HStep HLFrame HArr CellsX TacX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil AsanAllocModel LazyRestrict LazyLedger LazySR.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsDriverLaws RtA_Iface RtA_TR RtA_Inst DvA_FuzzStmt AsDrvDefs AsMainPre AsInstance AllocWf AllocBudget AllocRep AllocRepX AsDepotInv FakeStackRep AsSR AS_InstWF AS_InstMainDefs AS_InstDefs AS_InstLaws1 AS_InstMainRep AS_InstMainK AS_InstMainVis AS_InstMainHeap AsInstanceMain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPropExec AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit AsImages AsPlanImages AsStartupHSF AsMainState AsMainFacts AsMainLazy AsMainCells AsMainIface AsMainIfaceDepot AsMainIfaceAlloc AsMainIfaceFS.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AsMainSyms.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require LbA_RtOwn.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtA_Td AS_InstLawsTd.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section KIT.

  Variable P : fuzz_params.
  Variable LIB : list (list Z).
  Hypothesis LIBLEN : Nat.leb (length (TR_bp LIB)) 1000 = true.
  Hypothesis PCOST : 4 * fz_cost P (2 ^ 26) <= 2 ^ 38.
  Hypothesis PPF : Forall (fun pp : Z * list Z => In (fst pp :: snd pp ++ [0xe8b48]) LIB /\ ~ In (fst pp) (snd pp ++ [0xe8b48])) (fz_pf P).
  Hypothesis PTR : forall H : asr, as_TR H = TR_bp LIB -> fz_tr_ok P H.

  Hypothesis KOWN : forall (HC : HeapCeil) (p : iparams), @LbA_RtOwn.rt_own HC (@KHp HC p).

  Definition kip (k : mctx) : iparams :=
    {| ip_fsb := ps_b16 (KX k); ip_D := ps_b12 (KX k); ip_TR := TR_bp LIB; ip_TB := ps_b05 (KX k) |}.
  Definition KH (k : mctx) : asr := @KHp (KCEIL k) (kip k).
  Definition KB (k : mctx) : Z := bv_unsigned (k_sp0 k).

  Definition AL0 : Z := 2 ^ 39 - 2 ^ 37 - 2 ^ 29.

  Definition Ks0 (k : mctx) : ast := cert_s0 (bv_unsigned (k_sp0 k)) (bv_unsigned (k_brk0 k)) (KX k) [] false AL0.
  Definition Kd0 (k : mctx) : depot := depot0 (bv_unsigned (k_sp0 k)) (KX k).
  Definition KS0 (k : mctx) : as_St (KH k) := IST (Ks0 k) (Kd0 k).

  Lemma kit_rt : forall k, @asan_rt_hyps_bp (KCEIL k) (KH k).
  Proof.
    intros k. unfold KH. apply (@inst_rt_hyps_bp (KCEIL k) (kip k)).
    - cbn [ip_TR kip]. exact (TR_bp_len_le LIB LIBLEN).
    - cbn [ip_TR kip]. exact (TR_bp_op LIB).
  Qed.

  Lemma kit_vis : forall k, as_VIS (KH k) (KS0 k) (cfg_ms (Kcfg k)) = mkst (k_R k) (Z_to_bv 64 A_MAIN) (KVM k) (seg_rom asegs).
  Proof. intros k. exact (AS_InstMainK.vis_main_s0 (k_sp0 k) (k_brk0 k) (k_h k) (k_E k) (k_R k) (k_FULL k) [] false AL0). Qed.

  Lemma kit_rfs : forall k, as_RFS (KH k) [] (KVM k).
  Proof.
    intros k. exact (AS_InstMainK.rfs_main (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
                       (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Vfit k) (k_Hh k) (k_HC k) (KCEIL k) eq_refl).
  Qed.

  Lemma kit_heap : forall k, as_RHEAP (KH k) (KS0 k) [] (KVM k).
  Proof.
    intros k. exact (AS_InstMainHeap.rheap_main (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
                       (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Vfit k) (k_Hh k) (k_HC k) (KCEIL k) eq_refl [] false AL0 (kip k) eq_refl eq_refl eq_refl).
  Qed.

  Lemma kit_budget : forall k, ABUDGET (Ks0 k) (k_model k).
  Proof.
    intros k.
    pose proof (AsMainIfaceAlloc.ak_budget (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
                  (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Hh k) (k_HC k)) as (B1 & B2 & B3 & B4).
    unfold ABUDGET, aPhi, Ks0, KX. cbn [a_AL a_S a_st cert_s0]. unfold cert_st0. rewrite AllocBudget.pusage_init. rewrite B2. unfold KX in B3. rewrite B4 in B3.
    unfold target_alloc_limit, page_size, AllocBudget.B_PRIM, AL0. lia.
  Qed.

  Lemma kit_IK : forall k, @IK (KCEIL k) (kip k) (KS0 k) (k_model k).
  Proof.
    intros k. unfold IK. cbn [i_s i_d KS0].
    split; [|split; [|split]].
    -   split; [split; [|split]|].
      + exact (AS_InstMainK.amaps_main (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
                 (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Hh k) (k_HC k) (KCEIL k) eq_refl [] false AL0).
      + exact (AS_InstMainK.ashadow_main (k_sp0 k) (k_brk0 k) (k_h k) (k_E k) [] false AL0).
      + exact (kit_budget k).
      + exact (AS_InstMainK.akernel_main (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
                 (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Hh k) (k_HC k) (KCEIL k) eq_refl [] false AL0).
    -
      intros x Hx. cbn [Kd0 depot0 d_nb d_sb] in Hx.
      destruct Hx as [Hx|Hx].
      + apply (AsMainIfaceAlloc.ak_maps_in (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
                 (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Hh k) (k_HC k) (ps_b21 (KX k)) 0x100000); [cbn; tauto | lia].
      + apply (AsMainIfaceAlloc.ak_maps_in (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
                 (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Hh k) (k_HC k) (ps_b22 (KX k)) 0x800000); [cbn; tauto | lia].
    -
      intros x Hx. cbn [kip ip_D] in Hx. unfold kPageSize in Hx.
      apply (AsMainIfaceAlloc.ak_maps_in (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
               (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Hh k) (k_HC k) (ps_b12 (KX k)) 0x1000); [cbn; tauto | lia].
    -
      intros x Hx. cbn [kip ip_TB] in Hx. unfold AHM_SIZE in Hx.
      apply (AsMainIfaceAlloc.ak_maps_in (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
               (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Hh k) (k_HC k) (ps_b05 (KX k)) 0x38e000); [cbn; tauto | lia].
  Qed.

  Lemma kit_krel : forall k, as_AKREL (KH k) (KS0 k) (Kcfg k).
  Proof.
    intros k. split.
    -   exact (proj1 (AsMainLazy.lzok_open (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
                          (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Hh k) (k_HC k))).
    - exact (kit_IK k).
  Qed.

  Lemma kit_aux : forall k, as_rauxv_ok (KH k) (KVM k) (KB k) /\ bv_unsigned (k_sp0 k) <= KB k < 2 ^ 64.
  Proof.
    intros k. pose proof (k_Vfit k) as F. unfold entry_stack_fits, entry_stack_span, sp_window_hi in F.
    pose proof (total_arg_bytes_nonneg (in_argv (k_inp k))). pose proof (total_arg_bytes_nonneg (in_envp (k_inp k))).
    pose proof (u64_range (k_sp0 k)).
    unfold KH, KB. cbn [as_rauxv_ok KHp]. unfold Irauxv_ok. lia.
  Qed.

  Lemma kit_al : forall k, AMAIN_COST (KH k) P <= as_AL (KH k) (KS0 k).
  Proof.
    intros k. unfold KH, AMAIN_COST. cbn [as_Cm as_Cf as_AL KHp KS0 i_s a_AL Ks0 cert_s0]. unfold ICm, ICf, AL0.
    replace (2 ^ 26 <=? 64512) with false by reflexivity. lia.
  Qed.

  Lemma kit_tr : forall k, adrv_traces (KH k) P.
  Proof.
    intros k. unfold adrv_traces. unfold KH. cbn [as_TR KHp kip ip_TR].
    pose proof (TR_bp_drv LIB) as (T1 & T2 & T3 & T4 & T5 & T6).
    repeat (split; [assumption|]). split; [| apply PTR; reflexivity].
    apply TR_bp_pf. cbn [map]. exact PPF.
  Qed.

  Theorem as_instance_kit : as_instance_stmt P_main P.
  Proof.
    exact (instance_of_kit P KH KS0 KB kit_rt (fun k => @inst_driver_laws (KCEIL k) (kip k)) (fun k => KOWN (KCEIL k) (kip k)) (fun k => @AS_InstLawsTd.inst_td_law (KCEIL k) (kip k)) (fun k => @inst_live (KCEIL k) (kip k))
             kit_vis kit_krel kit_rfs kit_heap kit_aux kit_al kit_tr).
  Qed.
End KIT.

Check as_instance_kit.
