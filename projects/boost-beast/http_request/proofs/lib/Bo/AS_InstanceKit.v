(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.boost_beast.http_request.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Mem Cells Step Frame Arr CellsX TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil AsanAllocModel LazyRestrict LazyLedger LazySR.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface AsIface5 AsIface6 AsIface7 AsIface8 AsTRList AsDriverLaws AsCXXHeap AsStack0 AXPres AXFuzz_stmt AsDrvDefs AsMainPre AsInstance.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AllocWf AllocBudget.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AllocRep AllocRepX AsDepotInv FakeStackRep AsSR.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AS_InstWF.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AS_InstMainDefs AS_InstDefs AS_InstLaws1 AS_InstLaws2 AS_InstLaws3 AS_InstLaws8 AS_InstStubs AS_InstStubs7 AS_InstTR AS_InstHeap AS_InstFree AS_InstFreeW AS_InstMainRep AS_InstMainK AS_InstMainVis AS_InstMainHeap AsInstanceMain.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  PropExec AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit BothImages BothPlanImages BoStartupHSF BoMainState BoMainFacts BoMainLazy BoMainCells BoMainIface BoMainIfaceStk BoMainIfaceDepot BoMainIfaceAlloc BoMainIfaceFS.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AsMainSyms.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kip (k : mctx) : iparams := {| ip_fsb := ps_b16 (KX k); ip_D := ps_b12 (KX k); ip_TR := TRLIST |}.
Definition KH (k : mctx) : asr := @KHp (KCEIL k) (kip k).
Definition KB (k : mctx) : Z := bv_unsigned (k_sp0 k).

(* [comment removed for export] *)
Definition AL0 : Z := 2 ^ 39 - 2 ^ 36 - 2 ^ 29.

Section KIT.
  Definition Ks0 (k : mctx) : ast := cert_s0 (bv_unsigned (k_sp0 k)) (bv_unsigned (k_brk0 k)) (KX k) [] false AL0.
  Definition Kd0 (k : mctx) : depot := depot0 (bv_unsigned (k_sp0 k)) (KX k).
  Definition KS0 (k : mctx) : as_St (KH k) := IST (Ks0 k) (Kd0 k).

  (* [comment removed for export] *)
  Definition ACOST_at (k : mctx) : Prop := AMAIN_COST (KH k) <= ACWILD * AWMAX.
  Hypothesis BCOST : forall k, ACOST_at k.

  Lemma R_free : forall k, @free_stmt (KCEIL k) (KH k).
  Proof. intros k. exact (@inst_free_stmt (KCEIL k) (kip k) TRLIST_len_nat). Qed.
  Lemma R_free_null : forall k, @free_null_stmt_at (KCEIL k) (KH k) AFREE_STUB.
  Proof. intros k. exact (@inst_free_null_stmt (KCEIL k) (kip k)). Qed.

  (* [comment removed for export] *)
  Lemma kit_rt : forall k, @asan_rt_hyps (KCEIL k) (KH k).
  Proof.
    intros k. unfold KH.
    pose proof (@inst_SR_laws (KCEIL k) (kip k)) as Lsr. pose proof (@inst_MPRES_laws (KCEIL k) (kip k)) as Lmp.
    pose proof (@inst_RHEAP_block_range (KCEIL k) (kip k)) as Lbr. pose proof (@inst_RHEAP_fsb (KCEIL k) (kip k)) as Lfsb.
    pose proof (@inst_rauxv_frame (KCEIL k) (kip k)) as Laux. pose proof (@inst_chain_laws (KCEIL k) (kip k)) as Lch.
    pose proof (@inst_TR_laws1 (KCEIL k) (kip k) eq_refl) as Ltr.
    pose proof (@inst_RHEAP_frame (KCEIL k) (kip k)) as Lrf. pose proof (@inst_malloc_stmt (KCEIL k) (kip k) TRLIST_len_nat) as Lma. pose proof (R_free k) as Lfr. pose proof (R_free_null k) as Lfn.
    unfold KH in Lfr, Lfn.
    unfold asan_rt_hyps.
    split; [exact Lsr|]. split; [exact (inst_AKREL_laws (kip k))|]. split; [exact Lmp|].
    split; [exact (inst_alloc_ok_of_live (kip k))|]. split; [exact (inst_cost_laws (kip k))|].
    split; [exact Lrf|]. split; [exact Lbr|]. split; [exact (inst_RHEAP_blocks_disjoint (kip k))|]. split; [exact (inst_RHEAP_blocks_nodup (kip k))|].
    split; [exact (inst_RHEAP_shvis (kip k))|]. split; [exact Lfsb|]. split; [exact (inst_RHEAP_thr (kip k))|].
    split; [exact Laux|]. split; [exact (inst_lb_remove_laws (kip k))|].
    split; [exact (inst_RFS_frame (kip k))|]. split; [exact (inst_RFS_ext (kip k))|]. split; [exact (inst_RFS_range (kip k))|].
    split; [exact (inst_RFS_disjoint (kip k))|]. split; [exact (inst_RFS_nodup (kip k))|]. split; [exact (inst_RFS_shvis (kip k))|].
    split; [exact (inst_frame_release (kip k))|].
    split; [exact Lch|]. split; [exact Ltr|].
    split; [exact Lma|]. split; [exact (opnew_of_malloc _ Lsr Lmp Lbr Lfsb Lrf Laux Lch Ltr Lma)|].
    split; [exact Lfr|]. split; [exact (opdel_of_free _ Lsr Lmp Lfr)|]. split; [exact (opdel2_of_free _ Lsr Lmp Lfr)|].
    split; [exact Lfn|]. split; [exact (opdel_null_of_free_null _ Lsr Lmp Lfn)|]. split; [exact (opdel2_null_of_free_null _ Lsr Lmp Lfn)|].
    split; [exact (inst_stack_malloc_1 (kip k))|]. split; [exact (inst_stack_malloc_4 (kip k))|]. split; [exact inst_set_shadow_f5|].
    split; [exact inst_asan_memcpy|]. split; [exact inst_asan_memset|]. split; [exact inst_asan_memmove|].
    split; [exact inst_memcpy_icpt|]. split; [exact inst_memmove_icpt|].
    split; [exact inst_strlen_icpt|]. exact inst_annotate_cc.
  Qed.

  (* [comment removed for export] *)
  Lemma kit_rtx : forall k, @asan_rt_hyps5 (KCEIL k) (KH k) /\ @asan_rt_hyps5x (KCEIL k) (KH k) /\ @asan_rt_hyps6 (KCEIL k) /\ @asan_rt_hyps7 (KCEIL k) (KH k)
                            /\ asan_rt_hyps8 (KH k) /\ incl TRLIST (as_TR (KH k)).   (* [comment removed for export] *)
  Proof.
    intros k. pose proof (@inst_SR_laws (KCEIL k) (kip k)) as Lsr. pose proof (@inst_MPRES_laws (KCEIL k) (kip k)) as Lmp.
    pose proof (R_free k) as Lfr. pose proof (R_free_null k) as Lfn. unfold KH in *.
    split; [exact (@inst_rt_hyps5 (KCEIL k) (kip k))|]. split; [exact (@inst_rt_hyps5x (KCEIL k) (kip k))|].
    split; [exact (@inst_rt_hyps6 (KCEIL k))|].
    split; [| split; [exact (@inst_rt_hyps8 (KCEIL k) (kip k))| exact (inst_incl_TR (@KHp (KCEIL k) (kip k)) eq_refl)]].
    apply (@asan_rt_hyps7_of (KCEIL k) (KHp (kip k)) Lsr Lmp).
    - exact (opdel_of_free _ Lsr Lmp Lfr).
    - exact (opdel_null_of_free_null _ Lsr Lmp Lfn).
    - exact (@inst_free_wild_stmt (KCEIL k) (kip k) TRLIST_len_nat).
  Qed.

  (* [comment removed for export] *)

  Lemma kit_vis : forall k, as_VIS (KH k) (KS0 k) (cfg_ms (Kcfg k)) = mkst (k_R k) (Z_to_bv 64 A_MAIN) (KVM k) (seg_rom bsegs).
  Proof. intros k. exact (AS_InstMainK.vis_main_s0 (k_sp0 k) (k_brk0 k) (k_h k) (k_E k) (k_R k) (k_FULL k) [] false AL0). Qed.

  Lemma kit_rfs : forall k, as_RFS (KH k) [] (KVM k).
  Proof.
    ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.mctx); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AS_InstMainK.rfs_main); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.k_sp0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.k_brk0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.k_rdraw); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.k_inp); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.k_h); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.k_ch); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.k_E); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.k_R); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.k_FULL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.k_model); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.k_Vsp); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.k_Vbrk); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.k_Vav); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.k_Vev); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.k_Vfit); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.k_Hh); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.k_HC); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.KCEIL); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil)|] [|@k|] "##9#$#;###)#*#+#,#-#.#/#0#1#2#3#4#5#6#7#8#9#:#=#;#<#(#'#UDCUECUFCUGCUHCUICUJCUKCULCUMCUNCUOCUPCUQCURCUS#CUS$CUS%CUS&#VS'S(#gS)6543210/.-,+*)('&%#j#$S*##"). Qed.

  Lemma kit_heap : forall k, as_RHEAP (KH k) (KS0 k) [] (KVM k).
  Proof.
    intros k. exact (AS_InstMainHeap.rheap_main (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
                       (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Vfit k) (k_Hh k) (k_HC k) (KCEIL k) eq_refl [] false AL0 (kip k) eq_refl eq_refl
                       (BoMainIfaceStk.stack_present (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
                          (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Vfit k) (k_Hh k) (k_HC k))).
  Qed.

  (* [comment removed for export] *)
  Lemma kit_budget : forall k, ABUDGET (Ks0 k) (k_model k).
  Proof.
    intros k.
    pose proof (BoMainIfaceAlloc.ak_budget (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
                  (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Hh k) (k_HC k)) as (B1 & B2 & B3 & B4).
    unfold ABUDGET, aPhi, Ks0, KX. cbn [a_AL a_S a_st cert_s0]. unfold cert_st0. rewrite AllocBudget.pusage_init. rewrite B2. unfold KX in B3. rewrite B4 in B3.
    unfold target_alloc_limit, page_size, AllocBudget.B_PRIM, AL0. lia.
  Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.or Sort Prop.

  (* [comment removed for export] *)
  Lemma kit_IK : forall k, @IK (KCEIL k) (kip k) (KS0 k) (k_model k).
  Proof.
    ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.mctx); constr:(@Corelib.Init.Logic.conj); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRepX.AMODELX); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.KCEIL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AS_InstanceKit.KIT.Ks0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.k_model); constr:(@Corelib.Init.Logic.and); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRepX.depot_cov); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AS_InstanceKit.KIT.Kd0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AS_InstDefs.dtv_cov); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AS_InstanceKit.kip); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRep.AMODEL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRepX.akernel); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRep.amaps_in_ledger); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRep.ashadow_visible); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRep.ABUDGET); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AS_InstMainK.amaps_main); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.k_sp0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.k_brk0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.k_rdraw); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.k_inp); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.k_h); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.k_ch); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.k_E); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.k_R); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.k_FULL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.k_Vsp); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.k_Vbrk); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.k_Vav); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.k_Vev); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.k_Hh); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.k_HC); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.false); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AS_InstanceKit.AL0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AS_InstMainK.ashadow_main); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AS_InstanceKit.KIT.kit_budget); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AS_InstMainK.akernel_main); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.or); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsDepotInv.d_nb); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsDepotInv.d_sb); constr:(@kc__1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsMainSyms.ps_b21); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsInstanceMain.KX); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsMainSyms.ps_b22); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.in_rangesb); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_maps); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainIfaceAlloc.ak_maps_in); constr:(@Corelib.Init.Logic.and_ind); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.pair); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.vE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.K_B23); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.hole_granted); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.K_B21); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.K_B22); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.K_B20); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsMainSyms.pm_meta_map); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.Xof); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.K_B16); constr:(@Corelib.Numbers.BinNums.xI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.K_B12); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.K_B11); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.K_B10); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.K_B09); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.K_B08); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.K_B06); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.K_B05); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.K_B04); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Logic.or_intror); constr:(@Corelib.Init.Logic.or_introl); constr:(@Stdlib.Lists.List.In); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.PM_MAPS); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AS_InstDefs.ip_D); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.kPageSize); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsMainSyms.ps_b12); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AS_InstDefs.i_s); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AS_InstanceKit.KIT.KS0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AS_InstDefs.i_d); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AS_InstDefs.IK)|] [|@H0; @H; @__ff; @__varmap; @__wit; @__x1; @__x2; @__arith; @Hx; @x; @k|] "#,{#*$K#N##$5#%#'#$$6$4$'$<#&$=#Q#R#Y#h#l#y#{#|#}#~$#$$$%$&#)$2#m#/#5#4#7#P$+$,$:$?$I#0#1#6#8#9#:#;#<#O#=#S#T#U#W#V#\#b#k#j#i#o#($-$/$0$.$1$3$;$A$B$D$E$F$C#c$G$H$K$J$L$M#-#X#g#Z#z#p#`#q#_#^#3#a#[$(#]$@$9$8#M#.$>$7#2#?#B#D#e#d#f#>#@#A#C#E#F#G#H#I#J#K#L#s#r#t#u#v#x#w$)#n$*U#u$#v&#w%#x$#y'#z%#{%#|%#}%#~%$#$$$%$%&$&%$'%$('$)*$*%$+'$,&$-*$.$$/$$0$$1$$2$$3$$4$$5$$6$$7$$8$$9$$:$$;$$<$$=$$>$$?$$@$$A$$B$$C$$D$$E$$F%$G%$H&$I($J&US:DUS;D8DWS0%$#US1DVS2#%US3DVS<#',%#VS=*)WS>,+*VS?,+US@-VSA.-,$#?D9D@DAD:DBD;DCDDDEDFDGDHDIDJDUSB@4C#US4Ci#8SC43210/.-,A+*)('&s##$#OP[SD541/$OPUSED5:9$#5<9&#i#8SF987654321s#&0/.-,+s#()(OP5@?$##Q##########USG#USH#US1HUSI#0&D.$#-+#*##################-#(.#*2#+2#,2#USJ6.#5->#+##-#(&#*)#+<#,*#%-#<F=#0s#%H.$#*%5+%#,%#>).#(*$0+*#,%#%(#8MUSK#USL#VSMF#$R#S#j##(#<M=#0s#8F.$#*%s#(+%#,%#?G9G@GAG:GBG;GCGDG8GEGFGGGHGIGJG<G=##s#5##-#0s#RM.'#*(s#B+%#VSNCC-s#KK9L#)9#(&#'CC#'M')=#(*#'CC#1$-'#N,)B#(/##7####-#'CC'#$6#,$7--O6)s#,#(9#'CC#:$<#20s#qs#5P<s#1Q$#-s#g'CC$#$B#8)s#6S$(s###&s$#&#########&#####&#########################-#'CC:#$s#=#s#3)s#QS%(s#>#'CC#s#?$s#A#s#7)s#US&(s#B#'CC#s#C$s#E#s#;)s#YS'(s#F#'CC#s$/$s#I#s#?)s#]S((s#J#'CC#s#K$s#M#s#C)s#aS)(s#N#'CC#s#>$s#Q#s#G)s#eS*(s#R#&s#Z######&#########################-#'CC5#$s#g#s#])s#{S+(s#h#&Q&#######&#&#&###########################-#'CC9#$s$%#s#w)s$9S,(s$&#'CC#s$k$s$)#s#{&s$u######&#&#&#&#&#&#&#&#&#&#&#&###&#&#&#########################-##s#?&#&#&#&#&#&#&#&#&#&#&#&#&###############################&#########################-#'CCs#.#$s$w#s$m&s%t&#&#&#&#&#&#&#&#&#&#&###&#&#&#########################-##s%(##################################-#'CC6#$s%M#s%C&s$A&#&#&#&#&#&#&#&#&#&#&###&#&#&#########################-#-s#0'CC$#$s%m#s%c%#K%s#$#%s#W#%s$J#%s$O#%s$j#%s%%#%s%*#%s%/#%s%4#%s%9#%s%>#%s%Z#%s%a#%s%g#%s%i#%s%s#0s&wG<SO=#*#s&h+&#;S-:S-K#L#)&#(s&,#'CC#s&-M')*#(s&0#'CC#s&7$s&3'#N,)/#(s&5#'CC#s&%$s&8#($s&9))O2)5#(s&;#'CC#s&<$s&>#.9S-0s'8#P9;Q$#'CC#s&%$s&D#4)?S$(s&E#'CC#s%j$s&H#8)s##S%(s&I#'CC#s&J$s&L#<)s#'S&(s&M#'CC#s&N$s&P#@)s#+S'(s&Q#'CC#s':$s&T#s#$)s#/S((s&U#'CC#s&V$s&X#s#()s#3S)(s&Y#'CC#s&I$s&\#s#,)s#7S*(s&]#'CC#s%X$s&`#s#0)s#;S+(s&a#'CC#s%B$s&d#s#4)s#?S,(s&e#'CC#s'N$s&h#s#8$s&is$Qs#9$s&js#|s#:$s&ks#]s#;%#K%%#%'#%)#%.#%3#%8#%=#%B#%s#'#%s#,#%s#1#%s#6#%s#=#%s#C#%s#E#4s&|s#LRs#F&#/s#H&#/s#N&#j#$s#[#j#%s'(#Ss')s''s#b#D'CCs'/s',VS5s&is&hTs')$#m#&#US4S6USPS6VSQCFUSRCXSSC$H#USTCUSUCVS7CQVS7Cs(12C$SV#3&JEEI#L1Cs((1Cs'zWS8C$#6C)#2C)N#3,JEEI#L7-JEEI)#USWE1Cs'C6C/#2C/N#32JEEI#L73JEEI/#\S.4JEEI)(#VSX5I4RS#VSYDF$R#S#m$%#WSZCS[HXS\DF$#l#&*)#l#'?>#l#(s#$s###j#)C#j#*C#.DH*Ds(7+H#,%#.HF*Hs'Z+F#,%#k##'#k#)C#k#*C#WDs$:s$8Hl#+/$#i#8S/s'vs'us'ts'ss'rs'qs'ps'os'ns'ms'ls'ks'js'is'hs'gs'es'bMs#5#j#,s'x#U#Dj##s(1#>s(%.#s($*$s(?+s(&#,%#>s'o.#s'k*$s(D+s'm#$s'js'ds'W$s'ks'Xs'X$s'ls'bs'Y$s'ms'Ts'Z$s'ns'Os'[$s'os'5s'\$s'ps'2s']$s'qs'/s'^$s'rs',s'_$s'ss')s'`$s'ts'&s'a$s'us&ms'b$s'vs&Ts'c$s'ws&Qs'd$s'xs%`s'e$s'ys%/s'f$s'zs$ls'g%#K%%#%'#%)#%+#%-#%/#%1#%3#%5#%7#%9#%;#%=#%?#%A#%s###>s$j*#s(i+s$m#$s(3s$cs$Z$s(4s$[s$[$s(5s$as$\$s(6s$Ws$]$s(7s$Rs$^$s(8s$Os$_$s(9s$Ls$`$s(:s$Is$a$s(;s$Fs$b$s(<s$Cs$c$s(=s$@s$d$s(>s$=s$e$s(?s$:s$f$s(@s$7s$g$s(As&)s$h$s(Bs%Ts$i$s(Cs%5s$j%#K%%#%'#%)#%+#%-#%/#%1#%3#%5#%7#%9#%;#%=#%?#%A#4s(Ts${Rs##%#/s#%%#j#$s#'#j#%s#O#Ss#Ps#Ns#,#D'CCs#Rs(HTs([#s$5m#%#1Cs)=1Cs);WS8C$#6Cs$0#2Cs$0N#3s$3JEEI#L7s$4JEEIs$0#1Cs(R6Cs$5#2Cs$5N#3s$8JEEI#L7s$9JEEIs$5#\S.s$:JEEI(s$.#l#&#s$(s#~l#'s$>s$=#l#(s$Cs$B#j#)C#j#*C#*Ds)K+H#,s$##*Hs(`+F#,s#~#k##&#k#)C#k#*C#WDs%Ws#JHl#+-$#i#8S/s)7s)6s)5s)4s)3s)2s)1s)0s)/s).s)-s),s)+s)*s))s)(s#rs(hM@#j#,s#t#U#Dj##s)I#ZS]s)Os)Js)Cs#|#Dj#,s)W#j#-s)w#m##s*FUS3HUS^#.#s)x*$S_+s)z#,%#?F9F@FAF:FBF;FCFDF8FEFFFGFHFIFJFUS9s)o.#s)n*$s)=+s)p#K2L#)2#(s)B#'CC#s)C)5S%(s)E#'CC#s)F$s)H&#N+):#(s)J#'CC#s):$s)M#(M0)?#(s)O#'CC#s)V$s)R#-O5)s#$#(s)T#'CC#s)U$s)W#20s*Ps#-P;s#)Q$#'CC#s)=$s)\#7)s#-S$(s)]#'CC#s)&$s)`#;$s)a<<)s#2S&(s)b#'CC#s)c$s)e#@)s#6S'(s)f#'CC#s*O$s)i#s#$)s#:S((s)j#'CC#s)k$s)m#s#()s#>S)(s)n#'CC#s)^$s)q#s#,)s#BS*(s)r#'CC#s(m$s)u#s#0)s#FS+(s)v#'CC#s(W$s)y#s#4)s#JS,(s)z#'CC#s*c$s)}#s#8$s)~s'fs#9$s*#s'5s#:$s*$s&rs#;%#K%%#%'#%)#%.#%3#%8#%=#%B#%s#'#%s#,#%s#.#%s#3#%s#9#%s#?#%s#E#%s#K#US9s*V*#s*6+s*V#$s*9s*3s)W$s*:s*'s)X$s*;s*1s)Y$s*<s*#s)Z$s*=s)zs)[$s*>s)`s)\$s*?s)]s)]$s*@s)Zs)^$s*As)Ws)_$s*Bs)Ts)`$s*Cs)Qs)a$s*Ds)<s)b$s*Es)#s)c$s*Fs(|s)d$s*Gs(/s)e$s*Hs'Zs)f$s*Is';s)g%#K%%#%'#%)#%+#%-#%/#%1#%3#%5#%7#%9#%;#%=#%?#%A#4s*Zs)xR>*#/@*#/B*#/s#$*#/s#&*#/s#(*#/s#**#j#$s#,#j#%s$(#Ss$)s$'s#1#D'CCs$+s*dVS5s#ls#kTs*g$#m#&#1Cs*h6Cs&:#2Cs&:N#3s&=JEEI#L7s&>JEEIs&:#\S.s&?JEEI#s&3#l#&#s&-s&'l#'s&Cs&B#l#(s&Hs&G#j#)C#j#*C#*Ds*s+H#,s&(#*Hs*v+F#,s&'#k##&#k#)C#k#*C#WDs+?s#IHl#+-$#i#8S/s$Us$Ts$Ss$Rs$Qs$Ps$Os$Ns$Ms$Ls$Ks$Js$Is$Hs$Gs$Fs$Es*~H9#j#,s$W#j#-s+x#m##s,E5s,Hs,Fs$`#5s,Ks,Fs,'#US`DVSas,P#WS0s,Q#s,OVSbs,R%VS2#s,Q,#s,M,&#m#*#XScs,Ws,Q*s,Um#$#j#.Sd##"). Qed.

  Lemma kit_krel : forall k, as_AKREL (KH k) (KS0 k) (Kcfg k).
  Proof.
    intros k. split.
    - (* [comment removed for export] *) exact (proj1 (BoMainLazy.lzok_open (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
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

  (* [comment removed for export] *)
  Lemma kit_al : forall k, AMAIN_COST (KH k) <= as_AL (KH k) (KS0 k).
  Proof.
    intros k. pose proof (BCOST k) as C. unfold ACOST_at in C.
    unfold KH in *. cbn [as_AL KHp]. unfold IAL. cbn [KS0 i_s i_d a_AL Ks0 cert_s0 Kd0].
    replace (nwild (kip k) (depot0 (bv_unsigned (k_sp0 k)) (KX k))) with 0 by reflexivity.
    unfold AL0, ACWILD, AWMAX in *. lia.
  Qed.

  Lemma kit_tr : forall k, adrv_traces (KH k).
  Proof. intros k. exact (inst_adrv_traces (KH k) eq_refl). Qed.

  (* [comment removed for export] *)
  Theorem as_instance_kit : as_instance_stmt P_main.
  Proof.
    exact (instance_of_kit KH KS0 KB kit_rt (fun k => @inst_driver_laws (KCEIL k) (kip k)) kit_rtx (fun k => @inst_live (KCEIL k) (kip k))
             kit_vis kit_krel kit_rfs kit_heap kit_aux kit_al kit_tr).
  Qed.

End KIT.

(* [comment removed for export] *)
Check as_instance_kit.
