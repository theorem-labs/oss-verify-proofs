(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Mem Cells Step Frame Arr CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil AsanAllocModel LazyRestrict LazyLedger LazySR.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsDriverLaws AsDrvDefs AsMainPre AsInstance AsAuxv
  AllocWf AllocBudget AllocRep AllocRepX AsDepotInv FakeStackRep AsSR
  AS_InstWF AS_InstMainDefs AS_InstDefs AS_InstLaws1 AS_InstLaws2 AS_InstLaws3 AS_InstTR AS_InstHeap AS_InstFree
  AS_InstMainRep AS_InstMainK AS_InstMainVis AS_InstMainHeap ECH_Iface AsInstanceMain   (* [comment removed for export] *)
  AsIfaceX AS_InstLaws1x AS_InstRealloc   (* [comment removed for export] *)
  F_time F_timeI AsIfaceMemalign AS_InstMemalign AInstFacts.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit AsStartupHSF. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both Require Import AsMainState AsMainFacts AsMainLazy AsMainCells AsMainIface AsMainIfaceDepot AsMainIfaceAlloc AsMainIfaceFS.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both Require Import AsMainIfaceAuxv.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsCert Require Import AsImages AsPlanImages.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AsMainSyms.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AL0 : Z := 2 ^ 39 - 2 ^ 36 - 2 ^ 29.
(* [comment removed for export] *)
Definition ALIB_COST_MAX : Z := 2 ^ 36.

Section KIT.
  Variable L : alib.
  Variable LD : list (Z * list Z).
  Hypothesis TRLEN : (length (trlist_of (all_demands L LD)) <= TRCAP)%nat.
  Hypothesis DOK : demands_okb (all_demands L LD) = true.
  Hypothesis LT : forall (HC : HeapCeil) (H : asr), (forall pc0 t, In (pc0, t) LD -> trace_ok (as_TR H) pc0 t) -> al_tr_ok L H.
  Hypothesis LCOST : forall (HC : HeapCeil) (H : asr), as_Cm H = ICm -> as_Cf H = ICf -> al_cost L H (2 ^ 26) <= ALIB_COST_MAX.
  Hypothesis K_libx0 : forall iv, In iv (al_LIBX0 L) -> img_check (fst iv) (snd iv) = true.

  Definition kip (k : mctx) : iparams := {| ip_fsb := ps_b16 (KX k); ip_D := ps_b12 (KX k); ip_TR := trlist_of (all_demands L LD) |}.
  Definition KH (k : mctx) : asr := @KHp (KCEIL k) (kip k).
  Definition KB (k : mctx) : Z := bv_unsigned (k_sp0 k).
  Definition Ks0 (k : mctx) : ast := cert_s0 (bv_unsigned (k_sp0 k)) (bv_unsigned (k_brk0 k)) (KX k) [] false AL0.
  Definition Kd0 (k : mctx) : depot := depot0 (bv_unsigned (k_sp0 k)) (KX k).
  Definition KS0 (k : mctx) : as_St (KH k) := IST (Ks0 k) (Kd0 k).

  Lemma kip_TRLEN : forall k, (length (ip_TR (kip k)) <= 4000)%nat.
  Proof. intros k. cbn [kip ip_TR]. exact TRLEN. Qed.

  (* [comment removed for export] *)
  Lemma kit_rt : forall k, @asan_rt_hyps (KCEIL k) (KH k).
  Proof.
    intros k. unfold KH.
    pose proof (@inst_SR_laws (KCEIL k) (kip k)) as Lsr. pose proof (@inst_MPRES_laws (KCEIL k) (kip k)) as Lmp.
    pose proof (@inst_RHEAP_block_range (KCEIL k) (kip k)) as Lbr. pose proof (@inst_RHEAP_fsb (KCEIL k) (kip k)) as Lfsb.
    pose proof (@inst_rauxv_frame (KCEIL k) (kip k)) as Laux. pose proof (@inst_chain_laws (KCEIL k) (kip k)) as Lch.
    pose proof (@inst_RHEAP_frame (KCEIL k) (kip k)) as Lrf. pose proof (@inst_malloc_stmt (KCEIL k) (kip k) (kip_TRLEN k)) as Lma.
    pose proof (@inst_free_stmt (KCEIL k) (kip k) (kip_TRLEN k)) as Lfr. pose proof (@inst_free_null_stmt (KCEIL k) (kip k)) as Lfn.
    unfold asan_rt_hyps.
    split; [exact Lsr|]. split; [exact (inst_AKREL_laws (kip k))|]. split; [exact Lmp|].
    split; [exact (inst_alloc_ok_of_live (kip k))|]. split; [exact (inst_cost_laws (kip k))|].
    split; [exact Lrf|]. split; [exact Lbr|]. split; [exact (inst_RHEAP_blocks_disjoint (kip k))|]. split; [exact (inst_RHEAP_blocks_nodup (kip k))|].
    split; [exact (inst_RHEAP_shvis (kip k))|]. split; [exact Lfsb|]. split; [exact (inst_RHEAP_thr (kip k))|].
    split; [exact Laux|]. split; [exact (inst_lb_remove_laws (kip k))|].
    split; [exact (inst_RFS_frame (kip k))|]. split; [exact (inst_RFS_ext (kip k))|]. split; [exact (inst_RFS_range (kip k))|].
    split; [exact (inst_RFS_disjoint (kip k))|]. split; [exact (inst_RFS_nodup (kip k))|]. split; [exact (inst_RFS_shvis (kip k))|].
    split; [exact (inst_frame_release (kip k))|].
    split; [exact Lch|].
    split; [exact Lma|]. split; [exact Lfr|]. split; [exact Lfn|].
    split; [exact (inst_stack_malloc_1 (kip k))|]. split; [exact (inst_stack_malloc_4 (kip k))|]. split; [exact inst_set_shadow_f5|].
    split; [exact inst_asan_memcpy|]. split; [exact inst_asan_memset|]. split; [exact inst_asan_memmove|].
    split; [exact inst_memcpy_icpt|].
    split; [exact inst_strlen_icpt|]. exact inst_strncmp_icpt.
  Qed.

  (* [comment removed for export] *)
  Lemma kit_rt_x : forall k, @asan_rt_hyps_x (KCEIL k) (KH k).
  Proof.
    intros k. unfold asan_rt_hyps_x. split; [exact (kit_rt k)|]. unfold KH.
    split; [exact (@inst_realloc_stmt (KCEIL k) (kip k) (kip_TRLEN k))|].
    split; [exact (@inst_stack_malloc_0 (KCEIL k) (kip k))|]. split; [exact (@inst_stack_malloc_2 (KCEIL k) (kip k))|].
    split; [exact (@inst_stack_malloc_6 (KCEIL k) (kip k))|]. split; [exact (@inst_stack_free_6 (KCEIL k) (kip k))|].
    split; [exact inst_set_shadow_00|]. split; [exact inst_set_shadow_f8|].
    split; [exact (@inst_slack_law (KCEIL k) (kip k))|].   (* [comment removed for export] *)
    split; [exact (@inst_rheap_perm (KCEIL k) (kip k))|].   (* [comment removed for export] *)
    exact (@inst_canary_law (KCEIL k) (kip k)).   (* [comment removed for export] *)
  Qed.

  (* [comment removed for export] *)
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
                       (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Vfit k) (k_Hh k) (k_HC k) (KCEIL k) eq_refl [] false AL0 (kip k) eq_refl eq_refl).
  Qed.

  (* [comment removed for export] *)
  Lemma kit_budget : forall k, ABUDGET (Ks0 k) (k_model k).
  Proof.
    intros k.
    pose proof (AsMainIfaceAlloc.ak_budget (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
                  (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Hh k) (k_HC k)) as (B1 & B2 & B3 & B4).
    unfold ABUDGET, aPhi, Ks0, KX. cbn [a_AL a_S a_st cert_s0]. unfold cert_st0. rewrite AllocBudget.pusage_init. rewrite B2. unfold KX in B3. rewrite B4 in B3.
    unfold target_alloc_limit, page_size, AllocBudget.B_PRIM, AL0. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma kit_IK : forall k, @IK (KCEIL k) (kip k) (KS0 k) (k_model k).
  Proof.
    intros k. unfold IK. cbn [i_s i_d KS0].
    split; [|split].
    - (* [comment removed for export] *) split; [split; [|split]|].
      + exact (AS_InstMainK.amaps_main (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
                 (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Hh k) (k_HC k) (KCEIL k) eq_refl [] false AL0).
      + exact (AS_InstMainK.ashadow_main (k_sp0 k) (k_brk0 k) (k_h k) (k_E k) [] false AL0).
      + exact (kit_budget k).
      + exact (AS_InstMainK.akernel_main (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
                 (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Hh k) (k_HC k) (KCEIL k) eq_refl [] false AL0).
    - (* [comment removed for export] *)
      intros x Hx. cbn [Kd0 depot0 d_nb d_sb] in Hx.
      destruct Hx as [Hx|Hx].
      + apply (AsMainIfaceAlloc.ak_maps_in (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
                 (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Hh k) (k_HC k) (ps_b21 (KX k)) 0x100000); [cbn; tauto | lia].
      + apply (AsMainIfaceAlloc.ak_maps_in (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
                 (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Hh k) (k_HC k) (ps_b22 (KX k)) 0x800000); [cbn; tauto | lia].
    - (* [comment removed for export] *)
      intros x Hx. cbn [kip ip_D] in Hx. unfold kPageSize in Hx.
      apply (AsMainIfaceAlloc.ak_maps_in (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
               (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Hh k) (k_HC k) (ps_b12 (KX k)) 0x1000); [cbn; tauto | lia].
  Qed.

  Lemma kit_krel : forall k, as_AKREL (KH k) (KS0 k) (Kcfg k).
  Proof.
    intros k. split.
    - (* [comment removed for export] *) exact (proj1 (AsMainLazy.lzok_open (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
                          (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Hh k) (k_HC k))).
    - exact (kit_IK k).
  Qed.

  Lemma kit_aux : forall k, as_rauxv_ok (KH k) (KVM k) (KB k) /\ bv_unsigned (k_sp0 k) <= KB k < 2 ^ 64 /\ @aauxv_ok (KCEIL k) (KVM k) (KB k).
  Proof.
    intros k. pose proof (k_Vfit k) as F. unfold entry_stack_fits, entry_stack_span, sp_window_hi in F.
    pose proof (total_arg_bytes_nonneg (in_argv (k_inp k))). pose proof (total_arg_bytes_nonneg (in_envp (k_inp k))).
    pose proof (u64_range (k_sp0 k)).
    split; [| split].
    - unfold KH, KB. cbn [as_rauxv_ok KHp]. unfold Irauxv_ok. lia.
    - unfold KB. lia.
    - (* [comment removed for export] *)
      exact (AsMainIfaceAuxv.auxv_ok_main (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
               (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Vfit k) (k_Hh k) (k_HC k) (KCEIL k) eq_refl).
  Qed.

  (* [comment removed for export] *)
  Lemma kit_al : forall k, AMAIN_COST (KH k) L <= as_AL (KH k) (KS0 k).
  Proof.
    intros k. pose proof (LCOST (KCEIL k) (KH k) eq_refl eq_refl) as LC.
    unfold AMAIN_COST, fuzz_cost. unfold KH in LC |- *. cbn [as_Cm as_Cf as_AL KHp KS0 i_s a_AL Ks0 cert_s0] in LC |- *.
    unfold ICm, ICf, ALIB_COST_MAX, AL0 in LC |- *. cbn [Z.leb] . change (2 ^ 26 <=? 64512) with false. cbn [negb].
    lia.
  Qed.

  Lemma kit_tr : forall k, adrv_traces (KH k) L.
  Proof.
    intros k. apply (inst_K_tr (KH k) L LD eq_refl DOK). apply (LT (KCEIL k) (KH k)). exact (inst_lib_demand (KH k) L LD eq_refl DOK).
  Qed.

  (* [comment removed for export] *)
  Lemma kit_ifacts : forall k, @ainst_facts (KCEIL k) (KH k).
  Proof. intros k. split; [exact (@atime_inst (KCEIL k) (kip k)) | exact (@inst_memalign_stmt (KCEIL k) (kip k) (kip_TRLEN k))]. Qed.

  (* [comment removed for export] *)
  Theorem as_instance_kit : as_instance_stmt P_main L.
  Proof.
    exact (instance_of_kit KH KS0 KB L kit_rt_x kit_ifacts (fun k => @inst_driver_laws (KCEIL k) (kip k)) (fun k => @inst_live (KCEIL k) (kip k))   (* [comment removed for export] *)
             kit_vis kit_krel kit_rfs kit_heap kit_aux kit_al kit_tr K_libx0).
  Qed.
End KIT.

(* [comment removed for export] *)
Check as_instance_kit.
Check kit_rt_x.
