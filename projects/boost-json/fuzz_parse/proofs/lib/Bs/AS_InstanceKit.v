(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Mem Cells Step Frame Arr CellsX TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil AsanAllocModel LazyRestrict LazyLedger LazySR.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AsConst AsIface AsDriverLaws AsDrvDefs AsMainPre AsInstance
  AllocWf AllocBudget AllocRep AllocRepX AsDepotInv FakeStackRep AsSR Fuzz_stmt
  AS_InstWF AS_InstMainDefs AS_InstDefs AS_InstLaws1 AS_InstLaws2 AS_InstLaws3 AS_InstStubs AS_InstTR AS_InstHeap AS_InstFree
  AS_InstMainRep AS_InstMainK AS_InstMainVis AS_InstMainHeap AsInstanceMain.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit BothImages BothPlanImages BsStartupHSF
  BsMainState BsMainFacts BsMainLazy BsMainCells BsMainIface BsMainIfaceDepot BsMainIfaceAlloc BsMainIfaceFS.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import AsMainSyms.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsbAS_InstDefs~~~~~~07iparams79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BseAsInstanceMain~~~~~~ka4mctxka2KX02IP79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs9AS_InstTR~~~~~~pe6TRLIST79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsaAsMainSyms~~~~~~u66ps_b12u66ps_b1679OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsIface~~~~~~hj83asr03KHp79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BseAS_InstanceKit~~~~~~ho13kipka5KCEIL37Corelib7Numbers7BinNumsht41Zht44Nposka5k_sp035stdpp9bitvectorbdefinitionsig2bbv_unsigned46Stdlib6ZArith6BinInt1Ziie3powiie3sub79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AllocRep~~~~~~il43ast37Corelib4Init9Datatypesip95falseip93nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsfAS_InstMainDefs~~~~~~is17cert_s0ho13AL0ka6k_brk079OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsaAsDepotInv~~~~~~ji15depot69OSSVerify6Proofsaboost_jsonafuzz_parse3libh0BsMainIfaceDepot~~~~~~jma6depot0ho12KHhj85as_St03IST89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BseAS_InstanceKit3KIT~~~~~~jsc3Kd0jsc3Ks0hj8casan_rt_hyps37Corelib4Init5Logickj22eq3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticskkcdmachine_state3h5LinuxProcessSemanticsfLinuxProcessSem3Runkp46cfg_msjsc3KS079OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~kt15asegshj86as_VISka3KVMka4Kcfgka3k_R69OSSVerify6Proofsaboost_jsonafuzz_parse3libbBsMainState~~~~~~lj26A_MAIN69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~lna3fx0lna4mkstlna7seg_romig27Z_to_bvhj86as_RFShj86fframehj88as_RHEAPhj85blockil47ABUDGETka7k_model02IKhj88as_AKRELho12KBkj23andhj8bas_rauxv_okiie2leiie2lthj85as_AL79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs9AsMainPre~~~~~~ml9aAMAIN_COST79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs9AsDrvDefs~~~~~~mq6badrv_traces79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsaAsInstance~~~~~~mv4h0as_instance_stmtlj26P_main79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsbAS_InstFree~~~~~~nl3dfree_stmt_big" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Existing Instance fx0.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kip : ltac2:(zQ "20!k1!oe>1k$1$0") := ltac2:(zQ "60!p5!pa!td!oe!hi6!hif\1k$3@3$1@1$5@1$0^1@1$4@1$0^1$2").
Definition KH : ltac2:(zQ "20!hn5!oe>1k$1$0") := ltac2:(zQ "40!hnc!hs5!hsc!oe\1k$3@2$0@1$2^1@1$1^1").
Definition KB : ltac2:(zQ "20!hud!oe>1k$1$0") := ltac2:(zQ "40!hv2!hva!oe!ihf\1k$2@2$3@1$0#k0@1$1^1").

(* [comment removed for export] *)
Definition AL0 : ltac2:(zQ "10!hud$0") := ltac2:(zQ "20!ik6!ikd@2$1@2$1@2$0+2+i7@2$0+2+i5@2$0+2+hd").   (* [comment removed for export] *)

Section KIT.
  Definition Ks0 : ltac2:(zQ "20!ip2!oe>1k$1$0") := ltac2:(zQ "b0!hv2!ihf!ir1!ira!hud!jg6!jh1!p5!jh8!hva!oe\1k$a@6$5@2$1@1$0#k0@1$9^1@2$1@1$0#k0@1$8^1@1$7^1@1$3$4$2$6").
  Definition Kd0 : ltac2:(zQ "20!jm1!oe>1k$1$0") := ltac2:(zQ "60!hv2!p5!hva!oe!jqe!ihf\1k$3@2$4@2$5@1$0#k0@1$2^1@1$1^1").
  Definition KS0 : ltac2:(zQ "30!jr8!jre!oe>1k$2@1$1@1$0^1") := ltac2:(zQ "50!js7!kh4!khb!hsc!oe\1k$4@3$0@1$3^1@1$2^1@1$1^1").

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis R_freebig : ltac2:(zQ "40!np4!hs5!hsc!oe>1k$3@2$0@1$2^1@1$1^1").
  Let R_free : forall k, @free_stmt (KCEIL k) (KH k) := fun k => @inst_free_stmt (KCEIL k) (kip k) TRLIST_length (R_freebig k).
  Let R_free_null : forall k, @free_null_stmt_at (KCEIL k) (KH k) AFREE_STUB := fun k => @inst_free_null_stmt (KCEIL k) (kip k).

  (* [comment removed for export] *)
  Lemma kit_rt : ltac2:(zQ "40!jr8!ki2!hsc!oe>1k$3@2$1@1$2^1@1$0^1").
  Proof.
    intros k. unfold KH.
    pose proof (@inst_SR_laws (KCEIL k) (kip k)) as Lsr. pose proof (@inst_MPRES_laws (KCEIL k) (kip k)) as Lmp.
    pose proof (@inst_RHEAP_block_range (KCEIL k) (kip k)) as Lbr. pose proof (@inst_RHEAP_fsb (KCEIL k) (kip k)) as Lfsb.
    pose proof (@inst_rauxv_frame (KCEIL k) (kip k)) as Laux. pose proof (@inst_chain_laws (KCEIL k) (kip k)) as Lch.
    pose proof (@inst_TR_laws1 (KCEIL k) (kip k) eq_refl) as Ltr.
    pose proof (@inst_RHEAP_frame (KCEIL k) (kip k)) as Lrf. pose proof (@inst_malloc_stmt (KCEIL k) (kip k) TRLIST_length) as Lma. pose proof (R_free k) as Lfr. pose proof (R_free_null k) as Lfn.
    unfold KH in Lfr, Lfn.
    unfold asan_rt_hyps.
    (* [comment removed for export] *)
    split; [exact Lsr|]. split; [exact (inst_AKREL_laws (kip k))|]. split; [exact Lmp|].
    split; [exact (inst_alloc_ok_of_classes (kip k))|]. split; [exact (inst_cost_laws (kip k))|].
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
    split; [exact (inst_RHEAP_perm (kip k))|]. split; [exact (opdelA_of_free _ Lsr Lmp Lfr)|]. split; [exact (opdelA_null_of_free_null _ Lsr Lmp Lfn)|].
    split; [exact (inst_stack_malloc_0 (kip k))|]. split; [exact (inst_stack_malloc_2 (kip k))|]. split; [exact (inst_stack_malloc_3 (kip k))|].
    split; [exact inst_set_shadow_00|]. split; [exact inst_set_shadow_f8|].
    exact inst_memcmp_icpt.
  Qed.

  (* [comment removed for export] *)

  Lemma kit_vis : ltac2:(zQ "h10!kk6!hv2!ko3!ks0!jr8!ksa!lgc!lh5!lhf!li5!lic!oe!ln0!lr5!lrc!ls4!lsf>1k$b@3$0$2@3$7@1$4^1@1$5^1@1$3@1$9^1@5$e$d@1$a^1@2$h0@1$1#k0$c@1$8^1@1$f$6").
  Proof. intros k. exact (AS_InstMainK.vis_main_s0 (k_sp0 k) (k_brk0 k) (k_h k) (k_E k) (k_R k) (k_FULL k) [] false AL0). Qed.

  Lemma kit_rfs : ltac2:(zQ "60!ira!jr8!lta!lu4!lhf!oe>1k$5@3$2@1$1^1@1$0$3@1$4^1").
  Proof.
    intros k. exact (AS_InstMainK.rfs_main (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
                       (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Vfit k) (k_Hh k) (k_HC k) (KCEIL k) eq_refl).
  Qed.

  Lemma kit_heap : ltac2:(zQ "70!ira!jr8!ksa!lue!lva!lhf!oe>1k$6@4$3@1$1^1@1$2^1@1$0$4@1$5^1").
  Proof.
    intros k. exact (AS_InstMainHeap.rheap_main (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
                       (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Vfit k) (k_Hh k) (k_HC k) (KCEIL k) eq_refl [] false AL0 (kip k) eq_refl eq_refl).
  Qed.

  (* [comment removed for export] *)
  Lemma kit_budget : ltac2:(zQ "40!khb!mg3!mge!oe>1k$3@2$1@1$0^1@1$2^1").
  Proof.
    intros k.
    npose (BsMainIfaceAlloc.ak_budget (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
                  (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Hh k) (k_HC k)) as (B1 & B2 & B3 & B4).
    unfold ABUDGET, aPhi, Ks0, KX. cbn [a_AL a_S a_st cert_s0]. unfold cert_st0. rewrite AllocBudget.pusage_init. rewrite B2. unfold KX in B3. rewrite B4 in B3.
    unfold target_alloc_limit, page_size, AllocBudget.B_PRIM, AL0. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma kit_IK : ltac2:(zQ "60!mh8!ksa!hs5!hsc!mge!oe>1k$5@4$0@1$3^1@1$2^1@1$1^1@1$4^1").
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
      + apply (BsMainIfaceAlloc.ak_maps_in (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
                 (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Hh k) (k_HC k) (ps_b21 (KX k)) 0x100000); [cbn; tauto | lia].
      + apply (BsMainIfaceAlloc.ak_maps_in (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
                 (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Hh k) (k_HC k) (ps_b22 (KX k)) 0x800000); [cbn; tauto | lia].
    - (* [comment removed for export] *)
      intros x Hx. cbn [kip ip_D] in Hx. unfold kPageSize in Hx.
      apply (BsMainIfaceAlloc.ak_maps_in (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
               (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Hh k) (k_HC k) (ps_b12 (KX k)) 0x1000); [cbn; tauto | lia].
  Qed.

  Lemma kit_krel : ltac2:(zQ "50!jr8!ksa!mhc!li5!oe>1k$4@3$2@1$0^1@1$1^1@1$3^1").
  Proof.
    intros k. split.
    - (* [comment removed for export] *) exact (proj1 (BsMainLazy.lzok_open (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
                          (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Hh k) (k_HC k))).
    - exact (kit_IK k).
  Qed.

  Lemma kit_aux : ltac2:(zQ "c0!mi8!mie!hv2!jr8!mj5!lhf!hva!oe!mk4!mka!ik6!ihf>1k$7@2$1@3$4@1$3^1@1$5^1@1$0^1@2$1@2$8@2$b@1$2#k0@1$6^1@1$0^1@2$9@1$0^1@2$a+2+k0").
  Proof.
    intros k. pose proof (k_Vfit k) as F. unfold entry_stack_fits, entry_stack_span, sp_window_hi in F.
    pose proof (total_arg_bytes_nonneg (in_argv (k_inp k))). pose proof (total_arg_bytes_nonneg (in_envp (k_inp k))).
    pose proof (u64_range (k_sp0 k)).
    unfold KH, KB. cbn [as_rauxv_ok KHp]. unfold Irauxv_ok. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma kit_al : ltac2:(zQ "60!jr8!ksa!ml0!oe!mp8!mk4>1k$3@2$5@1$4@1$0^1@2$2@1$0^1@1$1^1").
  Proof.
    intros k. unfold KH, AMAIN_COST, fuzz_cost. cbn [as_Cm as_Cf as_AL KHp KS0 i_s a_AL Ks0 cert_s0]. unfold ICm, ICf, AL0.
    vm_compute. discriminate.
  Qed.

  Lemma kit_tr : ltac2:(zQ "30!jr8!mu5!oe>1k$2@1$1@1$0^1").
  Proof. intros k. exact (inst_adrv_traces (KH k) eq_refl (inst_fuzz_tr_ok (KH k) eq_refl)).   (* [comment removed for export] *) Qed.

  (* [comment removed for export] *)
  Theorem as_instance_kit : ltac2:(zQ "30!nj4!nk9!lr5@2$0$2$1").
  Proof.
    exact (instance_of_kit KH KS0 KB kit_rt (fun k => @inst_driver_laws (KCEIL k) (kip k)) (fun k => @inst_live (KCEIL k) (kip k))
             kit_vis kit_krel kit_rfs kit_heap kit_aux kit_al kit_tr).
  Qed.

  (* [comment removed for export] *)
End KIT.

(* [comment removed for export] *)
Check as_instance_kit.
