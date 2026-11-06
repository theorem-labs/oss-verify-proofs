(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AsConst AsIface AsDriverLaws AsSR AsChain FakeStackRep
     AllocWf AllocKit AllocRep AllocRepFacts AllocRepX SecLazy AsDepotInv AsDepotHash AG_Malloc2 AG_MallocLarge3 AG_MallocAll
     AS_InstDefs AS_InstTR N5_stack_malloc0 N5_stack_malloc1 N5_stack_malloc2 N5_stack_malloc3 N5_stack_malloc4
     N5_set_shadow_00 N5_set_shadow_f5 N5_set_shadow_f8 N6_iface N6_poison N6_memcmp.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "3h5LinuxProcessSemanticsfLinuxProcessSem5State05Model08m_vmmaps79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs9AllocRepX~~~~~~jf7akernel37Corelib4Init5Logico82eq06VmMaps79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AllocRep~~~~~~q93ast37Corelib7Numbers7BinNumsud4Npos09m_vm_lazyq96AMODEL35stdpp9bitvectorbdefinitionshi12bv37Corelib4Init9Datatypeshk44listhk44prod79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsbAS_InstDefs~~~~~~hmc2IKhmc3ist69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLazyRestrict~~~~~~hrah5same_but_materializedhmc3KHp79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsIface~~~~~~iha7SR_lawsihaaAKREL_lawsihaaMPRES_lawsihah3alloc_ok_of_classes46Stdlib6ZArith6BinInt1Zip62leud1Zhmc3ICmo83andip63addiha9cost_lawsihaelb_remove_lawsihabrauxv_frameiha9RFS_frameiha7RFS_extiha9RFS_rangeihacRFS_disjointiha9RFS_nodupiha9RFS_shvisihah1frame_release_lawihah3stack_malloc_1_stmtihah3stack_malloc_4_stmtihah2set_shadow_f5_stmtihah3stack_malloc_0_stmtihah3stack_malloc_2_stmtihah3stack_malloc_3_stmtihah2set_shadow_00_stmtihah2set_shadow_f8_stmtihah0asan_memcpy_stmtihah0asan_memset_stmtihah1asan_memmove_stmtihah0memcmp_icpt_stmtihaachain_lawshmc5ip_TR79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs9AS_InstTR~~~~~~ko86TRLISTiha7TR_laws79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BscAsDriverLaws~~~~~~ktc8ADRV_CNTktc9ADRV_LIVEihafas_LIVE_CNT_MAXihabas_LIVE_MAXktch0asan_driver_lawshmc7iparams" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Laws.
  Context {HCEIL : HeapCeil}.
  Variable p : ltac2:(zQ "10!lme$0").

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma akernel_vm_ext : ltac2:(zQ "60!ie!j5!ne!pc!q1!u7>1s$5>2mo$0>3mo'$0>0@3$3$4@1$1^1@1$1^2>0@3$2?5HCEIL^4^3@3$2?5HCEIL^5^3").
  Proof. intros s mo mo' E K. unfold akernel in *. rewrite E. exact K. Qed.

  Lemma AMODEL_vm_ext : ltac2:(zQ "b0!pc!hg6!ie!hgd!j5!hh8!hje!hlc!hm4!q1!u7>1s$a>2mo$2>3mo'$2>0@3$0$9@1$4^1@1$4^2>0@3$0@1$7@2$8@1$6@1$1#k0@1$6@1$1#k0@1$3^2@1$3^3>0@2$5^5^4@2$5^6^4").
  Proof.
    (intros s mo mo' E1 E2 nd_i1; ndestruct nd_i1 as (A & V & B)). split; [| split; [exact V|]].
    - unfold amaps_in_ledger in *. rewrite E1. exact A.
    - destruct B as [B0 B1]. split; [exact B0|]. unfold eager_used in *. rewrite E1, E2. exact B1.
  Qed.

  Lemma IK_vm_ext : ltac2:(zQ "b0!pc!hg6!ie!hgd!j5!hqd!hje!hlc!hm4!q1!hr3>1x@1$a?5HCEIL>2mo$2>3mo'$2>0@3$0$9@1$4^1@1$4^2>0@3$0@1$7@2$8@1$6@1$1#k0@1$6@1$1#k0@1$3^2@1$3^3>0@4$5?5HCEIL?1p^5^4@4$5?5HCEIL?1p^6^4").
  Proof.
    (intros x mo mo' E1 E2 nd_i2; ndestruct nd_i2 as ((A & K) & D & T)). split; [split|split].
    - exact (AMODEL_vm_ext _ _ _ E1 E2 A).
    - exact (akernel_vm_ext _ _ _ E1 K).
    - unfold depot_cov in *. rewrite E1. exact D.
    - unfold dtv_cov in *. rewrite E1. exact T.
  Qed.

  Lemma IK_mat : ltac2:(zQ "40!ie!hqd!hr3!hv9>1x@1$2?5HCEIL>2mo$0>3mo'$0>0@4$1?5HCEIL?1p^3^2>0@2$3^3^2@4$1?5HCEIL?1p^5^3").
  Proof.
    intros x mo mo' K SB. pose proof (same_but_materialized_fields _ _ SB) as (_ & E1 & E2 & _).
    exact (IK_vm_ext x mo mo' E1 E2 K).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma inst_SR_laws : ltac2:(zQ "20!ih3!il7@1$1@2$0?5HCEIL?1p").
  Proof. exact (ASR_SR_laws ist (fun x => a_L (i_s x)) (fun x => a_S (i_s x)) (fun x => a_Zr (i_s x)) (IK p) nonvm_same (IK_mat) nonvm_same_mat). Qed.

  Lemma inst_AKREL_laws : ltac2:(zQ "20!ih3!im2@1$1@2$0?5HCEIL?1p").
  Proof. exact (ASR_AKREL_laws ist (fun x => a_L (i_s x)) (fun x => a_S (i_s x)) (fun x => a_Zr (i_s x)) (IK p)). Qed.

  Lemma inst_MPRES_laws : ltac2:(zQ "20!ih3!in0@1$1@2$0?5HCEIL?1p").
  Proof. split; [exact nonvm_same_refl | exact nonvm_same_trans]. Qed.

  (* [comment removed for export] *)
  Lemma inst_alloc_ok_of_classes : ltac2:(zQ "20!ih3!ine@1$1@2$0?5HCEIL?1p").
  Proof. intros s LB m n _ Hn HCL HC HB. cbn. unfold Ialloc_ok. exact (conj Hn (conj HCL (conj HC HB))). Qed.

  Lemma ICm_nonneg : ltac2:(zQ "30!iqe!ir4!ir8>1n$1>0@2$0Z^1@2$0Z@1$2^2").
  Proof. intros n Hn. unfold ICm. destruct (Z.leb_spec n 64512); lia. Qed.
  Lemma ICm_mono : ltac2:(zQ "40!iqe!ir4!ir8!irf>1n$1>2n'$1>0@2$3@2$0Z^2@2$0^2^1@2$0@1$2^3@1$2^2").
  Proof. intros n n' Hn. unfold ICm. destruct (Z.leb_spec n 64512), (Z.leb_spec n' 64512); lia. Qed.
  Lemma ICm_super : ltac2:(zQ "40!ir8!iqe!ir4!is5>1a$2>1b$2>0@2$1Z^2>0@2$1Z^2@2$1@2$3@1$0^4@1$0^3@1$0@2$3^4^3").
  Proof. intros a b Ha Hb. unfold ICm. destruct (Z.leb_spec a 64512), (Z.leb_spec b 64512), (Z.leb_spec (a + b) 64512); lia. Qed.

  Lemma inst_cost_laws : ltac2:(zQ "20!ih3!isc@1$1@2$0?5HCEIL?1p").
  Proof.
    unfold cost_laws. cbn [as_Cm as_Cf KHp]. unfold ICf.
    split; [exact ICm_nonneg|]. split; [exact ICm_mono|]. split; [intros; lia|]. split; [intros; lia|].
    split; [exact ICm_super| intros; lia].
  Qed.

  Lemma inst_lb_remove_laws : ltac2:(zQ "20!ih3!it9@1$1@2$0?5HCEIL?1p").
  Proof.
    unfold lb_remove_laws. cbn [as_lb_remove KHp]. unfold Ilb_remove. split; [|split].
    - intros q A n LB NI. cbn. rewrite Z.eqb_refl. cbn.
      induction LB as [|b LB IH]; [reflexivity|]. cbn in *.
      destruct (Z.eqb_spec (blk_id b) q) as [E|NE]; [exfalso; apply NI; left; exact E|].
      destruct (decide False) as [f|nf]; [destruct f|].
      destruct (decide (negb (b.1.1 =? q))) as [y|ny].
      + f_equal. apply IH. intros IN. apply NI. right. exact IN.
      + exfalso. apply ny. unfold blk_id in NE. destruct (Z.eqb_spec (b.1.1) q); [congruence|]. exact I.
    - intros q b LB NE. cbn. destruct (decide (negb (blk_id b =? q))) as [y|ny]; [reflexivity|].
      exfalso. apply ny. destruct (Z.eqb_spec (blk_id b) q); [congruence|exact I].
    - intros q LB b IN. induction LB as [|c LB IH]; cbn in *; [exact IN|].
      destruct (decide _); [destruct IN as [E|IN2]; [left; exact E| right; apply IH; exact IN2] | right; apply IH; exact IN].
  Qed.

  Lemma inst_rauxv_frame : ltac2:(zQ "20!ih3!iub@2$1?5HCEIL@2$0?5HCEIL?1p").
  Proof. intros LB m m' B W R _ _ _. exact R. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Let RFS_is : forall LF m, as_RFS (KHp p) LF m <-> RFSI (as_FSB (KHp p)) LF m.
  Proof. intros LF m. apply iff_refl. Qed.

  Lemma inst_RFS_frame : ltac2:(zQ "20!ih3!iva@1$1@2$0?5HCEIL?1p").            Proof. exact (RFSI_frame (KHp p) RFS_is). Qed.
  Lemma inst_RFS_ext : ltac2:(zQ "20!ih3!jg7@1$1@2$0?5HCEIL?1p").                Proof. exact (RFSI_ext (KHp p) RFS_is). Qed.
  Lemma inst_RFS_range : ltac2:(zQ "20!ih3!jh2@2$1?5HCEIL@2$0?5HCEIL?1p").            Proof. exact (RFSI_range (KHp p) RFS_is). Qed.
  Lemma inst_RFS_disjoint : ltac2:(zQ "20!ih3!jhf@1$1@2$0?5HCEIL?1p").      Proof. exact (RFSI_disjoint (KHp p) RFS_is). Qed.
  Lemma inst_RFS_nodup : ltac2:(zQ "20!ih3!jif@1$1@2$0?5HCEIL?1p").            Proof. exact (RFSI_nodup (KHp p) RFS_is). Qed.
  Lemma inst_RFS_shvis : ltac2:(zQ "20!ih3!jjc@1$1@2$0?5HCEIL?1p").            Proof. exact (RFSI_shvis (KHp p) RFS_is). Qed.
  Lemma inst_frame_release : ltac2:(zQ "20!ih3!jk9@1$1@2$0?5HCEIL?1p"). Proof. exact (RFSI_release (KHp p) RFS_is). Qed.
  Lemma inst_stack_malloc_1 : ltac2:(zQ "20!ih3!jlf@2$1?5HCEIL@2$0?5HCEIL?1p"). Proof. exact (stack_malloc_1_ok (KHp p) RFS_is). Qed.
  Lemma inst_stack_malloc_4 : ltac2:(zQ "20!ih3!jn7@2$1?5HCEIL@2$0?5HCEIL?1p"). Proof. exact (stack_malloc_4_ok (KHp p) RFS_is). Qed.
  Lemma inst_set_shadow_f5 : ltac2:(zQ "10!jof$0").       Proof. exact set_shadow_f5_ok. Qed.
  (* [comment removed for export] *)
  Lemma inst_stack_malloc_0 : ltac2:(zQ "20!ih3!jq6@2$1?5HCEIL@2$0?5HCEIL?1p"). Proof. exact (stack_malloc_0_ok (KHp p) RFS_is). Qed.
  Lemma inst_stack_malloc_2 : ltac2:(zQ "20!ih3!jre@2$1?5HCEIL@2$0?5HCEIL?1p"). Proof. exact (stack_malloc_2_ok (KHp p) RFS_is). Qed.
  Lemma inst_stack_malloc_3 : ltac2:(zQ "20!ih3!jt6@2$1?5HCEIL@2$0?5HCEIL?1p"). Proof. exact (stack_malloc_3_ok (KHp p) RFS_is). Qed.
  Lemma inst_set_shadow_00 : ltac2:(zQ "10!jue$0").       Proof. exact set_shadow_00_ok. Qed.
  Lemma inst_set_shadow_f8 : ltac2:(zQ "10!kg5$0").       Proof. exact set_shadow_f8_ok. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma inst_asan_memcpy : ltac2:(zQ "10!khc@1$0?5HCEIL").   Proof. exact asan_memcpy_ok. Qed.
  Lemma inst_asan_memset : ltac2:(zQ "10!kj1@1$0?5HCEIL").   Proof. exact asan_memset_ok. Qed.
  Lemma inst_asan_memmove : ltac2:(zQ "10!kk6@1$0?5HCEIL"). Proof. exact asan_memmove_ok. Qed.
  (* [comment removed for export] *)
  Lemma inst_memcmp_icpt : ltac2:(zQ "10!klc@1$0?5HCEIL").   Proof. exact memcmp_icpt_spec. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma inst_chain_laws : ltac2:(zQ "20!ih3!kn1@2$1?5HCEIL@2$0?5HCEIL?1p").
  Proof. apply achain_laws. intros m cur CH. apply iff_refl. Qed.

  Lemma inst_TR_laws1 : ltac2:(zQ "70!hlc!pc!ir4!ih3!knf!ks7!kt1>0@3$1@1$0@1$0$2@1$4?1p$5@1$6@2$3?5HCEIL?1p").
  Proof. intros E. exact (inst_TR_laws (KHp p) E). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma inst_live : ltac2:(zQ "70!ih3!iqe!irf!lhe!lia!lj7!lka@2$2@2$1$4@1$6@2$0?5HCEIL?1p@2$1$3@1$5@2$0?5HCEIL?1p").
  Proof. cbn [as_LIVE_MAX as_LIVE_CNT_MAX KHp]. unfold ILIVE_MAX, ILIVE_CNT_MAX. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma inst_driver_laws : ltac2:(zQ "20!ih3!ll9@1$1@2$0?5HCEIL?1p").
  Proof.
    constructor.
    - (* [comment removed for export] *) intros Q c T SRQ K. exact (ASR_realizes Q c T SRQ K).
    - (* [comment removed for export] *) intros s. nexists (a_L (i_s s)), (a_S (i_s s)), (a_Zr (i_s s)). split; [|split].
      + intros msF. reflexivity.
      + intros c [LZ _]. exact LZ.
      + intros ms mo ms' mo' [_ K] LZ E1 E2. split; [exact LZ|]. cbn [cfg_model] in *. exact (IK_vm_ext s mo mo' E1 E2 K).
    - (* [comment removed for export] *) (intros mo mo' nd_i3; ndestruct nd_i3 as (Efd & _ & Efs & Epr & _)). unfold m_fs, m_fds, m_halted. rewrite Efd, Efs, Epr. repeat split; reflexivity.
    - (* [comment removed for export] *) intros mo mo' SB. exact (nonvm_same_mat mo mo' SB).
    - (* [comment removed for export] *) exact inst_live.
  Qed.
End Laws.
(* [comment removed for export] *)
