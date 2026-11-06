(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.boost_beast.http_request.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AsanAllocModel SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface AsDriverLaws AsSR AsChain FakeStackRep.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AllocWf AllocKit.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AllocRep AllocRepFacts AllocRepX SecLazy AsDepotInv AsDepotHash AG_Malloc2 AG_MallocLarge3 AG_MallocAll AS_InstDefs AS_InstTR AsTRList AsIface5 AsIface6 AsIface7 N5_stack_malloc0 N5_stack_malloc1 N5_stack_malloc2 N5_stack_malloc3 N5_stack_malloc4 N5_stack_malloc7 N5_stack_free7 N5_set_shadow_f5 N5_set_shadow_00 N5_set_shadow_f8 N6_iface N6_poison N6_annotate N6_strcmp2 N6_bcmp N6_strtoll AXL_snprintf.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Laws.
  Context {HCEIL : HeapCeil}.
  Variable p : iparams.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma akernel_vm_ext : forall (s : ast) mo mo',
    m_vmmaps mo' = m_vmmaps mo -> akernel s mo -> akernel s mo'.
  Proof. intros s mo mo' E K. unfold akernel in *. rewrite E. exact K. Qed.

  Lemma AMODEL_vm_ext : forall (s : ast) mo mo',
    m_vmmaps mo' = m_vmmaps mo -> m_vm_lazy mo' = m_vm_lazy mo -> AMODEL s mo -> AMODEL s mo'.
  Proof.
    intros s mo mo' E1 E2 (A & V & B). split; [| split; [exact V|]].
    - unfold amaps_in_ledger in *. rewrite E1. exact A.
    - destruct B as [B0 B1]. split; [exact B0|]. unfold eager_used in *. rewrite E1, E2. exact B1.
  Qed.

  Lemma IK_vm_ext : forall (x : ist) mo mo',
    m_vmmaps mo' = m_vmmaps mo -> m_vm_lazy mo' = m_vm_lazy mo -> IK p x mo -> IK p x mo'.
  Proof.
    intros x mo mo' E1 E2 ((A & K) & D & T). split; [split|split].
    - exact (AMODEL_vm_ext _ _ _ E1 E2 A).
    - exact (akernel_vm_ext _ _ _ E1 K).
    - unfold depot_cov in *. rewrite E1. exact D.
    - unfold dtv_cov in *. rewrite E1. exact T.
  Qed.

  Lemma IK_mat : forall (x : ist) mo mo', IK p x mo -> same_but_materialized mo mo' -> IK p x mo'.
  Proof.
    intros x mo mo' K SB. pose proof (same_but_materialized_fields _ _ SB) as (_ & E1 & E2 & _).
    exact (IK_vm_ext x mo mo' E1 E2 K).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma inst_SR_laws : SR_laws (KHp p).
  Proof. exact (ASR_SR_laws ist (fun x => a_L (i_s x)) (fun x => a_S (i_s x)) (fun x => a_Zr (i_s x)) (IK p) nonvm_same (IK_mat) nonvm_same_mat). Qed.

  Lemma inst_AKREL_laws : AKREL_laws (KHp p).
  Proof. exact (ASR_AKREL_laws ist (fun x => a_L (i_s x)) (fun x => a_S (i_s x)) (fun x => a_Zr (i_s x)) (IK p)). Qed.

  Lemma inst_MPRES_laws : MPRES_laws (KHp p).
  Proof. split; [exact nonvm_same_refl | exact nonvm_same_trans]. Qed.

  Lemma inst_alloc_ok_of_live : alloc_ok_of_live (KHp p).
  Proof. intros s LB m n _ Hn HB HC. cbn in *. unfold Ialloc_ok, ILIVE_MAX, ILIVE_CNT_MAX in *. lia. Qed.

  Lemma ICm_nonneg : forall n, 0 <= n -> 0 <= ICm n.
  Proof. intros n Hn. unfold ICm. destruct (Z.leb_spec n 64512); lia. Qed.
  Lemma ICm_mono : forall n n', 0 <= n <= n' -> ICm n <= ICm n'.
  Proof. intros n n' Hn. unfold ICm. destruct (Z.leb_spec n 64512), (Z.leb_spec n' 64512); lia. Qed.
  Lemma ICm_super : forall a b, 0 <= a -> 0 <= b -> ICm a + ICm b <= ICm (a + b).
  Proof. intros a b Ha Hb. unfold ICm. destruct (Z.leb_spec a 64512), (Z.leb_spec b 64512), (Z.leb_spec (a + b) 64512); lia. Qed.

  Lemma inst_cost_laws : cost_laws (KHp p).
  Proof.
    unfold cost_laws. cbn [as_Cm as_Cf KHp]. unfold ICf.
    split; [exact ICm_nonneg|]. split; [exact ICm_mono|]. split; [intros; lia|]. split; [intros; lia|].
    split; [exact ICm_super| intros; lia].
  Qed.

  Lemma inst_lb_remove_laws : lb_remove_laws (KHp p).
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

  Lemma inst_rauxv_frame : rauxv_frame (KHp p).
  Proof. intros LB m m' B W R _ _ _. exact R. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Let RFS_is : forall LF m, as_RFS (KHp p) LF m <-> RFSI (as_FSB (KHp p)) LF m.
  Proof. intros LF m. apply iff_refl. Qed.

  Lemma inst_RFS_frame : RFS_frame (KHp p).            Proof. exact (RFSI_frame (KHp p) RFS_is). Qed.
  Lemma inst_RFS_ext : RFS_ext (KHp p).                Proof. exact (RFSI_ext (KHp p) RFS_is). Qed.
  Lemma inst_RFS_range : RFS_range (KHp p).            Proof. exact (RFSI_range (KHp p) RFS_is). Qed.
  Lemma inst_RFS_disjoint : RFS_disjoint (KHp p).      Proof. exact (RFSI_disjoint (KHp p) RFS_is). Qed.
  Lemma inst_RFS_nodup : RFS_nodup (KHp p).            Proof. exact (RFSI_nodup (KHp p) RFS_is). Qed.
  Lemma inst_RFS_shvis : RFS_shvis (KHp p).            Proof. exact (RFSI_shvis (KHp p) RFS_is). Qed.
  Lemma inst_frame_release : frame_release_law (KHp p). Proof. exact (RFSI_release (KHp p) RFS_is). Qed.
  Lemma inst_stack_malloc_1 : stack_malloc_1_stmt (KHp p). Proof. ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.N5_stack_malloc1.stack_malloc_1_ok); constr:(HCEIL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AS_InstDefs.KHp); constr:(p); constr:(RFS_is)|] Array.empty "##%###(#'#(#)#&#*#VDCEWFC#G#"). Qed.
  Lemma inst_stack_malloc_4 : stack_malloc_4_stmt (KHp p). Proof. exact (stack_malloc_4_ok (KHp p) RFS_is). Qed.
  Lemma inst_set_shadow_f5 : set_shadow_f5_stmt.       Proof. exact set_shadow_f5_ok. Qed.
  (* [comment removed for export] *)
  Lemma inst_rt_hyps5 : asan_rt_hyps5 (KHp p).
  Proof.
    unfold asan_rt_hyps5.
    split; [exact (stack_malloc_0_ok (KHp p) RFS_is)|]. split; [exact (stack_malloc_2_ok (KHp p) RFS_is)|].
    split; [exact (stack_malloc_3_ok (KHp p) RFS_is)|]. split; [exact set_shadow_00_ok | exact set_shadow_f8_ok].
  Qed.
  Lemma inst_rt_hyps5x : asan_rt_hyps5x (KHp p).
  Proof. unfold asan_rt_hyps5x. split; [exact (stack_malloc_7_ok (KHp p) RFS_is) | exact (stack_free_7_ok (KHp p) RFS_is)]. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma inst_asan_memcpy : asan_memcpy_stmt.   Proof. exact asan_memcpy_ok. Qed.
  Lemma inst_asan_memset : asan_memset_stmt.   Proof. exact asan_memset_ok. Qed.
  Lemma inst_asan_memmove : asan_memmove_stmt. Proof. exact asan_memmove_ok. Qed.
  Lemma inst_memcpy_icpt : memcpy_icpt_stmt.   Proof. exact memcpy_icpt_ok. Qed.
  Lemma inst_memmove_icpt : memmove_icpt_stmt. Proof. exact memmove_icpt_ok. Qed.
  Lemma inst_strlen_icpt : strlen_icpt_stmt.   Proof. exact strlen_icpt_ok. Qed.
  (* [comment removed for export] *)
  Lemma inst_rt_hyps6 : asan_rt_hyps6.
  Proof. unfold asan_rt_hyps6. split; [exact strcmp_icpt_ok|]. split; [exact memcmp_icpt_ok | exact bcmp_icpt_ok]. Qed.
  Lemma inst_rt_hyps6b : asan_rt_hyps6b.
  Proof. unfold asan_rt_hyps6b. split; [exact snprintf_d_m1_ok|]. split; [exact strtoll_m1_ok | exact strtoll_one_ok]. Qed.
  Lemma inst_strtoll : strtoll_m1_stmt /\ strtoll_one_stmt.
  Proof. split; [exact strtoll_m1_ok | exact strtoll_one_ok]. Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.or Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Logic.and Sort Prop.
  (* [comment removed for export] *)
  Lemma inst_annotate_cc : annotate_cc_stmt.
  Proof.
    ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@LinuxProcessSemantics.Riscv.Prelude.bvmap); constr:(@Corelib.Numbers.BinNums.xI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.mem); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.eq); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.aapp); constr:(HCEIL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.AAPP_HI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.SHAD); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.cc_shadow); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.stk); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.bsegs); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.aceil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.AINTRIN_STACK); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.mem_inv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.ACONST); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.in_app_mem); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Exec.evt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.annotate_post); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.MState.MS); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.mkR); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.AANNOTATE_CC); constr:(@Corelib.Init.Datatypes.None); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.PropExec.seg_rom); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.N6_annotate.annotate_body); constr:(@Corelib.Init.Logic.conj); constr:(@kc__1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.aapp_lo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.aapp_hi); constr:(@Corelib.Init.Logic.or); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.AHI_LO); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.AIMG_TOP); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.ALOWSH_LO); constr:(@kc__2); constr:(@Corelib.Init.Logic.or_intror); constr:(@Corelib.Init.Logic.or_introl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.N6_poison.app_rng); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.ACONST_cell); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.N6_poison.ACF_CLRTHR_CELL); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cell); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C8); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Init.Datatypes.pair); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AGOT_SHBASE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.TacX.wz); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.ASHBASE_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AGOT_UAR); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AUAR_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AGOT_MEMSETP); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AMEMSETP_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AGOT_FLAGS); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AGOT_CFLAGS); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AGOT_HIEND); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AHIEND_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AGOT_MIDBEG); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AMIDBEG_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AGOT_MIDEND); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AMIDEND_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AGOT_SEALED); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AGOT_DYING); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.ADYING_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AGOT_PGSZ); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.APGSZ_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AGOT_RINTRIN); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.ARINTRIN_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AGOT_FSTLS); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.ASHADOW_BASE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C4); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AREAL_MEMSET); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AINITED_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.TacX.b8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.ACANPOISON_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AMEMCPYP_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AREAL_MEMCPY); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.ASTRLENP_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AREAL_STRLEN); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.ACF_ISTRCMP_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AF_REPSTR_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AREAL_STRTOLL_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AREAL_VSNPRINTF_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AGOT_SSP_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.ASHW_STR_ONE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.ASHW_STR_PCTD); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.ACF_IMEMCMP_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AREAL_MEMCMP_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.ACF_ISTRLEN_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.ACF_STRICT_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AF_DCO_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AGOT_VERBOSITY); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AVERBOSITY_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.ACF_CSMT_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AGOT_DTLS); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AREAL_TLSGA_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AREAL_TLSGA); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.ACF_ITLS_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.ATSD_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AMUSL_TSD); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AMUSL_DTV); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AMUSL_DTV1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AMEMCHRP_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AREAL_MEMCHR); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AREADP_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AREAL_READ); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AFWRITEP_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AREAL_FWRITE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AVPRINTFP_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AREAL_VPRINTF); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AVFPRINTFP_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AREAL_VFPRINTF); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.ASTRNLENP_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AREAL_STRNLEN); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.ACF_CHKPRINTF_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AF_REPGLOB_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AMU_GLOBALS_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.AREGISTERED_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.ACOVFLAG_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.ASHW_FMTD); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.ASHW_MSG_USAGE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.ASHW_MSG_REFUSED); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.ASHW_MSG_OPEN); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.ASHW_MSG_SHORT); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.ASHW_STDOUTBUF); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.Lists.List.In); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsConst.aconst_cells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.N6_annotate.ADCO_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.N6_annotate.AGOT_VERB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.N6_annotate.AVERB_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.annotate_cc_stmt)|] [|@a0; @a1; @a2; @a3; @P2; @P1; @H; @IAM; @AC; @MI; @LO; @CEIL; @ST; @SH; @HI; @AP; @MN; @MO; @N8; @O8; @LEN; @L8; @B8; @lo; @newmid; @oldmid; @len; @beg; @m; @fc; @F; @t6; @t5; @t4; @t3; @s11; @s10; @s9; @s8; @s7; @s6; @s5; @s4; @s3; @s2; @a7; @a6; @a5; @a4; @s1; @s0; @t2; @t1; @t0; @tp; @gp; @sp; @ra|] "#75#_%;#i$=#;#A#<#p#=#:#>###@#{#?#2#V#$#3#W#]#\#[#L#K#J#I#H#G#F#E#D#9%:#1#u#Y#M#8#Z#X#C#/#4#P#O#N#B#0#v#^#.$3$4$5#(#,#-#5#Q%7#e#'#6#7#R%=#U#b#)#s#t#x#w#z#~$#$$$%$'#S#+$0$1$6$E$G$I$M$T$V$_$r$x$;%;%<#f#}#T$*$+$,$/$9$?$A$@$C$F$H$J$K$L$O$N$Q$P$R$S$U$X$W$Y$Z$\$]$`$b$a$d$c$e$f$g$h$i$j$k$l$m$n$o$p$q$s$t$v$u$w$y$z${$}$|%#$~%%%$%'%&%)%(%+%*%,%-%.%/%0%1%2%3%4%5%6$-#&#%#h%>#j$2#g#d$7$B$<#r$>$D#o#q#k#m%9#n$.#y$)$($&$8#c#|%8$:#l$[$^@$z&${%$|$$}$$~&%#'%$&%%%%&$%'$%($%)%%*%%+%%,&%-%%.'%/%%0B%1*%2&%3&%4$%5%%6%%7(%8)%9$%:$&SN&#&#&#&#&#9#USU#%*9#VSr#%9)USU#/)SO#)M#/+SH0SVSH/-##-F##.F&-42SI##C#H*HSJ-:-8VSW$#*SJ#.'#2SJ+#C#H*S3S;0S3SA*S;#.%#*PS;0PS3*S;#.%#WSXS4S#P0S<S#*#SB4S#SKVSYS<#WSZSPSK#:s#)S$XS[NSQP#USsS4*#S#:s#-S54#S\*S<#VS]NJUS^E0EJVS_E#i#:S`SCS%S&S'S$QS6S(S)S*S+S,S-S.S/S0OKGES1S7I5SCS%S&S'S8S5S9S$QSPStSaSRSLS=S>S?S6S(S)S*S+S,S-S.S/S0S:S@FM/s#6SuUSvs#6USwN6&O%K$I#7N(#k##*#k##-#k##/#k##1#k##5#k##8#k##;#k##?#k##B#k##s#$#k##s#)#k##s#.#k##s#/#k##s#2#k##s#9#k##s#:#k##s#>#k##s#?#k##s#A#j#$s#M#0SHSO/s#P##s#PM#/s#RG5SCS%S&S'S8S5S9S$Q#SKSaSRSLS=S>S?S6S(S)S*S+S,S-S.S/S0S:S@FM6#O@K?I>7Ns###k##s#%#k##s#(#k##s#*#k##s#,#k##s#0#k##s#3#k##s#6#k##s#:#k##s#=#k##s#?#k##s#D#k##s#I#k##s#J#k##s#M#k##s#T#k##s#U#k##s#Y#k##s#Z#j#%s#g#0GE/s#j#5SCS%S&S'S8S5S9S$Q;#S<SRSLS=S>S?S6S(S)S*S+S,S-S.S/S0S:S@FM6#Os#8Ks#7Is#67Ns#;#k##s#=#k##s#@#k##s#B#k##s#D#k##s#H#k##s#K#k##s#N#k##s#R#k##s#U#k##s#W#k##s#\#k##s#a#k##s#b#k##s#e#k##s#l#k##s#m#k##s#q#j#&s#~#/s$$J5SCS%S&S'S8S5S9S$Qs#19#S#SLS=S>S?S6S(S)S*S+S,S-S.S/S0S:S@FM6#Os#NKs#MIs#L7Ns#Q#k##s#S#k##s#V#k##s#X#k##s#Z#k##s#^#k##s#a#k##s#d#k##s#h#k##s#k#k##s#m#k##s#r#k##s#w#k##s#x#k##s#{#k##s$&#k##s$'#j#'s$7#2Sbs$+#C#H*HSI*SIs$(.$#*SASD0SAS;*SD#.%#*S3SD*SDs$).$#WSXS4PS30S#P*#SB4PS<VSYS##WSZSKS<#:s$KQXS[NSPS3#*s$$P:s$NS94#S\*S##VS]NS1US^J0JS1VS_J#2Es$G#C#H2Js$I#C#H2S1s$K#C#H2S7s$M#C#H.%#.(#3'%S;SD3*%S3#3-%P#*ES1*S1s$3.$#*ES7*S7s$6.$#3&#SJSIVScEJWSdS4EJ$$#*SEG*s#bSB.$#*SFG*s#eSG.$#$&#j##*#VScGE*SFI0IG*#SG.%#*SEK0KI*#SB.%#*SFK*&SG.$#$&#j##+#*SFO0MO*#SG*SEF0FM*#SB.%#*SFF*&SG.$#3%$RL''$#j#(,#j#)/#V#RLj##5#j##?#YSe@>4#Lj#*B#U#Lj##s#/#WSdS4GE*SEI*s#%s$p.$#j###=*s#$s$s*SEO*=s$u3<:RSA8:7#j#(%#j#)'#V#RLj##*#j##/#YSe0/-#Lj#*2#U#Lj##s#A#ZSxs#Cs#Bs#96#SbVSyEs${m#$#%SN%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#-#/s&5#+#USzD)D$#US{DVS|C#,Sf+#)D#((C'S}#&s#L%#%#%#%#%#%#&#%#&#%#&#&#%#&#&#&#&#&#-#%SN&#%#%#%#%#%#%#&#&#%#%#&#%#%#&#&#&#&#&#-#&SN&#%#&#%#&#%#&#%#%#%#%#%#&#%#%#%#&#&#&#-#&B%#%#%#&#%#&#&#&#-#&@%#&#&#&#&#%#%#%#%#&#%#&#%#&#&#&#&#-#&5%#%#%#%#&#%#%#%#&#%#%#&#%#%#&#&#-#&s#Y&#&#&#&#&#%#%#&#&#&#&#&#%#%#&#&#&#&#-#%s#7%#&#%#&#%#&#&#&#&#%#&#&#-#&.%#%#&#%#%#&#%#&#&#-#%s#+&#%#&#%#%#%#&#&#%#%#&#&#&#-#&s$:%#%#&#&#&#&#%#%#&#&#&#&#&#&#%#%#&#&#&#-#%/%#%#%#%#%#%#&#&#&#&#-#%s$A&#&#&#&#&#&#&#%#%#&#&#&#-#&s$e%#&#&#%#&#&#%#&#%#%#&#&#&#-#%s$D%#%#%#&#%#%#&#%#%#&#%#%#&#&#&#-#(Cs%Hs$vs%I#s%Hs%D#,Sg+#)D#s%N(Cs%MS~##s%M#(,Sh+#)D#s%S(Cs%RT###s%R#-%s)4&#%#&#%#%#&#&#&#%#&#%#%#%#%#&#&#&#-#,s%$+#)D#s%k(Cs%jT$##s%j#s#%&s%]%#&#%#&#%#&#&#&#-#,s%)+#)D#s%z(Cs%yT%##s%y#s#4,Si+#)D#s&#(Cs%~T&##s%~#s#9,T'+#)D#s&((Cs&'T(##s&'#s#>,T)+#)D#s&-(Cs&,T*##s&,#s#C-SN,#+#)D#s&3(Cs&2T+##s&2#s#I,Sj+#)D#s&8(Cs&7T,##s&7#s#N,Sk+#)D#s&=(Cs&<T-##s&<#s#S,T.+#)D#s&B(Cs&AT/##s&A#s#X&s&T&#&#&#&#&#&#&#&#&#&#-#,#+#)D#s&S)Ds#$#(Cs&ST0##s&S#s#j,T1+#)D#s&Y(Cs&XSf##s&X#s#o>s#-)D#s&](Cs&\Sg##s&\#s#s,T2+#)D#s&b(Cs&aSh##s&a#s#xUSls#7?#)D#s&g)D$#(Cs&gT3##s&g#s#~%s*B%#%#-#VSWs*6#4#s#B,#+#,H+#)D#s&u)D$#)D'#(Cs&vSi##s&v#s$1>))D#s&{(Cs&zSj##s&z#s$5&s*X&#&#&#&#&#-#,#+#)D#s'+(Cs'*Sk##s'*#s$A(Cs',T4s#%#s',#s$C,T5+#)D#s'2(Cs'1T6##s'1#s$H,T7+#)D#s'7(Cs'6T8##s'6#s$M(Cs'8T9s#1#s'8#s$O(Cs':T:s#3#s':#s$Q%s*w&#&#&#%#&#&#&#&#%#%#&#%#%#%#&#&#-#,s&J+#)D#s'R(Cs'QT;##s'Q#s$h%s+1%#%#%#%#&#&#&#%#%#%#%#%#&#&#&#-#,s&N+#)D#s'h(Cs'gT<##s'g#s$~&s'c%#%#&#&#&#&#%#%#&#%#&#&#%#%#%#&#&#&#&#-#,s&T+#)D#s(&(Cs(%T=##s(%#s%<&s(h&#%#%#%#%#%#%#&#&#%#%#%#%#%#%#&#&#%#&#&#&#&#&#&#%#&#%#%#%#%#%#&#&#%#%#%#%#%#%#&#&#%#%#%#%#%#%#&#&#%#%#%#%#%#%#&#&#%#-#,#+#)D#s(g(Cs(fT>##s(f#s%}%s#*%#%#%#%#%#&#&#%#%#%#%#%#%#&#&#%#%#%#%#%#%#&#&#%#&#&#&#&#&#&#%#%#-#,#+#)D#s)2(Cs)1T?##s)1#s&H(Cs)3T@s%+#s)3#s&J%s$S%#&#&#&#&#&#%#&#&#&#&#-#,s'f+#&1%#%#&#%#&#&#&#&#&#&#-#,s'i+#)D#s)T)D2#(Cs)TTA##s)T#s&k(Cs)VTBs%O#s)V#s&mUSlH?#)D#s)\(Cs)[TC##s)[#s&r(Cs)]TDs%V#s)]#s&t,Sm+#)D#s)c(Cs)bTE##s)b#s&y(Cs)dSms%I#s)d#s&{,s)k+#)D#s)j(Cs)iTF##s)i#s'$,s-8+#)D#s)o(Cs)nTG##s)n#s'),TH+#)D#s)t(Cs)sTI##s)s#s'.(Cs)uTJs%n#s)u#s'0(Cs)wSns%p#s)w#s'2-s-Y0Sn#(Cs){#s%`#s){#s'6%s$m&#%#%#&#%#%#%#&#%#%#&#&#&#-#,s(:+#)D#s*4(Cs*3TK##s*3#s'J&s$z&#%#&#&#&#&#-#,s(2+#)D#s*A(Cs*@TL##s*@#s'W&B&#&#%#%#%#%#&#%#&#&#&#-#,s(8+#)D#s*S(Cs*RTM##s*R#s'i,TN+#)D#s*X(Cs*WTO##s*W#s'n,TP+#)D#s*](Cs*\TQ##s*\#s's,TR+#)D#s*b(Cs*aTS##s*a#s'x,TT+#)D#s*g(Cs*fTU##s*f#s'},TV+#)D#s*l(Cs*kTW##s*k#s(&,TX+#)D#s*q(Cs*pTY##s*p#s(+(Cs*rTZs&k#s*r#s(-(Cs*tT[s&w#s*t#s(/(Cs*vT\s&a#s*v#s(1(Cs*xT]s'I#s*x#s(3(Cs*zT^s#~#s*z#s(5(Cs*|T_s&f#s*|#s(7(Cs*~T`s&h#s*~#s(9(Cs+$Tas&j#s+$#s(;(Cs+&Tbs&l#s+&#s(=(Cs+(Tcs&n#s+(#s(?(Cs+*Tds&q#s+*#s(A$#SM$&#$)#$,#$/#$2#$5#$8#$;#$>#$A#$s#$#$s#*#$s#0#$s#6#$s#<#$s#B#$s#H#$s#[#$s#i#$s#~#$s$'#$s$*#$s$-#$s$3#$s$9#$s$?#$s$B#$s$H#$s$K#$s$Q#$s$T#$s$v#$s$y#$s%E#$s&+#$s&F#$s&]#$s&u#$s&x#$s&{#$s'%#$s'+#$s'.#$s';#$s'@#$s'P#$s'W#$s']#$s'b#$s'h#$s'{#$s(%#$s(+#$s(1#$s(8#$s(>#$s(D#$s(J#$s(Z#$s(s#$s(y#;s+is)$8s$_s#)#'s$es#)#'s$hs#)#'s$ns#)#'s$qs#)#'s$ws#)#'s$zs#)#'s%@s#)#'s%Cs#)#'s%ks#)#'s&Qs#)#'s&ls#)#'s''s#)#'s'?s#)#'s'Bs#)#'s'Es#)#'s'Ks#)#'s'Qs#)#'s'Ts#)#'s'as#)#'s'fs#)#'s'vs#)#'s'}s#)#'s('s#)#'s(,s#)#'s(2s#)#'s(Es#)#'s(Ks#)#'s(Qs#)#'s(Ws#)#'s(^s#)#'s(ds#)#'s(js#)#'s(ps#)#'s)$s#)#'s)=s#)#'s)Cs#)#'s)Is#)#1s,4s)KS2m#$#(Cs,7Sos,81s,7#S2m#%#<GSos,;R#9s/v/#s(l?#)D#s,@%s)@%#&#%#%#&#&#&#-#(Cs,Hs*#,#s,Hs,D##s,Is)[$#s,Js)W%#s,Ks)@&#s,Ls)2'#s,Ms).(#s,Ns)*)#s,Os)&*#s,Ps(}+#s,Qs(y,#s,Rs(u-#s,Ss(q.#s,Ts(`/#s,Us(\0#s,Vs(Y1#s,Ws(U2#s,Xs(P3#s,Ys(B4#s,Zs(?5#s,[s(46#s,\s(37#s,]s(/8#s,^s(+9#s,_s(*:#s,`s();#s,as'o<#s,bs'Z=#s,cs'A>#s,ds&]?#s,es&7@#s,fs&6A#s,gs%rB#s,hs%qs###s,is%ms#$#s,js%ls#%#s,ks%hs#&#s,ls%gs#'#s,ms%cs#(#s,ns%_s#)#s,os%[s#*#s,ps%Zs#+#s,qs%Ys#,#s,rs%Vs#-#s,ss%Cs#.#s,ts%7s#/#s,us%&s#0#s,vs$~s#1#s,ws$zs#2#s,xs$vs#3#s,ys$rs#4#s,zs$ns#5#s,{s$js#6#s,|s$is#7#s,}s$hs#8#s,~s$gs#9#s-#s$fs#:#s-$s$es#;#s-%s$ds#<#s-&s$cs#=#s-'s$bs#>#s-(s$as#?#s-)s$`s#@#s-*s$_s#A$#SM$%#$'#$)#$+#$-#$/#$1#$3#$5#$7#$9#$;#$=#$?#$A#$s###$s#%#$s#'#$s#)#$s#+#$s#-#$s#/#$s#1#$s#3#$s#5#$s#7#$s#9#$s#;#$s#=#$s#?#$s#A#$s#C#$s#E#$s#G#$s#I#$s#K#$s#M#$s#O#$s#Q#$s#S#$s#U#$s#W#$s#Y#$s#[#$s#]#$s#_#$s#a#$s#c#$s#e#$s#g#$s#i#$s#k#$s#m#$s#o#$s#q#$s#s#$s#u#$s#w#$s#y#$s#{#$s#}#;s-is$$8s#^s#&#'s#`s#&#'s#bs#&#'s#ds#&#'s#fs#&#'s#hs#&#'s#js#&#'s#ls#&#'s#ns#&#'s#ps#&#'s#rs#&#'s#ts#&#'s#vs#&#'s#xs#&#'s#zs#&#'s#|s#&#'s#~s#&#'s$$s#&#'s$&s#&#'s$(s#&#'s$*s#&#'s$,s#&#'s$.s#&#'s$0s#&#'s$2s#&#'s$4s#&#'s$6s#&#'s$8s#&#'s$:s#&#'s$<s#&#'s$>s#&#'s$@s#&#'s$Bs#&#'s$Ds#&#'s$Fs#&#1s.1s$HS2m#$#(Cs.4Sps$T1s.4#S2m#%#<GSps$WR#/s1oSS+#)D#s.<%s)]%#%#%#%#&#&#&#&#%#%#%#%#&#&#&#-#&s.B%#&#%#&#&#&#&#&#%#%#&#&#&#-#/s26s,'+#)D#s._(Cs.^s+u##s.^s.Z##s._s+q$#s.`s+m%#s.as+V&#s.bs+H'#s.cs+D(#s.ds+@)#s.es+<*#s.fs+7+#s.gs+3,#s.hs+/-#s.is++.#s.js*v/#s.ks*r0#s.ls*o1#s.ms*k2#s.ns*f3#s.os*X4#s.ps*U5#s.qs*J6#s.rs*I7#s.ss*E8#s.ts*A9#s.us*@:#s.vs*?;#s.ws*)<#s.xs)p=#s.ys)W>#s.zs(s?#s.{s(M@#s.|s(LA#s.}s(,B#s.~s(+s###s/#s('s#$#s/$s(&s#%#s/%s'~s#&#s/&s'}s#'#s/'s'ys#(#s/(s'us#)#s/)s'qs#*#s/*s'ps#+#s/+s'os#,#s/,s'ls#-#s/-s'Ys#.#s/.s'Ms#/#s//s'<s#0#s/0s'8s#1#s/1s'4s#2#s/2s'0s#3#s/3s',s#4#s/4s'(s#5#s/5s'$s#6#s/6s'#s#7#s/7s&~s#8#s/8s&}s#9#s/9s&|s#:#s/:s&{s#;#s/;s&zs#<#s/<s&ys#=#s/=s&xs#>#s/>s&ws#?#s/?s&vs#@#s/@s&us#A$#SM$%#$'#$)#$+#$-#$/#$1#$3#$5#$7#$9#$;#$=#$?#$A#$s###$s#%#$s#'#$s#)#$s#+#$s#-#$s#/#$s#1#$s#3#$s#5#$s#7#$s#9#$s#;#$s#=#$s#?#$s#A#$s#C#$s#E#$s#G#$s#I#$s#K#$s#M#$s#O#$s#Q#$s#S#$s#U#$s#W#$s#Y#$s#[#$s#]#$s#_#$s#a#$s#c#$s#e#$s#g#$s#i#$s#k#$s#m#$s#o#$s#q#$s#s#$s#u#$s#w#$s#y#$s#{#$s#}#;s0#s$$8s#]s#'#'s#_s#'#'s#as#'#'s#cs#'#'s#es#'#'s#gs#'#'s#is#'#'s#ks#'#'s#ms#'#'s#os#'#'s#qs#'#'s#ss#'#'s#us#'#'s#ws#'#'s#ys#'#'s#{s#'#'s#}s#'#'s$#s#'#'s$%s#'#'s$'s#'#'s$)s#'#'s$+s#'#'s$-s#'#'s$/s#'#'s$1s#'#'s$3s#'#'s$5s#'#'s$7s#'#'s$9s#'#'s$;s#'#'s$=s#'#'s$?s#'#'s$As#'#'s$Cs#'#'s$Es#'#'s$Gs#'#1s0Hs$IS2m#$#(Cs0KSqs$o1s0K#S2m#%#<GSqs$rR#/s4*H>#)D#s0S(Cs0Rs-z##s0Rs0N##s0Ss-e$#s0Ts-a%#s0Us-J&#s0Vs-<'#s0Ws-8(#s0Xs-4)#s0Ys-0*#s0Zs-++#s0[s-',#s0\s-#-#s0]s,{.#s0^s,j/#s0_s,f0#s0`s,c1#s0as,_2#s0bs,Z3#s0cs,L4#s0ds,I5#s0es,>6#s0fs,=7#s0gs,98#s0hs,59#s0is,4:#s0js,3;#s0ks+y<#s0ls+d=#s0ms+K>#s0ns*g?#s0os*A@#s0ps*@A#s0qs)|B#s0rs){s###s0ss)ws#$#s0ts)vs#%#s0us)rs#&#s0vs)qs#'#s0ws)ms#(#s0xs)is#)#s0ys)es#*#s0zs)ds#+#s0{s)cs#,#s0|s)`s#-#s0}s)Ms#.#s0~s)As#/#s1#s)0s#0#s1$s),s#1#s1%s)(s#2#s1&s)$s#3#s1's(|s#4#s1(s(xs#5#s1)s(ts#6#s1*s(ss#7#s1+s(rs#8#s1,s(qs#9#s1-s(ps#:#s1.s(os#;#s1/s(ns#<#s10s(ms#=#s11s(ls#>#s12s(ks#?#s13s(js#@#s14s(is#A$#SM$%#$'#$)#$+#$-#$/#$1#$3#$5#$7#$9#$;#$=#$?#$A#$s###$s#%#$s#'#$s#)#$s#+#$s#-#$s#/#$s#1#$s#3#$s#5#$s#7#$s#9#$s#;#$s#=#$s#?#$s#A#$s#C#$s#E#$s#G#$s#I#$s#K#$s#M#$s#O#$s#Q#$s#S#$s#U#$s#W#$s#Y#$s#[#$s#]#$s#_#$s#a#$s#c#$s#e#$s#g#$s#i#$s#k#$s#m#$s#o#$s#q#$s#s#$s#u#$s#w#$s#y#$s#{#$s#}#;s1ss$$8s#\s#(#'s#^s#(#'s#`s#(#'s#bs#(#'s#ds#(#'s#fs#(#'s#hs#(#'s#js#(#'s#ls#(#'s#ns#(#'s#ps#(#'s#rs#(#'s#ts#(#'s#vs#(#'s#xs#(#'s#zs#(#'s#|s#(#'s#~s#(#'s$$s#(#'s$&s#(#'s$(s#(#'s$*s#(#'s$,s#(#'s$.s#(#'s$0s#(#'s$2s#(#'s$4s#(#'s$6s#(#'s$8s#(#'s$:s#(#'s$<s#(#'s$>s#(#'s$@s#(#'s$Bs#(#'s$Ds#(#'s$Fs#(#'s$Hs#(#1s2=s$JS2m#$#(Cs2@SSs$M1s2@#S2m#%#<GSSs$PR#i#UTeS4S%S&S'S8S5S9S$QSTS(S)S*S+S,S-S.S/S0S:S@FMOKIGEJS1S7SQs3xSAs3qs3-SVSHSOTfTgRs(hs&ks$T#S=S>S?S6i#:S`S%S&S'S8QSTS(S)S*S+S,S-S.S/S0S:KIEJS7SQG/s5}E/s5~s5N/s6#S1/s6$S75S%S&S'S8S5S9S$QST&%$#S=S>S?S6S(S)S*S+S,S-S.S/S0S:S@FMO6#Ks5NIs5MGs5L7N)#m#+#j#+s43#j#,s46#j#-s48#j#.s4:#j#/s4>#j#0s4@#j#1s4C#j#2s4G#j#3s4J#j#4s4L#j#5s4P#j#6s6$#j#7s6%#j#8s4W#j#9s4[#j#:s4\#=s68s60s4_#FLj#*s62#=s6:s62s4v#FLj#*s64#=s6<s62s53#FLj#*s5K#=s6>s66s5O#FLj#*s68#j#;C#j#<C#j#=C#j#>C#j#?C#j#@Th#j#As6A#j#Bs6D#j#Cs6H#j#Ds6I#j#Es6J#j#Fs6K#j#Gs6L#j#Hs6M#j#Is6N#j#Js6O#j#Ks6P#j#Ls6Q#j#Ms6R#j#Ns6S#j#Os6T#j#Ps6U#j#Qs6V#j#Rs6W#j#Ss6X#j#Ts6Y#j#'s6Z#j#&s6[#j#%s6\#j#$s6]#j#Us6^#j#Vs6_#j#Ws6`#j#Xs6a#j#Ys6b#j#Zs6c#j#[s6d#j#\s6e#j#]s6f#UTiS4m#$##"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma inst_chain_laws : chain_laws (KHp p).
  Proof. apply achain_laws. intros m cur CH. apply iff_refl. Qed.

  Lemma inst_TR_laws1 : ip_TR p = TRLIST -> TR_laws (KHp p).
  Proof. intros E. exact (inst_TR_laws (KHp p) E). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma inst_live : ADRV_LIVE <= as_LIVE_MAX (KHp p) /\ ADRV_CNT <= as_LIVE_CNT_MAX (KHp p).
  Proof. cbn [as_LIVE_MAX as_LIVE_CNT_MAX KHp]. unfold ILIVE_MAX, ILIVE_CNT_MAX. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma inst_driver_laws : asan_driver_laws (KHp p).
  Proof.
    constructor.
    - (* [comment removed for export] *) intros Q c T SRQ K. exact (ASR_realizes Q c T SRQ K).
    - (* [comment removed for export] *) intros s. exists (a_L (i_s s)), (a_S (i_s s)), (a_Zr (i_s s)). split; [|split].
      + intros msF. reflexivity.
      + intros c [LZ _]. exact LZ.
      + intros ms mo ms' mo' [_ K] LZ E1 E2. split; [exact LZ|]. cbn [cfg_model] in *. exact (IK_vm_ext s mo mo' E1 E2 K).
    - (* [comment removed for export] *) intros mo mo' (Efd & _ & Efs & Epr & _). unfold m_fs, m_fds, m_halted. rewrite Efd, Efs, Epr. repeat split; reflexivity.
    - (* [comment removed for export] *) intros mo mo' SB. exact (nonvm_same_mat mo mo' SB).
    - (* [comment removed for export] *) exact inst_live.
  Qed.
End Laws.
