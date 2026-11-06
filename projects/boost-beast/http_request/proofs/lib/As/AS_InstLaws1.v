(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.boost_beast.http_request.images Require Import Asan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AsanAllocModel SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsIface AsDriverLaws AsSR AsChain FakeStackRep
     AllocWf AllocKit AllocRep AllocRepFacts AllocRepX SecLazy AsDepotInv AsDepotHash AG_Malloc2 AG_MallocLarge3 AG_MallocAll
     AS_InstDefs AS_InstTR AsTRList AsIface5 AsIface6 AsIface7
     N5_stack_malloc0 N5_stack_malloc1 N5_stack_malloc2 N5_stack_malloc3 N5_stack_malloc4 N5_stack_malloc7 N5_stack_free7
     N5_set_shadow_f5 N5_set_shadow_00 N5_set_shadow_f8 N6_iface N6_poison N6_annotate N6_strcmp2 N6_bcmp N6_strtoll AXL_snprintf.
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
  Lemma inst_stack_malloc_1 : stack_malloc_1_stmt (KHp p). Proof. exact (stack_malloc_1_ok (KHp p) RFS_is). Qed.
  Lemma inst_stack_malloc_4 : stack_malloc_4_stmt (KHp p). Proof. exact (stack_malloc_4_ok (KHp p) RFS_is). Qed.
  Lemma inst_set_shadow_f5 : set_shadow_f5_stmt.       Proof. exact set_shadow_f5_ok. Qed.
  (* [comment removed for export] *)
  Lemma inst_rt_hyps5 : asan_rt_hyps5 (KHp p).
  Proof.
    ltac2:(KReplay.run [|constr:(@Corelib.Init.Logic.conj); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsIface5.stack_malloc_0_stmt); constr:(HCEIL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AS_InstDefs.KHp); constr:(p); constr:(@Corelib.Init.Logic.and); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsIface5.stack_malloc_2_stmt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsIface5.stack_malloc_3_stmt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsIface5.set_shadow_00_stmt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsIface5.set_shadow_f8_stmt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.N5_stack_malloc0.stack_malloc_0_ok); constr:(RFS_is); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.N5_stack_malloc2.stack_malloc_2_ok); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.N5_stack_malloc3.stack_malloc_3_ok); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.N5_set_shadow_00.set_shadow_00_ok); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.N5_set_shadow_f8.set_shadow_f8_ok); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsIface5.asan_rt_hyps5)|] Array.empty "##3###4#(#1#.#/#)#*#'#,#-#0#2#3#4#5#6#&#+%#2'#3%VGCHVIC#VJC$VKC%$EF$$#$&#WLC)DWMC*DWNC+D#EFOP#*)$##,)&##.)(#VQC0m#$##"). Qed.
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
    ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@LinuxProcessSemantics.Riscv.Prelude.bvmap); constr:(@Corelib.Numbers.BinNums.xI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsIface.mem); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.eq); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.aapp); constr:(HCEIL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.AAPP_HI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.SHAD); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsIface.cc_shadow); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.stk); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.ASegs.asegs); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.aceil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsIface.AINTRIN_STACK); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.mem_inv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.ACONST); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.in_app_mem); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Exec.evt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsIface.annotate_post); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.MState.MS); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.mkR); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsIface.AANNOTATE_CC); constr:(@Corelib.Init.Datatypes.None); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.PropExec.seg_rom); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.N6_annotate.annotate_body); constr:(@Corelib.Init.Logic.conj); constr:(@kc__1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.aapp_lo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.aapp_hi); constr:(@Corelib.Init.Logic.or); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.AHI_LO); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.ASegs.AIMG_TOP); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.ALOWSH_LO); constr:(@kc__2); constr:(@Corelib.Init.Logic.or_intror); constr:(@Corelib.Init.Logic.or_introl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.N6_poison.app_rng); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.ACONST_cell); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.N6_poison.ACF_CLRTHR_CELL); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cell); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C8); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Init.Datatypes.pair); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AGOT_SHBASE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.TacX.wz); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.ASHBASE_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AGOT_UAR); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AUAR_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AGOT_MEMSETP); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AMEMSETP_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AGOT_FLAGS); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AGOT_CFLAGS); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AGOT_HIEND); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AHIEND_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AGOT_MIDBEG); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AMIDBEG_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AGOT_MIDEND); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AMIDEND_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AGOT_SEALED); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AGOT_DYING); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.ADYING_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AGOT_PGSZ); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.APGSZ_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AGOT_RINTRIN); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.ARINTRIN_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AGOT_FSTLS); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.ASegs.ASHADOW_BASE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C4); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AREAL_MEMSET); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AINITED_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.TacX.b8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.ACANPOISON_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AMEMCPYP_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AREAL_MEMCPY); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.ASTRLENP_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AREAL_STRLEN); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.ACF_ISTRCMP_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AF_REPSTR_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AREAL_STRTOLL_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AREAL_VSNPRINTF_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AGOT_SSP_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.ASHW_STR_ONE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.ASHW_STR_PCTD); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.ACF_IMEMCMP_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AREAL_MEMCMP_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.ACF_ISTRLEN_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.ACF_STRICT_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AF_DCO_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AGOT_VERBOSITY); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AVERBOSITY_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.ACF_CSMT_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AGOT_DTLS); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AREAL_TLSGA_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AREAL_TLSGA); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.ACF_ITLS_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.ATSD_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AMUSL_TSD); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AMUSL_DTV); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AMUSL_DTV1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AMEMCHRP_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AREAL_MEMCHR); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AREADP_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AREAL_READ); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AFWRITEP_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AREAL_FWRITE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AVPRINTFP_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AREAL_VPRINTF); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AVFPRINTFP_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AREAL_VFPRINTF); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.ASTRNLENP_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AREAL_STRNLEN); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.ACF_CHKPRINTF_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AF_REPGLOB_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AMU_GLOBALS_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.AREGISTERED_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.ACOVFLAG_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.ASHW_FMTD); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.ASHW_MSG_USAGE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.ASHW_MSG_REFUSED); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.ASHW_MSG_OPEN); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.ASHW_MSG_SHORT); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.ASHW_STDOUTBUF); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.Lists.List.In); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsConst.aconst_cells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.N6_annotate.ADCO_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.N6_annotate.AGOT_VERB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.N6_annotate.AVERB_CELL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsIface.annotate_cc_stmt)|] [|@a0; @a1; @a2; @a3; @P2; @P1; @H; @IAM; @AC; @MI; @LO; @CEIL; @ST; @SH; @HI; @AP; @MN; @MO; @N8; @O8; @LEN; @L8; @B8; @lo; @newmid; @oldmid; @len; @beg; @m; @fc; @F; @t6; @t5; @t4; @t3; @s11; @s10; @s9; @s8; @s7; @s6; @s5; @s4; @s3; @s2; @a7; @a6; @a5; @a4; @s1; @s0; @t2; @t1; @t0; @tp; @gp; @sp; @ra|] "#74#_%;#i$=#;#A#<#p#=#:#>###@#{#?#2#V#$#3#W#]#\#[#L#K#J#I#H#G#F#E#D#9%:#1#u#Y#M#8#Z#X#C#/#4#P#O#N#B#0#v#^#.$3$4$5#(#,#-#5#Q%7#e#'#6#7#R%=#U#b#)#s#t#x#w#z#~$#$$$%$'#S#+$0$1$6$E$G$I$M$T$V$_$r$x$;%;%<#f#}#T$*$+$,$/$9$?$A$@$C$F$H$J$K$L$O$N$Q$P$R$S$U$X$W$Y$Z$\$]$`$b$a$d$c$e$f$g$h$i$j$k$l$m$n$o$p$q$s$t$v$u$w$y$z${$}$|%#$~%%%$%'%&%)%(%+%*%,%-%.%/%0%1%2%3%4%5%6$-#&#%#h%>#j$2#g#d$7$B$<#r$>$D#o#q#k#m%9#n$.#y$)$($&$8#c#|%8$:#l$[$^@$z&${%$|$$}$$~&%#'%$&%%%%&$%'$%($%)%%*%%+%%,&%-%%.'%/%%0B%1*%2&%3&%4$%5%%6%%7(%8)%9$%:$&SN&#&#&#&#&#9#USU#%*9#VSr#%9)USU#/)SO#)M#/+SH0SVSH/-##-F##.F&-42SI##C#H*HSJ-:-8VSW$#*SJ#.'#2SJ+#C#H*S3S;0S3SA*S;#.%#*PS;0PS3*S;#.%#WSXS4S#P0S<S#*#SB4S#SKVSYS<#WSZSPSK#:s#)S$XS[NSQP#USsS4*#S#:s#-S54#S\*S<#VS]NJUS^E0EJVS_E#i#:S`SCS%S&S'S$QS6S(S)S*S+S,S-S.S/S0OKGES1S7I5SCS%S&S'S8S5S9S$QSPStSaSRSLS=S>S?S6S(S)S*S+S,S-S.S/S0S:S@FM/s#6SuUSvs#6USwN6&O%K$I#7N(#k##*#k##-#k##/#k##1#k##5#k##8#k##;#k##?#k##B#k##s#$#k##s#)#k##s#.#k##s#/#k##s#2#k##s#9#k##s#:#k##s#>#k##s#?#k##s#A#j#$s#M#0SHSO/s#P##s#PM#/s#RG5SCS%S&S'S8S5S9S$Q#SKSaSRSLS=S>S?S6S(S)S*S+S,S-S.S/S0S:S@FM6#O@K?I>7Ns###k##s#%#k##s#(#k##s#*#k##s#,#k##s#0#k##s#3#k##s#6#k##s#:#k##s#=#k##s#?#k##s#D#k##s#I#k##s#J#k##s#M#k##s#T#k##s#U#k##s#Y#k##s#Z#j#%s#g#0GE/s#j#5SCS%S&S'S8S5S9S$Q;#S<SRSLS=S>S?S6S(S)S*S+S,S-S.S/S0S:S@FM6#Os#8Ks#7Is#67Ns#;#k##s#=#k##s#@#k##s#B#k##s#D#k##s#H#k##s#K#k##s#N#k##s#R#k##s#U#k##s#W#k##s#\#k##s#a#k##s#b#k##s#e#k##s#l#k##s#m#k##s#q#j#&s#~#/s$$J5SCS%S&S'S8S5S9S$Qs#19#S#SLS=S>S?S6S(S)S*S+S,S-S.S/S0S:S@FM6#Os#NKs#MIs#L7Ns#Q#k##s#S#k##s#V#k##s#X#k##s#Z#k##s#^#k##s#a#k##s#d#k##s#h#k##s#k#k##s#m#k##s#r#k##s#w#k##s#x#k##s#{#k##s$&#k##s$'#j#'s$7#2Sbs$+#C#H*HSI*SIs$(.$#*SASD0SAS;*SD#.%#*S3SD*SDs$).$#WSXS4PS30S#P*#SB4PS<VSYS##WSZSKS<#:s$KQXS[NSPS3#*s$$P:s$NS94#S\*S##VS]NS1US^J0JS1VS_J#2Es$G#C#H2Js$I#C#H2S1s$K#C#H2S7s$M#C#H.%#.(#3'%S;SD3*%S3#3-%P#*ES1*S1s$3.$#*ES7*S7s$6.$#3&#SJSIVScEJWSdS4EJ$$#*SEG*s#bSB.$#*SFG*s#eSG.$#$&#j##*#VScGE*SFI0IG*#SG.%#*SEK0KI*#SB.%#*SFK*&SG.$#$&#j##+#*SFO0MO*#SG*SEF0FM*#SB.%#*SFF*&SG.$#3%$RL''$#j#(,#j#)/#V#RLj##5#j##?#YSe@>4#Lj#*B#U#Lj##s#/#WSdS4GE*SEI*s#%s$p.$#j###=*s#$s$s*SEO*=s$u3<:RSA8:7#j#(%#j#)'#V#RLj##*#j##/#YSe0/-#Lj#*2#U#Lj##s#A#ZSxs#Cs#Bs#96#SbVSyEs${m#$#%SN%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#-#/s&5#+#USzD)D$#US{DVS|C#,Sf+#)D#((C'S}#&s#L%#%#%#&#%#%#&#&#&#%#%#%#%#&#&#&#&#&#-#%SN&#%#%#%#&#%#%#&#&#&#&#&#&#%#&#&#&#&#&#-#&SN&#%#&#&#%#%#&#%#%#&#&#&#%#%#%#%#&#&#&#-#&s#&%#%#%#%#%#&#%#&#%#&#&#&#-#&s#$&#%#%#&#&#%#%#&#&#&#&#&#%#&#%#&#&#-#&3%#%#&#%#&#&#&#&#%#%#&#&#&#&#-#&s#\%#%#%#%#%#&#%#&#%#&#&#%#%#%#%#&#&#&#&#-#%s#6&#%#%#%#&#%#&#&#%#&#&#&#-#&-&#%#%#%#%#&#&#&#-#%s#*&#%#&#&#&#&#%#&#%#%#&#&#&#-#&s#=%#%#%#&#%#&#%#&#&#%#%#&#%#%#&#&#&#-#%0%#&#&#%#&#%#%#&#&#&#&#-#%s$=%#&#%#%#&#&#&#-#&s$a&#%#%#%#%#&#&#&#%#%#&#&#&#-#%s$=%#&#%#%#&#%#&#&#&#&#&#%#%#&#&#&#-#(Cs%Es$ss%F#s%Es%A#,Sg+#)D#s%K(Cs%JS~##s%J#(,Sh+#)D#s%P(Cs%OT###s%O#-%s)1&#&#%#%#&#%#%#%#&#&#&#%#%#%#&#&#&#-#,s$}+#)D#s%h(Cs%gT$##s%g#s#%&s%Y%#%#&#%#&#&#&#-#,s$}+#)D#s%v(Cs%uT%##s%u#s#3,Si+#)D#s%{(Cs%zT&##s%z#s#8,T'+#)D#s&$(Cs&#T(##s&##s#=,T)+#)D#s&)(Cs&(T*##s&(#s#B-SN,#+#)D#s&/(Cs&.T+##s&.#s#H,Sj+#)D#s&4(Cs&3T,##s&3#s#M,Sk+#)D#s&9(Cs&8T-##s&8#s#R,T.+#)D#s&>(Cs&=T/##s&=#s#W&s&P&#&#&#&#&#&#&#&#&#&#-#,#+#)D#s&O)Ds#$#(Cs&OT0##s&O#s#i,T1+#)D#s&U(Cs&TSf##s&T#s#n>s#-)D#s&Y(Cs&XSg##s&X#s#r,T2+#)D#s&^(Cs&]Sh##s&]#s#wUSls#7?#)D#s&c)D$#(Cs&cT3##s&c#s#}%s*>%#%#-#VSWs*2#4#s#B,#+#,H+#)D#s&q)D$#)D'#(Cs&rSi##s&r#s$0>))D#s&w(Cs&vSj##s&v#s$4&s*T&#&#&#&#&#-#,#+#)D#s''(Cs'&Sk##s'&#s$@(Cs'(T4s#%#s'(#s$B,T5+#)D#s'.(Cs'-T6##s'-#s$G,T7+#)D#s'3(Cs'2T8##s'2#s$L(Cs'4T9s#1#s'4#s$N(Cs'6T:s#3#s'6#s$P%s*r%#&#&#%#%#&#%#%#&#&#%#%#&#&#&#-#,s&A+#)D#s'M(Cs'LT;##s'L#s$f&8%#%#&#%#&#%#%#&#%#%#&#%#&#&#-#,s&F+#)D#s'b(Cs'aT<##s'a#s${&s']%#&#%#%#%#&#%#&#%#%#%#&#&#%#%#&#&#&#&#-#,s&K+#)D#s'|(Cs'{T=##s'{#s%9&s(b&#%#%#%#%#%#%#&#&#%#%#%#%#%#%#&#&#%#&#&#&#&#&#&#%#&#%#%#%#%#%#&#&#%#%#%#%#%#%#&#&#%#%#%#%#%#%#&#&#%#%#%#%#%#%#&#&#%#-#,#+#)D#s(a(Cs(`T>##s(`#s%z%s#*%#%#%#%#%#&#&#%#%#%#%#%#%#&#&#%#%#%#%#%#%#&#&#%#&#&#&#&#&#&#%#%#-#,#+#)D#s),(Cs)+T?##s)+#s&E(Cs)-T@s%)#s)-#s&G%s$S%#&#&#&#%#%#&#&#%#%#&#&#-#,s'^+#&2%#%#%#%#%#%#%#%#%#&#&#-#,s'c+#)D#s)P)D3#(Cs)PTA##s)P#s&j(Cs)RTBs%O#s)R#s&lUSlH?#)D#s)X(Cs)WTC##s)W#s&q(Cs)YTDs%V#s)Y#s&s,Sm+#)D#s)_(Cs)^TE##s)^#s&x(Cs)`Sms%I#s)`#s&z,s)g+#)D#s)f(Cs)eTF##s)e#s'#,s-4+#)D#s)k(Cs)jTG##s)j#s'(,TH+#)D#s)p(Cs)oTI##s)o#s'-(Cs)qTJs%n#s)q#s'/(Cs)sSns%p#s)s#s'1-s-U0Sn#(Cs)w#s%`#s)w#s'5%s$o&#%#&#%#&#%#&#&#%#%#&#&#&#-#,s(4+#)D#s*0(Cs*/TK##s*/#s'I&s$~%#%#&#%#&#&#&#&#-#,s(0+#)D#s*?(Cs*>TL##s*>#s'X%s%4%#%#&#%#&#%#&#%#&#&#&#-#,s(5+#)D#s*Q(Cs*PTM##s*P#s'j,TN+#)D#s*V(Cs*UTO##s*U#s'o,TP+#)D#s*[(Cs*ZTQ##s*Z#s't,TR+#)D#s*`(Cs*_TS##s*_#s'y,TT+#)D#s*e(Cs*dTU##s*d#s'~,TV+#)D#s*j(Cs*iTW##s*i#s(',TX+#)D#s*o(Cs*nTY##s*n#s(,(Cs*pTZs&m#s*p#s(.(Cs*rT[s&y#s*r#s(0(Cs*tT\s&c#s*t#s(2(Cs*vT]s'K#s*v#s(4(Cs*xT^s$$#s*x#s(6(Cs*zT_s&h#s*z#s(8(Cs*|T`s&j#s*|#s(:(Cs*~Tas&l#s*~#s(<(Cs+$Tbs&n#s+$#s(>(Cs+&Tcs&p#s+&#s(@(Cs+(Tds&s#s+(#s(B$#SM$&#$)#$,#$/#$2#$5#$8#$;#$>#$A#$s#$#$s#*#$s#0#$s#6#$s#<#$s#B#$s#H#$s#[#$s#k#$s$$#$s$)#$s$,#$s$/#$s$5#$s$;#$s$A#$s$D#$s$J#$s$M#$s$S#$s$V#$s$z#$s$}#$s%I#$s&/#$s&J#$s&`#$s&w#$s&z#$s&}#$s''#$s'-#$s'0#$s'=#$s'B#$s'R#$s'Y#$s'_#$s'd#$s'j#$s'}#$s('#$s(-#$s(3#$s(:#$s(@#$s(F#$s(L#$s([#$s(t#$s(z#;s+gs)%8s$as#)#'s$gs#)#'s$js#)#'s$ps#)#'s$ss#)#'s$ys#)#'s$|s#)#'s%Ds#)#'s%Gs#)#'s%os#)#'s&Us#)#'s&ps#)#'s'*s#)#'s'As#)#'s'Ds#)#'s'Gs#)#'s'Ms#)#'s'Ss#)#'s'Vs#)#'s'cs#)#'s'hs#)#'s'xs#)#'s(#s#)#'s()s#)#'s(.s#)#'s(4s#)#'s(Gs#)#'s(Ms#)#'s(Ss#)#'s(Ys#)#'s(`s#)#'s(fs#)#'s(ls#)#'s(rs#)#'s)%s#)#'s)>s#)#'s)Ds#)#'s)Js#)#1s,2s)LS2m#$#(Cs,5Sos,61s,5#S2m#%#<GSos,9R#9s/t/#s(n?#)D#s,>%s)A&#&#%#%#&#&#&#-#(Cs,Fs*%,#s,Fs,B##s,Gs)\$#s,Hs)X%#s,Is)A&#s,Js)4'#s,Ks)0(#s,Ls),)#s,Ms)(*#s,Ns)#+#s,Os({,#s,Ps(w-#s,Qs(s.#s,Rs(b/#s,Ss(^0#s,Ts([1#s,Us(W2#s,Vs(R3#s,Ws(D4#s,Xs(A5#s,Ys(66#s,Zs(57#s,[s(18#s,\s(-9#s,]s(,:#s,^s(+;#s,_s'r<#s,`s'^=#s,as'E>#s,bs&a?#s,cs&;@#s,ds&:A#s,es%tB#s,fs%ss###s,gs%os#$#s,hs%ns#%#s,is%js#&#s,js%is#'#s,ks%es#(#s,ls%as#)#s,ms%]s#*#s,ns%\s#+#s,os%[s#,#s,ps%Xs#-#s,qs%Es#.#s,rs%7s#/#s,ss%&s#0#s,ts$~s#1#s,us$zs#2#s,vs$vs#3#s,ws$rs#4#s,xs$ns#5#s,ys$js#6#s,zs$is#7#s,{s$hs#8#s,|s$gs#9#s,}s$fs#:#s,~s$es#;#s-#s$ds#<#s-$s$cs#=#s-%s$bs#>#s-&s$as#?#s-'s$`s#@#s-(s$_s#A$#SM$%#$'#$)#$+#$-#$/#$1#$3#$5#$7#$9#$;#$=#$?#$A#$s###$s#%#$s#'#$s#)#$s#+#$s#-#$s#/#$s#1#$s#3#$s#5#$s#7#$s#9#$s#;#$s#=#$s#?#$s#A#$s#C#$s#E#$s#G#$s#I#$s#K#$s#M#$s#O#$s#Q#$s#S#$s#U#$s#W#$s#Y#$s#[#$s#]#$s#_#$s#a#$s#c#$s#e#$s#g#$s#i#$s#k#$s#m#$s#o#$s#q#$s#s#$s#u#$s#w#$s#y#$s#{#$s#}#;s-gs$$8s#^s#&#'s#`s#&#'s#bs#&#'s#ds#&#'s#fs#&#'s#hs#&#'s#js#&#'s#ls#&#'s#ns#&#'s#ps#&#'s#rs#&#'s#ts#&#'s#vs#&#'s#xs#&#'s#zs#&#'s#|s#&#'s#~s#&#'s$$s#&#'s$&s#&#'s$(s#&#'s$*s#&#'s$,s#&#'s$.s#&#'s$0s#&#'s$2s#&#'s$4s#&#'s$6s#&#'s$8s#&#'s$:s#&#'s$<s#&#'s$>s#&#'s$@s#&#'s$Bs#&#'s$Ds#&#'s$Fs#&#1s./s$HS2m#$#(Cs.2Sps$T1s.2#S2m#%#<GSps$WR#/s1mSS+#)D#s.:%s1t%#&#%#%#&#%#&#%#%#&#%#%#%#&#&#&#-#&s.A%#&#&#&#&#%#%#&#%#%#&#&#&#-#/s25s,*+#)D#s.^(Cs.]s+w##s.]s.Y##s.^s+s$#s._s+o%#s.`s+X&#s.as+K'#s.bs+G(#s.cs+C)#s.ds+?*#s.es+:+#s.fs+6,#s.gs+2-#s.hs+..#s.is*y/#s.js*u0#s.ks*r1#s.ls*n2#s.ms*i3#s.ns*[4#s.os*X5#s.ps*M6#s.qs*L7#s.rs*H8#s.ss*D9#s.ts*C:#s.us*B;#s.vs*-<#s.ws)u=#s.xs)\>#s.ys(x?#s.zs(R@#s.{s(QA#s.|s(/B#s.}s(.s###s.~s(*s#$#s/#s()s#%#s/$s(%s#&#s/%s($s#'#s/&s'|s#(#s/'s'xs#)#s/(s'ts#*#s/)s'ss#+#s/*s'rs#,#s/+s'os#-#s/,s'\s#.#s/-s'Ns#/#s/.s'=s#0#s//s'9s#1#s/0s'5s#2#s/1s'1s#3#s/2s'-s#4#s/3s')s#5#s/4s'%s#6#s/5s'$s#7#s/6s'#s#8#s/7s&~s#9#s/8s&}s#:#s/9s&|s#;#s/:s&{s#<#s/;s&zs#=#s/<s&ys#>#s/=s&xs#?#s/>s&ws#@#s/?s&vs#A$#SM$%#$'#$)#$+#$-#$/#$1#$3#$5#$7#$9#$;#$=#$?#$A#$s###$s#%#$s#'#$s#)#$s#+#$s#-#$s#/#$s#1#$s#3#$s#5#$s#7#$s#9#$s#;#$s#=#$s#?#$s#A#$s#C#$s#E#$s#G#$s#I#$s#K#$s#M#$s#O#$s#Q#$s#S#$s#U#$s#W#$s#Y#$s#[#$s#]#$s#_#$s#a#$s#c#$s#e#$s#g#$s#i#$s#k#$s#m#$s#o#$s#q#$s#s#$s#u#$s#w#$s#y#$s#{#$s#}#;s/~s$$8s#]s#'#'s#_s#'#'s#as#'#'s#cs#'#'s#es#'#'s#gs#'#'s#is#'#'s#ks#'#'s#ms#'#'s#os#'#'s#qs#'#'s#ss#'#'s#us#'#'s#ws#'#'s#ys#'#'s#{s#'#'s#}s#'#'s$#s#'#'s$%s#'#'s$'s#'#'s$)s#'#'s$+s#'#'s$-s#'#'s$/s#'#'s$1s#'#'s$3s#'#'s$5s#'#'s$7s#'#'s$9s#'#'s$;s#'#'s$=s#'#'s$?s#'#'s$As#'#'s$Cs#'#'s$Es#'#'s$Gs#'#1s0Gs$IS2m#$#(Cs0JSqs$p1s0J#S2m#%#<GSqs$sR#/s4)H>#)D#s0R(Cs0Qs-}##s0Qs0M##s0Rs-g$#s0Ss-c%#s0Ts-L&#s0Us-?'#s0Vs-;(#s0Ws-7)#s0Xs-3*#s0Ys-.+#s0Zs-*,#s0[s-&-#s0\s,~.#s0]s,m/#s0^s,i0#s0_s,f1#s0`s,b2#s0as,]3#s0bs,O4#s0cs,L5#s0ds,A6#s0es,@7#s0fs,<8#s0gs,89#s0hs,7:#s0is,6;#s0js+}<#s0ks+i=#s0ls+P>#s0ms*l?#s0ns*F@#s0os*EA#s0ps*#B#s0qs)~s###s0rs)zs#$#s0ss)ys#%#s0ts)us#&#s0us)ts#'#s0vs)ps#(#s0ws)ls#)#s0xs)hs#*#s0ys)gs#+#s0zs)fs#,#s0{s)cs#-#s0|s)Ps#.#s0}s)Bs#/#s0~s)1s#0#s1#s)-s#1#s1$s))s#2#s1%s)%s#3#s1&s(}s#4#s1's(ys#5#s1(s(us#6#s1)s(ts#7#s1*s(ss#8#s1+s(rs#9#s1,s(qs#:#s1-s(ps#;#s1.s(os#<#s1/s(ns#=#s10s(ms#>#s11s(ls#?#s12s(ks#@#s13s(js#A$#SM$%#$'#$)#$+#$-#$/#$1#$3#$5#$7#$9#$;#$=#$?#$A#$s###$s#%#$s#'#$s#)#$s#+#$s#-#$s#/#$s#1#$s#3#$s#5#$s#7#$s#9#$s#;#$s#=#$s#?#$s#A#$s#C#$s#E#$s#G#$s#I#$s#K#$s#M#$s#O#$s#Q#$s#S#$s#U#$s#W#$s#Y#$s#[#$s#]#$s#_#$s#a#$s#c#$s#e#$s#g#$s#i#$s#k#$s#m#$s#o#$s#q#$s#s#$s#u#$s#w#$s#y#$s#{#$s#}#;s1rs$$8s#\s#(#'s#^s#(#'s#`s#(#'s#bs#(#'s#ds#(#'s#fs#(#'s#hs#(#'s#js#(#'s#ls#(#'s#ns#(#'s#ps#(#'s#rs#(#'s#ts#(#'s#vs#(#'s#xs#(#'s#zs#(#'s#|s#(#'s#~s#(#'s$$s#(#'s$&s#(#'s$(s#(#'s$*s#(#'s$,s#(#'s$.s#(#'s$0s#(#'s$2s#(#'s$4s#(#'s$6s#(#'s$8s#(#'s$:s#(#'s$<s#(#'s$>s#(#'s$@s#(#'s$Bs#(#'s$Ds#(#'s$Fs#(#'s$Hs#(#1s2<s$JS2m#$#(Cs2?SSs$M1s2?#S2m#%#<GSSs$PR#i#UTeS4S%S&S'S8S5S9S$QSTS(S)S*S+S,S-S.S/S0S:S@FMOKIGEJS1S7SQs3wSAs3ps3,SVSHSOTfTgRs(is&ls$T#S=S>S?S6i#:S`S%S&S'S8QSTS(S)S*S+S,S-S.S/S0S:KIEJS7SQG/s5|E/s5}s5M/s5~S1/s6#S75S%S&S'S8S5S9S$QST&%$#S=S>S?S6S(S)S*S+S,S-S.S/S0S:S@FMO6#Ks5MIs5LGs5K7N)#m#+#j#+s42#j#,s45#j#-s47#j#.s49#j#/s4=#j#0s4?#j#1s4B#j#2s4F#j#3s4I#j#4s4K#j#5s4O#j#6s6##j#7s6$#j#8s4V#j#9s4Z#j#:s4[#=s67s6/s4^#FLj#*s61#=s69s61s4u#FLj#*s63#=s6;s61s52#FLj#*s5J#=s6=s65s5N#FLj#*s67#j#;C#j#<C#j#=C#j#>C#j#?C#j#@Th#j#As6@#j#Bs6C#j#Cs6G#j#Ds6H#j#Es6I#j#Fs6J#j#Gs6K#j#Hs6L#j#Is6M#j#Js6N#j#Ks6O#j#Ls6P#j#Ms6Q#j#Ns6R#j#Os6S#j#Ps6T#j#Qs6U#j#Rs6V#j#Ss6W#j#Ts6X#j#'s6Y#j#&s6Z#j#%s6[#j#$s6\#j#Us6]#j#Vs6^#j#Ws6_#j#Xs6`#j#Ys6a#j#Zs6b#j#[s6c#j#\s6d#j#]s6e#UTiS4m#$##"). Qed.

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
