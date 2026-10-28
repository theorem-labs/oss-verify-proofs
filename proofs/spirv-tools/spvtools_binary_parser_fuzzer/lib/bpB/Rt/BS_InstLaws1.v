(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel BReach BazyRestrict BazyLedger BazySR BazyNodes.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsDriverLaws BsSR BsChain BakeStackRep BllocWf BllocKit BllocRep BllocRepFacts BllocRepX BecLazy BsDepotInv BsDepotHash BG_Malloc2 BG_MallocLarge3 BG_MallocAll BS_InstDefs B5_stack_malloc1 B5_stack_malloc4 B5_set_shadow_f5 B6_iface B6_poison B6_annotate BothAllocCons RtB_Iface.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section Laws.
  Context {HCEIL : HeapCeil}.
  Variable p : iparams.

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
    intros x mo mo' E1 E2 ((A & K) & D & T & TB). split; [split|split; [|split]].
    - exact (AMODEL_vm_ext _ _ _ E1 E2 A).
    - exact (akernel_vm_ext _ _ _ E1 K).
    - unfold depot_cov in *. rewrite E1. exact D.
    - unfold dtv_cov in *. rewrite E1. exact T.
    - unfold tb_cov in *. rewrite E1. exact TB.
  Qed.

  Lemma IK_mat : forall (x : ist) mo mo', IK p x mo -> same_but_materialized mo mo' -> IK p x mo'.
  Proof.
    intros x mo mo' K SB. pose proof (same_but_materialized_fields _ _ SB) as (_ & E1 & E2 & _).
    exact (IK_vm_ext x mo mo' E1 E2 K).
  Qed.

  Lemma inst_SR_laws : SR_laws (KHp p).
  Proof. exact (ASR_SR_laws ist (fun x => a_L (i_s x)) (fun x => a_S (i_s x)) (fun x => a_Zr (i_s x)) (IK p) nonvm_same (IK_mat) nonvm_same_mat). Qed.

  Lemma inst_AKREL_laws : AKREL_laws (KHp p).
  Proof. exact (ASR_AKREL_laws ist (fun x => a_L (i_s x)) (fun x => a_S (i_s x)) (fun x => a_Zr (i_s x)) (IK p)). Qed.

  Lemma inst_MPRES_laws : MPRES_laws (KHp p).
  Proof. split; [exact nonvm_same_refl | exact nonvm_same_trans]. Qed.

  Lemma lb_small_le_bytes : forall LB, Forall (fun b => 0 <= blk_size b) LB -> lb_small LB <= lb_bytes LB.
  Proof.
    induction LB as [|b LB IH]; intros F; [cbn; lia|]. apply Forall_cons_iff in F as [F0 F].
    rewrite lb_small_cons. cbn [lb_bytes fold_right]. pose proof (nsmall_bounds _ F0). fold (lb_bytes LB). specialize (IH F). lia.
  Qed.
  Lemma nlarge_le_bytes : forall LB, Forall (fun b => 0 <= blk_size b) LB -> 64513 * nlarge LB <= lb_bytes LB.
  Proof.
    induction LB as [|b LB IH]; intros F; [cbn; lia|]. apply Forall_cons_iff in F as [F0 F].
    rewrite nlarge_cons. cbn [lb_bytes fold_right]. fold (lb_bytes LB). specialize (IH F). unfold nlg.
    destruct (Z.ltb_spec 64512 (blk_size b)); lia.
  Qed.

  Lemma inst_alloc_ok_of_live : alloc_ok_of_live (KHp p).
  Proof.
    intros s LB m n HR Hn HB HC. cbn [as_RHEAP as_alloc_ok as_LIVE_MAX as_LIVE_CNT_MAX KHp] in *.
    destruct HR as (_ & IDS & _).
    assert (F : Forall (fun b => 0 <= blk_size b) LB) by (apply Forall_forall; intros b Hb; pose proof (proj1 (Forall_forall _ _) IDS b Hb) as [_ HS]; lia).
    pose proof (lb_small_le_bytes LB F). pose proof (nlarge_le_bytes LB F). pose proof (nsmall_bounds n Hn).
    unfold Ialloc_ok, ILIVE_MAX, ILIVE_CNT_MAX, LIVEW, LMAX in *. unfold nlg.
    destruct (Z.ltb_spec 64512 n); repeat split; lia.
  Qed.

  Lemma inst_alloc_ok_of_live_bp : alloc_ok_of_live_bp (KHp p).
  Proof.
    intros s LB m n _ Hn HS HC HL. cbn [as_alloc_ok KHp]. unfold Ialloc_ok, ILIVE_CNT_MAX.
    unfold RT_SMALL_MAX, RT_CNT_MAX, RT_LARGE_MAX, LIVEW, CNTB, LMAX in *. repeat split; lia.
  Qed.

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

  Lemma inst_asan_memcpy : asan_memcpy_stmt.   Proof. exact asan_memcpy_ok. Qed.
  Lemma inst_asan_memset : asan_memset_stmt.   Proof. exact asan_memset_ok. Qed.
  Lemma inst_asan_memmove : asan_memmove_stmt. Proof. exact asan_memmove_ok. Qed.
  Lemma inst_memcpy_icpt : memcpy_icpt_stmt.   Proof. exact memcpy_icpt_ok. Qed.
  Lemma inst_memmove_icpt : memmove_icpt_stmt. Proof. exact memmove_icpt_ok. Qed.
  Lemma inst_strlen_icpt : strlen_icpt_stmt.   Proof. exact strlen_icpt_ok. Qed.
  Lemma inst_strncmp_icpt : strncmp_icpt_stmt. Proof. exact strncmp_icpt_ok. Qed.

  Lemma inst_annotate_cc : annotate_cc_stmt.
  Proof.
    intros until lo. intros -> -> -> -> B8 L8 LEN O8 N8 MO MN AP HI SH ST CEIL LO MI AC IAM.
    unfold AANNOTATE_CC. change 0xbc36c with annotate_entry.
    apply annotate_body; try assumption.
    - repeat split; assumption.
    - split; assumption.
    -   unfold app_rng. destruct AP as [[P1 P2]|[P1 P2]]; [right | left]; split; try assumption; try lia.
    - eapply ACONST_cell; [exact AC|]. unfold ACF_CLRTHR_CELL. cbn; clear; tauto.
    - eapply ACONST_cell; [exact AC|]. unfold ADCO_CELL. cbn; clear; tauto.
    - eapply ACONST_cell; [exact AC|]. unfold AGOT_VERB, AVERB_CELL. cbn; clear; tauto.
    - eapply ACONST_cell; [exact AC|]. unfold AVERB_CELL. cbn; clear; tauto.
  Qed.

  Lemma inst_chain_laws : chain_laws (KHp p).
  Proof. apply achain_laws. intros m cur CH. apply iff_refl. Qed.

  Lemma inst_TR_laws1 : trace_ok (ip_TR p) APC0_MALLOC [ARA_OPNEW] -> TR_laws (KHp p).
  Proof. intros T. exact T. Qed.

  Lemma inst_live : ADRV_LIVE <= as_LIVE_MAX (KHp p) /\ ADRV_CNT <= as_LIVE_CNT_MAX (KHp p).
  Proof. cbn [as_LIVE_MAX as_LIVE_CNT_MAX KHp]. unfold ILIVE_MAX, ILIVE_CNT_MAX, CNTB, ADRV_LIVE, ADRV_CNT. lia. Qed.

  Lemma inst_driver_laws : asan_driver_laws (KHp p).
  Proof.
    constructor.
    -   intros Q c T SRQ K. exact (ASR_realizes Q c T SRQ K).
    -   intros s. exists (a_L (i_s s)), (a_S (i_s s)), (a_Zr (i_s s)). split; [|split].
      + intros msF. reflexivity.
      + intros c [LZ _]. exact LZ.
      + intros ms mo ms' mo' [_ K] LZ E1 E2. split; [exact LZ|]. cbn [cfg_model] in *. exact (IK_vm_ext s mo mo' E1 E2 K).
    -   intros mo mo' (Efd & _ & Efs & Epr & _). unfold m_fs, m_fds, m_halted. rewrite Efd, Efs, Epr. repeat split; reflexivity.
    -   intros mo mo' SB. exact (nonvm_same_mat mo mo' SB).
    -   exact inst_live.
  Qed.
End Laws.
