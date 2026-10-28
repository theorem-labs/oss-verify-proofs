(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AxSymExec3Sound. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanCertDefs. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AsanPlanSound AsanInit AsanMainEntryKit. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanMainEntryFacts AsanMainEntryLemmas.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX AH0Spec0 AH0Base AH0Layout.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AH0Pure () : Init.string Init.list := ["Corelib.Lists.ListDef.Forall"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.lowhigh"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"].


Section Pure.
  Context {hAR : arun}.
  Variable p : me_params.
  Hypothesis HCN : Forall cnst_ok (me_cnsts p).
  Variable STKHI : Z.
  Variable FOG : list (Z * Z).
  Variable TF : Z.
  Hypothesis HAC : ACEIL = STKPG p - 0x800000.
  Hypothesis STKHI_gt : SP p < STKHI.
  Hypothesis STKHI_pg : STKHI mod 4096 = 0.
  Hypothesis STKHI_47 : STKHI <= 2 ^ 47.
  Hypothesis STKHI_len : STKHI <= SP p + 2 ^ 23.
  Hypothesis FOG_ok : ltac2:(CDefT.buildp (gd_tbl_AH0Pure ()) "(0.(1.$2.$2.)Lr,(1.$2.$2.)(3.(4.(5.$2.$2.R1.)(6.$2.$2.R1.))(3.(7.=(6.$2.$2.R1.))(3.(8.(9.(5.$2.$2.R1.)(6.$2.$2.R1.))(:.VhAR,))(3.(;.$2.(<.(5.$2.$2.R1.)+1000.)=)(;.$2.(<.(6.$2.$2.R1.)+1000.)=)))))VFOG,)")
(* [comment removed for export] *).
  Hypothesis FOG_len : (length FOG <= 2)%nat.
  Hypothesis FOG_small : Forall (fun r => snd r <= 8192) FOG.
  Hypothesis TF_ok : 1 <= TF <= 3.

  Let bp := bp_of p STKHI FOG TF.
  Let h0 := h0_of bp.

  Local Ltac pv := cbn; tauto.
  Local Ltac inC := apply In_CNSTS; vm_compute; reflexivity.

  (* [comment removed for export] *)
  #[using="HCN STKHI FOG TF HAC FOG_len TF_ok"] Lemma nb0_ok : 0x65f000 <= PG p v_dnodes /\ PG p v_dnodes + 2 ^ 20 <= ACEIL /\ PG p v_dnodes mod 4096 = 0.
  Proof.
    pose proof (r_s1 p HCN) as S1. pose proof (r_s2 p HCN) as S2.
    pose proof (PG_range p HCN v_dnodes ltac:(pv)) as [G G'].
    pose proof (page_stack_apart p HCN (proj2 S1) (proj2 S2) v_dnodes 0x100000 ltac:(pv) ltac:(lia) ltac:(inC)) as K.
    pose proof (page_hull_apart p HCN v_dnodes 0x100000 ltac:(pv) ltac:(lia) ltac:(inC)) as HH.
    rewrite HAC. split; [lia|]. split; [lia | exact G'].
  Qed.
  #[using="HCN STKHI FOG TF HAC FOG_len TF_ok"] Lemma ss0_ok : 0x65f000 <= PG p v_dstore /\ PG p v_dstore + 2 ^ 23 <= ACEIL /\ PG p v_dstore mod 4096 = 0.
  Proof.
    pose proof (r_s1 p HCN) as S1. pose proof (r_s2 p HCN) as S2.
    pose proof (PG_range p HCN v_dstore ltac:(pv)) as [G G'].
    pose proof (page_stack_apart p HCN (proj2 S1) (proj2 S2) v_dstore 0x800000 ltac:(pv) ltac:(lia) ltac:(inC)) as K.
    pose proof (page_hull_apart p HCN v_dstore 0x800000 ltac:(pv) ltac:(lia) ltac:(inC)) as HH.
    rewrite HAC. split; [lia|]. split; [lia | exact G'].
  Qed.

  #[using="Type"] Lemma owned_h0 : forall c, owned h0 c = [].
  Proof.
    intros c. unfold owned, fa_set, cache_set, chunk_set, batch_set. cbn [h0 h0_of h_reg h_cache h_chunks h_tq h_gq r_fa pc_chunks region0 pcl0 q_batches qcache0].
    rewrite app_nil_r. cbn. destruct (c =? kBatchClass); reflexivity.
  Qed.
  #[using="Type"] Lemma carved_h0 : forall c, carved h0 c = 0.
  Proof. intros c. unfold carved. cbn [h0 h0_of h_reg region0 r_alloc_user]. apply Zdiv_0_l. Qed.

  #[using="HCN HAC STKHI_gt STKHI_pg STKHI_47 STKHI_len FOG_ok FOG_len FOG_small TF_ok"] Theorem h0_awf : awf' h0.
  Proof.
    dpose nb0_ok as (N1 & N2 & N3). dpose ss0_ok as (T1 & T2 & T3).
    unfold awf'. split; [exact (L0_wf p HCN STKHI FOG TF HAC STKHI_gt STKHI_pg STKHI_47 STKHI_len FOG_ok)|].
    split. { (* [comment removed for export] *) intros c Hc. cbn [h0 h0_of h_cache h_cinit pcl0 pc_max pc_csize pc_chunks]. unfold pc_count. cbn.
             repeat match goal with |- _ /\ _ => split end; first [ lia | reflexivity | apply Forall_nil | (intros; reflexivity) | (intros; lia) ]. }
    split. { (* [comment removed for export] *) intros c Hc. cbn [h0 h0_of h_reg]. rewrite owned_h0, carved_h0.
             unfold region0, r_nfreed; cbn [r_mapped_user r_alloc_user r_mapped_fa r_fa length].
             unfold kUserMapSize, kUserLimit, kFreeArrayMapSize, kFreeArraySize.
             repeat match goal with |- _ /\ _ => split | |- _ <-> _ => split end;
               first [ lia | reflexivity | apply Forall_nil | apply NoDup_nil
                     | (intros kk; split; [intros HH; destruct HH; lia | intros HH; destruct HH])
                     | (intros; reflexivity) | (intros; lia) ]. }
    split. { (* [comment removed for export] *) split; [constructor|]. split; [constructor|]. intros i sh H. cbn in H. destruct i; discriminate H. }
    split. { (* [comment removed for export] *) unfold wf_quar, wf_qcache. cbn [h0 h0_of h_tq h_gq qcache0 q_batches q_bytes app map].
             unfold kQuarantineCache, kQuarantineMax.
             repeat match goal with |- _ /\ _ => split end; first [ lia | reflexivity | apply Forall_nil | apply NoDup_nil | (intros k HH; destruct HH) ]. }
    split. { (* [comment removed for export] *) unfold wf_sec. cbn [h0 h0_of h_sec sec0 s_chunks s_nres h_pa_committed length map]. unfold kPtrArrayChunks.
             repeat match goal with |- _ /\ _ => split end; first [ lia | reflexivity | apply Forall_nil | apply NoDup_nil ]. }
    split. { (* [comment removed for export] *) unfold wf_depot'. cbn [h0 h0_of h_dep d_n d_nb s_total d_bl length bp bp_of bp_nb0 bp_ss0 bp_tf].
             unfold kDepotNodesL2.
             replace ((TF + 2 ^ 20 - 1) / 2 ^ 20) with 1 by (apply (Z.div_unique _ _ _ (TF - 1)); lia).
             replace (1 / 2 ^ 16) with 0 by reflexivity.
             repeat match goal with |- _ /\ _ => split end;
               first [ lia | reflexivity | (constructor; [repeat split; lia | apply Forall_nil]) ]. }
    split. { (* [comment removed for export] *) unfold wf_budget, SECC. cbn. repeat match goal with |- _ /\ _ => split end; first [ apply Forall_nil | lia ]. }
    split. { (* [comment removed for export] *) unfold wf_big. cbn [h0 h0_of h_sec sec0 s_chunks h_acct a_sech h_L L0_of l_extra bp bp_of bp_extra].
             split; [constructor|]. split; [constructor|]. unfold EXTRA. split.
             - rewrite length_app. cbn [length]. lia.
             - apply Forall_app. split.
               + repeat apply Forall_cons; try apply Forall_nil; cbn [snd]; lia.
               + apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) FOG_small r Hr) as X. cbv beta in X. cbv beta. lia. }
    split. { (* [comment removed for export] *) unfold wf_x. cbn [h0 h0_of h_reg h_tq h_gq h_cinit qcache0 q_batches region0 r_mapped_fa r_alloc_user app flat_map]. rewrite ?carved_h0.
             unfold kFreeArrayMapSize. split; [intros; rewrite carved_h0; lia|]. split; [constructor|]. split; [intros _ c _; reflexivity|].
             (* [comment removed for export] *)
             cbv delta [h0]. cbn [h0_of h_sec h_havol s_chunks s_nres sec0 length Z.of_nat]. unfold kPtrArrayChunks. split; [lia|]. split; [lia|].
             (* [comment removed for export] *)
             split; [left; split; reflexivity|].
             split; [change (a_esz (h_acct (h0_of bp))) with 0; apply Z.mul_nonneg_nonneg; [unfold EM; lia| apply csum_nonneg; intros; apply epi_nonneg]|].
             (* [comment removed for export] *)
             split; [rewrite ?carved_h0; unfold CMAX24; lia| apply Z.leb_le; reflexivity]. }
    (* [comment removed for export] *) unfold wf_ghost. cbn. constructor.
  Qed.

  #[using="FOG_len TF_ok"] Lemma h0_hfr : hfr h0 <= 0.
  Proof. unfold hfr, sframes. cbn [h0 h0_of h_dep s_total d_n bp bp_of bp_tf]. rewrite Z.div_small by lia. lia. Qed.
  #[using="Type"] Lemma h0_havol : h_havol h0 = 0. Proof. reflexivity. Qed.
  End Pure.
