(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModelX APop APopGen.
Import ListNotations.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Local Ltac Stdlib.micromega.Lia.nia ::= nia_ah.
Ltac2 gd_tbl_AW_FreePM3 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.BHeap.AModel.AH"; "ARUN_1.RfN.L"; "ARUN_1.RfN.rf_reg"; "ARUN_1.RfN.rf_cache"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_chunks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_tq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_gq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_sec"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.DP"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_ia"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_fake"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_pa_committed"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_havol"; "RocqVerifyHarness.AgentSubmission.BHeap.APopGen.acct_set_exh"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_acct"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kNumClasses"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.pc_max"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.max_count"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.pc_csize"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.class_size"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Logic.ex"; "Stdlib.ZArith.BinInt.Z.add"; "ARUN_1.RfN.cv"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Datatypes.app"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.

Section RfN.
  Variable h : ahst.
  Variables (c nw UU FF N' tf' : Z) (nb' bl' : list Z) (fa' cache' : list Z) (cache_o : Z -> pcl) (xb : bool).
  Definition L := h_L h.
  Definition r := h_reg h c.
  Definition cs := class_size c.
  Definition cv := carved h c.
  Definition mu' := r_mapped_user r + UU.
  Definition mfa' := r_mapped_fa r + FF.
  Definition au' := r_alloc_user r + nw * cs.

  Definition rf_reg (j : Z) : region := if j =? c then RG mu' au' mfa' fa' else h_reg h j.
  Definition rf_cache (j : Z) : pcl := if j =? c then PC (max_count c) (class_size c) cache' else cache_o j.
  Definition rf_h : ahst := ltac2:(CDefT.buildp (gd_tbl_AW_FreePM3 ()) "(0.$1.$2.$3.$4.(5.Vh,)(6.Vh,)(7.Vh,)(8.Vh,)(9.VN',Vnb',Vtf',Vbl',)(:.Vh,)(;.Vh,)(<.Vh,)(=.Vh,)(>.(?.Vh,)Vc,Vxb,))")
(* [comment removed for export] *).   (* [comment removed for export] *)

  Hypothesis AWF : awf' h.
  Hypothesis GC : 1 <= c <= 30.
  (* [comment removed for export] *)
  Hypothesis HUU : UU = 0 \/ UU = kUserMapSize.
  Hypothesis HFF : FF = 0 \/ FF = kFreeArrayMapSize.
  Hypothesis MULIM : mu' <= kUserLimit.
  Hypothesis MFAB : mfa' <= kFreeArraySize.
  (* [comment removed for export] *)
  Hypothesis NW : 0 <= nw.
  Hypothesis AUMU : au' <= mu'.
  Hypothesis MUAU : mu' - au' <= 2^19.
  (* [comment removed for export] *)
  Hypothesis XBH : xb = a_exh (h_acct h) c \/ (xb = false /\ 1 <= nw /\ mu' - au' < cs).
  (* [comment removed for export] *)
  Hypothesis PERM : Permutation (fa' ++ cache') (fa_set h c ++ cache_set h c ++ newc cs cv nw).
  Hypothesis LFA : 4 * Z.of_nat (length fa') <= mfa'.
  Hypothesis WFX : mfa' <= 4 * (cv + nw) + kFreeArrayMapSize.
  Hypothesis LCA : Z.of_nat (length cache') <= max_count c.
  (* [comment removed for export] *)
  Hypothesis CO_ch : forall j, j <> c -> pc_chunks (cache_o j) = pc_chunks (h_cache h j).
  Hypothesis CO_hd : ltac2:(CDefT.buildp (gd_tbl_AW_FreePM3 ()) "Pj,$10.P,(11.(12.+1.R1.)(13.R1.$14.))P,(15.(16.$10.R2.Vc,))(11.(16.$10.(17.A1.Vcache_o,R3.)(18.R3.))(16.$10.(19.A1.Vcache_o,R3.)(1:.R3.)))")
(* [comment removed for export] *).
  (* [comment removed for export] *)
  Hypothesis DN : d_n (h_dep h) <= N' <= d_n (h_dep h) + 1.
  Hypothesis DTF : s_total (h_dep h) <= tf'.
  Hypothesis DLN : Z.of_nat (length nb') = N' / 65536 + 1.
  Hypothesis DWN : Forall (fun b => 0x65f000 <= b /\ b + 2^20 <= ACEIL /\ b mod 4096 = 0) nb'.
  Hypothesis DLB : Z.of_nat (length bl') = (tf' + 2^20 - 1) / 2^20.
  Hypothesis DWB : Forall (fun b => 0x65f000 <= b /\ b + 2^23 <= ACEIL /\ b mod 4096 = 0) bl'.
  Hypothesis DLNB : Z.of_nat (length nb') <= 32768.
  Hypothesis DLBB : Z.of_nat (length bl') <= 4096.

  #[using="hAR N' tf' nb' bl' fa' cache' GC"] Lemma CS16 : class_size c mod 16 = 0. Proof. apply class_size_mod16. lia. Qed.
  #[using="hAR N' tf' nb' bl' fa' cache' GC"] Lemma CSP : 32 <= class_size c. Proof. apply class_size_pos. lia. Qed.

  #[using="hAR N' tf' nb' bl' fa' cache' AWF GC"] Lemma cv_nonneg : 0 <= cv.
  Proof.
    dpose AWF as (_ & _ & WR & _). pose proof (WR c ltac:(unfold kNumClasses; lia)) as X. cbn zeta in X.
    ddestruct X as (_ & AU & AUCS & _). unfold cv, carved. apply Z.div_pos; [lia|]. pose proof CSP. lia.
  Qed.

  #[using="hAR N' tf' nb' bl' fa' cache' AWF GC"] Lemma au_cs : r_alloc_user r = cs * cv.
  Proof. dpose AWF as (_ & _ & WR & _). pose proof (WR c ltac:(unfold kNumClasses; lia)) as X. cbn zeta in X. ddestruct X as (_ & _ & AUCS & _). unfold r, cs, cv. exact AUCS. Qed.

  #[using="hAR AWF GC"] Lemma carved_rf : forall j, carved rf_h j = (if j =? c then cv + nw else carved h j).
  Proof.
    intros j. unfold carved. cbn [h_reg rf_h]. unfold rf_reg. destruct (Z.eqb_spec j c) as [->|NE]; [| reflexivity].
    cbn [r_alloc_user]. unfold au'. rewrite au_cs. fold cs. replace (cs * cv + nw * cs) with ((cv + nw) * cs) by lia.
    unfold cs. apply Z.div_mul. pose proof CSP. lia.
  Qed.

  #[using="Type"] Lemma chunk_set_rf : forall c', chunk_set rf_h c' = chunk_set h c'.
  Proof. intros c'. reflexivity. Qed.

  #[using="CO_ch"] Lemma cache_set_rf : forall c', cache_set rf_h c' = (if c' =? c then cache' else cache_set h c').
  Proof.
    intros c'. unfold cache_set. cbn [h_cache rf_h]. unfold rf_cache. destruct (Z.eqb_spec c' c) as [->|NE]; [reflexivity|].
    apply CO_ch. exact NE.
  Qed.

  #[using="Type"] Lemma fa_set_rf : forall c', fa_set rf_h c' = (if c' =? c then fa' else fa_set h c').
  Proof. intros c'. unfold fa_set. cbn [h_reg rf_h]. unfold rf_reg. destruct (c' =? c); reflexivity. Qed.

  #[using="Type"] Lemma batch_set_rf : forall c', batch_set rf_h c' = batch_set h c'.
  Proof. intros c'. reflexivity. Qed.

  #[using="CO_ch"] Lemma owned_rf_other : forall c', c' <> c -> owned rf_h c' = owned h c'.
  Proof.
    intros c' NE. unfold owned. rewrite cache_set_rf, chunk_set_rf, fa_set_rf, batch_set_rf.
    destruct (Z.eqb_spec c' c) as [->|_]; [exfalso; exact (NE eq_refl)| reflexivity].
  Qed.

  #[using="PERM CO_ch"] Lemma owned_rf_c : Permutation (owned rf_h c) (owned h c ++ newc cs cv nw).
  Proof.
    unfold owned. rewrite cache_set_rf, chunk_set_rf, fa_set_rf, batch_set_rf, Z.eqb_refl.
    transitivity ((fa' ++ cache') ++ (chunk_set h c ++ batch_set h c)).
    { rewrite <- !app_assoc. reflexivity. }
    transitivity ((fa_set h c ++ cache_set h c ++ newc cs cv nw) ++ (chunk_set h c ++ batch_set h c)).
    { apply Permutation_app_tail. exact PERM. }
    rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head.
    rewrite (app_assoc (chunk_set h c)). apply Permutation_app_comm.
  Qed.

  #[using="Type"] Lemma blocks_rf : blocks rf_h = blocks h.
  Proof. reflexivity. Qed.

  
  (* [comment removed for export] *)
  #[using="hAR N' tf' nb' bl' AWF GC NW PERM DLB"] Lemma owners_valid_rf : ltac2:(CDefT.buildp (gd_tbl_AW_FreePM3 ()) "(1;.$10.Lq,$10.(11.(12.=R1.)(1<.$10.Lk,$10.(11.(11.(12.=R1.)(13.R1.(1=.$1>.Vnw,)))(16.$10.(1?.+10.R2.)(1?.R1.(1:.Vc,))))))(20.$10.Vfa',Vcache',))")
(* [comment removed for export] *).
  Proof.
    dpose AWF as (_ & WC & WR & _). pose proof cv_nonneg as CV0.
    pose proof (WR c ltac:(unfold kNumClasses; lia)) as X. cbn zeta in X. ddestruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VFA & _).
    pose proof (WC c ltac:(unfold kNumClasses; lia)) as Y. cbn zeta in Y. ddestruct Y as (_ & _ & _ & _ & VCA).
    pose proof (Z.div_mod (class_size c) 16 ltac:(lia)) as D. rewrite CS16, Z.add_0_r in D.
    apply (Forall_perm _ _ _ (Permutation_sym PERM)). apply Forall_app; split; [| apply Forall_app; split].
    - apply Forall_forall. intros q Hq. pose proof (proj1 (Forall_forall _ _) VFA q Hq) as (Q0 & k & Hk & E). split; [exact Q0|]. exists k. unfold cv, r in *. split; [lia| exact E].
    - apply Forall_forall. intros q Hq. pose proof (proj1 (Forall_forall _ _) VCA q Hq) as (Q0 & k & Hk & E). split; [exact Q0|]. exists k. unfold cv in *. split; [lia| exact E].
    - apply Forall_forall. intros q Hq. apply (in_newc cs cv nw q NW) in Hq. ddestruct Hq as (k & Hk & ->). unfold cs in *. pose proof CSP as CP. split.
      + apply Z.div_pos; [| lia]. nia.
      + exists k. split; [lia|]. rewrite (div16_exact k _ CS16). lia.
  Qed.

  (* [comment removed for export] *)
  Hypothesis HX8 : c24_hid (c = kBatchClass -> 0 < nw -> carved h kBatchClass + nw <= CMAX24).
  #[using="AWF GC HUU HFF MULIM MFAB NW AUMU MUAU XBH PERM LFA WFX LCA CO_ch CO_hd DN DTF DLN DWN DLB DWB DLNB DLBB HX8"] Theorem awf'_rf : awf' rf_h.
  Proof.
    dpose AWF as (WL & WC & WR & (WKF & WKND & WKSEC) & WQ & WS & WD & WB & WBIG & WX & WG).
    pose proof cv_nonneg as CV0. pose proof au_cs as AUCS.
    pose proof (WR c ltac:(unfold kNumClasses; lia)) as WRc. cbn zeta in WRc. change (h_reg h c) with r in WRc.
    ddestruct WRc as (_ & AUMU0 & _ & MUAL & MULIM0 & _ & MFAL & MFAB0 & NF4 & VFA & OWN & PART).
    pose proof owners_valid_rf as OV. apply Forall_app in OV as [OVF OVC].
    pose proof (Z.div_mod (class_size c) 16 ltac:(lia)) as D16. rewrite CS16, Z.add_0_r in D16.
    split; [exact WL|].
    split. { (* [comment removed for export] *)
      intros c' Hc'. cbn zeta. cbn [h_cache h_cinit rf_h]. unfold rf_cache. rewrite carved_rf.
      destruct (Z.eqb_spec c' c) as [->|NEQ].
      - cbn [pc_max pc_csize pc_chunks]. unfold pc_count. cbn [pc_chunks].
        pose proof (max_count_range' c) as MCR.
        split; [intros _; split; reflexivity|]. split; [intros; lia|]. split; [lia|]. split; [lia|]. exact OVC.
      - pose proof (WC c' Hc') as X. cbn zeta in X. ddestruct X as (X1 & X2 & X3 & X4 & X5).
        unfold pc_count in *. rewrite (CO_ch c' NEQ).
        destruct (Z.leb_spec 1 c') as [LE|LT].
        + destruct (CO_hd c' ltac:(lia) NEQ) as [HM HS]. rewrite HM, HS.
          split; [intros _; split; reflexivity|].
          split; [exact X2|].
          split.
          * destruct (h_cinit h); [rewrite <- (proj1 (X1 LE)); exact X3|].
            destruct X1 as [M0 _]. rewrite M0 in X3. pose proof (max_count_range' c') as MR. lia.
          * split; [exact X4| exact X5].
        + (* [comment removed for export] *)
          assert (E0 : c' = 0) by lia. subst c'. rewrite (X2 eq_refl). cbn [length Z.of_nat].
          split; [intros; lia|]. split; [intros _; reflexivity|]. split; [lia|]. split; [lia| apply Forall_nil]. }
    split. { (* [comment removed for export] *)
      intros c' Hc'. cbn zeta. cbn [h_reg rf_h]. unfold rf_reg. rewrite carved_rf.
      destruct (Z.eqb_spec c' c) as [->|NEQ].
      - cbn [r_mapped_user r_alloc_user r_mapped_fa r_fa]. unfold r_nfreed. cbn [r_fa].
        split; [intros; lia|].
        split; [unfold au', mu', cs in *; pose proof CSP; nia|].
        split; [unfold au'; rewrite AUCS; unfold cs; lia|].
        split; [unfold mu'; unfold kUserMapSize in *; destruct HUU as [-> | ->]; [rewrite Z.add_0_r; exact MUAL| rewrite Z.add_mod, MUAL, Z.add_0_l by lia; reflexivity]|].
        split; [exact MULIM|].
        split; [intros _; exact MUAU|].
        split; [unfold mfa'; unfold kFreeArrayMapSize in *; destruct HFF as [-> | ->]; [rewrite Z.add_0_r; exact MFAL| rewrite Z.add_mod, MFAL, Z.add_0_l by lia; reflexivity]|].
        split; [unfold mfa' in *; destruct HFF as [X|X]; rewrite X in *; unfold kFreeArrayMapSize in *; lia|].
        split; [exact LFA|].
        split; [exact OVF|].
        split.
        + eapply Permutation_NoDup'; [apply Permutation_sym; exact owned_rf_c|]. apply NoDup_app; [exact OWN| apply NoDup_newc; [pose proof CSP; unfold cs; lia| exact CS16| exact CV0]|].
          intros x Hx Hn. apply (in_newc cs cv nw x NW) in Hn. ddestruct Hn as (k & Hk & ->).
          assert (IN : In (k * class_size c / 16) (owned h c)) by exact Hx. apply (proj2 (PART k)) in IN. unfold cv in *. lia.
        + intros k. rewrite (Permutation_in' eq_refl owned_rf_c), in_app_iff, (in_newc cs cv nw _ NW). split.
          * intros Hk. destruct (Z.lt_ge_cases k cv) as [LT|GE]; [left; apply (proj1 (PART k)); unfold cv in *; lia| right; exists k; split; [lia| reflexivity]].
          * intros [Hk|(k' & Hk' & E)]; [apply (proj2 (PART k)) in Hk; unfold cv in *; lia|].
            unfold cs in E. rewrite !(div16_exact _ _ CS16) in E. pose proof CSP as CP. assert (k = k') by nia. subst k'. lia.
      - pose proof (WR c' Hc') as X. cbn zeta in X. rewrite (owned_rf_other c' NEQ). exact X. }
    split. { (* [comment removed for export] *)
      split; [| split].
      - apply Forall_forall. intros k' Hk'. pose proof (proj1 (Forall_forall _ _) WKF k' Hk') as (W1 & W2 & W3 & W4).
          unfold wf_chunk'. rewrite carved_rf. change (h_L rf_h) with L. change (h_sec rf_h) with (h_sec h).
          split; [exact W1|]. split; [exact W2|]. split; [exact W3|].
          destruct (ck_prim k'); [| exact W4]. ddestruct W4 as (W5 & W6 & i & Hi & E). split; [exact W5|]. split; [exact W6|].
        exists i. split; [| exact E]. destruct (Z.eqb_spec (ck_cls k') c) as [EQ|NE]; [rewrite EQ in Hi; unfold cv; lia| lia].
      - exact WKND.
      - exact WKSEC. }
    split. { (* [comment removed for export] *)
      assert (FB : forall b, wf_batch h b -> wf_batch rf_h b).
      { (intros b dd_H; ddestruct dd_H as (B1 & B2 & B3 & B4)). unfold wf_batch. rewrite carved_rf. change (h_L rf_h) with L.
        cbn [h_chunks rf_h]. split; [exact B1|]. split; [exact B2| split; [exact B3|]].
        ddestruct B4 as (i & Hi & E). exists i. split; [| exact E]. destruct (Z.eqb_spec kBatchClass c) as [EQ|NE]; [rewrite EQ in Hi; unfold cv; lia| lia]. }
      ddestruct WQ as ((T1 & T2 & T3) & (G1 & G2 & G3) & ND & UQ).
      split; [split; [| split; [exact T2| exact T3]]| split; [split; [| split; [exact G2| exact G3]]| split; [exact ND|]]].
      - apply Forall_forall. intros b Hb. apply FB. exact (proj1 (Forall_forall _ _) T1 b Hb).
      - apply Forall_forall. intros b Hb. apply FB. exact (proj1 (Forall_forall _ _) G1 b Hb).
      - exact UQ. }
    split; [exact WS|].
    split. { (* [comment removed for export] *)
      ddestruct WD as (N1 & _ & _ & T0 & _). unfold wf_depot'. cbn [h_dep rf_h d_n d_nb s_total d_bl h_havol]. unfold kDepotNodesL2 in *.
      repeat split; try assumption; lia. }
    split. { (* [comment removed for export] *) ddestruct WB as (F1 & F2 & F3). split; [exact F1|]. cbn [h_havol rf_h]. change (SECC rf_h) with (SECC h). lia. }
    split; [exact WBIG|].
    split. { (* [comment removed for export] *)
      ddestruct WX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8h & X9h). assert (X8 : c24_hid (carved h kBatchClass <= CMAX24)) by exact X8h. assert (X9 : c24_hid (cnt24 (blocks h) <= C24MAX)) by exact X9h. clear X8h X9h.
      split; [| split; [exact X2| split; [intros E; discriminate E| split; [exact X4| split; [exact X5| split; [| split; [| split]]]]]]].
      { intros c' Hc'. cbn [h_reg rf_h]. unfold rf_reg. rewrite carved_rf. destruct (Z.eqb_spec c' c) as [->|NE]; [| exact (X1 c' Hc')].
        cbn [r_mapped_fa]. exact WFX. }
      - (* [comment removed for export] *) cbn [h_acct h_L rf_h a_emb a_esz acct_set_exh]. exact X6.
      - (* [comment removed for export] *)
        cbn [h_acct rf_h a_esz acct_set_exh]. eapply Z.le_trans; [exact X7|]. apply Z.mul_le_mono_nonneg_l; [unfold EM; clear; lia|].
        apply csum_le. intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE].
        2:{ rewrite (epi_frame h rf_h c'); [clear; lia| |]; cbn [h_reg h_acct rf_h acct_set_exh a_exh]; unfold rf_reg;
              destruct (Z.eqb_spec c' c) as [E|_]; [exfalso; exact (NE E)| reflexivity| exfalso; exact (NE E)| reflexivity]. }
        unfold epi, frozen. cbn [h_reg h_acct rf_h acct_set_exh a_exh]. unfold rf_reg. rewrite Z.eqb_refl. cbn [r_mapped_user r_alloc_user].
        fold r. pose proof CSP as CSP'. unfold mu', au', cs, kUserLimit, kUserMapSize in *. change (2^18) with 262144 in *.
        assert (NWC : 0 <= nw * class_size c) by (apply Z.mul_nonneg_nonneg; [exact NW| clear - CSP'; lia]).
        destruct XBH as [-> | (-> & NW1 & CA)].
        + repeat match goal with |- context [if ?a <? ?b then _ else _] => destruct (Z.ltb_spec a b) end;
          repeat match goal with |- context [if ?a <=? ?b then _ else _] => destruct (Z.leb_spec a b) end;
          destruct (a_exh (h_acct h) c); destruct HUU as [U0|U0]; rewrite U0 in *; lia.
        + assert (NWC1 : class_size c <= nw * class_size c) by (clear - NW1 CSP'; nia).
          repeat match goal with |- context [if ?a <? ?b then _ else _] => destruct (Z.ltb_spec a b) end;
          repeat match goal with |- context [if ?a <=? ?b then _ else _] => destruct (Z.leb_spec a b) end;
          destruct (a_exh (h_acct h) c); destruct HUU as [U0|U0]; rewrite U0 in *; lia.
      - (* [comment removed for export] *)
        unfold c24_hid in X8. rewrite carved_rf. destruct (Z.eqb_spec kBatchClass c) as [E|NE]; [| exact X8].
        destruct (Z.eq_dec nw 0) as [N0|N0]; [rewrite N0, Z.add_0_r; unfold cv; rewrite <- E; exact X8|].
        pose proof HX8 as B0. unfold c24_hid in B0. pose proof (B0 (eq_sym E) ltac:(clear - NW N0; lia)) as B. unfold cv. rewrite <- E. exact B.
      - (* [comment removed for export] *) unfold c24_hid in X9. rewrite blocks_rf. exact X9. }
    exact WG.
  Qed.

  End RfN.
End ARUN_1.
