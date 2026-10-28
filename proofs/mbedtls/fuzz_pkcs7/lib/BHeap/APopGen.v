(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModelX APop.
Import ListNotations.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Local Ltac Stdlib.micromega.Lia.nia ::= nia_ah.
Ltac2 gd_tbl_APopGen () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.iff"; "Stdlib.Lists.List.In"; "ARUN_1.newc"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.AH"; "ARUN_1.PopGen.L"; "ARUN_1.PopGen.gen_reg"; "ARUN_1.PopGen.gen_cache"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.chunk"; "ARUN_1.PopGen.newk"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_chunks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_tq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_gq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_sec"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.DP"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_ia"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_fake"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_pa_committed"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_havol"; "ARUN_1.acct_set_exh"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_acct"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kNumClasses"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.pc_max"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.max_count"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.pc_csize"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.class_size"; "Corelib.Lists.ListDef.Forall"; "ARUN_1.PopGen.cv"; "Corelib.Init.Datatypes.app"; "ARUN_1.PopGen.cs"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "ARUN_1.NullGrow.null_reg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_cache"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_cinit"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_dep"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.

#[using="Type"] Lemma Permutation_NoDup' : forall {A} (l l' : list A), Permutation l l' -> NoDup l -> NoDup l'.
Proof. intros A l l' P ND. eapply Permutation_NoDup; eauto. Qed.

#[using="Type"] Lemma Forall_perm : forall {A} (P : A -> Prop) (l l' : list A), Permutation l l' -> Forall P l -> Forall P l'.
Proof. intros A P l l' HP HF. apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall _ _) HF). eapply Permutation_in; [apply Permutation_sym; exact HP| exact Hx]. Qed.

#[using="Type"] Lemma div16_exact : forall k cs, cs mod 16 = 0 -> k * cs / 16 = k * (cs / 16).
Proof.
  intros k cs H. pose proof (Z.div_mod cs 16 ltac:(lia)) as D. rewrite H, Z.add_0_r in D.
  rewrite D at 1. replace (k * (16 * (cs / 16))) with (k * (cs / 16) * 16) by lia. apply Z_div_mult. lia.
Qed.

(* [comment removed for export] *)
Definition newc (cs cv nw : Z) : list Z := map (fun i => (cv + Z.of_nat i) * cs / 16) (seq 0 (Z.to_nat nw)).

#[using="Type"] Lemma in_newc : ltac2:(CDefT.buildp (gd_tbl_APopGen ()) "Pcs,$0.Pcv,$0.Pnw,$0.Px,$0.P,(1.=R2.)(2.(3.$0.R2.(4.R5.R4.R3.))(5.$0.Lk,$0.(6.(6.(1.R5.R1.)(7.R1.(8.R5.R4.)))(9.$0.R3.(:.(;.R1.R6.)+10.)))))")
(* [comment removed for export] *).
Proof.
  intros cs cv nw x NW. unfold newc. rewrite in_map_iff. split.
  - (intros dd_H; ddestruct dd_H as (i & <- & Hi)). apply in_seq in Hi. exists (cv + Z.of_nat i). split; [lia| reflexivity].
  - (intros dd_H; ddestruct dd_H as (k & Hk & ->)). exists (Z.to_nat (k - cv)). split; [f_equal; f_equal; lia|]. apply in_seq. lia.
Qed.

#[using="Type"] Lemma NoDup_newc : forall cs cv nw, 32 <= cs -> cs mod 16 = 0 -> 0 <= cv -> NoDup (newc cs cv nw).
Proof.
  intros cs cv nw CS C16 CV. unfold newc. apply (NoDup_map_NoDup_ForallPairs).
  - intros i j Hi Hj E. apply in_seq in Hi. apply in_seq in Hj.
    rewrite !(div16_exact _ _ C16) in E. pose proof (Z.div_mod cs 16 ltac:(lia)) as D. rewrite C16, Z.add_0_r in D. nia.
  - apply seq_NoDup.
Qed.


#[using="Type"] Lemma max_count_range' : forall c, 2 <= max_count c <= 16.
Proof. intros c. unfold max_count, max_cached. lia. Qed.

(* [comment removed for export] *)
Definition acct_set_exh (a : acct) (c : Z) (b : bool) : acct :=
  AC (a_sech a) (a_emb a) (a_esz a) (fun j => if j =? c then b else a_exh a j).

Section PopGen.
  Variable h : ahst.
  Variables (c n AB kab nw UU FF N' tf' : Z) (nb' bl' : list Z) (fa' cache' : list Z) (cache_o : Z -> pcl) (xb : bool).
  Definition L := h_L h.
  Definition r := h_reg h c.
  Definition cs := class_size c.
  Definition cv := carved h c.
  Definition mu' := r_mapped_user r + UU.
  Definition mfa' := r_mapped_fa r + FF.
  Definition au' := r_alloc_user r + nw * cs.

  Definition gen_reg (j : Z) : region := if j =? c then RG mu' au' mfa' fa' else h_reg h j.
  Definition gen_cache (j : Z) : pcl := if j =? c then PC (max_count c) (class_size c) cache' else cache_o j.
  Definition newk : chunk := CK AB n true c CHUNK_ALLOCATED.
  Definition gen_h : ahst := ltac2:(CDefT.buildp (gd_tbl_APopGen ()) "(<.$=.$>.$?.$10.(11.$12.$13.(14.Vh,))(15.Vh,)(16.Vh,)(17.Vh,)(18.VN',Vnb',Vtf',Vbl',)(19.Vh,)(1:.Vh,)(1;.Vh,)(1<.Vh,)(1=.(1>.Vh,)Vc,Vxb,))")
(* [comment removed for export] *).

  Hypothesis AWF : awf' h.
  Hypothesis GC : 1 <= c <= 30.
  Hypothesis NB : 0 <= n < 2^28.
  Hypothesis FP : from_primary n = true.
  Hypothesis EC : pclass n = c.
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
  Hypothesis KAB : 0 <= kab < cv + nw /\ AB = chunk_at L c kab.
  Hypothesis PERM : Permutation (fa' ++ cache' ++ [kab * cs / 16]) (fa_set h c ++ cache_set h c ++ newc cs cv nw).
  Hypothesis LFA : 4 * Z.of_nat (length fa') <= mfa'.
  Hypothesis WFX : mfa' <= 4 * (cv + nw) + kFreeArrayMapSize.
  Hypothesis LCA : Z.of_nat (length cache') <= max_count c - 1.
  (* [comment removed for export] *)
  Hypothesis CO_ch : forall j, j <> c -> pc_chunks (cache_o j) = pc_chunks (h_cache h j).
  Hypothesis CO_hd : ltac2:(CDefT.buildp (gd_tbl_APopGen ()) "Pj,$0.P,(6.(1.+1.R1.)(7.R1.$1?.))P,(20.(9.$0.R2.Vc,))(6.(9.$0.(21.A1.Vcache_o,R3.)(22.R3.))(9.$0.(23.A1.Vcache_o,R3.)(24.R3.)))")
(* [comment removed for export] *).
  (* [comment removed for export] *)
  Hypothesis OLDAP : Forall (fun k' => ck_end k' <= AB \/ AB + class_size c <= (if ck_prim k' then ck_ab k' else ck_map_beg k')) (h_chunks h).
  (* [comment removed for export] *)
  Hypothesis DN : d_n (h_dep h) <= N' <= d_n (h_dep h) + 1.
  Hypothesis DTF : s_total (h_dep h) <= tf'.
  Hypothesis DLN : Z.of_nat (length nb') = N' / 65536 + 1.
  Hypothesis DWN : Forall (fun b => 0x65f000 <= b /\ b + 2^20 <= ACEIL /\ b mod 4096 = 0) nb'.
  Hypothesis DLB : Z.of_nat (length bl') = (tf' + 2^20 - 1) / 2^20.
  Hypothesis DWB : Forall (fun b => 0x65f000 <= b /\ b + 2^23 <= ACEIL /\ b mod 4096 = 0) bl'.
  Hypothesis DLNB : Z.of_nat (length nb') <= 32768.
  Hypothesis DLBB : Z.of_nat (length bl') <= 4096.

  #[using="hAR n kab N' tf' nb' bl' fa' cache' GC NB"] Lemma CS16 : class_size c mod 16 = 0. Proof. apply class_size_mod16. lia. Qed.
  #[using="hAR n kab N' tf' nb' bl' fa' cache' GC NB"] Lemma CSP : 32 <= class_size c. Proof. apply class_size_pos. lia. Qed.

  #[using="hAR n kab N' tf' nb' bl' fa' cache' AWF GC NB"] Lemma cv_nonneg : 0 <= cv.
  Proof.
    dpose AWF as (_ & _ & WR & _). pose proof (WR c ltac:(unfold kNumClasses; lia)) as X. cbn zeta in X.
    ddestruct X as (_ & AU & AUCS & _). unfold cv, carved. apply Z.div_pos; [lia|]. pose proof CSP. lia.
  Qed.

  #[using="hAR n kab N' tf' nb' bl' fa' cache' AWF GC NB"] Lemma au_cs : r_alloc_user r = cs * cv.
  Proof. dpose AWF as (_ & _ & WR & _). pose proof (WR c ltac:(unfold kNumClasses; lia)) as X. cbn zeta in X. ddestruct X as (_ & _ & AUCS & _). unfold r, cs, cv. exact AUCS. Qed.

  #[using="hAR kab AWF GC NB"] Lemma carved_gen : forall j, carved gen_h j = (if j =? c then cv + nw else carved h j).
  Proof.
    intros j. unfold carved. cbn [h_reg gen_h]. unfold gen_reg. destruct (Z.eqb_spec j c) as [->|NE]; [| reflexivity].
    cbn [r_alloc_user]. unfold au'. rewrite au_cs. fold cs. replace (cs * cv + nw * cs) with ((cv + nw) * cs) by lia.
    unfold cs. apply Z.div_mul. pose proof CSP. lia.
  Qed.

  #[using="hAR n nw N' tf' nb' bl' fa' cache' GC NB KAB OLDAP"] Lemma compact_AB : compact L c AB = kab * cs / 16.
  Proof.
    destruct KAB as [_ ->]. unfold cs. rewrite compact_chunk_at by exact CS16. symmetry. apply div16_exact. exact CS16.
  Qed.

  #[using="Type"] Lemma chunk_set_gen : forall c', chunk_set gen_h c' = (if c' =? c then compact L c AB :: chunk_set h c' else chunk_set h c').
  Proof.
    intros c'. unfold chunk_set. cbn [h_chunks gen_h h_L filter ck_prim ck_cls newk andb].
    rewrite (Z.eqb_sym c c'). destruct (Z.eqb_spec c' c) as [->|NEQ]; reflexivity.
  Qed.

  #[using="CO_ch"] Lemma cache_set_gen : forall c', cache_set gen_h c' = (if c' =? c then cache' else cache_set h c').
  Proof.
    intros c'. unfold cache_set. cbn [h_cache gen_h]. unfold gen_cache. destruct (Z.eqb_spec c' c) as [->|NE]; [reflexivity|].
    apply CO_ch. exact NE.
  Qed.

  #[using="Type"] Lemma fa_set_gen : forall c', fa_set gen_h c' = (if c' =? c then fa' else fa_set h c').
  Proof. intros c'. unfold fa_set. cbn [h_reg gen_h]. unfold gen_reg. destruct (c' =? c); reflexivity. Qed.

  #[using="Type"] Lemma batch_set_gen : forall c', batch_set gen_h c' = batch_set h c'.
  Proof. intros c'. reflexivity. Qed.

  #[using="CO_ch"] Lemma owned_gen_other : forall c', c' <> c -> owned gen_h c' = owned h c'.
  Proof.
    intros c' NE. unfold owned. rewrite cache_set_gen, chunk_set_gen, fa_set_gen, batch_set_gen.
    destruct (Z.eqb_spec c' c) as [->|_]; [exfalso; exact (NE eq_refl)| reflexivity].
  Qed.

  #[using="hAR kab GC NB KAB PERM CO_ch OLDAP"] Lemma owned_gen_c : Permutation (owned gen_h c) (owned h c ++ newc cs cv nw).
  Proof.
    unfold owned. rewrite cache_set_gen, chunk_set_gen, fa_set_gen, batch_set_gen, Z.eqb_refl, compact_AB.
    transitivity ((fa' ++ cache' ++ [kab * cs / 16]) ++ (chunk_set h c ++ batch_set h c)).
    { rewrite <- !app_assoc. reflexivity. }
    transitivity ((fa_set h c ++ cache_set h c ++ newc cs cv nw) ++ (chunk_set h c ++ batch_set h c)).
    { apply Permutation_app_tail. exact PERM. }
    rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head.
    rewrite (app_assoc (chunk_set h c)). apply Permutation_app_comm.
  Qed.

  #[using="Type"] Lemma blocks_gen : blocks gen_h = (AB + rz_size n, n) :: blocks h.
  Proof. unfold blocks, live. cbn [h_chunks gen_h filter ck_st newk]. reflexivity. Qed.

  
  (* [comment removed for export] *)
  #[using="kab N' tf' nb' bl' fa' cache' GC NB FP EC OLDAP"] Lemma hdr_new_old_gen : forall k', In k' (h_chunks h) -> wf_chunk' h k' -> ck_hdr newk <> ck_hdr k'.
  Proof.
    intros k' Hk' W E. pose proof (hdr_in_slot h k' W) as [S1 S2]. pose proof (proj1 (Forall_forall _ _) OLDAP k' Hk') as AP. cbn beta in AP.
    unfold ck_hdr, ck_user, ck_rz, kChunkHeaderSize in E. cbn [ck_ab ck_n newk] in E.
    pose proof (rz_size_bound' n) as RZ. pose proof CSP.
    pose proof (needed_le_class n ltac:(lia) FP) as NC. rewrite EC in NC. unfold needed in NC. pose proof (rounded_spec n ltac:(lia)) as [R _].
    unfold ck_hdr, ck_user, ck_rz, kChunkHeaderSize in S1, S2. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="hAR n AB N' tf' nb' bl' AWF GC NB NW KAB PERM DLB"] Lemma owners_valid : ltac2:(CDefT.buildp (gd_tbl_APopGen ()) "(25.$0.Lq,$0.(6.(1.=R1.)(5.$0.Lk,$0.(6.(6.(1.=R1.)(7.R1.(8.$26.Vnw,)))(9.$0.(;.+10.R2.)(;.R1.(24.Vc,))))))(27.$0.Vfa',(27.$0.Vcache',(11.$0.(:.(;.Vkab,$28.)+10.)(29.$0.)))))")
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
  Hypothesis XC24 : c24_hid (win24 n = true -> cnt24 (blocks h) < C24MAX).
  Hypothesis HX8 : c24_hid (c = kBatchClass -> 0 < nw -> carved h kBatchClass + nw <= CMAX24).
  #[using="kab AWF GC NB FP EC HUU HFF MULIM MFAB NW AUMU MUAU XBH KAB PERM LFA WFX LCA CO_ch CO_hd OLDAP DN DTF DLN DWN DLB DWB DLNB DLBB XC24 HX8"] Theorem awf'_gen : awf' gen_h.
  Proof.
    dpose AWF as (WL & WC & WR & (WKF & WKND & WKSEC) & WQ & WS & WD & WB & WBIG & WX & WG).
    pose proof cv_nonneg as CV0. pose proof au_cs as AUCS.
    pose proof (WR c ltac:(unfold kNumClasses; lia)) as WRc. cbn zeta in WRc. change (h_reg h c) with r in WRc.
    ddestruct WRc as (_ & AUMU0 & _ & MUAL & MULIM0 & _ & MFAL & MFAB0 & NF4 & VFA & OWN & PART).
    pose proof owners_valid as OV. apply Forall_app in OV as [OVF OV]. apply Forall_app in OV as [OVC OVK].
    pose proof (Z.div_mod (class_size c) 16 ltac:(lia)) as D16. rewrite CS16, Z.add_0_r in D16.
    split; [exact WL|].
    split. { (* [comment removed for export] *)
      intros c' Hc'. cbn zeta. cbn [h_cache h_cinit gen_h]. unfold gen_cache. rewrite carved_gen.
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
      intros c' Hc'. cbn zeta. cbn [h_reg gen_h]. unfold gen_reg. rewrite carved_gen.
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
        + eapply Permutation_NoDup'; [apply Permutation_sym; exact owned_gen_c|]. apply NoDup_app; [exact OWN| apply NoDup_newc; [pose proof CSP; unfold cs; lia| exact CS16| exact CV0]|].
          intros x Hx Hn. apply (in_newc cs cv nw x NW) in Hn. ddestruct Hn as (k & Hk & ->).
          assert (IN : In (k * class_size c / 16) (owned h c)) by exact Hx. apply (proj2 (PART k)) in IN. unfold cv in *. lia.
        + intros k. rewrite (Permutation_in' eq_refl owned_gen_c), in_app_iff, (in_newc cs cv nw _ NW). split.
          * intros Hk. destruct (Z.lt_ge_cases k cv) as [LT|GE]; [left; apply (proj1 (PART k)); unfold cv in *; lia| right; exists k; split; [lia| reflexivity]].
          * intros [Hk|(k' & Hk' & E)]; [apply (proj2 (PART k)) in Hk; unfold cv in *; lia|].
            unfold cs in E. rewrite !(div16_exact _ _ CS16) in E. pose proof CSP as CP. assert (k = k') by nia. subst k'. lia.
      - pose proof (WR c' Hc') as X. cbn zeta in X. rewrite (owned_gen_other c' NEQ). exact X. }
    split. { (* [comment removed for export] *)
      split; [| split].
      - constructor.
        + unfold wf_chunk'. cbn [ck_n ck_st ck_prim ck_cls ck_ab newk]. rewrite carved_gen, Z.eqb_refl. change (h_L gen_h) with L.
          split; [lia|]. split; [left; reflexivity|]. split; [symmetry; exact FP|].
          split; [symmetry; exact EC|]. split; [exact GC|]. exists kab. exact KAB.
        + apply Forall_forall. intros k' Hk'. pose proof (proj1 (Forall_forall _ _) WKF k' Hk') as (W1 & W2 & W3 & W4).
          unfold wf_chunk'. rewrite carved_gen. change (h_L gen_h) with L. change (h_sec gen_h) with (h_sec h).
          split; [exact W1|]. split; [exact W2|]. split; [exact W3|].
          destruct (ck_prim k'); [| exact W4]. ddestruct W4 as (W5 & W6 & i & Hi & E). split; [exact W5|]. split; [exact W6|].
          exists i. split; [| exact E]. destruct (Z.eqb_spec (ck_cls k') c) as [EQ|NE]; [rewrite EQ in Hi; unfold cv; lia| lia].
      - cbn [map h_chunks gen_h ck_ab newk]. constructor; [| exact WKND].
        intros HIN. apply in_map_iff in HIN. ddestruct HIN as (k' & E & Hk').
        pose proof (proj1 (Forall_forall _ _) OLDAP k' Hk') as AP. cbn beta in AP.
        pose proof (proj1 (Forall_forall _ _) WKF k' Hk') as W. pose proof (hdr_in_slot h k' W) as [S1 S2].
        unfold ck_hdr, ck_user, ck_rz, ck_map_beg, kChunkHeaderSize in *. pose proof (rz_size_bound' (ck_n k')). pose proof CSP.
        destruct (ck_prim k'); lia.
      - intros i sh Hi. ddestruct (WKSEC i sh Hi) as (k' & Hk' & REST). exists k'. split; [right; exact Hk'| exact REST]. }
    split. { (* [comment removed for export] *)
      assert (FB : forall b, wf_batch h b -> wf_batch gen_h b).
      { (intros b dd_H; ddestruct dd_H as (B1 & B2 & B3 & B4)). unfold wf_batch. rewrite carved_gen. change (h_L gen_h) with L.
        cbn [h_chunks gen_h]. split; [exact B1|]. split; [| split].
        - rewrite B2. f_equal. f_equal. apply map_ext_in. intros e He. cbn [find].
          destruct (Z.eqb_spec (ck_hdr newk) e) as [E|NEQ]; [| reflexivity].
          exfalso. destruct (proj1 (Forall_forall _ _) B3 e He) as (k0 & Hk0 & _ & Hh). apply (hdr_new_old_gen k0 Hk0 (proj1 (Forall_forall _ _) WKF k0 Hk0)). congruence.
        - apply Forall_forall. intros e He. destruct (proj1 (Forall_forall _ _) B3 e He) as (k0 & Hk0 & R). exists k0. split; [right; exact Hk0| exact R].
        - ddestruct B4 as (i & Hi & E). exists i. split; [| exact E]. destruct (Z.eqb_spec kBatchClass c) as [EQ|NE]; [rewrite EQ in Hi; unfold cv; lia| lia]. }
      ddestruct WQ as ((T1 & T2 & T3) & (G1 & G2 & G3) & ND & UQ).
      split; [split; [| split; [exact T2| exact T3]]| split; [split; [| split; [exact G2| exact G3]]| split; [exact ND|]]].
      - apply Forall_forall. intros b Hb. apply FB. exact (proj1 (Forall_forall _ _) T1 b Hb).
      - apply Forall_forall. intros b Hb. apply FB. exact (proj1 (Forall_forall _ _) G1 b Hb).
      - intros k0 [<-|Hk0] ST; [cbv in ST; discriminate ST|]. exact (UQ k0 Hk0 ST). }
    split; [exact WS|].
    split. { (* [comment removed for export] *)
      ddestruct WD as (N1 & _ & _ & T0 & _). unfold wf_depot'. cbn [h_dep gen_h d_n d_nb s_total d_bl h_havol]. unfold kDepotNodesL2 in *.
      repeat split; try assumption; lia. }
    split. { (* [comment removed for export] *) ddestruct WB as (F1 & F2 & F3). split; [exact F1|]. cbn [h_havol gen_h]. change (SECC gen_h) with (SECC h). lia. }
    split; [exact WBIG|].
    split. { (* [comment removed for export] *)
      ddestruct WX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8h & X9h). assert (X8 : c24_hid (carved h kBatchClass <= CMAX24)) by exact X8h. assert (X9 : c24_hid (cnt24 (blocks h) <= C24MAX)) by exact X9h. clear X8h X9h.
      split; [| split; [exact X2| split; [intros E; discriminate E| split; [exact X4| split; [exact X5| split; [| split; [| split]]]]]]].
      { intros c' Hc'. cbn [h_reg gen_h]. unfold gen_reg. rewrite carved_gen. destruct (Z.eqb_spec c' c) as [->|NE]; [| exact (X1 c' Hc')].
        cbn [r_mapped_fa]. exact WFX. }
      - (* [comment removed for export] *) cbn [h_acct h_L gen_h a_emb a_esz acct_set_exh]. exact X6.
      - (* [comment removed for export] *)
        cbn [h_acct gen_h a_esz acct_set_exh]. eapply Z.le_trans; [exact X7|]. apply Z.mul_le_mono_nonneg_l; [unfold EM; clear; lia|].
        apply csum_le. intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE].
        2:{ rewrite (epi_frame h gen_h c'); [clear; lia| |]; cbn [h_reg h_acct gen_h acct_set_exh a_exh]; unfold gen_reg;
              destruct (Z.eqb_spec c' c) as [E|_]; [exfalso; exact (NE E)| reflexivity| exfalso; exact (NE E)| reflexivity]. }
        unfold epi, frozen. cbn [h_reg h_acct gen_h acct_set_exh a_exh]. unfold gen_reg. rewrite Z.eqb_refl. cbn [r_mapped_user r_alloc_user].
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
        unfold c24_hid in X8. rewrite carved_gen. destruct (Z.eqb_spec kBatchClass c) as [E|NE]; [| exact X8].
        destruct (Z.eq_dec nw 0) as [N0|N0]; [rewrite N0, Z.add_0_r; unfold cv; rewrite <- E; exact X8|].
        pose proof HX8 as B0. unfold c24_hid in B0. pose proof (B0 (eq_sym E) ltac:(clear - NW N0; lia)) as B. unfold cv. rewrite <- E. exact B.
      - (* [comment removed for export] *)
        unfold c24_hid in X9. pose proof XC24 as B0. unfold c24_hid in B0. rewrite blocks_gen, cnt24_cons. cbn [snd]. destruct (win24 n) eqn:W; [pose proof (B0 eq_refl) as B; clear - B; lia| clear - X9; lia].
    }
    exact WG.
  Qed.

  End PopGen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section NullGrow.
  Variable h : ahst.
  Variables (c UU : Z) (xb : bool).
  Definition rN := h_reg h c.
  Definition null_reg (j : Z) : region := if j =? c then RG (r_mapped_user rN + UU) (r_alloc_user rN) (r_mapped_fa rN) (r_fa rN) else h_reg h j.
  Definition null_h : ahst := ltac2:(CDefT.buildp (gd_tbl_APopGen ()) "(<.(2:.Vh,)$2;.(2<.Vh,)(2=.Vh,)(14.Vh,)(15.Vh,)(16.Vh,)(17.Vh,)(2>.Vh,)(19.Vh,)(1:.Vh,)(1;.Vh,)(1<.Vh,)(1=.(1>.Vh,)Vc,Vxb,))")
(* [comment removed for export] *).

  Hypothesis AWF : awf' h.
  Hypothesis GC : 1 <= c <= 30.
  Hypothesis HUU : UU = 0 \/ UU = kUserMapSize.
  Hypothesis MULIM : r_mapped_user rN + UU <= kUserLimit.
  Hypothesis MUAU : r_mapped_user rN + UU - r_alloc_user rN <= 2^19.
  (* [comment removed for export] *)
  Hypothesis XBN : xb = a_exh (h_acct h) c \/ xb = true.

  #[using="Type"] Lemma carved_null : forall j, carved null_h j = carved h j.
  Proof. intros j. unfold carved. cbn [h_reg null_h]. unfold null_reg. destruct (Z.eqb_spec j c) as [->|]; reflexivity. Qed.
  #[using="Type"] Lemma owned_null : forall j, owned null_h j = owned h j.
  Proof.
    intros j. unfold owned, fa_set, cache_set, chunk_set, batch_set. cbn [h_reg h_cache h_chunks h_tq h_gq h_L null_h]. unfold null_reg.
    destruct (Z.eqb_spec j c) as [->|]; reflexivity.
  Qed.
  #[using="Type"] Lemma blocks_null : blocks null_h = blocks h. Proof. reflexivity. Qed.
  
  #[using="AWF GC HUU MULIM MUAU XBN"] Theorem awf'_null : awf' null_h.
  Proof.
    dpose AWF as (WL & WC & WR & WK & WQ & WS & WD & WB & WBIG & WX & WG).
    split; [exact WL|].
    split. { intros c' Hc'. pose proof (WC c' Hc') as X. cbn zeta in X |- *. cbn [h_cache h_cinit null_h]. rewrite carved_null. exact X. }
    split. { intros c' Hc'. pose proof (WR c' Hc') as X. cbn zeta in X |- *. cbn [h_reg null_h]. unfold null_reg. rewrite carved_null, owned_null.
      destruct (Z.eqb_spec c' c) as [->|NE]; [| exact X].
      fold rN in X. ddestruct X as (X0 & X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11).
      cbn [r_mapped_user r_alloc_user r_mapped_fa r_fa]. unfold r_nfreed in *. cbn [r_fa].
      split; [intros; lia|]. split; [destruct HUU as [-> | ->]; unfold kUserMapSize in *; lia|]. split; [exact X2|].
      split; [unfold kUserMapSize in *; destruct HUU as [-> | ->]; [rewrite Z.add_0_r; exact X3| rewrite Z.add_mod, X3, Z.add_0_l by lia; reflexivity]|].
      split; [exact MULIM|]. split; [intros _; exact MUAU|]. repeat (split; [assumption|]). exact X11. }
    split. { ddestruct WK as (WKF & WKND & WKSEC). split; [| split; [exact WKND| exact WKSEC]].
      apply Forall_forall. intros k' Hk'. pose proof (proj1 (Forall_forall _ _) WKF k' Hk') as (W1 & W2 & W3 & W4).
      unfold wf_chunk'. rewrite carved_null. change (h_L null_h) with (h_L h). change (h_sec null_h) with (h_sec h).
      split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. exact W4. }
    split. { ddestruct WQ as ((T1 & T2 & T3) & (G1 & G2 & G3) & ND & UQ).
      assert (FB : forall b, wf_batch h b -> wf_batch null_h b).
      { (intros b dd_H; ddestruct dd_H as (B1 & B2 & B3 & B4)). unfold wf_batch. rewrite carved_null. change (h_L null_h) with (h_L h). change (h_chunks null_h) with (h_chunks h).
        split; [exact B1|]. split; [exact B2|]. split; [exact B3| exact B4]. }
      split; [split; [| split; [exact T2| exact T3]]| split; [split; [| split; [exact G2| exact G3]]| split; [exact ND| exact UQ]]];
        apply Forall_forall; intros b Hb; apply FB; [exact (proj1 (Forall_forall _ _) T1 b Hb)| exact (proj1 (Forall_forall _ _) G1 b Hb)]. }
    split; [exact WS|]. split; [exact WD|]. split; [exact WB|]. split; [exact WBIG|].
    split. { ddestruct WX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8h & X9h). assert (X8 : c24_hid (carved h kBatchClass <= CMAX24)) by exact X8h. assert (X9 : c24_hid (cnt24 (blocks h) <= C24MAX)) by exact X9h. clear X8h X9h.
      split; [| split; [exact X2| split; [| split; [exact X4| split; [exact X5| split; [| split; [| split; [unfold c24_hid in X8; rewrite carved_null; exact X8| unfold c24_hid in X9; rewrite blocks_null; exact X9]]]]]]]].
      3:{ cbn [h_acct h_L null_h a_emb a_esz acct_set_exh]. exact X6. }
      3:{ cbn [h_acct null_h a_esz acct_set_exh]. eapply Z.le_trans; [exact X7|]. apply Z.mul_le_mono_nonneg_l; [unfold EM; clear; lia|].
          apply csum_le. intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE].
          2:{ rewrite (epi_frame h null_h c'); [clear; lia| |]; cbn [h_reg h_acct null_h acct_set_exh a_exh]; unfold null_reg;
                destruct (Z.eqb_spec c' c) as [E|_]; [exfalso; exact (NE E)| reflexivity| exfalso; exact (NE E)| reflexivity]. }
          unfold epi, frozen. cbn [h_reg h_acct null_h acct_set_exh a_exh]. unfold null_reg. rewrite Z.eqb_refl. cbn [r_mapped_user r_alloc_user]. fold rN.
          unfold kUserLimit, kUserMapSize in *. change (2^18) with 262144 in *.
          destruct XBN as [-> | ->];
          repeat match goal with |- context [if ?a <? ?b then _ else _] => destruct (Z.ltb_spec a b) end;
          repeat match goal with |- context [if ?a <=? ?b then _ else _] => destruct (Z.leb_spec a b) end;
          destruct (a_exh (h_acct h) c); destruct HUU as [U0|U0]; rewrite U0 in *; lia. }
      - intros c' Hc'. cbn [h_reg null_h]. unfold null_reg. rewrite carved_null. destruct (Z.eqb_spec c' c) as [->|NE]; [cbn [r_mapped_fa]; fold rN| exact (X1 c' Hc')]. exact (X1 c Hc').
      - intros E c' Hc'. cbn [h_reg null_h]. unfold null_reg. destruct (Z.eqb_spec c' c) as [->|NE]; [cbn [r_alloc_user]; fold rN| exact (X3 E c' Hc')]. exact (X3 E c Hc'). }
    exact WG.
  Qed.
End NullGrow.

End ARUN_1.
