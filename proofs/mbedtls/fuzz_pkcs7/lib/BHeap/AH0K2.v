(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AxSymExec3Sound. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanCertDefs. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AsanPlanCore AsanPlan AsanPlanSound AsanAcct AsanInit AsanMainEntryKit. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanMainEntryFacts AsanMainEntryLemmas. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AsanNodesMmB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm AVst AHeapR AH0Spec0 AH0Base AH0Layout AH0Pure AH0Vwf AH0K.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import APS.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_AH0K2 () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlanSound.APS.seps"; "Stdlib.Lists.List.In"; "Stdlib.ZArith.BinInt.Z.lt"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.snd"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Logic.and"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.lowhigh"; "K2.FOG"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.trange"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.tr_of"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.node_tr"; "RocqVerifyHarness.AgentSubmission.BHeap.AH0Base.PG"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_dnodes"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.store_tr"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_dstore"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.ri_tr"; "RocqVerifyHarness.AgentSubmission.BHeap.AH0Spec0.L0_of"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.TR"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_thr"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.KEager"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_treg"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_fstk"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kFakeBytes"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_dtls"; "Corelib.Lists.ListDef.map"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.xkind"; "Corelib.Init.Datatypes.false"; "RocqVerifyHarness.AgentSubmission.BHeap.AH0Layout.EXTRA"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.KLazy"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.KNoacc"; "zz"; "LinuxProcessSemantics.LinuxProcessSem.Run.segments_reserved"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanCertDefs.ASEGS"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.cover_of"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_prim"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.kPrimHullLen"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_secv"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.kPaHullLen"; "RocqVerifyHarness.AgentSubmission.BHeap.AH0Vwf.SH3"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_lla"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_ictx"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_tvec"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_gvec"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_divec"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_lo"; "RocqVerifyHarness.AgentSubmission.BHeap.AH0Vwf.AL0"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_hi"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.State.page_in_ranges"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.csranges"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.zpb"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.shadow_of"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vgood"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.aok_addr"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vcs"; "LinuxProcessSemantics.LinuxProcessSem.State.page_base_of"].


(* [comment removed for export] *)
Definition zz (iv : word * word) : Z * Z := (bv_unsigned (fst iv), bv_unsigned (snd iv)).

(* [comment removed for export] *)
Lemma seps_app_inv : forall a b, seps (a ++ b) -> seps a /\ seps b /\ (forall x y, In x a -> In y b -> iv_disjoint x y).
Proof.
  induction a as [|e a IH]; intros b H; cbn in H.
  - split; [constructor|]. split; [exact H|]. intros x y [].
  - apply seps_cons_inv' in H as [F S]. ddestruct (IH b S) as (Sa & Sb & X). apply Forall_app in F as [Fa Fb].
    split; [constructor; [exact Fa| exact Sa]|]. split; [exact Sb|].
    intros x y [<-|Hx] Hy; [exact (proj1 (Forall_forall _ _) Fb y Hy) | exact (X x y Hx Hy)].
Qed.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L3699512445.900000;S1h2e21D2e1". (* [comment removed for export] *)
Lemma seps_pairwise : ltac2:(CDefT.buildp (gd_tbl_AH0K2 ()) "Pl,(0.(1.(2.&40.)(2.&40.)))P,(3.R1.)P,Piv,(1.(2.&40.)(2.&40.))P,(4.(1.(2.&40.)(2.&40.))R1.R3.)(5.=(6.&40.(7.(2.&40.)(2.&40.)R2.)))Pe1,(1.(2.&40.)(2.&40.))Pe2,(1.(2.&40.)(2.&40.))P,(4.(1.(2.&40.)(2.&40.))R2.R5.)P,(4.(1.(2.&40.)(2.&40.))R2.R6.)(8.(9.(1.(2.&40.)(2.&40.))R4.R3.)(8.(:.(;.(6.&40.(<.(2.&40.)(2.&40.)R4.))(6.&40.(7.(2.&40.)(2.&40.)R4.)))(6.&40.(<.(2.&40.)(2.&40.)R3.)))(:.(;.(6.&40.(<.(2.&40.)(2.&40.)R3.))(6.&40.(7.(2.&40.)(2.&40.)R3.)))(6.&40.(<.(2.&40.)(2.&40.)R4.)))))")
(* [comment removed for export] *).
Proof.
  induction l as [|h t IH]; intros Hs Hpos e1 e2 H1 H2; [destruct H1|].
  apply seps_cons_inv' in Hs as [Hf Ht].
  destruct H1 as [<-|H1]; destruct H2 as [<-|H2].
  - left; reflexivity.
  - right. pose proof (proj1 (Forall_forall _ _) Hf e2 H2) as D. unfold iv_disjoint in D. lia.
  - right. pose proof (proj1 (Forall_forall _ _) Hf e1 H1) as D. unfold iv_disjoint in D. lia.
  - apply IH; auto. intros iv Hiv. apply Hpos. right. exact Hiv.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L24928565580.3000008S1n1H2H0". (* [comment removed for export] *)
Lemma xkind_small : forall n, n < 2^17 -> xkind n = KNoacc.
Proof. intros n H. unfold xkind. destruct (Z.ltb_spec n (2^17)); [reflexivity| lia]. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L24928565580.3000008S1n1H2H0". (* [comment removed for export] *)
Lemma xkind_big : forall n, 2^17 <= n -> xkind n = KLazy.
Proof. intros n H. unfold xkind. destruct (Z.ltb_spec n (2^17)); [lia| reflexivity]. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section K2.
  Context {hAR : arun}.
  Variables (sp : word) (fs : Fs.Fs) (p : me_params).
  Hypothesis HCN : Forall cnst_ok (me_cnsts p).
  Variables (STKHI TF : Z) (md : Model) (fog : list (word * word)).
  Hypothesis HMOD : me_model sp fs p md.
  Hypothesis HAC : ACEIL = STKPG p - 0x800000.
  Hypothesis HSP : bv_unsigned sp = SP p.
  Hypothesis HFOG : vm_maps (m_vmmaps md) = me_maps_new p ++ fog ++ me_maps_old p.

  Definition FOG : list (Z * Z) := map zz fog.
  Let bp := bp_of p STKHI FOG TF.
  Let h0 := h0_of bp.
  Let v0 := vst_of h0.
  Let M := vm_maps (m_vmmaps md).
  Let N := vm_noaccess (m_vmmaps md).
  Let Lz := m_vm_lazy md.
  Local Ltac pv := cbn; tauto.

  (* [comment removed for export] *)
  Local Ltac mm X :=
    pose proof HMOD as X; unfold me_model in X;
    destruct X as (Mhalt & Mfds & Mfs & Mres & Mlim & Mfog & Mseps & Mwf & Mbounds & Mlazyb & Mnasub & MNsecv & MNgap
                   & MAdstore & MAhigh & MAlow & Mtot & Misp & Mbrk & Msbrk & Meager & Mabytes & Mminv & MNcov & MLcov
                   & Ndivec & Ngvec & Ndstore & Ndnodes & Nfstk & Ndtls & Ntvec & Ntreg & Nthr & Nictx & Nlla & Nhigh & Nlow
                   & Ldivec & Lgvec & Ldnodes & Lfstk & Ldtls & Ltvec & Ltreg & Lthr & Lictx & Llla & Mri & K5secv & K5prim & K5gap).   (* [comment removed for export] *)
  Local Ltac uvals := rewrite ?(u_divec p HCN), ?(u_gvec p HCN), ?(u_dstore p HCN), ?(u_dnodes p HCN), ?(u_fstk p HCN), ?(u_dtls p HCN),
    ?(u_tvec p HCN), ?(u_treg p HCN), ?(u_thr p HCN), ?(u_ictx p HCN), ?(u_lla p HCN), ?(u_tmpv p HCN), ?(u_mus1 p HCN), ?(u_mus2 p HCN),
    ?(u_prim p HCN), ?(u_secv p HCN), ?(u_brk0pg p HCN), ?(u_mus1p p HCN), ?(u_ri p HCN), ?(u_stkb p HCN HAC), ?(u_stkn p HCN HAC) in *;
    rewrite ?(u_wlit p) in * by lia.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="sp fs p HMOD"] Lemma M_pos : forall iv, In iv M -> 0 < bv_unsigned (snd iv).
  Proof. mm X. exact (bounds_pos _ _ Mbounds). Qed.
  #[using="sp fs p HMOD"] Lemma M_seps : seps M.
  Proof. mm X. exact Mseps. Qed.
  #[using="sp fs p HMOD"] Lemma M_disj : forall x y, In x M -> In y M -> x <> y -> iv_disjoint x y.
  Proof. intros x y Hx Hy Hne. exact (seps_In_disjoint' M x y M_seps M_pos Hx Hy Hne). Qed.
  #[using="sp fs p HMOD"] Lemma M_nodup : List.NoDup M.
  Proof. exact (seps_NoDup M M_seps M_pos). Qed.
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L18433093931.83L18926383094.80L18926563191.81L19585141836.7 L7109197814.82 00000:00D00N00c00mS3hAR1p2ivS3hAR1p2ivS3hAR1p2ivS1p2iv2B52D12D22D32M3S3hAR1p2iv". (* [comment removed for export] *)
  #[using="sp fs p HCN HMOD HAC HSP"] Lemma M_bounds : ltac2:(CDefT.buildp (gd_tbl_AH0K2 ()) "Piv,(1.(2.&40.)(2.&40.))P,(4.(1.(2.&40.)(2.&40.))R1.VM,)(=.(5.=(6.&40.(7.(2.&40.)(2.&40.)R2.)))(=.(9.$>.(?.(6.&40.(<.(2.&40.)(2.&40.)R2.))+1000.)=)(=.(9.$>.(?.(6.&40.(7.(2.&40.)(2.&40.)R2.))+1000.)=)(=.(8.(:.(;.(6.&40.(<.(2.&40.)(2.&40.)R2.))(6.&40.(7.(2.&40.)(2.&40.)R2.)))+10000.)(:.+65?000.(6.&40.(<.(2.&40.)(2.&40.)R2.))))(=.(:.(;.(6.&40.(<.(2.&40.)(2.&40.)R2.))(6.&40.(7.(2.&40.)(2.&40.)R2.)))(10.VhAR,))(5.=(6.&40.(<.(2.&40.)(2.&40.)R2.))))))))")
(* [comment removed for export] *).
  Proof.
    intros iv Hiv. mm X. pose proof (proj1 (Forall_forall _ _) Mbounds iv Hiv) as (B1 & B2 & B3 & B4 & B5 & B6).
    rewrite HSP in B5. repeat split; try assumption.
    (* [comment removed for export] *)
    pose proof (r_s2 p HCN) as S2. rewrite HAC. unfold SP, STKPG in *.
    pose proof (Z.div_mod (bv_unsigned (fst iv)) 4096 ltac:(lia)) as D1. pose proof (Z.div_mod (bv_unsigned (snd iv)) 4096 ltac:(lia)) as D2.
    rewrite B2, Z.add_0_r in D1. rewrite B3, Z.add_0_r in D2.
    pose proof (Z.div_mod (uv p v_s2) 256 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (uv p v_s2) 256 ltac:(lia)) as M3.
    clear - B5 D1 D2 D3 M3. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L3699512445.2600000;S3hAR1x1y1D". (* [comment removed for export] *)
  #[using="hAR sp fs md HMOD HFOG M"] Lemma fog_disj : forall x y, In x fog -> In y (me_maps_new p ++ me_maps_old p) -> iv_disjoint x y.
  Proof.
    intros x y Hx Hy. pose proof M_seps as S. unfold M in S. rewrite HFOG in S.
    apply seps_app_inv in S as (_ & S2 & X1). apply seps_app_inv in S2 as (_ & _ & X2).
    apply in_app_iff in Hy as [Hy|Hy].
    - pose proof (X1 y x Hy ltac:(apply in_app_iff; left; exact Hx)) as D. unfold iv_disjoint in *. lia.
    - exact (X2 x y Hx Hy).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="sp fs p md HMOD HFOG M"] Lemma fog_seps_w : seps fog.
  Proof. pose proof M_seps as S. unfold M in S. rewrite HFOG in S. apply seps_app_inv in S as (_ & S2 & _). apply seps_app_inv in S2 as (S & _ & _). exact S. Qed.
  #[using="p HFOG"] Lemma fog_in_M : forall x, In x fog -> In x M.
  Proof. intros x Hx. unfold M. rewrite HFOG. apply in_app_iff. right. apply in_app_iff. left. exact Hx. Qed.
  #[using="fog HFOG"] Lemma new_in_M : forall x, In x (me_maps_new p) -> In x M.
  Proof. intros x Hx. unfold M. rewrite HFOG. apply in_app_iff. left. exact Hx. Qed.
  #[using="fog HFOG"] Lemma old_in_M : forall x, In x (me_maps_old p) -> In x M.
  Proof. intros x Hx. unfold M. rewrite HFOG. apply in_app_iff. right. apply in_app_iff. right. exact Hx. Qed.

  (* [comment removed for export] *)
  #[using="fog HFOG"] Lemma new_nth : forall i e, nth_error MAPS_NEW i = Some e -> In (pinst p e) M.
  Proof. intros i e H. apply new_in_M. unfold me_maps_new. apply in_map. exact (nth_error_In _ i H). Qed.
  #[using="fog HFOG"] Lemma old_nth : forall i e, nth_error MAPS_OLD i = Some e -> In (pinst p e) M.
  Proof. intros i e H. apply old_in_M. unfold me_maps_old. apply in_map. exact (nth_error_In _ i H). Qed.
  #[using="hAR sp fs md HMOD HFOG M"] Lemma fog_disj_new : forall x i e, In x fog -> nth_error MAPS_NEW i = Some e -> iv_disjoint x (pinst p e).
  Proof. intros x i e Hx H. apply (fog_disj x _ Hx). apply in_app_iff. left. unfold me_maps_new. apply in_map. exact (nth_error_In _ i H). Qed.
  #[using="hAR sp fs md HMOD HFOG M"] Lemma fog_disj_old : forall x i e, In x fog -> nth_error MAPS_OLD i = Some e -> iv_disjoint x (pinst p e).
  Proof. intros x i e Hx H. apply (fog_disj x _ Hx). apply in_app_iff. right. unfold me_maps_old. apply in_map. exact (nth_error_In _ i H). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L18928660343.30L19582022821.31L59579257137.30L59899878056.3100000700R00Y00iS3hAR1xS3hAR1x2B12B42D93D103D112D1S3hAR1xS3hAR1x2B12B62D1". (* [comment removed for export] *)
  #[using="sp fs p HCN md HMOD HAC HSP HFOG M"] Lemma fog_ok : ltac2:(CDefT.buildp (gd_tbl_AH0K2 ()) "(11.(1.$>.$>.)Lr,(1.$>.$>.)(=.(12.(<.$>.$>.R1.)(7.$>.$>.R1.))(=.(5.=(7.$>.$>.R1.))(=.(:.(;.(<.$>.$>.R1.)(7.$>.$>.R1.))(10.VhAR,))(=.(9.$>.(?.(<.$>.$>.R1.)+1000.)=)(9.$>.(?.(7.$>.$>.R1.)+1000.)=)))))$13.)")
(* [comment removed for export] *).
  Proof.
    unfold FOG. apply Forall_map. apply Forall_forall. intros x Hx. unfold zz. cbn [fst snd].
    ddestruct (M_bounds x (fog_in_M x Hx)) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (fog_disj_old x 9 _ Hx eq_refl) as D9. pose proof (fog_disj_old x 10 _ Hx eq_refl) as D10. pose proof (fog_disj_old x 11 _ Hx eq_refl) as D11.
    unfold iv_disjoint, pinst in D9, D10, D11. cbn [fst snd] in D9, D10, D11. rewrite !(u_wlit p) in D9, D10, D11 by lia.
    unfold lowhigh, kHighMemBeg. pose proof (Z.div_mod (bv_unsigned (fst x)) 4096 ltac:(lia)) as D1. rewrite B2, Z.add_0_r in D1.
    repeat split; try assumption; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L3705736066.2600000<S3hAR1e1y2Hy". (* [comment removed for export] *)
  #[using="hAR"] Lemma seps_zseps : forall l, seps l -> zseps (map zz l).
  Proof.
    induction l as [|e l IH]; intros H; cbn; [constructor|]. apply seps_cons_inv' in H as [F S]. constructor; [| exact (IH S)].
    apply Forall_map. eapply Forall_impl; [| exact F]. intros y Hy. unfold zap, zz, iv_disjoint in *. cbn [fst snd]. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="hAR sp fs p md HMOD HFOG M"] Lemma fog_seps : zseps FOG.
  Proof. unfold FOG. apply seps_zseps. exact fog_seps_w. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L44668082586.22L59583457926.2200000;00@S3hAR1p1f1DS3hAR". (* [comment removed for export] *)
  #[using="hAR sp fs HCN md HMOD HFOG M"] Lemma fog_apart : forall r x, In r FOG -> In x PGOBJS -> zap r (pgz p x).
  Proof.
    intros r x Hr Hx. unfold FOG in Hr. apply in_map_iff in Hr as (f & <- & Hf). unfold zap, zz, pgz.
    Ltac fap H := unfold iv_disjoint, pinst in H; cbn [fst snd] in H |- *; uvals; lia.
    cbn in Hx. destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]; cbn [fst snd].
    - pose proof (fog_disj_old f 6 _ Hf eq_refl) as D. fap D.
    - pose proof (fog_disj_old f 5 _ Hf eq_refl) as D. fap D.
    - pose proof (fog_disj_old f 4 _ Hf eq_refl) as D. fap D.
    - pose proof (fog_disj_old f 3 _ Hf eq_refl) as D. fap D.
    - pose proof (fog_disj_old f 0 _ Hf eq_refl) as D. fap D.
    - pose proof (fog_disj_old f 1 _ Hf eq_refl) as D. fap D.
    - pose proof (fog_disj_new f 3 _ Hf eq_refl) as D. fap D.
    - pose proof (fog_disj_new f 2 _ Hf eq_refl) as D. fap D.
    - pose proof (fog_disj_old f 8 _ Hf eq_refl) as D. fap D.
    - pose proof (fog_disj_old f 7 _ Hf eq_refl) as D. fap D.
    - pose proof (fog_disj_old f 2 _ Hf eq_refl) as D. fap D.
    - pose proof (fog_disj_new f 1 _ Hf eq_refl) as D. fap D.
    - pose proof (fog_disj_new f 0 _ Hf eq_refl) as D. fap D.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma tr_of_h0' : ltac2:(CDefT.buildp (gd_tbl_AH0K2 ()) "(9.(0.$14.)(15.Vh0,)(16.$14.(17.$14.(18.(19.Vp,$1:.))(17.$14.(1;.(19.Vp,$1<.))(17.$14.(1=.(1>.Vbp,))(1?.$14.))))(16.$14.(17.$14.(20.(19.Vp,$21.)+1000.$22.$23.$23.)(17.$14.(20.(19.Vp,$24.)+10000.$22.$23.$23.)(17.$14.(20.(19.Vp,$25.)$26.$22.$23.$23.)(17.$14.(20.(19.Vp,$27.)+1000.$22.$23.$23.)(1?.$14.)))))(16.$14.(28.(1.$>.$>.)$14.Lr,(1.$>.$>.)(20.(<.$>.$>.R1.)(7.$>.$>.R1.)(29.(7.$>.$>.R1.))$23.$2:.)(2;.Vp,$13.))(17.$14.(20.+7???7000.+10000000.$2<.$23.$2:.)(17.$14.(20.+8???7000.+20000000000.$2=.$23.$2:.)(17.$14.(20.+2008???7000.+=???0001000.$2<.$23.$2:.)(1?.$14.))))))))")
(* [comment removed for export] *).
  Proof. assert (E : emb_tr h0 = []) by reflexivity. unfold tr_of. rewrite E, app_nil_r. reflexivity. Qed.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L42581184446.2800000AS3hAR1e1b1n2Hb2Hn". (* [comment removed for export] *)
  #[using="hAR"] Lemma tf_lit : forall (e : word * word) b n k cs, In e M -> eB e = b -> eS e = n ->
    match k with KEager => clear N b (b + n) /\ clear Lz b (b + n) | KLazy => clear N b (b + n) | KNoacc => True end ->
    tfacts M N Lz (TR b n k true cs).
  Proof.
    intros e b n k cs He Hb Hn Hk. unfold tfacts, t_hi. cbn [t_lo t_len t_kind t_lit].
    split; [exists e; split; [exact He| lia]|]. split; [| exact Hk].
    intros _. unfold haslit. rewrite <- Hb, <- Hn, !Z_to_bv_bv_unsigned, <- surjective_pairing. exact He.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac lit_tac IN UB :=
    eapply tf_lit; [exact IN | unfold pinst; cbn [fst snd]; apply UB | unfold pinst; cbn [fst snd]; rewrite (u_wlit p) by lia; reflexivity |].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma R_zz : ltac2:(CDefT.buildp (gd_tbl_AH0K2 ()) "(9.(0.(1.$>.$>.))(28.(1.(2.&40.)(2.&40.))(1.$>.$>.)$2>.(2?.$30.))(17.(1.$>.$>.)(31.$>.$>.+10000.+36000.)(17.(1.$>.$>.)(31.$>.$>.+46000.+:;000.)(17.(1.$>.$>.)(31.$>.$>.+?1000.+6000.)(17.(1.$>.$>.)(31.$>.$>.+?7000.+568000.)(1?.(1.$>.$>.)))))))")
(* [comment removed for export] *).
  Proof. vm_compute. reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L30749989228.74000005S3hAR". (* [comment removed for export] *)
  #[using="hAR sp fs p HMOD"] Lemma R_bounds : forall e, In e (vm_reserved (m_vmmaps md)) -> 0x10000 <= eB e /\ eB e + eS e <= 0x65f000.
  Proof.
    intros e He. mm X. rewrite Mres in He. apply (in_map zz) in He. rewrite R_zz in He. unfold zz in He.
    cbn in He. destruct He as [H|[H|[H|[H|[]]]]]; injection H as H1 H2; rewrite <- H1, <- H2; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L63839518770.86L63841627758.87L63841628141.8800000E00Z01<S3hAR1x2Hx2e02A12A21lS3hAR1x2e12B12B21l2l0S3hAR1x2e22C12C22l02l12Hx2e32D12D2". (* [comment removed for export] *)
  #[using="hAR sp fs p HMOD"] Lemma R_cover : ltac2:(CDefT.buildp (gd_tbl_AH0K2 ()) "Px,$>.P,(=.(:.+10000.R1.)(5.R1.+65?000.))(32.(1.(2.&40.)(2.&40.))Le,(1.(2.&40.)(2.&40.))(=.(4.(1.(2.&40.)(2.&40.))R1.(33.(34.Vmd,)))(=.(:.(6.&40.(<.(2.&40.)(2.&40.)R1.))R3.)(5.R3.(;.(6.&40.(<.(2.&40.)(2.&40.)R1.))(6.&40.(7.(2.&40.)(2.&40.)R1.)))))))")
(* [comment removed for export] *).
  Proof.
    intros x Hx. mm X. rewrite Mres. pose proof R_zz as Z4.
    remember (segments_reserved ASEGS) as R eqn:HR. clear HR.
    destruct R as [|e0 [|e1 [|e2 [|e3 [|e4 R]]]]]; try discriminate Z4. cbn [map] in Z4. unfold zz in Z4.
    injection Z4 as A1 A2 B1 B2 C1 C2 D1 D2.
    destruct (Z_lt_le_dec x 286720); [exists e0 | destruct (Z_lt_le_dec x 987136); [exists e1 | destruct (Z_lt_le_dec x 1011712); [exists e2 | exists e3]]];
      (split; [cbn; tauto | lia]).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="Type"] Lemma cover_of_h0 : ltac2:(CDefT.buildp (gd_tbl_AH0K2 ()) "(9.(0.(1.$>.$>.))(35.Vh0,)(16.(1.$>.$>.)(17.(1.$>.$>.)(31.$>.$>.(19.Vp,$36.)$37.)(17.(1.$>.$>.)(31.$>.$>.(19.Vp,$38.)$39.)(1?.(1.$>.$>.))))(16.(1.$>.$>.)(16.(1.$>.$>.)(17.(1.$>.$>.)(31.$>.$>.(19.Vp,$21.)+1000.)(17.(1.$>.$>.)(31.$>.$>.(19.Vp,$24.)+10000.)(17.(1.$>.$>.)(31.$>.$>.(19.Vp,$25.)$26.)(17.(1.$>.$>.)(31.$>.$>.(19.Vp,$27.)+1000.)(1?.(1.$>.$>.))))))(16.(1.$>.$>.)(28.(1.$>.$>.)(1.$>.$>.)Lr,(1.$>.$>.)(31.$>.$>.(<.$>.$>.R1.)(7.$>.$>.R1.))(2;.Vp,$13.))$3:.))(16.(1.$>.$>.)(17.(1.$>.$>.)(31.$>.$>.(19.Vp,$1:.)(3;.+2.+14.))(1?.(1.$>.$>.)))(16.(1.$>.$>.)(17.(1.$>.$>.)(31.$>.$>.(19.Vp,$1<.)(3;.+2.+17.))(1?.(1.$>.$>.)))(16.(1.$>.$>.)(1?.(1.$>.$>.))(1?.(1.$>.$>.))))))))")
(* [comment removed for export] *).
  Proof. unfold cover_of. cbn -[PG Z.pow EXTRA]. unfold EXTRA. rewrite !map_app, !map_map. reflexivity. Qed.

  Definition COVER_LIT : list (Z * Z) := ltac2:(CDefT.buildp (gd_tbl_AH0K2 ()) "(16.(1.$>.$>.)(17.(1.$>.$>.)(31.$>.$>.(19.Vp,$36.)$37.)(17.(1.$>.$>.)(31.$>.$>.(19.Vp,$38.)$39.)(17.(1.$>.$>.)(31.$>.$>.(19.Vp,$21.)+1000.)(17.(1.$>.$>.)(31.$>.$>.(19.Vp,$24.)+10000.)(17.(1.$>.$>.)(31.$>.$>.(19.Vp,$25.)$26.)(17.(1.$>.$>.)(31.$>.$>.(19.Vp,$27.)+1000.)(17.(1.$>.$>.)(31.$>.$>.(19.Vp,$3<.)+10000.)(17.(1.$>.$>.)(31.$>.$>.(19.Vp,$3=.)+38>000.)(17.(1.$>.$>.)(31.$>.$>.(19.Vp,$3>.)+1000.)(17.(1.$>.$>.)(31.$>.$>.(19.Vp,$3?.)+1000.)(17.(1.$>.$>.)(31.$>.$>.(19.Vp,$40.)+1000.)(1?.(1.$>.$>.)))))))))))))(16.(1.$>.$>.)$3:.(17.(1.$>.$>.)(31.$>.$>.(19.Vp,$1:.)(3;.+2.+14.))(17.(1.$>.$>.)(31.$>.$>.(19.Vp,$1<.)(3;.+2.+17.))(1?.(1.$>.$>.))))))")
(* [comment removed for export] *).
  #[using="Type"] Lemma in_cover : forall c, In c (cover_of h0) <-> (In c COVER_LIT \/ In c FOG).
  Proof.
    intros c. rewrite cover_of_h0. unfold EXTRA. rewrite !map_app. cbn [map fst snd]. unfold COVER_LIT, SH3. rewrite !in_app_iff. cbn [In].
    assert (MF : In c (map (fun r : Z * Z => (fst r, snd r)) FOG) <-> In c FOG).
    { rewrite in_map_iff. split; [(intros dd_H; ddestruct dd_H as (r & <- & Hr)); rewrite <- surjective_pairing; exact Hr | intros H; exists c; rewrite <- surjective_pairing; auto]. }
    rewrite MF. tauto.
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L18930958230.20L50159126113.20L66504047291.22L67792869265.2000000500:00C00HS3hARS3hARS3hAR1c1XS3hAR". (* [comment removed for export] *)
  #[using="sp fs HCN md HMOD HAC HSP HFOG M"] Lemma cover_nonneg : forall c, In c (cover_of h0) -> 0 <= snd c.
  Proof.
    intros c Hc. apply in_cover in Hc as [Hc|Hc].
    - unfold COVER_LIT, SH3 in Hc. rewrite !in_app_iff in Hc. cbn [In] in Hc.
      pose proof (proj1 (PG_range p HCN v_prim ltac:(pv))). 
      destruct Hc as [Hc|[Hc|Hc]]; repeat (destruct Hc as [<-|Hc]; [cbn [snd]; unfold kPrimHullLen, kPaHullLen, kFakeBytes; lia|]); destruct Hc.
    - pose proof (proj1 (Forall_forall _ _) fog_ok c Hc) as (_ & X & _). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0?L14411627883.21L19708637957.21L24830330373.21L50161164051.19L59314873579.24L59579071077.20L59579071470.21L60679088009.20L67790704355.19L9656813402.23 00000700>00C00H00U00Z00_00d00i010S3hAR1pS3hAR1pS3hARS3hARS3hAR1e3Hfl1HS3hARS3hARS3hARS3hARS3hAR1e". (* [comment removed for export] *)
  #[using="sp fs HCN HMOD HAC HSP HFOG"] Theorem h0_vcensus : vcensus v0 (vm_reserved (m_vmmaps md)) M.
  Proof.
    unfold vcensus. unfold v0. cbn [vst_of v_cover v_cb20 v_cb23]. fold h0.
    split; [| split; [exact cover_nonneg | split; apply cb_of_ok; [lia | exact cover_nonneg | lia | exact cover_nonneg]]].
    intros e He Hfl Hce.
    apply in_app_iff in He as [He|He].
    { exfalso. pose proof (R_bounds e He). unfold bottomup_floor in Hfl. lia. }
    unfold M in He. rewrite HFOG in He.
    Ltac cov C := exists C; split; [apply (proj2 (in_cover C)); left; unfold COVER_LIT, SH3; rewrite !in_app_iff; cbn [In]; tauto
                                   | unfold pinst; cbn [fst snd]; uvals; unfold kPrimHullLen, kPaHullLen, kFakeBytes; lia].
    apply in_app_iff in He as [He|He]; [| apply in_app_iff in He as [He|He]].
    - unfold me_maps_new, MAPS_NEW in He. cbn [map] in He. destruct He as [<-|[<-|[<-|[<-|[]]]]].
      + cov (PG p v_divec, 4096).
      + cov (PG p v_gvec, 4096).
      + cov (PG p v_dstore, 2 ^ 23).
      + cov (PG p v_dnodes, 2 ^ 20).
    - exists (zz e). split; [apply (proj2 (in_cover _)); right; unfold FOG; apply in_map; exact He | unfold zz; cbn [fst snd]; lia].
    - unfold me_maps_old, MAPS_OLD in He. cbn [map] in He. destruct He as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]].
      + cov (PG p v_fstk, kFakeBytes).
      + cov (PG p v_dtls, 4096).
      + cov (PG p v_tvec, 4096).
      + cov (PG p v_treg, 0x10000).
      + cov (PG p v_thr, 4096).
      + cov (PG p v_secv, kPaHullLen).
      + cov (PG p v_prim, kPrimHullLen).
      + cov (PG p v_ictx, 0x38e000).
      + cov (PG p v_lla, 0x10000).
      + cov (0x2008fff7000, 0xdfff0001000).
      + exfalso. unfold pinst in Hfl. cbn [fst snd] in Hfl. revert Hfl. uvals. unfold bottomup_floor. lia.
      + exfalso. unfold pinst in Hfl. cbn [fst snd] in Hfl. revert Hfl. uvals. unfold bottomup_floor. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L25171441213.3 L56297782960.4 L59579326857.7700000800C00HS1p1x2HZS1p1x2HZ2PSS3hAR". (* [comment removed for export] *)
  #[using="sp fs HCN HMOD"] Theorem h0_habs_nn : forall x, habs_zone h0 x -> in_ivs x N = true.
  Proof.
    intros x [HZ NT]. mm X. pose proof (r_prim p HCN) as PR. pose proof (r_pslack p HCN) as PS.
    assert (XRI : ~ (SB p + 2 ^ 37 <= x < SB p + 2 ^ 37 + 4096)).
    { specialize (NT (ri_tr (h_L h0)) ltac:(rewrite tr_of_h0'; cbn; tauto)).
      unfold t_hi, ri_tr in NT. cbn [t_lo t_len] in NT. change (ri_base (h_L h0)) with (SB p + 2 ^ 37) in NT. exact NT. }
    replace (l_b6 (h_L h0)) with (PG p v_prim) in HZ by reflexivity. replace (l_pa (h_L h0)) with (PG p v_secv) in HZ by reflexivity.
    change (ri_base (h_L h0)) with (SB p + 2 ^ 37) in HZ. unfold kPaHullLen in HZ.
    destruct HZ as [HZ|HZ].
    - destruct (K5prim x ltac:(uvals; unfold SB, PG in *; clear - HZ PS; lia)) as [X|X]; [exact X| exfalso; apply XRI; revert X; uvals; intros X; exact X].
    - destruct (K5secv x ltac:(uvals; clear - HZ; lia)) as [X|X]; [exact X| exfalso; apply XRI; revert X; uvals; intros X; exact X].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis FOG_len : (length fog <= 2)%nat.
  Hypothesis FOG_small : Forall (fun iv => bv_unsigned (snd iv) <= 8192) fog.
  Hypothesis STKHI_gt : SP p < STKHI.
  Hypothesis STKHI_pg : STKHI mod 4096 = 0.
  Hypothesis STKHI_47 : STKHI <= 2 ^ 47.
  Hypothesis STKHI_len : STKHI <= SP p + 2 ^ 23.
  Hypothesis TF_ok : 1 <= TF <= 3.
  #[using="FOG_len"] Lemma fog_len : (length FOG <= 2)%nat.
  Proof. unfold FOG. rewrite length_map. exact FOG_len. Qed.
  #[using="FOG_small"] Lemma fog_small : Forall (fun r => snd r <= 8192) FOG.
  Proof. unfold FOG. apply Forall_map. eapply Forall_impl; [| exact FOG_small]. intros iv H. exact H. Qed.

  #[using="sp fs HCN md HMOD HAC HSP HFOG M FOG_len FOG_small STKHI_gt STKHI_pg STKHI_47 STKHI_len TF_ok"] Lemma h0_awf' : awf' h0.
  Proof. exact (h0_awf p HCN STKHI FOG TF HAC STKHI_gt STKHI_pg STKHI_47 STKHI_len fog_ok fog_len fog_small TF_ok). Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00E0?L14409530848.71L16787670394.72L17798123742.71L25171181228.69L25173275180.77L37620449012.75L50512722708.71L51469819826.67L52945112538.70L59308730611.73L59576947120.72L59576974181.71L59577012529.72L59577118350.67L59584050426.68L59591670898.65L6231640470.72 L63842185068.76L63842341845.71L9034677927.73 L9658821775.73 00000I00k01B01`02H02n03E03\04704[05205I05`06706N06e07H07o08N08n09PS3hAR1p5STKHI3fog7FOG_lenS3hAR1p5STKHI3fog7FOG_len2iv2R12R2S3hAR5STKHI3fog7FOG_lenS3hAR1p5STKHI3fog7FOG_len1x2XIS3hAR1p5STKHI3fog7FOG_len1U1n1x2Hx2I12I2S3hAR1p5STKHI3fog7FOG_len1U1n3APT1x2HxS3hAR5STKHI3fog7FOG_lenS3hAR5STKHI3fog7FOG_lenS3hAR5STKHI3fog7FOG_len1f1HS3hAR1p5STKHI3fog7FOG_len1e2M22M12APS3hAR5STKHI3fog7FOG_lenS3hAR5STKHI3fog7FOG_lenS3hAR5STKHI3fog7FOG_lenS3hAR5STKHI3fog7FOG_lenS3hAR5STKHI3fog7FOG_lenS3hAR5STKHI3fog7FOG_lenS3hAR1p5STKHI3fog7FOG_len1U1n2I12I2S3hAR5STKHI3fog7FOG_len1e1x2Hx2iv2B12B2S3hAR5STKHI3fog7FOG_len2iv1x2XIS3hAR5STKHI3fog7FOG_len1b1n1e2H0S3hAR5STKHI3fog7FOG_len1e2iv2B12B2". (* [comment removed for export] *)
  #[using="sp fs HCN HMOD HAC HSP HFOG FOG_len FOG_small STKHI_gt STKHI_pg STKHI_47 STKHI_len TF_ok"] Theorem h0_vm_table : vm_table v0 M N Lz.
  Proof.
    mm X. clear Mfog Mres Mlim Mhalt Mfds Mfs Mtot Misp Mbrk Msbrk Meager Mabytes Mminv. uvals.
    dpose h0_awf' as ((WL0 & _) & _). change (wf_L (h_L h0)) in WL0.
    assert (CL : forall X b n, (forall e, In e X -> zE e <= b \/ b + n <= zB e) -> clear X b (b + n)).
    { intros X b n H e He. pose proof (H e He). unfold zB, zE in *. lia. }
    unfold vm_table. split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
    - (* [comment removed for export] *)
      unfold v0. cbn [vst_of v_tr]. fold h0. rewrite tr_of_h0'. unfold EXTRA. rewrite !map_app. cbn [map fst snd].
      repeat (apply Forall_app; split); repeat apply Forall_cons; try apply Forall_nil.
      + (* [comment removed for export] *) lit_tac (new_nth 3 _ eq_refl) (u_dnodes p HCN). split; apply CL; assumption.
      + (* [comment removed for export] *) lit_tac (new_nth 2 _ eq_refl) (u_dstore p HCN). apply CL; assumption.
      + (* [comment removed for export] *) ddestruct Mri as (_ & (iv & Hiv & R1 & R2) & RN & RL).
        unfold tfacts, t_hi. cbn [ri_tr t_lo t_len t_kind t_lit]. change (ri_base (L0_of bp)) with (SB p + 2 ^ 37).
        split; [exists iv; split; [exact Hiv| unfold zB, zE in *; lia]|]. split; [intros X; discriminate X|]. split; apply CL; assumption.
      + (* [comment removed for export] *) lit_tac (old_nth 4 _ eq_refl) (u_thr p HCN). split; apply CL; assumption.
      + (* [comment removed for export] *) lit_tac (old_nth 3 _ eq_refl) (u_treg p HCN). split; apply CL; assumption.
      + (* [comment removed for export] *) lit_tac (old_nth 0 _ eq_refl) (u_fstk p HCN). unfold kFakeBytes. split; apply CL; assumption.
      + (* [comment removed for export] *) lit_tac (old_nth 1 _ eq_refl) (u_dtls p HCN). split; apply CL; assumption.
      + (* [comment removed for export] *) lit_tac (old_nth 8 _ eq_refl) (u_lla p HCN). exact I.
      + (* [comment removed for export] *) lit_tac (old_nth 7 _ eq_refl) (u_ictx p HCN). cbn [xkind Z.ltb Z.compare Pos.compare Pos.compare_cont Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]. apply CL; assumption.
      + (* [comment removed for export] *) lit_tac (old_nth 2 _ eq_refl) (u_tvec p HCN). exact I.
      + (* [comment removed for export] *) lit_tac (new_nth 1 _ eq_refl) (u_gvec p HCN). exact I.
      + (* [comment removed for export] *) lit_tac (new_nth 0 _ eq_refl) (u_divec p HCN). exact I.
      + (* [comment removed for export] *) apply Forall_forall. intros t Ht. apply in_map_iff in Ht as (r & <- & Hr). unfold FOG in Hr. apply in_map_iff in Hr as (f & <- & Hf).
        unfold zz. cbn [fst snd]. eapply (tf_lit f); [exact (fog_in_M f Hf) | reflexivity | reflexivity |].
        unfold xkind. replace (bv_unsigned (snd f) <? 2 ^ 17) with true by (symmetry; apply Z.ltb_lt; pose proof (proj1 (Forall_forall _ _) FOG_small f Hf); cbn beta in *; lia). exact I.
      + (* [comment removed for export] *) eapply tf_lit; [exact (old_nth 11 _ eq_refl) | unfold pinst; cbn [fst snd]; apply (u_wlit p); lia | unfold pinst; cbn [fst snd]; apply (u_wlit p); lia |]. apply CL; assumption.
      + (* [comment removed for export] *) eapply tf_lit; [exact (old_nth 10 _ eq_refl) | unfold pinst; cbn [fst snd]; apply (u_wlit p); lia | unfold pinst; cbn [fst snd]; apply (u_wlit p); lia |]. exact I.
      + (* [comment removed for export] *) eapply tf_lit; [exact (old_nth 9 _ eq_refl) | unfold pinst; cbn [fst snd]; apply (u_wlit p); lia | unfold pinst; cbn [fst snd]; apply (u_wlit p); lia |]. apply CL; assumption.
    - (* [comment removed for export] *) intros e He. ddestruct (MNcov e He) as (_ & iv & Hiv & B1 & B2). exists iv. unfold zB, zE in *. split; [exact Hiv| lia].
    - (* [comment removed for export] *) intros e He. ddestruct (MLcov e He) as (_ & iv & Hiv & B1 & B2). exists iv. unfold zB, zE in *. split; [exact Hiv| lia].
    - (* [comment removed for export] *)
      intros U n HU. unfold v0 in HU. cbn [vst_of v_unit] in HU. fold h0 in HU.
      pose proof (units_of_L_inside (h_L h0) U n WL0 HU) as INS.
      replace (l_b6 (h_L h0)) with (PG p v_prim) in INS by reflexivity. replace (l_pa (h_L h0)) with (PG p v_secv) in INS by reflexivity.
      unfold kPrimHullLen, kPaHullLen in INS. destruct INS as [[I1 I2]|[I1 I2]].
      + eexists. split; [exact (old_nth 6 _ eq_refl)|]. unfold pinst. cbn [fst snd]. uvals. lia.
      + eexists. split; [exact (old_nth 5 _ eq_refl)|]. unfold pinst. cbn [fst snd]. uvals. lia.
    - (* [comment removed for export] *)
      (* [comment removed for export] *)
      assert (MXA : forall iv, In iv M -> forall x, bv_unsigned (fst iv) <= x < bv_unsigned (fst iv) + bv_unsigned (snd iv) ->
                (exists t, In t (v_tr v0) /\ t_lit t = true /\ t_lo t <= x < t_hi t) \/ (exists U n, v_unit v0 U n /\ U <= x < U + n)).
      { intros iv Hiv x XI.
        unfold M in Hiv. rewrite HFOG in Hiv.
        unfold v0. cbn [vst_of v_hulls v_tr v_unit hulls_of]. fold h0. rewrite tr_of_h0'. unfold EXTRA. rewrite !map_app. cbn [map fst snd].
        rewrite (xkind_big 3727360) by lia. rewrite !(xkind_small 65536) by lia. rewrite !(xkind_small 4096) by lia.
        Ltac trk2 T XI := left; exists T; split; [| split; [reflexivity| revert XI; unfold pinst, t_hi; cbn [fst snd t_lo t_len store_tr node_tr]; unfold kFakeBytes; uvals; intros XI; first [exact XI| lia]]].
        Ltac hull2 HX XI WL0 x h0 := right; cbn [vst_of v_unit]; apply (units_of_L_cover (h_L h0) HX x WL0); [unfold hulls_of; cbn; tauto| revert XI; unfold pinst; cbn [fst snd]; uvals; intros XI; cbn [fst snd]; unfold kPrimHullLen, kPaHullLen; lia].
        apply in_app_iff in Hiv as [Hiv|Hiv]; [| apply in_app_iff in Hiv as [Hiv|Hiv]].
        * unfold me_maps_new, MAPS_NEW in Hiv. cbn [map] in Hiv. destruct Hiv as [<-|[<-|[<-|[<-|[]]]]].
          -- trk2 (TR (PG p v_divec) 4096 KNoacc true false) XI. cbn; tauto.
          -- trk2 (TR (PG p v_gvec) 4096 KNoacc true false) XI. cbn; tauto.
          -- trk2 (store_tr (PG p v_dstore)) XI. cbn; tauto.
          -- trk2 (node_tr (PG p v_dnodes)) XI. cbn; tauto.
        * left. exists (TR (eB iv) (eS iv) (xkind (eS iv)) true false). split; [| split; [reflexivity| unfold t_hi; cbn [t_lo t_len]; lia]].
          apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. apply in_app_iff. right.
          apply in_map_iff. exists (zz iv). split; [reflexivity|]. unfold FOG. apply in_map. exact Hiv.
        * unfold me_maps_old, MAPS_OLD in Hiv. cbn [map] in Hiv. destruct Hiv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]].
          -- trk2 (TR (PG p v_fstk) kFakeBytes KEager true true) XI. cbn; tauto.
          -- trk2 (TR (PG p v_dtls) 4096 KEager true true) XI. cbn; tauto.
          -- trk2 (TR (PG p v_tvec) 4096 KNoacc true false) XI. cbn; tauto.
          -- trk2 (TR (PG p v_treg) 0x10000 KEager true true) XI. cbn; tauto.
          -- trk2 (TR (PG p v_thr) 4096 KEager true true) XI. cbn; tauto.
          -- hull2 (PG p v_secv, kPaHullLen) XI WL0 x h0.
          -- hull2 (PG p v_prim, kPrimHullLen) XI WL0 x h0.
          -- trk2 (TR (PG p v_ictx) 0x38e000 KLazy true false) XI. cbn; tauto.   (* [comment removed for export] *)
          -- trk2 (TR (PG p v_lla) 0x10000 KNoacc true false) XI. cbn; tauto.
          -- trk2 (TR 0x2008fff7000 0xdfff0001000 KLazy true false) XI. do 3 (apply in_app_iff; right); cbn; tauto.
          -- trk2 (TR 0x8fff7000 0x20000000000 KNoacc true false) XI. do 3 (apply in_app_iff; right); cbn; tauto.
          -- trk2 (TR 0x7fff7000 0x10000000 KLazy true false) XI. do 3 (apply in_app_iff; right); cbn; tauto. }
      split; [| split; [| split; [| split]]].
      + (* [comment removed for export] *)
        intros U n HU APT x Hx. unfold v0 in HU. cbn [vst_of v_unit] in HU. fold h0 in HU.
        pose proof (units_of_L_inside (h_L h0) U n WL0 HU) as INS.
        replace (l_b6 (h_L h0)) with (PG p v_prim) in INS by reflexivity. replace (l_pa (h_L h0)) with (PG p v_secv) in INS by reflexivity.
        unfold kPrimHullLen, kPaHullLen in INS.
        assert (XRI : ~ (SB p + 2 ^ 37 <= x < SB p + 2 ^ 37 + 4096)).
        { specialize (APT (ri_tr (h_L h0)) ltac:(unfold v0; cbn [vst_of v_tr]; fold h0; rewrite tr_of_h0'; cbn; tauto)).
          unfold t_hi, ri_tr in APT. cbn [t_lo t_len] in APT. change (ri_base (h_L h0)) with (SB p + 2 ^ 37) in APT. lia. }
        assert (NC : in_ivs x N = true).
        { destruct INS as [[I1 I2]|[I1 I2]].
          - destruct (K5prim x ltac:(uvals; lia)) as [X|X]; [exact X| exfalso; revert X; uvals; intros X; apply XRI; exact X].
          - destruct (K5secv x ltac:(uvals; lia)) as [X|X]; [exact X| exfalso; revert X; uvals; intros X; apply XRI; exact X]. }
        apply in_ivs_true in NC. ddestruct NC as (iv & Hiv & R). exists iv. split; [exact Hiv| exact R].
      + (* [comment removed for export] *) exact M_pos.
      + (* [comment removed for export] *)
        intros e He x Hx. ddestruct (MLcov e He) as (_ & iv & Hiv & B1 & B2). unfold zB, zE in B1, B2. apply (MXA iv Hiv x). lia.
      + (* [comment removed for export] *) exact MXA.
      + (* [comment removed for export] *)
        intros e H He HH M1 M2. unfold v0 in HH. cbn [vst_of v_hulls hulls_of] in HH. fold h0 in HH.
        replace (l_b6 (h_L h0)) with (PG p v_prim) in HH by reflexivity. replace (l_pa (h_L h0)) with (PG p v_secv) in HH by reflexivity.
        destruct HH as [<-|[<-|[]]]; cbn [fst snd] in M1, M2 |- *; unfold kPrimHullLen, kPaHullLen in *.
        (* [comment removed for export] *)
        * destruct (seps_pairwise M M_seps M_pos e _ He (old_nth 6 _ eq_refl)) as [->|AP]; [unfold pinst; cbn [fst snd]; uvals; change (l_b6 (h_L h0)) with (PG p v_prim) in *; lia|].
          exfalso. revert AP. unfold pinst. cbn [fst snd]. uvals. intros AP. change (l_b6 (h_L h0)) with (PG p v_prim) in *. lia.
        * destruct (seps_pairwise M M_seps M_pos e _ He (old_nth 5 _ eq_refl)) as [->|AP]; [unfold pinst; cbn [fst snd]; uvals; change (l_pa (h_L h0)) with (PG p v_secv) in *; lia|].
          exfalso. revert AP. unfold pinst. cbn [fst snd]. uvals. intros AP. change (l_pa (h_L h0)) with (PG p v_secv) in *. lia.
    - (* [comment removed for export] *) exact M_nodup.
    - (* [comment removed for export] *) exact (seps_pairwise M M_seps M_pos).
    - (* [comment removed for export] *) intros e He. exact (proj1 (MNcov e He)).
    - (* [comment removed for export] *) intros e He. exact (proj1 (MLcov e He)).
    - (* [comment removed for export] *) split; [| split].
      + exists (pinst p (WLit 0x7fff7000, WLit 0x10000000)). split; [exact (old_nth 11 _ eq_refl)|]. unfold pinst. cbn [fst snd]. rewrite !(u_wlit p) by lia. lia.
      + exists (pinst p (WLit 0x8fff7000, WLit 0x20000000000)). split; [exact (old_nth 10 _ eq_refl)|]. unfold pinst. cbn [fst snd]. rewrite !(u_wlit p) by lia. lia.
      + exists (pinst p (WLit 0x2008fff7000, WLit 0xdfff0001000)). split; [exact (old_nth 9 _ eq_refl)|]. unfold pinst. cbn [fst snd]. rewrite !(u_wlit p) by lia. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L15043033658.29L16363626134.3400000G00lS3hAR5STKHI3fog7FOG_lenS3hAR5STKHI3fog7FOG_len1A1f1x1r2H02H1". (* [comment removed for export] *)
  #[using="hAR STKHI fog FOG_len"] Lemma zsum_nonneg : forall {A} (f : A -> Z) l, (forall x, In x l -> 0 <= f x) -> 0 <= AFreeSlot.zsum f l.
  Proof. intros A f l H. induction l as [|x r IH]; cbn; [lia|]. pose proof (H x ltac:(now left)). assert (0 <= AFreeSlot.zsum f r) by (apply IH; intros y Hy; apply H; now right). lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L15301369260.27L51411159700.2700000L00cS3hAR5STKHI3fog2h07FOG_len1HS3hAR5STKHI3fog7FOG_len". (* [comment removed for export] *)
  #[using="FOG_len"] Lemma h0_eb : E0 <= eb_of h0.
  Proof.
    unfold eb_of.
    assert (0 <= AFreeSlot.zsum (fun c => r_mapped_user (h_reg h0 c) + r_mapped_fa (h_reg h0 c)) (map Z.of_nat (seq 1 (Z.to_nat (kNumClasses - 1))))).
    { apply zsum_nonneg. intros c _. cbn -[Z.add]. lia. }
    change (Z.of_nat (length (d_nb (h_dep h0)))) with 1. change (AFreeSlot.zsum s_map_size (s_chunks (h_sec h0))) with 0.
    change (AFreeSlot.zsum snd (a_sech (h_acct h0))) with 0. change (h_pa_committed h0) with 0.
    change (AFreeSlot.zsum t_len (emb_tr h0)) with 0.   (* [comment removed for export] *)
    unfold kDepotBlockBytes. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L24091416208.79L27568766702.27L28743610084.26L66134598948.2600000V01201I01`S3hAR5STKHI2md3fog2h07FOG_len6Meager1HS3hAR5STKHI3fog2h07FOG_len1HS3hAR5STKHI3fog7FOG_lenS3hAR5STKHI3fog7FOG_len". (* [comment removed for export] *)
  #[using="sp fs HCN HMOD HAC HSP HFOG M FOG_len FOG_small STKHI_gt STKHI_pg STKHI_47 STKHI_len TF_ok"] Theorem h0_budget : eager_bytes md <= v_eb v0 /\ v_eb v0 + 4096 * vnb v0 <= VLIMIT.
  Proof.
    split.
    - mm X. change (eager_bytes md) with (eager_used md). unfold v0. cbn [vst_of v_eb]. fold h0. pose proof h0_eb. unfold E0 in *. lia.
    - pose proof (vst_slack h0 0 (awf'_bwf h0 h0_awf') ltac:(rewrite (h0_havol p STKHI FOG TF); unfold AVOL_MAX; lia) ltac:(lia)). unfold v0. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L18433093931.80L25807818766.81L7108853750.79 00000I00k01BS3hAR1p5STKHI3fog7FOG_lenS3hAR1p5STKHI3fog7FOG_len2S22D32M3S3hAR5STKHI3fog7FOG_len". (* [comment removed for export] *)
  #[using="sp fs p HCN STKHI fog HMOD HAC HSP FOG_len"] Theorem h0_atop : atop_ok (alloc_top (m_vmmaps md)).
  Proof.
    mm X. unfold atop_ok, alloc_top, stack_max_size. rewrite Misp, HSP, HAC.
    pose proof (r_s2 p HCN) as S2. unfold SP, STKPG.
    pose proof (Z.div_mod (uv p v_s2) 256 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (uv p v_s2) 256 ltac:(lia)) as M3. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="hAR sp fs p HMOD"] Theorem h0_reserved : ltac2:(CDefT.buildp (gd_tbl_AH0K2 ()) "(=.Pe,(1.(2.&40.)(2.&40.))P,(4.(1.(2.&40.)(2.&40.))R1.(33.(34.Vmd,)))(=.(:.(41.$42.)(6.&40.(<.(2.&40.)(2.&40.)R2.)))(:.(;.(6.&40.(<.(2.&40.)(2.&40.)R2.))(6.&40.(7.(2.&40.)(2.&40.)R2.)))(43.$42.)))Px,$>.P,(=.(:.(41.$42.)R1.)(5.R1.(43.$42.)))(32.(1.(2.&40.)(2.&40.))Le,(1.(2.&40.)(2.&40.))(=.(4.(1.(2.&40.)(2.&40.))R1.(33.(34.Vmd,)))(=.(:.(6.&40.(<.(2.&40.)(2.&40.)R1.))R3.)(5.R3.(;.(6.&40.(<.(2.&40.)(2.&40.)R1.))(6.&40.(7.(2.&40.)(2.&40.)R1.))))))))")
(* [comment removed for export] *).
  Proof. cbn [al_img_lo al_img_hi AL0]. split; [exact R_bounds | exact R_cover]. Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L56648762597.93L59885749579.9300000[01FS3hAR5STKHI3fog7FOG_len2pg1e2E12iv2C12B12B6S3hAR5STKHI3fog7FOG_len2pg1e2E22iv2C22B12B6". (* [comment removed for export] *)
  #[using="sp fs p HCN STKHI fog HMOD HAC HSP FOG_len"] Lemma lazy_page : ltac2:(CDefT.buildp (gd_tbl_AH0K2 ()) "Ppg,(2.&40.)P,(9.$44.(45.R1.VLz,)$23.)(32.(1.(2.&40.)(2.&40.))Liv,(1.(2.&40.)(2.&40.))(=.(4.(1.(2.&40.)(2.&40.))R1.VM,)(=.(:.(6.&40.(<.(2.&40.)(2.&40.)R1.))(6.&40.R3.))(=.(:.(;.(6.&40.R3.)+1000.)(;.(6.&40.(<.(2.&40.)(2.&40.)R1.))(6.&40.(7.(2.&40.)(2.&40.)R1.))))(=.(8.(:.(;.(6.&40.(<.(2.&40.)(2.&40.)R1.))(6.&40.(7.(2.&40.)(2.&40.)R1.)))+10000.)(:.+65?000.(6.&40.(<.(2.&40.)(2.&40.)R1.))))(=.(:.(;.(6.&40.(<.(2.&40.)(2.&40.)R1.))(6.&40.(7.(2.&40.)(2.&40.)R1.)))(10.VhAR,))(32.(1.(2.&40.)(2.&40.))Le,(1.(2.&40.)(2.&40.))(=.(4.(1.(2.&40.)(2.&40.))R1.VLz,)(=.(:.(6.&40.(<.(2.&40.)(2.&40.)R1.))(6.&40.R4.))(:.(;.(6.&40.R4.)+1000.)(;.(6.&40.(<.(2.&40.)(2.&40.)R1.))(6.&40.(7.(2.&40.)(2.&40.)R1.)))))))))))))")
(* [comment removed for export] *).
  Proof.
    intros pg H. mm X. apply page_in_ranges_true in H as (e & He & E1 & E2). unfold page_size in E2.
    ddestruct (MLcov e He) as (_ & iv & Hiv & C1 & C2). ddestruct (M_bounds iv Hiv) as (B1 & B2 & B3 & B4 & B5 & B6).
    exists iv. unfold zB, zE in *. split; [exact Hiv|]. split; [lia|]. split; [lia|]. split; [exact B4|]. split; [exact B5|]. exists e. auto.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L12806522960.35L14487954312.33L18928452141.35L18928648876.34L29125626184.32L38665527318.36L41813434151.34L63368119981.33L63370422135.3200000N00l01G01b02@02g03E03`047S3hAR5STKHI3fog7FOG_len1R1c2D2S3hAR5STKHI3fog7FOG_len1R1c2HcS3hAR5STKHI3fog7FOG_len1R1cS3hAR5STKHI3fog7FOG_len1R1cS3hAR5STKHI3fog7FOG_len1R1c2HcS3hAR5STKHI3fog7FOG_len1R1c2D12D22P12P2S3hAR5STKHI3fog7FOG_len1R1c2D1S3hAR5STKHI3fog7FOG_len1R1cS3hAR5STKHI3fog7FOG_len". (* [comment removed for export] *)
  #[using="FOG_len"] Lemma good_shb : ltac2:(CDefT.buildp (gd_tbl_AH0K2 ()) "PR,(1.$>.$>.)Pc,$>.Ppg,(2.&40.)P,(4.(1.$>.$>.)R3.(46.Vv0,))P,(=.(:.(<.$>.$>.R4.)R3.)(5.R3.(;.(<.$>.$>.R4.)(7.$>.$>.R4.))))P,(9.$>.(6.&40.R3.)(47.(48.$42.R4.)))(49.$42.Vv0,R4.)")
(* [comment removed for export] *).
  Proof.
    intros R c pg HR Hc Hpg. unfold vgood, vgood_b. apply Bool.orb_true_iff. left. apply existsb_exists. exists R. split; [exact HR|].
    unfold pg_shadow_b. rewrite Hpg. unfold zpb, shadow_of, AL0. cbn [al_sb].
    assert (D1 : fst R / 8 <= c / 8) by (apply Z.div_le_mono; lia). assert (D2 : c / 8 <= (fst R + snd R - 1) / 8) by (apply Z.div_le_mono; lia).
    assert (P1 : (2147450880 + fst R / 8) / 4096 <= (2147450880 + c / 8) / 4096) by (apply Z.div_le_mono; lia).
    assert (P2 : (2147450880 + c / 8) / 4096 <= (2147450880 + (fst R + snd R - 1) / 8) / 4096) by (apply Z.div_le_mono; lia).
    rewrite !andb_true_iff. split; [split; apply Z.leb_le; lia|]. apply Z.eqb_eq. apply Z_mod_mult.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L47803412682.2800000LS3hAR5STKHI3fog7FOG_len1x2Hx". (* [comment removed for export] *)
  #[using="hAR STKHI fog FOG_len"] Lemma u_pbo : forall x, 0 <= x < 2 ^ 64 -> bv_unsigned (page_base_of x) = x / 4096 * 4096.
  Proof.
    intros x Hx. unfold page_base_of, page_size. apply u64_lit.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="hAR STKHI fog FOG_len"] Lemma pbo_in : ltac2:(CDefT.buildp (gd_tbl_AH0K2 ()) "Px,$>.Plo,$>.Pn,$>.P,(9.$>.(?.R2.+1000.)=)P,(9.$>.(?.R2.+1000.)=)P,(=.(:.R4.R5.)(5.R5.(;.R4.R3.)))(=.(:.R5.(4:.(4;.R6.+1000.)+1000.))(:.(;.(4:.(4;.R6.+1000.)+1000.)+1000.)(;.R5.R4.)))")
(* [comment removed for export] *).
  Proof.
    intros x lo n Hl Hn Hx. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). split; nia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00Z0@L10786746824.100L14797007543.100L18435116950.91 L18441381513.89 L18928466588.88 L18928577789.92 L18928663069.93 L23067212638.91 L23305109826.100L24122832638.94 L29625360005.102L29885909363.94 L30010739830.100L31332237274.91 L31334547415.92 L31482006335.91 L35497778844.88 L37601419051.93 L41624166639.89 L42132423155.100L44674373266.100L45295462279.92 L49007494144.100L51683429760.88 L53049256423.102L5738343814.90  L5744960791.100 L5744973488.102 L57706257591.88 L59096888697.88 L59308579027.93 L59308988881.92 L59314873579.94 L59591670898.68 L60723950899.95 L61390772559.94 L63368316331.92 L63374621462.93 L65345616370.93 L68390435618.92 L68524348478.88 L7109229939.90  00000X01401M02:02Q02j03C03_04S05105O05m06a07=07f08Q08h09P0:00:10:J0:k0;P0;l0<J0=50=h0>g0?>0?Z0@K0A?0B30BJ0Bi0CE0C\0D50DZ0EB0Ea0F8S3hAR1p5STKHI3fog7FOG_len2G12G32G42G52G6S3hAR1p5STKHI3fog7FOG_len2G1S3hAR1p5STKHI3fog7FOG_lenS3hAR1p5STKHI3fog7FOG_len8STKHI_gt2AB2S12S21HS3hAR5STKHI3fog7FOG_lenS3hAR5STKHI3fog7FOG_len1yS3hAR5STKHI3fog7FOG_len1yS3hAR5STKHI3fog7FOG_len1y2HyS3hAR1p5STKHI3fog7FOG_len2AB2G12G22G32G42G52G62PR2PSS3hAR5STKHI3fog7FOG_len1c1H2H0S3hAR1p5STKHI3fog7FOG_len1x2Q1S3hAR5STKHI3fog7FOG_len1c1t2TcS3hAR1p5STKHI3fog7FOG_len2AB2G12G22G32G42G52G62PR2PSS3hAR5STKHI3fog7FOG_len1y2HyS3hAR5STKHI3fog2bp7FOG_len2AB1y2Hy2CE3Y47S3hAR5STKHI3fog2bp7FOG_len8STKHI_472AB1y2HyS3hAR5STKHI3fog7FOG_lenS3hAR5STKHI3fog7FOG_len1c2AB2lo2hi2H12H3S3hAR5STKHI3fog7FOG_len8STKHI_47FS3hAR1p5STKHI3fog7FOG_lenS3hAR1p5STKHI3fog7FOG_len2AB2S21HS3hAR1p5STKHI3fog7FOG_len2G32G42G52G6S3hAR5STKHI3fog7FOG_len1c2IMS3hAR1p5STKHI3fog7FOG_len1x2Q2S3hAR5STKHI3fog7FOG_len1x2AB2lo1n2Hx2H03H47S3hAR1p5STKHI3fog7FOG_len1x2Tx2AB2G12G22G32G42G52G6S3hAR1p5STKHI3fog7FOG_len1x2Tx2AB2iv2I22I52G12G22G32G42G52G62Q1S3hAR5STKHI3fog7FOG_lenS3hAR5STKHI3fog7FOG_len1c2IMS3hAR5STKHI3fog7FOG_len2AB1y2Hy3iv'2J12J22J41H2H0S3hAR5STKHI3fog7FOG_len1x2AB1e2E12E22lo1n2H01D2Q12Q2S3hAR5STKHI3fog2bp7FOG_len2AB1y2Hy3iv'2J22J52CE2DA1HS3hAR5STKHI3fog7FOG_lenS3hAR5STKHI3fog7FOG_len1t2AB2T3S3hAR5STKHI3fog7FOG_len1t2T1S3hAR5STKHI3fog7FOG_lenS3hAR5STKHI3fog7FOG_len1cS3hAR5STKHI3fog2bp7FOG_len2AB1y2Hy2CES3hAR5STKHI3fog7FOG_len1c2AB2lo2hi2H12H2S3hAR5STKHI3fog2v07FOG_len1c2STS3hAR5STKHI3fog7FOG_len". (* [comment removed for export] *)
  #[using="sp fs HCN HMOD HAC HSP HFOG M FOG_len STKHI_gt STKHI_pg STKHI_47 STKHI_len TF_ok"] Theorem h0_lazy_good : ltac2:(CDefT.buildp (gd_tbl_AH0K2 ()) "Px,$>.P,(4<.$42.(4=.$42.Vv0,)R1.)P,(9.$44.(45.(4>.R2.)VLz,)$23.)(49.$42.Vv0,(4>.R3.))")
(* [comment removed for export] *).
  Proof.
    intros x AOK HL. mm X. clear Mfog Mres Mlim Mhalt Mfds Mfs Mtot Misp Mbrk Msbrk Meager Mabytes Mminv. uvals.
    pose proof aceil_bounds as AB. pose proof ACEIL_pg as AP. pose proof (r_s1 p HCN) as S1. pose proof (r_s2 p HCN) as S2.
    destruct (lazy_page _ HL) as (iv & Hiv & I1 & I2 & I4 & I5 & e & He & E1 & E2).
    (* [comment removed for export] *)
    assert (EAGER : forall lo n, lo mod 4096 = 0 -> n mod 4096 = 0 -> lo <= x < lo + n -> 0 <= lo -> lo + n <= 2 ^ 64 ->
                    (zE e <= lo \/ lo + n <= zB e) -> vgood AL0 v0 (page_base_of x)).
    { intros lo n Hl Hn Hx H0 H47 D. exfalso. rewrite (u_pbo x) in E1, E2 by lia.
      destruct (pbo_in x lo n Hl Hn Hx) as [Q1 Q2]. unfold zB, zE in *. lia. }
    (* [comment removed for export] *)
    assert (STK : forall y, stk64 (L0_of bp) <= y < l_stk_hi (L0_of bp) -> page_in_ranges (page_base_of y) Lz = true -> False).
    { intros y Hy HLy. destruct (lazy_page _ HLy) as (iv' & _ & J1 & J2 & _ & J5 & _).
      assert (CE : ACEIL <= stk64 (L0_of bp)).
      { unfold stk64. apply ACEIL_le_hull64. cbn [L0_of l_stk_lo bp bp_of bp_sp0]. fold (SP p). rewrite HAC. unfold SP, STKPG.
        pose proof (Z.div_mod (uv p v_s2) 256 ltac:(lia)). pose proof (Z.mod_pos_bound (uv p v_s2) 256 ltac:(lia)). lia. }
      assert (Y47 : y < 2 ^ 47) by (cbn [L0_of l_stk_hi bp bp_of bp_stkhi] in Hy; lia).
      rewrite (u_pbo y) in J1, J2 by lia.
      pose proof (Z.div_mod ACEIL 4096 ltac:(lia)) as DA. rewrite AP, Z.add_0_r in DA.
      assert (ACEIL / 4096 <= y / 4096) by (apply Z.div_le_mono; lia). lia. }
    assert (IMGNO : forall y, 0x10000 <= y < 0x65f000 -> page_in_ranges (page_base_of y) Lz = true -> False).
    { intros y Hy HLy. destruct (lazy_page _ HLy) as (iv' & _ & J1 & J2 & J4 & _ & _). rewrite (u_pbo y) in J1, J2 by lia.
      destruct (pbo_in y 0x10000 0x64f000 eq_refl eq_refl ltac:(lia)). lia. }
    destruct AOK as [CS | [(c & CSc & Hx) | IMG]].
    - (* [comment removed for export] *) destruct CS as [ST | [(IM & _ & _) | (t & Ht & TC & Tx)]].
      + exfalso. exact (STK x ST HL).
      + exfalso. cbn [v0 vst_of v_img fst snd] in IM. exact (IMGNO x IM HL).
      + unfold v0 in Ht. cbn [vst_of v_tr] in Ht. fold h0 in Ht. rewrite tr_of_h0' in Ht. unfold EXTRA in Ht. rewrite !map_app in Ht. cbn [map fst snd app] in Ht.
        pose proof (PG_range p HCN v_dnodes ltac:(pv)) as [G1 A1]. pose proof (PG_range p HCN v_dstore ltac:(pv)) as [G2 A2].
        pose proof (PG_range p HCN v_thr ltac:(pv)) as [G3 A3]. pose proof (PG_range p HCN v_treg ltac:(pv)) as [G4 A4].
        pose proof (PG_range p HCN v_fstk ltac:(pv)) as [G5 A5]. pose proof (PG_range p HCN v_dtls ltac:(pv)) as [G6 A6].
        pose proof (r_prim p HCN) as PR. pose proof (r_pslack p HCN) as PS.
        unfold t_hi in Tx.
        destruct Ht as [<-|[<-|[<-|[<-|[<-|[<-|[<-|Ht]]]]]]]; cbn [t_lo t_len node_tr store_tr ri_tr] in Tx, TC.
        * (* [comment removed for export] *) apply (EAGER (PG p v_dnodes) (2 ^ 20)); auto; try lia.
        * (* [comment removed for export] *) rewrite (u_pbo x) in * by lia.
          destruct (pbo_in x (PG p v_dstore) (2 ^ 23) A2 eq_refl Tx) as [Q1 Q2].
          apply (good_store p STKHI FOG TF); rewrite ?(u_pbo x) by lia; [lia | lia | apply Z_mod_mult].
        * (* [comment removed for export] *) change (ri_base (L0_of bp)) with (SB p + 2 ^ 37) in Tx. ddestruct Mri as (_ & _ & _ & RL).
          apply (EAGER (SB p + 2 ^ 37) 4096); auto; unfold SB, PG in *; try lia.
          replace (4096 * uv p v_prim - 4096 * uv p v_pslack + 0x10000 + 2 ^ 37) with ((uv p v_prim - uv p v_pslack + 16 + 2 ^ 25) * 4096) by lia. apply Z_mod_mult.
        * apply (EAGER (PG p v_thr) 4096); auto; lia.
        * apply (EAGER (PG p v_treg) 0x10000); auto; lia.
        * apply (EAGER (PG p v_fstk) kFakeBytes); auto; unfold kFakeBytes in *; lia.
        * apply (EAGER (PG p v_dtls) 4096); auto; lia.
        * (* [comment removed for export] *) exfalso. cbn in Ht.
          repeat (destruct Ht as [<-|Ht]; [cbn in TC; discriminate TC|]).
          apply in_app_iff in Ht as [Ht|Ht].
          -- apply in_map_iff in Ht as (r & <- & Hr). cbn in TC. discriminate TC.
          -- cbn in Ht. repeat (destruct Ht as [<-|Ht]; [cbn in TC; discriminate TC|]). destruct Ht.
    - (* [comment removed for export] *)
      assert (PB : forall lo hi, lo <= c < hi -> 0 <= lo -> hi <= 2 ^ 47 -> bv_unsigned (page_base_of x) = zpb (shadow_of AL0 c)).
      { intros lo hi H1 H2 H3. rewrite Hx. unfold zpb, shadow_of, AL0. cbn [al_sb]. apply u_pbo.
        assert (0 <= c / 8) by (apply Z.div_pos; lia). assert (c / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). lia. }
      destruct CSc as [ST | [(IM & _ & _) | (t & Ht & TC & Tc)]].
      + apply (good_shb (fst (v_stk v0), snd (v_stk v0) - fst (v_stk v0)) c); [left; reflexivity | cbn [fst snd]; lia |].
        cbn [v0 vst_of v_stk fst snd] in ST |- *.
        assert (CE : 0 <= stk64 (L0_of bp)) by (unfold stk64; pose proof (Z.mod_pos_bound (l_stk_lo (L0_of bp)) 64 ltac:(lia)); cbn [L0_of l_stk_lo bp bp_of bp_sp0] in *; fold (SP p) in *; unfold SP in *; lia).
        apply (PB (stk64 (L0_of bp)) (l_stk_hi (L0_of bp))); [exact ST | exact CE | cbn [L0_of l_stk_hi bp bp_of bp_stkhi]; lia].
      + apply (good_shb (0x10000, 0x64f000) c); [apply cs_img | cbn [v0 vst_of v_img fst snd] in IM |- *; lia |].
        cbn [v0 vst_of v_img fst snd] in IM. apply (PB 0x10000 0x65f000); lia.
      + pose proof (proj1 (Forall_forall _ _) (proj1 (h0_vwf p HCN STKHI FOG TF HAC STKHI_gt STKHI_pg STKHI_47 STKHI_len fog_ok fog_len TF_ok fog_seps fog_apart)) t Ht) as (T1 & T2 & T3 & _).
        apply (good_shb (t_lo t, t_len t) c); [apply (cs_tr p STKHI FOG TF t Ht TC) | cbn [fst snd]; unfold t_hi in Tc; lia |].
        apply (PB (t_lo t) (t_hi t)); [exact Tc | lia | pose proof aceil_lt47; lia].
    - (* [comment removed for export] *) exfalso. cbn [al_img_lo al_img_hi AL0] in IMG. exact (IMGNO x IMG HL).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="sp fs HCN HMOD HAC HSP HFOG M N Lz FOG_len FOG_small STKHI_gt STKHI_pg STKHI_47 STKHI_len TF_ok"] Theorem h0_HKv : HKv AL0 v0 md.
  Proof.
    unfold HKv. pose proof HMOD as X. unfold me_model in X. ddestruct X as (Mhalt & _ & _ & _ & Mlim & _ & _ & Mwf & _).
    split; [exact Mhalt|].
    split; [exact (minv_nodup _ _ (MM_minv sp fs p md HMOD))|].
    split; [apply Forall_forall; intros pg Hpg; exact (h0_mat_good sp fs p HCN STKHI FOG TF md HMOD HAC HSP pg Hpg)|].
    split; [exact h0_lazy_good|].
    split; [rewrite Mlim; reflexivity|].
    split; [exact (proj1 h0_budget)|]. split; [exact (proj2 h0_budget)|].
    split; [exact Mwf|].
    split; [exact h0_vm_table|].
    split; [exact h0_vcensus|].
    split; [exact (proj1 h0_reserved)|].
    split; [exact (proj2 h0_reserved)|].
    split; [exact (h0_vwf p HCN STKHI FOG TF HAC STKHI_gt STKHI_pg STKHI_47 STKHI_len fog_ok fog_len TF_ok fog_seps fog_apart)|].
    exact h0_atop.
  Qed.

  #[using="sp fs HCN HMOD HAC HSP HFOG v0 M N Lz FOG_len FOG_small STKHI_gt STKHI_pg STKHI_47 STKHI_len TF_ok"] Theorem h0_HK : HK AL0 h0 md.
  Proof. split; [exact h0_HKv | exact (h0_vranges p HCN STKHI FOG TF HAC STKHI_gt fog_ok fog_len TF_ok)]. Qed.

End K2.
