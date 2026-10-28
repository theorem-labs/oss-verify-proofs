(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import MState.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import BackingAlgebra.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AFreeSlot AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm AVst AVstT.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AVstE () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.alayout"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_mapped_user"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_reg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_mapped_fa"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_nb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_dep"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_bl"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.shdr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_chunks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_sec"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_sech"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_acct"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_pa_committed"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_emb"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.HK"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kEmbBytes"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "Corelib.Init.Datatypes.app"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.v_eb"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.vst_of"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vnb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.CE"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.VLIMIT"; "ARUN_1.R_emb"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.anon_grant"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vcs"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.trange"; "Corelib.Lists.ListDef.map"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.node_tr"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.store_tr"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.sec_tr"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.units_of"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.ri_tr"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.pa_tr"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.zseq"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.kPaSlice"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.fixed_of"; "ARUN_1.tr_base"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_hi"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_lo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_lo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_hi"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_b6"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.kPrimHullLen"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_pa"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.kPaHullLen"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.

(* [comment removed for export] *)
Definition R_emb (h : ahst) (a : Z) (h' : ahst) : Prop := ltac2:(CDefT.buildp (gd_tbl_AVstE ()) "(0.(1.$2.(3.O1.)(3.O3.))(0.Pc',$4.(1.$4.(5.(6.O1.R1.))(5.(6.O3.R1.)))(0.Pc',$4.(1.$4.(7.(6.O1.R1.))(7.(6.O3.R1.)))(0.(1.(8.$4.)(9.(:.O1.))(9.(:.O3.)))(0.(1.(8.$4.)(;.(:.O1.))(;.(:.O3.)))(0.(1.(8.$<.)(=.(>.O1.))(=.(>.O3.)))(0.(1.(8.(?.$4.$4.))(10.(11.O1.))(10.(11.O3.)))(0.(1.$4.(12.O1.)(12.O3.))(0.(1.$4.(13.(11.O3.))=)(0.(1.$4.(13.(11.O1.))O2.)(14.(1.$4.O2.=))))))))))))")
(* [comment removed for export] *).

#[using="Type"] Lemma vst_of_emb : forall h a h', R_emb h a h' -> vperm (v_add_eager (vst_of h) a kEmbBytes true) (vst_of h').
Proof.
  (intros h a h' dd_H; ddestruct dd_H as (EL & EU & EF & ENB & EBL & ESC & EGH & EPA & E0 & E1 & NZ)).
  assert (UE : units_of h' = units_of h) by (apply units_of_ext; assumption).
  assert (T0 : emb_tr h = []) by (unfold emb_tr; rewrite E0; reflexivity).
  assert (T1 : emb_tr h' = [TR a kEmbBytes KEager true true]).
  { unfold emb_tr. rewrite E1. destruct (Z.eqb_spec a 0) as [E|_]; [exfalso; exact (NZ E)| reflexivity]. }
  assert (E2 : forall l, zsum (fun c => r_mapped_user (h_reg h' c) + r_mapped_fa (h_reg h' c)) l = zsum (fun c => r_mapped_user (h_reg h c) + r_mapped_fa (h_reg h c)) l).
  { induction l as [|c l IH]; [reflexivity|]. cbn [zsum]. rewrite EU, EF, IH. reflexivity. }
  unfold vperm, vst_of, v_add_eager. cbn [v_tr v_hulls v_ghost v_stk v_img v_eb v_cover v_cb20 v_cb23 v_unit].
  rewrite EL, EGH. split; [| split; [| repeat split; try reflexivity]].
  - unfold tr_of. rewrite T0, T1, ENB, EBL, ESC, EPA, EL, UE. rewrite app_nil_r. rewrite !app_assoc. apply Permutation_cons_append.
  - unfold cover_of. rewrite T0, T1, EL, ENB, EBL, ESC, EGH. cbn [map t_lo t_len]. rewrite app_nil_r. rewrite !app_assoc. apply Permutation_cons_append.
  - unfold eb_of. rewrite T0, T1, ENB, ESC, EGH, EPA, E2. cbn [zsum t_len]. lia.
  - unfold cb_of, cover_of. rewrite T0, T1, EL, ENB, EBL, ESC, EGH. cbn [map t_lo t_len]. rewrite !zsum_app. cbn [zsum snd]. lia.
  - unfold cb_of, cover_of. rewrite T0, T1, EL, ENB, EBL, ESC, EGH. cbn [map t_lo t_len]. rewrite !zsum_app. cbn [zsum snd]. lia.
Qed.

Section TRANS.
  Variable AL : asan_layout.
  Hypothesis ALWF : al_wf AL.
  Hypothesis ASB : al_sb AL = 0x7fff8000.
  Hypothesis IML : al_img_lo AL <= 0x10000.
  Hypothesis IMH : al_img_hi AL = 0x65f000.

  #[using="ASB IML IMH"] Theorem HK_emb : ltac2:(CDefT.buildp (gd_tbl_AVstE ()) "Ph,$15.Pmo,$16.Pa,(17.&40.)Ph',$15.P,(18.VhAR,VAL,R4.R3.)Zua,$4.(19.&40.R3.)P,(1.$4.(1:.R1.+1000.)=)P,(1;.=R2.)P,(1<.(1=.R3.$1>.)(1?.VhAR,))P,(1.$20.(21.(22.(?.(17.&40.)(17.&40.))(23.(24.R8.))(25.(24.R8.)))R7.(26.&40.$1>.))$27.)P,(1<.(1=.(1=.(28.(29.R:.))(2:.+1000.(2;.(29.R:.))))$2<.)$2=.)P,(2>.R;.R6.R8.)(0.(18.VhAR,VAL,R9.(2?.+22.R:.$1>.R;.))(0.(30.(31.VAL,(29.R9.))R7.$1>.)(0.(1<.+65?000.R7.)(32.(1<.(1=.R7.$1>.)+7???7000.)(1<.+10007???8000.R7.)))))")
(* [comment removed for export] *).
  Proof.
    intros h mo a h' K ua AAL A0 ACE RF SL RE. pose proof K as [Kv VR]. unfold kEmbBytes in *.
    assert (N16 : bv_unsigned (Z_to_bv 64 0x10000) = 0x10000) by (apply u64_lit; lia).
    pose proof (HKv_fresh_above_img AL (vst_of h) mo a (Z_to_bv 64 0x10000) Kv RF A0 IML ltac:(rewrite IMH; lia) ltac:(rewrite N16; lia) ltac:(rewrite N16; exact ACE)) as IMA. rewrite IMH in IMA. fold ua in IMA.
    pose proof (HKv_fresh_band AL (vst_of h) mo a (Z_to_bv 64 0x10000) Kv RF ltac:(rewrite N16; lia)) as BND. rewrite N16 in BND. fold ua in BND.
    pose proof (HKv_grant_eager AL (vst_of h) mo a 0x10000 true Kv ltac:(rewrite ASB; lia) ltac:(rewrite ASB; lia) AAL A0 ACE ltac:(lia) eq_refl ltac:(rewrite IMH; exact IMA) RF) as K'.
    cbn zeta in K'. fold ua in K'. specialize (K' ltac:(rewrite vnb_add_eager; unfold CE, npg_shadow, kEmbBytes in SL; cbn [v_eb v_add_eager]; clear - SL; lia)).
    pose proof (vst_of_emb h ua h' RE) as P. unfold kEmbBytes in P.
    split; [| split; [| exact (conj IMA BND)]].
    - apply (HK_perm AL h' _ _ P K'). apply vranges_ok_eager; [exact VR| lia| lia].
    - intros x Hx. apply (proj1 (vcs_perm AL _ _ x P)). unfold vcs, v_add_eager. cbn [v_tr v_stk v_img]. right. right.
      eexists. split; [left; reflexivity|]. unfold t_hi. cbn. exact (conj eq_refl Hx).
  Qed.
End TRANS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tr_base (h : ahst) : list trange := ltac2:(CDefT.buildp (gd_tbl_AVstE ()) "ZL,$2.(3.O1.)(22.$33.(34.$4.$33.$35.(9.(:.O1.)))(22.$33.(34.$4.$33.$36.(;.(:.O1.)))(22.$33.(34.$<.$33.$37.(=.(>.O1.)))(22.$33.(38.O1.)(22.$33.(39.$33.(3:.R1.)(3;.$33.))(22.$33.(34.$4.$33.(3<.R1.)(3=.(3>.(12.O1.)$3?.)))(40.R1.)))))))")
(* [comment removed for export] *).

#[using="Type"] Lemma tr_of_base : forall h, tr_of h = tr_base h ++ emb_tr h.
Proof. intros h. unfold tr_of, tr_base. cbn zeta. rewrite <- !app_assoc. reflexivity. Qed.

#[using="Type"] Lemma tr_base_ext : ltac2:(CDefT.buildp (gd_tbl_AVstE ()) "Ph,$15.Ph',$15.P,(1.$2.(3.R1.)(3.R2.))P,Pc,$4.(1.$4.(5.(6.R3.R1.))(5.(6.R4.R1.)))P,Pc,$4.(1.$4.(7.(6.R4.R1.))(7.(6.R5.R1.)))P,(1.(8.$4.)(9.(:.R4.))(9.(:.R5.)))P,(1.(8.$4.)(;.(:.R5.))(;.(:.R6.)))P,(1.(8.$<.)(=.(>.R6.))(=.(>.R7.)))P,(1.$4.(12.R7.)(12.R8.))(1.(8.$33.)(41.R8.)(41.R9.))")
(* [comment removed for export] *).
Proof. intros h h' EL EU EF ENB EBL ESC EPA. unfold tr_base. rewrite (units_of_ext h h' EL EU EF), EL, ENB, EBL, ESC, EPA. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma trb_node : forall h b, In b (d_nb (h_dep h)) -> In (node_tr b) (tr_base h).
Proof. intros h b Hb. unfold tr_base. rewrite !in_app_iff. left. apply in_map. exact Hb. Qed.
#[using="Type"] Lemma trb_store : forall h b, In b (d_bl (h_dep h)) -> In (store_tr b) (tr_base h).
Proof. intros h b Hb. unfold tr_base. rewrite !in_app_iff. right. left. apply in_map. exact Hb. Qed.
#[using="Type"] Lemma trb_sec : forall h sh, In sh (s_chunks (h_sec h)) -> In (sec_tr sh) (tr_base h).
Proof. intros h sh Hs. unfold tr_base. rewrite !in_app_iff. right. right. left. apply in_map. exact Hs. Qed.
#[using="Type"] Lemma trb_T : forall h, In (TR (l_T (h_L h)) 4096 KEager true true) (tr_base h).
Proof. intros h. unfold tr_base. rewrite !in_app_iff. do 6 right. unfold fixed_of. rewrite !in_app_iff. left. cbn. auto. Qed.
#[using="Type"] Lemma trb_ctx : forall h, In (TR (l_ctx (h_L h)) (l_ctxlen (h_L h)) KEager true true) (tr_base h).
Proof. intros h. unfold tr_base. rewrite !in_app_iff. do 6 right. unfold fixed_of. rewrite !in_app_iff. left. cbn. auto. Qed.
#[using="Type"] Lemma trb_fs : forall h, In (TR (l_fs (h_L h)) kFakeBytes KEager true true) (tr_base h).
Proof. intros h. unfold tr_base. rewrite !in_app_iff. do 6 right. unfold fixed_of. rewrite !in_app_iff. left. cbn. auto. Qed.
#[using="Type"] Lemma trb_dtls : forall h, In (TR (l_dtls (h_L h)) 4096 KEager true true) (tr_base h).
Proof. intros h. unfold tr_base. rewrite !in_app_iff. do 6 right. unfold fixed_of. rewrite !in_app_iff. left. cbn. auto. Qed.

Section EMBGEO.
  Variable AL : asan_layout.

  (* [comment removed for export] *)
  #[using="Type"] Lemma emb_apart : ltac2:(CDefT.buildp (gd_tbl_AVstE ()) "Ph,$15.Pmo,$16.Pt,$33.P,(18.VhAR,VAL,R3.R2.)P,(14.(1.$4.(13.(11.R4.))=))P,(42.$33.R3.(41.R5.))(32.(1<.(43.R4.)(13.(11.R6.)))(1<.(1=.(13.(11.R6.))$1>.)(44.R4.)))")
(* [comment removed for export] *).
  Proof.
    intros h mo t K NZ Ht.
    assert (EE : emb_tr h = [TR (a_emb (h_acct h)) kEmbBytes KEager true true]) by (unfold emb_tr; destruct (Z.eqb_spec (a_emb (h_acct h)) 0) as [E|_]; [exfalso; exact (NZ E)| reflexivity]).
    pose proof (tr_of_NoDup AL h mo K) as ND. rewrite tr_of_base, EE in ND.
    destruct (tr_apart AL h mo t (TR (a_emb (h_acct h)) kEmbBytes KEager true true) K) as [E|[X|X]].
    - rewrite tr_of_base. apply in_app_iff. left. exact Ht.
    - rewrite tr_of_base, EE. apply in_app_iff. right. left. reflexivity.
    - exfalso. apply (NoDup_app_in _ _ t ND Ht). left. symmetry. exact E.
    - left. cbn [t_lo] in X. exact X.
    - right. unfold t_hi in X. cbn [t_lo t_len] in X. exact X.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma emb_geom : ltac2:(CDefT.buildp (gd_tbl_AVstE ()) "Ph,$15.Pmo,$16.P,(18.VhAR,VAL,R2.R1.)P,(14.(1.$4.(13.(11.R3.))=))Za,$4.(13.(11.R4.))(0.(1<.+1000.R1.)(0.(1<.(1=.R1.$1>.)(1?.VhAR,))(0.(1.$4.(1:.R1.+1000.)=)(0.(32.(1<.(1=.R1.$1>.)(45.VAL,))(1<.(46.VAL,)R1.))(0.(32.(1<.(1=.R1.$1>.)+7???7000.)(1<.+10007???8000.R1.))(0.(32.(1<.(1=.R1.$1>.)(47.(3.R5.)))(1<.(1=.(47.(3.R5.))$48.)R1.))(32.(1<.(1=.R1.$1>.)(49.(3.R5.)))(1<.(1=.(49.(3.R5.))$4:.)R1.))))))))")
(* [comment removed for export] *).
  Proof.
    intros h mo K NZ a.
    assert (IN : In (TR a kEmbBytes KEager true true) (tr_of h)).
    { rewrite tr_of_base. apply in_app_iff. right. unfold emb_tr. fold a. destruct (Z.eqb_spec a 0) as [E|_]; [exfalso; exact (NZ E)| left; reflexivity]. }
    destruct (tr_wf AL h mo _ K IN) as (W0 & W1 & W2 & W3 & W4 & W5 & W6). unfold t_hi in *. cbn [t_lo t_len t_cs] in *. specialize (W6 eq_refl).
    split; [exact W0|]. split; [exact W2|]. split; [exact W3|]. split; [exact W5|]. split; [exact W6|].
    split.
    - destruct (hulls_apart_tr AL h mo _ (l_b6 (h_L h), kPrimHullLen) K IN ltac:(left; reflexivity)) as [(_ & _ & LIT & _)|X]; [discriminate LIT|]. unfold t_hi in X. cbn [t_lo t_len fst snd] in X. exact X.
    - destruct (hulls_apart_tr AL h mo _ (l_pa (h_L h), kPaHullLen) K IN ltac:(right; left; reflexivity)) as [(_ & _ & LIT & _)|X]; [discriminate LIT|]. unfold t_hi in X. cbn [t_lo t_len fst snd] in X. exact X.
  Qed.
End EMBGEO.

End ARUN_1.
