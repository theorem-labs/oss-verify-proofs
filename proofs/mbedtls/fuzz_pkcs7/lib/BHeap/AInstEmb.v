(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import MState HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import BackingAlgebra.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv AKFrame. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AFreeSlot AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm AVst AInstDepot AInstPop AVstT AVstE AInstGen.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import APop APopGen APopEmb HMLib HM AHeapR AInstMallocG AW_Populate AW_EmbCfg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AInstEmb () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_emb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_acct"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vcs"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.AL0"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.vst_of"; "ARUN_1.G.hx"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kEmbBytes"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.BHeap.AInstMallocG.KhF"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_nb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_dep"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_bl"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.true"; "ARUN_1.G.KxF"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.anon_grant"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "ARUN_1.G.CSxh"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.HK"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.bwf"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_havol"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_mapped_fa"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_reg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kFreeArrayMapSize"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kFreeArraySize"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.awf'"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_EmbCfg.b12_siteS"; "RocqVerifyHarness.AgentSubmission.BHeap.AInstGen.CSh"; "ARUN_1.KxF"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.emb_P"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.emb_cap"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_esz"].

Section ARUN_1. Context {hAR : arun}.

(* [comment removed for export] *)
#[using="Type"] Lemma HK_kinv : forall AL h, kinv AL (vcs AL (vst_of h)) (HK AL h).
Proof.
  intros AL h. split.
  - intros mo [K W]. exact (ki_halted (HKv_kinv AL _ W) mo K).
  - intros mo [K W]. exact (ki_top (HKv_kinv AL _ W) mo K).
  - intros mo acc [K W] OK. destruct (ki_mat (HKv_kinv AL _ W) mo acc K OK) as (mo' & E & K' & MM).
    exists mo'. split; [exact E|]. split; [exact (conj K' W)| exact MM].
Qed.

(* [comment removed for export] *)

Section G.
  Variables (h : ahst) (c : Z) (mo0 : Model).
  Hypothesis K0 : HK AL0 h mo0.
  Hypothesis B : bwf h.
  Hypothesis HV : h_havol h <= AVOL_MAX.
  Hypothesis Hc : 1 <= c <= 31.
  Hypothesis ROOMF : r_mapped_fa (h_reg h c) + kFreeArrayMapSize <= kFreeArraySize.
  Set Default Proof Using "K0 B HV Hc ROOMF".

  Local Notation nb0 := (d_nb (h_dep h)).
  Local Notation bl0 := (d_bl (h_dep h)).
  Local Notation CS := (CSh AL0 h c).
  Local Notation KF := (KhF h c mo0).

  Definition hx (a : Z) : ahst := emb_h h a (a_esz (h_acct h)).
  Definition xvalid (a : Z) : Prop := a_emb (h_acct h) = 0 /\ a <> 0 /\ exists mo, HK AL0 (hx a) mo.
  Definition CSxh (a : Z) (x : Z) : Prop := CS None None nb0 bl0 x \/ (xvalid a /\ a <= x < a + kEmbBytes).
  Definition KxF (a : Z) (mo : Model) : Prop := a_emb (h_acct h) = 0 /\ a <> 0 /\ HK AL0 (hx a) mo /\ mo_frame mo0 mo.

  Lemma R_emb_hx : forall a, a_emb (h_acct h) = 0 -> a <> 0 -> R_emb h a (hx a).
  Proof. intros a E0 NZ. unfold R_emb, hx, emb_h. cbn. repeat split; try reflexivity; assumption. Qed.

  (* [comment removed for export] *)
  Lemma vcs_hx : ltac2:(CDefT.buildp (gd_tbl_AInstEmb ()) "Pa,$0.Px,$0.P,(1.$0.(2.(3.Vh,))=)P,(4.(1.$0.R3.=))(5.(6.$7.(8.(9.R4.))R3.)(:.(6.$7.(8.Vh,)R3.)(;.(<.R4.R3.)(=.R3.(>.R4.$?.)))))")
(* [comment removed for export] *).
  Proof.
    intros a x E0 NZ. rewrite <- (vcs_perm AL0 _ _ x (vst_of_emb h a (hx a) (R_emb_hx a E0 NZ))).
    unfold vcs, v_add_eager. cbn [v_tr v_stk v_img]. split.
    - intros [A|[A|(t & [<-|Ht] & TC & R)]]; [left; left; exact A| left; right; left; exact A| right; unfold t_hi in R; cbn in R; exact R| left; right; right; exists t; auto].
    - intros [[A|[A|(t & Ht & R)]]|R]; [left; exact A| right; left; exact A| right; right; exists t; split; [right; exact Ht| exact R]|].
      right. right. eexists. split; [left; reflexivity|]. unfold t_hi. cbn. exact (conj eq_refl R).
  Qed.

  Lemma CSxh_sub : forall a, xvalid a -> forall x, CSxh a x -> vcs AL0 (vst_of (hx a)) x.
  Proof.
    (intros a dd_H; ddestruct dd_H as (E0 & NZ & _); intros x [X|[_ X]]); apply (proj2 (vcs_hx a x E0 NZ)); [left; exact (proj1 (CSh_entry AL0 h c x) X)| right; exact X].
  Qed.

  Lemma MX_CSOKx : forall a, cs_ok AL0 (CSxh a).
  Proof.
    intros a.
    dpose (MG_CSOK h c mo0 K0 B HV Hc ROOMF None None nb0 bl0) as (C1 & C2 & C3 & C4).
    assert (V : xvalid a -> cs_ok AL0 (vcs AL0 (vst_of (hx a)))).
    { (intros dd_H; ddestruct dd_H as (_ & _ & mo & KX)). apply vcs_cs_ok; [exact (HK_vwf AL0 _ mo KX)| exact AL0_wf| exact AL0_sb| rewrite AL0_IMH; lia| exact (proj2 (proj2 AL0_GOT64))| exact (proj2 (proj2 AL0_GSB64))]. }
    split; [| split; [| split; [| exact C4]]].
    - intros x [X|[XV X]].
      + ddestruct (C1 x X) as (A1 & A2 & A3 & A4). repeat split; try assumption; try lia. intros [Y|[XV Y]]; [exact (A4 Y)|].
        destruct (V XV) as (D1 & _). ddestruct (D1 x (CSxh_sub a XV x (or_introl X))) as (_ & _ & _ & D4). apply D4. apply (CSxh_sub a XV). right. exact (conj XV Y).
      + destruct (V XV) as (D1 & _). ddestruct (D1 x (CSxh_sub a XV x (or_intror (conj XV X)))) as (A1 & A2 & A3 & A4). repeat split; try assumption; try lia.
        intros Y. exact (A4 (CSxh_sub a XV _ Y)).
    - intros i Hi. destruct (C2 i Hi) as [A1 A2]. split; intros [Y|[XV Y]]; try (first [exact (A1 Y)| exact (A2 Y)]);
        ddestruct (V XV) as (_ & D2 & _); destruct (D2 i Hi) as [E1 E2]; [apply E1| apply E2]; apply (CSxh_sub a XV); right; exact (conj XV Y).
    - intros x i [X|[XV X]] Hi; [exact (C3 x i X Hi)|]. ddestruct (V XV) as (_ & _ & D3 & _). exact (D3 x i (CSxh_sub a XV x (or_intror (conj XV X))) Hi).
  Qed.

  Lemma MX_KxL : forall a, kinv AL0 (CSxh a) (KxF a).
  Proof.
    intros a. split.
    - (intros mo dd_H; ddestruct dd_H as (_ & _ & K & _)). exact (ki_halted (HK_kinv AL0 (hx a)) mo K).
    - (intros mo dd_H; ddestruct dd_H as (_ & _ & K & _)). exact (ki_top (HK_kinv AL0 (hx a)) mo K).
    - (intros mo acc dd_H; ddestruct dd_H as (E0 & NZ & K & FR); intros OK).
      assert (XV : xvalid a) by (split; [exact E0| split; [exact NZ| exists mo; exact K]]).
      destruct (ki_mat (HK_kinv AL0 (hx a)) mo acc K (acc_ok_mono AL0 _ _ acc (CSxh_sub a XV) OK)) as (mo' & E & K' & MM).
      exists mo'. split; [exact E|]. split; [| exact MM]. split; [exact E0|]. split; [exact NZ|]. split; [exact K'|].
      eapply mo_frame_trans; [exact FR| apply mo_frame_mat; exact MM].
  Qed.

  Lemma MX_CSx_inc : forall a y, CS None None nb0 bl0 y -> CSxh a y.
  Proof. intros a y H. left. exact H. Qed.

  (* [comment removed for export] *)
  Lemma MX_entry_HK : forall mo, KF None None nb0 bl0 mo -> HK AL0 h mo /\ mo_frame mo0 mo.
  Proof.
    intros mo KK. ddestruct (MG_exit h c mo0 K0 B HV Hc ROOMF None None nb0 bl0 mo h KK) as (sn & sb & E1 & E2 & _ & _ & _ & _ & _ & _ & _ & FR & EX).
    assert (sn = []) as -> by (apply (app_inv_head nb0); rewrite app_nil_r; symmetry; exact E1).
    assert (sb = []) as -> by (apply (app_inv_head bl0); rewrite app_nil_r; symmetry; exact E2).
    split; [| exact FR]. apply EX. unfold R_gen. cbn [unit_if AInstGen.unit_if]. rewrite !app_nil_r. repeat split; try reflexivity; intros; lia.
  Qed.

  (* [comment removed for export] *)
  Theorem MX_T_emb : ltac2:(CDefT.buildp (gd_tbl_AInstEmb ()) "Pmo,$10.Pa,(11.&40.)P,(1.$0.(2.(3.Vh,))=)P,(12.VhAR,Vh,Vc,Vmo0,(13.$14.)(13.$14.)(15.(16.Vh,))(17.(16.Vh,))R3.)P,(1.$0.(18.(19.&40.R3.)+1000.)=)P,(=.=(19.&40.R4.))P,(<.(>.(19.&40.R5.)$?.)(1:.VhAR,))P,(1.$14.(1;.(1<.(1=.(11.&40.)(11.&40.))(1>.(1?.R7.))(20.(1?.R7.)))R6.(21.&40.$?.))$22.)(;.(23.(19.&40.R7.)(24.+22.R7.$?.R8.))(;.(25.(26.(19.&40.R7.))(19.&40.R7.)$?.)(;.(<.+65?000.(19.&40.R7.))(:.(<.(>.(19.&40.R7.)$?.)+7???7000.)(<.+10007???8000.(19.&40.R7.))))))")
(* [comment removed for export] *).
  Proof.
    intros mo a E0 KK AAL A0 ACE RF. destruct (MX_entry_HK mo KK) as [K FR].
    assert (NZ : bv_unsigned a <> 0) by lia.
    destruct (HK_emb AL0 AL0_sb AL0_IML AL0_IMH h mo a (hx (bv_unsigned a)) K AAL A0 ACE RF
                ltac:(apply vst_slack; [exact B| exact HV| unfold CE, npg_shadow, kEmbBytes; cbn; lia]) (R_emb_hx _ E0 NZ)) as (K' & CR & I0 & BD).
    split; [split; [exact E0| split; [exact NZ| split; [exact K'| eapply mo_frame_trans; [exact FR| apply mo_frame_anon_grant]]]]|].
    split; [| exact (conj I0 BD)].
    intros x Hx. right. split; [| exact Hx]. split; [exact E0| split; [exact NZ| eexists; exact K']].
  Qed.

  (* [comment removed for export] *)
  Theorem MX_exit : forall xa mo h', Kfx (KF None None nb0 bl0) KxF xa mo ->
    h_L h' = h_L h -> (forall j, r_mapped_user (h_reg h' j) = r_mapped_user (h_reg h j)) -> (forall j, r_mapped_fa (h_reg h' j) = r_mapped_fa (h_reg h j)) ->
    d_nb (h_dep h') = nb0 -> d_bl (h_dep h') = bl0 -> s_chunks (h_sec h') = s_chunks (h_sec h) -> a_sech (h_acct h') = a_sech (h_acct h) ->
    h_pa_committed h' = h_pa_committed h ->
    a_emb (h_acct h') = match xa with Some a => a | None => a_emb (h_acct h) end ->
    HK AL0 h' mo /\ mo_frame mo0 mo /\ (forall x, CSfx (CS None None nb0 bl0) CSxh xa x <-> vcs AL0 (vst_of h') x).
  Proof.
    intros xa mo h' KK EL EU EF ENB EBL ESC EGH EPA EEM. destruct xa as [a|]; cbn [Kfx CSfx] in *.
    - ddestruct KK as (E0 & NZ & K & FR).
      assert (EV : vst_of h' = vst_of (hx a)) by (apply vst_of_ext; unfold hx, emb_h; cbn; assumption).
      split; [unfold HK in *; rewrite EV; exact K|]. split; [exact FR|]. intros x. rewrite EV. split.
      + apply CSxh_sub. split; [exact E0| split; [exact NZ| eexists; exact K]].
      + intros X. apply (proj1 (vcs_hx a x E0 NZ)) in X. destruct X as [X|X]; [left; exact (proj2 (CSh_entry AL0 h c x) X)| right; split; [| exact X]].
        split; [exact E0| split; [exact NZ| eexists; exact K]].
    - destruct (MX_entry_HK mo KK) as [K FR].
      assert (EV : vst_of h' = vst_of h) by (apply vst_of_ext; assumption).
      split; [unfold HK in *; rewrite EV; exact K|]. split; [exact FR|]. intros x. rewrite EV. exact (CSh_entry AL0 h c x).
  Qed.
End G.

(* [comment removed for export] *)
Definition b12_siteT : Prop := ltac2:(CDefT.buildp (gd_tbl_AInstEmb ()) "Ph,$27.Pc,$0.Pmo0,$10.P,(28.VhAR,$7.R3.R1.)P,(29.VhAR,R4.)P,(<.(2:.R5.)$2;.)P,(;.(<.+1.R5.)(<.R5.+1?.))P,(<.(>.(2<.(2=.R7.R6.))$2>.)$2?.)P,(30.VhAR,R8.)(31.VhAR,(32.VhAR,$7.R9.R8.(13.$14.)(13.$14.)(15.(16.R9.))(17.(16.R9.)))(12.VhAR,R9.R8.R7.(13.$14.)(13.$14.)(15.(16.R9.))(17.(16.R9.)))(33.R9.R7.)(34.(2.(3.R9.)))(2.(3.R9.))(35.(2.(3.R9.)))(36.(3.R9.)))")
(* [comment removed for export] *).

End ARUN_1.
