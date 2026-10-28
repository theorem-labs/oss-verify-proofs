(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import MState HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import BackingAlgebra.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv AKFrame. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AFreeSlot AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm AVst AKinvM AVmScar AInstDepot AInstPop AVstT AInstGen.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_DepotB AW_DepotTop AW_MallocB HMLib HM HMFrame AHeapR.
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
Ltac2 gd_tbl_AInstMallocG () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.BHeap.AInstGen.UOKh"; "ARUN_1.G.KhF"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_nb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_dep"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_bl"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.BHeap.AInstGen.UAh"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Logic.or"; "LinuxProcessSemantics.LinuxProcessSem.State.map_contains"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.prod"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_commit"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_fresh"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.BHeap.AInstGen.FAh"; "RocqVerifyHarness.AgentSubmission.AHeap.ASysS.fixrw_grantable"; "RocqVerifyHarness.AgentSubmission.BHeap.AKinvM.scar_site"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.AL0"; "RocqVerifyHarness.AgentSubmission.BHeap.AInstGen.CSh"; "Corelib.Init.Datatypes.list"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_lo"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_hi"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.BHeap.AInstGen.Gnh"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.anon_grant"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.BHeap.AInstGen.Gsh"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.AHeap.ASysS.anon_grantable"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.BHeap.AInstDepot.sane"; "Corelib.Init.Peano.le"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Datatypes.false"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.BHeap.AInstGen.R_gen"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.HK"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vcs"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.vst_of"].

Section ARUN_1. Context {hAR : arun}.

#[using="Type"] Lemma AL0_IML : al_img_lo AL0 <= 0x10000. Proof. cbn. lia. Qed.
#[using="Type"] Lemma AL0_IMH : al_img_hi AL0 = 0x65f000. Proof. reflexivity. Qed.
#[using="Type"] Lemma AL0_GOT64 : al_img_lo AL0 + 64 <= al_got AL0 /\ al_got AL0 + 128 <= al_img_hi AL0 /\ al_got AL0 mod 8 = 0. Proof. cbn. lia. Qed.
#[using="Type"] Lemma AL0_GSB64 : al_img_lo AL0 + 64 <= al_gsb AL0 /\ al_gsb AL0 + 128 <= al_img_hi AL0 /\ al_gsb AL0 mod 8 = 0. Proof. cbn. lia. Qed.

Section G.
  Variables (h : ahst) (c : Z) (mo0 : Model).
  Hypothesis K0 : HK AL0 h mo0.
  Hypothesis B : bwf h.
  Hypothesis HV : h_havol h <= AVOL_MAX.
  Hypothesis Hc : 1 <= c <= 31.
  Hypothesis ROOMF : r_mapped_fa (h_reg h c) + kFreeArrayMapSize <= kFreeArraySize.
  (* [comment removed for export] *)
  Set Default Proof Using "K0 B HV Hc ROOMF".

  Local Notation nb0 := (d_nb (h_dep h)).
  Local Notation bl0 := (d_bl (h_dep h)).
  Local Notation v0 := (vst_of h).
  Local Notation UA := (UAh h c).
  Local Notation FAA := (FAh h c).
  Local Notation UOK := (UOKh h c).
  Local Notation CS := (CSh AL0 h c).

  (* [comment removed for export] *)
  Definition KhF (u f : option bool) (nb bl : list Z) (mo : Model) : Prop := Kh AL0 h c u f nb bl mo /\ mo_frame mo0 mo.

  Lemma VR0 : vranges_ok AL0 v0. Proof. exact (proj2 K0). Qed.
  Lemma VWF0 : vwf AL0 v0. Proof. exact (HK_vwf AL0 h mo0 K0). Qed.
  Lemma HH : In (HB h) (v_hulls v0). Proof. left. reflexivity. Qed.
  Lemma H68 : 0x65f000 <= fst (HB h). Proof. exact (h_H68 AL0 h c B Hc ROOMF). Qed.
  Lemma HU : fst (HB h) <= UA /\ UA + 2^18 <= fst (HB h) + snd (HB h) /\ UA mod 4096 = 0. Proof. exact (h_HU AL0 h c B Hc ROOMF). Qed.
  Lemma HF : fst (HB h) <= FAA /\ FAA + 2^18 <= fst (HB h) + snd (HB h) /\ FAA mod 4096 = 0. Proof. exact (h_HF AL0 h c B Hc ROOMF). Qed.
  Lemma UF : UOK -> UA + 2^18 <= FAA \/ FAA + 2^18 <= UA. Proof. exact (h_UF AL0 h c B Hc ROOMF). Qed.
  Lemma APT_U : UOK -> forall t, In t (v_tr v0) -> UA + 2^18 <= t_lo t \/ t_hi t <= UA. Proof. exact (h_APT_U AL0 h c mo0 K0 B Hc). Qed.
  Lemma APT_F : forall t, In t (v_tr v0) -> FAA + 2^18 <= t_lo t \/ t_hi t <= FAA. Proof. exact (h_APT_F AL0 h c mo0 K0 B Hc ROOMF). Qed.
  Lemma SLACK : v_eb v0 + 4096 * vnb v0 + RES_GEN <= VLIMIT. Proof. exact (h_SLACK AL0 h B HV). Qed.
  Lemma CB20 : v_cb20 v0 < J20. Proof. exact (h_CB20 AL0 h B HV). Qed.
  Lemma CB23 : v_cb23 v0 + (2^20 / 2^23 + 2) < J23. Proof. exact (h_CB23 AL0 h B HV). Qed.
  (* [comment removed for export] *)
  Lemma UUN : UOK -> v_unit v0 UA (2^18).
  Proof.
    intros OK. dpose (bwf_breg h B c ltac:(unfold kNumClasses; lia)) as (MU0 & MUAL & MULIM & MFAL & MFAB).
    cbn [vst_of v_unit]. unfold UAh. apply (uunit_unit (h_L h) c _ (bwf_L h B) Hc MU0 MUAL). unfold UOKh, kUserMapSize, kUserLimit, kRegionSize in *. clear - OK. lia.
  Qed.
  Lemma FUN : v_unit v0 FAA (2^18).
  Proof.
    dpose (bwf_breg h B c ltac:(unfold kNumClasses; lia)) as (MU0 & MUAL & MULIM & MFAL & MFAB).
    cbn [vst_of v_unit]. unfold FAh. apply (funit_unit (h_L h) c _ (bwf_L h B) Hc); [clear - MFAB; lia| exact MFAL| exact ROOMF].
  Qed.
  Lemma HC : In (HB h) (v_cover v0).
  Proof. cbn [vst_of v_cover]. unfold cover_of, hulls_of, HB. apply in_app_iff. left. left. reflexivity. Qed.

  Ltac gfacts := first [ exact AL0_wf | exact AL0_sb | exact AL0_IML | exact AL0_IMH | exact AL0_GOT64 | exact AL0_GSB64
                       | exact VR0 | exact VWF0 | exact HH | exact H68 | exact HU | exact HF | exact UF | exact APT_U | exact APT_F
                       | exact UUN | exact FUN | exact SLACK | exact CB20 | exact CB23 | exact HC | eassumption ].

  Lemma MG_CSOK : forall u f nb bl, cs_ok AL0 (CS u f nb bl).
  Proof. intros. unfold CSh. eapply (G_CSOK AL0); gfacts. Qed.

  Lemma MG_KL : forall u f nb bl, kinv AL0 (CS u f nb bl) (KhF u f nb bl).
  Proof. intros. unfold KhF, Kh, CSh. apply kinv_KF. eapply (G_KL AL0); gfacts. Qed.

  Lemma MG_noshadow : forall u f nb bl x, CS u f nb bl x -> ~ (0x7fff8000 <= x < 0x10007fff8000).
  Proof. intros u f nb bl x Hx. unfold CSh in Hx. eapply (G_noshadow AL0) in Hx; gfacts. Qed.

  Lemma MG_CSmono_u : forall b f y, CS None f nb0 bl0 y -> CS (Some b) f nb0 bl0 y.
  Proof. intros. unfold CSh in *. apply G_CSmono_u. assumption. Qed.
  Lemma MG_CSmono_f : forall u b y, CS u None nb0 bl0 y -> CS u (Some b) nb0 bl0 y.
  Proof. intros. unfold CSh in *. apply G_CSmono_f. assumption. Qed.
  Lemma MG_CSmono_n : forall u f nb bl a x, CS u f nb bl x -> CS u f (nb ++ [a]) bl x.
  Proof. intros. unfold CSh in *. apply G_CSmono_n. assumption. Qed.
  Lemma MG_CSmono_s : forall u f nb bl a x, CS u f nb bl x -> CS u f nb (bl ++ [a]) x.
  Proof. intros. unfold CSh in *. apply G_CSmono_s. assumption. Qed.

  Lemma MG_LEDGER_U : ltac2:(CDefT.buildp (gd_tbl_AInstMallocG ()) "Pmo,$0.P,(1.Vh,Vc,)P,(2.(3.$4.)(3.$4.)(5.(6.Vh,))(7.(6.Vh,))R2.)(8.(9.$4.(:.(;.(<.R3.))(=.&40.(>.Vh,Vc,))(=.&40.(?.+2.+12.)))$10.)(11.(9.$4.(12.(13.(<.R3.))(=.&40.(>.Vh,Vc,))(=.&40.(?.+2.+12.)))$10.)(9.$4.(:.(14.(15.(16.&40.)(16.&40.))(;.(<.R3.))(13.(<.R3.)))(=.&40.(>.Vh,Vc,))(=.&40.(?.+2.+12.)))$10.)))")
(* [comment removed for export] *).
  Proof. intros mo OK [K _]. eapply (G_LEDGER_U AL0) in K; [exact K| gfacts ..]. Qed.
  Lemma MG_TU_commit : ltac2:(CDefT.buildp (gd_tbl_AInstMallocG ()) "Pmo,$0.P,(1.Vh,Vc,)P,(2.(3.$4.)(3.$4.)(5.(6.Vh,))(7.(6.Vh,))R2.)P,(9.$4.(12.(13.(<.R3.))(=.&40.(>.Vh,Vc,))(=.&40.(?.+2.+12.)))$10.)(2.(17.$4.$10.)(3.$4.)(5.(6.Vh,))(7.(6.Vh,))(18.+32.(>.Vh,Vc,)(?.+2.+12.)R4.))")
(* [comment removed for export] *).
  Proof.
    intros mo OK [K FR] MC. split; [eapply (G_TU_commit AL0) in K; [exact K| gfacts ..]|].
    eapply mo_frame_trans; [exact FR| apply mo_frame_fixrw_commit].
  Qed.
  Lemma MG_TU_fresh : ltac2:(CDefT.buildp (gd_tbl_AInstMallocG ()) "Pmo,$0.P,(1.Vh,Vc,)P,(2.(3.$4.)(3.$4.)(5.(6.Vh,))(7.(6.Vh,))R2.)P,(9.$4.(:.(14.(15.(16.&40.)(16.&40.))(;.(<.R3.))(13.(<.R3.)))(=.&40.(>.Vh,Vc,))(=.&40.(?.+2.+12.)))$10.)(2.(17.$4.$10.)(3.$4.)(5.(6.Vh,))(7.(6.Vh,))(19.+32.(>.Vh,Vc,)(?.+2.+12.)R4.))")
(* [comment removed for export] *).
  Proof.
    intros mo OK [K FR] RF. split; [eapply (G_TU_fresh AL0) in K; [exact K| gfacts ..]|].
    eapply mo_frame_trans; [exact FR| apply mo_frame_fixrw_fresh].
  Qed.
  Lemma MG_ROOM_U : forall mo, UOK -> KhF None None nb0 bl0 mo -> fixrw_grantable 0x32 UA (2^18) mo.
  Proof. intros mo OK [K _]. eapply (G_ROOM_U AL0) in K; [exact K| gfacts ..]. Qed.
  Lemma MG_LEDGER_F : ltac2:(CDefT.buildp (gd_tbl_AInstMallocG ()) "Pu,(1:.$4.)Pmo,$0.P,(11.(9.(1:.$4.)R2.(3.$4.))(9.(1:.$4.)R2.(17.$4.$10.)))P,(2.R3.(3.$4.)(5.(6.Vh,))(7.(6.Vh,))R2.)(8.(9.$4.(:.(;.(<.R3.))(=.&40.(1;.Vh,Vc,))(=.&40.(?.+2.+12.)))$10.)(11.(9.$4.(12.(13.(<.R3.))(=.&40.(1;.Vh,Vc,))(=.&40.(?.+2.+12.)))$10.)(9.$4.(:.(14.(15.(16.&40.)(16.&40.))(;.(<.R3.))(13.(<.R3.)))(=.&40.(1;.Vh,Vc,))(=.&40.(?.+2.+12.)))$10.)))")
(* [comment removed for export] *).
  Proof. intros u mo Hu [K _]. eapply (G_LEDGER_F AL0) in K; [exact K| gfacts ..]. Qed.
  Lemma MG_TF_commit : ltac2:(CDefT.buildp (gd_tbl_AInstMallocG ()) "Pu,(1:.$4.)Pmo,$0.P,(11.(9.(1:.$4.)R2.(3.$4.))(9.(1:.$4.)R2.(17.$4.$10.)))P,(2.R3.(3.$4.)(5.(6.Vh,))(7.(6.Vh,))R2.)P,(9.$4.(12.(13.(<.R3.))(=.&40.(1;.Vh,Vc,))(=.&40.(?.+2.+12.)))$10.)(2.R5.(17.$4.$10.)(5.(6.Vh,))(7.(6.Vh,))(18.+32.(1;.Vh,Vc,)(?.+2.+12.)R4.))")
(* [comment removed for export] *).
  Proof.
    intros u mo Hu [K FR] MC. split; [eapply (G_TF_commit AL0) in K; [exact K| gfacts ..]|].
    eapply mo_frame_trans; [exact FR| apply mo_frame_fixrw_commit].
  Qed.
  Lemma MG_TF_fresh : ltac2:(CDefT.buildp (gd_tbl_AInstMallocG ()) "Pu,(1:.$4.)Pmo,$0.P,(11.(9.(1:.$4.)R2.(3.$4.))(9.(1:.$4.)R2.(17.$4.$10.)))P,(2.R3.(3.$4.)(5.(6.Vh,))(7.(6.Vh,))R2.)P,(9.$4.(:.(14.(15.(16.&40.)(16.&40.))(;.(<.R3.))(13.(<.R3.)))(=.&40.(1;.Vh,Vc,))(=.&40.(?.+2.+12.)))$10.)(2.R5.(17.$4.$10.)(5.(6.Vh,))(7.(6.Vh,))(19.+32.(1;.Vh,Vc,)(?.+2.+12.)R4.))")
(* [comment removed for export] *).
  Proof.
    intros u mo Hu [K FR] RF. split; [eapply (G_TF_fresh AL0) in K; [exact K| gfacts ..]|].
    eapply mo_frame_trans; [exact FR| apply mo_frame_fixrw_fresh].
  Qed.
  Lemma MG_ROOM_F : ltac2:(CDefT.buildp (gd_tbl_AInstMallocG ()) "Pu,(1:.$4.)Pmo,$0.P,(11.(9.(1:.$4.)R2.(3.$4.))(9.(1:.$4.)R2.(17.$4.$10.)))P,(2.R3.(3.$4.)(5.(6.Vh,))(7.(6.Vh,))R2.)(1<.+32.(1;.Vh,Vc,)(?.+2.+12.)R3.)")
(* [comment removed for export] *).
  Proof. intros u mo Hu [K _]. eapply (G_ROOM_F AL0) in K; [exact K| gfacts ..]. Qed.
  (* [comment removed for export] *)
  Lemma MG_SCAR_U : UOK -> scar_site AL0 (CS None None nb0 bl0) (KhF None None nb0 bl0) UA (2^18).
  Proof. intros OK. unfold KhF, Kh, CSh. apply (scar_site_KF AL0). eapply (G_SCAR_U AL0); gfacts. Qed.
  Lemma MG_SCAR_F : ltac2:(CDefT.buildp (gd_tbl_AInstMallocG ()) "Pu,(1:.$4.)P,(11.(9.(1:.$4.)R1.(3.$4.))(9.(1:.$4.)R1.(17.$4.$10.)))(1=.VhAR,$1>.(1?.VhAR,$1>.Vh,Vc,R2.(3.$4.)(5.(6.Vh,))(7.(6.Vh,)))(2.R2.(3.$4.)(5.(6.Vh,))(7.(6.Vh,)))(1;.Vh,Vc,)(?.+2.+12.))")
(* [comment removed for export] *).
  Proof. intros u Hu. unfold KhF, Kh, CSh. apply (scar_site_KF AL0). eapply (G_SCAR_F AL0); gfacts. Qed.

  Lemma MG_CSUz : forall f, crange (CS (Some true) f nb0 bl0) UA (2^18).
  Proof. intros. unfold CSh. apply G_CSUz. Qed.
  Lemma MG_CSFz : forall u, crange (CS u (Some true) nb0 bl0) FAA (2^18).
  Proof. intros. unfold CSh. apply G_CSFz. Qed.

  Lemma MG_apart : ltac2:(CDefT.buildp (gd_tbl_AInstMallocG ()) "Pu,(1:.$4.)Pf,(1:.$4.)Pnb,(20.$21.)Pbl,(20.$21.)Pmo,$0.Pa,(16.&40.)Pw,(16.&40.)P,(2.R7.R6.R5.R4.R3.)P,(9.$4.(:.(14.(15.(16.&40.)(16.&40.))(;.(<.R4.))(13.(<.R4.)))R3.R2.)$10.)P,(22.+10000.(23.&40.R3.))P,(22.(24.(23.&40.R5.)(23.&40.R4.))(25.VhAR,))Px,$21.P,(11.(1?.VhAR,$1>.Vh,Vc,R<.R;.R:.R9.R1.)(8.(22.(26.$1>.)R1.)(27.R1.(28.$1>.))))(29.(8.(22.(23.&40.R8.)R2.)(27.R2.(24.(23.&40.R8.)(23.&40.R7.)))))")
(* [comment removed for export] *).
  Proof. intros u f nb bl mo a w [K _] RF W16 CE x Hx. unfold CSh in Hx. exact (G_apart AL0 AL0_GOT64 AL0_GSB64 _ _ _ _ _ _ HU HF _ u f nb bl mo a w K RF W16 CE x Hx). Qed.

  Lemma MG_T_node : ltac2:(CDefT.buildp (gd_tbl_AInstMallocG ()) "Pu,(1:.$4.)Pf,(1:.$4.)Pnb,(20.$21.)Pbl,(20.$21.)Pmo,$0.Pa,(16.&40.)P,(2:.Vh,R6.R5.R4.R3.)P,(2.R7.R6.R5.R4.R3.)P,(9.$21.(2;.(23.&40.R3.)+1000.)=)P,(27.=(23.&40.R4.))P,(22.(24.(23.&40.R5.)(?.+2.+14.))(25.VhAR,))P,(9.$4.(:.(14.(15.(16.&40.)(16.&40.))(;.(<.R7.))(13.(<.R7.)))R6.(=.&40.(?.+2.+14.)))$10.)(8.(2.R<.R;.(14.$21.R:.(2<.$21.(23.&40.R7.)(2=.$21.)))R9.(2>.+22.R7.(?.+2.+14.)R8.))(2?.(1?.VhAR,$1>.Vh,Vc,R<.R;.(14.$21.R:.(2<.$21.(23.&40.R7.)(2=.$21.)))R9.)(23.&40.R7.)(?.+2.+14.)))")
(* [comment removed for export] *).
  Proof.
    intros u f nb bl mo a G [K FR] AAL A0 ACE RF.
    eapply (G_T_node AL0) in K; [| gfacts ..]. destruct K as [K' C'].
    split; [| exact C']. split; [exact K'|]. eapply mo_frame_trans; [exact FR| apply mo_frame_anon_grant].
  Qed.
  Lemma MG_T_store : ltac2:(CDefT.buildp (gd_tbl_AInstMallocG ()) "Pu,(1:.$4.)Pf,(1:.$4.)Pnb,(20.$21.)Pbl,(20.$21.)Pmo,$0.Pa,(16.&40.)P,(30.Vh,R6.R5.R4.R3.)P,(2.R7.R6.R5.R4.R3.)P,(9.$21.(2;.(23.&40.R3.)+1000.)=)P,(27.=(23.&40.R4.))P,(22.(24.(23.&40.R5.)(?.+2.+17.))(25.VhAR,))P,(9.$4.(:.(14.(15.(16.&40.)(16.&40.))(;.(<.R7.))(13.(<.R7.)))R6.(=.&40.(?.+2.+17.)))$10.)(8.(2.R<.R;.R:.(14.$21.R9.(2<.$21.(23.&40.R7.)(2=.$21.)))(2>.+4022.R7.(?.+2.+17.)R8.))(2?.(1?.VhAR,$1>.Vh,Vc,R<.R;.R:.(14.$21.R9.(2<.$21.(23.&40.R7.)(2=.$21.))))(23.&40.R7.)(?.+2.+17.)))")
(* [comment removed for export] *).
  Proof.
    intros u f nb bl mo a G [K FR] AAL A0 ACE RF.
    eapply (G_T_store AL0) in K; [| gfacts ..]. destruct K as [K' C'].
    split; [| exact C']. split; [exact K'|]. eapply mo_frame_trans; [exact FR| apply mo_frame_anon_grant].
  Qed.
  Lemma MG_ROOM_n : ltac2:(CDefT.buildp (gd_tbl_AInstMallocG ()) "Pu,(1:.$4.)Pf,(1:.$4.)Pnb,(20.$21.)Pbl,(20.$21.)Pmo,$0.P,(2:.Vh,R5.R4.R3.R2.)P,(2.R6.R5.R4.R3.R2.)(31.(16.&40.)La,(16.&40.)(32.VhAR,+22.(?.+2.+14.)R4.R1.))")
(* [comment removed for export] *).
  Proof. intros u f nb bl mo G [K _]. eapply (G_ROOM_n AL0) in K; [exact K| gfacts ..]. Qed.
  Lemma MG_ROOM_s : ltac2:(CDefT.buildp (gd_tbl_AInstMallocG ()) "Pu,(1:.$4.)Pf,(1:.$4.)Pnb,(20.$21.)Pbl,(20.$21.)Pmo,$0.P,(30.Vh,R5.R4.R3.R2.)P,(2.R6.R5.R4.R3.R2.)(31.(16.&40.)La,(16.&40.)(32.VhAR,+4022.(?.+2.+17.)R4.R1.))")
(* [comment removed for export] *).
  Proof. intros u f nb bl mo G [K _]. eapply (G_ROOM_s AL0) in K; [exact K| gfacts ..]. Qed.

  (* [comment removed for export] *)
  Lemma MG_entry : KhF None None nb0 bl0 mo0.
  Proof. split; [exact (Kh_entry AL0 h c mo0 K0)| apply mo_frame_refl]. Qed.
  Lemma MG_Gn : forall u f, Gnh h u f nb0 bl0. Proof. intros. split; reflexivity. Qed.
  Lemma MG_Gs : forall u f, Gsh h u f nb0 bl0. Proof. intros. split; [reflexivity| left; reflexivity]. Qed.
  Lemma MG_Gsx : forall u f x, Gsh h u f (nb0 ++ [x]) bl0. Proof. intros. split; [reflexivity| right; exists x; reflexivity]. Qed.

  Theorem MG_exit : ltac2:(CDefT.buildp (gd_tbl_AInstMallocG ()) "Pu,(1:.$4.)Pf,(1:.$4.)Pnb,(20.$21.)Pbl,(20.$21.)Pmo,$0.Ph',$33.P,(2.R6.R5.R4.R3.R2.)(31.(20.$21.)Lsn,(20.$21.)(31.(20.$21.)Lsb,(20.$21.)(8.(9.(20.$21.)R7.(14.$21.(5.(6.Vh,))R2.))(8.(9.(20.$21.)R6.(14.$21.(7.(6.Vh,))R1.))(8.(34.$21.(35.VhAR,(?.+2.+14.))R2.)(8.(34.$21.(35.VhAR,(?.+2.+17.))R1.)(8.(36.(37.$21.R2.)#1.)(8.(36.(37.$21.R1.)#1.)(8.(29.(9.(1:.$4.)R9.(17.$4.$38.)))(8.(29.(9.(1:.$4.)R8.(17.$4.$38.)))(8.P,(9.(1:.$4.)R9.(17.$4.$10.))(1.Vh,Vc,)(8.(39.Vmo0,R5.)P,(3:.Vh,Vc,R9.R8.R2.R1.R4.)(8.(3;.VhAR,$1>.R5.R6.)Px,$21.(3<.(1?.VhAR,$1>.Vh,Vc,R;.R:.R9.R8.R1.)(3=.$1>.(3>.R6.)R1.)))))))))))))))")
(* [comment removed for export] *).
  Proof.
    intros u f nb bl mo h' [K FR].
    ddestruct (HK_gen_exit AL0 AL0_GOT64 AL0_GSB64 h c mo0 K0 B Hc ROOMF u f nb bl mo h' K)
      as (sn & sb & E1 & E2 & F1 & F2 & L1 & L2 & NU & NF & UK & EX).
    dexists sn, sb. repeat (split; [assumption|]). exact EX.
  Qed.
End G.

End ARUN_1.
