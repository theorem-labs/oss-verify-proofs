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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import APop APopGen APopEmb HMLib HM AHeapR AInstMallocG AW_Populate AW_EmbCfg AInstEmb AW_B12Walk.
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
Ltac2 gd_tbl_AInstEmbT () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "stdpp.bitvector.definitions.bv"; "Stdlib.ZArith.BinInt.Z.le"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.awf'"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_EmbCfg.emb_wf"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.emb_P"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_emb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_acct"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.emb_cap"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_esz"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_B12Walk.b12_laws"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.AL0"; "RocqVerifyHarness.AgentSubmission.BHeap.AInstGen.CSh"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_nb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_dep"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_bl"; "RocqVerifyHarness.AgentSubmission.BHeap.AInstMallocG.KhF"; "RocqVerifyHarness.AgentSubmission.BHeap.AInstEmb.CSxh"; "RocqVerifyHarness.AgentSubmission.BHeap.AInstEmb.KxF"].

Section ARUN_1. Context {hAR : arun}.

(* [comment removed for export] *)
#[using="Type"] Lemma region_free_prefix' : ltac2:(CDefT.buildp (gd_tbl_AInstEmbT ()) "Pmaps,(0.(1.(2.&40.)(2.&40.)))Pb,(2.&40.)Psmall,(2.&40.)Pbig,(2.&40.)P,(3.(4.&40.R2.)(4.&40.R1.))P,(5.$6.(7.R5.R4.R2.)$8.)(5.$6.(7.R6.R5.R4.)$8.)")
(* [comment removed for export] *).
Proof.
  induction maps as [|[a sz] maps IH]; intros b small big Hle Hfree; [reflexivity|].
  cbn [region_free] in Hfree |- *. apply andb_true_iff in Hfree as [Hhead Htail].
  apply andb_true_iff. split; [| eapply IH; eassumption].
  apply negb_true_iff in Hhead. apply negb_true_iff. unfold iv_overlap in Hhead |- *.
  apply andb_false_iff in Hhead. apply andb_false_iff.
  destruct Hhead as [Hhead|Hhead]; [left| right]; apply Z.ltb_ge in Hhead; apply Z.ltb_ge; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma emb_wf_of_awf : ltac2:(CDefT.buildp (gd_tbl_AInstEmbT ()) "Ph,$9.P,(:.VhAR,R1.)(;.(<.(=.(>.R2.)))(=.(>.R2.))(?.(=.(>.R2.)))(10.(>.R2.)))")
(* [comment removed for export] *).
Proof.
  (intros h dd_H; ddestruct dd_H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & WX & _)). ddestruct WX as (_ & _ & _ & _ & _ & X6 & X7 & _).
  unfold emb_wf, emb_P, emb_cap. split.
  - intros E. rewrite E. cbn. destruct X6 as [[_ SZ]|(_ & P0 & _)]; [auto| exfalso; rewrite E in P0; lia].
  - intros NZ. destruct (Z.eqb_spec (a_emb (h_acct h)) 0) as [E|_]; [exfalso; exact (NZ E)|]. split; [reflexivity|]. split; [reflexivity|].
    destruct X6 as [[E _]|(_ & _ & _ & _ & _ & _ & SZ0)]; [exfalso; exact (NZ E)|]. split; [exact SZ0|].
    pose proof (csum_le (epi h) (fun _ => 2) (fun c _ => epi_le2 h c)) as LE.
    assert (E62 : csum (fun _ => 2) = 62) by (unfold csum, cls31; cbn; reflexivity). rewrite E62 in LE. unfold EM in *. lia.
Qed.

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

  (* [comment removed for export] *)
  Lemma MX_ROOM_e : forall mo, KF None None nb0 bl0 mo -> exists a, anon_grantable 0x22 kEmbBytes mo a.
  Proof.
    intros mo KK.
    ddestruct (MG_ROOM_n h c mo0 K0 B HV Hc ROOMF None None nb0 bl0 mo (MG_Gn h c mo0 K0 B HV Hc ROOMF None None) KK) as (a & AAL & A0 & FL & CE & RF & BU).
    exists a. unfold anon_grantable, kEmbBytes. split; [exact AAL|]. split; [exact A0|]. split; [exact FL|]. split; [clear - CE; lia|]. split.
    - eapply region_free_prefix'; [| exact RF]. rewrite !u64_lit by lia. lia.
    - intros E. specialize (BU E). clear - BU. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma MX_emb_cs : a_emb (h_acct h) <> 0 -> crange (CS None None nb0 bl0) (a_emb (h_acct h)) kEmbBytes.
  Proof.
    intros NZ x Hx. apply (proj2 (CSh_entry AL0 h c x)).
    apply (vcs_of_tr AL0 h (TR (a_emb (h_acct h)) kEmbBytes KEager true true)); [| reflexivity| unfold t_hi; cbn [t_lo t_len]; exact Hx].
    rewrite tr_of_base. apply in_app_iff. right. unfold emb_tr. destruct (Z.eqb_spec (a_emb (h_acct h)) 0) as [E|_]; [exfalso; exact (NZ E)| left; reflexivity].
  Qed.

  Theorem MX_laws : ltac2:(CDefT.buildp (gd_tbl_AInstEmbT ()) "P,(:.VhAR,Vh,)(11.VhAR,$12.(13.VhAR,$12.Vh,Vc,(14.$6.)(14.$6.)(15.(16.Vh,))(17.(16.Vh,)))(18.VhAR,Vh,Vc,Vmo0,(14.$6.)(14.$6.)(15.(16.Vh,))(17.(16.Vh,)))(19.VhAR,Vh,Vc,)(1:.VhAR,Vh,Vmo0,)(<.(=.(>.Vh,)))(=.(>.Vh,))(?.(=.(>.Vh,)))(10.(>.Vh,)))")
(* [comment removed for export] *).
  Proof.
    intros AW. unfold b12_laws.
    split; [exact (MG_CSOK h c mo0 K0 B HV Hc ROOMF None None nb0 bl0)|].
    split; [exact (MG_KL h c mo0 K0 B HV Hc ROOMF None None nb0 bl0)|].
    split; [exact (MX_CSOKx h c mo0 K0 B HV Hc ROOMF)|].
    split; [exact (MX_KxL h c mo0 K0 B HV Hc ROOMF)|].
    split; [exact (MX_CSx_inc h c mo0 K0 B HV Hc ROOMF)|].
    split; [intros mo a n KK; exact (MG_apart h c mo0 K0 B HV Hc ROOMF None None nb0 bl0 mo a n KK)|].
    split; [intros mo a E0 KK; exact (MX_T_emb h c mo0 K0 B HV Hc ROOMF mo a E0 KK)|].
    split; [intros mo _ KK; exact (MX_ROOM_e mo KK)|].
    split; [exact MX_emb_cs|]. split; [exact (emb_wf_of_awf h AW)|].
    (* [comment removed for export] *)
    intros NZ. ddestruct AW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & WX & _). ddestruct WX as (_ & _ & _ & _ & _ & X6 & _).
    destruct X6 as [[E _]|(LH & _ & CE & _)]; [exfalso; exact (NZ E)|].
    split; [apply (lowhigh_big _ kEmbBytes LH); unfold kEmbBytes; lia| exact CE].
  Qed.
End G.
Unset Default Proof Using.

(* [comment removed for export] *)
#[using="Type"] Theorem b12_siteT_of_walk : b12_walk_T -> b12_siteT.
Proof.
  intros W h c mo0 K0 B HV Hc ROOMF AW.
  exact (W AL0 AL0_img AL0_wf AL0_sb _ _ (CSxh h c) _ _ _ _ _ (MX_laws h c mo0 K0 B HV Hc ROOMF AW)).
Qed.

End ARUN_1.
