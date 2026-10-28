(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX AW_FreeP AW_FreeR. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv AKinvM AW_FreeK AW_FreeFam.
Import ListNotations.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AW_FreeFamU () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeK.WFK"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kNumClasses"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_mapped_user"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_reg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kUserMapSize"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kUserLimit"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeP.h_ugrow"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Stdlib.ZArith.BinInt.Z.pow"; "ARUN_1.Fam.Kg"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Datatypes.bool"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.region_beg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Logic.or"; "LinuxProcessSemantics.LinuxProcessSem.State.map_contains"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.prod"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_commit"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_fresh"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.

Definition usel (h : ahst) (c : Z) (u : option bool) : ahst := match u with Some _ => h_ugrow h c | None => h end.
Definition gsel (h : ahst) (c : Z) (u f : option bool) : ahst := fsel (usel h c u) c f.

#[using="Type"] Lemma usel_L : forall h c u, h_L (usel h c u) = h_L h. Proof. intros h c [b|]; reflexivity. Qed.
#[using="Type"] Lemma gsel_L : forall h c u f, h_L (gsel h c u f) = h_L h. Proof. intros h c u f. unfold gsel. rewrite fsel_L. apply usel_L. Qed.
#[using="Type"] Lemma usel_fa : forall h c u c', r_mapped_fa (h_reg (usel h c u) c') = r_mapped_fa (h_reg h c').
Proof. intros h c [b|] c'; [| reflexivity]. cbn. unfold fupd. destruct (Z.eqb_spec c' c) as [->|NE]; reflexivity. Qed.
#[using="Type"] Lemma usel_mu : forall h c u c', r_mapped_user (h_reg (usel h c u) c') = r_mapped_user (h_reg h c') + (if c' =? c then match u with Some _ => kUserMapSize | None => 0 end else 0).
Proof. intros h c [b|] c'; cbn; unfold fupd; [destruct (Z.eqb_spec c' c) as [->|NE]; cbn; lia| destruct (c' =? c); lia]. Qed.
#[using="Type"] Lemma gsel_mu : forall h c u f c', r_mapped_user (h_reg (gsel h c u f) c') = r_mapped_user (h_reg (usel h c u) c').
Proof. intros h c u [b|] c'; [| reflexivity]. unfold gsel. cbn. unfold fupd. destruct (Z.eqb_spec c' c) as [->|NE]; reflexivity. Qed.
#[using="Type"] Lemma gsel_fa : forall h c u f c', r_mapped_fa (h_reg (gsel h c u f) c') = r_mapped_fa (h_reg h c') + (if c' =? c then match f with Some _ => kFreeArrayMapSize | None => 0 end else 0).
Proof. intros h c u [b|] c'; unfold gsel; cbn; unfold fupd; [destruct (Z.eqb_spec c' c) as [->|NE]; cbn; rewrite ?usel_fa; lia| destruct (c' =? c); rewrite ?usel_fa; lia]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma WFK_ugrow : ltac2:(CDefT.buildp (gd_tbl_AW_FreeFamU ()) "Ph,$0.Pc,$1.P,(2.VhAR,R2.)P,(3.(4.+1.R2.)(5.R2.$6.))P,(4.(7.(8.(9.R4.R3.))$:.)$;.)(2.VhAR,(<.R5.R4.))")
(* [comment removed for export] *).
Proof.
  (intros h c dd_H; ddestruct dd_H as (WL & WR & WS & WD & WB & WBIG & WG & HV); intros Hc ROOM).
  split; [exact WL|]. split; [| exact (conj WS (conj WD (conj WB (conj WBIG (conj WG HV)))))].
  intros c' Hc'. cbn zeta. unfold h_ugrow. cbn [h_reg set_reg]. unfold fupd.
  pose proof (WR c' Hc') as X. cbn zeta in X.
  destruct (Z.eqb_spec c' c) as [->|NE]; [| exact X].
  ddestruct X as (X0 & X1 & X2 & X3 & X4 & X5 & X6). cbn [r_mapped_user r_alloc_user r_mapped_fa r_fa]. unfold r_nfreed in *. cbn [r_fa].
  split; [intros E; exfalso; lia|].
  split; [unfold kUserMapSize in *; lia|].
  split. { unfold kUserMapSize in *. rewrite Z.add_mod, X2 by lia. reflexivity. }
  split; [exact ROOM|]. split; [exact X4|]. split; [exact X5| exact X6].
Qed.

Section Fam.
  Variable AL : asan_layout.
  Variable FF : ffam AL.

  Definition CSg (h : ahst) (c : Z) (u f : option bool) : Z -> Prop := ff_CS AL FF (gsel h c u f).
  Definition Kg (h : ahst) (c : Z) (u f : option bool) : Model -> Prop := ff_K AL FF (gsel h c u f).

  Section HC.
    Variables (h : ahst) (c : Z).
    Local Notation L := (h_L h).
    Local Notation mu := (r_mapped_user (h_reg h c)).
    Local Notation mfa := (r_mapped_fa (h_reg h c)).
    Local Notation UA := (region_beg (h_L h) c + r_mapped_user (h_reg h c)).
    Local Notation FAA := (fa_beg (h_L h) c + r_mapped_fa (h_reg h c)).
    Hypothesis W : WFK h.
    Hypothesis GC : 1 <= c <= 31.
    Hypothesis FROOM : mfa + kFreeArrayMapSize <= kFreeArraySize.

    #[using="W GC"] Lemma Wu : forall u, (match u with Some _ => mu + kUserMapSize <= kUserLimit | None => True end) -> WFK (usel h c u).
    Proof. intros [b|] H; [apply WFK_ugrow; [exact W| unfold kNumClasses; lia| exact H]| exact W]. Qed.
    #[using="W GC FROOM"] Lemma Wg : forall u f, (match u with Some _ => mu + kUserMapSize <= kUserLimit | None => True end) -> WFK (gsel h c u f).
    Proof. intros u f H. unfold gsel. destruct f as [b|]; [apply WFK_fagrow; [exact (Wu u H)| unfold kNumClasses; lia| rewrite usel_fa; exact FROOM]| exact (Wu u H)]. Qed.

    #[using="Type"] Lemma gfam_CSOK : forall u f, cs_ok AL (CSg h c u f). Proof. intros u f. apply ff_csok. Qed.
    #[using="Type"] Lemma gfam_KL : forall u f, kinv AL (CSg h c u f) (Kg h c u f). Proof. intros u f. apply ff_kinv. Qed.
    (* [comment removed for export] *)
    #[using="Type"] Lemma kview_ug_fg : kview_eq (h_ugrow (h_fagrow h c) c) (h_fagrow (h_ugrow h c) c).
    Proof.
      unfold kview_eq, h_ugrow, h_fagrow. cbn. split; [reflexivity|]. split; [| repeat split; reflexivity].
      intros c'. unfold fupd. destruct (Z.eqb_spec c' c) as [->|NE]; [rewrite ?Z.eqb_refl; cbn; rewrite ?Z.eqb_refl; cbn; split; reflexivity|].
      cbn. rewrite ?(proj2 (Z.eqb_neq c' c) NE). cbn. rewrite ?(proj2 (Z.eqb_neq c' c) NE). split; reflexivity.
    Qed.
    #[using="Type"] Lemma gfam_mono_u : forall b f y, CSg h c None f y -> CSg h c (Some b) f y.
    Proof. intros b [fb|] y H; unfold CSg, gsel, usel, fsel in *.
      - apply (ff_view_CS AL FF (h_ugrow (h_fagrow h c) c) _ y kview_ug_fg). apply ff_cs_mono_u. exact H.
      - apply ff_cs_mono_u. exact H. Qed.
    #[using="Type"] Lemma gfam_mono_f : forall u b y, CSg h c u None y -> CSg h c u (Some b) y.
    Proof. intros u b y H. unfold CSg, gsel, fsel. apply ff_cs_mono_fa. exact H. Qed.

    #[using="W GC FROOM"] Lemma gfam_T : forall u f, (match u with Some _ => mu + kUserMapSize <= kUserLimit | None => True end) -> crange (CSg h c u f) (l_T L) 4096.
    Proof. intros u f H. unfold CSg. rewrite <- (gsel_L h c u f). apply ff_cs_T. apply Wg. exact H. Qed.
    #[using="W GC FROOM"] Lemma gfam_ctx : forall u f, (match u with Some _ => mu + kUserMapSize <= kUserLimit | None => True end) -> crange (CSg h c u f) (l_ctx L) (l_ctxlen L).
    Proof. intros u f H. unfold CSg. rewrite <- (gsel_L h c u f). apply ff_cs_ctx. apply Wg. exact H. Qed.
    #[using="W GC FROOM"] Lemma gfam_ri : forall u f, (match u with Some _ => mu + kUserMapSize <= kUserLimit | None => True end) -> crange (CSg h c u f) (ri_base L) 4096.
    Proof. intros u f H. unfold CSg. rewrite <- (gsel_L h c u f). apply ff_cs_ri. apply Wg. exact H. Qed.
        (* [comment removed for export] *)
        #[using="W GC FROOM"] Lemma gfam_fa : forall u f, (match u with Some _ => mu + kUserMapSize <= kUserLimit | None => True end) -> crange (CSg h c u f) (fa_beg L c) mfa.
    Proof.
      intros u f H. unfold CSg. rewrite <- (gsel_L h c u f).
      eapply crange_sub; [apply (ff_cs_fa AL FF (gsel h c u f) c (Wg u f H) GC)| dpose W as (_ & WR & _); pose proof (WR c ltac:(unfold kNumClasses; lia)) as X; cbn zeta in X; lia|].
      rewrite gsel_fa, Z.eqb_refl. destruct f; unfold kFreeArrayMapSize; lia.
    Qed.
    (* [comment removed for export] *)
    #[using="W GC FROOM"] Lemma gfam_uz : forall f, mu + kUserMapSize <= kUserLimit -> crange (CSg h c (Some true) f) UA (2^18).
    Proof.
      intros f H. unfold CSg. rewrite <- (gsel_L h c (Some true) f).
      eapply crange_sub; [apply (ff_cs_user AL FF (gsel h c (Some true) f) c (Wg (Some true) f H) GC)| dpose W as (_ & WR & _); pose proof (WR c ltac:(unfold kNumClasses; lia)) as X; cbn zeta in X; lia|].
      rewrite gsel_mu, usel_mu, Z.eqb_refl. unfold kUserMapSize. lia.
    Qed.
    #[using="W GC FROOM"] Lemma gfam_faz : forall u, (match u with Some _ => mu + kUserMapSize <= kUserLimit | None => True end) -> crange (CSg h c u (Some true)) FAA kFreeArrayMapSize.
    Proof.
      intros u H. unfold CSg. rewrite <- (gsel_L h c u (Some true)).
      eapply crange_sub; [apply (ff_cs_fa AL FF (gsel h c u (Some true)) c (Wg u (Some true) H) GC)| dpose W as (_ & WR & _); pose proof (WR c ltac:(unfold kNumClasses; lia)) as X; cbn zeta in X; lia|].
      rewrite gsel_fa, Z.eqb_refl. lia.
    Qed.
    (* [comment removed for export] *)
    #[using="W GC"] Lemma gfam_u_ledger : ltac2:(CDefT.buildp (gd_tbl_AW_FreeFamU ()) "Pmo,$=.P,(4.(7.(8.(9.Vh,Vc,))(>.+2.+12.))+>0000000.)P,(?.Vh,Vc,(10.$11.)(10.$11.)R2.)(3.(12.$11.(13.(14.(15.R3.))(16.&40.(7.(17.(18.Vh,)Vc,)(8.(9.Vh,Vc,))))(16.&40.(>.+2.+12.)))$19.)(1:.(12.$11.(1;.(1<.(15.R3.))(16.&40.(7.(17.(18.Vh,)Vc,)(8.(9.Vh,Vc,))))(16.&40.(>.+2.+12.)))$19.)(12.$11.(13.(1=.(1>.(1?.&40.)(1?.&40.))(14.(15.R3.))(1<.(15.R3.)))(16.&40.(7.(17.(18.Vh,)Vc,)(8.(9.Vh,Vc,))))(16.&40.(>.+2.+12.)))$19.)))")
(* [comment removed for export] *).
    Proof. intros mo R HK. exact (ff_u_ledger AL FF h c mo W GC ltac:(unfold kUserMapSize, kUserLimit; lia) HK). Qed.
    #[using="W GC"] Lemma gfam_u_commit : ltac2:(CDefT.buildp (gd_tbl_AW_FreeFamU ()) "Pmo,$=.P,(4.(7.(8.(9.Vh,Vc,))(>.+2.+12.))+>0000000.)P,(?.Vh,Vc,(10.$11.)(10.$11.)R2.)P,(12.$11.(1;.(1<.(15.R3.))(16.&40.(7.(17.(18.Vh,)Vc,)(8.(9.Vh,Vc,))))(16.&40.(>.+2.+12.)))$19.)(?.Vh,Vc,(20.$11.$19.)(10.$11.)(21.+32.(7.(17.(18.Vh,)Vc,)(8.(9.Vh,Vc,)))(>.+2.+12.)R4.))")
(* [comment removed for export] *).
    Proof. intros mo R HK MC. exact (ff_u_commit AL FF h c mo W GC ltac:(unfold kUserMapSize, kUserLimit; lia) HK MC). Qed.
    #[using="W GC"] Lemma gfam_u_fresh : ltac2:(CDefT.buildp (gd_tbl_AW_FreeFamU ()) "Pmo,$=.P,(4.(7.(8.(9.Vh,Vc,))(>.+2.+12.))+>0000000.)P,(?.Vh,Vc,(10.$11.)(10.$11.)R2.)P,(12.$11.(13.(1=.(1>.(1?.&40.)(1?.&40.))(14.(15.R3.))(1<.(15.R3.)))(16.&40.(7.(17.(18.Vh,)Vc,)(8.(9.Vh,Vc,))))(16.&40.(>.+2.+12.)))$19.)(?.Vh,Vc,(20.$11.$19.)(10.$11.)(22.+32.(7.(17.(18.Vh,)Vc,)(8.(9.Vh,Vc,)))(>.+2.+12.)R4.))")
(* [comment removed for export] *).
    Proof. intros mo R HK RF. exact (ff_u_fresh AL FF h c mo W GC ltac:(unfold kUserMapSize, kUserLimit; lia) HK RF). Qed.
    #[using="W GC"] Lemma gfam_u_room : forall mo, mu + 2^18 <= 0xE0000000 -> Kg h c None None mo -> fixrw_grantable 0x32 UA (2^18) mo.
    Proof. intros mo R HK. exact (ff_u_room AL FF h c mo W GC ltac:(unfold kUserMapSize, kUserLimit; lia) HK). Qed.
    (* [comment removed for export] *)
    #[using="W GC"] Lemma gfam_u_scar : mu + 2^18 <= 0xE0000000 -> scar_site AL (CSg h c None None) (Kg h c None None) UA (2^18).
    Proof. intros R. exact (ff_u_scar AL FF h c W GC ltac:(unfold kUserMapSize, kUserLimit; lia)). Qed.
    (* [comment removed for export] *)
    #[using="W GC FROOM"] Lemma gfam_f_ledger : forall u mo, (u = None \/ u = Some true) -> (match u with Some _ => mu + kUserMapSize <= kUserLimit | None => True end) -> Kg h c u None mo ->
      region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 FAA) (Z_to_bv 64 (2^18)) = true
      /\ (map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 FAA) (Z_to_bv 64 (2^18)) = true
          \/ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 FAA) (Z_to_bv 64 (2^18)) = true).
    Proof.
      intros u mo _ H HK. pose proof (ff_fa_ledger AL FF (usel h c u) c mo (Wu u H) GC ltac:(rewrite usel_fa; exact FROOM) HK) as X.
      unfold faa in X. rewrite usel_L, usel_fa in X. exact X.
    Qed.
    #[using="W GC FROOM"] Lemma gfam_f_commit : forall u mo, (u = None \/ u = Some true) -> (match u with Some _ => mu + kUserMapSize <= kUserLimit | None => True end) -> Kg h c u None mo ->
      map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 FAA) (Z_to_bv 64 (2^18)) = true -> Kg h c u (Some true) (fixrw_commit 0x32 FAA (2^18) mo).
    Proof.
      intros u mo _ H HK MC. pose proof (ff_fa_commit AL FF (usel h c u) c mo (Wu u H) GC ltac:(rewrite usel_fa; exact FROOM) HK) as X.
      unfold faa in X. rewrite usel_L, usel_fa in X. exact (X MC).
    Qed.
    #[using="W GC FROOM"] Lemma gfam_f_fresh : forall u mo, (u = None \/ u = Some true) -> (match u with Some _ => mu + kUserMapSize <= kUserLimit | None => True end) -> Kg h c u None mo ->
      region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 FAA) (Z_to_bv 64 (2^18)) = true -> Kg h c u (Some true) (fixrw_fresh 0x32 FAA (2^18) mo).
    Proof.
      intros u mo _ H HK RF. pose proof (ff_fa_fresh AL FF (usel h c u) c mo (Wu u H) GC ltac:(rewrite usel_fa; exact FROOM) HK) as X.
      unfold faa in X. rewrite usel_L, usel_fa in X. exact (X RF).
    Qed.
    #[using="W GC FROOM"] Lemma gfam_f_room : forall u mo, (u = None \/ u = Some true) -> (match u with Some _ => mu + kUserMapSize <= kUserLimit | None => True end) -> Kg h c u None mo ->
      fixrw_grantable 0x32 FAA (2^18) mo.
    Proof.
      intros u mo _ H HK. pose proof (ff_fa_room AL FF (usel h c u) c mo (Wu u H) GC ltac:(rewrite usel_fa; exact FROOM) HK) as X.
      unfold faa in X. rewrite usel_L, usel_fa in X. exact X.
    Qed.
    (* [comment removed for export] *)
    #[using="W GC FROOM"] Lemma gfam_f_scar : forall u, (u = None \/ u = Some true) -> (match u with Some _ => mu + kUserMapSize <= kUserLimit | None => True end) ->
      scar_site AL (CSg h c u None) (Kg h c u None) FAA (2^18).
    Proof.
      intros u _ H. pose proof (ff_fa_scar AL FF (usel h c u) c (Wu u H) GC ltac:(rewrite usel_fa; exact FROOM)) as X.
      unfold faa in X. rewrite usel_L, usel_fa in X. exact X.
    Qed.
  End HC.
End Fam.
End ARUN_1.
