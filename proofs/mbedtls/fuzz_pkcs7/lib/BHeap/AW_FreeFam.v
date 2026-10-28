(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX AW_FreeP AW_FreeR. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv AKinvM AW_FreeK.
Import ListNotations.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AW_FreeFam () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeK.WFK"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kNumClasses"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_mapped_fa"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_reg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kFreeArrayMapSize"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kFreeArraySize"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeP.h_fagrow"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "ARUN_1.Fam.CSp"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.region_beg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_mapped_user"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.true"; "ARUN_1.Fam.Kp"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.fa_beg"; "Stdlib.ZArith.BinInt.Z.pow"; "LinuxProcessSemantics.LinuxProcessSem.State.map_contains"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.prod"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_commit"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_fresh"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.
Section Fam.
  Variable AL : asan_layout.
  Variable FF : ffam AL.

  Definition CSp (h : ahst) (c : Z) (u f : option bool) : Z -> Prop := ff_CS AL FF (fsel h c f).
  Definition Kp (h : ahst) (c : Z) (u f : option bool) : Model -> Prop := ff_K AL FF (fsel h c f).

  (* [comment removed for export] *)
  #[using="Type"] Lemma WFK_fagrow : ltac2:(CDefT.buildp (gd_tbl_AW_FreeFam ()) "Ph,$0.Pc,$1.P,(2.VhAR,R2.)P,(3.(4.+1.R2.)(5.R2.$6.))P,(4.(7.(8.(9.R4.R3.))$:.)$;.)(2.VhAR,(<.R5.R4.))")
(* [comment removed for export] *).
  Proof.
    (intros h c dd_H; ddestruct dd_H as (WL & WR & WS & WD & WB & WBIG & WG & HV); intros Hc ROOM).
    split; [exact WL|]. split; [| exact (conj WS (conj WD (conj WB (conj WBIG (conj WG HV)))))].
    intros c' Hc'. cbn zeta. unfold h_fagrow. cbn [h_reg set_reg]. unfold fupd.
    pose proof (WR c' Hc') as X. cbn zeta in X.
    destruct (Z.eqb_spec c' c) as [->|NE]; [| exact X].
    ddestruct X as (X0 & X1 & X2 & X3 & X4 & X5 & X6). cbn [r_mapped_user r_alloc_user r_mapped_fa r_fa]. unfold r_nfreed in *. cbn [r_fa].
    split; [intros E; exfalso; lia|].
    split; [exact X1|]. split; [exact X2|]. split; [exact X3|].
    split. { unfold kFreeArrayMapSize in *. rewrite Z.add_mod, X4 by lia. reflexivity. }
    split; [unfold kFreeArrayMapSize in *; lia| lia].
  Qed.

  #[using="Type"] Lemma fsel_L : forall h c f, h_L (fsel h c f) = h_L h.
  Proof. intros h c [b|]; reflexivity. Qed.

  Section HC.
    Variables (h : ahst) (c : Z).
    Local Notation L := (h_L h).
    Local Notation mfa := (r_mapped_fa (h_reg h c)).
    Local Notation FAA := (fa_beg (h_L h) c + r_mapped_fa (h_reg h c)).
    Hypothesis W : WFK h.
    Hypothesis GC : 1 <= c <= 31.
    Hypothesis ROOM : mfa + kFreeArrayMapSize <= kFreeArraySize.

    #[using="W GC ROOM"] Lemma W' : WFK (h_fagrow h c). Proof. apply WFK_fagrow; [exact W| unfold kNumClasses; lia| exact ROOM]. Qed.
    #[using="W GC ROOM"] Lemma Wf : forall f, WFK (fsel h c f). Proof. intros [b|]; [exact W'| exact W]. Qed.

    #[using="Type"] Lemma fam_CSOK : forall u f, cs_ok AL (CSp h c u f). Proof. intros u f. apply ff_csok. Qed.
    #[using="Type"] Lemma fam_KL : forall u f, kinv AL (CSp h c u f) (Kp h c u f). Proof. intros u f. apply ff_kinv. Qed.
    #[using="Type"] Lemma fam_mono : forall u b y, CSp h c u None y -> CSp h c u (Some b) y. Proof. intros u b y H. unfold CSp, fsel. apply ff_cs_mono_fa. exact H. Qed.
    #[using="W GC ROOM"] Lemma fam_T : forall u f, crange (CSp h c u f) (l_T L) 4096.
    Proof. intros u f. unfold CSp. rewrite <- (fsel_L h c f). apply ff_cs_T. apply Wf. Qed.
    #[using="W GC ROOM"] Lemma fam_ctx : forall u f, crange (CSp h c u f) (l_ctx L) (l_ctxlen L).
    Proof. intros u f. unfold CSp. rewrite <- (fsel_L h c f). apply ff_cs_ctx. apply Wf. Qed.
    #[using="W GC ROOM"] Lemma fam_ri : forall u f, crange (CSp h c u f) (ri_base L) 4096.
    Proof. intros u f. unfold CSp. rewrite <- (fsel_L h c f). apply ff_cs_ri. apply Wf. Qed.
        #[using="W GC ROOM"] Lemma fam_stack : forall u f lo n, l_stk_lo L <= lo -> lo + n <= l_stk_hi L -> crange (CSp h c u f) lo n.
    Proof. intros u f lo n H0 H1. unfold CSp. apply ff_cs_stack; [apply Wf| rewrite fsel_L; exact H0| rewrite fsel_L; exact H1]. Qed.
    #[using="W GC ROOM"] Lemma fam_user : ltac2:(CDefT.buildp (gd_tbl_AW_FreeFam ()) "Pu,(=.$>.)Pf,(=.$>.)Pc',$1.P,(3.(4.+1.R1.)(4.R1.+1?.))(?.(10.Vh,Vc,R4.R3.)(11.(12.Vh,)R2.)(13.(9.Vh,R2.)))")
(* [comment removed for export] *).
    Proof.
      intros u f c' Hc'. unfold CSp. rewrite <- (fsel_L h c f).
      replace (r_mapped_user (h_reg h c')) with (r_mapped_user (h_reg (fsel h c f) c')); [apply ff_cs_user; [apply Wf| exact Hc']|].
      destruct f as [b|]; [| reflexivity]. cbn. unfold fupd. destruct (Z.eqb_spec c' c) as [->|]; reflexivity.
    Qed.
    (* [comment removed for export] *)
    #[using="W GC ROOM"] Lemma fam_fa : forall u f, crange (CSp h c u f) (fa_beg L c) mfa.
    Proof.
      intros u f. unfold CSp. destruct f as [b|]; cbn [fsel].
      - eapply crange_sub; [apply (ff_cs_fa AL FF (h_fagrow h c) c W' GC)| cbn; lia | cbn; rewrite fupd_same; cbn; unfold kFreeArrayMapSize; lia].
      - apply (ff_cs_fa AL FF h c W GC).
    Qed.
    #[using="W GC ROOM"] Lemma fam_faz : forall u, crange (CSp h c u (Some true)) FAA kFreeArrayMapSize.
    Proof.
      intros u. unfold CSp. cbn [fsel].
      eapply crange_sub; [apply (ff_cs_fa AL FF (h_fagrow h c) c W' GC)| cbn; dpose W as (_ & WR & _); pose proof (WR c ltac:(unfold kNumClasses; lia)) as X; cbn zeta in X; lia|].
      cbn. rewrite fupd_same. cbn. lia.
    Qed.
    #[using="W GC ROOM"] Lemma fam_ledger : ltac2:(CDefT.buildp (gd_tbl_AW_FreeFam ()) "Pu,(=.$>.)Pmo,$14.P,(15.(16.(=.$>.)R2.(17.$>.))(16.(=.$>.)R2.(18.$>.$19.)))P,(1:.Vh,Vc,R3.(17.$>.)R2.)(3.(16.$>.(1;.(1<.(1=.R3.))(1>.&40.(7.(1?.(12.Vh,)Vc,)(8.(9.Vh,Vc,))))(1>.&40.(20.+2.+12.)))$19.)(15.(16.$>.(21.(22.(1=.R3.))(1>.&40.(7.(1?.(12.Vh,)Vc,)(8.(9.Vh,Vc,))))(1>.&40.(20.+2.+12.)))$19.)(16.$>.(1;.(23.(24.(25.&40.)(25.&40.))(1<.(1=.R3.))(22.(1=.R3.)))(1>.&40.(7.(1?.(12.Vh,)Vc,)(8.(9.Vh,Vc,))))(1>.&40.(20.+2.+12.)))$19.)))")
(* [comment removed for export] *).
    Proof. intros u mo _ HK. exact (ff_fa_ledger AL FF h c mo W GC ROOM HK). Qed.
    #[using="W GC ROOM"] Lemma fam_commit : ltac2:(CDefT.buildp (gd_tbl_AW_FreeFam ()) "Pu,(=.$>.)Pmo,$14.P,(15.(16.(=.$>.)R2.(17.$>.))(16.(=.$>.)R2.(18.$>.$19.)))P,(1:.Vh,Vc,R3.(17.$>.)R2.)P,(16.$>.(21.(22.(1=.R3.))(1>.&40.(7.(1?.(12.Vh,)Vc,)(8.(9.Vh,Vc,))))(1>.&40.(20.+2.+12.)))$19.)(1:.Vh,Vc,R5.(18.$>.$19.)(26.+32.(7.(1?.(12.Vh,)Vc,)(8.(9.Vh,Vc,)))(20.+2.+12.)R4.))")
(* [comment removed for export] *).
    Proof. intros u mo _ HK MC. exact (ff_fa_commit AL FF h c mo W GC ROOM HK MC). Qed.
    #[using="W GC ROOM"] Lemma fam_fresh : ltac2:(CDefT.buildp (gd_tbl_AW_FreeFam ()) "Pu,(=.$>.)Pmo,$14.P,(15.(16.(=.$>.)R2.(17.$>.))(16.(=.$>.)R2.(18.$>.$19.)))P,(1:.Vh,Vc,R3.(17.$>.)R2.)P,(16.$>.(1;.(23.(24.(25.&40.)(25.&40.))(1<.(1=.R3.))(22.(1=.R3.)))(1>.&40.(7.(1?.(12.Vh,)Vc,)(8.(9.Vh,Vc,))))(1>.&40.(20.+2.+12.)))$19.)(1:.Vh,Vc,R5.(18.$>.$19.)(27.+32.(7.(1?.(12.Vh,)Vc,)(8.(9.Vh,Vc,)))(20.+2.+12.)R4.))")
(* [comment removed for export] *).
    Proof. intros u mo _ HK RF. exact (ff_fa_fresh AL FF h c mo W GC ROOM HK RF). Qed.
    #[using="W GC ROOM"] Lemma fam_room : forall u mo, (u = None \/ u = Some true) -> Kp h c u None mo -> fixrw_grantable 0x32 FAA (2^18) mo.
    Proof. intros u mo _ HK. exact (ff_fa_room AL FF h c mo W GC ROOM HK). Qed.
    (* [comment removed for export] *)
    #[using="W GC ROOM"] Lemma fam_scar : forall u, (u = None \/ u = Some true) -> scar_site AL (CSp h c u None) (Kp h c u None) FAA (2^18).
    Proof. intros u _. exact (ff_fa_scar AL FF h c W GC ROOM). Qed.

    (* [comment removed for export] *)
    #[using="hAR W GC ROOM"] Lemma fam_GMFA : 0 <= mfa /\ mfa mod 2^18 = 0 /\ mfa + 2^18 <= 2^29.
    Proof.
      dpose W as (_ & WR & _). pose proof (WR c ltac:(unfold kNumClasses; lia)) as X. cbn zeta in X. ddestruct X as (_ & _ & _ & _ & X4 & X5 & _).
      unfold kFreeArrayMapSize, kFreeArraySize in *. split; [lia|]. split; [exact X4| lia].
    Qed.
  End HC.
End Fam.

End ARUN_1.
