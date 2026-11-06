(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Logic.FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common Require Import SimInv ExitSim.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import CatExec CatSim SeqExec StoreOk ShapeX AgentLib.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy SRz AEvtS AEvtA Restrict RestrictLib NodesA SymDriveA.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_RestrictRun () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.PropExec.rdn"; "Corelib.Init.Datatypes.Some"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.LibA.SymDriveA.DcovZ"; "OSSVerify.KrLib.LibA.Restrict.restrict"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Datatypes.length"; "OSSVerify.KrLib.BB.CatExec.wbytes"; "Corelib.Init.Datatypes.false"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "stdpp.bitvector.definitions.Z_to_bv"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Datatypes.prod"; "OSSVerify.KrLib.LibA.ALazy.acc_ok"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.LinuxProcessSem.State.materialize_model_accesses"; "OSSVerify.KrLib.LibA.ALazy.mo_mat"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "OSSVerify.KrLib.Lib.Shape.TSet"; "OSSVerify.KrLib.Lib.Shape.msteps"; "OSSVerify.KrLib.Lib.PropExec.mkst"; "OSSVerify.KrLib.Lib.PropExec.fx0"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.LibA.SRz.srealizesJ"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"].

#[local] Existing Instance Lib.PropExec.fx0.

Section RR.
Variable segs : list Segment.
Variable D : word -> bool.

#[warnings="-deprecated"] Notation rst := (restrict D).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma rdn_restrictD : ltac2:(CDefT.buildp (gd_tbl_RestrictRun ()) "PM,P,(0.&40.)(1.(0.&8.))Pa,(0.&40.)Pn,$2.Pbs,(3.(0.&8.))P,(4.(1.(3.(0.&8.)))(5.Vsegs,R4.R3.R2.)(6.(3.(0.&8.))R1.))P,(7.(8.(9.&40.R4.)(:.R3.))(;.+2.+40.))P,(<.VD,(9.&40.R5.)(8.(9.&40.R5.)(:.R4.)))(4.(1.(3.(0.&8.)))(5.Vsegs,(=.VD,R7.)R6.R5.)(6.(3.(0.&8.))R4.))")
(* [comment removed for export] *).
Proof. intros M a n bs H Hnw HD. rewrite (rdn_restrict_in segs D M a n Hnw HD). exact H. Qed.

#[using="Type"] Lemma store_ok_restrictD : ltac2:(CDefT.buildp (gd_tbl_RestrictRun ()) "PM,P,(0.&40.)(1.(0.&8.))Pa,(0.&40.)Pn,$2.P,(4.$>.(?.Vsegs,R3.R2.R1.)$10.)P,(7.(8.(9.&40.R3.)(:.R2.))(;.+2.+40.))P,(<.VD,(9.&40.R4.)(8.(9.&40.R4.)(:.R3.)))(4.$>.(?.Vsegs,(=.VD,R6.)R5.R4.)$10.)")
(* [comment removed for export] *).
Proof. intros M a n H Hnw HD. rewrite (store_ok_restrict_in segs D n M a Hnw HD). exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma wbytes_restrict : ltac2:(CDefT.buildp (gd_tbl_RestrictRun ()) "Pbs,(3.(0.&8.))PM,P,(0.&40.)(1.(0.&8.))Pa,(0.&40.)P,(7.(8.(9.&40.R1.)(:.(11.(0.&8.)R3.)))(;.+2.+40.))P,(<.VD,(9.&40.R2.)(8.(9.&40.R2.)(:.(11.(0.&8.)R4.))))(4.P,(0.&40.)(1.(0.&8.))(12.(=.VD,R4.)R3.R5.)(=.VD,(12.R4.R3.R5.)))")
(* [comment removed for export] *).
Proof.
  intros bs M a Hnw HD. rewrite <- !write_to_mem_wbytes. apply write_to_mem_restrict.
  intros i Hi. pose proof (u64_range a) as Ra.
  replace (wplus a i) with (Z_to_bv 64 (bv_unsigned a + Z.of_nat i)); [apply HD; lia|].
  unfold wplus. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

#[using="Type"] Lemma wbytes_agree_outD : ltac2:(CDefT.buildp (gd_tbl_RestrictRun ()) "Pbs,(3.(0.&8.))PM,P,(0.&40.)(1.(0.&8.))Pa,(0.&40.)Px,(0.&40.)P,(7.(8.(9.&40.R2.)(:.(11.(0.&8.)R4.)))(;.+2.+40.))P,(<.VD,(9.&40.R3.)(8.(9.&40.R3.)(:.(11.(0.&8.)R5.))))P,(4.$>.A1.VD,R3.$13.)(4.(1.(0.&8.))(12.R6.R5.R7.R4.)A1.R6.R4.)")
(* [comment removed for export] *).
Proof.
  intros bs M a x Hnw HD Hx. rewrite <- write_to_mem_wbytes. apply write_to_mem_outside.
  intros i Hi E. pose proof (u64_range a) as Ra.
  assert (HDx : D x = true); [|congruence].
  subst x. replace (wplus a i) with (Z_to_bv 64 (bv_unsigned a + Z.of_nat i)); [apply HD; lia|].
  unfold wplus. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma wbytes_restrict_Z : ltac2:(CDefT.buildp (gd_tbl_RestrictRun ()) "Pk,$2.Pv,(0.&40.)PM,P,(0.&40.)(1.(0.&8.))Pz,$14.P,(15.(7.=R1.)(16.R1.(;.+2.+40.)))P,(7.(8.R2.(:.R5.))(;.+2.+40.))P,(<.VD,R3.(8.R3.(:.R6.)))(4.P,(0.&40.)(1.(0.&8.))(12.(=.VD,R5.)(17.&40.R4.)(18.R7.R6.))(=.VD,(12.R5.(17.&40.R4.)(18.R7.R6.))))")
(* [comment removed for export] *).
Proof.
  intros k v M z Hz Hnw HD. pose proof (length_N_to_le_bytes k v) as L.
  apply wbytes_restrict; rewrite L; rewrite u64_lit by lia; [lia | exact HD].
Qed.

#[using="Type"] Lemma wbytes_agree_outD_Z : ltac2:(CDefT.buildp (gd_tbl_RestrictRun ()) "Pk,$2.Pv,(0.&40.)PM,P,(0.&40.)(1.(0.&8.))Pz,$14.Px,(0.&40.)P,(15.(7.=R2.)(16.R2.(;.+2.+40.)))P,(7.(8.R3.(:.R6.))(;.+2.+40.))P,(<.VD,R4.(8.R4.(:.R7.)))P,(4.$>.A1.VD,R4.$13.)(4.(1.(0.&8.))(12.R7.(17.&40.R6.)(18.R9.R8.)R5.)A1.R7.R5.)")
(* [comment removed for export] *).
Proof.
  intros k v M z x Hz Hnw HD Hx. pose proof (length_N_to_le_bytes k v) as L.
  apply wbytes_agree_outD; [rewrite L; rewrite u64_lit by lia; lia | rewrite L; rewrite u64_lit by lia; exact HD | exact Hx].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithK.
Variable AL : asan_layout.
Variable CS : Z -> Prop.
Variable K : Model -> Prop.
Hypothesis K_halted : forall mo, K mo -> m_halted mo = None.
Hypothesis K_mat : ltac2:(CDefT.buildp (gd_tbl_RestrictRun ()) "Pmo,$19.Pacc,(3.(1:.(0.&40.)$2.))P,A1.VK,R2.P,(1;.VAL,VCS,R2.)(1<.$19.Lmo',$19.(15.(4.(1.$19.)(1=.R5.R4.)(6.$19.R1.))(15.A1.VK,R1.(1>.R5.R1.))))")
(* [comment removed for export] *).
Hypothesis Dseg : forall a : word, segcov segs (bv_unsigned a) = true -> D a = true.
Hypothesis SEGTOP : forallb (fun seg => (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? 2^64)%Z) segs = true.
Hypothesis DOK : forall a, D a = true -> aok_addr AL CS (bv_unsigned a).
Hypothesis D0 : D (Z_to_bv 64 0) = false.

#[using="AL CS K_halted K_mat Dseg SEGTOP DOK D0"] Theorem rz_smsteps_RK : ltac2:(CDefT.buildp (gd_tbl_RestrictRun ()) "PR,(1?.&5.(0.&40.))Ppc,(0.&40.)PM,P,(0.&40.)(1.(0.&8.))PR1,(1?.&5.(0.&40.))Ppc1,(0.&40.)PM1,P,(0.&40.)(1.(0.&8.))Pmo,$19.PT,$20.P,A1.VK,R2.P,(21.Vsegs,(22.$23.R9.R8.(=.VD,R7.)(24.Vsegs,))(22.$23.R6.R5.(=.VD,R4.)(24.Vsegs,)))P,Pa,(0.&40.)P,(4.$>.A1.VD,R1.$13.)(4.(1.(0.&8.))A1.R7.R2.A1.R:.R2.)P,Pmo',$19.P,A1.VK,R1.P,(1>.R7.R2.)(25.Vsegs,(26.(22.$23.R;.R:.R9.(24.Vsegs,))R3.)R7.)(25.Vsegs,(26.(22.$23.R<.R;.R:.(24.Vsegs,))R6.)R5.)")
(* [comment removed for export] *).
Proof.
  intros R pc M R1 pc1 M1 mo T HK Hms Hout1 Hc.
  assert (Hrms : mkst R pc (rst M) (seg_rom segs) = rms D (mkst R pc M (seg_rom segs))) by reflexivity.
  rewrite Hrms in Hms.
  destruct (smsteps_restrict segs D Dseg SEGTOP AL CS DOK D0 _ _ Hms _ eq_refl) as (ms1' & HA & Hr & Hout).
  eapply (rz_mstepsA_K segs AL CS K K_halted K_mat); [exact HK | exact HA |].
  intros mo' HK' MM.
  destruct (rms_eq_mkst D _ _ _ _ _ Hr) as (M1' & -> & EM). cbn [ms_mem mkst] in Hout.
  replace M1' with M1; [apply Hc; assumption|].
  apply functional_extensionality. intros a. destruct (D a) eqn:Da.
  - rewrite <- (restrict_in D M1 a Da), <- (restrict_in D M1' a Da), EM. reflexivity.
  - rewrite (Hout1 a Da), (Hout a Da). reflexivity.
Qed.
End WithK.
End RR.

(* [comment removed for export] *)
Ltac push_restrict tac :=
  repeat (rewrite wbytes_restrict_Z; [ | tac | tac | tac ]).
