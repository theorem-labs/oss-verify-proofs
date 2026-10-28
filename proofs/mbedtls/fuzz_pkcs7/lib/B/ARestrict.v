(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Exec Shape Mem Cells Arr Frame Step.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtA AShadow Restrict RestrictLib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_ARestrict () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Corelib.Init.Datatypes.fst"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.snd"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "Dimg"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.aok_addr"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.LibA.Restrict.restrict"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.LibA.Restrict.rms"; "Corelib.Init.Datatypes.false"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_mem"].


Definition AIMG_LO : Z := 0x10000.
Definition AIMG_HI : Z := 0x65f000.

Lemma asegs_top : forallb (fun seg => Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? 2^64) asegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma asegs_segcov : forall z, segcov asegs z = true -> AIMG_LO <= z < AIMG_HI.
Proof.
  intros z H. unfold segcov, asegs in H.
  cbn -[Z.leb Z.ltb Z.add Z.of_N] in H.
  repeat match type of H with context [Z.of_N ?x] => let v := eval vm_compute in (Z.of_N x) in change (Z.of_N x) with v in H end.
  unfold AIMG_LO, AIMG_HI.
  repeat (apply orb_prop in H; destruct H as [H|H]);
    try (apply andb_prop in H; destruct H as [H1 H2]; apply Z.leb_le in H1; apply Z.ltb_lt in H2; lia).
  discriminate.
Qed.

(* [comment removed for export] *)
Definition Dimg (ivs : list (Z * Z)) : word -> bool := Dof ((AIMG_LO, AIMG_HI) :: ivs).

Lemma Dimg_Dseg : forall ivs a, segcov asegs (bv_unsigned a) = true -> Dimg ivs a = true.
Proof.
  intros ivs a H. apply asegs_segcov in H. apply (proj2 (Dof_true _ a)). exists (AIMG_LO, AIMG_HI). split; [left; reflexivity|]. cbn. lia.
Qed.

Lemma Dimg_img : forall ivs, Dcov (Dimg ivs) AIMG_LO AIMG_HI.
Proof. intros ivs. apply Dof_cov; [left; reflexivity| unfold AIMG_LO; lia | unfold AIMG_HI; lia]. Qed.

Lemma Dimg_cov : forall ivs lo hi, In (lo, hi) ivs -> 0 <= lo -> hi <= 2^64 -> Dcov (Dimg ivs) lo hi.
Proof. intros. apply Dof_cov; auto. right; assumption. Qed.

Section WithLayout.
Variable AL : asan_layout.
Variable CS : Z -> Prop.
Hypothesis IMG : asan_img_ok AL.

#[using="IMG"] Lemma Dimg_DOK : ltac2:(CDefT.buildp (gd_tbl_ARestrict ()) "Pivs,(0.(1.$2.$2.))P,(3.(1.$2.$2.)Liv,(1.$2.$2.)(4.VCS,(5.$2.$2.R1.)(6.(7.$2.$2.R1.)(5.$2.$2.R1.)))R1.)Pa,(8.&40.)P,(9.$:.(;.R3.R1.)$<.)(=.VAL,VCS,(>.&40.R2.))")
(* [comment removed for export] *).
Proof.
  intros ivs H. apply Dof_DOK. constructor.
  - cbn. intros z Hz. right; right. ddestruct IMG as (_ & -> & -> & _). unfold AIMG_LO, AIMG_HI in Hz. lia.
  - apply Forall_impl with (P := fun iv => crange CS (fst iv) (snd iv - fst iv)); [|exact H].
    intros [lo hi] Hc z Hz. cbn in *. left. apply Hc. lia.
Qed.

#[using="Type"] Lemma Dimg_D0 : forall ivs, Forall (fun iv => 0 < fst iv) ivs -> Dimg ivs (Z_to_bv 64 0) = false.
Proof. intros ivs H. apply Dof_D0. constructor; [cbn; unfold AIMG_LO; lia | exact H]. Qed.

(* [comment removed for export] *)
#[using="IMG"] Lemma Dimg_DOK_aok : ltac2:(CDefT.buildp (gd_tbl_ARestrict ()) "Pivs,(0.(1.$2.$2.))P,(3.(1.$2.$2.)Liv,(1.$2.$2.)Pz,$2.P,(?.(10.(5.$2.$2.R2.)R1.)(11.R1.(7.$2.$2.R2.)))(=.VAL,VCS,R2.)R1.)Pa,(8.&40.)P,(9.$:.(;.R3.R1.)$<.)(=.VAL,VCS,(>.&40.R2.))")
(* [comment removed for export] *).
Proof.
  intros ivs H. apply Dof_DOK. constructor; [|exact H].
  cbn. intros z Hz. right; right. ddestruct IMG as (_ & -> & -> & _). unfold AIMG_LO, AIMG_HI in Hz. lia.
Qed.

(* [comment removed for export] *)
#[using="IMG"] Theorem evtA_of_evt_img : ltac2:(CDefT.buildp (gd_tbl_ARestrict ()) "Pivs,(0.(1.$2.$2.))PQ,P,$12.SpPR,(13.&5.(8.&40.))PF,(13.&5.(8.&40.))Ppc,(8.&40.)Pfc,(8.&20.)Prv,(14.(8.&40.))Pm,P,(8.&40.)(14.(8.&8.))Pro,P,(8.&40.)(14.(8.&8.))P,(3.(1.$2.$2.)Liv,(1.$2.$2.)(4.VCS,(5.$2.$2.R1.)(6.(7.$2.$2.R1.)(5.$2.$2.R1.)))R9.)P,(3.(1.$2.$2.)Liv,(1.$2.$2.)(11.=(5.$2.$2.R1.))R:.)P,(15.$16.R:.(17.R9.R8.R7.R6.R5.(18.(;.R;.)R4.)R3.))(19.$16.VAL,VCS,Lms1,$12.(?.A1.R<.(1:.(;.R=.)R1.)Pa,(8.&40.)P,(9.$:.(;.R>.R1.)$1;.)(9.(14.(8.&8.))(1<.R3.R2.)A1.R8.R2.))(17.R:.R9.R8.R7.R6.R5.R4.))")
(* [comment removed for export] *).
Proof.
  intros ivs Q R F pc fc rv m ro HCS H0 HE.
  exact (evt_restrict_evtA asegs (Dimg ivs) (Dimg_Dseg ivs) asegs_top AL CS (Dimg_DOK ivs HCS) (Dimg_D0 ivs H0)
           Q (MS R F pc fc rv m ro) HE).
Qed.
#[using="IMG"] Theorem evtA_of_evt_imgA : ltac2:(CDefT.buildp (gd_tbl_ARestrict ()) "Pivs,(0.(1.$2.$2.))PQ,P,$12.SpPR,(13.&5.(8.&40.))PF,(13.&5.(8.&40.))Ppc,(8.&40.)Pfc,(8.&20.)Prv,(14.(8.&40.))Pm,P,(8.&40.)(14.(8.&8.))Pro,P,(8.&40.)(14.(8.&8.))P,(3.(1.$2.$2.)Liv,(1.$2.$2.)Pz,$2.P,(?.(10.(5.$2.$2.R2.)R1.)(11.R1.(7.$2.$2.R2.)))(=.VAL,VCS,R2.)R9.)P,(3.(1.$2.$2.)Liv,(1.$2.$2.)(11.=(5.$2.$2.R1.))R:.)P,(15.$16.R:.(17.R9.R8.R7.R6.R5.(18.(;.R;.)R4.)R3.))(19.$16.VAL,VCS,Lms1,$12.(?.A1.R<.(1:.(;.R=.)R1.)Pa,(8.&40.)P,(9.$:.(;.R>.R1.)$1;.)(9.(14.(8.&8.))(1<.R3.R2.)A1.R8.R2.))(17.R:.R9.R8.R7.R6.R5.R4.))")
(* [comment removed for export] *).
Proof.
  intros ivs Q R F pc fc rv m ro HA H0 HE.
  exact (evt_restrict_evtA asegs (Dimg ivs) (Dimg_Dseg ivs) asegs_top AL CS (Dimg_DOK_aok ivs HA) (Dimg_D0 ivs H0)
           Q (MS R F pc fc rv m ro) HE).
Qed.
End WithLayout.
