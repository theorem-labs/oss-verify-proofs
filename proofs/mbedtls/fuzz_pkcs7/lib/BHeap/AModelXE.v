(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AModelXE () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_mapped_user"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_reg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_alloc_user"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_exh"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_acct"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.epi"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.csum"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_emb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_esz"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.lowhigh"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kEmbBytes"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_b6"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_pa"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.EM"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.carved"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kBatchClass"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.CMAX24"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.cnt24"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.blocks"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.C24MAX"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.alayout"; "ARUN_1.wf_x67"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.acct"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.

(* [comment removed for export] *)
#[using="Type"] Lemma epi_frame_ua : ltac2:(CDefT.buildp (gd_tbl_AModelXE ()) "Ph,$0.Ph',$0.Pc,$1.P,(2.$1.(3.(4.R2.R1.))(3.(4.R3.R1.)))P,(2.$1.(5.(4.R3.R2.))(5.(4.R4.R2.)))P,(2.$6.(7.(8.R4.)R3.)(7.(8.R5.)R3.))(2.$1.(9.R5.R4.)(9.R6.R4.))")
(* [comment removed for export] *).
Proof. intros h h' c HM HA HX. unfold epi, frozen. rewrite HM, HA, HX. reflexivity. Qed.

#[using="Type"] Lemma csum_epi_frame_ua : ltac2:(CDefT.buildp (gd_tbl_AModelXE ()) "Ph,$0.Ph',$0.P,Pc,$1.P,(:.(;.+1.R1.)(;.R1.+1?.))(:.(2.$1.(3.(4.R3.R2.))(3.(4.R4.R2.)))(2.$1.(5.(4.R3.R2.))(5.(4.R4.R2.))))P,Pc,$1.P,(:.(;.+1.R1.)(;.R1.+1?.))(2.$6.(7.(8.R4.)R2.)(7.(8.R5.)R2.))(2.$1.(<.(9.R3.))(<.(9.R4.)))")
(* [comment removed for export] *).
Proof.
  intros h h' HR HX. apply Z.le_antisymm; apply csum_le; intros c Hc; destruct (HR c Hc) as [E1 E2];
    rewrite (epi_frame_ua h h' c E1 E2 (HX c Hc)); lia.
Qed.

(* [comment removed for export] *)
Definition wf_x67 (h : ahst) : Prop := ltac2:(CDefT.buildp (gd_tbl_AModelXE ()) "(:.(=.(:.(2.$1.(>.(8.O1.))=)(2.$1.(?.(8.O1.))=))(:.(10.(>.(8.O1.))$11.)(:.(12.=(>.(8.O1.)))(:.(;.(13.(>.(8.O1.))$11.)(14.VhAR,))(:.(2.$1.(15.(>.(8.O1.))+1000.)=)(:.(=.(;.(13.(>.(8.O1.))$11.)(16.(17.O1.)))(;.(13.(16.(17.O1.))+2000011000.)(>.(8.O1.))))(:.(=.(;.(13.(>.(8.O1.))$11.)(18.(17.O1.)))(;.(13.(18.(17.O1.))+800000.)(>.(8.O1.))))(;.=(?.(8.O1.))))))))))(:.(;.(?.(8.O1.))(19.$1:.(<.(9.O1.))))(:.(;.(1;.O1.$1<.)$1=.)(;.(1>.(1?.O1.))$20.))))")
(* [comment removed for export] *).

#[using="Type"] Lemma wf_x67_frame : ltac2:(CDefT.buildp (gd_tbl_AModelXE ()) "Ph,$0.Ph',$0.P,(2.$21.(17.R1.)(17.R2.))P,(2.$1.(>.(8.R2.))(>.(8.R3.)))P,(2.$1.(?.(8.R3.))(?.(8.R4.)))P,Pc,$1.P,(:.(;.+1.R1.)(;.R1.+1?.))(2.$6.(7.(8.R6.)R2.)(7.(8.R7.)R2.))P,Pc,$1.P,(:.(;.+1.R1.)(;.R1.+1?.))(:.(2.$1.(3.(4.R7.R2.))(3.(4.R8.R2.)))(2.$1.(5.(4.R7.R2.))(5.(4.R8.R2.))))P,(;.(1>.(1?.R6.))(1>.(1?.R7.)))P,(22.R8.)(22.R8.)")
(* [comment removed for export] *).
Proof.
  (intros h h' EL EE ES EX ER EB dd_H; ddestruct dd_H as (X6 & X7 & X8 & X9)). unfold wf_x67. rewrite EL, EE, ES, (csum_epi_frame_ua h h' ER EX).
  split; [exact X6|]. split; [exact X7|]. split; [| lia].
  unfold carved in *. rewrite (proj2 (ER kBatchClass ltac:(unfold kBatchClass; lia))). exact X8.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma wf_x67_frame_acct : ltac2:(CDefT.buildp (gd_tbl_AModelXE ()) "Ph,$0.Ph',$0.P,(2.$21.(17.R1.)(17.R2.))P,(2.$23.(8.R2.)(8.R3.))P,Pc,$1.P,(:.(;.+1.R1.)(;.R1.+1?.))(:.(2.$1.(3.(4.R5.R2.))(3.(4.R6.R2.)))(2.$1.(5.(4.R5.R2.))(5.(4.R6.R2.))))P,(;.(1>.(1?.R4.))(1>.(1?.R5.)))P,(22.R6.)(22.R6.)")
(* [comment removed for export] *).
Proof.
  intros h h' EL EA ER EB X. apply (wf_x67_frame h h' EL); [rewrite EA; reflexivity| rewrite EA; reflexivity| intros c _; rewrite EA; reflexivity| exact ER| exact EB| exact X].
Qed.

End ARUN_1.
