(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AModel AModelX.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.

From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AModelXE () : Init.string Init.list := ["OSSVerify.KrLib.AHeap.AModel.ahst"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.AHeap.AModel.r_mapped_user"; "OSSVerify.KrLib.AHeap.AModel.h_reg"; "OSSVerify.KrLib.AHeap.AModel.r_alloc_user"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.AHeap.AModel.a_exh"; "OSSVerify.KrLib.AHeap.AModel.h_acct"; "OSSVerify.KrLib.AHeap.AModelX.epi"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.AHeap.AModelX.csum"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.AHeap.AModel.a_emb"; "OSSVerify.KrLib.AHeap.AModel.a_esz"; "OSSVerify.KrLib.AHeap.AModel.lowhigh"; "OSSVerify.KrLib.AHeap.AModel.kEmbBytes"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.AHeap.ACeil.ACEIL"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.AHeap.AModel.l_b6"; "OSSVerify.KrLib.AHeap.AModel.h_L"; "OSSVerify.KrLib.AHeap.AModel.l_pa"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.AHeap.AModelX.EM"; "OSSVerify.KrLib.AHeap.AModel.carved"; "OSSVerify.KrLib.AHeap.AModel.kBatchClass"; "OSSVerify.KrLib.AHeap.AModelX.CMAX24"; "OSSVerify.KrLib.LibA.ACnt24.cnt24"; "OSSVerify.KrLib.AHeap.AModel.blocks"; "OSSVerify.KrLib.LibA.ACnt24.C24MAX"; "OSSVerify.KrLib.AHeap.AModel.alayout"; "ARUN_1.wf_x67"; "OSSVerify.KrLib.AHeap.AModel.acct"].
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
