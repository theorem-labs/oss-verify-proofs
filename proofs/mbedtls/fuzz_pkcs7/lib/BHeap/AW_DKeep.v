(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Mem Arr Bytes Asn1Aux CellsX SysStep ITree Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_MmapFixed AKinv AKinvS ASpinS AW_MmapAnon AW_MmapDie ASpin
     AW_DepotA AW_DepotB AW_DepotC AW_DepotD AW_DepotE AW_DepotF AW_DepotCfg AW_DepotInv AW_DepotTop.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AW_DKeep () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotTop.dkeep"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotB.A_SS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotTop.A_DEP_END"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.dblk"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotC.sblk"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Corelib.Init.Logic.not"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Logic.eq"; "Stdlib.Lists.List.In"].

Section ARUN_1. Context {hAR : arun}.
#[using="Type"] Lemma dkeep_window : ltac2:(CDefT.buildp (gd_tbl_AW_DKeep ()) "Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))Plo,$2.PSP,$2.Pnb,(3.$2.)Pbl,(3.$2.)PA,$2.Psz,$2.P,(4.R8.R7.R6.R5.R4.R3.)P,(5.=R3.)P,(5.(6.R4.R3.)(7.+2.+40.))P,(8.(5.(6.R5.R4.)R9.)(5.R8.R5.))P,(8.(5.(6.R6.R5.)$9.)(5.$:.R6.))P,Pk,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.R:.))))(8.(5.(6.R9.R8.)(?.R;.R2.))(5.(6.(?.R;.R2.)(7.+2.+14.))R9.))P,Pj,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.R:.))))(8.(5.(6.R:.R9.)(10.R;.R2.))(5.(6.(10.R;.R2.)(7.+2.+17.))R:.))(11.(12.(13.$2.$2.)(14.$2.$2.=R9.)(12.(13.$2.$2.)(14.$2.$2.(6.R9.R8.)(7.+2.+40.))(15.(13.$2.$2.))))R?.R>.)")
(* [comment removed for export] *).
Proof.
  intros m m' lo SP nb bl A sz DK A0 A1 H1 H2 H3 H4 x Hx. cbn [outside] in Hx. ddestruct Hx as (X1 & X2 & _).
  pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. change (2 ^ Z.of_N 64) with (2^64) in XR.
  apply DK.
  - clear - H1 X1 X2 XR. lia.
  - clear - H2 X1 X2 XR. lia.
  - intros k Hk. specialize (H3 k Hk). clear - H3 X1 X2 XR. lia.
  - intros j Hj. specialize (H4 j Hj). clear - H4 X1 X2 XR. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma dkeep_low : ltac2:(CDefT.buildp (gd_tbl_AW_DKeep ()) "Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))Plo,$2.PSP,$2.Pnb,(3.$2.)Pbl,(3.$2.)P,(4.R6.R5.R4.R3.R2.R1.)P,(5.+65?000.R5.)P,Pk,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.R5.))))(5.+65?000.(?.R6.R2.))P,Pj,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.R5.))))(5.+65?000.(10.R6.R2.))(11.(12.(13.$2.$2.)(14.$2.$2.$9.$:.)(12.(13.$2.$2.)(14.$2.$2.+65?000.(7.+2.+40.))(15.(13.$2.$2.))))R:.R9.)")
(* [comment removed for export] *).
Proof.
  intros m m' lo SP nb bl DK LO BN BS x Hx. cbn [outside] in Hx. ddestruct Hx as (X1 & X2 & _).
  pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. change (2 ^ Z.of_N 64) with (2^64) in XR.
  apply DK.
  - clear - LO X1 X2 XR. lia.
  - exact X1.
  - intros k Hk. specialize (BN k Hk). clear - BN X1 X2 XR. lia.
  - intros j Hj. specialize (BS j Hj). clear - BS X1 X2 XR. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma apart_of_cs : ltac2:(CDefT.buildp (gd_tbl_AW_DKeep ()) "PP,P,$2.SpPA,$2.Pn,$2.Pb,$2.Pw,$2.P,(16.R5.R4.R3.)P,Px,$2.P,A1.R7.R1.(17.(;.(5.R5.R2.)(<.R2.(6.R5.R4.))))P,(<.=R5.)P,(<.=R4.)(8.(5.(6.R8.R7.)R6.)(5.(6.R6.R5.)R8.))")
(* [comment removed for export] *).
Proof.
  intros P A n b w CR NB Hn Hw. destruct (Z_lt_dec b A).
  - destruct (Z_lt_dec A (b + w)); [| lia]. exfalso. apply (NB A); [apply CR; lia| lia].
  - destruct (Z_lt_dec b (A + n)); [| lia]. exfalso. apply (NB b); [apply CR; lia| lia].
Qed.
#[using="Type"] Lemma dblk_app_cases : ltac2:(CDefT.buildp (gd_tbl_AW_DKeep ()) "Pnb,(3.$2.)Psn,(3.$2.)Pk,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.(18.$2.R3.R2.)))))(8.(;.(;.(5.=R2.)(<.R2.(=.(>.$2.R4.))))(19.$2.(?.(18.$2.R4.R3.)R2.)(?.R4.R2.)))(1:.$2.(?.(18.$2.R4.R3.)R2.)R3.))")
(* [comment removed for export] *).
Proof.
  intros nb sn k Hk. unfold dblk. rewrite app_length in Hk. destruct (Z_lt_dec k (Z.of_nat (length nb))).
  - left. rewrite app_nth1 by lia. split; [lia| reflexivity].
  - right. rewrite app_nth2 by lia. apply nth_In. lia.
Qed.
#[using="Type"] Lemma sblk_app_cases : ltac2:(CDefT.buildp (gd_tbl_AW_DKeep ()) "Pbl,(3.$2.)Psb,(3.$2.)Pj,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.(18.$2.R3.R2.)))))(8.(;.(;.(5.=R2.)(<.R2.(=.(>.$2.R4.))))(19.$2.(10.(18.$2.R4.R3.)R2.)(10.R4.R2.)))(1:.$2.(10.(18.$2.R4.R3.)R2.)R3.))")
(* [comment removed for export] *).
Proof.
  intros bl sb j Hj. unfold sblk. rewrite app_length in Hj. destruct (Z_lt_dec j (Z.of_nat (length bl))).
  - left. rewrite app_nth1 by lia. split; [lia| reflexivity].
  - right. rewrite app_nth2 by lia. apply nth_In. lia.
Qed.
#[using="Type"] Lemma crange_mono : forall (P Q : Z -> Prop) A n, crange P A n -> (forall x, P x -> Q x) -> crange Q A n.
Proof. intros P Q A n CR PQ x Hx. apply PQ, CR, Hx. Qed.

(* [comment removed for export] *)


End ARUN_1.
