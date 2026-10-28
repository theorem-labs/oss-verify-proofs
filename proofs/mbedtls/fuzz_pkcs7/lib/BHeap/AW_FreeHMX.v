(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX AW_FreeP AW_Blist AW_FakeDefs HMLib HM HMFrame AW_FreeHM.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AW_FreeHMX () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_T"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeHM.in_hull"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeHM.in_blk"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.shad"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_b6"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.prod"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.or"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.in_rangesZ"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeHM.free_img_ranges"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_pa"; "ARUN_1.in_rp"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.alayout"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeHM.fkeep"; "ARUN_1.fkeepR"; "Stdlib.Lists.List.incl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Lists.ListDef.Forall"; "ARUN_1.zone_okR"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.

Definition in_rp (RP : list (Z * Z)) (a : Z) : Prop := exists r, In r RP /\ fst r <= a < fst r + snd r.

Definition fkeepR (L : alayout) (LBK QS RP : list (Z * Z)) (NB BL : list Z) (lo SP : Z) (m m' : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_FreeHMX ()) "Px,(0.&40.)Za,$1.(2.&40.R1.)P,(3.(4.(5.O4.R1.)(6.R1.O3.)))P,(3.(4.(5.(7.O:.)R2.)(6.R2.(8.(7.O:.)+1000.))))P,(3.(4.(9.O:.R3.)(3.(:.O9.R3.))))P,(3.(4.(4.(5.(;.(<.O:.))R4.)(6.R4.(;.(8.(<.O:.)+2000011000.))))(3.(=.$1.Lc,$1.(4.(:.O9.R1.)(>.$1.R5.(;.R1.)))))))P,(3.(=.(?.$1.$1.)Lq,(?.$1.$1.)(4.(10.(?.$1.$1.)R1.O8.)(11.(4.(5.(12.$1.$1.R1.)R6.)(6.R6.(8.(12.$1.$1.R1.)(13.$1.$1.R1.))))(4.(5.(;.(12.$1.$1.R1.))R6.)(6.R6.(8.(;.(12.$1.$1.R1.))(14.(13.$1.$1.R1.)+8.))))))))P,(3.(15.$16.R6.))P,(3.(=.$1.Lb,$1.(4.(10.$1.R1.O6.)(4.(5.R1.R8.)(6.R8.(8.R1.(17.+2.+14.)))))))P,(3.(=.$1.Lb,$1.(4.(10.$1.R1.O5.)(4.(5.R1.R9.)(6.R9.(8.R1.(17.+2.+17.)))))))P,(3.(4.(5.(18.O:.)R9.)(6.R9.(8.(18.O:.)+800000.))))P,(3.(19.O7.R:.))(>.(1:.(0.&8.))A1.O1.R<.A1.O2.R<.)")
(* [comment removed for export] *).

#[using="Type"] Lemma fkeep_fkeepR : ltac2:(CDefT.buildp (gd_tbl_AW_FreeHMX ()) "PL,$1;.PLBK,(1<.(?.$1.$1.))PQS,(1<.(?.$1.$1.))PRP,(1<.(?.$1.$1.))PNB,(1<.$1.)PBL,(1<.$1.)Plo,$1.PSP,$1.Pm,P,(0.&40.)(1:.(0.&8.))Pm',P,(0.&40.)(1:.(0.&8.))P,(1=.R:.R9.R8.R6.R5.R4.R3.R2.R1.)(1>.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.)")
(* [comment removed for export] *).
Proof. intros L LBK QS RP NB BL lo SP m m' K x. cbv zeta. intros H1 H2 H3 H4 H5 H6 H7 H8 H9 _. exact (K x H1 H2 H3 H4 H5 H6 H7 H8 H9). Qed.


#[using="Type"] Lemma fkeepR_trans : ltac2:(CDefT.buildp (gd_tbl_AW_FreeHMX ()) "PL,$1;.PLBK,(1<.(?.$1.$1.))PQS,(1<.(?.$1.$1.))PRP,(1<.(?.$1.$1.))PNB,(1<.$1.)PBL,(1<.$1.)PNB',(1<.$1.)PBL',(1<.$1.)Plo,$1.PSP,$1.Pm1,P,(0.&40.)(1:.(0.&8.))Pm2,P,(0.&40.)(1:.(0.&8.))Pm3,P,(0.&40.)(1:.(0.&8.))P,(1>.R=.R<.R;.R:.R9.R8.R5.R4.R3.R2.)P,(1>.R>.R=.R<.R;.R8.R7.R6.R5.R3.R2.)P,(1?.$1.R;.R9.)P,(1?.$1.R;.R9.)(1>.R11.R10.R?.R>.R;.R:.R9.R8.R7.R5.)")
(* [comment removed for export] *).
Proof.
  intros L LBK QS RP NB BL NB' BL' lo SP m1 m2 m3 K1 K2 IN IB x. cbv zeta. intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
  pose proof (K1 x) as K1x. pose proof (K2 x) as K2x. cbv zeta in K1x, K2x.
  rewrite (K2x H1 H2 H3 H4 H5 H6 H7 H8 H9 H10). apply (K1x H1 H2 H3 H4 H5 H6); [| | exact H9| exact H10].
  - (intros dd_H; ddestruct dd_H as (b & Hb & R)). apply H7. exists b. split; [apply IN; exact Hb| exact R].
  - (intros dd_H; ddestruct dd_H as (b & Hb & R)). apply H8. exists b. split; [apply IB; exact Hb| exact R].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fkeepR_mono : ltac2:(CDefT.buildp (gd_tbl_AW_FreeHMX ()) "PL,$1;.PLBK,(1<.(?.$1.$1.))PQS,(1<.(?.$1.$1.))PQS',(1<.(?.$1.$1.))PRP,(1<.(?.$1.$1.))PRP',(1<.(?.$1.$1.))PNB,(1<.$1.)PBL,(1<.$1.)Plo,$1.PSP,$1.Pm,P,(0.&40.)(1:.(0.&8.))Pm',P,(0.&40.)(1:.(0.&8.))P,(1>.R<.R;.R:.R8.R6.R5.R4.R3.R2.R1.)P,(1?.(?.$1.$1.)R;.R:.)P,(1?.(?.$1.$1.)R:.R9.)(1>.R?.R>.R<.R:.R9.R8.R7.R6.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros L LBK QS QS' RP RP' NB BL lo SP m m' K IQ IR x. cbv zeta. intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
  apply (K x H1 H2 H3 H4); [| exact H6| exact H7| exact H8| exact H9|].
  - (intros dd_H; ddestruct dd_H as (q & Hq & R)). apply H5. exists q. split; [apply IQ; exact Hq| exact R].
  - (intros dd_H; ddestruct dd_H as (r & Hr & R)). apply H10. exists r. split; [apply IR; exact Hr| exact R].
Qed.

Definition zone_okR (L : alayout) (LBK QS RP : list (Z * Z)) (NB BL : list Z) (lo SP : Z) (iv : Z * Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_FreeHMX ()) "Pa,$1.P,(4.(5.(12.$1.$1.O1.)R1.)(6.R1.(13.$1.$1.O1.)))(11.(4.(5.O3.R2.)(6.R2.O2.))(11.(4.(5.(7.O9.)R2.)(6.R2.(8.(7.O9.)+1000.)))(11.(4.(9.O9.R2.)(3.(:.O8.R2.)))(11.(4.(4.(5.(;.(<.O9.))R2.)(6.R2.(;.(8.(<.O9.)+2000011000.))))(3.(=.$1.Lc,$1.(4.(:.O8.R1.)(>.$1.R3.(;.R1.))))))(11.(=.(?.$1.$1.)Lq,(?.$1.$1.)(4.(10.(?.$1.$1.)R1.O7.)(11.(4.(5.(12.$1.$1.R1.)R3.)(6.R3.(8.(12.$1.$1.R1.)(13.$1.$1.R1.))))(4.(5.(;.(12.$1.$1.R1.))R3.)(6.R3.(8.(;.(12.$1.$1.R1.))(14.(13.$1.$1.R1.)+8.)))))))(11.(15.$16.R2.)(11.(=.$1.Lb,$1.(4.(10.$1.R1.O5.)(4.(5.R1.R3.)(6.R3.(8.R1.(17.+2.+14.))))))(11.(=.$1.Lb,$1.(4.(10.$1.R1.O4.)(4.(5.R1.R3.)(6.R3.(8.R1.(17.+2.+17.))))))(11.(4.(5.(18.O9.)R2.)(6.R2.(8.(18.O9.)+800000.)))(19.O6.R2.))))))))))")
(* [comment removed for export] *).

#[using="Type"] Lemma fkeepR_of_munch : ltac2:(CDefT.buildp (gd_tbl_AW_FreeHMX ()) "PL,$1;.PLBK,(1<.(?.$1.$1.))PQS,(1<.(?.$1.$1.))PRP,(1<.(?.$1.$1.))PNB,(1<.$1.)PBL,(1<.$1.)Plo,$1.PSP,$1.PW,(1<.$20.)Pm,P,(0.&40.)(1:.(0.&8.))Pm',P,(0.&40.)(1:.(0.&8.))P,(21.R3.R2.R1.)P,(22.(?.$1.$1.)(23.R<.R;.R:.R9.R8.R7.R6.R5.)R4.)(1>.R=.R<.R;.R:.R9.R8.R7.R6.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros L LBK QS RP NB BL lo SP W m m' MU ZW x. cbv zeta. intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10. apply MU. clear MU.
  induction W as [|[u v] W IH]; [exact I|]. inversion ZW as [|iv W' Z1 Z2]; subst. cbn. split; [| exact (IH Z2)].
  intros R. destruct (Z1 (bv_unsigned x) R) as [X|[X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]]; tauto.
Qed.

End ARUN_1.
