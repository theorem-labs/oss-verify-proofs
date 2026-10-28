(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts MpiOpnd.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_mpi_opnd () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_limbs"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.MPI_MAX_LIMBS"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "opnd_atA"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C2"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_layout"].


Definition temp_opndA (segs : list Segment) (R : art_layout) (LF : list blk) (m : mem) (SP : Z) (d : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_opnd ()) "(0.(1.$2.(3.O1.)$4.)(0.(5.O6.O3.(6.O1.)(7.(8.O1.)(9.&40.(:.O1.))(;.O1.)(<.O1.)))(0.(1.$=.(>.(6.O1.)+8.)=)(0.(?.=(6.O1.))(0.(1.$=.(10.(11.(12.&40.)(13.O1.)))(;.O1.))(0.(0.(14.=(;.O1.))(14.(;.O1.)$15.))(0.(14.+1.(;.O1.))(0.(1.$=.(>.(8.O1.)+4.)=)(0.(?.=(8.O1.))(0.(16.O6.O3.(8.O1.)(17.(13.O1.)))(0.(18.(19.O5.)(1:.O4.)O2.(8.O1.)(1;.+4.(;.O1.)))(0.(?.(1<.(8.O1.)(1;.+4.(;.O1.)))(1=.+2.+40.))(1>.(1.$=.(:.O1.)+1.)(1.$=.(:.O1.)-1.))))))))))))))")
(* [comment removed for export] *).

Definition opnd_atA (segs : list Segment) (R : art_layout) (LF : list blk) (m : mem) (LB : list blk) (SP : Z) (d : mpd) : Prop :=
  mpd_at segs m LB d \/ temp_opndA segs R LF m SP d.

Lemma opnd_atA_mpd : forall segs R LF m LB SP d, mpd_at segs m LB d -> opnd_atA segs R LF m LB SP d.
Proof. intros; left; assumption. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma opnd_viewA : forall segs R LF m LB SP d, opnd_atA segs R LF m LB SP d ->
  (rw_cells segs m (md_addr d) (mpi_cells (md_p d) (Z_to_bv 64 (md_sg d)) (md_n d) (md_pad d))
   /\ md_addr d mod 8 = 0 /\ 0 < md_addr d /\ Z.of_nat (length (md_limbs d)) = md_n d /\ 0 <= md_n d <= MPI_MAX_LIMBS
   /\ match md_own d with
      | LNull => md_p d = 0 /\ md_n d = 0
      | LHeap => 1 <= md_n d /\ In (md_p d, 4 * md_n d) LB /\ md_p d mod 16 = 0 /\ u32arr segs m (md_p d) (md_limbs d)
      | LStatic => 1 <= md_n d /\ md_p d mod 4 = 0 /\ 0 < md_p d /\ bytes_at segs m (md_p d) (u32s (md_limbs d))
                   /\ ((forall i, 0 <= i < 4 * md_n d -> ro_addr segs (wa (md_p d + i)) = true)
                       \/ (client_range (arl_L R) (fdata LF) SP (md_p d) (4 * md_n d) /\ md_p d + 4 * md_n d < 2^64))
      end)
  /\ (md_sg d = 1 \/ md_sg d = -1).
Proof.
  intros segs R LF m LB SP d [[HA HS]|K].
  - split; [| exact HS]. ddestruct HA as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|].
    destruct (md_own d); [exact Q6| exact Q6|]. ddestruct Q6 as (D1 & D2 & D3 & D4 & D5).
    split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [exact D4|]. left. exact D5.
  - ddestruct K as (EO & Q1 & Q2 & Q3 & Q4 & Q5 & D1 & D2 & D3 & D4 & D6 & D7 & HS). split; [| exact HS].
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|].
    rewrite EO. split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [exact D4|]. right. split; [exact D6| exact D7].
Qed.

Lemma opnd_atA_SP_le : ltac2:(CDefT.buildp (gd_tbl_A_mpi_opnd ()) "Psegs,(1?.$20.)PR,$21.PLF,(1?.$22.)Pm,P,(12.&40.)(23.(12.&8.))PLB,(1?.$22.)PSP,$=.PSP',$=.Pd,$24.P,(25.R8.R7.R6.R5.R4.R3.R1.)P,(14.R3.R4.)(25.R:.R9.R8.R7.R6.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros segs R LF m LB SP SP' d [H|K] LE; [left; exact H| right].
  ddestruct K as (EO & Q1 & Q2 & Q3 & Q4 & Q5 & D1 & D2 & D3 & D4 & D6 & D7 & HS).
  repeat (split; [assumption|]). split; [eapply client_range_sp_mono; [exact LE| exact D6]|]. split; [exact D7| exact HS].
Qed.

(* [comment removed for export] *)

Lemma opnd_atA_blocks : ltac2:(CDefT.buildp (gd_tbl_A_mpi_opnd ()) "Psegs,(1?.$20.)PR,$21.PLF,(1?.$22.)Pm,P,(12.&40.)(23.(12.&8.))PLB,(1?.$22.)PLB',(1?.$22.)PSP,$=.Pd,$24.P,(25.R8.R7.R6.R5.R4.R2.R1.)P,Pb,$22.P,(26.$22.R1.(27.R3.))(26.$22.R2.R6.)(25.R:.R9.R8.R7.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros segs R LF m LB LB' SP d [[HA HS]|K] HBL; [left| right; exact K]. split; [| exact HS].
  ddestruct HA as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6). split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|].
  destruct (md_own d) eqn:EO; [exact Q6| | exact Q6]. ddestruct Q6 as (D1 & D2 & D3 & D4). split; [exact D1|].
  split; [apply HBL; unfold mpd_blk; rewrite EO; left; reflexivity|]. split; [exact D3| exact D4].
Qed.

Lemma opnd_atA_munch_any : ltac2:(CDefT.buildp (gd_tbl_A_mpi_opnd ()) "Psegs,(1?.$20.)PR,$21.PLF,(1?.$22.)Pm,P,(12.&40.)(23.(12.&8.))Pm',P,(12.&40.)(23.(12.&8.))PLB,(1?.$22.)PSP,$=.Pd,$24.PW,(1?.$28.)P,(25.R9.R8.R7.R6.R4.R3.R2.)P,(29.R2.R7.R6.)P,(2:.R;.R8.R7.)P,(2;.R4.(6.R5.)+10.)P,P,(2<.(1.$2.(3.R6.)$2=.))(2;.R6.(8.R7.)(1;.+4.(;.R7.)))(25.R>.R=.R<.R:.R9.R8.R7.)")
(* [comment removed for export] *).
Proof.
  intros segs R LF m m' LB SP d W [H|K] MU WM D1 D2.
  - left. eapply mpd_at_munch_any; eassumption.
  - right. ddestruct K as (EO & Q1 & Q2 & Q3 & Q4 & Q5 & E1 & E2 & E3 & E4 & E6 & E7 & HS).
    split; [exact EO|]. split; [eapply rw_cells_transport; [exact Q1| exact MU| exact WM| exact D1]|].
    split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|]. split; [exact E1|]. split; [exact E2|]. split; [exact E3|].
    split; [eapply u32ro_transport; [exact E4| exact MU|]; rewrite Q4; apply D2; rewrite EO; discriminate|].
    split; [exact E6|]. split; [exact E7| exact HS].
Qed.

(* [comment removed for export] *)
Lemma opnd_atA_heap_presx : ltac2:(CDefT.buildp (gd_tbl_A_mpi_opnd ()) "Psegs,(1?.$20.)PR,$21.PLF,(1?.$22.)Pm,P,(12.&40.)(23.(12.&8.))Pm',P,(12.&40.)(23.(12.&8.))PLB,(1?.$22.)PLBp,(1?.$22.)PLB',(1?.$22.)PSPh,$=.PSP,$=.PXI,(1?.$28.)Pd,$24.P,(25.R<.R;.R:.R9.R7.R3.R1.)P,(2>.R=.(19.R<.)R7.R5.R3.R:.R9.)P,(2?.R>.R;.)P,(2?.R?.R;.)P,(18.(19.R?.)R:.R8.(6.R5.)+10.)P,P,(1.$2.(3.R6.)$30.)(18.(19.R11.)R<.R:.(8.R7.)(1;.+4.(;.R7.)))P,(2;.R8.(6.R7.)+10.)P,P,(2<.(1.$2.(3.R8.)$2=.))(2;.R:.(8.R9.)(1;.+4.(;.R9.)))P,Pb,$22.P,(26.$22.R1.(27.R:.))(26.$22.R2.R?.)P,(14.R=.R<.)P,Pb,$22.P,(26.$22.R1.(1:.R15.))(26.$22.R2.R12.)(25.R17.R16.R15.R13.R10.R>.R<.)")
(* [comment removed for export] *).
Proof.
  intros segs R LF m m' LB LBp LB' SPh SP XI d [H|K] HP MI MI' CR CRL X1 X2 HBL LE SUBF.
  - left. eapply mpd_at_heap_presx; try eassumption. intros EO. apply X2. rewrite EO. discriminate.
  - right. ddestruct K as (EO & Q1 & Q2 & Q3 & Q4 & Q5 & E1 & E2 & E3 & E4 & E6 & E7 & HS).
    split; [exact EO|]. split; [eapply heap_presx_rw_cells; [exact HP| exact Q1| exact CR| exact X1]|].
    split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|]. split; [exact E1|]. split; [exact E2|]. split; [exact E3|].
    split; [| split; [exact E6| split; [exact E7| exact HS]]].
    assert (E4L : Z.of_nat (length (u32s (md_limbs d))) = 4 * md_n d) by (rewrite u32s_length; lia).
    eapply heap_presx_bytes_at; [exact HP| exact E4| rewrite E4L| rewrite E4L; apply X2; rewrite EO; discriminate].
    intros a Ha. destruct (E6 a Ha) as [C|[C|(b & Hb & Rb)]]; [left; lia| right; left; exact C| right; right; exists b; split; [apply SUBF; exact Hb| exact Rb]].
Qed.

(* [comment removed for export] *)
Lemma opnd_atA_mpd_back : ltac2:(CDefT.buildp (gd_tbl_A_mpi_opnd ()) "Psegs,(1?.$20.)PR,$21.PLF,(1?.$22.)Pm0,P,(12.&40.)(23.(12.&8.))PLB0,(1?.$22.)Pm,P,(12.&40.)(23.(12.&8.))PLB,(1?.$22.)PSP,$=.Pd,$24.P,(31.R9.R6.R5.R1.)P,(25.R:.R9.R8.R5.R4.R3.R2.)(31.R;.R6.R5.R3.)")
(* [comment removed for export] *).
Proof.
  intros segs R LF m0 LB0 m LB SP d [HA0 HS0] [H|K]; [exact H|].
  ddestruct K as (EO & Q1 & Q2 & Q3 & Q4 & Q5 & D1 & D2 & D3 & D4 & D6 & D7 & HS). split; [| exact HS].
  ddestruct HA0 as (_ & _ & _ & _ & _ & OW0). rewrite EO in OW0. ddestruct OW0 as (_ & _ & _ & _ & RO).
  split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|].
  rewrite EO. split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [exact D4| exact RO].
Qed.

(* [comment removed for export] *)
Lemma opnd_rawA : ltac2:(CDefT.buildp (gd_tbl_A_mpi_opnd ()) "Psegs,(1?.$20.)PR,$21.PLF,(1?.$22.)Pm,P,(12.&40.)(23.(12.&8.))PLB,(1?.$22.)PSP,$=.Pd,$24.P,(25.R7.R6.R5.R4.R3.R2.R1.)P,P,(1.$2.(3.R2.)$30.)(?.=(8.R3.))(0.(5.R9.R6.(6.R3.)(32.$33.(34.(9.&40.(8.R3.)))(32.$33.(35.(9.&40.(:.R3.)))(32.$33.(35.(9.&40.(;.R3.)))(32.$33.(36.(<.R3.))(37.$33.))))))(0.(16.R9.R6.(8.R3.)(17.(13.R3.)))(0.(1.$=.(10.(11.(12.&40.)(13.R3.)))(;.R3.))(0.(0.(14.=(;.R3.))(14.(;.R3.)+2710.))(0.(1>.(1.$=.(:.R3.)+1.)(1.$=.(:.R3.)-1.))(0.(0.(14.=(6.R3.))(14.(1<.(6.R3.)+10.)(1=.+2.+40.)))(1>.(1.$=.(;.R3.)=)(0.(?.=(8.R3.))(1.$=.(>.(8.R3.)+4.)=)))))))))")
(* [comment removed for export] *).
Proof.
  intros segs R LF m LB SP d HA PNZ. pose proof (opnd_viewA _ _ _ _ _ _ _ HA) as [(HR & HAL & HPOS & HL & HN & HO) HS]. unfold MPI_MAX_LIMBS in HN.
  unfold mpi_cells in HR.
  pose proof (rw_cells_bound _ _ _ _ HR) as B. cbn [cells_size csize Nat.add] in B.
  split; [exact HR|].
  assert (K : bytes_at segs m (md_p d) (u32s (md_limbs d)) /\ (md_n d = 0 \/ 0 < md_p d /\ md_p d mod 4 = 0)).
  { destruct (md_own d) eqn:EO.
    - destruct HO as [HP HN0]. rewrite HP. assert (md_limbs d = []) as -> by (destruct (md_limbs d); [reflexivity| cbn in HL; lia]).
      split; [| left; exact HN0]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
    - ddestruct HO as (N1 & PIN & PAL & [HB _]). split; [exact HB| right]. split; [exact (PNZ eq_refl)|].
      apply Z.mod_divide in PAL; [| lia]. apply Z.mod_divide; [lia|]. destruct PAL as [k E]. exists (4 * k). lia.
    - ddestruct HO as (N1 & PAL & PP & HB & _). split; [exact HB| right; split; [exact PP| exact PAL]]. }
  destruct K as [K1 K2]. split; [exact K1|]. split; [exact HL|]. split; [lia|]. split; [exact HS|]. split; [lia| exact K2].
Qed.

(* [comment removed for export] *)
Lemma client_range_temp : ltac2:(CDefT.buildp (gd_tbl_A_mpi_opnd ()) "PL,$38.PLT,(1?.$22.)PLBn,(1?.$22.)PSP,$=.PSP',$=.PA,$=.Pn,$=.P,(18.R7.R6.R4.R2.R1.)P,(14.R4.R5.)P,Pb,$22.P,(26.$22.R1.R9.)(26.$22.R2.R9.)(18.R:.R8.R6.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros L LT LBn SP SP' A n H LE SUB a Ha.
  destruct (H a Ha) as [C|[C|(b & Hb & Rb)]]; [left; lia| right; left; exact C| right; right; exists b; split; [apply SUB; exact Hb| exact Rb]].
Qed.
