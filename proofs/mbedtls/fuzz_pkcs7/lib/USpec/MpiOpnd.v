(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux AStep CellsX MpiCoreAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_mpi_addsub.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_MpiOpnd () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_layout"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_pres"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_limbs"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.MPI_MAX_LIMBS"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.ro_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Corelib.Init.Datatypes.true"; "opnd_at"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C2"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_sep"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.opnd_sep"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpd_writable"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpi_binop_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_iface"; "mpi_binop_stmt'"; "mpi_binop_stmtB'"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpi_binop_stmt"].


(* [comment removed for export] *)
Lemma mpd_at_munch_any : ltac2:(CDefT.buildp (gd_tbl_MpiOpnd ()) "Psegs,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))PLB,(0.$4.)Pd,$5.PW,(0.$6.)P,(7.R6.R5.R3.R2.)P,(8.R2.R6.R5.)P,(9.R8.R7.R6.)P,(:.R4.(;.R5.)+10.)P,P,(<.(=.$>.(?.R6.)$10.))(:.R6.(11.R7.)(12.+4.(13.R7.)))(7.R;.R9.R8.R7.)")
(* [comment removed for export] *).
Proof.
  intros segs m m' LB d W [HA HS] MU WM HD1 HD2. split; [| exact HS].
  destruct HA as (HR & HAL & HPOS & HL & HN & HO).
  split; [| split; [exact HAL| split; [exact HPOS| split; [exact HL| split; [exact HN|]]]]].
  - eapply rw_cells_transport; [exact HR| exact MU| exact WM| exact HD1].
  - destruct (md_own d); [exact HO| |].
    + destruct HO as (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
      eapply u32arr_transport; [exact H4| exact MU| exact WM|]. rewrite HL. apply HD2. discriminate.
    + destruct HO as (H1 & H2 & H3 & H4 & H5). split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [| exact H5].
      eapply u32ro_transport; [exact H4| exact MU|]. rewrite HL. apply HD2. discriminate.
Qed.

Lemma mpd_at_heap_pres : ltac2:(CDefT.buildp (gd_tbl_MpiOpnd ()) "Psegs,(0.$1.)PL,$14.Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))PLB,(0.$4.)PLBh,(0.$4.)PLB',(0.$4.)PSP,$15.Pd,$5.P,(7.R9.R7.R5.R1.)P,(16.R:.R9.R5.R3.R8.R7.)P,(17.R;.R9.)P,(17.R<.R9.)P,(18.R<.R8.R6.(;.R5.)+10.)P,P,(=.$>.(?.R6.)$19.)(18.R>.R:.R8.(11.R7.)(12.+4.(13.R7.)))P,Pb,$4.P,(1:.$4.R1.(1;.R8.))(1:.$4.R2.R;.)(7.R10.R=.R:.R8.)")
(* [comment removed for export] *).
Proof.
  intros segs L m m' LB LBh LB' SP d [HA HS] HP MI MI' CR CRL HBL. split; [| exact HS].
  destruct HA as (HR & HAL & HPOS & HL & HN & HO).
  split; [| split; [exact HAL| split; [exact HPOS| split; [exact HL| split; [exact HN|]]]]].
  - eapply heap_pres_rw_cells; [exact HP| exact HR| exact CR].
  - destruct (md_own d) eqn:EO; [exact HO| |].
    + destruct HO as (H1 & H2 & H3 & [H4 H5]). split; [exact H1|]. split; [apply HBL; unfold mpd_blk; rewrite EO; left; reflexivity|]. split; [exact H3|].
      split; [eapply heap_pres_bytes_at; [exact HP| exact H4| rewrite u32s_length; replace (Z.of_nat (4 * length (md_limbs d))) with (4 * md_n d) by lia; exact (CRL eq_refl)]|].
      eapply heap_pres_wr_at; [exact HP| exact H5| rewrite HL; exact (CRL eq_refl)].
    + destruct HO as (H1 & H2 & H3 & H4 & H5). split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [| exact H5].
      eapply static_limbs_any_mem; [exact MI| exact MI'| exact H4|]. rewrite u32s_length. intros i Hi. apply H5. lia.
Qed.

Lemma mpd_at_heap_presx : ltac2:(CDefT.buildp (gd_tbl_MpiOpnd ()) "Psegs,(0.$1.)PL,$14.Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))PLB,(0.$4.)PLBp,(0.$4.)PLB',(0.$4.)PSP,$15.PXI,(0.$6.)Pd,$5.P,(7.R:.R8.R6.R1.)P,(1<.R;.R:.R6.R4.R3.R9.R8.)P,(17.R<.R:.)P,(17.R=.R:.)P,(18.R=.R9.R7.(;.R5.)+10.)P,P,(=.$>.(?.R6.)$19.)(18.R?.R;.R9.(11.R7.)(12.+4.(13.R7.)))P,(:.R8.(;.R7.)+10.)P,P,(=.$>.(?.R8.)$19.)(:.R:.(11.R9.)(12.+4.(13.R9.)))P,Pb,$4.P,(1:.$4.R1.(1;.R:.))(1:.$4.R2.R>.)(7.R13.R10.R=.R:.)")
(* [comment removed for export] *).
Proof.
  intros segs L m m' LB LBp LB' SP XI d [HA HS] HP MI MI' CR CRL D1 D2 HBL. split; [| exact HS].
  destruct HA as (HR & HAL & HPOS & HL & HN & HO).
  split; [| split; [exact HAL| split; [exact HPOS| split; [exact HL| split; [exact HN|]]]]].
  - eapply heap_presx_rw_cells; [exact HP| exact HR| exact CR| exact D1].
  - destruct (md_own d) eqn:EO; [exact HO| |].
    + destruct HO as (H1 & H2 & H3 & [H4 H5]). split; [exact H1|]. split; [apply HBL; unfold mpd_blk; rewrite EO; left; reflexivity|]. split; [exact H3|].
      assert (E4 : Z.of_nat (length (u32s (md_limbs d))) = 4 * md_n d) by (rewrite u32s_length; lia).
      split; [eapply heap_presx_bytes_at; [exact HP| exact H4| rewrite E4; exact (CRL eq_refl)| rewrite E4; exact (D2 eq_refl)]|].
      eapply heap_presx_wr_at; [exact HP| exact H5| rewrite HL; exact (CRL eq_refl)| rewrite HL; exact (D2 eq_refl)].
    + destruct HO as (H1 & H2 & H3 & H4 & H5). split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [| exact H5].
      eapply static_limbs_any_mem; [exact MI| exact MI'| exact H4|]. rewrite u32s_length. intros i Hi. apply H5. lia.
Qed.


Definition stack_opnd (segs : list Segment) (m : mem) (SP : Z) (d : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_MpiOpnd ()) "(1=.(=.$>.(?.O1.)$1>.)(1=.(1?.O4.O3.(;.O1.)(20.(11.O1.)(21.&40.(22.O1.))(13.O1.)(23.O1.)))(1=.(=.$15.(24.(;.O1.)+8.)=)(1=.(25.=(;.O1.))(1=.(=.$15.(26.(27.(2.&40.)(28.O1.)))(13.O1.))(1=.(1=.(29.=(13.O1.))(29.(13.O1.)$2:.))(1=.(29.+1.(13.O1.))(1=.(=.$15.(24.(11.O1.)+4.)=)(1=.(25.=(11.O1.))(1=.(2;.O4.O3.(11.O1.)(2<.(28.O1.)))(1=.(29.O2.(11.O1.))(1=.(25.(2=.(11.O1.)(12.+4.(13.O1.)))(2>.+2.+40.))(2?.(=.$15.(22.O1.)+1.)(=.$15.(22.O1.)-1.))))))))))))))")
(* [comment removed for export] *).

Definition opnd_at (segs : list Segment) (m : mem) (LB : list blk) (SP : Z) (d : mpd) : Prop :=
  mpd_at segs m LB d \/ stack_opnd segs m SP d.

Lemma opnd_at_mpd : forall segs m LB SP d, mpd_at segs m LB d -> opnd_at segs m LB SP d.
Proof. intros; left; assumption. Qed.

(* [comment removed for export] *)
Definition limbs_where (segs : list Segment) (SP : Z) (d : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_MpiOpnd ()) "(2?.Pi,$15.P,(1=.(29.=R1.)(25.R1.(12.+4.(13.O1.))))(=.$30.(31.O3.(32.(2=.(11.O1.)R2.)))$33.)(1=.(29.O2.(11.O1.))(25.(2=.(11.O1.)(12.+4.(13.O1.)))(2>.+2.+40.))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Lemma opnd_view : forall segs m LB SP d, opnd_at segs m LB SP d ->
  (rw_cells segs m (md_addr d) (mpi_cells (md_p d) (Z_to_bv 64 (md_sg d)) (md_n d) (md_pad d))
   /\ md_addr d mod 8 = 0 /\ 0 < md_addr d /\ Z.of_nat (length (md_limbs d)) = md_n d /\ 0 <= md_n d <= MPI_MAX_LIMBS
   /\ match md_own d with
      | LNull => md_p d = 0 /\ md_n d = 0
      | LHeap => 1 <= md_n d /\ In (md_p d, 4 * md_n d) LB /\ md_p d mod 16 = 0 /\ u32arr segs m (md_p d) (md_limbs d)
      | LStatic => 1 <= md_n d /\ md_p d mod 4 = 0 /\ 0 < md_p d /\ bytes_at segs m (md_p d) (u32s (md_limbs d))
                   /\ ((forall i, 0 <= i < 4 * md_n d -> ro_addr segs (wa (md_p d + i)) = true) \/ (SP <= md_p d /\ md_p d + 4 * md_n d < 2^64))
      end)
  /\ (md_sg d = 1 \/ md_sg d = -1).
Proof.
  intros segs m LB SP d [[HA HS]|K].
  - split; [| exact HS]. destruct HA as (C1 & C2 & C3 & C4 & C5 & C6).
    split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5|].
    destruct (md_own d); [exact C6| exact C6|]. destruct C6 as (D1 & D2 & D3 & D4 & D5).
    split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [exact D4|]. left. exact D5.
  - destruct K as (EO & C1 & C2 & C3 & C4 & C5 & D1 & D2 & D3 & D4 & D6 & D7 & HS). split; [| exact HS].
    split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5|].
    rewrite EO. split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [exact D4|]. right. split; [exact D6| exact D7].
Qed.

Lemma opnd_at_SP_le : forall segs m LB SP SP' d, opnd_at segs m LB SP d -> SP' <= SP -> opnd_at segs m LB SP' d.
Proof.
  intros segs m LB SP SP' d [H|K] LE; [left; exact H| right].
  destruct K as (EO & C1 & C2 & C3 & C4 & C5 & D1 & D2 & D3 & D4 & D6 & D7 & HS).
  repeat (split; [assumption|]). split; [lia|]. split; [exact D7| exact HS].
Qed.

Lemma opnd_at_blocks : ltac2:(CDefT.buildp (gd_tbl_MpiOpnd ()) "Psegs,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))PLB,(0.$4.)PLB',(0.$4.)PSP,$15.Pd,$5.P,(34.R6.R5.R4.R2.R1.)P,Pb,$4.P,(1:.$4.R1.(1;.R3.))(1:.$4.R2.R6.)(34.R8.R7.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros segs m LB LB' SP d [[HA HS]|K] HBL; [left| right; exact K]. split; [| exact HS].
  destruct HA as (C1 & C2 & C3 & C4 & C5 & C6). split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5|].
  destruct (md_own d) eqn:EO; [exact C6| | exact C6]. destruct C6 as (D1 & D2 & D3 & D4). split; [exact D1|].
  split; [apply HBL; unfold mpd_blk; rewrite EO; left; reflexivity|]. split; [exact D3| exact D4].
Qed.

Lemma opnd_at_munch_any : ltac2:(CDefT.buildp (gd_tbl_MpiOpnd ()) "Psegs,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))PLB,(0.$4.)PSP,$15.Pd,$5.PW,(0.$6.)P,(34.R7.R6.R4.R3.R2.)P,(8.R2.R7.R6.)P,(9.R9.R8.R7.)P,(:.R4.(;.R5.)+10.)P,P,(<.(=.$>.(?.R6.)$10.))(:.R6.(11.R7.)(12.+4.(13.R7.)))(34.R<.R:.R9.R8.R7.)")
(* [comment removed for export] *).
Proof.
  intros segs m m' LB SP d W [H|K] MU WM D1 D2.
  - left. eapply mpd_at_munch_any; eassumption.
  - right. destruct K as (EO & C1 & C2 & C3 & C4 & C5 & E1 & E2 & E3 & E4 & E6 & E7 & HS).
    split; [exact EO|]. split; [eapply rw_cells_transport; [exact C1| exact MU| exact WM| exact D1]|].
    split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5|]. split; [exact E1|]. split; [exact E2|]. split; [exact E3|].
    split; [eapply u32ro_transport; [exact E4| exact MU|]; rewrite C4; apply D2; rewrite EO; discriminate|].
    split; [exact E6|]. split; [exact E7| exact HS].
Qed.

Lemma opnd_at_heap_pres : ltac2:(CDefT.buildp (gd_tbl_MpiOpnd ()) "Psegs,(0.$1.)PL,$14.Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))PLB,(0.$4.)PLBh,(0.$4.)PLB',(0.$4.)PSPh,$15.PSP,$15.Pd,$5.P,(34.R:.R8.R6.R2.R1.)P,(16.R;.R:.R6.R4.R9.R8.)P,(17.R<.R:.)P,(17.R=.R:.)P,(18.R=.R9.R7.(;.R5.)+10.)P,P,(=.$>.(?.R6.)$19.)(18.R?.R;.R9.(11.R7.)(12.+4.(13.R7.)))P,Pb,$4.P,(1:.$4.R1.(1;.R8.))(1:.$4.R2.R<.)P,(29.R:.R9.)(34.R12.R?.R<.R:.R9.)")
(* [comment removed for export] *).
Proof.
  intros segs L m m' LB LBh LB' SPh SP d [H|K] HP MI MI' CR CRL HBL LE.
  - left. eapply mpd_at_heap_pres; eassumption.
  - right. destruct K as (EO & C1 & C2 & C3 & C4 & C5 & E1 & E2 & E3 & E4 & E6 & E7 & HS).
    split; [exact EO|]. split; [eapply heap_pres_rw_cells; [exact HP| exact C1| exact CR]|].
    split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5|]. split; [exact E1|]. split; [exact E2|]. split; [exact E3|].
    split; [| split; [exact E6| split; [exact E7| exact HS]]].
    eapply heap_pres_bytes_at; [exact HP| exact E4|]. rewrite u32s_length. intros a Ha. left. lia.
Qed.

Lemma opnd_at_heap_presx : ltac2:(CDefT.buildp (gd_tbl_MpiOpnd ()) "Psegs,(0.$1.)PL,$14.Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))PLB,(0.$4.)PLBp,(0.$4.)PLB',(0.$4.)PSPh,$15.PSP,$15.PXI,(0.$6.)Pd,$5.P,(34.R;.R9.R7.R3.R1.)P,(1<.R<.R;.R7.R5.R3.R:.R9.)P,(17.R=.R;.)P,(17.R>.R;.)P,(18.R>.R:.R8.(;.R5.)+10.)P,P,(=.$>.(?.R6.)$19.)(18.R10.R<.R:.(11.R7.)(12.+4.(13.R7.)))P,(:.R8.(;.R7.)+10.)P,P,(<.(=.$>.(?.R8.)$10.))(:.R:.(11.R9.)(12.+4.(13.R9.)))P,Pb,$4.P,(1:.$4.R1.(1;.R:.))(1:.$4.R2.R?.)P,(29.R=.R<.)(34.R15.R12.R?.R=.R;.)")
(* [comment removed for export] *).
Proof.
  intros segs L m m' LB LBp LB' SPh SP XI d [H|K] HP MI MI' CR CRL X1 X2 HBL LE.
  - left. eapply mpd_at_heap_presx; try eassumption. intros EO. apply X2. rewrite EO. discriminate.
  - right. destruct K as (EO & C1 & C2 & C3 & C4 & C5 & E1 & E2 & E3 & E4 & E6 & E7 & HS).
    split; [exact EO|]. split; [eapply heap_presx_rw_cells; [exact HP| exact C1| exact CR| exact X1]|].
    split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5|]. split; [exact E1|]. split; [exact E2|]. split; [exact E3|].
    split; [| split; [exact E6| split; [exact E7| exact HS]]].
    assert (E4L : Z.of_nat (length (u32s (md_limbs d))) = 4 * md_n d) by (rewrite u32s_length; lia).
    eapply heap_presx_bytes_at; [exact HP| exact E4| rewrite E4L; intros a Ha; left; lia| rewrite E4L; apply X2; rewrite EO; discriminate].
Qed.

(* [comment removed for export] *)
Lemma opnd_at_mpd_back : forall segs m0 LB0 m LB SP d, mpd_at segs m0 LB0 d -> opnd_at segs m LB SP d -> mpd_at segs m LB d.
Proof.
  intros segs m0 LB0 m LB SP d [HA0 HS0] [H|K]; [exact H|].
  destruct K as (EO & C1 & C2 & C3 & C4 & C5 & D1 & D2 & D3 & D4 & D6 & D7 & HS). split; [| exact HS].
  destruct HA0 as (_ & _ & _ & _ & _ & OW0). rewrite EO in OW0. destruct OW0 as (_ & _ & _ & _ & RO).
  split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5|].
  rewrite EO. split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [exact D4| exact RO].
Qed.

(* [comment removed for export] *)
Lemma opnd_raw : ltac2:(CDefT.buildp (gd_tbl_MpiOpnd ()) "Psegs,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))PLB,(0.$4.)PSP,$15.Pd,$5.P,(34.R5.R4.R3.R2.R1.)P,P,(=.$>.(?.R2.)$19.)(25.=(11.R3.))(1=.(1?.R7.R6.(;.R3.)(35.$36.(37.(21.&40.(11.R3.)))(35.$36.(38.(21.&40.(22.R3.)))(35.$36.(38.(21.&40.(13.R3.)))(35.$36.(39.(23.R3.))(3:.$36.))))))(1=.(2;.R7.R6.(11.R3.)(2<.(28.R3.)))(1=.(=.$15.(26.(27.(2.&40.)(28.R3.)))(13.R3.))(1=.(1=.(29.=(13.R3.))(29.(13.R3.)+2710.))(1=.(2?.(=.$15.(22.R3.)+1.)(=.$15.(22.R3.)-1.))(1=.(1=.(29.=(;.R3.))(29.(2=.(;.R3.)+10.)(2>.+2.+40.)))(2?.(=.$15.(13.R3.)=)(1=.(25.=(11.R3.))(=.$15.(24.(11.R3.)+4.)=)))))))))")
(* [comment removed for export] *).
Proof.
  intros segs m LB SP d HA PNZ. pose proof (opnd_view _ _ _ _ _ HA) as [(HR & HAL & HPOS & HL & HN & HO) HS]. unfold MPI_MAX_LIMBS in HN.
  unfold mpi_cells in HR.
  pose proof (rw_cells_bound _ _ _ _ HR) as B. cbn [cells_size csize Nat.add] in B.
  split; [exact HR|].
  assert (K : bytes_at segs m (md_p d) (u32s (md_limbs d)) /\ (md_n d = 0 \/ 0 < md_p d /\ md_p d mod 4 = 0)).
  { destruct (md_own d) eqn:EO.
    - destruct HO as [HP HN0]. rewrite HP. assert (md_limbs d = []) as -> by (destruct (md_limbs d); [reflexivity| cbn in HL; lia]).
      split; [| left; exact HN0]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
    - destruct HO as (N1 & PIN & PAL & [HB _]). split; [exact HB| right]. split; [exact (PNZ eq_refl)|].
      apply Z.mod_divide in PAL; [| lia]. apply Z.mod_divide; [lia|]. destruct PAL as [k E]. exists (4 * k). lia.
    - destruct HO as (N1 & PAL & PP & HB & _). split; [exact HB| right; split; [exact PP| exact PAL]]. }
  destruct K as [K1 K2]. split; [exact K1|]. split; [exact HL|]. split; [lia|]. split; [exact HS|]. split; [lia| exact K2].
Qed.

(* [comment removed for export] *)
Definition mpi_binop_stmt' (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY MSF STACK : Z)
    (R : list blk -> mpd -> mpd -> mpd -> Z -> mpd -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_MpiOpnd ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(3;.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$3<.Ph,(3=.O7.O6.O5.)PLB,(0.$4.)PdX,$5.PdA,$5.PdB,$5.Plo,$15.P,(3>.O7.O6.O5.R6.R5.R8.R7.)P,(7.O7.R9.R6.R5.)P,(34.O7.R:.R7.(3?.&40.R2:.)R5.)P,(34.O7.R;.R8.(3?.&40.R2;.)R5.)P,(40.R8.R7.)P,(40.R9.R7.)P,(40.R9.R8.)P,(<.(=.$>.(?.R;.)$1>.))P,(41.R<.R;.R9.(3?.&40.R30.))P,(41.R=.R;.R:.(3?.&40.R31.))P,(18.O6.R?.R;.(;.R=.)+10.)P,P,(=.$>.(?.R>.)$19.)(18.O6.R11.R=.(11.R?.)(12.+4.(13.R?.)))P,(18.O6.R11.R=.(;.R>.)+10.)P,P,(=.$>.(?.R?.)$19.)(18.O6.R13.R?.(11.R10.)(12.+4.(13.R10.)))P,(42.O6.R13.(3?.&40.R36.)(43.O7.O6.O5.R14.)R12.)P,P,(<.(=.$>.(?.R13.)$10.))(2?.(29.(2=.(11.R14.)(12.+4.(13.R14.)))R11.)(29.(3?.&40.R38.)(11.R14.)))P,(44.O7.R18.R11.(3?.&40.R38.))P,(29.R12.(45.(45.(3?.&40.R39.)O2.)(46.O6.)))P,(29.(47.O6.)R13.)P,(29.(3?.&40.R3;.)(43.O7.O6.O5.R19.))P,(=.$15.(24.(3?.&40.R3<.)+10.)=)P,(29.(48.O6.)(47.O6.))P,(=.(2.&40.)R3<.(21.&40.(49.O6.)))P,(17.O7.R1?.)P,(4:.O7.O6.R20.)P,(4;.O6.O3.+8.)P,(=.(2.&40.)R3:.(21.&40.(;.R1>.)))P,(=.(2.&40.)R3:.(21.&40.(;.R1>.)))P,(=.(2.&40.)R3:.(21.&40.(;.R1>.)))(4<.O7.R24.(4=.O7.O6.O5.R46.R45.R44.R43.R3?.R3>.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R27.R26.R23.R22.R21.A4.O1.R22.R21.R20.R1?.R1>.R25.R24.)(4>.(4?.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.)R27.(21.&40.O4.)R26.(50.(2.&40.))R25.(51.O7.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition mpi_binop_stmtB' (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY MSF STACK : Z)
    (R : list blk -> mpd -> mpd -> mpd -> Z -> mpd -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_MpiOpnd ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(3;.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$3<.Ph,(3=.O7.O6.O5.)PLB,(0.$4.)PdX,$5.PdA,$5.PdB,$5.Plo,$15.P,(3>.O7.O6.O5.R6.R5.R8.R7.)P,(7.O7.R9.R6.R5.)P,(7.O7.R:.R7.R5.)P,(34.O7.R;.R8.(3?.&40.R2;.)R5.)P,(40.R8.R7.)P,(40.R9.R7.)P,(40.R9.R8.)P,(<.(=.$>.(?.R;.)$1>.))P,(41.R<.R;.R9.(3?.&40.R30.))P,(41.R=.R;.R:.(3?.&40.R31.))P,(18.O6.R?.R;.(;.R=.)+10.)P,P,(=.$>.(?.R>.)$19.)(18.O6.R11.R=.(11.R?.)(12.+4.(13.R?.)))P,(18.O6.R11.R=.(;.R>.)+10.)P,P,(=.$>.(?.R?.)$19.)(18.O6.R13.R?.(11.R10.)(12.+4.(13.R10.)))P,(42.O6.R13.(3?.&40.R36.)(43.O7.O6.O5.R14.)R12.)P,P,(<.(=.$>.(?.R13.)$10.))(2?.(29.(2=.(11.R14.)(12.+4.(13.R14.)))R11.)(29.(3?.&40.R38.)(11.R14.)))P,(44.O7.R18.R11.(3?.&40.R38.))P,(29.R12.(45.(45.(3?.&40.R39.)O2.)(46.O6.)))P,(29.(47.O6.)R13.)P,(29.(3?.&40.R3;.)(43.O7.O6.O5.R19.))P,(=.$15.(24.(3?.&40.R3<.)+10.)=)P,(29.(48.O6.)(47.O6.))P,(=.(2.&40.)R3<.(21.&40.(49.O6.)))P,(17.O7.R1?.)P,(4:.O7.O6.R20.)P,(4;.O6.O3.+8.)P,(=.(2.&40.)R3:.(21.&40.(;.R1>.)))P,(=.(2.&40.)R3:.(21.&40.(;.R1>.)))P,(=.(2.&40.)R3:.(21.&40.(;.R1>.)))(4<.O7.R24.(4=.O7.O6.O5.R46.R45.R44.R43.R3?.R3>.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R27.R26.R23.R22.R21.A4.O1.R22.R21.R20.R1?.R1>.R25.R24.)(4>.(4?.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.)R27.(21.&40.O4.)R26.(50.(2.&40.))R25.(51.O7.)))")
(* [comment removed for export] *).

Lemma mpi_binop_stmtB_of_prime : ltac2:(CDefT.buildp (gd_tbl_MpiOpnd ()) "Psegs,(0.$1.)PL,$14.PHI,(52.R2.R1.)PENTRY,$15.PMSF,$15.PSTACK,$15.PR,P,(0.$4.)P,$5.P,$5.P,$5.P,$15.P,$5.SpP,(53.R7.R6.R5.R4.R3.R2.R1.)(54.R8.R7.R6.R5.R4.R3.R2.)")
(* [comment removed for export] *).
Proof.
  intros segs L HI ENTRY MSF STACK R H. unfold mpi_binop_stmtB'. intros. eapply H; try eassumption; apply opnd_at_mpd; assumption.
Qed.

Lemma mpi_binop_stmt_of_primeB : ltac2:(CDefT.buildp (gd_tbl_MpiOpnd ()) "Psegs,(0.$1.)PL,$14.PHI,(52.R2.R1.)PENTRY,$15.PMSF,$15.PSTACK,$15.PR,P,(0.$4.)P,$5.P,$5.P,$5.P,$15.P,$5.SpP,(54.R7.R6.R5.R4.R3.R2.R1.)(55.R8.R7.R6.R5.R4.R3.R2.)")
(* [comment removed for export] *).
Proof.
  intros segs L HI ENTRY MSF STACK R H. unfold mpi_binop_stmt. intros. eapply H; try eassumption; apply opnd_at_mpd; assumption.
Qed.

Lemma mpi_binop_stmt_of_prime : ltac2:(CDefT.buildp (gd_tbl_MpiOpnd ()) "Psegs,(0.$1.)PL,$14.PHI,(52.R2.R1.)PENTRY,$15.PMSF,$15.PSTACK,$15.PR,P,(0.$4.)P,$5.P,$5.P,$5.P,$15.P,$5.SpP,(53.R7.R6.R5.R4.R3.R2.R1.)(55.R8.R7.R6.R5.R4.R3.R2.)")
(* [comment removed for export] *).
Proof.
  intros segs L HI ENTRY MSF STACK R H. unfold mpi_binop_stmt. intros. eapply H; try eassumption; apply opnd_at_mpd; assumption.
Qed.

Definition mpi_add_abs_stmt' segs L HI ENTRY MSF := mpi_binop_stmtB' segs L HI ENTRY MSF MPI_ADD_ABS_STACK add_abs_R.
Definition mpi_sub_abs_stmt' segs L HI ENTRY MSF := mpi_binop_stmt' segs L HI ENTRY MSF MPI_SUB_ABS_STACK sub_abs_R.
