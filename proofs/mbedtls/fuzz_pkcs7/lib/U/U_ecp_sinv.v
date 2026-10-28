(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk CellsX HeapIface Asn1Aux Statics AStep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import StreamSim StoreOk.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import SInv.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_layout U_ecp_grp_id_list.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_ecp_sinv () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_written"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_static"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Lib.Statics.img_bytes_b"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Corelib.Init.Datatypes.nil"].


(* [comment removed for export] *)
Definition ecp_ids_lok (L : heap_layout) (IDONE IDS : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_sinv ()) "(0.(1.(2.O3.)O2.)(0.(1.(3.O2.+1.)O1.)(0.(1.(3.O1.+38.)(4.O3.))Pa,$5.P,(6.(0.(1.O2.R1.)(7.R1.(3.O2.+1.)))(0.(1.O1.R1.)(7.R1.(3.O1.+38.))))(0.(8.O3.R2.)(9.(:.O3.R2.))))))")
(* [comment removed for export] *).

Lemma U_ecp_ids_lok sp0 : ecp_ids_lok (U_layout sp0) U_ECP_IDS_DONE U_ECP_IDS.
Proof.
  unfold ecp_ids_lok, U_ECP_IDS_DONE, U_ECP_IDS. cbn -[Z.add Z.le Z.lt]. unfold U_written, U_static.
  repeat split; try lia.
Qed.

(* [comment removed for export] *)
Section Agree.
  Variable segs : list Segment.
  Let agree_on (m m' : mem) (A n : Z) : Prop := forall a, A <= a < A + n -> m' (wa a) = m (wa a).
  #[using="Type"] Lemma rw_cells_agree' : ltac2:(CDefT.buildp (gd_tbl_P_ecp_sinv ()) "Pm,P,(;.&40.)(<.(;.&8.))Pm',P,(;.&40.)(<.(;.&8.))PA,$5.Pcs,(=.$>.)P,(?.Vsegs,R4.R2.R1.)P,A4.Vagree_on,R5.R4.R3.(10.(11.R2.))(?.Vsegs,R5.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros m m' A cs [[Hwf Hb] Hw] AG. split; [split; [exact Hwf|]|].
    - ddestruct Hb as (H0 & H1 & H). split; [exact H0|]. split; [exact H1|]. intros i Hi.
      rewrite <- (H i Hi). unfold mrd. rewrite (AG (A + Z.of_nat i)) by (rewrite cells_bytes_length in Hi by exact Hwf; lia). reflexivity.
    - ddestruct Hw as (H0 & H1 & H). split; [exact H0|]. split; [exact H1|]. intros i Hi.
      specialize (H i Hi). unfold wview in *. rewrite (AG (A + i)) by lia. exact H.
  Qed.
End Agree.

(* [comment removed for export] *)
Lemma U_wseg_49 : wseg_ok usegs (Z_to_bv 64 0x5c000) 8192%nat = true.
Proof. vm_compute. reflexivity. Qed.

Lemma U_data_rw_cells : ltac2:(CDefT.buildp (gd_tbl_P_ecp_sinv ()) "Pm,Px,(;.&40.)(<.(;.&8.))PA,$5.Pbs,(=.(;.&8.))P,(12.$13.(14.$15.R2.R1.)$16.)P,(1.+5<000.R3.)P,(1.(3.R4.(10.(17.(;.&8.)R3.)))+5>000.)P,Pa,$5.P,(0.(1.R6.R1.)(7.R1.(3.R6.(10.(17.(;.&8.)R5.)))))(12.(<.(;.&8.))A1.R8.(18.R2.)(19.(;.&8.)))(?.$15.R7.R6.(1:.$>.(1;.(17.(;.&8.)R5.)R5.)(1<.$>.)))")
(* [comment removed for export] *).
Proof.
  intros m A bs IB LO HI NONE.
  pose proof (pristine_cells usegs A (A + Z.of_nat (length bs)) (fun _ => False) m A bs
                ltac:(split; [lia|]; split; [lia|]; intros a Ha _; exact (NONE a Ha)) IB ltac:(lia) ltac:(lia) ltac:(intros a _ F; exact F)) as [WF BA].
  split; [exact (conj WF BA)|]. cbn [cells_size csize Nat.add].
  split; [lia|]. split; [lia|]. intros i Hi.
  pose proof (store_ok_window usegs m (Z_to_bv 64 0x5c000) (Z_to_bv 64 A) 8192%nat (length bs) 0x5c000 0x5e000
                eq_refl eq_refl ltac:(lia) U_wseg_49 ltac:(rewrite unsigned_lit by lia; lia) ltac:(rewrite unsigned_lit by lia; lia)) as SOK.
  pose proof (store_ok_wview usegs m (Z_to_bv 64 A) (length bs) (Z.to_nat i) SOK ltac:(lia)) as W.
  rewrite unsigned_lit in W by lia. rewrite Z2Nat.id in W by lia. exact W.
Qed.

Section Inst.
  Variable L : heap_layout.
  Hypothesis HL : ecp_ids_lok L U_ECP_IDS_DONE U_ECP_IDS.

  Definition U_ecp_sinv : sinv L.
  Proof.
    refine (mkSI L (ecp_ids_state usegs U_ECP_IDS_DONE U_ECP_IDS)
                  [(U_ECP_IDS_DONE, U_ECP_IDS_DONE + 1); (U_ECP_IDS, U_ECP_IDS + 56)] _ _ _ _).
    - (* [comment removed for export] *)
      (intros m m' dd_H; ddestruct dd_H as (b & bs & R1 & R2 & IMP); intros AG). dexists b, bs. split; [| split; [| exact IMP]].
      + eapply rw_cells_agree'; [exact R1|]. cbn [cells_size csize Nat.add]. intros a Ha. apply AG; [unfold U_ECP_IDS_DONE in Ha; lia|].
        cbn. intros [H _]. apply H. lia.
      + pose proof R2 as [[WF _] _]. cbn in WF. destruct WF as [LEN _].
        eapply rw_cells_agree'; [exact R2|]. cbn [cells_size csize Nat.add]. intros a Ha. apply AG; [unfold U_ECP_IDS in Ha; lia|].
        cbn. (intros dd_H; ddestruct dd_H as (_ & H & _)). apply H. lia.
    - (* [comment removed for export] *)
      intros m NONE. dexists (Z_to_bv 8 0), (repeat (Z_to_bv 8 0) 56). split; [| split].
      + apply (U_data_rw_cells m U_ECP_IDS_DONE [Z_to_bv 8 0]); [vm_compute; reflexivity| unfold U_ECP_IDS_DONE; lia| unfold U_ECP_IDS_DONE; cbn; lia|].
        intros a Ha. apply NONE; [unfold U_ECP_IDS_DONE in Ha; cbn in Ha; lia|]. cbn. intros [H _]. apply H. cbn in Ha. lia.
      + apply (U_data_rw_cells m U_ECP_IDS (repeat (Z_to_bv 8 0) 56)); [vm_compute; reflexivity| unfold U_ECP_IDS; lia| unfold U_ECP_IDS; cbn; lia|].
        intros a Ha. apply NONE; [unfold U_ECP_IDS in Ha; cbn in Ha; lia|]. cbn. (intros dd_H; ddestruct dd_H as (_ & H & _)). apply H. cbn in Ha. lia.
      + intros NZ. exfalso. apply NZ. reflexivity.
    - (* [comment removed for export] *)
      intros a NO. ddestruct HL as (D1 & D2 & D3 & D4). cbn in NO.
      assert (IN : U_ECP_IDS_DONE <= a < U_ECP_IDS_DONE + 1 \/ U_ECP_IDS <= a < U_ECP_IDS + 56) by (clear -NO; unfold U_ECP_IDS_DONE, U_ECP_IDS in *; lia).
      destruct (D4 a IN) as [W NS]. split; [lia|]. split; [exact W| exact NS].
    - (* [comment removed for export] *)
      repeat constructor; cbn; lia.
  Defined.
End Inst.
