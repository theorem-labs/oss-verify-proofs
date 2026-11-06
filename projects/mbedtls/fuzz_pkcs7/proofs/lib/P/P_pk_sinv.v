(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk CellsX HeapIface Asn1Aux Statics AStep.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import StreamSim StoreOk.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import SInv.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_layout P_ecp_grp_id_list P_ecp_sinv.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_pk_sinv () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_lo"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_hi"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.Lib.HeapIface.hl_written"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.Lib.HeapIface.hl_static"; "OSSVerify.KrLib.P.P_ecp_grp_id_list.ecp_ids_state"; "OSSVerify.KrLib.P.PImg.psegs"; "OSSVerify.KrLib.P.P_ecp_grp_id_list.P_ECP_IDS_DONE"; "OSSVerify.KrLib.P.P_ecp_grp_id_list.P_ECP_IDS"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"].


Notation P_MUL_COUNT := 366760 (only parsing).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition mc_lok (L : heap_layout) (MC : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_pk_sinv ()) "(0.(1.(2.O2.)O1.)(0.(1.(3.O1.+8.)(4.O2.))Pa,$5.P,(0.(1.O1.R1.)(6.R1.(3.O1.+8.)))(0.(7.O2.R2.)(8.(9.O2.R2.)))))")
(* [comment removed for export] *).

Lemma P_mc_lok sp0 : mc_lok (P_layout sp0) P_MUL_COUNT.
Proof.
  unfold mc_lok. cbn -[Z.add Z.le Z.lt]. unfold P_written, P_static. repeat split; try lia.
Qed.

Definition pk_sinv_P (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_pk_sinv ()) "(0.(:.$;.$<.$=.O1.)(>.(?.&40.)Lcnt,(?.&40.)(10.$;.O1.+598:8.(11.$12.(13.R1.)(14.$12.)))))")
(* [comment removed for export] *).

Section Inst.
  Variable L : heap_layout.
  Hypothesis HL : ecp_ids_lok L P_ECP_IDS_DONE P_ECP_IDS.
  Hypothesis HM : mc_lok L P_MUL_COUNT.

  Definition P_pk_sinv : sinv L.
  Proof.
    refine (mkSI L pk_sinv_P
                  [(P_ECP_IDS_DONE, P_ECP_IDS_DONE + 1); (P_MUL_COUNT, P_MUL_COUNT + 8); (P_ECP_IDS, P_ECP_IDS + 56)] _ _ _ _).
    - (* [comment removed for export] *)
      (intros m m' dd_H; ddestruct dd_H as [(b & bs & R1 & R2 & IMP) (cnt & RC)]; intros AG). split; [dexists b, bs; split; [| split; [| exact IMP]]| exists cnt].
      + eapply rw_cells_agree'; [exact R1|]. cbn [cells_size csize Nat.add]. intros a Ha. apply AG; [unfold P_ECP_IDS_DONE in Ha; lia|].
        cbn. intros [H _]. apply H. lia.
      + pose proof R2 as [[WF _] _]. cbn in WF. destruct WF as [LEN _].
        eapply rw_cells_agree'; [exact R2|]. cbn [cells_size csize Nat.add]. intros a Ha. apply AG; [unfold P_ECP_IDS in Ha; lia|].
        cbn. (intros dd_H; ddestruct dd_H as (_ & _ & H & _)). apply H. lia.
      + eapply rw_cells_agree'; [exact RC|]. cbn [cells_size csize Nat.add]. intros a Ha. apply AG; [lia|].
        cbn. (intros dd_H; ddestruct dd_H as (_ & H & _)). apply H. lia.
    - (* [comment removed for export] *)
      intros m NONE. split; [dexists (Z_to_bv 8 0), (repeat (Z_to_bv 8 0) 56); split; [| split]| exists (Z_to_bv 64 0)].
      + apply (P_data_rw_cells m P_ECP_IDS_DONE [Z_to_bv 8 0]); [vm_compute; reflexivity| unfold P_ECP_IDS_DONE; lia| unfold P_ECP_IDS_DONE; cbn; lia|].
        intros a Ha. apply NONE; [unfold P_ECP_IDS_DONE in Ha; cbn in Ha; lia|]. cbn. intros [H _]. apply H. cbn in Ha. lia.
      + apply (P_data_rw_cells m P_ECP_IDS (repeat (Z_to_bv 8 0) 56)); [vm_compute; reflexivity| unfold P_ECP_IDS; lia| unfold P_ECP_IDS; cbn; lia|].
        intros a Ha. apply NONE; [unfold P_ECP_IDS in Ha; cbn in Ha; lia|]. cbn. (intros dd_H; ddestruct dd_H as (_ & _ & H & _)). apply H. cbn in Ha. lia.
      + intros NZ. exfalso. apply NZ. reflexivity.
      + pose proof (P_data_rw_cells m P_MUL_COUNT (repeat (Z_to_bv 8 0) 8) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)
                      ltac:(intros a Ha; apply NONE; [cbn in Ha; lia|]; cbn; (intros dd_H; ddestruct dd_H as (_ & H & _)); apply H; cbn in Ha; lia)) as R.
        cbn [length repeat] in R. cb8_to_c8 R ([] : list cell).
        replace (le_bytes_to_word (repeat (Z_to_bv 8 0) 8)) with (Z_to_bv 64 0) in R by (vm_compute; reflexivity). exact R.
    - (* [comment removed for export] *)
      intros a NO. ddestruct HL as (D1 & D2 & D3 & D4). ddestruct HM as (M1 & M2 & M3). cbn in NO.
      assert (IN : (P_ECP_IDS_DONE <= a < P_ECP_IDS_DONE + 1 \/ P_ECP_IDS <= a < P_ECP_IDS + 56) \/ P_MUL_COUNT <= a < P_MUL_COUNT + 8)
        by (clear -NO; unfold P_ECP_IDS_DONE, P_ECP_IDS in *; lia).
      destruct IN as [IN|IN]; [destruct (D4 a IN) as [W NS]| destruct (M3 a IN) as [W NS]]; (split; [unfold P_ECP_IDS_DONE, P_ECP_IDS in *; lia| split; [exact W| exact NS]]).
    - (* [comment removed for export] *)
      repeat constructor; cbn; lia.
  Defined.
End Inst.
