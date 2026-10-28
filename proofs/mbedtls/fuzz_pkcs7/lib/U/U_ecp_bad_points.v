(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux MpiCoreAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal RepEcp EcpCurves EcpLoad EcpFacts EcpPkGlue.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_ecp_check_pubkey.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_ecp_bad_points () : Init.string Init.list := ["Corelib.Lists.ListDef.map"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_layout"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_check_pubkey.U_BAD_POINTS"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_check_pubkey.bad_point_ok"; "U_bp1"; "Stdlib.ZArith.BinInt.Z.add"; "U_bp2"].


Lemma const_at_sub' : forall L A n a k, const_at L A n -> A <= a -> a + k <= A + n -> const_at L a k.
Proof. (intros L A n a k dd_H; ddestruct dd_H as (H1 & H2 & H3); intros Ha Hk). split; [lia|]. split; [lia|]. intros x Hx. apply H3. lia. Qed.

Definition bad1_limbs : list word := ltac2:(CDefT.buildp (gd_tbl_P_ecp_bad_points ()) "(0.$1.(2.&40.)(3.&40.)(4.$1.+7<7:>;>0.(4.$1.+:>;8413;.(4.$1.+?:>35616.(4.$1.+6:<49??1.(4.$1.+>;8=09=:.(4.$1.+?=;1329<.(4.$1.+16056286.(4.$1.+;8495?.(5.$1.))))))))))")
(* [comment removed for export] *).
Definition bad2_limbs : list word := ltac2:(CDefT.buildp (gd_tbl_P_ecp_bad_points ()) "(0.$1.(2.&40.)(3.&40.)(4.$1.+;<959<5?.(4.$1.+248<50:3.(4.$1.+55;1=0;1.(4.$1.+5;>?839<.(4.$1.+<45<4404.(4.$1.+868>1<58.(4.$1.+==4>22=8.(4.$1.+57119?=0.(5.$1.))))))))))")
(* [comment removed for export] *).
Definition U_BAD1_LIMBS : Z := 0x112b0.
Definition U_BAD2_LIMBS : Z := 0x112d0.
Definition U_bp1 : mpd := smpd U_BAD_POINTS U_BAD1_LIMBS bad1_limbs (Z_to_bv 64 0).
Definition U_bp2 : mpd := smpd (U_BAD_POINTS + 16) U_BAD2_LIMBS bad2_limbs (Z_to_bv 64 0).

Lemma U_bad_points_ok : ltac2:(CDefT.buildp (gd_tbl_P_ecp_bad_points ()) "PL,$6.PLB,(7.$8.)Pm,P,(2.&40.)(9.(2.&8.))P,(:.$;.R3.R1.)P,(<.R4.$=.+20.)P,(>.$;.R3.)(?.(10.$;.R4.R5.$=.$11.)(10.$;.R4.R5.(12.$=.+10.)$13.))")
(* [comment removed for export] *).
Proof.
  intros L LB m SOK CA MI. unfold U_bp1, U_bp2, U_BAD1_LIMBS, U_BAD2_LIMBS, U_BAD_POINTS in *.
  assert (S1 : static_limbs usegs m 0x112b0 bad1_limbs) by (apply static_limbs_image; [exact MI| vm_compute; reflexivity| reflexivity| reflexivity| vm_compute; discriminate| cbn; lia]).
  assert (S2 : static_limbs usegs m 0x112d0 bad2_limbs) by (apply static_limbs_image; [exact MI| vm_compute; reflexivity| reflexivity| reflexivity| vm_compute; discriminate| cbn; lia]).
  set (bs1 := map (Z_to_bv 8) [0xb0; 0x12; 1; 0; 0; 0; 0; 0; 1; 0; 8; 0; 0; 0; 0; 0]).
  set (bs2 := map (Z_to_bv 8) [0xd0; 0x12; 1; 0; 0; 0; 0; 0; 1; 0; 8; 0; 0; 0; 0; 0]).
  assert (C1 : rw_cells usegs m 0x48f20 [CB 16 bs1]).
  { apply (rw_cells_img usegs L); [exact SOK| eapply const_at_sub'; [exact CA| cbn; lia| cbn; lia]| vm_compute; reflexivity| vm_compute; reflexivity| cbn; lia]. }
  assert (C2 : rw_cells usegs m (0x48f20 + 16) [CB 16 bs2]).
  { apply (rw_cells_img usegs L); [exact SOK| eapply const_at_sub'; [exact CA| cbn; lia| cbn; lia]| vm_compute; reflexivity| vm_compute; reflexivity| cbn; lia]. }
  apply mpi_cells_of_bytes in C1. apply mpi_cells_of_bytes in C2.
  match type of C1 with rw_cells _ _ _ ?c => let c' := eval vm_compute in c in change c with c' in C1 end.
  match type of C2 with rw_cells _ _ _ ?c => let c' := eval vm_compute in c in change c with c' in C2 end.
  split.
  - split; [| split; [reflexivity| split; reflexivity]]. split; [| left; reflexivity].
    apply smpd_at; [| reflexivity| reflexivity| exact S1].
    match goal with |- rw_cells _ _ _ ?c => let c' := eval vm_compute in c in change c with c' end. exact C1.
  - split; [| split; [reflexivity| split; reflexivity]]. split; [| left; reflexivity].
    apply smpd_at; [| reflexivity| reflexivity| exact S2].
    match goal with |- rw_cells _ _ _ ?c => let c' := eval vm_compute in c in change c with c' end. exact C2.
Qed.
