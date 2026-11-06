(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux MpiCoreAux HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal RepEcp EcpCurves EcpLoad EcpFacts EcpPkGlue.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_ecp_check_pubkey.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_ecp_bad_points () : Init.string Init.list := ["Corelib.Lists.ListDef.map"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.HeapIface.heap_layout"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.Lib.AStep.statics_ok"; "OSSVerify.KrLib.P.PImg.psegs"; "OSSVerify.KrLib.Lib.AStep.const_at"; "OSSVerify.KrLib.P.P_ecp_check_pubkey.P_BAD_POINTS"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "Corelib.Init.Logic.and"; "OSSVerify.KrLib.P.P_ecp_check_pubkey.bad_point_ok"; "P_bp1"; "Stdlib.ZArith.BinInt.Z.add"; "P_bp2"].


Lemma const_at_sub' : forall L A n a k, const_at L A n -> A <= a -> a + k <= A + n -> const_at L a k.
Proof. (intros L A n a k dd_H; ddestruct dd_H as (H1 & H2 & H3); intros Ha Hk). split; [lia|]. split; [lia|]. intros x Hx. apply H3. lia. Qed.

Definition bad1_limbs : list word := ltac2:(CDefT.buildp (gd_tbl_P_ecp_bad_points ()) "(0.$1.(2.&40.)(3.&40.)(4.$1.+7<7:>;>0.(4.$1.+:>;8413;.(4.$1.+?:>35616.(4.$1.+6:<49??1.(4.$1.+>;8=09=:.(4.$1.+?=;1329<.(4.$1.+16056286.(4.$1.+;8495?.(5.$1.))))))))))")
(* [comment removed for export] *).
Definition bad2_limbs : list word := ltac2:(CDefT.buildp (gd_tbl_P_ecp_bad_points ()) "(0.$1.(2.&40.)(3.&40.)(4.$1.+;<959<5?.(4.$1.+248<50:3.(4.$1.+55;1=0;1.(4.$1.+5;>?839<.(4.$1.+<45<4404.(4.$1.+868>1<58.(4.$1.+==4>22=8.(4.$1.+57119?=0.(5.$1.))))))))))")
(* [comment removed for export] *).
Definition P_BAD1_LIMBS : Z := 0x112a0.
Definition P_BAD2_LIMBS : Z := 0x112c0.
Definition P_bp1 : mpd := smpd P_BAD_POINTS P_BAD1_LIMBS bad1_limbs (Z_to_bv 64 0).
Definition P_bp2 : mpd := smpd (P_BAD_POINTS + 16) P_BAD2_LIMBS bad2_limbs (Z_to_bv 64 0).

Lemma P_bad_points_ok : ltac2:(CDefT.buildp (gd_tbl_P_ecp_bad_points ()) "PL,$6.PLB,(7.$8.)Pm,P,(2.&40.)(9.(2.&8.))P,(:.$;.R3.R1.)P,(<.R4.$=.+20.)P,(>.$;.R3.)(?.(10.$;.R4.R5.$=.$11.)(10.$;.R4.R5.(12.$=.+10.)$13.))")
(* [comment removed for export] *).
Proof.
  intros L LB m SOK CA MI. unfold P_bp1, P_bp2, P_BAD1_LIMBS, P_BAD2_LIMBS, P_BAD_POINTS in *.
  assert (S1 : static_limbs psegs m 0x112a0 bad1_limbs) by (apply static_limbs_image; [exact MI| vm_compute; reflexivity| reflexivity| reflexivity| vm_compute; discriminate| cbn; lia]).
  assert (S2 : static_limbs psegs m 0x112c0 bad2_limbs) by (apply static_limbs_image; [exact MI| vm_compute; reflexivity| reflexivity| reflexivity| vm_compute; discriminate| cbn; lia]).
  set (bs1 := map (Z_to_bv 8) [0xa0; 0x12; 1; 0; 0; 0; 0; 0; 1; 0; 8; 0; 0; 0; 0; 0]).
  set (bs2 := map (Z_to_bv 8) [0xc0; 0x12; 1; 0; 0; 0; 0; 0; 1; 0; 8; 0; 0; 0; 0; 0]).
  assert (C1 : rw_cells psegs m 0x45828 [CB 16 bs1]).
  { apply (rw_cells_img psegs L); [exact SOK| eapply const_at_sub'; [exact CA| cbn; lia| cbn; lia]| vm_compute; reflexivity| vm_compute; reflexivity| cbn; lia]. }
  assert (C2 : rw_cells psegs m (0x45828 + 16) [CB 16 bs2]).
  { apply (rw_cells_img psegs L); [exact SOK| eapply const_at_sub'; [exact CA| cbn; lia| cbn; lia]| vm_compute; reflexivity| vm_compute; reflexivity| cbn; lia]. }
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
