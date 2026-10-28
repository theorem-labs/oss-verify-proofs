(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX SysStep ITree Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv AKinvS AW_Unwind AW_Unwind2 AW_MmapFixed AW_Poison.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_CfgS AW_Populate AW_EmbCfg.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AW_B12Walk () : Init.string Init.list := ["Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.BHeap.AKinv.kinv"; "Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.le"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_lo"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_hi"; "Corelib.Init.Logic.not"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kEmbBytes"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.anon_grant"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.AHeap.ASysS.anon_grantable"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_EmbCfg.emb_wf"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.asan_layout"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.al_wf"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "ARUN_1.b12_laws"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_EmbCfg.b12_siteS"].


Section ARUN_1. Context {hAR : arun}.

Section Laws.
  Variable AL : asan_layout.
  Variables (CS00 : Z -> Prop) (K00 : Model -> Prop) (CSx : Z -> Z -> Prop) (Kx : Z -> Model -> Prop).
  Variables (EP EB ECAP ESZ : Z).

  (* [comment removed for export] *)
  Definition b12_laws : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_B12Walk ()) "(0.(1.VAL,VCS00,)(0.(2.VhAR,VAL,VCS00,VK00,)(0.Pa,$3.(1.VAL,A1.VCSx,R1.)(0.Pa,$3.(2.VhAR,VAL,A1.VCSx,R1.A1.VKx,R1.)(0.Pa,$3.Py,$3.P,A1.VCS00,R1.A2.VCSx,R3.R2.(0.Pmo,$4.Pa,(5.&40.)Pn,(5.&40.)P,A1.VK00,R3.P,(6.$7.(8.(9.(:.(5.&40.)(5.&40.))(;.(<.R4.))(=.(<.R4.)))R3.R2.)$>.)P,(?.+10000.(10.&40.R3.))P,(?.(11.(10.&40.R5.)(10.&40.R4.))(12.VhAR,))Px,$3.P,(13.A1.VCS00,R1.(0.(?.(14.VAL,)R1.)(15.R1.(16.VAL,))))(17.(0.(?.(10.&40.R8.)R2.)(15.R2.(11.(10.&40.R8.)(10.&40.R7.)))))(0.Pmo,$4.Pa,(5.&40.)P,(6.$3.VEB,=)P,A1.VK00,R3.P,(6.$3.(18.(10.&40.R3.)+1000.)=)P,(15.=(10.&40.R4.))P,(?.(11.(10.&40.R5.)$19.)(12.VhAR,))P,(6.$7.(8.(9.(:.(5.&40.)(5.&40.))(;.(<.R7.))(=.(<.R7.)))R6.(1:.&40.$19.))$>.)(0.A2.VKx,(10.&40.R7.)(1;.+22.R7.$19.R8.)(0.(1<.A1.VCSx,(10.&40.R7.)(10.&40.R7.)$19.)(0.(?.+65?000.(10.&40.R7.))(13.(?.(11.(10.&40.R7.)$19.)+7???7000.)(?.+10007???8000.(10.&40.R7.))))))(0.Pmo,$4.P,(6.$3.VEB,=)P,A1.VK00,R2.(1=.(5.&40.)La,(5.&40.)(1>.VhAR,+22.$19.R4.R1.))(0.P,(17.(6.$3.VEB,=))(1<.VCS00,VEB,$19.)(0.(1?.VEP,VEB,VECAP,VESZ,)P,(17.(6.$3.VEB,=))(0.(?.+65?000.VEB,)(?.(11.VEB,$19.)(12.VhAR,)))))))))))))")
(* [comment removed for export] *).
End Laws.

(* [comment removed for export] *)
Definition b12_walk_T : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_B12Walk ()) "PAL,$20.P,(21.R1.)P,(22.R2.)P,(6.$3.(23.R3.)+7???8000.)PCS00,P,$3.SpPK00,P,$4.SpPCSx,P,$3.P,$3.SpPKx,P,$3.P,$4.SpPEP,$3.PEB,$3.PECAP,$3.PESZ,$3.P,(24.R<.R8.R7.R6.R5.R4.R3.R2.R1.)(25.VhAR,R9.R8.R6.R5.R4.R3.R2.)")
(* [comment removed for export] *).

End ARUN_1.
