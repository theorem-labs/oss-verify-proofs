(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AImg () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_got"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_lo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_hi"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_gsb"].

Definition asegs : list Segment := AsanUbsan.M.loaded_segments.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require ALazy.
(* [comment removed for export] *)
Definition asan_img_ok (AL : ALazy.asan_layout) : Prop := ltac2:(CDefT.buildp (gd_tbl_AImg ()) "(0.(1.$2.(3.O1.)+?5>50.)(0.(1.$2.(4.O1.)+10000.)(0.(1.$2.(5.O1.)+65?000.)(1.$2.(6.O1.)+1099?8.))))")
(* [comment removed for export] *).   (* [comment removed for export] *)
