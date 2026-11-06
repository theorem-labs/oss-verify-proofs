(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.mbedtls.fuzz_pkcs7.images Require Import Asan.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AImg () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.LibA.ALazy.al_got"; "OSSVerify.KrLib.LibA.ALazy.al_img_lo"; "OSSVerify.KrLib.LibA.ALazy.al_img_hi"; "OSSVerify.KrLib.LibA.ALazy.al_gsb"].

Definition asegs : list Segment := Asan.M.loaded_segments.

From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require ALazy.
(* [comment removed for export] *)
Definition asan_img_ok (AL : ALazy.asan_layout) : Prop := ltac2:(CDefT.buildp (gd_tbl_AImg ()) "(0.(1.$2.(3.O1.)+?2:90.)(0.(1.$2.(4.O1.)+10000.)(0.(1.$2.(5.O1.)+65;000.)(1.$2.(6.O1.)+1065?8.))))")
(* [comment removed for export] *).   (* [comment removed for export] *)
