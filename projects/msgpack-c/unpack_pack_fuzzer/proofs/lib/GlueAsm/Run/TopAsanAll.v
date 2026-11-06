(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Asan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Img Require Import ImgSrc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Top Require Import TopUbs TopLib TopSrc31.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import DrvShape.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require MainEntry SpinAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require TopLevelGen.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require TopLevel.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AImg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require RzBridge AsanRun AsanImgx AsanDrun AsanAcct AcctPlug.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Acct.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.AsanU Require UnivAsan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2F Require T_Asan2F.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2L Require T_Asan2L.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.LibRun Require Asan_r12.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueAsm.Run Require MainAsan G0Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module TopAsanAll.
Import TopUbs.
Module TG := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.TopLevelGen.
Module ME := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.MainEntry.
Module AI := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg.
Module MA := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueAsm.Run.MainAsan.

Definition ASAN_SEGS := AI.asegs.
Definition ASAN_PC := AI.a_init_pc.
Definition ASAN_PH := AI.a_phdrs.
Definition ASAN : Image := mkImage ASAN_SEGS ASAN_PC ASAN_PH.

Section G0.

Let G0 : MA.G0_stmt := G0Asan.G0.

Let MAIN := MA.MAIN G0.

Theorem asan_base1 :
  strong_universal_error_free_T_scfg_budgets_abort (mkSpuriousCfg false true true true true true)
    SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage SRC_SEGS SRC_PC SRC_PH) (mkImage AI.asegs AI.a_init_pc AI.a_phdrs).
Proof. exact (TopSrc31.TopSrc31.asan_base_of_main MAIN). Qed.
End G0.
End TopAsanAll.
