(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0d.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YH00 YH03 YH02.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI06 YI16 YI14 YI07 YI5b YI5c.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section b.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[global] Instance src0_sys_laws : sys_laws src0_msyms.
Proof.
constructor.
- intros a Ha. exact (skl_errno src0_msyms a Ha).
- intros a Ha. destruct (skl_env src0_msyms a (or_introl Ha)) as (H1 & H2 & H3 & _). auto.
Qed.
End b.
