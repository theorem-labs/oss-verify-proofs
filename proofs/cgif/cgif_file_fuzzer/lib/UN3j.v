(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI06 YI16 YI14 YI07 UI5b UI5c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section b.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[global] Instance ubs0_sys_laws : sys_laws ubs0_msyms.
Proof using.
constructor.
- intros a Ha. exact (skl_errno ubs0_msyms a Ha).
- intros a Ha. destruct (skl_env ubs0_msyms a (or_introl Ha)) as (H1 & H2 & H3 & _). auto.
Qed.
End b.
