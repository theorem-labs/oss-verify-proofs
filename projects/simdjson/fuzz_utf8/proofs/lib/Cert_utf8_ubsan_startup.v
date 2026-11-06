(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec AxSymExec3 AsanPlan. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import AsanNodesIO AsanMainLib ImgParams MainDefs Img_utf8_ubsan.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import Cert_common ITab_utf8_ubsan Plan_utf8_ubsan_startup HS_utf8_ubsan_startup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition SH_utf8_ubsan_startup : shape := SHole 0.
Definition FUEL_utf8_ubsan_startup : nat := 3000.
Lemma cert_utf8_ubsan_startup : startup_check IP_utf8_ubsan ITm_utf8_ubsan FUEL_utf8_ubsan_startup HS_utf8_ubsan_startup plan_utf8_ubsan_startup = COk SH_utf8_ubsan_startup.
Proof. cert_vm (COk SH_utf8_ubsan_startup). Qed.
