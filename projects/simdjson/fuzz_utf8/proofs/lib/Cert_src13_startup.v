(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec AxSymExec3 AsanPlan. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import AsanNodesIO AsanMainLib ImgParams MainDefs Img_src13.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import Cert_common ITab_src13 Plan_src13_startup HS_src13_startup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition SH_src13_startup : shape := SHole 0.
Definition FUEL_src13_startup : nat := 3000.
Lemma cert_src13_startup : startup_check IP_src13 ITm_src13 FUEL_src13_startup HS_src13_startup plan_src13_startup = COk SH_src13_startup.
Proof. cert_vm (COk SH_src13_startup). Qed.
