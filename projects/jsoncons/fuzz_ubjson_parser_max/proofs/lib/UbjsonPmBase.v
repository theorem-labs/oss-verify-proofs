(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import State Run MemImageType.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import UbjsonPmFinal UbjsonPmPkgs UbjsonPmRows.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition ubjson_pm_ubsan_base := UbjsonPmRows.ubjson_pm_ubsan_base packages_src packages_ub.
Definition ubjson_pm_ubsan_base_abort := UbjsonPmRows.ubjson_pm_ubsan_base_abort packages_src packages_ub.
