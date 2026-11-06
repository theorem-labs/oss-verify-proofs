(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import NArith List ZArith Lia Bool.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import E_As0ui E_Top.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require DrvImzd.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require DrvImzd.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.DrvImzd.Allo10x OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.DrvImzd.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ACoreF4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ACoreF6 APopTop.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACoreF4.ACoreF3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACoreF6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopTop.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_Har9f.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yt Require Import E_Askyl.

Theorem asan_pinned : strong_universal_error_free_T_scfg (LinuxProcessSemantics.LinuxProcessSem.Run.alloc_only_cfg false) SRC0 ASANI.
Proof.
  exact (@asan_base (fun Clg => @AllocP0 Clg) (fun Clg => @DriverP0 Clg) (fun Clg => @E_Top.LIB0 Clg)
           (fun Clg => @pop_core_ok Clg)
           (fun Clg => @restF2_ok Clg) (fun Clg => @restF0_ok Clg)
           (fun Clg AI AI16 => @alib_call_ok_proved Clg AI AI16)).
Qed.

(* [comment removed for export] *)
Theorem asan_budgets :
  strong_universal_error_free_T_scfg_budgets (LinuxProcessSemantics.LinuxProcessSem.Run.alloc_only_cfg false) SanitizerBudgets.lim_source SanitizerBudgets.lim_target SRC0 ASANI.
Proof.
  exact (@asan_base_budgets (fun Clg => @AllocP0 Clg) (fun Clg => @DriverP0 Clg) (fun Clg => @E_Top.LIB0 Clg)
           (fun Clg => @pop_core_ok Clg)
           (fun Clg => @restF2_ok Clg) (fun Clg => @restF0_ok Clg)
           (fun Clg AI AI16 => @alib_call_ok_proved Clg AI AI16)).
Qed.
