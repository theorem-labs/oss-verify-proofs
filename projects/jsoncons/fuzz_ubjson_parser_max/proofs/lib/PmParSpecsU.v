(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec StoreOk HeapIface L5Defs L5Core PmLayout PmLayoutU PmModel PmStatics PmSpecs PmSpecsU
PmParSpecs PmTxtSpecs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMPSU.
Import PMU.
Section Names.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Definition xsgetn_spec := PMPS.xsgetn_spec RSEGS AD L HI.
Definition fill_buffer_spec := PMPS.fill_buffer_spec RSEGS AD L HI.
Definition peek_spec := PMPS.peek_spec RSEGS AD L HI.
Definition ignore_spec := PMPS.ignore_spec RSEGS AD L HI.
Definition src_read_spec := PMPS.src_read_spec RSEGS AD L HI.
Definition fill_buffer_tb_spec := PMTXS.fill_buffer_tb_spec RSEGS AD L HI.
Definition srd_read_spec := PMTXS.srd_read_spec RSEGS AD L HI.
End Names.
End PMPSU.
