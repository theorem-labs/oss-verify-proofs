(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_parse_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_pstr_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pstr_A.CJ_print_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import Scan_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_sscanf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_sscanf.F_strtod.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import CJ_pwopts CJ_print_top CJ_fuzz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Theorem fuzz_spec_closed : forall HI, fuzz_stmt HI.
Proof.
  intros HI. apply fuzz_spec.
  - apply parse_wopts_spec. exact rstrtod_proof.
  - apply pbuffered_spec'.
  - apply cjprint_spec'.
  - apply cjprintu_spec'.
Qed.


End CeilWrap.
