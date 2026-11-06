(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_parse_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import Scan_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_sscanf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_strtod.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import CJ_parse_main CJ_pwlopts_B CJ_pstring_C.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Theorem parse_wopts_from_ps : forall HI, parse_string_stmt HI -> parse_wopts_stmt HI.
Proof. intros HI PS. apply parse_wopts_from_pv. apply parse_value_spec; [exact rstrtod_proof| exact PS]. Qed.

Theorem parse_wlopts_from_ps : forall HI, parse_string_stmt HI -> parse_wlopts_stmt HI.
Proof. intros HI PS. apply parse_wlopts_from_pv. apply parse_value_spec; [exact rstrtod_proof| exact PS]. Qed.

(* [comment removed for export] *)
Theorem parse_value_spec' : forall HI, parse_value_stmt HI.
Proof. intros HI. apply parse_value_spec; [exact rstrtod_proof| apply parse_string_spec]. Qed.

Theorem parse_object_spec' : forall HI, parse_object_stmt HI.
Proof. intros HI. apply parse_object_spec; [exact rstrtod_proof| apply parse_string_spec]. Qed.

Theorem parse_wlopts_spec : forall HI, parse_wlopts_stmt HI.
Proof. intros HI. apply parse_wlopts_from_ps. apply parse_string_spec. Qed.

Theorem parse_wopts_spec : forall HI, parse_wopts_stmt HI.
Proof. intros HI. apply parse_wopts_from_ps. apply parse_string_spec. Qed.


End CeilWrap.
