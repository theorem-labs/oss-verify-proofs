(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2.
Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.

Ltac olin_core P lo hi ::=
  let L := fresh "OLx" in
  pose proof (oclr_lin lo hi P ltac:(lia)) as L;
  unfold AIMG_LO, AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_BEG in L.
Ltac alin_core P lo hi ::=
  let L := fresh "ALx" in let D := fresh "ADx" in
  pose proof (ablk_lin lo hi P) as L; pose proof (ablk_disj_band lo hi P) as D;
  unfold AIMG_LO, AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_BEG in L, D.
Ltac olin_mark lo hi ::= let M := fresh "OLM" in pose proof (I : olin_done lo hi) as M.
Ltac olin_clean := repeat match goal with X : olin_done _ _ |- _ => clear X end.
