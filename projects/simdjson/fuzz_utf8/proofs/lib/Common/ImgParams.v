(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AsanPlanCore. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import AsanNodesArg AsanNodesRP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
Record mtab : Type := MT {
  mt_enframe : Z;     (* [comment removed for export] *)
  mt_getmeta : Z;     (* [comment removed for export] *)
  mt_free : Z;        (* [comment removed for export] *)
  mt_free_k : Z;      (* [comment removed for export] *)
  mt_sct : Z;         (* [comment removed for export] *)
  mt_secret : Z       (* [comment removed for export] *)
}.

Record imgparams : Type := IP {
  ip_segs : list Segment;     (* [comment removed for export] *)
  ip_A : APC.atable;          (* [comment removed for export] *)
  ip_G : AN.argtab;           (* [comment removed for export] *)
  ip_limit : Z;               (* [comment removed for export] *)
  ip_M : mtab;                (* [comment removed for export] *)
  ip_RP : RPN.rptab           (* [comment removed for export] *)
}.
