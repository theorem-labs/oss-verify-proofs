(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the rseq-dependent auxv): changed cert_202, shape_202; removed planK_202; taken in part from projects/jsoncons/fuzz_json_cursor/proofs/lib/Pm9CertK_202.v, lines 8, 13-27. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import AxSymExec3K AsanPlanCoreK AsanPlanK AsanPlanFastK AsanNodesExtraDefsK AsanInitK Pm5DefsK Pm5ResK Pm5PlanK Pm5HSK_201 Pm5HSK_202 Pm5HSK_0 Pm5HSK_1 Pm5MainTableK.
Import ListNotations. Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* STATEMENT CHANGED, old beside new: certified once PER CONFIG_RSEQ FLAG.
     OLD  cert_202 : check ... LIMIT XN0 ... HS_202 planK_202 = COk shape_202
     NEW  cert_202 : forall b, check ... LIMIT (rseq_z b) XN0 ... (HS_202 b) planK_202 = COk (shape_202 b)
   The plan text moved to Pm5PlanK (fresh indices +4); [shape_202 b] is the shape
   the checker returns, computed per flag.  The proof destructs [b] ABOVE the
   computation, so nothing is computed under an open binder. *)
Definition shape_202 (b : bool) : shape :=
  if b then ltac:(let s := eval vm_compute in (shape_of (chkK 1 (HS_as0 true) (HS_202 true) planK_202)) in exact s)
  else ltac:(let s := eval vm_compute in (shape_of (chkK 0 (HS_as0 false) (HS_202 false) planK_202)) in exact s).
Lemma cert_202 : forall b,
  check ASEGS0 IT0 ASAN0 NX0 AsanInitK.LIMIT (rseq_z b) XN0 XE0 XB0 (HS_as0 b) KC0 BFUEL FUEL None (HS_202 b) planK_202 = COk (shape_202 b).
Proof.
  intros [|]; rewrite <- APKF.check_fast_eq.
  - vm_cast_no_check (@eq_refl cres (COk (shape_202 true))).
  - vm_cast_no_check (@eq_refl cres (COk (shape_202 false))).
Qed.
