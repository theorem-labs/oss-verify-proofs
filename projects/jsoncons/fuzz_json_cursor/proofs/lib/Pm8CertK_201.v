(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the rseq-dependent auxv): changed JS_as0_201, cert_201, shape_201; planK_201 moved to Pm8PlanK.v. *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import AxSymExec3K AsanPlanCoreK AsanPlanK AsanPlanFastK AsanNodesExtraDefsK AsanInitK Pm8DefsK Pm8ResK Pm8PlanK Pm8HSK_201 Pm8HSK_202.
Import ListNotations. Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* STATEMENT CHANGED, old beside new: certified once PER CONFIG_RSEQ FLAG.
     OLD  cert_201 : check ... LIMIT XN0 ... HS_201 planK_201 = COk shape_201
     NEW  cert_201 : forall b, check ... LIMIT (rseq_z b) XN0 ... (HS_201 b) planK_201 = COk (shape_201 b)
   The plan text moved to Pm8PlanK (fresh indices +4); [shape_201 b] is the shape
   the checker returns, computed per flag.  The proof destructs [b] ABOVE the
   computation, so nothing is computed under an open binder. *)
Definition JS_as0_201 (b : bool) (h : nat) : option acs := if Nat.eqb h 202 then Some (HS_202 b) else None.
Definition shape_201 (b : bool) : shape :=
  if b then ltac:(let s := eval vm_compute in (shape_of (chkK 1 (JS_as0_201 true) (HS_201 true) planK_201)) in exact s)
  else ltac:(let s := eval vm_compute in (shape_of (chkK 0 (JS_as0_201 false) (HS_201 false) planK_201)) in exact s).
Lemma cert_201 : forall b,
  check ASEGS0 IT0 ASAN0 NX0 AsanInitK.LIMIT (rseq_z b) XN0 XE0 XB0 (JS_as0_201 b) KC0 BFUEL FUEL None (HS_201 b) planK_201 = COk (shape_201 b).
Proof.
  intros [|]; rewrite <- APKF.check_fast_eq.
  - vm_cast_no_check (@eq_refl cres (COk (shape_201 true))).
  - vm_cast_no_check (@eq_refl cres (COk (shape_201 false))).
Qed.
