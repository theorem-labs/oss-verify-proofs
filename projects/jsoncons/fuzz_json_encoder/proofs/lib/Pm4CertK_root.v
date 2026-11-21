(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the rseq-dependent auxv): changed JS_as0_root, cert_root, shape_root; removed planK_root; taken in part from projects/jsoncons/fuzz_json_cursor/proofs/lib/Pm8CertK_root.v, lines 8, 13-28. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import AxSymExec3K AsanPlanCoreK AsanPlanK AsanPlanFastK AsanNodesExtraDefsK AsanInitK Pm4DefsK Pm4ResK Pm4PlanK Pm4HSK_201.
Import ListNotations. Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* STATEMENT CHANGED, old beside new: certified once PER CONFIG_RSEQ FLAG.
     OLD  cert_root : check ... LIMIT XN0 ... asan0_init planK_root = COk shape_root
     NEW  cert_root : forall b, check ... LIMIT (rseq_z b) XN0 ... (asan0_init (rseq_z b)) planK_root = COk (shape_root b)
   The plan text moved to Pm4PlanK (fresh indices +4); [shape_root b] is the shape
   the checker returns, computed per flag.  The proof destructs [b] ABOVE the
   computation, so nothing is computed under an open binder. *)
Definition JS_as0_root (b : bool) (h : nat) : option acs := if Nat.eqb h 201 then Some (HS_201 b) else None.
Definition shape_root (b : bool) : shape :=
  if b then ltac:(let s := eval vm_compute in (shape_of (chkK 1 (JS_as0_root true) (asan0_init 1) planK_root)) in exact s)
  else ltac:(let s := eval vm_compute in (shape_of (chkK 0 (JS_as0_root false) (asan0_init 0) planK_root)) in exact s).
Lemma cert_root : forall b,
  check ASEGS0 IT0 ASAN0 NX0 AsanInitK.LIMIT (rseq_z b) XN0 XE0 XB0 (JS_as0_root b) KC0 BFUEL FUEL None (asan0_init (rseq_z b)) planK_root = COk (shape_root b).
Proof.
  intros [|]; rewrite <- APKF.check_fast_eq.
  - vm_cast_no_check (@eq_refl cres (COk (shape_root true))).
  - vm_cast_no_check (@eq_refl cres (COk (shape_root false))).
Qed.
