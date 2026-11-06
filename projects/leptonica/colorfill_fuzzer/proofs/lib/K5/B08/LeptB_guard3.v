(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import ImageA.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import Layout.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit LeptB_guard LeptB_guard2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma div_guard_pos : forall x, 0 <= x -> (0 <? Z.lor 18446744073709551614 x) = true.
Proof.
  intros x Hx. apply Z.ltb_lt. assert (H0 : 0 <= Z.lor 18446744073709551614 x) by (apply Z.lor_nonneg; lia).
  assert (H1 : Z.lor 18446744073709551614 x <> 0) by (intro E; apply Z.lor_eq_0_iff in E; lia). lia.
Qed.
Ltac div_guard_fix :=
  repeat match goal with
  | |- context [0 <? Z.lor 18446744073709551614 (Z.lxor (bv_unsigned ?w) ?k)] =>
      rewrite (div_guard_pos (Z.lxor (bv_unsigned w) k))
        by (apply Z.lxor_nonneg; pose proof (bv_unsigned_in_range 64 w); split; intros _; lia)
  end; cbn [Z.b2z].
Ltac po_irrefl_fix :=
  progress (rewrite !Z.ltb_irrefl); cbn [Z.b2z]; change (Z.lxor 0 0) with 0; change (Z.lxor 0 1) with 1; change (Z.lxor 1 0) with 1.
Ltac guard_fix ::= try sx32_fix; swrap_fix; po_fix; al_fix; try mulh_fix; try mulh_fix2; po_neg_fix; po_not_fix; try al_or_fix; try po_irrefl_fix; try (progress div_guard_fix).
