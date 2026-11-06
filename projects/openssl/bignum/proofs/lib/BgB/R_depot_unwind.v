(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr Walk. 
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import R_unwind_defs R_depot_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation mem := (word -> option byte).

Definition rng64 (x : Z) : Prop := 0 <= x < 2 ^ 64.

Lemma wr_trace_split : forall tr tb, wr_trace tr tb = map (Z_to_bv 64) tr ++ skipn (length tr) tb.
Proof. reflexivity. Qed.

Lemma map_unsigned_lits : forall tr, Forall rng64 tr -> map bv_unsigned (map (Z_to_bv 64) tr) = tr.
Proof.
  induction tr as [|x tr IH]; intros HF; [reflexivity|]. inversion HF as [|? ? Hx Htr]; subst.
  cbn [map]. rewrite unsigned_lit by (unfold rng64 in Hx; lia). f_equal. apply IH. exact Htr.
Qed.

