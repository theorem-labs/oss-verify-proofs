(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.CliDriver Require Import SymExec2 SymDrive.
Import ListNotations. Import SX2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.

(* [comment removed for export] *)
Definition cfglen_canon : expr :=
  EAlu ALU_OR
    (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EExt true 0 1 (EVar 42))) (ELit 49))
    (EExt false 0 1 (EVar 41)).

(* [comment removed for export] *)
Definition cfgF_canon (v41 v42 : word) : word :=
  edenot (Env (fun n => match n with 41%nat => v41 | 42%nat => v42 | _ => Z_to_bv 64 0 end) (blobs_ev [])) cfglen_canon.

Definition zseq (n : nat) : list Z := map Z.of_nat (seq 0 n).

Lemma cfgF_tab_canon :
  forallb (fun b1 => forallb (fun b0 =>
     Z.eqb (bv_unsigned (cfgF_canon (Z_to_bv 64 b0) (Z_to_bv 64 b1))) ((b0 + 256 * b1) mod 32768))
     (zseq 256)) (zseq 256) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
