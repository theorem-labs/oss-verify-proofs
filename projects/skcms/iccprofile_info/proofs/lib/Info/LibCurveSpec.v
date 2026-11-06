(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim Hoare Frame LibDefs LibWP1Spec.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section Specs.
Variable segs : list Segment.
Variable W : wp1_abi.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition classify_pre (sp tf : word)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let t := bv_unsigned tf in
  getr regs 2 = sp /\ getr regs 10 = tf /\
  getr regs 11 = Z_to_bv 64 0 /\ getr regs 12 = Z_to_bv 64 0 /\
  (exists g a b c d e f : word,
     cell segs mem t 4 g /\ cell segs mem (t + 4) 4 a /\ cell segs mem (t + 8) 4 b /\
     cell segs mem (t + 12) 4 c /\ cell segs mem (t + 16) 4 d /\ cell segs mem (t + 20) 4 e /\
     cell segs mem (t + 24) 4 f) /\
  t + 28 <= 2 ^ 64 /\
  writable segs mem (bv_unsigned sp - 16) 16 /\
  rodata_clear mem (w1_ro_lo W) (w1_ro_hi W) /\
  (bv_unsigned sp <= t \/ t + 28 <= bv_unsigned sp - 16).

Definition classify_post (sp tf : word)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 16), 16)].

Definition classify_contract : Prop :=
  forall sp tf, fn_contract segs (w1_classify W) (classify_pre sp tf) (classify_post sp tf).

End Specs.
