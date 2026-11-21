(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Zg_infl_c_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_ikit Z_infl_defs Z_infl_c_pure Z_infl_c_tab Zg_infl_defs.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg ZIface InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb RefInflateA_DIST1 RefInflateSafeH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Module GC := OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P.Zg_infl_c_kit.

Definition DECG (X : ictx) (s : inflate_state) (c : icall) (rw rb : iregs) (RES : ares Z) (rf : iregs) (p : codeptr) (index need : Z -> Z)
    (pcj : Z) (Q : iregs -> iscrh -> Prop) : machine_state -> Prop :=
  fun ms' =>
    (exists r1 q, RES = ARun (code_at s p (index (ir_hold r1))) (mkW s c r1)
                  /\ rf = r1
                  /\ need (code_at s p (index (ir_hold r1))) <= ir_bits r1
                  /\ 0 <= index (ir_hold r1) < ctab_size p
                  /\ REGS c r1 /\ pulled rb r1
                  /\ ILOOPh X (mkW s c rw) pcj q ms' /\ Q r1 q)
    \/ (exists r1, RES = ALeave (mkW s c r1) /\ pulled rb r1 /\ ILEAVE X (mkW s c r1) ms').

Definition DC_found := GC.DC_found.
Definition DC_dry := GC.DC_dry.
Definition DC_pull := GC.DC_pull.
Definition CK_found := GC.CK_found.
Definition CK_range := GC.CK_range.
Definition CK_dry := GC.CK_dry.
Definition CK_pull := GC.CK_pull.
Definition CK_short0 := GC.CK_short0.
Definition decG_r1_facts := GC.decG_r1_facts.

Notation DREGSg := GC.DREGSg.
Definition DREGSg_of_REGS := GC.DREGSg_of_REGS.
Definition dec_r1_factsg := GC.dec_r1_factsg.
Definition DREGSg_hold64 := GC.DREGSg_hold64.
Definition DREGSg_drop := GC.DREGSg_drop.
Definition DREGSg_nb := GC.DREGSg_nb.
