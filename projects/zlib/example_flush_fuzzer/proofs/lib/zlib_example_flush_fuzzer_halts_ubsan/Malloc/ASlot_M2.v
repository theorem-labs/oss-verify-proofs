(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Malloc Require Import MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Malloc Require Import Malloc_fp MallocKit_A2 AllocSlot_iface F_malloc_join Malloc_iface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Malloc Require Import MallocNat MallocFacts_AS MallocKit_A3 ASlot_W0 ASlot_W1 ASlot_W2 ASlot_W8 ASlot_W9 ASlot_W10 ASlot_W12 ASlot_I ASlot_M0 ASlot_M1.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Malloc Require MallocFacts_inv4.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section EPI2.
Variables (lo : Z).
Hypothesis CLO : ATOP <= lo.
End EPI2.

Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : AREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis CLO : ATOP <= lo.
Hypothesis LO : lo <= bv_unsigned sp - AS_STACK (S f).
Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a65c.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Let F0 : ISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.

Variable am_pre : mstate -> Prop.
Hypothesis AMP : AMP_AS am_pre.


End LEVEL.


End CANSEC1.
