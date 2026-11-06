(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocKit_A.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocFacts_A MallocHINV.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocKit_AB.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl Monad RawAlloc.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import Malloc_fp MallocKit_A2 AllocSlot_iface F_malloc_join Malloc_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocNat MallocFacts_AS.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocKit_A3 ASlot_W0 ASlot_W1 ASlot_W9 ASlot_W10 ASlot_W11 ASlot_I ASlot_M0.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require MallocFacts_inv4.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Export MallocVocab MallocOracle.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma halve_big_pos F : forall cnt sz, 1 <= cnt -> 0 <= sz < 2^18 -> 1 <= halve_big F cnt sz.
Proof.
  induction F as [|F IH]; intros cnt sz Hc Hs; cbn [halve_big]; [lia|].
  destruct (Z.leb_spec (65536 * UNIT) (sz * cnt)) as [LE|GT]; [|lia].
  apply IH; [|lia]. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. unfold UNIT in LE.
  assert (2 <= cnt) by nia. Z.div_mod_to_equations. lia.
Qed.

Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - AS_STACK (S f).
Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
End LEVEL.
End RC__1.
