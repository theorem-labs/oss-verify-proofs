(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj X1bq X1br.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qn X0qc X0qp X0pv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ea X1m2 X1m3 X1m5 X1fr.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1r6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Notation rsegs := X1gj.rsegs.

Definition RFUZZ_ENTRY : Z := 0x1c128.
Definition RFUZZ_STACK : Z := 4194304.
Definition REMPTY : Z := 0x4d360.
Definition RTABLES_LO : Z := 0x3b6e8.
Definition RTABLES_HI : Z := 0x3c0d0.

Definition rtables_pristine (m : mem) : Prop :=
forall a : word, RTABLES_LO <= bv_unsigned a < RTABLES_HI -> m a = None.

Definition rharness_X : list (Z * Z) := [(RSTDERR, RSTDERR + 232)].

Definition harness_post {RCEIL : RunCeiling} (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(s : PState) (LB : list block) (B lo : Z) (m : mem)
(r : Z) (s' : PState) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (errv' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ -2^31 <= r < 2^31
/\ frm0 fc'
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv']
/\ rauxv_ok m' B
/\ pres_except rsegs (rclient_addr LB (bv_unsigned sp)) rharness_X m m'
/\ RHEAP s' LB m'
/\ stderr_wfile m'
/\ ps_so s' = ps_so s.

Definition harness_stmt {RCEIL : RunCeiling} : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (pb : bptr) (P : Z) (payload : list Z) (B lo : Z) (errv : word),
RHEAP s LB m ->
bytes_at rsegs m P (to_bytes payload) -> Forall (fun c => 0 <= c < 256) payload ->
0 < P -> P mod 16 = 0 -> zlength payload <= 2^26 ->
((payload <> [] /\ In (pb, P, zlength payload) LB) \/ (payload = [] /\ P = REMPTY)) ->
rtables_pristine m ->
stderr_wfile m ->
rauxv_ok m B -> bv_unsigned sp <= B -> B < 2^62 ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RFUZZ_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m -> frm0 fc ->
tp = Z_to_bv 64 RATP -> bv_unsigned sp mod 16 = 0 ->
a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 (zlength payload) ->
implM rsegs (fuzz_one payload) s
(harness_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB B lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RFUZZ_ENTRY) fc None m (seg_rom rsegs)).

Goal rsegs = X1ea.rsegs. Proof. reflexivity. Qed.
