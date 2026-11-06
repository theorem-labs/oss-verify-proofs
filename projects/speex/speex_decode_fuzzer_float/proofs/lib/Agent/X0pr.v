(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bj.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0ok.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pu X0qm X0pc X0pb X0qn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qh X0qk X0pl X0pm X0pn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qj X0po X0pp X0pq.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Definition nest_frame (st : mstate) (g p : aptr) (j0 j1 : list byte) (raw : word) : list cell :=
[CB 8 j0; C8 (Z_to_bv 64 (conc st p)); C8 (Z_to_bv 64 (conc st g)); C8 (Z_to_bv 64 CTX); CB 40 j1; C8 raw].

Definition nest_call_post {RCEIL : RunCeiling} (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g p : aptr) (G1 idx : Z) (raw : word) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 j0 j1 m',
ms' = MS (mkR (Z_to_bv 64 0x15db0) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 G1) (Z_to_bv 64 idx) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x15a6c) fc None m' (seg_rom asegs)
/\ pres_except (free_fp st lo (bv_unsigned sp)) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp + -80)
/\ rw_cells asegs m' (bv_unsigned sp + -80) (nest_frame st g p j0 j1 raw)
/\ mrep st' m'.

