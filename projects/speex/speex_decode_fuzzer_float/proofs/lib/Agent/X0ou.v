(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bj.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0ok.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pu X0pj X0qm X0pc X0qn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qh X0qk X0qj X0pm.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0op X0ow X0oq X0ot.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac showregs := lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ ?m _) => idtac "REGS" R "PC" pc "MEM" m end.

Definition tomm_post {RCEIL : RunCeiling} (sp tp t0 t2 s0 s1 a4x a5x a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 t1v raw : word) (F : bvmap 5 word) (fc : bv 32)
(lo n : Z) (st : mstate) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists m' j0 j1,
ms' = MS (mkR (Z_to_bv 64 0x1615c) (Z_to_bv 64 (bv_unsigned sp + -64)) (Z_to_bv 64 0x1a800) tp t0 t1v t2 s0 s1
(Z_to_bv 64 0) (Z_to_bv 64 (n * 4096)) (Z_to_bv 64 0) (Z_to_bv 64 34) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) a6 (Z_to_bv 64 n)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 4096) t4 t5 t6)
F (Z_to_bv 64 mmap_entry) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' (bv_unsigned sp + -64) [CB 8 j0; C8 t1v; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 4096); CB 24 j1; C8 raw]
/\ stk asegs m' lo (bv_unsigned sp + -64)
/\ mrep st m'.

Definition mm_ok_st (st : mstate) (rid : N) (n : Z) : mstate :=
upd_ctx (fun c => set_meta_alloc_shift (c_meta_alloc_shift c + 1) (set_avail_meta_area_count (n - 1) (set_avail_meta_areas (Some (rid, 4096)) c))) st.

