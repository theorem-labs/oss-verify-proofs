(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from lib/R_memchr.v. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/libreac/fuzz_scene/lib/U/Prog/memchr_c.v, with its module paths and addresses changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from plugin-hostd/fuzz_reply (a working branch 86b50358d34) to libreac/fuzz_boxreg.asan by symbol + offset pairing (port_addr_check 5033540ba83b predict mode; boxreg's interceptor and runtime code is instruction-for-instruction fuzz_reply's modulo numerals): 1 address numeral(s) rewritten, module paths changed. *)
(* Ported from: a working branch 840c4afa7e2 proofs/omx-clap-core/fuzz_state/lib/A/Prog/memchr_c.v.
   Changes (a Theorem Labs lane, 2026-10-29): module path fuzz_state -> fuzz_reply; 1 fuzz_state.asan address numerals moved to fuzz_reply.asan, each paired by code (instruction by instruction, relocation fields masked) or, for a data cell, by the instruction that loads it (table: lib/A/RT_kit.v). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Spec Require Import StrFun.
Import ListNotations.
Open Scope bv_scope.

Definition MEMCHR : Z := 0x92088.

Definition memchr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (buf : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (memchr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf))
                 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ bytes_at rsegs m' (bv_unsigned a0) buf.

Definition memchr_contract : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (buf : list byte),
  bytes_at rsegs m (bv_unsigned a0) buf ->
  memchr_ok (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf ->
  mem_inv rsegs m ->
  evt rsegs (memchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 buf m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 MEMCHR) fc None m (seg_rom rsegs)).
