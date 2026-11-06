(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Image.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Export Layout.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Exit Imp_ios_defs Pj_loc_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation psegs := Image.psegs.
Notation mem := (word -> option byte).

Definition F_IOS_INIT : Z := 0x7c9c0.
Definition IOS_INIT_DEPTH : Z := 736.
Definition IOS_TPLOC : Z := 0xe9d68.
Definition IOS_GLOC : Z := 0x10a060.
Definition IOS_LOCLOCK : Z := 0x10a100.
Definition IOS_RLIBC : Z := 0x10a028.

Definition ios_img_facts (m : mem) : Prop :=
  rw_cells psegs m 0xd3c68 [C8 (Z_to_bv 64 16)]
  /\ rw_cells psegs m 0xd3cb8 [C8 (Z_to_bv 64 8)]
  /\ rw_cells psegs m 0xd3d88 [C8 (Z_to_bv 64 16)]
  /\ rw_cells psegs m 0xd3dd8 [C8 (Z_to_bv 64 8)]
  /\ rw_cells psegs m 0xd40a8 [C8 (Z_to_bv 64 0x7bb40)]
  /\ rw_cells psegs m 0xd41d8 [C8 (Z_to_bv 64 0x7c2ac)]
  /\ rw_cells psegs m 0xd4528 [C8 (Z_to_bv 64 0xa4190); C8 (Z_to_bv 64 0xa4290)]
  /\ rw_cells psegs m 0xd47d8 [C8 (Z_to_bv 64 0xa38f0); C8 (Z_to_bv 64 0xa38f8)]
  /\ rw_cells psegs m 0xd64b0 [C8 (Z_to_bv 64 RSTDERR); C8 (Z_to_bv 64 RSTDIN); C8 (Z_to_bv 64 RSTDOUT)]
  /\ rw_cells psegs m 0xd6510 [C8 (Z_to_bv 64 0xd64b0)]
  /\ rw_cells psegs m 0xd6520 [C8 (Z_to_bv 64 0xd64c0)]
  /\ rw_cells psegs m 0xd6540 [C8 (Z_to_bv 64 0xd3be8)]
  /\ rw_cells psegs m 0xd6648 [C8 (Z_to_bv 64 0xd3c68); C8 (Z_to_bv 64 0xd3cb8); C8 (Z_to_bv 64 0xd3d08); C8 (Z_to_bv 64 0xd3d88);
                               C8 (Z_to_bv 64 0xd3dd8); C8 (Z_to_bv 64 LOC_IDC); C8 (Z_to_bv 64 0xd64b8); C8 (Z_to_bv 64 LOC_IDW)].

Definition ios_img_addr (a : Z) : Prop :=
  (0xd3c68 <= a < 0xd3c68 + 8) \/ (0xd3cb8 <= a < 0xd3cb8 + 8) \/ (0xd3d88 <= a < 0xd3d88 + 8) \/ (0xd3dd8 <= a < 0xd3dd8 + 8)
  \/ (0xd40a8 <= a < 0xd40a8 + 8) \/ (0xd41d8 <= a < 0xd41d8 + 8) \/ (0xd4528 <= a < 0xd4528 + 16) \/ (0xd47d8 <= a < 0xd47d8 + 16)
  \/ (0xd64b0 <= a < 0xd64b0 + 24) \/ (0xd6510 <= a < 0xd6510 + 8) \/ (0xd6520 <= a < 0xd6520 + 8) \/ (0xd6540 <= a < 0xd6540 + 8) \/ (0xd6648 <= a < 0xd6648 + 64).

Definition ios_init_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - 736, bv_unsigned sp); (0xe7e70, 0xe9488); (0xe9d68, 0xe9d70); (0x109de8, 0x109df8); (0x109e00, 0x109e08); (0x109f00, 0x109f08)] m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ ios_block m'
    /\ LOCB m' /\ locx m'
    /\ aex_tbl m' 1
    /\ rw_cells psegs m' IOS_TPLOC [C8 (Z_to_bv 64 IOS_GLOC)]
    /\ ssp_cells m' canary.

Definition ios_init_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (canary : word) (cdt thr sec : byte) (tm1 : word),
    stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 736) -> (GLOBALS_TOP <= lo) -> (bv_unsigned sp < 2^62) ->
    rw_cells psegs m IOS [CB 1952 (repeat (Z_to_bv 8 0) 1952)] ->
    LOC0 m ->
    rw_cells psegs m AEX [CB 312 (repeat (Z_to_bv 8 0) 312)] ->
    ios_img_facts m ->
    rw_cells psegs m IOS_RLIBC [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    rw_cells psegs m IOS_LOCLOCK [C4 (Z_to_bv 64 0)] ->
    rw_cells psegs m IOS_TPLOC [C8 (Z_to_bv 64 IOS_GLOC)] ->
    ssp_cells m canary ->
    tp = Z_to_bv 64 RTP ->
    mem_inv psegs m ->
    evt psegs (ios_init_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 F_IOS_INIT) fc None m (seg_rom psegs)).
