(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Image.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Export Layout.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Import Exit Imp_ios_defs Pj_loc_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation usegs := Image.usegs.
Notation mem := (word -> option byte).

Definition F_IOS_INIT : Z := 0x87e64.
Definition IOS_INIT_DEPTH : Z := 736.
Definition IOS_TPLOC : Z := 0xf5518.
Definition IOS_GLOC : Z := 0x115810.
Definition IOS_LOCLOCK : Z := 0x1158b0.
Definition IOS_RLIBC : Z := 0x1157d8.

Definition ios_img_facts (m : mem) : Prop :=
  rw_cells usegs m 0xdf110 [C8 (Z_to_bv 64 16)]
  /\ rw_cells usegs m 0xdf160 [C8 (Z_to_bv 64 8)]
  /\ rw_cells usegs m 0xdf230 [C8 (Z_to_bv 64 16)]
  /\ rw_cells usegs m 0xdf280 [C8 (Z_to_bv 64 8)]
  /\ rw_cells usegs m 0xdf550 [C8 (Z_to_bv 64 0x86fe4)]
  /\ rw_cells usegs m 0xdf680 [C8 (Z_to_bv 64 0x87750)]
  /\ rw_cells usegs m 0xdf9d0 [C8 (Z_to_bv 64 0xaf634); C8 (Z_to_bv 64 0xaf734)]
  /\ rw_cells usegs m 0xdfc80 [C8 (Z_to_bv 64 0xaed94); C8 (Z_to_bv 64 0xaed9c)]
  /\ rw_cells usegs m 0xe1958 [C8 (Z_to_bv 64 RSTDERR); C8 (Z_to_bv 64 RSTDIN); C8 (Z_to_bv 64 RSTDOUT)]
  /\ rw_cells usegs m 0xe19b8 [C8 (Z_to_bv 64 0xe1958)]
  /\ rw_cells usegs m 0xe19c8 [C8 (Z_to_bv 64 0xe1968)]
  /\ rw_cells usegs m 0xe19e8 [C8 (Z_to_bv 64 0xdf090)]
  /\ rw_cells usegs m 0xe1af0 [C8 (Z_to_bv 64 0xdf110); C8 (Z_to_bv 64 0xdf160); C8 (Z_to_bv 64 0xdf1b0); C8 (Z_to_bv 64 0xdf230);
                               C8 (Z_to_bv 64 0xdf280); C8 (Z_to_bv 64 LOC_IDC); C8 (Z_to_bv 64 0xe1960); C8 (Z_to_bv 64 LOC_IDW)].

Definition ios_img_addr (a : Z) : Prop :=
  (0xdf110 <= a < 0xdf110 + 8) \/ (0xdf160 <= a < 0xdf160 + 8) \/ (0xdf230 <= a < 0xdf230 + 8) \/ (0xdf280 <= a < 0xdf280 + 8)
  \/ (0xdf550 <= a < 0xdf550 + 8) \/ (0xdf680 <= a < 0xdf680 + 8) \/ (0xdf9d0 <= a < 0xdf9d0 + 16) \/ (0xdfc80 <= a < 0xdfc80 + 16)
  \/ (0xe1958 <= a < 0xe1958 + 24) \/ (0xe19b8 <= a < 0xe19b8 + 8) \/ (0xe19c8 <= a < 0xe19c8 + 8) \/ (0xe19e8 <= a < 0xe19e8 + 8) \/ (0xe1af0 <= a < 0xe1af0 + 64).

Definition ios_init_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 736, bv_unsigned sp); (0xf3620, 0xf4c38); (0xf5518, 0xf5520); (0x115598, 0x1155a8); (0x1155b0, 0x1155b8); (0x1156b0, 0x1156b8)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ ios_block m'
    /\ LOCB m' /\ locx m'
    /\ aex_tbl m' 1
    /\ rw_cells usegs m' IOS_TPLOC [C8 (Z_to_bv 64 IOS_GLOC)]
    /\ ssp_cells m' canary.

Definition ios_init_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (canary : word) (cdt thr sec : byte) (tm1 : word),
    stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 736) -> (GLOBALS_TOP <= lo) -> (bv_unsigned sp < 2^62) ->
    rw_cells usegs m IOS [CB 1952 (repeat (Z_to_bv 8 0) 1952)] ->
    LOC0 m ->
    rw_cells usegs m AEX [CB 312 (repeat (Z_to_bv 8 0) 312)] ->
    ios_img_facts m ->
    rw_cells usegs m IOS_RLIBC [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    rw_cells usegs m IOS_LOCLOCK [C4 (Z_to_bv 64 0)] ->
    rw_cells usegs m IOS_TPLOC [C8 (Z_to_bv 64 IOS_GLOC)] ->
    ssp_cells m canary ->
    tp = Z_to_bv 64 RTP ->
    mem_inv usegs m ->
    evt usegs (ios_init_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 F_IOS_INIT) fc None m (seg_rom usegs)).
