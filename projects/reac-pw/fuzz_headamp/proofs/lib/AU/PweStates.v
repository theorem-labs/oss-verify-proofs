(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the entry-state shape of proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at 5afd8b87436 (its regions, atom facts, assumed branch conditions and alias fact) for reac-pw/fuzz_rate's image B: the four states are pod_write_ent's own, measured on its code. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/PweStates.v at d75b4b9c2458; module paths changed to reac-pw/fuzz_headamp; the run pcs PWE_P1, PWE_P2, PWE_P3, PWE_RET, PWE_RA1, PWE_RA2 moved to fuzz_headamp's image B (pod_write_ent at 0x84634, the same 194 words up to their pc-relative fields: every pc keeps its offset from the entry); comments' addresses and image hashes moved with them. *)
(* The four engine states of pod_write_ent's walk on image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94). Proves no function (kind: statement text):
   this file only names the states; lib/AU/PweWalk.v proves the function against them.

   THE ATOMS. Registers are atoms 0 .. 31 of the run's own entry registers. The extra atoms are, in each state:
     32 the runtime's shadow offset K, 33 len, 34 e_size, 35 e_type, 36 pp + len,
     35 .. 39 (the last run only) the caller's ra, s0, s1, s2 and s3, as the prologue saved them.
   In the first run pp is a0 (atom 10) and e is a1 (atom 11); from the second run on pp is s1 (atom 9), because
   `mv s1,a0` at 0x84654 put it there.

   THE RUNS (every pc measured on the image):
     R0 0x84634 -> 0x84664   the prologue's five stores into the 48-byte save slot, the UBSan alignment test of e,
                             and the two 8-byte loads that fetch the runtime's shadow offset K: the GOT slot
                             0x9c7f0 holds the address 0xa5238 of the shadow-offset cell, and that cell holds K.
                             Three regions, no shadow entry: no shadow byte is read yet.
     R1 0x84664 -> 0x51d8c   the two put32s at pp + len and pp + len + 4, each under its capacity guard, its two
                             UBSan tests and its two instrumented checks; the len cell's three checks and its two
                             updates; and the `jal` of __asan_memcpy. Three regions, three shadow entries (pp's
                             block, e's object, the eight bytes at pp + len), seven assumed branch conditions and
                             the alias that names pp + len.
     R2 0x84804 -> 0x52228   the len cell's check and its update to len + 8 + size, the pad (-(len + 8 + size)) & 7,
                             its capacity guard and its two UBSan tests, and the `jal` of __asan_memset.
     R3 0x8484c -> 0x84878   the len cell's last check and its update to len + n, the epilogue's five loads and
                             `ret`.
   An assumed branch condition (f_conds) is a branch outcome the walk proves from the contract's premises; the
   engine then decides that branch. Here they are the four capacity guards of pod_put (pod.h:177) and the UBSan
   tests `~pp <u len + c` (pod.h:179) that would mean pp + len wraps. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import PweKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the pcs the runs start and stop at *)
Definition PWE_P1 : Z := 0x84664.
Definition PWE_P2 : Z := 0x84804.
Definition PWE_P3 : Z := 0x8484c.
Definition PWE_RET : Z := 0x84878.
(* the two return addresses the `jal`s leave in ra *)
Definition PWE_RA1 : Z := 0x84804.
Definition PWE_RA2 : Z := 0x8484c.

(* ---- R0: the prologue and the shadow-offset cell ---- *)
Definition p0_regions : smem := [ pwe_stack_region; pwe_got_region; pwe_cell_region ].
Definition p0_facts : facts := mkFacts
  [ (2%nat, mkAF (2^46) (2^47) 4); (11%nat, mkAF 0 (2^47 - 104) 3); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0) ] [] [].
Definition ss_p0 : sstate := mkSS PWE_A sr_atoms p0_regions None p0_facts.

(* ---- R1: the two put32s and the memcpy call ---- *)
Definition p1_len_region : YP09.region :=
YP09.mkRegion (Some 9%nat) 0x4000 0x4008 0x4000 0x4008 [YP09.mkChunk 0x4000 (CVal 8 (SOff 33 0))].
Definition p1_ent_region : YP09.region :=
YP09.mkRegion (Some 11%nat) 0 104 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 35 0)); YP09.mkChunk 4 (CVal 4 (SOff 34 0))].
Definition p1_body_region : YP09.region := YP09.mkRegion (Some 36%nat) 0 8 0 8 [].
Definition p1_regions : smem := [ p1_len_region; p1_ent_region; p1_body_region ].
Definition p1_SH : list shent := [ mkSHE 9 0 19744; mkSHE 11 0 104; mkSHE 36 0 8 ].
(* ~pp, the value of `not a7,s1`; and len + 8 + size, the end of the body *)
Definition pwe_notpp : sv := SAlu ALU_XOR (SOff 9 0) (SLit (-1)).
Definition pwe_tot : sv := SAlu ALU_ADD (SOff 33 8) (SOff 34 0).
Definition p1_facts : facts := mkFacts
  [ (2%nat, mkAF (2^46) (2^47) 4); (9%nat, mkAF 0 (2^47 - 19744) 3); (11%nat, mkAF 0 (2^47 - 104) 3);
    (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 0 16376 3); (34%nat, mkAF 0 96 0);
    (35%nat, mkAF 0 (2^32) 0); (36%nat, mkAF 0 (2^47 - 8) 3) ]
  [ mkAC BC_GEU (SOff 33 (-16381)) (SLit 18446744073709535231);
    mkAC BC_GEU (SOff 33 (-16377)) (SLit 18446744073709535231);
    mkAC BC_GEU pwe_notpp (SOff 33 0);
    mkAC BC_GEU pwe_notpp (SOff 33 4);
    mkAC BC_GEU pwe_notpp (SOff 33 8);
    mkAC BC_GEU (SLit 16384) pwe_tot ]
  [ (SAlu ALU_ADD (SOff 9 0) (SOff 33 0), SOff 36 0) ].
Definition p1_regs : list sv := sr_set sr_atoms (15%bv : bv 5) (SOff 32 0).
Definition ss_p1 : sstate := mkSS PWE_P1 p1_regs p1_regions None p1_facts.

(* ---- R2: the pad and the memset call ---- *)
(* s3, the len cell's shadow address, and the pad (-(len + 8 + size)) & 7 as the code computes it *)
Definition pwe_sh3 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 9 16384) (SLit 3)) (SOff 32 0).
Definition pwe_pad : sv :=
SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 33 0) (SLit (-1))) (SLit (-8)))
  (SMd M_MUL (SOff 34 0) (SLit (-1)))) (SLit 7).
Definition p2_len_region : YP09.region :=
YP09.mkRegion (Some 9%nat) 0x4000 0x4008 0x4000 0x4008 [YP09.mkChunk 0x4000 (CVal 8 (SOff 33 8))].
Definition p2_regions : smem := [ p2_len_region ].
Definition p2_SH : list shent := [ mkSHE 9 0 19744 ].
Definition p2_facts : facts := mkFacts
  [ (2%nat, mkAF (2^46) (2^47) 4); (9%nat, mkAF 0 (2^47 - 19744) 3);
    (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 0 16376 3); (34%nat, mkAF 0 96 0) ]
  [ mkAC BC_GEU (SLit 16384) (SAlu ALU_ADD pwe_pad pwe_tot);
    mkAC BC_LTU pwe_tot (SLit 16385);
    mkAC BC_GEU pwe_notpp pwe_tot ]
  [ ].
(* a5 is caller-saved: the runtime copy does not keep it, and nothing from 0x84804 on reads it *)
Definition p2_regs : list sv :=
  sr_set (sr_set (sr_set sr_atoms (8%bv : bv 5) (SOff 9 16384))
    (19%bv : bv 5) pwe_sh3) (18%bv : bv 5) (SOff 34 0).
Definition ss_p2 : sstate := mkSS PWE_P2 p2_regs p2_regions None p2_facts.

(* ---- R3: the last len update, the epilogue and `ret` ---- *)
Definition p3_stack_region : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 48 0 0
  [ YP09.mkChunk 40 (CVal 8 (SOff 35 0)); YP09.mkChunk 32 (CVal 8 (SOff 36 0));
    YP09.mkChunk 24 (CVal 8 (SOff 37 0)); YP09.mkChunk 16 (CVal 8 (SOff 38 0));
    YP09.mkChunk 8 (CVal 8 (SOff 39 0)) ].
Definition p3_len_region : YP09.region :=
YP09.mkRegion (Some 9%nat) 0x4000 0x4008 0x4000 0x4008 [YP09.mkChunk 0x4000 (CVal 8 pwe_tot)].
Definition p3_regions : smem := [ p3_stack_region; p3_len_region ].
Definition p3_SH : list shent := [ mkSHE 9 0 19744 ].
Definition p3_facts : facts := mkFacts
  [ (2%nat, mkAF (2^46) (2^47) 4); (9%nat, mkAF 0 (2^47 - 19744) 3);
    (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 0 16376 3); (34%nat, mkAF 0 96 0);
    (35%nat, mkAF 0 (2^64 - 1) 0); (36%nat, mkAF 0 (2^64 - 1) 0); (37%nat, mkAF 0 (2^64 - 1) 0);
    (38%nat, mkAF 0 (2^64 - 1) 0); (39%nat, mkAF 0 (2^64 - 1) 0) ]
  [ ] [ ].
Definition p3_regs : list sv :=
  sr_set (sr_set (sr_set sr_atoms (8%bv : bv 5) (SOff 9 16384))
    (19%bv : bv 5) pwe_sh3) (18%bv : bv 5) pwe_pad.
Definition ss_p3 : sstate := mkSS PWE_P3 p3_regs p3_regions None p3_facts.
