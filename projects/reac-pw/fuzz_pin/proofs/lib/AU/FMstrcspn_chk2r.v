(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: cgif_file_fuzzer lib/A/AE6y.v's walk of the wrapper's shadow check (with AE7e.v's entry registers), restated for the strlen wrapper of libreac/fuzz_disco: a0 = n - 1 and s1 = 1 at RC_ENTRY, the size test is decided by the engine, the code table adds the wrapper body, and the common-flags pointer and the strlen flag are read-only cells; module paths. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Rt/StrlenChk.v, with its module paths, addresses and numbers changed; 35 of its 231 lines of code are new or changed and 2300 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_identity/lib/A/FMstrlen_chk1.v at 6ebe35ba632; the symbolic runs are those of the strcspn wrapper's range check of the string, reac-pw/fuzz_pin.asan 0x42d88 .. 0x42de0 and its paths 0x42e98, 0x42fec .. 0x4301c and 0x43020 .. 0x43034, over tbl_cs (A/FMcs0.v): p is in s1, n - 1 in a0 and s5, the flags object in s7, the read-only cells are cs_rodata, and every run result is computed anew for this code. *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/FMstrcspn_chk2r.v of this library, for reac-pw/fuzz_pin's asan-ubsan image (fuzz_pin.asan-ubsan d6f83d301522) instead of its asan image (fuzz_pin.asan 3e4859aed23f): module paths lib.A -> lib.AU (the core files A<xyz> -> Y<xyz>); 2 address numerals moved to the same symbol + offset of the asan-ubsan image (each checked on that image); by hand, one comment: it names fuzz_pin.asan-ubsan. The comment lines above describe how lib/A/FMstrcspn_chk2r.v was made and quote the asan image's values; the code and comments below carry the asan-ubsan values. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.

From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.

From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.

Require Import
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.YB1v
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.YE34
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.YF0l
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.YF0m
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.YF0x
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.YB1w
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.YE20
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.YE2y.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require Import FMcs0.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YN01.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* The range check of the string [p, p + n) that the strcspn wrapper runs after musl strcspn returns r = n - 1:
   fuzz_pin.asan-ubsan 0x42d88 (CS2_ENTRY) to 0x42de0 (CS2_END, the epilogue).  At the entry s1 = p, a0 = s5 = n - 1,
   s7 = the runtime's flags object 0x133228.
     42d88 lbu a1, 0xf5(s7) (strict_string_checks, byte 5 of the const cell 0x133318, = 0) ; 42d8c s3 = a0
     42d90 bnez a1 (not taken) ; 42d94 s2 = s3 + 1 ; 42d98 a1 = ~s1 ; 42d9c bltu a1, s2 (wrap: the error path 0x42e30)
     42da0 a1 = 64 ; 42da4 bgeu s3, a1 (n > 64: 0x42e98 bnez s2 -> 0x43020)
     42da8-42ddc the two-word shadow test (the words holding the shadow bytes of s1 and of s1 + s3), bnez -> 0x42fec
     42fec-4301c the byte-exact test of the last granule (to 0x42de0 when its flag is 0, else 0x43020)
     43020-43034 a0 = s1, a1 = s2, jal 0x5437c (__asan_region_is_poisoned, returns 0 to 0x4302c), s1 = a0,
                 a0 = s5, beqz s1 -> 0x42de0.
   Each symbolic state below is computed for this code over tbl_cs. *)
Module CS2R.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* __asan_region_is_poisoned (0x5437c) opens a 0x40-byte frame below the wrapper's sp; the stretch model of
   __sanitizer::mem_is_zero (called from 0x544ec with sp = sp0 - 64) writes the 8 bytes below that: CHK_SCR = 72 *)
Definition STK : Z := 64.
Definition shreg1 (t : Z) : YP09.region :=
YP09.mkRegion (Some 32%nat) SB (SB + t + 1) SB SB
((if 0 <? t then [YP09.mkChunk SB (CZero t)] else []) ++ [YP09.mkChunk (SB + t) (CVal 1 (SOff 34 0))]).
Definition shregs2 : smem :=
[ YP09.mkRegion (Some 32%nat) SB (SB + 1) SB SB [YP09.mkChunk SB (CZero 1)];
YP09.mkRegion (Some 33%nat) SB (SB + 1) SB SB [YP09.mkChunk SB (CVal 1 (SOff 34 0))] ].
Definition aliases1 (t : Z) : list (sv * sv) :=
[ (SAlu ALU_SRL (SOff 9 0) (SLit 3), SOff 32 0);
(SAlu ALU_SRL (SAlu ALU_ADD (SOff 9 (-1)) (SOff 41 0)) (SLit 3), SOff 32 t) ].
Definition aliases2 : list (sv * sv) :=
[ (SAlu ALU_SRL (SOff 9 0) (SLit 3), SOff 32 0);
(SAlu ALU_SRL (SAlu ALU_ADD (SOff 9 (-1)) (SOff 41 0)) (SLit 3), SOff 33 0);
(SAlu ALU_AND (SOff 9 7) (SLit (-8)), SOff 37 0);
(SAlu ALU_AND (SAlu ALU_ADD (SOff 9 0) (SOff 41 0)) (SLit (-8)), SOff 38 0);
(SAlu ALU_SRL (SOff 37 0) (SLit 3), SOff 39 0);
(SAlu ALU_SRL (SOff 38 0) (SLit 3), SOff 40 0) ].
Definition stkR : YP09.region := YP09.mkRegion (Some 2%nat) (- STK) 0 (- STK) 0 [].
Definition factsR1 : list (nat * afact) :=
[(2%nat, mkAF (2^44) (2^47) 4); (9%nat, mkAF 0 (2^47) 0); (41%nat, mkAF 1 64 0); (32%nat, mkAF 0 (2^44) 0); (34%nat, mkAF 0 7 0)].
Definition factsR2L : list (nat * afact) :=
[(2%nat, mkAF (2^44) (2^47) 4); (9%nat, mkAF 0 0x7fff7fbe 0); (41%nat, mkAF 65 (2^32 - 1) 0);
(32%nat, mkAF 0 (2^44) 0); (33%nat, mkAF 0 (2^44) 0); (34%nat, mkAF 0 7 0);
(37%nat, mkAF 0 0x7fff7fc8 3); (38%nat, mkAF 0 0x7fff7fff 3); (39%nat, mkAF 0 (2^44) 0); (40%nat, mkAF 0 (2^44) 0)].
Definition factsR2H : list (nat * afact) :=
[(2%nat, mkAF (2^44) (2^47) 4); (9%nat, mkAF 0x10007fff8000 (2^47 - 66) 0); (41%nat, mkAF 65 (2^32 - 1) 0);
(32%nat, mkAF 0 (2^44) 0); (33%nat, mkAF 0 (2^44) 0); (34%nat, mkAF 0 7 0);
(37%nat, mkAF 0x10007fff8000 (2^47 - 1) 3); (38%nat, mkAF 0x10007fff8000 (2^47 - 1) 3); (39%nat, mkAF 0 (2^44) 0); (40%nat, mkAF 0 (2^44) 0)].
(* a0 = s5 = n - 1 (atom 41 is n), s7 = the flags object; every other register is its entry value *)
Definition regsS : list sv := Eval vm_compute in
(firstn 10 sr_atoms ++ [SOff 41 (-1)] ++ firstn 10 (skipn 11 sr_atoms) ++ [SOff 41 (-1)] ++ firstn 1 (skipn 22 sr_atoms) ++ [SLit CS_FLAGS] ++ skipn 24 sr_atoms).
Definition ssR1 (t : Z) : sstate := mkSS CS2_ENTRY regsS (stkR :: shreg1 t :: map ro_region cs_rodata) None (mkFacts factsR1 [] (aliases1 t)).
Definition ssR2L : sstate := mkSS CS2_ENTRY regsS (stkR :: shregs2 ++ map ro_region cs_rodata) None (mkFacts factsR2L [] aliases2).
Definition ssR2H : sstate := mkSS CS2_ENTRY regsS (stkR :: shregs2 ++ map ro_region cs_rodata) None (mkFacts factsR2H [] aliases2).
Definition RUN (s : sstate) := sym_runN tfibsegs tbl_cs FUEL s.
Definition RUNTO (s : sstate) := sym_run_toN tfibsegs tbl_cs FUEL CS2_END s.
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition AC (s : sstate) (c : branch_cond) (a b : sv) : sstate := YP06.add_cond s (mkAC c a b).
(* n <= 64, t = g1 - g0 shadow bytes between the first and the last granule (the states r1_t_..); n > 64 below or above the
   shadow gap (r2L_.., r2H_..); z / n: the shadow byte of the last granule is 0 / not 0 *)
Definition r1_0_e0 : sstate := Eval vm_compute in fst (RUN (ssR1 0)).
Lemma r_r1_0_0 : RUN (ssR1 0) = (r1_0_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 9 0) (SLit (-1))) (SOff 41 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_0_e1 : sstate := Eval vm_compute in fst (RUN (AC r1_0_e0 BC_GEU (RG r1_0_e0 11) (RG r1_0_e0 18))).
Lemma r_r1_0_1 : RUN (AC r1_0_e0 BC_GEU (RG r1_0_e0 11) (RG r1_0_e0 18)) = (r1_0_e1, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition r1_0_e2 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc r1_0_e1 [((13%bv : bv 5), SOff 35 0)] 0x42dd4) [((14%bv : bv 5), SOff 36 0)] 0x42dd8)).
Lemma r_r1_0_2 : RUN (set_regs_pc (set_regs_pc r1_0_e1 [((13%bv : bv 5), SOff 35 0)] 0x42dd4) [((14%bv : bv 5), SOff 36 0)] 0x42dd8) = (r1_0_e2, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_0z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC r1_0_e2 BC_EQ (RG r1_0_e2 13) (SLit 0))).
Lemma r_r1_0z_0 : RUNTO (AC r1_0_e2 BC_EQ (RG r1_0_e2 13) (SLit 0)) = (r1_0z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r1_0n_e0 : sstate := Eval vm_compute in fst (RUN (AC r1_0_e2 BC_NE (RG r1_0_e2 13) (SLit 0))).
Lemma r_r1_0n_0 : RUN (AC r1_0_e2 BC_NE (RG r1_0_e2 13) (SLit 0)) = (r1_0n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 0%nat 9 41 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_0n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC r1_0n_e0 BC_EQ (RG r1_0n_e0 11) (SLit 0))).
Lemma r_r1_0n_1 : RUNTO (AC r1_0n_e0 BC_EQ (RG r1_0n_e0 11) (SLit 0)) = (r1_0n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r1_1_e0 : sstate := Eval vm_compute in fst (RUN (ssR1 1)).
Lemma r_r1_1_0 : RUN (ssR1 1) = (r1_1_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 9 0) (SLit (-1))) (SOff 41 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_1_e1 : sstate := Eval vm_compute in fst (RUN (AC r1_1_e0 BC_GEU (RG r1_1_e0 11) (RG r1_1_e0 18))).
Lemma r_r1_1_1 : RUN (AC r1_1_e0 BC_GEU (RG r1_1_e0 11) (RG r1_1_e0 18)) = (r1_1_e1, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition r1_1_e2 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc r1_1_e1 [((13%bv : bv 5), SOff 35 0)] 0x42dd4) [((14%bv : bv 5), SOff 36 0)] 0x42dd8)).
Lemma r_r1_1_2 : RUN (set_regs_pc (set_regs_pc r1_1_e1 [((13%bv : bv 5), SOff 35 0)] 0x42dd4) [((14%bv : bv 5), SOff 36 0)] 0x42dd8) = (r1_1_e2, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_1z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC r1_1_e2 BC_EQ (RG r1_1_e2 13) (SLit 0))).
Lemma r_r1_1z_0 : RUNTO (AC r1_1_e2 BC_EQ (RG r1_1_e2 13) (SLit 0)) = (r1_1z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r1_1n_e0 : sstate := Eval vm_compute in fst (RUN (AC r1_1_e2 BC_NE (RG r1_1_e2 13) (SLit 0))).
Lemma r_r1_1n_0 : RUN (AC r1_1_e2 BC_NE (RG r1_1_e2 13) (SLit 0)) = (r1_1n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 1%nat 9 41 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_1n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC r1_1n_e0 BC_EQ (RG r1_1n_e0 11) (SLit 0))).
Lemma r_r1_1n_1 : RUNTO (AC r1_1n_e0 BC_EQ (RG r1_1n_e0 11) (SLit 0)) = (r1_1n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r1_2_e0 : sstate := Eval vm_compute in fst (RUN (ssR1 2)).
Lemma r_r1_2_0 : RUN (ssR1 2) = (r1_2_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 9 0) (SLit (-1))) (SOff 41 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_2_e1 : sstate := Eval vm_compute in fst (RUN (AC r1_2_e0 BC_GEU (RG r1_2_e0 11) (RG r1_2_e0 18))).
Lemma r_r1_2_1 : RUN (AC r1_2_e0 BC_GEU (RG r1_2_e0 11) (RG r1_2_e0 18)) = (r1_2_e1, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition r1_2_e2 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc r1_2_e1 [((13%bv : bv 5), SOff 35 0)] 0x42dd4) [((14%bv : bv 5), SOff 36 0)] 0x42dd8)).
Lemma r_r1_2_2 : RUN (set_regs_pc (set_regs_pc r1_2_e1 [((13%bv : bv 5), SOff 35 0)] 0x42dd4) [((14%bv : bv 5), SOff 36 0)] 0x42dd8) = (r1_2_e2, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_2z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC r1_2_e2 BC_EQ (RG r1_2_e2 13) (SLit 0))).
Lemma r_r1_2z_0 : RUNTO (AC r1_2_e2 BC_EQ (RG r1_2_e2 13) (SLit 0)) = (r1_2z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r1_2n_e0 : sstate := Eval vm_compute in fst (RUN (AC r1_2_e2 BC_NE (RG r1_2_e2 13) (SLit 0))).
Lemma r_r1_2n_0 : RUN (AC r1_2_e2 BC_NE (RG r1_2_e2 13) (SLit 0)) = (r1_2n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 2%nat 9 41 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_2n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC r1_2n_e0 BC_EQ (RG r1_2n_e0 11) (SLit 0))).
Lemma r_r1_2n_1 : RUNTO (AC r1_2n_e0 BC_EQ (RG r1_2n_e0 11) (SLit 0)) = (r1_2n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r1_3_e0 : sstate := Eval vm_compute in fst (RUN (ssR1 3)).
Lemma r_r1_3_0 : RUN (ssR1 3) = (r1_3_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 9 0) (SLit (-1))) (SOff 41 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_3_e1 : sstate := Eval vm_compute in fst (RUN (AC r1_3_e0 BC_GEU (RG r1_3_e0 11) (RG r1_3_e0 18))).
Lemma r_r1_3_1 : RUN (AC r1_3_e0 BC_GEU (RG r1_3_e0 11) (RG r1_3_e0 18)) = (r1_3_e1, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition r1_3_e2 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc r1_3_e1 [((13%bv : bv 5), SOff 35 0)] 0x42dd4) [((14%bv : bv 5), SOff 36 0)] 0x42dd8)).
Lemma r_r1_3_2 : RUN (set_regs_pc (set_regs_pc r1_3_e1 [((13%bv : bv 5), SOff 35 0)] 0x42dd4) [((14%bv : bv 5), SOff 36 0)] 0x42dd8) = (r1_3_e2, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_3z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC r1_3_e2 BC_EQ (RG r1_3_e2 13) (SLit 0))).
Lemma r_r1_3z_0 : RUNTO (AC r1_3_e2 BC_EQ (RG r1_3_e2 13) (SLit 0)) = (r1_3z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r1_3n_e0 : sstate := Eval vm_compute in fst (RUN (AC r1_3_e2 BC_NE (RG r1_3_e2 13) (SLit 0))).
Lemma r_r1_3n_0 : RUN (AC r1_3_e2 BC_NE (RG r1_3_e2 13) (SLit 0)) = (r1_3n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 3%nat 9 41 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_3n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC r1_3n_e0 BC_EQ (RG r1_3n_e0 11) (SLit 0))).
Lemma r_r1_3n_1 : RUNTO (AC r1_3n_e0 BC_EQ (RG r1_3n_e0 11) (SLit 0)) = (r1_3n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r1_4_e0 : sstate := Eval vm_compute in fst (RUN (ssR1 4)).
Lemma r_r1_4_0 : RUN (ssR1 4) = (r1_4_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 9 0) (SLit (-1))) (SOff 41 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_4_e1 : sstate := Eval vm_compute in fst (RUN (AC r1_4_e0 BC_GEU (RG r1_4_e0 11) (RG r1_4_e0 18))).
Lemma r_r1_4_1 : RUN (AC r1_4_e0 BC_GEU (RG r1_4_e0 11) (RG r1_4_e0 18)) = (r1_4_e1, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition r1_4_e2 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc r1_4_e1 [((13%bv : bv 5), SOff 35 0)] 0x42dd4) [((14%bv : bv 5), SOff 36 0)] 0x42dd8)).
Lemma r_r1_4_2 : RUN (set_regs_pc (set_regs_pc r1_4_e1 [((13%bv : bv 5), SOff 35 0)] 0x42dd4) [((14%bv : bv 5), SOff 36 0)] 0x42dd8) = (r1_4_e2, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_4z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC r1_4_e2 BC_EQ (RG r1_4_e2 13) (SLit 0))).
Lemma r_r1_4z_0 : RUNTO (AC r1_4_e2 BC_EQ (RG r1_4_e2 13) (SLit 0)) = (r1_4z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r1_4n_e0 : sstate := Eval vm_compute in fst (RUN (AC r1_4_e2 BC_NE (RG r1_4_e2 13) (SLit 0))).
Lemma r_r1_4n_0 : RUN (AC r1_4_e2 BC_NE (RG r1_4_e2 13) (SLit 0)) = (r1_4n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 4%nat 9 41 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_4n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC r1_4n_e0 BC_EQ (RG r1_4n_e0 11) (SLit 0))).
Lemma r_r1_4n_1 : RUNTO (AC r1_4n_e0 BC_EQ (RG r1_4n_e0 11) (SLit 0)) = (r1_4n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r1_5_e0 : sstate := Eval vm_compute in fst (RUN (ssR1 5)).
Lemma r_r1_5_0 : RUN (ssR1 5) = (r1_5_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 9 0) (SLit (-1))) (SOff 41 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_5_e1 : sstate := Eval vm_compute in fst (RUN (AC r1_5_e0 BC_GEU (RG r1_5_e0 11) (RG r1_5_e0 18))).
Lemma r_r1_5_1 : RUN (AC r1_5_e0 BC_GEU (RG r1_5_e0 11) (RG r1_5_e0 18)) = (r1_5_e1, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition r1_5_e2 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc r1_5_e1 [((13%bv : bv 5), SOff 35 0)] 0x42dd4) [((14%bv : bv 5), SOff 36 0)] 0x42dd8)).
Lemma r_r1_5_2 : RUN (set_regs_pc (set_regs_pc r1_5_e1 [((13%bv : bv 5), SOff 35 0)] 0x42dd4) [((14%bv : bv 5), SOff 36 0)] 0x42dd8) = (r1_5_e2, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_5z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC r1_5_e2 BC_EQ (RG r1_5_e2 13) (SLit 0))).
Lemma r_r1_5z_0 : RUNTO (AC r1_5_e2 BC_EQ (RG r1_5_e2 13) (SLit 0)) = (r1_5z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r1_5n_e0 : sstate := Eval vm_compute in fst (RUN (AC r1_5_e2 BC_NE (RG r1_5_e2 13) (SLit 0))).
Lemma r_r1_5n_0 : RUN (AC r1_5_e2 BC_NE (RG r1_5_e2 13) (SLit 0)) = (r1_5n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 5%nat 9 41 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_5n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC r1_5n_e0 BC_EQ (RG r1_5n_e0 11) (SLit 0))).
Lemma r_r1_5n_1 : RUNTO (AC r1_5n_e0 BC_EQ (RG r1_5n_e0 11) (SLit 0)) = (r1_5n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r1_6_e0 : sstate := Eval vm_compute in fst (RUN (ssR1 6)).
Lemma r_r1_6_0 : RUN (ssR1 6) = (r1_6_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 9 0) (SLit (-1))) (SOff 41 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_6_e1 : sstate := Eval vm_compute in fst (RUN (AC r1_6_e0 BC_GEU (RG r1_6_e0 11) (RG r1_6_e0 18))).
Lemma r_r1_6_1 : RUN (AC r1_6_e0 BC_GEU (RG r1_6_e0 11) (RG r1_6_e0 18)) = (r1_6_e1, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition r1_6_e2 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc r1_6_e1 [((13%bv : bv 5), SOff 35 0)] 0x42dd4) [((14%bv : bv 5), SOff 36 0)] 0x42dd8)).
Lemma r_r1_6_2 : RUN (set_regs_pc (set_regs_pc r1_6_e1 [((13%bv : bv 5), SOff 35 0)] 0x42dd4) [((14%bv : bv 5), SOff 36 0)] 0x42dd8) = (r1_6_e2, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_6z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC r1_6_e2 BC_EQ (RG r1_6_e2 13) (SLit 0))).
Lemma r_r1_6z_0 : RUNTO (AC r1_6_e2 BC_EQ (RG r1_6_e2 13) (SLit 0)) = (r1_6z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r1_6n_e0 : sstate := Eval vm_compute in fst (RUN (AC r1_6_e2 BC_NE (RG r1_6_e2 13) (SLit 0))).
Lemma r_r1_6n_0 : RUN (AC r1_6_e2 BC_NE (RG r1_6_e2 13) (SLit 0)) = (r1_6n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 6%nat 9 41 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_6n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC r1_6n_e0 BC_EQ (RG r1_6n_e0 11) (SLit 0))).
Lemma r_r1_6n_1 : RUNTO (AC r1_6n_e0 BC_EQ (RG r1_6n_e0 11) (SLit 0)) = (r1_6n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r1_7_e0 : sstate := Eval vm_compute in fst (RUN (ssR1 7)).
Lemma r_r1_7_0 : RUN (ssR1 7) = (r1_7_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 9 0) (SLit (-1))) (SOff 41 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_7_e1 : sstate := Eval vm_compute in fst (RUN (AC r1_7_e0 BC_GEU (RG r1_7_e0 11) (RG r1_7_e0 18))).
Lemma r_r1_7_1 : RUN (AC r1_7_e0 BC_GEU (RG r1_7_e0 11) (RG r1_7_e0 18)) = (r1_7_e1, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition r1_7_e2 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc r1_7_e1 [((13%bv : bv 5), SOff 35 0)] 0x42dd4) [((14%bv : bv 5), SOff 36 0)] 0x42dd8)).
Lemma r_r1_7_2 : RUN (set_regs_pc (set_regs_pc r1_7_e1 [((13%bv : bv 5), SOff 35 0)] 0x42dd4) [((14%bv : bv 5), SOff 36 0)] 0x42dd8) = (r1_7_e2, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_7z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC r1_7_e2 BC_EQ (RG r1_7_e2 13) (SLit 0))).
Lemma r_r1_7z_0 : RUNTO (AC r1_7_e2 BC_EQ (RG r1_7_e2 13) (SLit 0)) = (r1_7z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r1_7n_e0 : sstate := Eval vm_compute in fst (RUN (AC r1_7_e2 BC_NE (RG r1_7_e2 13) (SLit 0))).
Lemma r_r1_7n_0 : RUN (AC r1_7_e2 BC_NE (RG r1_7_e2 13) (SLit 0)) = (r1_7n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 7%nat 9 41 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_7n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC r1_7n_e0 BC_EQ (RG r1_7n_e0 11) (SLit 0))).
Lemma r_r1_7n_1 : RUNTO (AC r1_7n_e0 BC_EQ (RG r1_7n_e0 11) (SLit 0)) = (r1_7n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r1_8_e0 : sstate := Eval vm_compute in fst (RUN (ssR1 8)).
Lemma r_r1_8_0 : RUN (ssR1 8) = (r1_8_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 9 0) (SLit (-1))) (SOff 41 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_8_e1 : sstate := Eval vm_compute in fst (RUN (AC r1_8_e0 BC_GEU (RG r1_8_e0 11) (RG r1_8_e0 18))).
Lemma r_r1_8_1 : RUN (AC r1_8_e0 BC_GEU (RG r1_8_e0 11) (RG r1_8_e0 18)) = (r1_8_e1, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition r1_8_e2 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc r1_8_e1 [((13%bv : bv 5), SOff 35 0)] 0x42dd4) [((14%bv : bv 5), SOff 36 0)] 0x42dd8)).
Lemma r_r1_8_2 : RUN (set_regs_pc (set_regs_pc r1_8_e1 [((13%bv : bv 5), SOff 35 0)] 0x42dd4) [((14%bv : bv 5), SOff 36 0)] 0x42dd8) = (r1_8_e2, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_8z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC r1_8_e2 BC_EQ (RG r1_8_e2 13) (SLit 0))).
Lemma r_r1_8z_0 : RUNTO (AC r1_8_e2 BC_EQ (RG r1_8_e2 13) (SLit 0)) = (r1_8z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r1_8n_e0 : sstate := Eval vm_compute in fst (RUN (AC r1_8_e2 BC_NE (RG r1_8_e2 13) (SLit 0))).
Lemma r_r1_8n_0 : RUN (AC r1_8_e2 BC_NE (RG r1_8_e2 13) (SLit 0)) = (r1_8n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 8%nat 9 41 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_8n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC r1_8n_e0 BC_EQ (RG r1_8n_e0 11) (SLit 0))).
Lemma r_r1_8n_1 : RUNTO (AC r1_8n_e0 BC_EQ (RG r1_8n_e0 11) (SLit 0)) = (r1_8n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r2L_e0 : sstate := Eval vm_compute in fst (RUN (ssR2L)).
Lemma r_r2L_0 : RUN (ssR2L) = (r2L_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 9 0) (SLit (-1))) (SOff 41 0))). Proof. vm_compute. reflexivity. Qed.
Definition r2L_e1 : sstate := Eval vm_compute in fst (RUN (AC r2L_e0 BC_GEU (RG r2L_e0 11) (RG r2L_e0 18))).
Lemma r_r2L_1 : RUN (AC r2L_e0 BC_GEU (RG r2L_e0 11) (RG r2L_e0 18)) = (r2L_e1, RS_stopped (SR_branch BC_GEU (SLit 2147450879) (SAlu ALU_ADD (SOff 9 0) (SOff 41 0)))). Proof. vm_compute. reflexivity. Qed.
Definition r2L_e2 : sstate := Eval vm_compute in fst (RUN (AC r2L_e1 BC_GEU (SLit 2147450879) (RG r2L_e1 18))).
Lemma r_r2L_2 : RUN (AC r2L_e1 BC_GEU (SLit 2147450879) (RG r2L_e1 18)) = (r2L_e2, RS_stopped (SR_branch BC_GEU (SOff 9 0) (SAlu ALU_ADD (SOff 9 0) (SOff 41 0)))). Proof. vm_compute. reflexivity. Qed.
Definition r2L_e3 : sstate := Eval vm_compute in fst (RUN (AC r2L_e2 BC_LTU (RG r2L_e2 8) (RG r2L_e2 18))).
Lemma r_r2L_3 : RUN (AC r2L_e2 BC_LTU (RG r2L_e2 8) (RG r2L_e2 18)) = (r2L_e3, RS_stopped (SR_branch BC_EQ (SOff 34 0) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r2Lz_e0 : sstate := Eval vm_compute in fst (RUN (AC r2L_e3 BC_EQ (RG r2L_e3 11) (SLit 0))).
Lemma r_r2Lz_0 : RUN (AC r2L_e3 BC_EQ (RG r2L_e3 11) (SLit 0)) = (r2Lz_e0, RS_stopped (SR_branch BC_GEU (SOff 39 2147450880) (SOff 40 2147450880))). Proof. vm_compute. reflexivity. Qed.
Definition r2Lz_e1 : sstate := Eval vm_compute in fst (RUN (AC r2Lz_e0 BC_LTU (RG r2Lz_e0 19) (RG r2Lz_e0 10))).
Lemma r_r2Lz_1 : RUN (AC r2Lz_e0 BC_LTU (RG r2Lz_e0 19) (RG r2Lz_e0 10)) = (r2Lz_e1, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition r2Lz_e2 : sstate := Eval vm_compute in fst (RUNTO (ss_after_mz r2Lz_e1 (ss_mem r2Lz_e1) 56 0x544f0)).
Lemma r_r2Lz_2 : RUNTO (ss_after_mz r2Lz_e1 (ss_mem r2Lz_e1) 56 0x544f0) = (r2Lz_e2, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r2Ln_e0 : sstate := Eval vm_compute in fst (RUN (AC r2L_e3 BC_NE (RG r2L_e3 11) (SLit 0))).
Lemma r_r2Ln_0 : RUN (AC r2L_e3 BC_NE (RG r2L_e3 11) (SLit 0)) = (r2Ln_e0, RS_stopped (SR_branch BC_LT (SAlu ALU_AND (SAlu ALU_ADD (SOff 9 (-1)) (SOff 41 0)) (SLit 7)) (SOff 34 0))). Proof. vm_compute. reflexivity. Qed.
Definition r2Ln_e1 : sstate := Eval vm_compute in fst (RUN (AC r2Ln_e0 BC_LT (RG r2Ln_e0 12) (RG r2Ln_e0 11))).
Lemma r_r2Ln_1 : RUN (AC r2Ln_e0 BC_LT (RG r2Ln_e0 12) (RG r2Ln_e0 11)) = (r2Ln_e1, RS_stopped (SR_branch BC_GEU (SOff 39 2147450880) (SOff 40 2147450880))). Proof. vm_compute. reflexivity. Qed.
Definition r2Ln_e2 : sstate := Eval vm_compute in fst (RUN (AC r2Ln_e1 BC_LTU (RG r2Ln_e1 19) (RG r2Ln_e1 10))).
Lemma r_r2Ln_2 : RUN (AC r2Ln_e1 BC_LTU (RG r2Ln_e1 19) (RG r2Ln_e1 10)) = (r2Ln_e2, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition r2Ln_e3 : sstate := Eval vm_compute in fst (RUNTO (ss_after_mz r2Ln_e2 (ss_mem r2Ln_e2) 56 0x544f0)).
Lemma r_r2Ln_3 : RUNTO (ss_after_mz r2Ln_e2 (ss_mem r2Ln_e2) 56 0x544f0) = (r2Ln_e3, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r2H_e0 : sstate := Eval vm_compute in fst (RUN (ssR2H)).
Lemma r_r2H_0 : RUN (ssR2H) = (r2H_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 9 0) (SLit (-1))) (SOff 41 0))). Proof. vm_compute. reflexivity. Qed.
Definition r2H_e1 : sstate := Eval vm_compute in fst (RUN (AC r2H_e0 BC_GEU (RG r2H_e0 11) (RG r2H_e0 18))).
Lemma r_r2H_1 : RUN (AC r2H_e0 BC_GEU (RG r2H_e0 11) (RG r2H_e0 18)) = (r2H_e1, RS_stopped (SR_branch BC_LTU (SLit 140737488355327) (SAlu ALU_ADD (SOff 9 0) (SOff 41 0)))). Proof. vm_compute. reflexivity. Qed.
Definition r2H_e2 : sstate := Eval vm_compute in fst (RUN (AC r2H_e1 BC_GEU (SLit 140737488355327) (RG r2H_e1 18))).
Lemma r_r2H_2 : RUN (AC r2H_e1 BC_GEU (SLit 140737488355327) (RG r2H_e1 18)) = (r2H_e2, RS_stopped (SR_branch BC_GEU (SOff 9 0) (SAlu ALU_ADD (SOff 9 0) (SOff 41 0)))). Proof. vm_compute. reflexivity. Qed.
Definition r2H_e3 : sstate := Eval vm_compute in fst (RUN (AC r2H_e2 BC_LTU (RG r2H_e2 8) (RG r2H_e2 18))).
Lemma r_r2H_3 : RUN (AC r2H_e2 BC_LTU (RG r2H_e2 8) (RG r2H_e2 18)) = (r2H_e3, RS_stopped (SR_branch BC_EQ (SOff 34 0) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r2Hz_e0 : sstate := Eval vm_compute in fst (RUN (AC r2H_e3 BC_EQ (RG r2H_e3 11) (SLit 0))).
Lemma r_r2Hz_0 : RUN (AC r2H_e3 BC_EQ (RG r2H_e3 11) (SLit 0)) = (r2Hz_e0, RS_stopped (SR_branch BC_GEU (SOff 39 2147450880) (SOff 40 2147450880))). Proof. vm_compute. reflexivity. Qed.
Definition r2Hz_e1 : sstate := Eval vm_compute in fst (RUN (AC r2Hz_e0 BC_LTU (RG r2Hz_e0 19) (RG r2Hz_e0 10))).
Lemma r_r2Hz_1 : RUN (AC r2Hz_e0 BC_LTU (RG r2Hz_e0 19) (RG r2Hz_e0 10)) = (r2Hz_e1, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition r2Hz_e2 : sstate := Eval vm_compute in fst (RUNTO (ss_after_mz r2Hz_e1 (ss_mem r2Hz_e1) 56 0x544f0)).
Lemma r_r2Hz_2 : RUNTO (ss_after_mz r2Hz_e1 (ss_mem r2Hz_e1) 56 0x544f0) = (r2Hz_e2, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r2Hn_e0 : sstate := Eval vm_compute in fst (RUN (AC r2H_e3 BC_NE (RG r2H_e3 11) (SLit 0))).
Lemma r_r2Hn_0 : RUN (AC r2H_e3 BC_NE (RG r2H_e3 11) (SLit 0)) = (r2Hn_e0, RS_stopped (SR_branch BC_LT (SAlu ALU_AND (SAlu ALU_ADD (SOff 9 (-1)) (SOff 41 0)) (SLit 7)) (SOff 34 0))). Proof. vm_compute. reflexivity. Qed.
Definition r2Hn_e1 : sstate := Eval vm_compute in fst (RUN (AC r2Hn_e0 BC_LT (RG r2Hn_e0 12) (RG r2Hn_e0 11))).
Lemma r_r2Hn_1 : RUN (AC r2Hn_e0 BC_LT (RG r2Hn_e0 12) (RG r2Hn_e0 11)) = (r2Hn_e1, RS_stopped (SR_branch BC_GEU (SOff 39 2147450880) (SOff 40 2147450880))). Proof. vm_compute. reflexivity. Qed.
Definition r2Hn_e2 : sstate := Eval vm_compute in fst (RUN (AC r2Hn_e1 BC_LTU (RG r2Hn_e1 19) (RG r2Hn_e1 10))).
Lemma r_r2Hn_2 : RUN (AC r2Hn_e1 BC_LTU (RG r2Hn_e1 19) (RG r2Hn_e1 10)) = (r2Hn_e2, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition r2Hn_e3 : sstate := Eval vm_compute in fst (RUNTO (ss_after_mz r2Hn_e2 (ss_mem r2Hn_e2) 56 0x544f0)).
Lemma r_r2Hn_3 : RUNTO (ss_after_mz r2Hn_e2 (ss_mem r2Hn_e2) 56 0x544f0) = (r2Hn_e3, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (RG ss r) v.
(* the region writes s1, s2 and s3 (and a0 .. a7, t0); s5 and s7 keep the values n - 1 and the flags object they
   hold at the entry, a0 is n - 1 again at the end; every other callee-saved register keeps its entry value *)
Definition KEPT : list Z := [2; 3; 4; 8; 20; 22; 24; 25; 26; 27].
Definition shapeR (ss : sstate) : bool :=
(ss_pc ss =? CS2_END) &&
match ss_mem ss with r :: _ => obase_eqb (YP09.r_base r) (Some 2%nat) && (YP09.r_wlo r =? - STK) && (YP09.r_whi r =? 0) | [] => false end &&
reg_is ss 10 (SOff 41 (-1)) && reg_is ss 21 (SOff 41 (-1)) && reg_is ss 23 (SLit CS_FLAGS) &&
forallb (fun r => reg_is ss r (SOff (Z.to_nat r) 0)) KEPT.
Definition win_chk (rs : smem) : bool := forallb (fun t => win_eqb t (Some 2%nat, - STK, 0) || (snd t <=? snd (fst t))) (windows rs).
Lemma md_wvb_gen : forall m : Model, m = with_vm_backing (m_vm_lazy m) (m_vm_materialized m) m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
End e.
End CS2R.
