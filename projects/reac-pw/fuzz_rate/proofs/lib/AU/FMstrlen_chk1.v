(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: cgif_file_fuzzer lib/A/AE6y.v's walk of the wrapper's shadow check (with AE7e.v's entry registers), restated for the strlen wrapper of libreac/fuzz_disco: a0 = n - 1 and s1 = 1 at RC_ENTRY, the size test is decided by the engine, the code table adds the wrapper body, and the common-flags pointer and the strlen flag are read-only cells; module paths. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Rt/StrlenChk.v, with its module paths and addresses changed; 58 of its 275 lines of code are new or changed and 2279 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: relocated from port-fm's cgif_file_fuzzer-coordinate copy (origin/cold/port-fm-rtscan f8664b31b9c, proofs/cgif/cgif_file_fuzzer/lib/A/FMstrlen_chk1.v) to fuzz_identity.asan by an address map recorded by the porting lane; module paths, the record class TfibSyms (unchanged), YA0m import dropped. *)
(* Modified by Theorem Labs, 2026-10-29: for r-identity's acceptance (cold/h-rw-ide-6-wrapacc), the record class is TfibSyms, not IdentTfibSyms (DECISIONS-LIVE 05:31Z: TfibSyms in both A and B, no --rename), and the core modules are Required by full path at the applied A core's names (lib/A/A*.v, lib/Reusable/YA0m, YE08, YE21). *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_identity/lib/A/FMstrlen_chk1.v at origin/ossv/recipes 2d2ff01bb6f2 (donor image sha256 c954b804786c); module paths changed and addresses moved to reac-pw/fuzz_rate's ASan build (fuzz_rate.asan sha256 22bc8613d780) by port_core.py 1e42da8952ec, cross-checked numeral by numeral with alreloc a5c53bb2bed4 (ledger provenance/reloc/A-Rt-Strlen.tsv). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/FMstrlen_chk1.v at eace7ccc610b, derived by derive_y.py: addresses moved from reac-pw/fuzz_rate's asan image (image A) to its asan-ubsan image (image B), the image module Asan -> AsanUbsan; the Modified-by lines above describe how lib/A/FMstrlen_chk1.v was made and quote that file's image-A values; the code below carries image B's values; a numeral in a comment that quotes the donor's text (lib/A/FMstrlen_chk1.v keeps its donor's comment text) is kept as lib/A/FMstrlen_chk1.v writes it. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.

From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.

From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.

Require Import
  OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU.YB1v
  OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU.YE34
  OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU.YF0l
  OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU.YF0m
  OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU.YF0x
  OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU.YB1w
  OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU.YE20
  OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU.YE2y.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import FMsl0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN01.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* The range check that the strlen interceptor runs after musl strlen returns: fuzz_identity.asan 0x4226c (RC_ENTRY,
   the return address of the call through the slot 0x9e0b0) to 0x422d4 (RC_END, the epilogue).  26 instructions,
   listed here with port-fm's cgif_file.asan addresses (fuzz_identity.asan = cgif + 0x894):
     419d8 beqz s1 ; 419dc-e0 s3 = *0x9c3a0 ; 419e4 lbu a1, 0xfb(s3) ; 419e8 beqz a1
     419ec s1 = a0 + 1 ; 419f0 a1 = ~s2 ; 419f4-f8 s4 = s0 - 0x858 ; 419fc bltu a1, s1 (wrap: slow path)
     41a00 a1 = 64 ; 41a04 bgeu a0, a1 (length >= 64: __asan_region_is_poisoned 0x543d4 through 0x4239c)
     41a08-41a3c the two-granule shadow test (the words holding the shadow bytes of s2 and of s2 + a0), bnez -> 0x423ac
   The structure follows the strnlen interceptor's check (donor A/AE7e.v); every symbolic state below is computed
   anew for this region over tbl_sl (A/FMsl0.v), which holds the strlen interceptor body. *)
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition RC_ENTRY : Z := 0x422cc.
Definition RC_END : Z := 0x42334.
(* __asan_region_is_poisoned (0x543d4) opens a 0x40-byte frame below the wrapper's sp; the stretch model of
   __sanitizer::mem_is_zero (called from 0x54544 with sp = sp0 - 64) writes the 8 bytes below that *)
Definition RC_STK : Z := 64.
Definition RC_SCR : Z := 72.
Definition shreg1 (t : Z) : YP09.region :=
YP09.mkRegion (Some 32%nat) SB (SB + t + 1) SB SB
((if 0 <? t then [YP09.mkChunk SB (CZero t)] else []) ++ [YP09.mkChunk (SB + t) (CVal 1 (SOff 34 0))]).
Definition shregs2 : smem :=
[ YP09.mkRegion (Some 32%nat) SB (SB + 1) SB SB [YP09.mkChunk SB (CZero 1)];
YP09.mkRegion (Some 33%nat) SB (SB + 1) SB SB [YP09.mkChunk SB (CVal 1 (SOff 34 0))] ].
Definition aliases1 (t : Z) : list (sv * sv) :=
[ (SAlu ALU_SRL (SOff 18 0) (SLit 3), SOff 32 0);
(SAlu ALU_SRL (SAlu ALU_ADD (SOff 18 (-1)) (SOff 41 0)) (SLit 3), SOff 32 t) ].
Definition aliases2 : list (sv * sv) :=
[ (SAlu ALU_SRL (SOff 18 0) (SLit 3), SOff 32 0);
(SAlu ALU_SRL (SAlu ALU_ADD (SOff 18 (-1)) (SOff 41 0)) (SLit 3), SOff 33 0);
(SAlu ALU_AND (SOff 18 7) (SLit (-8)), SOff 37 0);
(SAlu ALU_AND (SAlu ALU_ADD (SOff 18 0) (SOff 41 0)) (SLit (-8)), SOff 38 0);
(SAlu ALU_SRL (SOff 37 0) (SLit 3), SOff 39 0);
(SAlu ALU_SRL (SOff 38 0) (SLit 3), SOff 40 0) ].
Definition stkR : YP09.region := YP09.mkRegion (Some 2%nat) (- RC_STK) 0 (- RC_STK) 0 [].
Definition factsR1 : list (nat * afact) :=
[(2%nat, mkAF (2^44) (2^47) 4); (18%nat, mkAF 0 (2^47) 0); (41%nat, mkAF 1 64 0); (32%nat, mkAF 0 (2^44) 0); (34%nat, mkAF 0 7 0)].
Definition factsR2L : list (nat * afact) :=
[(2%nat, mkAF (2^44) (2^47) 4); (18%nat, mkAF 0 0x7fff7fbe 0); (41%nat, mkAF 65 (2^32 - 1) 0);
(32%nat, mkAF 0 (2^44) 0); (33%nat, mkAF 0 (2^44) 0); (34%nat, mkAF 0 7 0);
(37%nat, mkAF 0 0x7fff7fc8 3); (38%nat, mkAF 0 0x7fff7fff 3); (39%nat, mkAF 0 (2^44) 0); (40%nat, mkAF 0 (2^44) 0)].
Definition factsR2H : list (nat * afact) :=
[(2%nat, mkAF (2^44) (2^47) 4); (18%nat, mkAF 0x10007fff8000 (2^47 - 66) 0); (41%nat, mkAF 65 (2^32 - 1) 0);
(32%nat, mkAF 0 (2^44) 0); (33%nat, mkAF 0 (2^44) 0); (34%nat, mkAF 0 7 0);
(37%nat, mkAF 0x10007fff8000 (2^47 - 1) 3); (38%nat, mkAF 0x10007fff8000 (2^47 - 1) 3); (39%nat, mkAF 0 (2^44) 0); (40%nat, mkAF 0 (2^44) 0)].
Definition regsS : list sv := Eval vm_compute in (firstn 9 sr_atoms ++ [SLit 1; SOff 41 (-1)] ++ skipn 11 sr_atoms).
(* the slot 0x9c3a0 holds the runtime's flags object 0x136ae8; its byte 0x136be3 (offset 0xfb) is 1 *)
Definition sl_rodata : list (Z * Z * list (Z * BinNums.N * Z)) := icpt_rodata ++ [(0x9c160, 8, [(0, 8%N, 0x136a68)]); (0x136b63, 1, [(0, 1%N, 1)])].
Lemma sl_rodata_chk : forall ly, rodata_chk ly sl_rodata = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Definition ssR1 (t : Z) : sstate := mkSS RC_ENTRY regsS (stkR :: shreg1 t :: map ro_region sl_rodata) None (mkFacts factsR1 [] (aliases1 t)).
Definition ssR2L : sstate := mkSS RC_ENTRY regsS (stkR :: shregs2 ++ map ro_region sl_rodata) None (mkFacts factsR2L [] aliases2).
Definition ssR2H : sstate := mkSS RC_ENTRY regsS (stkR :: shregs2 ++ map ro_region sl_rodata) None (mkFacts factsR2H [] aliases2).
Definition RUN (s : sstate) := sym_runN tfibsegs tbl_sl FUEL s.
Definition RUNTO (s : sstate) := sym_run_toN tfibsegs tbl_sl FUEL RC_END s.
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition AC (s : sstate) (c : branch_cond) (a b : sv) : sstate := YP06.add_cond s (mkAC c a b).
(* n <= 64, t = g1 - g0 shadow bytes between the first and the last granule: the wrap test stops the run, the
   length test 0x42298 is decided from the fact 1 <= n <= 64, the run stops at the load 0x422c4 of the aligned word
   holding the first shadow byte; the two loads are done by sl_ld8 (atoms 35, 36); the or of the two words decides
   the byte-exact path 0x423ac, whose flag (a0) is the qc_flag of YE2y. *)
Definition r1_0_e0 : sstate := Eval vm_compute in fst (RUN (ssR1 0)).
Lemma r_r1_0_0 : RUN (ssR1 0) = (r1_0_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 18 0) (SLit (-1))) (SOff 41 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_0_e1 : sstate := Eval vm_compute in fst (RUN (AC r1_0_e0 BC_GEU (RG r1_0_e0 11) (RG r1_0_e0 9))).
Lemma r_r1_0_1 : RUN (AC r1_0_e0 BC_GEU (RG r1_0_e0 11) (RG r1_0_e0 9)) = (r1_0_e1, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition r1_0_e2 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc r1_0_e1 [((14%bv : bv 5), SOff 35 0)] 0x42328) [((15%bv : bv 5), SOff 36 0)] 0x4232c)).
Lemma r_r1_0_2 : RUN (set_regs_pc (set_regs_pc r1_0_e1 [((14%bv : bv 5), SOff 35 0)] 0x42328) [((15%bv : bv 5), SOff 36 0)] 0x4232c) = (r1_0_e2, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_0z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC r1_0_e2 BC_EQ (RG r1_0_e2 14) (SLit 0))).
Lemma r_r1_0z_0 : RUNTO (AC r1_0_e2 BC_EQ (RG r1_0_e2 14) (SLit 0)) = (r1_0z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r1_0n_e0 : sstate := Eval vm_compute in fst (RUN (AC r1_0_e2 BC_NE (RG r1_0_e2 14) (SLit 0))).
Lemma r_r1_0n_0 : RUN (AC r1_0_e2 BC_NE (RG r1_0_e2 14) (SLit 0)) = (r1_0n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 0%nat 18 41 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_0n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC r1_0n_e0 BC_EQ (RG r1_0n_e0 10) (SLit 0))).
Lemma r_r1_0n_1 : RUNTO (AC r1_0n_e0 BC_EQ (RG r1_0n_e0 10) (SLit 0)) = (r1_0n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r1_1_e0 : sstate := Eval vm_compute in fst (RUN (ssR1 1)).
Lemma r_r1_1_0 : RUN (ssR1 1) = (r1_1_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 18 0) (SLit (-1))) (SOff 41 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_1_e1 : sstate := Eval vm_compute in fst (RUN (AC r1_1_e0 BC_GEU (RG r1_1_e0 11) (RG r1_1_e0 9))).
Lemma r_r1_1_1 : RUN (AC r1_1_e0 BC_GEU (RG r1_1_e0 11) (RG r1_1_e0 9)) = (r1_1_e1, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition r1_1_e2 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc r1_1_e1 [((14%bv : bv 5), SOff 35 0)] 0x42328) [((15%bv : bv 5), SOff 36 0)] 0x4232c)).
Lemma r_r1_1_2 : RUN (set_regs_pc (set_regs_pc r1_1_e1 [((14%bv : bv 5), SOff 35 0)] 0x42328) [((15%bv : bv 5), SOff 36 0)] 0x4232c) = (r1_1_e2, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_1z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC r1_1_e2 BC_EQ (RG r1_1_e2 14) (SLit 0))).
Lemma r_r1_1z_0 : RUNTO (AC r1_1_e2 BC_EQ (RG r1_1_e2 14) (SLit 0)) = (r1_1z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r1_1n_e0 : sstate := Eval vm_compute in fst (RUN (AC r1_1_e2 BC_NE (RG r1_1_e2 14) (SLit 0))).
Lemma r_r1_1n_0 : RUN (AC r1_1_e2 BC_NE (RG r1_1_e2 14) (SLit 0)) = (r1_1n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 1%nat 18 41 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_1n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC r1_1n_e0 BC_EQ (RG r1_1n_e0 10) (SLit 0))).
Lemma r_r1_1n_1 : RUNTO (AC r1_1n_e0 BC_EQ (RG r1_1n_e0 10) (SLit 0)) = (r1_1n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r1_2_e0 : sstate := Eval vm_compute in fst (RUN (ssR1 2)).
Lemma r_r1_2_0 : RUN (ssR1 2) = (r1_2_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 18 0) (SLit (-1))) (SOff 41 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_2_e1 : sstate := Eval vm_compute in fst (RUN (AC r1_2_e0 BC_GEU (RG r1_2_e0 11) (RG r1_2_e0 9))).
Lemma r_r1_2_1 : RUN (AC r1_2_e0 BC_GEU (RG r1_2_e0 11) (RG r1_2_e0 9)) = (r1_2_e1, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition r1_2_e2 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc r1_2_e1 [((14%bv : bv 5), SOff 35 0)] 0x42328) [((15%bv : bv 5), SOff 36 0)] 0x4232c)).
Lemma r_r1_2_2 : RUN (set_regs_pc (set_regs_pc r1_2_e1 [((14%bv : bv 5), SOff 35 0)] 0x42328) [((15%bv : bv 5), SOff 36 0)] 0x4232c) = (r1_2_e2, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_2z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC r1_2_e2 BC_EQ (RG r1_2_e2 14) (SLit 0))).
Lemma r_r1_2z_0 : RUNTO (AC r1_2_e2 BC_EQ (RG r1_2_e2 14) (SLit 0)) = (r1_2z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r1_2n_e0 : sstate := Eval vm_compute in fst (RUN (AC r1_2_e2 BC_NE (RG r1_2_e2 14) (SLit 0))).
Lemma r_r1_2n_0 : RUN (AC r1_2_e2 BC_NE (RG r1_2_e2 14) (SLit 0)) = (r1_2n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 2%nat 18 41 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_2n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC r1_2n_e0 BC_EQ (RG r1_2n_e0 10) (SLit 0))).
Lemma r_r1_2n_1 : RUNTO (AC r1_2n_e0 BC_EQ (RG r1_2n_e0 10) (SLit 0)) = (r1_2n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r1_3_e0 : sstate := Eval vm_compute in fst (RUN (ssR1 3)).
Lemma r_r1_3_0 : RUN (ssR1 3) = (r1_3_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 18 0) (SLit (-1))) (SOff 41 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_3_e1 : sstate := Eval vm_compute in fst (RUN (AC r1_3_e0 BC_GEU (RG r1_3_e0 11) (RG r1_3_e0 9))).
Lemma r_r1_3_1 : RUN (AC r1_3_e0 BC_GEU (RG r1_3_e0 11) (RG r1_3_e0 9)) = (r1_3_e1, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition r1_3_e2 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc r1_3_e1 [((14%bv : bv 5), SOff 35 0)] 0x42328) [((15%bv : bv 5), SOff 36 0)] 0x4232c)).
Lemma r_r1_3_2 : RUN (set_regs_pc (set_regs_pc r1_3_e1 [((14%bv : bv 5), SOff 35 0)] 0x42328) [((15%bv : bv 5), SOff 36 0)] 0x4232c) = (r1_3_e2, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_3z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC r1_3_e2 BC_EQ (RG r1_3_e2 14) (SLit 0))).
Lemma r_r1_3z_0 : RUNTO (AC r1_3_e2 BC_EQ (RG r1_3_e2 14) (SLit 0)) = (r1_3z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r1_3n_e0 : sstate := Eval vm_compute in fst (RUN (AC r1_3_e2 BC_NE (RG r1_3_e2 14) (SLit 0))).
Lemma r_r1_3n_0 : RUN (AC r1_3_e2 BC_NE (RG r1_3_e2 14) (SLit 0)) = (r1_3n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 3%nat 18 41 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_3n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC r1_3n_e0 BC_EQ (RG r1_3n_e0 10) (SLit 0))).
Lemma r_r1_3n_1 : RUNTO (AC r1_3n_e0 BC_EQ (RG r1_3n_e0 10) (SLit 0)) = (r1_3n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r1_4_e0 : sstate := Eval vm_compute in fst (RUN (ssR1 4)).
Lemma r_r1_4_0 : RUN (ssR1 4) = (r1_4_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 18 0) (SLit (-1))) (SOff 41 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_4_e1 : sstate := Eval vm_compute in fst (RUN (AC r1_4_e0 BC_GEU (RG r1_4_e0 11) (RG r1_4_e0 9))).
Lemma r_r1_4_1 : RUN (AC r1_4_e0 BC_GEU (RG r1_4_e0 11) (RG r1_4_e0 9)) = (r1_4_e1, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition r1_4_e2 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc r1_4_e1 [((14%bv : bv 5), SOff 35 0)] 0x42328) [((15%bv : bv 5), SOff 36 0)] 0x4232c)).
Lemma r_r1_4_2 : RUN (set_regs_pc (set_regs_pc r1_4_e1 [((14%bv : bv 5), SOff 35 0)] 0x42328) [((15%bv : bv 5), SOff 36 0)] 0x4232c) = (r1_4_e2, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_4z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC r1_4_e2 BC_EQ (RG r1_4_e2 14) (SLit 0))).
Lemma r_r1_4z_0 : RUNTO (AC r1_4_e2 BC_EQ (RG r1_4_e2 14) (SLit 0)) = (r1_4z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r1_4n_e0 : sstate := Eval vm_compute in fst (RUN (AC r1_4_e2 BC_NE (RG r1_4_e2 14) (SLit 0))).
Lemma r_r1_4n_0 : RUN (AC r1_4_e2 BC_NE (RG r1_4_e2 14) (SLit 0)) = (r1_4n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 4%nat 18 41 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_4n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC r1_4n_e0 BC_EQ (RG r1_4n_e0 10) (SLit 0))).
Lemma r_r1_4n_1 : RUNTO (AC r1_4n_e0 BC_EQ (RG r1_4n_e0 10) (SLit 0)) = (r1_4n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r1_5_e0 : sstate := Eval vm_compute in fst (RUN (ssR1 5)).
Lemma r_r1_5_0 : RUN (ssR1 5) = (r1_5_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 18 0) (SLit (-1))) (SOff 41 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_5_e1 : sstate := Eval vm_compute in fst (RUN (AC r1_5_e0 BC_GEU (RG r1_5_e0 11) (RG r1_5_e0 9))).
Lemma r_r1_5_1 : RUN (AC r1_5_e0 BC_GEU (RG r1_5_e0 11) (RG r1_5_e0 9)) = (r1_5_e1, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition r1_5_e2 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc r1_5_e1 [((14%bv : bv 5), SOff 35 0)] 0x42328) [((15%bv : bv 5), SOff 36 0)] 0x4232c)).
Lemma r_r1_5_2 : RUN (set_regs_pc (set_regs_pc r1_5_e1 [((14%bv : bv 5), SOff 35 0)] 0x42328) [((15%bv : bv 5), SOff 36 0)] 0x4232c) = (r1_5_e2, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_5z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC r1_5_e2 BC_EQ (RG r1_5_e2 14) (SLit 0))).
Lemma r_r1_5z_0 : RUNTO (AC r1_5_e2 BC_EQ (RG r1_5_e2 14) (SLit 0)) = (r1_5z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r1_5n_e0 : sstate := Eval vm_compute in fst (RUN (AC r1_5_e2 BC_NE (RG r1_5_e2 14) (SLit 0))).
Lemma r_r1_5n_0 : RUN (AC r1_5_e2 BC_NE (RG r1_5_e2 14) (SLit 0)) = (r1_5n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 5%nat 18 41 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_5n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC r1_5n_e0 BC_EQ (RG r1_5n_e0 10) (SLit 0))).
Lemma r_r1_5n_1 : RUNTO (AC r1_5n_e0 BC_EQ (RG r1_5n_e0 10) (SLit 0)) = (r1_5n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r1_6_e0 : sstate := Eval vm_compute in fst (RUN (ssR1 6)).
Lemma r_r1_6_0 : RUN (ssR1 6) = (r1_6_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 18 0) (SLit (-1))) (SOff 41 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_6_e1 : sstate := Eval vm_compute in fst (RUN (AC r1_6_e0 BC_GEU (RG r1_6_e0 11) (RG r1_6_e0 9))).
Lemma r_r1_6_1 : RUN (AC r1_6_e0 BC_GEU (RG r1_6_e0 11) (RG r1_6_e0 9)) = (r1_6_e1, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition r1_6_e2 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc r1_6_e1 [((14%bv : bv 5), SOff 35 0)] 0x42328) [((15%bv : bv 5), SOff 36 0)] 0x4232c)).
Lemma r_r1_6_2 : RUN (set_regs_pc (set_regs_pc r1_6_e1 [((14%bv : bv 5), SOff 35 0)] 0x42328) [((15%bv : bv 5), SOff 36 0)] 0x4232c) = (r1_6_e2, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_6z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC r1_6_e2 BC_EQ (RG r1_6_e2 14) (SLit 0))).
Lemma r_r1_6z_0 : RUNTO (AC r1_6_e2 BC_EQ (RG r1_6_e2 14) (SLit 0)) = (r1_6z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r1_6n_e0 : sstate := Eval vm_compute in fst (RUN (AC r1_6_e2 BC_NE (RG r1_6_e2 14) (SLit 0))).
Lemma r_r1_6n_0 : RUN (AC r1_6_e2 BC_NE (RG r1_6_e2 14) (SLit 0)) = (r1_6n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 6%nat 18 41 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_6n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC r1_6n_e0 BC_EQ (RG r1_6n_e0 10) (SLit 0))).
Lemma r_r1_6n_1 : RUNTO (AC r1_6n_e0 BC_EQ (RG r1_6n_e0 10) (SLit 0)) = (r1_6n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r1_7_e0 : sstate := Eval vm_compute in fst (RUN (ssR1 7)).
Lemma r_r1_7_0 : RUN (ssR1 7) = (r1_7_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 18 0) (SLit (-1))) (SOff 41 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_7_e1 : sstate := Eval vm_compute in fst (RUN (AC r1_7_e0 BC_GEU (RG r1_7_e0 11) (RG r1_7_e0 9))).
Lemma r_r1_7_1 : RUN (AC r1_7_e0 BC_GEU (RG r1_7_e0 11) (RG r1_7_e0 9)) = (r1_7_e1, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition r1_7_e2 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc r1_7_e1 [((14%bv : bv 5), SOff 35 0)] 0x42328) [((15%bv : bv 5), SOff 36 0)] 0x4232c)).
Lemma r_r1_7_2 : RUN (set_regs_pc (set_regs_pc r1_7_e1 [((14%bv : bv 5), SOff 35 0)] 0x42328) [((15%bv : bv 5), SOff 36 0)] 0x4232c) = (r1_7_e2, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_7z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC r1_7_e2 BC_EQ (RG r1_7_e2 14) (SLit 0))).
Lemma r_r1_7z_0 : RUNTO (AC r1_7_e2 BC_EQ (RG r1_7_e2 14) (SLit 0)) = (r1_7z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r1_7n_e0 : sstate := Eval vm_compute in fst (RUN (AC r1_7_e2 BC_NE (RG r1_7_e2 14) (SLit 0))).
Lemma r_r1_7n_0 : RUN (AC r1_7_e2 BC_NE (RG r1_7_e2 14) (SLit 0)) = (r1_7n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 7%nat 18 41 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_7n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC r1_7n_e0 BC_EQ (RG r1_7n_e0 10) (SLit 0))).
Lemma r_r1_7n_1 : RUNTO (AC r1_7n_e0 BC_EQ (RG r1_7n_e0 10) (SLit 0)) = (r1_7n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r1_8_e0 : sstate := Eval vm_compute in fst (RUN (ssR1 8)).
Lemma r_r1_8_0 : RUN (ssR1 8) = (r1_8_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 18 0) (SLit (-1))) (SOff 41 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_8_e1 : sstate := Eval vm_compute in fst (RUN (AC r1_8_e0 BC_GEU (RG r1_8_e0 11) (RG r1_8_e0 9))).
Lemma r_r1_8_1 : RUN (AC r1_8_e0 BC_GEU (RG r1_8_e0 11) (RG r1_8_e0 9)) = (r1_8_e1, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition r1_8_e2 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc r1_8_e1 [((14%bv : bv 5), SOff 35 0)] 0x42328) [((15%bv : bv 5), SOff 36 0)] 0x4232c)).
Lemma r_r1_8_2 : RUN (set_regs_pc (set_regs_pc r1_8_e1 [((14%bv : bv 5), SOff 35 0)] 0x42328) [((15%bv : bv 5), SOff 36 0)] 0x4232c) = (r1_8_e2, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_8z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC r1_8_e2 BC_EQ (RG r1_8_e2 14) (SLit 0))).
Lemma r_r1_8z_0 : RUNTO (AC r1_8_e2 BC_EQ (RG r1_8_e2 14) (SLit 0)) = (r1_8z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r1_8n_e0 : sstate := Eval vm_compute in fst (RUN (AC r1_8_e2 BC_NE (RG r1_8_e2 14) (SLit 0))).
Lemma r_r1_8n_0 : RUN (AC r1_8_e2 BC_NE (RG r1_8_e2 14) (SLit 0)) = (r1_8n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 8%nat 18 41 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_8n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC r1_8n_e0 BC_EQ (RG r1_8n_e0 10) (SLit 0))).
Lemma r_r1_8n_1 : RUNTO (AC r1_8n_e0 BC_EQ (RG r1_8n_e0 10) (SLit 0)) = (r1_8n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
(* n >= 65: the length test is decided, 0x423a0 takes the call to __asan_region_is_poisoned (a0 = s2, a1 = n);
   inside it the runs are those of the strnlen check; it returns to 0x423f0, and 0x424a8 restores a0 = n - 1 *)
Definition r2L_e0 : sstate := Eval vm_compute in fst (RUN (ssR2L)).
Lemma r_r2L_0 : RUN (ssR2L) = (r2L_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 18 0) (SLit (-1))) (SOff 41 0))). Proof. vm_compute. reflexivity. Qed.
Definition r2L_e1 : sstate := Eval vm_compute in fst (RUN (AC r2L_e0 BC_GEU (RG r2L_e0 11) (RG r2L_e0 9))).
Lemma r_r2L_1 : RUN (AC r2L_e0 BC_GEU (RG r2L_e0 11) (RG r2L_e0 9)) = (r2L_e1, RS_stopped (SR_branch BC_GEU (SLit 2147450879) (SAlu ALU_ADD (SOff 18 0) (SOff 41 0)))). Proof. vm_compute. reflexivity. Qed.
Definition r2L_e2 : sstate := Eval vm_compute in fst (RUN (AC r2L_e1 BC_GEU (SLit 2147450879) (RG r2L_e1 18))).
Lemma r_r2L_2 : RUN (AC r2L_e1 BC_GEU (SLit 2147450879) (RG r2L_e1 18)) = (r2L_e2, RS_stopped (SR_branch BC_GEU (SOff 18 0) (SAlu ALU_ADD (SOff 18 0) (SOff 41 0)))). Proof. vm_compute. reflexivity. Qed.
Definition r2L_e3 : sstate := Eval vm_compute in fst (RUN (AC r2L_e2 BC_LTU (RG r2L_e2 8) (RG r2L_e2 18))).
Lemma r_r2L_3 : RUN (AC r2L_e2 BC_LTU (RG r2L_e2 8) (RG r2L_e2 18)) = (r2L_e3, RS_stopped (SR_branch BC_EQ (SOff 34 0) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r2Lz_e0 : sstate := Eval vm_compute in fst (RUN (AC r2L_e3 BC_EQ (RG r2L_e3 11) (SLit 0))).
Lemma r_r2Lz_0 : RUN (AC r2L_e3 BC_EQ (RG r2L_e3 11) (SLit 0)) = (r2Lz_e0, RS_stopped (SR_branch BC_GEU (SOff 39 2147450880) (SOff 40 2147450880))). Proof. vm_compute. reflexivity. Qed.
Definition r2Lz_e1 : sstate := Eval vm_compute in fst (RUN (AC r2Lz_e0 BC_LTU (RG r2Lz_e0 19) (RG r2Lz_e0 10))).
Lemma r_r2Lz_1 : RUN (AC r2Lz_e0 BC_LTU (RG r2Lz_e0 19) (RG r2Lz_e0 10)) = (r2Lz_e1, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition r2Lz_e2 : sstate := Eval vm_compute in fst (RUNTO (ss_after_mz r2Lz_e1 (ss_mem r2Lz_e1) 56 0x545a8)).
Lemma r_r2Lz_2 : RUNTO (ss_after_mz r2Lz_e1 (ss_mem r2Lz_e1) 56 0x545a8) = (r2Lz_e2, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r2Ln_e0 : sstate := Eval vm_compute in fst (RUN (AC r2L_e3 BC_NE (RG r2L_e3 11) (SLit 0))).
Lemma r_r2Ln_0 : RUN (AC r2L_e3 BC_NE (RG r2L_e3 11) (SLit 0)) = (r2Ln_e0, RS_stopped (SR_branch BC_LT (SAlu ALU_AND (SAlu ALU_ADD (SOff 18 (-1)) (SOff 41 0)) (SLit 7)) (SOff 34 0))). Proof. vm_compute. reflexivity. Qed.
Definition r2Ln_e1 : sstate := Eval vm_compute in fst (RUN (AC r2Ln_e0 BC_LT (RG r2Ln_e0 12) (RG r2Ln_e0 11))).
Lemma r_r2Ln_1 : RUN (AC r2Ln_e0 BC_LT (RG r2Ln_e0 12) (RG r2Ln_e0 11)) = (r2Ln_e1, RS_stopped (SR_branch BC_GEU (SOff 39 2147450880) (SOff 40 2147450880))). Proof. vm_compute. reflexivity. Qed.
Definition r2Ln_e2 : sstate := Eval vm_compute in fst (RUN (AC r2Ln_e1 BC_LTU (RG r2Ln_e1 19) (RG r2Ln_e1 10))).
Lemma r_r2Ln_2 : RUN (AC r2Ln_e1 BC_LTU (RG r2Ln_e1 19) (RG r2Ln_e1 10)) = (r2Ln_e2, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition r2Ln_e3 : sstate := Eval vm_compute in fst (RUNTO (ss_after_mz r2Ln_e2 (ss_mem r2Ln_e2) 56 0x545a8)).
Lemma r_r2Ln_3 : RUNTO (ss_after_mz r2Ln_e2 (ss_mem r2Ln_e2) 56 0x545a8) = (r2Ln_e3, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r2H_e0 : sstate := Eval vm_compute in fst (RUN (ssR2H)).
Lemma r_r2H_0 : RUN (ssR2H) = (r2H_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 18 0) (SLit (-1))) (SOff 41 0))). Proof. vm_compute. reflexivity. Qed.
Definition r2H_e1 : sstate := Eval vm_compute in fst (RUN (AC r2H_e0 BC_GEU (RG r2H_e0 11) (RG r2H_e0 9))).
Lemma r_r2H_1 : RUN (AC r2H_e0 BC_GEU (RG r2H_e0 11) (RG r2H_e0 9)) = (r2H_e1, RS_stopped (SR_branch BC_LTU (SLit 140737488355327) (SAlu ALU_ADD (SOff 18 0) (SOff 41 0)))). Proof. vm_compute. reflexivity. Qed.
Definition r2H_e2 : sstate := Eval vm_compute in fst (RUN (AC r2H_e1 BC_GEU (SLit 140737488355327) (RG r2H_e1 18))).
Lemma r_r2H_2 : RUN (AC r2H_e1 BC_GEU (SLit 140737488355327) (RG r2H_e1 18)) = (r2H_e2, RS_stopped (SR_branch BC_GEU (SOff 18 0) (SAlu ALU_ADD (SOff 18 0) (SOff 41 0)))). Proof. vm_compute. reflexivity. Qed.
Definition r2H_e3 : sstate := Eval vm_compute in fst (RUN (AC r2H_e2 BC_LTU (RG r2H_e2 8) (RG r2H_e2 18))).
Lemma r_r2H_3 : RUN (AC r2H_e2 BC_LTU (RG r2H_e2 8) (RG r2H_e2 18)) = (r2H_e3, RS_stopped (SR_branch BC_EQ (SOff 34 0) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r2Hz_e0 : sstate := Eval vm_compute in fst (RUN (AC r2H_e3 BC_EQ (RG r2H_e3 11) (SLit 0))).
Lemma r_r2Hz_0 : RUN (AC r2H_e3 BC_EQ (RG r2H_e3 11) (SLit 0)) = (r2Hz_e0, RS_stopped (SR_branch BC_GEU (SOff 39 2147450880) (SOff 40 2147450880))). Proof. vm_compute. reflexivity. Qed.
Definition r2Hz_e1 : sstate := Eval vm_compute in fst (RUN (AC r2Hz_e0 BC_LTU (RG r2Hz_e0 19) (RG r2Hz_e0 10))).
Lemma r_r2Hz_1 : RUN (AC r2Hz_e0 BC_LTU (RG r2Hz_e0 19) (RG r2Hz_e0 10)) = (r2Hz_e1, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition r2Hz_e2 : sstate := Eval vm_compute in fst (RUNTO (ss_after_mz r2Hz_e1 (ss_mem r2Hz_e1) 56 0x545a8)).
Lemma r_r2Hz_2 : RUNTO (ss_after_mz r2Hz_e1 (ss_mem r2Hz_e1) 56 0x545a8) = (r2Hz_e2, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r2Hn_e0 : sstate := Eval vm_compute in fst (RUN (AC r2H_e3 BC_NE (RG r2H_e3 11) (SLit 0))).
Lemma r_r2Hn_0 : RUN (AC r2H_e3 BC_NE (RG r2H_e3 11) (SLit 0)) = (r2Hn_e0, RS_stopped (SR_branch BC_LT (SAlu ALU_AND (SAlu ALU_ADD (SOff 18 (-1)) (SOff 41 0)) (SLit 7)) (SOff 34 0))). Proof. vm_compute. reflexivity. Qed.
Definition r2Hn_e1 : sstate := Eval vm_compute in fst (RUN (AC r2Hn_e0 BC_LT (RG r2Hn_e0 12) (RG r2Hn_e0 11))).
Lemma r_r2Hn_1 : RUN (AC r2Hn_e0 BC_LT (RG r2Hn_e0 12) (RG r2Hn_e0 11)) = (r2Hn_e1, RS_stopped (SR_branch BC_GEU (SOff 39 2147450880) (SOff 40 2147450880))). Proof. vm_compute. reflexivity. Qed.
Definition r2Hn_e2 : sstate := Eval vm_compute in fst (RUN (AC r2Hn_e1 BC_LTU (RG r2Hn_e1 19) (RG r2Hn_e1 10))).
Lemma r_r2Hn_2 : RUN (AC r2Hn_e1 BC_LTU (RG r2Hn_e1 19) (RG r2Hn_e1 10)) = (r2Hn_e2, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition r2Hn_e3 : sstate := Eval vm_compute in fst (RUNTO (ss_after_mz r2Hn_e2 (ss_mem r2Hn_e2) 56 0x545a8)).
Lemma r_r2Hn_3 : RUNTO (ss_after_mz r2Hn_e2 (ss_mem r2Hn_e2) 56 0x545a8) = (r2Hn_e3, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (RG ss r) v.
(* the region writes s1 (n), s3 (the flags object), s4 (s0 - 0x858) and s5 (n - 1, on the paths through 0x4239c and
   0x423ac); every other callee-saved register keeps its entry value *)
Definition KEPT : list Z := [2; 3; 4; 8; 18; 22; 23; 24; 25; 26; 27].
Definition shapeR (ss : sstate) : bool :=
(ss_pc ss =? RC_END) &&
match ss_mem ss with r :: _ => obase_eqb (YP09.r_base r) (Some 2%nat) && (YP09.r_wlo r =? - RC_STK) && (YP09.r_whi r =? 0) | [] => false end &&
reg_is ss 10 (SOff 41 (-1)) && forallb (fun r => reg_is ss r (SOff (Z.to_nat r) 0)) KEPT.
Definition win_chk (rs : smem) : bool := forallb (fun t => win_eqb t (Some 2%nat, - RC_STK, 0) || (snd t <=? snd (fst t))) (windows rs).
Lemma md_wvb_gen : forall m : Model, m = with_vm_backing (m_vm_lazy m) (m_vm_materialized m) m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
(* YE2y.icpt_ld8 over tbl_sl: the two shadow-word loads 0x422c4 / 0x422c8 are in the strlen interceptor body *)
Lemma sl_ld8 : forall (W : world tfibsegs) E ss ms md (rd rs : bv 5) (w : Z) (h : Z) (k K : nat),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_atoms_lt K ss = true ->
clookup tbl_sl (ss_pc ss) = Some w -> decode_any (Z_to_bv 32 w) = Some (Load SZ8 true rd rs 0%bv, 4) ->
bv_eqb rd 0%bv = false ->
sv_denot E (sr_get (ss_regs ss) rs) = Z_to_bv 64 h -> 0 <= h -> h + 8 <= 2 ^ 64 ->
rdword (aview tfibsegs (w_H W) (ms_mem ms)) h = Some (bv_unsigned (ew E k)) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
st_ok tfibsegs E (set_regs_pc ss [(rd, SOff k 0)] (ss_pc ss + 4)) (restrict (w_H W) ms1) /\
ms_mem ms1 = ms_mem ms).
Proof.
intros W E ss ms md rd rs w h k K HS Hrv Hat Hlk Hdec Hrd Hrs Hh0 Hh8 Hw. pose proof YF0x.Hwx_tfa as Hwx.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS Hrv) as Hshape.
pose proof (tbl_sl_ok _ _ Hlk) as Hfetch.
assert (Hec : is_ecall (Z_to_bv 32 w) = false).
{ unfold is_ecall. destruct (bv_eqb (Z_to_bv 32 w) _) eqn:Eq; [|reflexivity].
apply bv_eqb_eq in Eq. rewrite Eq in Hdec. vm_compute in Hdec. discriminate. }
pose proof (val_mem_of_rdword (w_H W) (ms_mem ms) h _ Hw) as Hvm.
apply (proj1 (val_mem_word_mem tfibsegs _ _ _)) in Hvm.
destruct (word_mem_ld tfibsegs _ h _ Hvm Hh0 Hh8) as (bs & Hbs & Hle). rewrite Z_to_bv_bv_unsigned in Hle.
assert (R : getr (ms_regs ms) rs = Z_to_bv 64 h) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E ss ms rs HS); exact Hrs).
rewrite Hshape. eapply (SRr_step tfibsegs Hwx W); [reflexivity | |].
- rewrite restrict_mkst_fx. apply (step_ld tfibsegs _ _ _ _ _ rd rs (0%bv : bv 12) bs (ew E k) Hfetch Hec Hdec); [|exact Hle].
rewrite R. replace (v_addi (Z_to_bv 64 h) (bv_signed (0%bv : bv 12))) with (Z_to_bv 64 h : word); [exact Hbs|].
apply bv_eq. unfold v_addi. rewrite !Z_to_bv_unsigned. change (bv_signed (0%bv : bv 12)) with 0.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_0_r, Z.mod_mod by lia. reflexivity.
- intros model' Hsbm. rewrite (same_but_materialized_wvb md model' Hsbm). rewrite Hrd.
cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
apply SRr_ret. split; [reflexivity|]. eexists _, _. split; [reflexivity|]. split; [|reflexivity].
rewrite restrict_mkst_fx. rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
replace (v_addi (Z_to_bv 64 (ss_pc ss)) 4) with (Z_to_bv 64 (ss_pc ss + 4) : word)
by (apply bv_eq; unfold v_addi; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64);
rewrite Zplus_mod_idemp_l; reflexivity).
apply (st_ok_set_regs tfibsegs K E E ss _ _ _ (ss_pc ss + 4) _ [(rd, SOff k 0)] HS (env_agree_refl K E) Hat Hrv).
+ cbn. rewrite ?Bool.orb_false_r. reflexivity.
+ intros r Hr. cbn in Hr. rewrite ?Bool.orb_false_r in Hr. rewrite getr_other; [reflexivity|].
intros ->. rewrite bv_eqb_refl in Hr. discriminate.
+ constructor; [|constructor]. cbn [fst snd]. split; [exact Hrd|].
rewrite getr_same by (intros H'; rewrite H', bv_eqb_refl in Hrd; discriminate). cbn [sv_denot].
rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
End e.
