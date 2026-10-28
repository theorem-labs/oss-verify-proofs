(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v YO0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AB1w AE3c AE20 AE2y.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition MC_ENTRY : Z := 0x515dc.
Definition MC_MID : Z := 0x51684.
Definition MC_STK : Z := 2208.
Definition MC_REAL : Z := 0x97294.
Definition MC_RA : Z := 0x516d8.
Definition shreg1 (g : nat) (t : Z) : YP09.region :=
YP09.mkRegion (Some g) SB (SB + t + 1) SB SB
((if 0 <? t then [YP09.mkChunk SB (CZero t)] else []) ++ [YP09.mkChunk (SB + t) (CVal 1 (SOff (2 + g) 0))]).
Definition shregs2 (g : nat) : smem :=
[ YP09.mkRegion (Some g) SB (SB + 1) SB SB [YP09.mkChunk SB (CZero 1)];
YP09.mkRegion (Some (1 + g)%nat) SB (SB + 1) SB SB [YP09.mkChunk SB (CVal 1 (SOff (2 + g) 0))] ].
Definition aliases1 (pa g : nat) (t : Z) : list (sv * sv) :=
[ (SAlu ALU_SRL (SOff pa 0) (SLit 3), SOff g 0);
(SAlu ALU_SRL (SAlu ALU_ADD (SOff pa (-1)) (SOff 12 0)) (SLit 3), SOff g t) ].
Definition aliases2 (pa g : nat) : list (sv * sv) :=
[ (SAlu ALU_SRL (SOff pa 0) (SLit 3), SOff g 0);
(SAlu ALU_SRL (SAlu ALU_ADD (SOff pa (-1)) (SOff 12 0)) (SLit 3), SOff (1 + g) 0);
(SAlu ALU_AND (SOff pa 7) (SLit (-8)), SOff (5 + g) 0);
(SAlu ALU_AND (SAlu ALU_ADD (SOff pa 0) (SOff 12 0)) (SLit (-8)), SOff (6 + g) 0);
(SAlu ALU_SRL (SOff (5 + g) 0) (SLit 3), SOff (7 + g) 0);
(SAlu ALU_SRL (SOff (6 + g) 0) (SLit 3), SOff (8 + g) 0) ].
Definition stkS : YP09.region := YP09.mkRegion (Some 2%nat) (- MC_STK) 0 (- MC_STK) 0 [].
Definition stkD_chunks : list YP09.chunk :=
[YP09.mkChunk 2136 (CVal 8 (SOff 32 0)); YP09.mkChunk 2128 (CVal 8 (SOff 33 0)); YP09.mkChunk 2120 (CVal 8 (SOff 34 0));
YP09.mkChunk 2112 (CVal 8 (SOff 35 0)); YP09.mkChunk 2104 (CVal 8 (SOff 36 0)); YP09.mkChunk 2096 (CVal 8 (SOff 37 0));
YP09.mkChunk 2088 (CVal 8 (SOff 38 0)); YP09.mkChunk 2080 (CVal 8 (SOff 39 0)); YP09.mkChunk 2072 (CVal 8 (SOff 40 0))].
Definition stkD : YP09.region := YP09.mkRegion (Some 2%nat) (-64) 2144 (-64) 2144 stkD_chunks.
Definition factsS0 : list (nat * afact) := [(2%nat, mkAF (2^44) (2^47) 4); (10%nat, mkAF 0 (2^47) 0); (11%nat, mkAF 0 (2^47) 0); (12%nat, mkAF 0 0 0)].
Definition factsS1 : list (nat * afact) :=
[(2%nat, mkAF (2^44) (2^47) 4); (10%nat, mkAF 0 (2^47) 0); (11%nat, mkAF 0 (2^47) 0); (12%nat, mkAF 1 64 0); (32%nat, mkAF 0 (2^44) 0); (34%nat, mkAF 0 7 0)].
Definition factsS2L : list (nat * afact) :=
[(2%nat, mkAF (2^44) (2^47) 4); (10%nat, mkAF 0 (2^47) 0); (11%nat, mkAF 0 0x7fff7fbe 0); (12%nat, mkAF 65 (2^32 - 1) 0);
(32%nat, mkAF 0 (2^44) 0); (33%nat, mkAF 0 (2^44) 0); (34%nat, mkAF 0 7 0);
(37%nat, mkAF 0 0x7fff7fc8 3); (38%nat, mkAF 0 0x7fff7fff 3); (39%nat, mkAF 0 (2^44) 0); (40%nat, mkAF 0 (2^44) 0)].
Definition factsS2H : list (nat * afact) :=
[(2%nat, mkAF (2^44) (2^47) 4); (10%nat, mkAF 0 (2^47) 0); (11%nat, mkAF 0x10007fff8000 (2^47 - 66) 0); (12%nat, mkAF 65 (2^32 - 1) 0);
(32%nat, mkAF 0 (2^44) 0); (33%nat, mkAF 0 (2^44) 0); (34%nat, mkAF 0 7 0);
(37%nat, mkAF 0x10007fff8000 (2^47 - 1) 3); (38%nat, mkAF 0x10007fff8000 (2^47 - 1) 3); (39%nat, mkAF 0 (2^44) 0); (40%nat, mkAF 0 (2^44) 0)].
Definition factsD1 : list (nat * afact) :=
[(2%nat, mkAF (2^43) (2^47) 4); (10%nat, mkAF 0 (2^47) 0); (11%nat, mkAF 0 (2^47) 0); (12%nat, mkAF 1 64 0); (42%nat, mkAF 0 (2^44) 0); (44%nat, mkAF 0 7 0)].
Definition factsD2L : list (nat * afact) :=
[(2%nat, mkAF (2^43) (2^47) 4); (10%nat, mkAF 0 0x7fff7fbe 0); (11%nat, mkAF 0 (2^47) 0); (12%nat, mkAF 65 (2^32 - 1) 0);
(42%nat, mkAF 0 (2^44) 0); (43%nat, mkAF 0 (2^44) 0); (44%nat, mkAF 0 7 0);
(47%nat, mkAF 0 0x7fff7fc8 3); (48%nat, mkAF 0 0x7fff7fff 3); (49%nat, mkAF 0 (2^44) 0); (50%nat, mkAF 0 (2^44) 0)].
Definition factsD2H : list (nat * afact) :=
[(2%nat, mkAF (2^43) (2^47) 4); (10%nat, mkAF 0x10007fff8000 (2^47 - 66) 0); (11%nat, mkAF 0 (2^47) 0); (12%nat, mkAF 65 (2^32 - 1) 0);
(42%nat, mkAF 0 (2^44) 0); (43%nat, mkAF 0 (2^44) 0); (44%nat, mkAF 0 7 0);
(47%nat, mkAF 0x10007fff8000 (2^47 - 1) 3); (48%nat, mkAF 0x10007fff8000 (2^47 - 1) 3); (49%nat, mkAF 0 (2^44) 0); (50%nat, mkAF 0 (2^44) 0)].
Definition sr_mid : list sv := Eval vm_compute in
(firstn 19 sr_atoms ++ [SAlu ALU_ADD (SOff 10 0) (SOff 12 0)] ++ [SOff 20 0; SOff 21 0] ++ [SOff 12 (-65)] ++ skipn 23 sr_atoms).
Definition ssS0 : sstate := mkSS MC_ENTRY sr_atoms (stkS :: map ro_region icpt_rodata) None (mkFacts factsS0 [] []).
Definition ssS1 (t : Z) : sstate := mkSS MC_ENTRY sr_atoms (stkS :: shreg1 32 t :: map ro_region icpt_rodata) None (mkFacts factsS1 [] (aliases1 11 32 t)).
Definition ssS2L : sstate := mkSS MC_ENTRY sr_atoms (stkS :: shregs2 32 ++ map ro_region icpt_rodata) None (mkFacts factsS2L [] (aliases2 11 32)).
Definition ssS2H : sstate := mkSS MC_ENTRY sr_atoms (stkS :: shregs2 32 ++ map ro_region icpt_rodata) None (mkFacts factsS2H [] (aliases2 11 32)).
Definition ssD1 (t : Z) : sstate := mkSS MC_MID sr_mid (stkD :: shreg1 42 t :: map ro_region icpt_rodata) None (mkFacts factsD1 [] (aliases1 10 42 t)).
Definition ssD2L : sstate := mkSS MC_MID sr_mid (stkD :: shregs2 42 ++ map ro_region icpt_rodata) None (mkFacts factsD2L [] (aliases2 10 42)).
Definition ssD2H : sstate := mkSS MC_MID sr_mid (stkD :: shregs2 42 ++ map ro_region icpt_rodata) None (mkFacts factsD2H [] (aliases2 10 42)).
Definition RUN (s : sstate) := sym_runN tfibsegs tbl_icpt FUEL s.
Definition RUNTO (s : sstate) := sym_run_toN tfibsegs tbl_icpt FUEL MC_MID s.
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition AC (s : sstate) (c : branch_cond) (a b : sv) : sstate := YP06.add_cond s (mkAC c a b).
Definition q0o_s0 : sstate := Eval vm_compute in (ssS0).
Definition q0o_e0 : sstate := Eval vm_compute in fst (RUN (ssS0)).
Lemma r_q0o_0 : RUN (ssS0) = (q0o_e0, RS_stopped (SR_branch BC_EQ (SOff 10 0) (SOff 11 0))). Proof. vm_compute. reflexivity. Qed.
Definition q0oA_s0 : sstate := Eval vm_compute in (AC q0o_e0 BC_NE (RG q0o_e0 10) (RG q0o_e0 11)).
Definition q0oA_e0 : sstate := Eval vm_compute in fst (RUN (AC q0o_e0 BC_NE (RG q0o_e0 10) (RG q0o_e0 11))).
Lemma r_q0oA_0 : RUN (AC q0o_e0 BC_NE (RG q0o_e0 10) (RG q0o_e0 11)) = (q0oA_e0, RS_stopped (SR_branch BC_GEU (SOff 11 0) (SAlu ALU_ADD (SOff 10 0) (SOff 12 0)))). Proof. vm_compute. reflexivity. Qed.
Definition q0oA_s1 : sstate := Eval vm_compute in (AC q0oA_e0 BC_GEU (RG q0oA_e0 11) (RG q0oA_e0 19)).
Definition q0oA_e1 : sstate := Eval vm_compute in fst (RUN (AC q0oA_e0 BC_GEU (RG q0oA_e0 11) (RG q0oA_e0 19))).
Lemma r_q0oA_1 : RUN (AC q0oA_e0 BC_GEU (RG q0oA_e0 11) (RG q0oA_e0 19)) = (q0oA_e1, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Definition q0_c : sstate := Eval vm_compute in DROPC q0oA_e1.
Definition q0oB_s0 : sstate := Eval vm_compute in (AC q0oA_e0 BC_LTU (RG q0oA_e0 11) (RG q0oA_e0 19)).
Definition q0oB_e0 : sstate := Eval vm_compute in fst (RUN (AC q0oA_e0 BC_LTU (RG q0oA_e0 11) (RG q0oA_e0 19))).
Lemma r_q0oB_0 : RUN (AC q0oA_e0 BC_LTU (RG q0oA_e0 11) (RG q0oA_e0 19)) = (q0oB_e0, RS_stopped (SR_branch BC_LTU (SOff 10 0) (SAlu ALU_ADD (SOff 11 0) (SOff 12 0)))). Proof. vm_compute. reflexivity. Qed.
Definition q0oB_s1 : sstate := Eval vm_compute in (AC q0oB_e0 BC_GEU (RG q0oB_e0 10) (RG q0oB_e0 21)).
Definition q0oB_e1 : sstate := Eval vm_compute in fst (RUN (AC q0oB_e0 BC_GEU (RG q0oB_e0 10) (RG q0oB_e0 21))).
Lemma r_q0oB_1 : RUN (AC q0oB_e0 BC_GEU (RG q0oB_e0 10) (RG q0oB_e0 21)) = (q0oB_e1, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Lemma q0oB_canon : DROPC q0oB_e1 = q0_c. Proof. reflexivity. Qed.
Lemma q0oA_canon : DROPC q0oA_e1 = q0_c. Proof. reflexivity. Qed.
Definition q0oC_s0 : sstate := Eval vm_compute in (AC q0o_e0 BC_EQ (RG q0o_e0 10) (RG q0o_e0 11)).
Definition q0oC_e0 : sstate := Eval vm_compute in fst (RUN (AC q0o_e0 BC_EQ (RG q0o_e0 10) (RG q0o_e0 11))).
Lemma r_q0oC_0 : RUN (AC q0o_e0 BC_EQ (RG q0o_e0 10) (RG q0o_e0 11)) = (q0oC_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Lemma q0oC_canon : DROPC q0oC_e0 = q0_c. Proof. reflexivity. Qed.
Definition q0_s0 : sstate := Eval vm_compute in (q0_c).
Definition q0_e0 : sstate := Eval vm_compute in fst (RUN (q0_c)).
Lemma r_q0_0 : RUN (q0_c) = (q0_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Definition q0_s1 : sstate := Eval vm_compute in (AC q0_e0 BC_GEU (RG q0_e0 13) (RG q0_e0 12)).
Definition q0_e1 : sstate := Eval vm_compute in fst (RUN (AC q0_e0 BC_GEU (RG q0_e0 13) (RG q0_e0 12))).
Lemma r_q0_1 : RUN (AC q0_e0 BC_GEU (RG q0_e0 13) (RG q0_e0 12)) = (q0_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 12 (-65)))). Proof. vm_compute. reflexivity. Qed.
Definition q0_s2 : sstate := Eval vm_compute in (AC q0_e1 BC_GEU (RG q0_e1 13) (RG q0_e1 22)).
Definition q0_e2 : sstate := Eval vm_compute in fst (RUN (AC q0_e1 BC_GEU (RG q0_e1 13) (RG q0_e1 22))).
Lemma r_q0_2 : RUN (AC q0_e1 BC_GEU (RG q0_e1 13) (RG q0_e1 22)) = (q0_e2, RS_stopped (SR_branch BC_NE (SOff 12 0) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition q0_s3 : sstate := Eval vm_compute in (AC q0_e2 BC_EQ (RG q0_e2 12) (SLit 0)).
Definition q0_e3 : sstate := Eval vm_compute in fst (RUN (AC q0_e2 BC_EQ (RG q0_e2 12) (SLit 0))).
Lemma r_q0_3 : RUN (AC q0_e2 BC_EQ (RG q0_e2 12) (SLit 0)) = (q0_e3, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 10 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Definition q0_s4 : sstate := Eval vm_compute in (AC q0_e3 BC_GEU (RG q0_e3 13) (RG q0_e3 12)).
Definition q0_e4 : sstate := Eval vm_compute in fst (RUN (AC q0_e3 BC_GEU (RG q0_e3 13) (RG q0_e3 12))).
Lemma r_q0_4 : RUN (AC q0_e3 BC_GEU (RG q0_e3 13) (RG q0_e3 12)) = (q0_e4, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition q1_0o_s0 : sstate := Eval vm_compute in (ssS1 0).
Definition q1_0o_e0 : sstate := Eval vm_compute in fst (RUN (ssS1 0)).
Lemma r_q1_0o_0 : RUN (ssS1 0) = (q1_0o_e0, RS_stopped (SR_branch BC_EQ (SOff 10 0) (SOff 11 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_0oA_s0 : sstate := Eval vm_compute in (AC q1_0o_e0 BC_NE (RG q1_0o_e0 10) (RG q1_0o_e0 11)).
Definition q1_0oA_e0 : sstate := Eval vm_compute in fst (RUN (AC q1_0o_e0 BC_NE (RG q1_0o_e0 10) (RG q1_0o_e0 11))).
Lemma r_q1_0oA_0 : RUN (AC q1_0o_e0 BC_NE (RG q1_0o_e0 10) (RG q1_0o_e0 11)) = (q1_0oA_e0, RS_stopped (SR_branch BC_GEU (SOff 11 0) (SAlu ALU_ADD (SOff 10 0) (SOff 12 0)))). Proof. vm_compute. reflexivity. Qed.
Definition q1_0oA_s1 : sstate := Eval vm_compute in (AC q1_0oA_e0 BC_GEU (RG q1_0oA_e0 11) (RG q1_0oA_e0 19)).
Definition q1_0oA_e1 : sstate := Eval vm_compute in fst (RUN (AC q1_0oA_e0 BC_GEU (RG q1_0oA_e0 11) (RG q1_0oA_e0 19))).
Lemma r_q1_0oA_1 : RUN (AC q1_0oA_e0 BC_GEU (RG q1_0oA_e0 11) (RG q1_0oA_e0 19)) = (q1_0oA_e1, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_0_c : sstate := Eval vm_compute in DROPC q1_0oA_e1.
Definition q1_0oB_s0 : sstate := Eval vm_compute in (AC q1_0oA_e0 BC_LTU (RG q1_0oA_e0 11) (RG q1_0oA_e0 19)).
Definition q1_0oB_e0 : sstate := Eval vm_compute in fst (RUN (AC q1_0oA_e0 BC_LTU (RG q1_0oA_e0 11) (RG q1_0oA_e0 19))).
Lemma r_q1_0oB_0 : RUN (AC q1_0oA_e0 BC_LTU (RG q1_0oA_e0 11) (RG q1_0oA_e0 19)) = (q1_0oB_e0, RS_stopped (SR_branch BC_LTU (SOff 10 0) (SAlu ALU_ADD (SOff 11 0) (SOff 12 0)))). Proof. vm_compute. reflexivity. Qed.
Definition q1_0oB_s1 : sstate := Eval vm_compute in (AC q1_0oB_e0 BC_GEU (RG q1_0oB_e0 10) (RG q1_0oB_e0 21)).
Definition q1_0oB_e1 : sstate := Eval vm_compute in fst (RUN (AC q1_0oB_e0 BC_GEU (RG q1_0oB_e0 10) (RG q1_0oB_e0 21))).
Lemma r_q1_0oB_1 : RUN (AC q1_0oB_e0 BC_GEU (RG q1_0oB_e0 10) (RG q1_0oB_e0 21)) = (q1_0oB_e1, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Lemma q1_0oB_canon : DROPC q1_0oB_e1 = q1_0_c. Proof. reflexivity. Qed.
Lemma q1_0oA_canon : DROPC q1_0oA_e1 = q1_0_c. Proof. reflexivity. Qed.
Definition q1_0_s0 : sstate := Eval vm_compute in (q1_0_c).
Definition q1_0_e0 : sstate := Eval vm_compute in fst (RUN (q1_0_c)).
Lemma r_q1_0_0 : RUN (q1_0_c) = (q1_0_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_0_s1 : sstate := Eval vm_compute in (AC q1_0_e0 BC_GEU (RG q1_0_e0 13) (RG q1_0_e0 12)).
Definition q1_0_e1 : sstate := Eval vm_compute in fst (RUN (AC q1_0_e0 BC_GEU (RG q1_0_e0 13) (RG q1_0_e0 12))).
Lemma r_q1_0_1 : RUN (AC q1_0_e0 BC_GEU (RG q1_0_e0 13) (RG q1_0_e0 12)) = (q1_0_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 12 (-65)))). Proof. vm_compute. reflexivity. Qed.
Definition q1_0_s2 : sstate := Eval vm_compute in (AC q1_0_e1 BC_LTU (RG q1_0_e1 13) (RG q1_0_e1 22)).
Definition q1_0_e2 : sstate := Eval vm_compute in fst (RUN (AC q1_0_e1 BC_LTU (RG q1_0_e1 13) (RG q1_0_e1 22))).
Lemma r_q1_0_2 : RUN (AC q1_0_e1 BC_LTU (RG q1_0_e1 13) (RG q1_0_e1 22)) = (q1_0_e2, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition q1_0_s3 : sstate := Eval vm_compute in (set_regs_pc (set_regs_pc q1_0_e2 [((15%bv : bv 5), SOff 35 0)] 0x51678) [((16%bv : bv 5), SOff 36 0)] 0x5167c).
Definition q1_0_e3 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc q1_0_e2 [((15%bv : bv 5), SOff 35 0)] 0x51678) [((16%bv : bv 5), SOff 36 0)] 0x5167c)).
Lemma r_q1_0_3 : RUN (set_regs_pc (set_regs_pc q1_0_e2 [((15%bv : bv 5), SOff 35 0)] 0x51678) [((16%bv : bv 5), SOff 36 0)] 0x5167c) = (q1_0_e3, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_0z_s0 : sstate := Eval vm_compute in (AC q1_0_e3 BC_EQ (RG q1_0_e3 15) (SLit 0)).
Definition q1_0z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC q1_0_e3 BC_EQ (RG q1_0_e3 15) (SLit 0))).
Lemma r_q1_0z_0 : RUNTO (AC q1_0_e3 BC_EQ (RG q1_0_e3 15) (SLit 0)) = (q1_0z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition q1_0n_s0 : sstate := Eval vm_compute in (AC q1_0_e3 BC_NE (RG q1_0_e3 15) (SLit 0)).
Definition q1_0n_e0 : sstate := Eval vm_compute in fst (RUN (AC q1_0_e3 BC_NE (RG q1_0_e3 15) (SLit 0))).
Lemma r_q1_0n_0 : RUN (AC q1_0_e3 BC_NE (RG q1_0_e3 15) (SLit 0)) = (q1_0n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 0%nat 11 12 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_0n_s1 : sstate := Eval vm_compute in (AC q1_0n_e0 BC_EQ (RG q1_0n_e0 13) (SLit 0)).
Definition q1_0n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC q1_0n_e0 BC_EQ (RG q1_0n_e0 13) (SLit 0))).
Lemma r_q1_0n_1 : RUNTO (AC q1_0n_e0 BC_EQ (RG q1_0n_e0 13) (SLit 0)) = (q1_0n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition q1_1o_s0 : sstate := Eval vm_compute in (ssS1 1).
Definition q1_1o_e0 : sstate := Eval vm_compute in fst (RUN (ssS1 1)).
Lemma r_q1_1o_0 : RUN (ssS1 1) = (q1_1o_e0, RS_stopped (SR_branch BC_EQ (SOff 10 0) (SOff 11 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_1oA_s0 : sstate := Eval vm_compute in (AC q1_1o_e0 BC_NE (RG q1_1o_e0 10) (RG q1_1o_e0 11)).
Definition q1_1oA_e0 : sstate := Eval vm_compute in fst (RUN (AC q1_1o_e0 BC_NE (RG q1_1o_e0 10) (RG q1_1o_e0 11))).
Lemma r_q1_1oA_0 : RUN (AC q1_1o_e0 BC_NE (RG q1_1o_e0 10) (RG q1_1o_e0 11)) = (q1_1oA_e0, RS_stopped (SR_branch BC_GEU (SOff 11 0) (SAlu ALU_ADD (SOff 10 0) (SOff 12 0)))). Proof. vm_compute. reflexivity. Qed.
Definition q1_1oA_s1 : sstate := Eval vm_compute in (AC q1_1oA_e0 BC_GEU (RG q1_1oA_e0 11) (RG q1_1oA_e0 19)).
Definition q1_1oA_e1 : sstate := Eval vm_compute in fst (RUN (AC q1_1oA_e0 BC_GEU (RG q1_1oA_e0 11) (RG q1_1oA_e0 19))).
Lemma r_q1_1oA_1 : RUN (AC q1_1oA_e0 BC_GEU (RG q1_1oA_e0 11) (RG q1_1oA_e0 19)) = (q1_1oA_e1, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_1_c : sstate := Eval vm_compute in DROPC q1_1oA_e1.
Definition q1_1oB_s0 : sstate := Eval vm_compute in (AC q1_1oA_e0 BC_LTU (RG q1_1oA_e0 11) (RG q1_1oA_e0 19)).
Definition q1_1oB_e0 : sstate := Eval vm_compute in fst (RUN (AC q1_1oA_e0 BC_LTU (RG q1_1oA_e0 11) (RG q1_1oA_e0 19))).
Lemma r_q1_1oB_0 : RUN (AC q1_1oA_e0 BC_LTU (RG q1_1oA_e0 11) (RG q1_1oA_e0 19)) = (q1_1oB_e0, RS_stopped (SR_branch BC_LTU (SOff 10 0) (SAlu ALU_ADD (SOff 11 0) (SOff 12 0)))). Proof. vm_compute. reflexivity. Qed.
Definition q1_1oB_s1 : sstate := Eval vm_compute in (AC q1_1oB_e0 BC_GEU (RG q1_1oB_e0 10) (RG q1_1oB_e0 21)).
Definition q1_1oB_e1 : sstate := Eval vm_compute in fst (RUN (AC q1_1oB_e0 BC_GEU (RG q1_1oB_e0 10) (RG q1_1oB_e0 21))).
Lemma r_q1_1oB_1 : RUN (AC q1_1oB_e0 BC_GEU (RG q1_1oB_e0 10) (RG q1_1oB_e0 21)) = (q1_1oB_e1, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Lemma q1_1oB_canon : DROPC q1_1oB_e1 = q1_1_c. Proof. reflexivity. Qed.
Lemma q1_1oA_canon : DROPC q1_1oA_e1 = q1_1_c. Proof. reflexivity. Qed.
Definition q1_1_s0 : sstate := Eval vm_compute in (q1_1_c).
Definition q1_1_e0 : sstate := Eval vm_compute in fst (RUN (q1_1_c)).
Lemma r_q1_1_0 : RUN (q1_1_c) = (q1_1_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_1_s1 : sstate := Eval vm_compute in (AC q1_1_e0 BC_GEU (RG q1_1_e0 13) (RG q1_1_e0 12)).
Definition q1_1_e1 : sstate := Eval vm_compute in fst (RUN (AC q1_1_e0 BC_GEU (RG q1_1_e0 13) (RG q1_1_e0 12))).
Lemma r_q1_1_1 : RUN (AC q1_1_e0 BC_GEU (RG q1_1_e0 13) (RG q1_1_e0 12)) = (q1_1_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 12 (-65)))). Proof. vm_compute. reflexivity. Qed.
Definition q1_1_s2 : sstate := Eval vm_compute in (AC q1_1_e1 BC_LTU (RG q1_1_e1 13) (RG q1_1_e1 22)).
Definition q1_1_e2 : sstate := Eval vm_compute in fst (RUN (AC q1_1_e1 BC_LTU (RG q1_1_e1 13) (RG q1_1_e1 22))).
Lemma r_q1_1_2 : RUN (AC q1_1_e1 BC_LTU (RG q1_1_e1 13) (RG q1_1_e1 22)) = (q1_1_e2, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition q1_1_s3 : sstate := Eval vm_compute in (set_regs_pc (set_regs_pc q1_1_e2 [((15%bv : bv 5), SOff 35 0)] 0x51678) [((16%bv : bv 5), SOff 36 0)] 0x5167c).
Definition q1_1_e3 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc q1_1_e2 [((15%bv : bv 5), SOff 35 0)] 0x51678) [((16%bv : bv 5), SOff 36 0)] 0x5167c)).
Lemma r_q1_1_3 : RUN (set_regs_pc (set_regs_pc q1_1_e2 [((15%bv : bv 5), SOff 35 0)] 0x51678) [((16%bv : bv 5), SOff 36 0)] 0x5167c) = (q1_1_e3, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_1z_s0 : sstate := Eval vm_compute in (AC q1_1_e3 BC_EQ (RG q1_1_e3 15) (SLit 0)).
Definition q1_1z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC q1_1_e3 BC_EQ (RG q1_1_e3 15) (SLit 0))).
Lemma r_q1_1z_0 : RUNTO (AC q1_1_e3 BC_EQ (RG q1_1_e3 15) (SLit 0)) = (q1_1z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition q1_1n_s0 : sstate := Eval vm_compute in (AC q1_1_e3 BC_NE (RG q1_1_e3 15) (SLit 0)).
Definition q1_1n_e0 : sstate := Eval vm_compute in fst (RUN (AC q1_1_e3 BC_NE (RG q1_1_e3 15) (SLit 0))).
Lemma r_q1_1n_0 : RUN (AC q1_1_e3 BC_NE (RG q1_1_e3 15) (SLit 0)) = (q1_1n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 1%nat 11 12 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_1n_s1 : sstate := Eval vm_compute in (AC q1_1n_e0 BC_EQ (RG q1_1n_e0 13) (SLit 0)).
Definition q1_1n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC q1_1n_e0 BC_EQ (RG q1_1n_e0 13) (SLit 0))).
Lemma r_q1_1n_1 : RUNTO (AC q1_1n_e0 BC_EQ (RG q1_1n_e0 13) (SLit 0)) = (q1_1n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition q1_2o_s0 : sstate := Eval vm_compute in (ssS1 2).
Definition q1_2o_e0 : sstate := Eval vm_compute in fst (RUN (ssS1 2)).
Lemma r_q1_2o_0 : RUN (ssS1 2) = (q1_2o_e0, RS_stopped (SR_branch BC_EQ (SOff 10 0) (SOff 11 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_2oA_s0 : sstate := Eval vm_compute in (AC q1_2o_e0 BC_NE (RG q1_2o_e0 10) (RG q1_2o_e0 11)).
Definition q1_2oA_e0 : sstate := Eval vm_compute in fst (RUN (AC q1_2o_e0 BC_NE (RG q1_2o_e0 10) (RG q1_2o_e0 11))).
Lemma r_q1_2oA_0 : RUN (AC q1_2o_e0 BC_NE (RG q1_2o_e0 10) (RG q1_2o_e0 11)) = (q1_2oA_e0, RS_stopped (SR_branch BC_GEU (SOff 11 0) (SAlu ALU_ADD (SOff 10 0) (SOff 12 0)))). Proof. vm_compute. reflexivity. Qed.
Definition q1_2oA_s1 : sstate := Eval vm_compute in (AC q1_2oA_e0 BC_GEU (RG q1_2oA_e0 11) (RG q1_2oA_e0 19)).
Definition q1_2oA_e1 : sstate := Eval vm_compute in fst (RUN (AC q1_2oA_e0 BC_GEU (RG q1_2oA_e0 11) (RG q1_2oA_e0 19))).
Lemma r_q1_2oA_1 : RUN (AC q1_2oA_e0 BC_GEU (RG q1_2oA_e0 11) (RG q1_2oA_e0 19)) = (q1_2oA_e1, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_2_c : sstate := Eval vm_compute in DROPC q1_2oA_e1.
Definition q1_2oB_s0 : sstate := Eval vm_compute in (AC q1_2oA_e0 BC_LTU (RG q1_2oA_e0 11) (RG q1_2oA_e0 19)).
Definition q1_2oB_e0 : sstate := Eval vm_compute in fst (RUN (AC q1_2oA_e0 BC_LTU (RG q1_2oA_e0 11) (RG q1_2oA_e0 19))).
Lemma r_q1_2oB_0 : RUN (AC q1_2oA_e0 BC_LTU (RG q1_2oA_e0 11) (RG q1_2oA_e0 19)) = (q1_2oB_e0, RS_stopped (SR_branch BC_LTU (SOff 10 0) (SAlu ALU_ADD (SOff 11 0) (SOff 12 0)))). Proof. vm_compute. reflexivity. Qed.
Definition q1_2oB_s1 : sstate := Eval vm_compute in (AC q1_2oB_e0 BC_GEU (RG q1_2oB_e0 10) (RG q1_2oB_e0 21)).
Definition q1_2oB_e1 : sstate := Eval vm_compute in fst (RUN (AC q1_2oB_e0 BC_GEU (RG q1_2oB_e0 10) (RG q1_2oB_e0 21))).
Lemma r_q1_2oB_1 : RUN (AC q1_2oB_e0 BC_GEU (RG q1_2oB_e0 10) (RG q1_2oB_e0 21)) = (q1_2oB_e1, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Lemma q1_2oB_canon : DROPC q1_2oB_e1 = q1_2_c. Proof. reflexivity. Qed.
Lemma q1_2oA_canon : DROPC q1_2oA_e1 = q1_2_c. Proof. reflexivity. Qed.
Definition q1_2_s0 : sstate := Eval vm_compute in (q1_2_c).
Definition q1_2_e0 : sstate := Eval vm_compute in fst (RUN (q1_2_c)).
Lemma r_q1_2_0 : RUN (q1_2_c) = (q1_2_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_2_s1 : sstate := Eval vm_compute in (AC q1_2_e0 BC_GEU (RG q1_2_e0 13) (RG q1_2_e0 12)).
Definition q1_2_e1 : sstate := Eval vm_compute in fst (RUN (AC q1_2_e0 BC_GEU (RG q1_2_e0 13) (RG q1_2_e0 12))).
Lemma r_q1_2_1 : RUN (AC q1_2_e0 BC_GEU (RG q1_2_e0 13) (RG q1_2_e0 12)) = (q1_2_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 12 (-65)))). Proof. vm_compute. reflexivity. Qed.
Definition q1_2_s2 : sstate := Eval vm_compute in (AC q1_2_e1 BC_LTU (RG q1_2_e1 13) (RG q1_2_e1 22)).
Definition q1_2_e2 : sstate := Eval vm_compute in fst (RUN (AC q1_2_e1 BC_LTU (RG q1_2_e1 13) (RG q1_2_e1 22))).
Lemma r_q1_2_2 : RUN (AC q1_2_e1 BC_LTU (RG q1_2_e1 13) (RG q1_2_e1 22)) = (q1_2_e2, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition q1_2_s3 : sstate := Eval vm_compute in (set_regs_pc (set_regs_pc q1_2_e2 [((15%bv : bv 5), SOff 35 0)] 0x51678) [((16%bv : bv 5), SOff 36 0)] 0x5167c).
Definition q1_2_e3 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc q1_2_e2 [((15%bv : bv 5), SOff 35 0)] 0x51678) [((16%bv : bv 5), SOff 36 0)] 0x5167c)).
Lemma r_q1_2_3 : RUN (set_regs_pc (set_regs_pc q1_2_e2 [((15%bv : bv 5), SOff 35 0)] 0x51678) [((16%bv : bv 5), SOff 36 0)] 0x5167c) = (q1_2_e3, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_2z_s0 : sstate := Eval vm_compute in (AC q1_2_e3 BC_EQ (RG q1_2_e3 15) (SLit 0)).
Definition q1_2z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC q1_2_e3 BC_EQ (RG q1_2_e3 15) (SLit 0))).
Lemma r_q1_2z_0 : RUNTO (AC q1_2_e3 BC_EQ (RG q1_2_e3 15) (SLit 0)) = (q1_2z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition q1_2n_s0 : sstate := Eval vm_compute in (AC q1_2_e3 BC_NE (RG q1_2_e3 15) (SLit 0)).
Definition q1_2n_e0 : sstate := Eval vm_compute in fst (RUN (AC q1_2_e3 BC_NE (RG q1_2_e3 15) (SLit 0))).
Lemma r_q1_2n_0 : RUN (AC q1_2_e3 BC_NE (RG q1_2_e3 15) (SLit 0)) = (q1_2n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 2%nat 11 12 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_2n_s1 : sstate := Eval vm_compute in (AC q1_2n_e0 BC_EQ (RG q1_2n_e0 13) (SLit 0)).
Definition q1_2n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC q1_2n_e0 BC_EQ (RG q1_2n_e0 13) (SLit 0))).
Lemma r_q1_2n_1 : RUNTO (AC q1_2n_e0 BC_EQ (RG q1_2n_e0 13) (SLit 0)) = (q1_2n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition q1_3o_s0 : sstate := Eval vm_compute in (ssS1 3).
Definition q1_3o_e0 : sstate := Eval vm_compute in fst (RUN (ssS1 3)).
Lemma r_q1_3o_0 : RUN (ssS1 3) = (q1_3o_e0, RS_stopped (SR_branch BC_EQ (SOff 10 0) (SOff 11 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_3oA_s0 : sstate := Eval vm_compute in (AC q1_3o_e0 BC_NE (RG q1_3o_e0 10) (RG q1_3o_e0 11)).
Definition q1_3oA_e0 : sstate := Eval vm_compute in fst (RUN (AC q1_3o_e0 BC_NE (RG q1_3o_e0 10) (RG q1_3o_e0 11))).
Lemma r_q1_3oA_0 : RUN (AC q1_3o_e0 BC_NE (RG q1_3o_e0 10) (RG q1_3o_e0 11)) = (q1_3oA_e0, RS_stopped (SR_branch BC_GEU (SOff 11 0) (SAlu ALU_ADD (SOff 10 0) (SOff 12 0)))). Proof. vm_compute. reflexivity. Qed.
Definition q1_3oA_s1 : sstate := Eval vm_compute in (AC q1_3oA_e0 BC_GEU (RG q1_3oA_e0 11) (RG q1_3oA_e0 19)).
Definition q1_3oA_e1 : sstate := Eval vm_compute in fst (RUN (AC q1_3oA_e0 BC_GEU (RG q1_3oA_e0 11) (RG q1_3oA_e0 19))).
Lemma r_q1_3oA_1 : RUN (AC q1_3oA_e0 BC_GEU (RG q1_3oA_e0 11) (RG q1_3oA_e0 19)) = (q1_3oA_e1, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_3_c : sstate := Eval vm_compute in DROPC q1_3oA_e1.
Definition q1_3oB_s0 : sstate := Eval vm_compute in (AC q1_3oA_e0 BC_LTU (RG q1_3oA_e0 11) (RG q1_3oA_e0 19)).
Definition q1_3oB_e0 : sstate := Eval vm_compute in fst (RUN (AC q1_3oA_e0 BC_LTU (RG q1_3oA_e0 11) (RG q1_3oA_e0 19))).
Lemma r_q1_3oB_0 : RUN (AC q1_3oA_e0 BC_LTU (RG q1_3oA_e0 11) (RG q1_3oA_e0 19)) = (q1_3oB_e0, RS_stopped (SR_branch BC_LTU (SOff 10 0) (SAlu ALU_ADD (SOff 11 0) (SOff 12 0)))). Proof. vm_compute. reflexivity. Qed.
Definition q1_3oB_s1 : sstate := Eval vm_compute in (AC q1_3oB_e0 BC_GEU (RG q1_3oB_e0 10) (RG q1_3oB_e0 21)).
Definition q1_3oB_e1 : sstate := Eval vm_compute in fst (RUN (AC q1_3oB_e0 BC_GEU (RG q1_3oB_e0 10) (RG q1_3oB_e0 21))).
Lemma r_q1_3oB_1 : RUN (AC q1_3oB_e0 BC_GEU (RG q1_3oB_e0 10) (RG q1_3oB_e0 21)) = (q1_3oB_e1, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Lemma q1_3oB_canon : DROPC q1_3oB_e1 = q1_3_c. Proof. reflexivity. Qed.
Lemma q1_3oA_canon : DROPC q1_3oA_e1 = q1_3_c. Proof. reflexivity. Qed.
Definition q1_3_s0 : sstate := Eval vm_compute in (q1_3_c).
Definition q1_3_e0 : sstate := Eval vm_compute in fst (RUN (q1_3_c)).
Lemma r_q1_3_0 : RUN (q1_3_c) = (q1_3_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_3_s1 : sstate := Eval vm_compute in (AC q1_3_e0 BC_GEU (RG q1_3_e0 13) (RG q1_3_e0 12)).
Definition q1_3_e1 : sstate := Eval vm_compute in fst (RUN (AC q1_3_e0 BC_GEU (RG q1_3_e0 13) (RG q1_3_e0 12))).
Lemma r_q1_3_1 : RUN (AC q1_3_e0 BC_GEU (RG q1_3_e0 13) (RG q1_3_e0 12)) = (q1_3_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 12 (-65)))). Proof. vm_compute. reflexivity. Qed.
Definition q1_3_s2 : sstate := Eval vm_compute in (AC q1_3_e1 BC_LTU (RG q1_3_e1 13) (RG q1_3_e1 22)).
Definition q1_3_e2 : sstate := Eval vm_compute in fst (RUN (AC q1_3_e1 BC_LTU (RG q1_3_e1 13) (RG q1_3_e1 22))).
Lemma r_q1_3_2 : RUN (AC q1_3_e1 BC_LTU (RG q1_3_e1 13) (RG q1_3_e1 22)) = (q1_3_e2, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition q1_3_s3 : sstate := Eval vm_compute in (set_regs_pc (set_regs_pc q1_3_e2 [((15%bv : bv 5), SOff 35 0)] 0x51678) [((16%bv : bv 5), SOff 36 0)] 0x5167c).
Definition q1_3_e3 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc q1_3_e2 [((15%bv : bv 5), SOff 35 0)] 0x51678) [((16%bv : bv 5), SOff 36 0)] 0x5167c)).
Lemma r_q1_3_3 : RUN (set_regs_pc (set_regs_pc q1_3_e2 [((15%bv : bv 5), SOff 35 0)] 0x51678) [((16%bv : bv 5), SOff 36 0)] 0x5167c) = (q1_3_e3, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_3z_s0 : sstate := Eval vm_compute in (AC q1_3_e3 BC_EQ (RG q1_3_e3 15) (SLit 0)).
Definition q1_3z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC q1_3_e3 BC_EQ (RG q1_3_e3 15) (SLit 0))).
Lemma r_q1_3z_0 : RUNTO (AC q1_3_e3 BC_EQ (RG q1_3_e3 15) (SLit 0)) = (q1_3z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition q1_3n_s0 : sstate := Eval vm_compute in (AC q1_3_e3 BC_NE (RG q1_3_e3 15) (SLit 0)).
Definition q1_3n_e0 : sstate := Eval vm_compute in fst (RUN (AC q1_3_e3 BC_NE (RG q1_3_e3 15) (SLit 0))).
Lemma r_q1_3n_0 : RUN (AC q1_3_e3 BC_NE (RG q1_3_e3 15) (SLit 0)) = (q1_3n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 3%nat 11 12 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_3n_s1 : sstate := Eval vm_compute in (AC q1_3n_e0 BC_EQ (RG q1_3n_e0 13) (SLit 0)).
Definition q1_3n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC q1_3n_e0 BC_EQ (RG q1_3n_e0 13) (SLit 0))).
Lemma r_q1_3n_1 : RUNTO (AC q1_3n_e0 BC_EQ (RG q1_3n_e0 13) (SLit 0)) = (q1_3n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition q1_4o_s0 : sstate := Eval vm_compute in (ssS1 4).
Definition q1_4o_e0 : sstate := Eval vm_compute in fst (RUN (ssS1 4)).
Lemma r_q1_4o_0 : RUN (ssS1 4) = (q1_4o_e0, RS_stopped (SR_branch BC_EQ (SOff 10 0) (SOff 11 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_4oA_s0 : sstate := Eval vm_compute in (AC q1_4o_e0 BC_NE (RG q1_4o_e0 10) (RG q1_4o_e0 11)).
Definition q1_4oA_e0 : sstate := Eval vm_compute in fst (RUN (AC q1_4o_e0 BC_NE (RG q1_4o_e0 10) (RG q1_4o_e0 11))).
Lemma r_q1_4oA_0 : RUN (AC q1_4o_e0 BC_NE (RG q1_4o_e0 10) (RG q1_4o_e0 11)) = (q1_4oA_e0, RS_stopped (SR_branch BC_GEU (SOff 11 0) (SAlu ALU_ADD (SOff 10 0) (SOff 12 0)))). Proof. vm_compute. reflexivity. Qed.
Definition q1_4oA_s1 : sstate := Eval vm_compute in (AC q1_4oA_e0 BC_GEU (RG q1_4oA_e0 11) (RG q1_4oA_e0 19)).
Definition q1_4oA_e1 : sstate := Eval vm_compute in fst (RUN (AC q1_4oA_e0 BC_GEU (RG q1_4oA_e0 11) (RG q1_4oA_e0 19))).
Lemma r_q1_4oA_1 : RUN (AC q1_4oA_e0 BC_GEU (RG q1_4oA_e0 11) (RG q1_4oA_e0 19)) = (q1_4oA_e1, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_4_c : sstate := Eval vm_compute in DROPC q1_4oA_e1.
Definition q1_4oB_s0 : sstate := Eval vm_compute in (AC q1_4oA_e0 BC_LTU (RG q1_4oA_e0 11) (RG q1_4oA_e0 19)).
Definition q1_4oB_e0 : sstate := Eval vm_compute in fst (RUN (AC q1_4oA_e0 BC_LTU (RG q1_4oA_e0 11) (RG q1_4oA_e0 19))).
Lemma r_q1_4oB_0 : RUN (AC q1_4oA_e0 BC_LTU (RG q1_4oA_e0 11) (RG q1_4oA_e0 19)) = (q1_4oB_e0, RS_stopped (SR_branch BC_LTU (SOff 10 0) (SAlu ALU_ADD (SOff 11 0) (SOff 12 0)))). Proof. vm_compute. reflexivity. Qed.
Definition q1_4oB_s1 : sstate := Eval vm_compute in (AC q1_4oB_e0 BC_GEU (RG q1_4oB_e0 10) (RG q1_4oB_e0 21)).
Definition q1_4oB_e1 : sstate := Eval vm_compute in fst (RUN (AC q1_4oB_e0 BC_GEU (RG q1_4oB_e0 10) (RG q1_4oB_e0 21))).
Lemma r_q1_4oB_1 : RUN (AC q1_4oB_e0 BC_GEU (RG q1_4oB_e0 10) (RG q1_4oB_e0 21)) = (q1_4oB_e1, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Lemma q1_4oB_canon : DROPC q1_4oB_e1 = q1_4_c. Proof. reflexivity. Qed.
Lemma q1_4oA_canon : DROPC q1_4oA_e1 = q1_4_c. Proof. reflexivity. Qed.
Definition q1_4_s0 : sstate := Eval vm_compute in (q1_4_c).
Definition q1_4_e0 : sstate := Eval vm_compute in fst (RUN (q1_4_c)).
Lemma r_q1_4_0 : RUN (q1_4_c) = (q1_4_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_4_s1 : sstate := Eval vm_compute in (AC q1_4_e0 BC_GEU (RG q1_4_e0 13) (RG q1_4_e0 12)).
Definition q1_4_e1 : sstate := Eval vm_compute in fst (RUN (AC q1_4_e0 BC_GEU (RG q1_4_e0 13) (RG q1_4_e0 12))).
Lemma r_q1_4_1 : RUN (AC q1_4_e0 BC_GEU (RG q1_4_e0 13) (RG q1_4_e0 12)) = (q1_4_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 12 (-65)))). Proof. vm_compute. reflexivity. Qed.
Definition q1_4_s2 : sstate := Eval vm_compute in (AC q1_4_e1 BC_LTU (RG q1_4_e1 13) (RG q1_4_e1 22)).
Definition q1_4_e2 : sstate := Eval vm_compute in fst (RUN (AC q1_4_e1 BC_LTU (RG q1_4_e1 13) (RG q1_4_e1 22))).
Lemma r_q1_4_2 : RUN (AC q1_4_e1 BC_LTU (RG q1_4_e1 13) (RG q1_4_e1 22)) = (q1_4_e2, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition q1_4_s3 : sstate := Eval vm_compute in (set_regs_pc (set_regs_pc q1_4_e2 [((15%bv : bv 5), SOff 35 0)] 0x51678) [((16%bv : bv 5), SOff 36 0)] 0x5167c).
Definition q1_4_e3 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc q1_4_e2 [((15%bv : bv 5), SOff 35 0)] 0x51678) [((16%bv : bv 5), SOff 36 0)] 0x5167c)).
Lemma r_q1_4_3 : RUN (set_regs_pc (set_regs_pc q1_4_e2 [((15%bv : bv 5), SOff 35 0)] 0x51678) [((16%bv : bv 5), SOff 36 0)] 0x5167c) = (q1_4_e3, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_4z_s0 : sstate := Eval vm_compute in (AC q1_4_e3 BC_EQ (RG q1_4_e3 15) (SLit 0)).
Definition q1_4z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC q1_4_e3 BC_EQ (RG q1_4_e3 15) (SLit 0))).
Lemma r_q1_4z_0 : RUNTO (AC q1_4_e3 BC_EQ (RG q1_4_e3 15) (SLit 0)) = (q1_4z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition q1_4n_s0 : sstate := Eval vm_compute in (AC q1_4_e3 BC_NE (RG q1_4_e3 15) (SLit 0)).
Definition q1_4n_e0 : sstate := Eval vm_compute in fst (RUN (AC q1_4_e3 BC_NE (RG q1_4_e3 15) (SLit 0))).
Lemma r_q1_4n_0 : RUN (AC q1_4_e3 BC_NE (RG q1_4_e3 15) (SLit 0)) = (q1_4n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 4%nat 11 12 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_4n_s1 : sstate := Eval vm_compute in (AC q1_4n_e0 BC_EQ (RG q1_4n_e0 13) (SLit 0)).
Definition q1_4n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC q1_4n_e0 BC_EQ (RG q1_4n_e0 13) (SLit 0))).
Lemma r_q1_4n_1 : RUNTO (AC q1_4n_e0 BC_EQ (RG q1_4n_e0 13) (SLit 0)) = (q1_4n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition q1_5o_s0 : sstate := Eval vm_compute in (ssS1 5).
Definition q1_5o_e0 : sstate := Eval vm_compute in fst (RUN (ssS1 5)).
Lemma r_q1_5o_0 : RUN (ssS1 5) = (q1_5o_e0, RS_stopped (SR_branch BC_EQ (SOff 10 0) (SOff 11 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_5oA_s0 : sstate := Eval vm_compute in (AC q1_5o_e0 BC_NE (RG q1_5o_e0 10) (RG q1_5o_e0 11)).
Definition q1_5oA_e0 : sstate := Eval vm_compute in fst (RUN (AC q1_5o_e0 BC_NE (RG q1_5o_e0 10) (RG q1_5o_e0 11))).
Lemma r_q1_5oA_0 : RUN (AC q1_5o_e0 BC_NE (RG q1_5o_e0 10) (RG q1_5o_e0 11)) = (q1_5oA_e0, RS_stopped (SR_branch BC_GEU (SOff 11 0) (SAlu ALU_ADD (SOff 10 0) (SOff 12 0)))). Proof. vm_compute. reflexivity. Qed.
Definition q1_5oA_s1 : sstate := Eval vm_compute in (AC q1_5oA_e0 BC_GEU (RG q1_5oA_e0 11) (RG q1_5oA_e0 19)).
Definition q1_5oA_e1 : sstate := Eval vm_compute in fst (RUN (AC q1_5oA_e0 BC_GEU (RG q1_5oA_e0 11) (RG q1_5oA_e0 19))).
Lemma r_q1_5oA_1 : RUN (AC q1_5oA_e0 BC_GEU (RG q1_5oA_e0 11) (RG q1_5oA_e0 19)) = (q1_5oA_e1, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_5_c : sstate := Eval vm_compute in DROPC q1_5oA_e1.
Definition q1_5oB_s0 : sstate := Eval vm_compute in (AC q1_5oA_e0 BC_LTU (RG q1_5oA_e0 11) (RG q1_5oA_e0 19)).
Definition q1_5oB_e0 : sstate := Eval vm_compute in fst (RUN (AC q1_5oA_e0 BC_LTU (RG q1_5oA_e0 11) (RG q1_5oA_e0 19))).
Lemma r_q1_5oB_0 : RUN (AC q1_5oA_e0 BC_LTU (RG q1_5oA_e0 11) (RG q1_5oA_e0 19)) = (q1_5oB_e0, RS_stopped (SR_branch BC_LTU (SOff 10 0) (SAlu ALU_ADD (SOff 11 0) (SOff 12 0)))). Proof. vm_compute. reflexivity. Qed.
Definition q1_5oB_s1 : sstate := Eval vm_compute in (AC q1_5oB_e0 BC_GEU (RG q1_5oB_e0 10) (RG q1_5oB_e0 21)).
Definition q1_5oB_e1 : sstate := Eval vm_compute in fst (RUN (AC q1_5oB_e0 BC_GEU (RG q1_5oB_e0 10) (RG q1_5oB_e0 21))).
Lemma r_q1_5oB_1 : RUN (AC q1_5oB_e0 BC_GEU (RG q1_5oB_e0 10) (RG q1_5oB_e0 21)) = (q1_5oB_e1, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Lemma q1_5oB_canon : DROPC q1_5oB_e1 = q1_5_c. Proof. reflexivity. Qed.
Lemma q1_5oA_canon : DROPC q1_5oA_e1 = q1_5_c. Proof. reflexivity. Qed.
Definition q1_5_s0 : sstate := Eval vm_compute in (q1_5_c).
Definition q1_5_e0 : sstate := Eval vm_compute in fst (RUN (q1_5_c)).
Lemma r_q1_5_0 : RUN (q1_5_c) = (q1_5_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_5_s1 : sstate := Eval vm_compute in (AC q1_5_e0 BC_GEU (RG q1_5_e0 13) (RG q1_5_e0 12)).
Definition q1_5_e1 : sstate := Eval vm_compute in fst (RUN (AC q1_5_e0 BC_GEU (RG q1_5_e0 13) (RG q1_5_e0 12))).
Lemma r_q1_5_1 : RUN (AC q1_5_e0 BC_GEU (RG q1_5_e0 13) (RG q1_5_e0 12)) = (q1_5_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 12 (-65)))). Proof. vm_compute. reflexivity. Qed.
Definition q1_5_s2 : sstate := Eval vm_compute in (AC q1_5_e1 BC_LTU (RG q1_5_e1 13) (RG q1_5_e1 22)).
Definition q1_5_e2 : sstate := Eval vm_compute in fst (RUN (AC q1_5_e1 BC_LTU (RG q1_5_e1 13) (RG q1_5_e1 22))).
Lemma r_q1_5_2 : RUN (AC q1_5_e1 BC_LTU (RG q1_5_e1 13) (RG q1_5_e1 22)) = (q1_5_e2, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition q1_5_s3 : sstate := Eval vm_compute in (set_regs_pc (set_regs_pc q1_5_e2 [((15%bv : bv 5), SOff 35 0)] 0x51678) [((16%bv : bv 5), SOff 36 0)] 0x5167c).
Definition q1_5_e3 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc q1_5_e2 [((15%bv : bv 5), SOff 35 0)] 0x51678) [((16%bv : bv 5), SOff 36 0)] 0x5167c)).
Lemma r_q1_5_3 : RUN (set_regs_pc (set_regs_pc q1_5_e2 [((15%bv : bv 5), SOff 35 0)] 0x51678) [((16%bv : bv 5), SOff 36 0)] 0x5167c) = (q1_5_e3, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_5z_s0 : sstate := Eval vm_compute in (AC q1_5_e3 BC_EQ (RG q1_5_e3 15) (SLit 0)).
Definition q1_5z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC q1_5_e3 BC_EQ (RG q1_5_e3 15) (SLit 0))).
Lemma r_q1_5z_0 : RUNTO (AC q1_5_e3 BC_EQ (RG q1_5_e3 15) (SLit 0)) = (q1_5z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition q1_5n_s0 : sstate := Eval vm_compute in (AC q1_5_e3 BC_NE (RG q1_5_e3 15) (SLit 0)).
Definition q1_5n_e0 : sstate := Eval vm_compute in fst (RUN (AC q1_5_e3 BC_NE (RG q1_5_e3 15) (SLit 0))).
Lemma r_q1_5n_0 : RUN (AC q1_5_e3 BC_NE (RG q1_5_e3 15) (SLit 0)) = (q1_5n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 5%nat 11 12 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_5n_s1 : sstate := Eval vm_compute in (AC q1_5n_e0 BC_EQ (RG q1_5n_e0 13) (SLit 0)).
Definition q1_5n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC q1_5n_e0 BC_EQ (RG q1_5n_e0 13) (SLit 0))).
Lemma r_q1_5n_1 : RUNTO (AC q1_5n_e0 BC_EQ (RG q1_5n_e0 13) (SLit 0)) = (q1_5n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition q1_6o_s0 : sstate := Eval vm_compute in (ssS1 6).
Definition q1_6o_e0 : sstate := Eval vm_compute in fst (RUN (ssS1 6)).
Lemma r_q1_6o_0 : RUN (ssS1 6) = (q1_6o_e0, RS_stopped (SR_branch BC_EQ (SOff 10 0) (SOff 11 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_6oA_s0 : sstate := Eval vm_compute in (AC q1_6o_e0 BC_NE (RG q1_6o_e0 10) (RG q1_6o_e0 11)).
Definition q1_6oA_e0 : sstate := Eval vm_compute in fst (RUN (AC q1_6o_e0 BC_NE (RG q1_6o_e0 10) (RG q1_6o_e0 11))).
Lemma r_q1_6oA_0 : RUN (AC q1_6o_e0 BC_NE (RG q1_6o_e0 10) (RG q1_6o_e0 11)) = (q1_6oA_e0, RS_stopped (SR_branch BC_GEU (SOff 11 0) (SAlu ALU_ADD (SOff 10 0) (SOff 12 0)))). Proof. vm_compute. reflexivity. Qed.
Definition q1_6oA_s1 : sstate := Eval vm_compute in (AC q1_6oA_e0 BC_GEU (RG q1_6oA_e0 11) (RG q1_6oA_e0 19)).
Definition q1_6oA_e1 : sstate := Eval vm_compute in fst (RUN (AC q1_6oA_e0 BC_GEU (RG q1_6oA_e0 11) (RG q1_6oA_e0 19))).
Lemma r_q1_6oA_1 : RUN (AC q1_6oA_e0 BC_GEU (RG q1_6oA_e0 11) (RG q1_6oA_e0 19)) = (q1_6oA_e1, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_6_c : sstate := Eval vm_compute in DROPC q1_6oA_e1.
Definition q1_6oB_s0 : sstate := Eval vm_compute in (AC q1_6oA_e0 BC_LTU (RG q1_6oA_e0 11) (RG q1_6oA_e0 19)).
Definition q1_6oB_e0 : sstate := Eval vm_compute in fst (RUN (AC q1_6oA_e0 BC_LTU (RG q1_6oA_e0 11) (RG q1_6oA_e0 19))).
Lemma r_q1_6oB_0 : RUN (AC q1_6oA_e0 BC_LTU (RG q1_6oA_e0 11) (RG q1_6oA_e0 19)) = (q1_6oB_e0, RS_stopped (SR_branch BC_LTU (SOff 10 0) (SAlu ALU_ADD (SOff 11 0) (SOff 12 0)))). Proof. vm_compute. reflexivity. Qed.
Definition q1_6oB_s1 : sstate := Eval vm_compute in (AC q1_6oB_e0 BC_GEU (RG q1_6oB_e0 10) (RG q1_6oB_e0 21)).
Definition q1_6oB_e1 : sstate := Eval vm_compute in fst (RUN (AC q1_6oB_e0 BC_GEU (RG q1_6oB_e0 10) (RG q1_6oB_e0 21))).
Lemma r_q1_6oB_1 : RUN (AC q1_6oB_e0 BC_GEU (RG q1_6oB_e0 10) (RG q1_6oB_e0 21)) = (q1_6oB_e1, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Lemma q1_6oB_canon : DROPC q1_6oB_e1 = q1_6_c. Proof. reflexivity. Qed.
Lemma q1_6oA_canon : DROPC q1_6oA_e1 = q1_6_c. Proof. reflexivity. Qed.
Definition q1_6_s0 : sstate := Eval vm_compute in (q1_6_c).
Definition q1_6_e0 : sstate := Eval vm_compute in fst (RUN (q1_6_c)).
Lemma r_q1_6_0 : RUN (q1_6_c) = (q1_6_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_6_s1 : sstate := Eval vm_compute in (AC q1_6_e0 BC_GEU (RG q1_6_e0 13) (RG q1_6_e0 12)).
Definition q1_6_e1 : sstate := Eval vm_compute in fst (RUN (AC q1_6_e0 BC_GEU (RG q1_6_e0 13) (RG q1_6_e0 12))).
Lemma r_q1_6_1 : RUN (AC q1_6_e0 BC_GEU (RG q1_6_e0 13) (RG q1_6_e0 12)) = (q1_6_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 12 (-65)))). Proof. vm_compute. reflexivity. Qed.
Definition q1_6_s2 : sstate := Eval vm_compute in (AC q1_6_e1 BC_LTU (RG q1_6_e1 13) (RG q1_6_e1 22)).
Definition q1_6_e2 : sstate := Eval vm_compute in fst (RUN (AC q1_6_e1 BC_LTU (RG q1_6_e1 13) (RG q1_6_e1 22))).
Lemma r_q1_6_2 : RUN (AC q1_6_e1 BC_LTU (RG q1_6_e1 13) (RG q1_6_e1 22)) = (q1_6_e2, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition q1_6_s3 : sstate := Eval vm_compute in (set_regs_pc (set_regs_pc q1_6_e2 [((15%bv : bv 5), SOff 35 0)] 0x51678) [((16%bv : bv 5), SOff 36 0)] 0x5167c).
Definition q1_6_e3 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc q1_6_e2 [((15%bv : bv 5), SOff 35 0)] 0x51678) [((16%bv : bv 5), SOff 36 0)] 0x5167c)).
Lemma r_q1_6_3 : RUN (set_regs_pc (set_regs_pc q1_6_e2 [((15%bv : bv 5), SOff 35 0)] 0x51678) [((16%bv : bv 5), SOff 36 0)] 0x5167c) = (q1_6_e3, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_6z_s0 : sstate := Eval vm_compute in (AC q1_6_e3 BC_EQ (RG q1_6_e3 15) (SLit 0)).
Definition q1_6z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC q1_6_e3 BC_EQ (RG q1_6_e3 15) (SLit 0))).
Lemma r_q1_6z_0 : RUNTO (AC q1_6_e3 BC_EQ (RG q1_6_e3 15) (SLit 0)) = (q1_6z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition q1_6n_s0 : sstate := Eval vm_compute in (AC q1_6_e3 BC_NE (RG q1_6_e3 15) (SLit 0)).
Definition q1_6n_e0 : sstate := Eval vm_compute in fst (RUN (AC q1_6_e3 BC_NE (RG q1_6_e3 15) (SLit 0))).
Lemma r_q1_6n_0 : RUN (AC q1_6_e3 BC_NE (RG q1_6_e3 15) (SLit 0)) = (q1_6n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 6%nat 11 12 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_6n_s1 : sstate := Eval vm_compute in (AC q1_6n_e0 BC_EQ (RG q1_6n_e0 13) (SLit 0)).
Definition q1_6n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC q1_6n_e0 BC_EQ (RG q1_6n_e0 13) (SLit 0))).
Lemma r_q1_6n_1 : RUNTO (AC q1_6n_e0 BC_EQ (RG q1_6n_e0 13) (SLit 0)) = (q1_6n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition q1_7o_s0 : sstate := Eval vm_compute in (ssS1 7).
Definition q1_7o_e0 : sstate := Eval vm_compute in fst (RUN (ssS1 7)).
Lemma r_q1_7o_0 : RUN (ssS1 7) = (q1_7o_e0, RS_stopped (SR_branch BC_EQ (SOff 10 0) (SOff 11 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_7oA_s0 : sstate := Eval vm_compute in (AC q1_7o_e0 BC_NE (RG q1_7o_e0 10) (RG q1_7o_e0 11)).
Definition q1_7oA_e0 : sstate := Eval vm_compute in fst (RUN (AC q1_7o_e0 BC_NE (RG q1_7o_e0 10) (RG q1_7o_e0 11))).
Lemma r_q1_7oA_0 : RUN (AC q1_7o_e0 BC_NE (RG q1_7o_e0 10) (RG q1_7o_e0 11)) = (q1_7oA_e0, RS_stopped (SR_branch BC_GEU (SOff 11 0) (SAlu ALU_ADD (SOff 10 0) (SOff 12 0)))). Proof. vm_compute. reflexivity. Qed.
Definition q1_7oA_s1 : sstate := Eval vm_compute in (AC q1_7oA_e0 BC_GEU (RG q1_7oA_e0 11) (RG q1_7oA_e0 19)).
Definition q1_7oA_e1 : sstate := Eval vm_compute in fst (RUN (AC q1_7oA_e0 BC_GEU (RG q1_7oA_e0 11) (RG q1_7oA_e0 19))).
Lemma r_q1_7oA_1 : RUN (AC q1_7oA_e0 BC_GEU (RG q1_7oA_e0 11) (RG q1_7oA_e0 19)) = (q1_7oA_e1, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_7_c : sstate := Eval vm_compute in DROPC q1_7oA_e1.
Definition q1_7oB_s0 : sstate := Eval vm_compute in (AC q1_7oA_e0 BC_LTU (RG q1_7oA_e0 11) (RG q1_7oA_e0 19)).
Definition q1_7oB_e0 : sstate := Eval vm_compute in fst (RUN (AC q1_7oA_e0 BC_LTU (RG q1_7oA_e0 11) (RG q1_7oA_e0 19))).
Lemma r_q1_7oB_0 : RUN (AC q1_7oA_e0 BC_LTU (RG q1_7oA_e0 11) (RG q1_7oA_e0 19)) = (q1_7oB_e0, RS_stopped (SR_branch BC_LTU (SOff 10 0) (SAlu ALU_ADD (SOff 11 0) (SOff 12 0)))). Proof. vm_compute. reflexivity. Qed.
Definition q1_7oB_s1 : sstate := Eval vm_compute in (AC q1_7oB_e0 BC_GEU (RG q1_7oB_e0 10) (RG q1_7oB_e0 21)).
Definition q1_7oB_e1 : sstate := Eval vm_compute in fst (RUN (AC q1_7oB_e0 BC_GEU (RG q1_7oB_e0 10) (RG q1_7oB_e0 21))).
Lemma r_q1_7oB_1 : RUN (AC q1_7oB_e0 BC_GEU (RG q1_7oB_e0 10) (RG q1_7oB_e0 21)) = (q1_7oB_e1, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Lemma q1_7oB_canon : DROPC q1_7oB_e1 = q1_7_c. Proof. reflexivity. Qed.
Lemma q1_7oA_canon : DROPC q1_7oA_e1 = q1_7_c. Proof. reflexivity. Qed.
Definition q1_7_s0 : sstate := Eval vm_compute in (q1_7_c).
Definition q1_7_e0 : sstate := Eval vm_compute in fst (RUN (q1_7_c)).
Lemma r_q1_7_0 : RUN (q1_7_c) = (q1_7_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_7_s1 : sstate := Eval vm_compute in (AC q1_7_e0 BC_GEU (RG q1_7_e0 13) (RG q1_7_e0 12)).
Definition q1_7_e1 : sstate := Eval vm_compute in fst (RUN (AC q1_7_e0 BC_GEU (RG q1_7_e0 13) (RG q1_7_e0 12))).
Lemma r_q1_7_1 : RUN (AC q1_7_e0 BC_GEU (RG q1_7_e0 13) (RG q1_7_e0 12)) = (q1_7_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 12 (-65)))). Proof. vm_compute. reflexivity. Qed.
Definition q1_7_s2 : sstate := Eval vm_compute in (AC q1_7_e1 BC_LTU (RG q1_7_e1 13) (RG q1_7_e1 22)).
Definition q1_7_e2 : sstate := Eval vm_compute in fst (RUN (AC q1_7_e1 BC_LTU (RG q1_7_e1 13) (RG q1_7_e1 22))).
Lemma r_q1_7_2 : RUN (AC q1_7_e1 BC_LTU (RG q1_7_e1 13) (RG q1_7_e1 22)) = (q1_7_e2, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition q1_7_s3 : sstate := Eval vm_compute in (set_regs_pc (set_regs_pc q1_7_e2 [((15%bv : bv 5), SOff 35 0)] 0x51678) [((16%bv : bv 5), SOff 36 0)] 0x5167c).
Definition q1_7_e3 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc q1_7_e2 [((15%bv : bv 5), SOff 35 0)] 0x51678) [((16%bv : bv 5), SOff 36 0)] 0x5167c)).
Lemma r_q1_7_3 : RUN (set_regs_pc (set_regs_pc q1_7_e2 [((15%bv : bv 5), SOff 35 0)] 0x51678) [((16%bv : bv 5), SOff 36 0)] 0x5167c) = (q1_7_e3, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_7z_s0 : sstate := Eval vm_compute in (AC q1_7_e3 BC_EQ (RG q1_7_e3 15) (SLit 0)).
Definition q1_7z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC q1_7_e3 BC_EQ (RG q1_7_e3 15) (SLit 0))).
Lemma r_q1_7z_0 : RUNTO (AC q1_7_e3 BC_EQ (RG q1_7_e3 15) (SLit 0)) = (q1_7z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition q1_7n_s0 : sstate := Eval vm_compute in (AC q1_7_e3 BC_NE (RG q1_7_e3 15) (SLit 0)).
Definition q1_7n_e0 : sstate := Eval vm_compute in fst (RUN (AC q1_7_e3 BC_NE (RG q1_7_e3 15) (SLit 0))).
Lemma r_q1_7n_0 : RUN (AC q1_7_e3 BC_NE (RG q1_7_e3 15) (SLit 0)) = (q1_7n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 7%nat 11 12 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_7n_s1 : sstate := Eval vm_compute in (AC q1_7n_e0 BC_EQ (RG q1_7n_e0 13) (SLit 0)).
Definition q1_7n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC q1_7n_e0 BC_EQ (RG q1_7n_e0 13) (SLit 0))).
Lemma r_q1_7n_1 : RUNTO (AC q1_7n_e0 BC_EQ (RG q1_7n_e0 13) (SLit 0)) = (q1_7n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition q1_8o_s0 : sstate := Eval vm_compute in (ssS1 8).
Definition q1_8o_e0 : sstate := Eval vm_compute in fst (RUN (ssS1 8)).
Lemma r_q1_8o_0 : RUN (ssS1 8) = (q1_8o_e0, RS_stopped (SR_branch BC_EQ (SOff 10 0) (SOff 11 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_8oA_s0 : sstate := Eval vm_compute in (AC q1_8o_e0 BC_NE (RG q1_8o_e0 10) (RG q1_8o_e0 11)).
Definition q1_8oA_e0 : sstate := Eval vm_compute in fst (RUN (AC q1_8o_e0 BC_NE (RG q1_8o_e0 10) (RG q1_8o_e0 11))).
Lemma r_q1_8oA_0 : RUN (AC q1_8o_e0 BC_NE (RG q1_8o_e0 10) (RG q1_8o_e0 11)) = (q1_8oA_e0, RS_stopped (SR_branch BC_GEU (SOff 11 0) (SAlu ALU_ADD (SOff 10 0) (SOff 12 0)))). Proof. vm_compute. reflexivity. Qed.
Definition q1_8oA_s1 : sstate := Eval vm_compute in (AC q1_8oA_e0 BC_GEU (RG q1_8oA_e0 11) (RG q1_8oA_e0 19)).
Definition q1_8oA_e1 : sstate := Eval vm_compute in fst (RUN (AC q1_8oA_e0 BC_GEU (RG q1_8oA_e0 11) (RG q1_8oA_e0 19))).
Lemma r_q1_8oA_1 : RUN (AC q1_8oA_e0 BC_GEU (RG q1_8oA_e0 11) (RG q1_8oA_e0 19)) = (q1_8oA_e1, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_8_c : sstate := Eval vm_compute in DROPC q1_8oA_e1.
Definition q1_8oB_s0 : sstate := Eval vm_compute in (AC q1_8oA_e0 BC_LTU (RG q1_8oA_e0 11) (RG q1_8oA_e0 19)).
Definition q1_8oB_e0 : sstate := Eval vm_compute in fst (RUN (AC q1_8oA_e0 BC_LTU (RG q1_8oA_e0 11) (RG q1_8oA_e0 19))).
Lemma r_q1_8oB_0 : RUN (AC q1_8oA_e0 BC_LTU (RG q1_8oA_e0 11) (RG q1_8oA_e0 19)) = (q1_8oB_e0, RS_stopped (SR_branch BC_LTU (SOff 10 0) (SAlu ALU_ADD (SOff 11 0) (SOff 12 0)))). Proof. vm_compute. reflexivity. Qed.
Definition q1_8oB_s1 : sstate := Eval vm_compute in (AC q1_8oB_e0 BC_GEU (RG q1_8oB_e0 10) (RG q1_8oB_e0 21)).
Definition q1_8oB_e1 : sstate := Eval vm_compute in fst (RUN (AC q1_8oB_e0 BC_GEU (RG q1_8oB_e0 10) (RG q1_8oB_e0 21))).
Lemma r_q1_8oB_1 : RUN (AC q1_8oB_e0 BC_GEU (RG q1_8oB_e0 10) (RG q1_8oB_e0 21)) = (q1_8oB_e1, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Lemma q1_8oB_canon : DROPC q1_8oB_e1 = q1_8_c. Proof. reflexivity. Qed.
Lemma q1_8oA_canon : DROPC q1_8oA_e1 = q1_8_c. Proof. reflexivity. Qed.
Definition q1_8_s0 : sstate := Eval vm_compute in (q1_8_c).
Definition q1_8_e0 : sstate := Eval vm_compute in fst (RUN (q1_8_c)).
Lemma r_q1_8_0 : RUN (q1_8_c) = (q1_8_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_8_s1 : sstate := Eval vm_compute in (AC q1_8_e0 BC_GEU (RG q1_8_e0 13) (RG q1_8_e0 12)).
Definition q1_8_e1 : sstate := Eval vm_compute in fst (RUN (AC q1_8_e0 BC_GEU (RG q1_8_e0 13) (RG q1_8_e0 12))).
Lemma r_q1_8_1 : RUN (AC q1_8_e0 BC_GEU (RG q1_8_e0 13) (RG q1_8_e0 12)) = (q1_8_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 12 (-65)))). Proof. vm_compute. reflexivity. Qed.
Definition q1_8_s2 : sstate := Eval vm_compute in (AC q1_8_e1 BC_LTU (RG q1_8_e1 13) (RG q1_8_e1 22)).
Definition q1_8_e2 : sstate := Eval vm_compute in fst (RUN (AC q1_8_e1 BC_LTU (RG q1_8_e1 13) (RG q1_8_e1 22))).
Lemma r_q1_8_2 : RUN (AC q1_8_e1 BC_LTU (RG q1_8_e1 13) (RG q1_8_e1 22)) = (q1_8_e2, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition q1_8_s3 : sstate := Eval vm_compute in (set_regs_pc (set_regs_pc q1_8_e2 [((15%bv : bv 5), SOff 35 0)] 0x51678) [((16%bv : bv 5), SOff 36 0)] 0x5167c).
Definition q1_8_e3 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc q1_8_e2 [((15%bv : bv 5), SOff 35 0)] 0x51678) [((16%bv : bv 5), SOff 36 0)] 0x5167c)).
Lemma r_q1_8_3 : RUN (set_regs_pc (set_regs_pc q1_8_e2 [((15%bv : bv 5), SOff 35 0)] 0x51678) [((16%bv : bv 5), SOff 36 0)] 0x5167c) = (q1_8_e3, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_8z_s0 : sstate := Eval vm_compute in (AC q1_8_e3 BC_EQ (RG q1_8_e3 15) (SLit 0)).
Definition q1_8z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC q1_8_e3 BC_EQ (RG q1_8_e3 15) (SLit 0))).
Lemma r_q1_8z_0 : RUNTO (AC q1_8_e3 BC_EQ (RG q1_8_e3 15) (SLit 0)) = (q1_8z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition q1_8n_s0 : sstate := Eval vm_compute in (AC q1_8_e3 BC_NE (RG q1_8_e3 15) (SLit 0)).
Definition q1_8n_e0 : sstate := Eval vm_compute in fst (RUN (AC q1_8_e3 BC_NE (RG q1_8_e3 15) (SLit 0))).
Lemma r_q1_8n_0 : RUN (AC q1_8_e3 BC_NE (RG q1_8_e3 15) (SLit 0)) = (q1_8n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 8%nat 11 12 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition q1_8n_s1 : sstate := Eval vm_compute in (AC q1_8n_e0 BC_EQ (RG q1_8n_e0 13) (SLit 0)).
Definition q1_8n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC q1_8n_e0 BC_EQ (RG q1_8n_e0 13) (SLit 0))).
Lemma r_q1_8n_1 : RUNTO (AC q1_8n_e0 BC_EQ (RG q1_8n_e0 13) (SLit 0)) = (q1_8n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition q2Lo_s0 : sstate := Eval vm_compute in (ssS2L).
Definition q2Lo_e0 : sstate := Eval vm_compute in fst (RUN (ssS2L)).
Lemma r_q2Lo_0 : RUN (ssS2L) = (q2Lo_e0, RS_stopped (SR_branch BC_EQ (SOff 10 0) (SOff 11 0))). Proof. vm_compute. reflexivity. Qed.
Definition q2LoA_s0 : sstate := Eval vm_compute in (AC q2Lo_e0 BC_NE (RG q2Lo_e0 10) (RG q2Lo_e0 11)).
Definition q2LoA_e0 : sstate := Eval vm_compute in fst (RUN (AC q2Lo_e0 BC_NE (RG q2Lo_e0 10) (RG q2Lo_e0 11))).
Lemma r_q2LoA_0 : RUN (AC q2Lo_e0 BC_NE (RG q2Lo_e0 10) (RG q2Lo_e0 11)) = (q2LoA_e0, RS_stopped (SR_branch BC_GEU (SOff 11 0) (SAlu ALU_ADD (SOff 10 0) (SOff 12 0)))). Proof. vm_compute. reflexivity. Qed.
Definition q2LoA_s1 : sstate := Eval vm_compute in (AC q2LoA_e0 BC_GEU (RG q2LoA_e0 11) (RG q2LoA_e0 19)).
Definition q2LoA_e1 : sstate := Eval vm_compute in fst (RUN (AC q2LoA_e0 BC_GEU (RG q2LoA_e0 11) (RG q2LoA_e0 19))).
Lemma r_q2LoA_1 : RUN (AC q2LoA_e0 BC_GEU (RG q2LoA_e0 11) (RG q2LoA_e0 19)) = (q2LoA_e1, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Definition q2L_c : sstate := Eval vm_compute in DROPC q2LoA_e1.
Definition q2LoB_s0 : sstate := Eval vm_compute in (AC q2LoA_e0 BC_LTU (RG q2LoA_e0 11) (RG q2LoA_e0 19)).
Definition q2LoB_e0 : sstate := Eval vm_compute in fst (RUN (AC q2LoA_e0 BC_LTU (RG q2LoA_e0 11) (RG q2LoA_e0 19))).
Lemma r_q2LoB_0 : RUN (AC q2LoA_e0 BC_LTU (RG q2LoA_e0 11) (RG q2LoA_e0 19)) = (q2LoB_e0, RS_stopped (SR_branch BC_LTU (SOff 10 0) (SAlu ALU_ADD (SOff 11 0) (SOff 12 0)))). Proof. vm_compute. reflexivity. Qed.
Definition q2LoB_s1 : sstate := Eval vm_compute in (AC q2LoB_e0 BC_GEU (RG q2LoB_e0 10) (RG q2LoB_e0 21)).
Definition q2LoB_e1 : sstate := Eval vm_compute in fst (RUN (AC q2LoB_e0 BC_GEU (RG q2LoB_e0 10) (RG q2LoB_e0 21))).
Lemma r_q2LoB_1 : RUN (AC q2LoB_e0 BC_GEU (RG q2LoB_e0 10) (RG q2LoB_e0 21)) = (q2LoB_e1, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Lemma q2LoB_canon : DROPC q2LoB_e1 = q2L_c. Proof. reflexivity. Qed.
Lemma q2LoA_canon : DROPC q2LoA_e1 = q2L_c. Proof. reflexivity. Qed.
Definition q2L_s0 : sstate := Eval vm_compute in (q2L_c).
Definition q2L_e0 : sstate := Eval vm_compute in fst (RUN (q2L_c)).
Lemma r_q2L_0 : RUN (q2L_c) = (q2L_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Definition q2L_s1 : sstate := Eval vm_compute in (AC q2L_e0 BC_GEU (RG q2L_e0 13) (RG q2L_e0 12)).
Definition q2L_e1 : sstate := Eval vm_compute in fst (RUN (AC q2L_e0 BC_GEU (RG q2L_e0 13) (RG q2L_e0 12))).
Lemma r_q2L_1 : RUN (AC q2L_e0 BC_GEU (RG q2L_e0 13) (RG q2L_e0 12)) = (q2L_e1, RS_stopped (SR_branch BC_GEU (SLit 2147450879) (SAlu ALU_ADD (SOff 11 0) (SOff 12 0)))). Proof. vm_compute. reflexivity. Qed.
Definition q2L_s2 : sstate := Eval vm_compute in (AC q2L_e1 BC_GEU (SLit 2147450879) (RG q2L_e1 18)).
Definition q2L_e2 : sstate := Eval vm_compute in fst (RUN (AC q2L_e1 BC_GEU (SLit 2147450879) (RG q2L_e1 18))).
Lemma r_q2L_2 : RUN (AC q2L_e1 BC_GEU (SLit 2147450879) (RG q2L_e1 18)) = (q2L_e2, RS_stopped (SR_branch BC_GEU (SOff 11 0) (SAlu ALU_ADD (SOff 11 0) (SOff 12 0)))). Proof. vm_compute. reflexivity. Qed.
Definition q2L_s3 : sstate := Eval vm_compute in (AC q2L_e2 BC_LTU (RG q2L_e2 8) (RG q2L_e2 18)).
Definition q2L_e3 : sstate := Eval vm_compute in fst (RUN (AC q2L_e2 BC_LTU (RG q2L_e2 8) (RG q2L_e2 18))).
Lemma r_q2L_3 : RUN (AC q2L_e2 BC_LTU (RG q2L_e2 8) (RG q2L_e2 18)) = (q2L_e3, RS_stopped (SR_branch BC_EQ (SOff 34 0) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition q2Lz_s0 : sstate := Eval vm_compute in (AC q2L_e3 BC_EQ (RG q2L_e3 11) (SLit 0)).
Definition q2Lz_e0 : sstate := Eval vm_compute in fst (RUN (AC q2L_e3 BC_EQ (RG q2L_e3 11) (SLit 0))).
Lemma r_q2Lz_0 : RUN (AC q2L_e3 BC_EQ (RG q2L_e3 11) (SLit 0)) = (q2Lz_e0, RS_stopped (SR_branch BC_GEU (SOff 39 2147450880) (SOff 40 2147450880))). Proof. vm_compute. reflexivity. Qed.
Definition q2Lz_s1 : sstate := Eval vm_compute in (AC q2Lz_e0 BC_LTU (RG q2Lz_e0 19) (RG q2Lz_e0 10)).
Definition q2Lz_e1 : sstate := Eval vm_compute in fst (RUN (AC q2Lz_e0 BC_LTU (RG q2Lz_e0 19) (RG q2Lz_e0 10))).
Lemma r_q2Lz_1 : RUN (AC q2Lz_e0 BC_LTU (RG q2Lz_e0 19) (RG q2Lz_e0 10)) = (q2Lz_e1, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition q2Lz_s2 : sstate := Eval vm_compute in (ss_after_mz q2Lz_e1 (ss_mem q2Lz_e1) 56 0x542cc).
Definition q2Lz_e2 : sstate := Eval vm_compute in fst (RUNTO (ss_after_mz q2Lz_e1 (ss_mem q2Lz_e1) 56 0x542cc)).
Lemma r_q2Lz_2 : RUNTO (ss_after_mz q2Lz_e1 (ss_mem q2Lz_e1) 56 0x542cc) = (q2Lz_e2, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition q2Ln_s0 : sstate := Eval vm_compute in (AC q2L_e3 BC_NE (RG q2L_e3 11) (SLit 0)).
Definition q2Ln_e0 : sstate := Eval vm_compute in fst (RUN (AC q2L_e3 BC_NE (RG q2L_e3 11) (SLit 0))).
Lemma r_q2Ln_0 : RUN (AC q2L_e3 BC_NE (RG q2L_e3 11) (SLit 0)) = (q2Ln_e0, RS_stopped (SR_branch BC_LT (SAlu ALU_AND (SAlu ALU_ADD (SOff 11 (-1)) (SOff 12 0)) (SLit 7)) (SOff 34 0))). Proof. vm_compute. reflexivity. Qed.
Definition q2Ln_s1 : sstate := Eval vm_compute in (AC q2Ln_e0 BC_LT (RG q2Ln_e0 12) (RG q2Ln_e0 11)).
Definition q2Ln_e1 : sstate := Eval vm_compute in fst (RUN (AC q2Ln_e0 BC_LT (RG q2Ln_e0 12) (RG q2Ln_e0 11))).
Lemma r_q2Ln_1 : RUN (AC q2Ln_e0 BC_LT (RG q2Ln_e0 12) (RG q2Ln_e0 11)) = (q2Ln_e1, RS_stopped (SR_branch BC_GEU (SOff 39 2147450880) (SOff 40 2147450880))). Proof. vm_compute. reflexivity. Qed.
Definition q2Ln_s2 : sstate := Eval vm_compute in (AC q2Ln_e1 BC_LTU (RG q2Ln_e1 19) (RG q2Ln_e1 10)).
Definition q2Ln_e2 : sstate := Eval vm_compute in fst (RUN (AC q2Ln_e1 BC_LTU (RG q2Ln_e1 19) (RG q2Ln_e1 10))).
Lemma r_q2Ln_2 : RUN (AC q2Ln_e1 BC_LTU (RG q2Ln_e1 19) (RG q2Ln_e1 10)) = (q2Ln_e2, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition q2Ln_s3 : sstate := Eval vm_compute in (ss_after_mz q2Ln_e2 (ss_mem q2Ln_e2) 56 0x542cc).
Definition q2Ln_e3 : sstate := Eval vm_compute in fst (RUNTO (ss_after_mz q2Ln_e2 (ss_mem q2Ln_e2) 56 0x542cc)).
Lemma r_q2Ln_3 : RUNTO (ss_after_mz q2Ln_e2 (ss_mem q2Ln_e2) 56 0x542cc) = (q2Ln_e3, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition q2Ho_s0 : sstate := Eval vm_compute in (ssS2H).
Definition q2Ho_e0 : sstate := Eval vm_compute in fst (RUN (ssS2H)).
Lemma r_q2Ho_0 : RUN (ssS2H) = (q2Ho_e0, RS_stopped (SR_branch BC_EQ (SOff 10 0) (SOff 11 0))). Proof. vm_compute. reflexivity. Qed.
Definition q2HoA_s0 : sstate := Eval vm_compute in (AC q2Ho_e0 BC_NE (RG q2Ho_e0 10) (RG q2Ho_e0 11)).
Definition q2HoA_e0 : sstate := Eval vm_compute in fst (RUN (AC q2Ho_e0 BC_NE (RG q2Ho_e0 10) (RG q2Ho_e0 11))).
Lemma r_q2HoA_0 : RUN (AC q2Ho_e0 BC_NE (RG q2Ho_e0 10) (RG q2Ho_e0 11)) = (q2HoA_e0, RS_stopped (SR_branch BC_GEU (SOff 11 0) (SAlu ALU_ADD (SOff 10 0) (SOff 12 0)))). Proof. vm_compute. reflexivity. Qed.
Definition q2HoA_s1 : sstate := Eval vm_compute in (AC q2HoA_e0 BC_GEU (RG q2HoA_e0 11) (RG q2HoA_e0 19)).
Definition q2HoA_e1 : sstate := Eval vm_compute in fst (RUN (AC q2HoA_e0 BC_GEU (RG q2HoA_e0 11) (RG q2HoA_e0 19))).
Lemma r_q2HoA_1 : RUN (AC q2HoA_e0 BC_GEU (RG q2HoA_e0 11) (RG q2HoA_e0 19)) = (q2HoA_e1, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Definition q2H_c : sstate := Eval vm_compute in DROPC q2HoA_e1.
Definition q2HoB_s0 : sstate := Eval vm_compute in (AC q2HoA_e0 BC_LTU (RG q2HoA_e0 11) (RG q2HoA_e0 19)).
Definition q2HoB_e0 : sstate := Eval vm_compute in fst (RUN (AC q2HoA_e0 BC_LTU (RG q2HoA_e0 11) (RG q2HoA_e0 19))).
Lemma r_q2HoB_0 : RUN (AC q2HoA_e0 BC_LTU (RG q2HoA_e0 11) (RG q2HoA_e0 19)) = (q2HoB_e0, RS_stopped (SR_branch BC_LTU (SOff 10 0) (SAlu ALU_ADD (SOff 11 0) (SOff 12 0)))). Proof. vm_compute. reflexivity. Qed.
Definition q2HoB_s1 : sstate := Eval vm_compute in (AC q2HoB_e0 BC_GEU (RG q2HoB_e0 10) (RG q2HoB_e0 21)).
Definition q2HoB_e1 : sstate := Eval vm_compute in fst (RUN (AC q2HoB_e0 BC_GEU (RG q2HoB_e0 10) (RG q2HoB_e0 21))).
Lemma r_q2HoB_1 : RUN (AC q2HoB_e0 BC_GEU (RG q2HoB_e0 10) (RG q2HoB_e0 21)) = (q2HoB_e1, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Lemma q2HoB_canon : DROPC q2HoB_e1 = q2H_c. Proof. reflexivity. Qed.
Lemma q2HoA_canon : DROPC q2HoA_e1 = q2H_c. Proof. reflexivity. Qed.
Definition q2H_s0 : sstate := Eval vm_compute in (q2H_c).
Definition q2H_e0 : sstate := Eval vm_compute in fst (RUN (q2H_c)).
Lemma r_q2H_0 : RUN (q2H_c) = (q2H_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Definition q2H_s1 : sstate := Eval vm_compute in (AC q2H_e0 BC_GEU (RG q2H_e0 13) (RG q2H_e0 12)).
Definition q2H_e1 : sstate := Eval vm_compute in fst (RUN (AC q2H_e0 BC_GEU (RG q2H_e0 13) (RG q2H_e0 12))).
Lemma r_q2H_1 : RUN (AC q2H_e0 BC_GEU (RG q2H_e0 13) (RG q2H_e0 12)) = (q2H_e1, RS_stopped (SR_branch BC_LTU (SLit 140737488355327) (SAlu ALU_ADD (SOff 11 0) (SOff 12 0)))). Proof. vm_compute. reflexivity. Qed.
Definition q2H_s2 : sstate := Eval vm_compute in (AC q2H_e1 BC_GEU (SLit 140737488355327) (RG q2H_e1 18)).
Definition q2H_e2 : sstate := Eval vm_compute in fst (RUN (AC q2H_e1 BC_GEU (SLit 140737488355327) (RG q2H_e1 18))).
Lemma r_q2H_2 : RUN (AC q2H_e1 BC_GEU (SLit 140737488355327) (RG q2H_e1 18)) = (q2H_e2, RS_stopped (SR_branch BC_GEU (SOff 11 0) (SAlu ALU_ADD (SOff 11 0) (SOff 12 0)))). Proof. vm_compute. reflexivity. Qed.
Definition q2H_s3 : sstate := Eval vm_compute in (AC q2H_e2 BC_LTU (RG q2H_e2 8) (RG q2H_e2 18)).
Definition q2H_e3 : sstate := Eval vm_compute in fst (RUN (AC q2H_e2 BC_LTU (RG q2H_e2 8) (RG q2H_e2 18))).
Lemma r_q2H_3 : RUN (AC q2H_e2 BC_LTU (RG q2H_e2 8) (RG q2H_e2 18)) = (q2H_e3, RS_stopped (SR_branch BC_EQ (SOff 34 0) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition q2Hz_s0 : sstate := Eval vm_compute in (AC q2H_e3 BC_EQ (RG q2H_e3 11) (SLit 0)).
Definition q2Hz_e0 : sstate := Eval vm_compute in fst (RUN (AC q2H_e3 BC_EQ (RG q2H_e3 11) (SLit 0))).
Lemma r_q2Hz_0 : RUN (AC q2H_e3 BC_EQ (RG q2H_e3 11) (SLit 0)) = (q2Hz_e0, RS_stopped (SR_branch BC_GEU (SOff 39 2147450880) (SOff 40 2147450880))). Proof. vm_compute. reflexivity. Qed.
Definition q2Hz_s1 : sstate := Eval vm_compute in (AC q2Hz_e0 BC_LTU (RG q2Hz_e0 19) (RG q2Hz_e0 10)).
Definition q2Hz_e1 : sstate := Eval vm_compute in fst (RUN (AC q2Hz_e0 BC_LTU (RG q2Hz_e0 19) (RG q2Hz_e0 10))).
Lemma r_q2Hz_1 : RUN (AC q2Hz_e0 BC_LTU (RG q2Hz_e0 19) (RG q2Hz_e0 10)) = (q2Hz_e1, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition q2Hz_s2 : sstate := Eval vm_compute in (ss_after_mz q2Hz_e1 (ss_mem q2Hz_e1) 56 0x542cc).
Definition q2Hz_e2 : sstate := Eval vm_compute in fst (RUNTO (ss_after_mz q2Hz_e1 (ss_mem q2Hz_e1) 56 0x542cc)).
Lemma r_q2Hz_2 : RUNTO (ss_after_mz q2Hz_e1 (ss_mem q2Hz_e1) 56 0x542cc) = (q2Hz_e2, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition q2Hn_s0 : sstate := Eval vm_compute in (AC q2H_e3 BC_NE (RG q2H_e3 11) (SLit 0)).
Definition q2Hn_e0 : sstate := Eval vm_compute in fst (RUN (AC q2H_e3 BC_NE (RG q2H_e3 11) (SLit 0))).
Lemma r_q2Hn_0 : RUN (AC q2H_e3 BC_NE (RG q2H_e3 11) (SLit 0)) = (q2Hn_e0, RS_stopped (SR_branch BC_LT (SAlu ALU_AND (SAlu ALU_ADD (SOff 11 (-1)) (SOff 12 0)) (SLit 7)) (SOff 34 0))). Proof. vm_compute. reflexivity. Qed.
Definition q2Hn_s1 : sstate := Eval vm_compute in (AC q2Hn_e0 BC_LT (RG q2Hn_e0 12) (RG q2Hn_e0 11)).
Definition q2Hn_e1 : sstate := Eval vm_compute in fst (RUN (AC q2Hn_e0 BC_LT (RG q2Hn_e0 12) (RG q2Hn_e0 11))).
Lemma r_q2Hn_1 : RUN (AC q2Hn_e0 BC_LT (RG q2Hn_e0 12) (RG q2Hn_e0 11)) = (q2Hn_e1, RS_stopped (SR_branch BC_GEU (SOff 39 2147450880) (SOff 40 2147450880))). Proof. vm_compute. reflexivity. Qed.
Definition q2Hn_s2 : sstate := Eval vm_compute in (AC q2Hn_e1 BC_LTU (RG q2Hn_e1 19) (RG q2Hn_e1 10)).
Definition q2Hn_e2 : sstate := Eval vm_compute in fst (RUN (AC q2Hn_e1 BC_LTU (RG q2Hn_e1 19) (RG q2Hn_e1 10))).
Lemma r_q2Hn_2 : RUN (AC q2Hn_e1 BC_LTU (RG q2Hn_e1 19) (RG q2Hn_e1 10)) = (q2Hn_e2, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition q2Hn_s3 : sstate := Eval vm_compute in (ss_after_mz q2Hn_e2 (ss_mem q2Hn_e2) 56 0x542cc).
Definition q2Hn_e3 : sstate := Eval vm_compute in fst (RUNTO (ss_after_mz q2Hn_e2 (ss_mem q2Hn_e2) 56 0x542cc)).
Lemma r_q2Hn_3 : RUNTO (ss_after_mz q2Hn_e2 (ss_mem q2Hn_e2) 56 0x542cc) = (q2Hn_e3, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition w1_0_s0 : sstate := Eval vm_compute in (ssD1 0).
Definition w1_0_e0 : sstate := Eval vm_compute in fst (RUN (ssD1 0)).
Lemma r_w1_0_0 : RUN (ssD1 0) = (w1_0_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 10 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Definition w1_0_s1 : sstate := Eval vm_compute in (AC w1_0_e0 BC_GEU (RG w1_0_e0 13) (RG w1_0_e0 12)).
Definition w1_0_e1 : sstate := Eval vm_compute in fst (RUN (AC w1_0_e0 BC_GEU (RG w1_0_e0 13) (RG w1_0_e0 12))).
Lemma r_w1_0_1 : RUN (AC w1_0_e0 BC_GEU (RG w1_0_e0 13) (RG w1_0_e0 12)) = (w1_0_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 12 (-65)))). Proof. vm_compute. reflexivity. Qed.
Definition w1_0_s2 : sstate := Eval vm_compute in (AC w1_0_e1 BC_LTU (RG w1_0_e1 13) (RG w1_0_e1 22)).
Definition w1_0_e2 : sstate := Eval vm_compute in fst (RUN (AC w1_0_e1 BC_LTU (RG w1_0_e1 13) (RG w1_0_e1 22))).
Lemma r_w1_0_2 : RUN (AC w1_0_e1 BC_LTU (RG w1_0_e1 13) (RG w1_0_e1 22)) = (w1_0_e2, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 42 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition w1_0_s3 : sstate := Eval vm_compute in (set_regs_pc (set_regs_pc w1_0_e2 [((15%bv : bv 5), SOff 45 0)] 0x516c0) [((16%bv : bv 5), SOff 46 0)] 0x516c4).
Definition w1_0_e3 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc w1_0_e2 [((15%bv : bv 5), SOff 45 0)] 0x516c0) [((16%bv : bv 5), SOff 46 0)] 0x516c4)).
Lemma r_w1_0_3 : RUN (set_regs_pc (set_regs_pc w1_0_e2 [((15%bv : bv 5), SOff 45 0)] 0x516c0) [((16%bv : bv 5), SOff 46 0)] 0x516c4) = (w1_0_e3, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 46 0) (SOff 45 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition w1_0z_s0 : sstate := Eval vm_compute in (AC w1_0_e3 BC_EQ (RG w1_0_e3 15) (SLit 0)).
Definition w1_0z_e0 : sstate := Eval vm_compute in fst (RUN (AC w1_0_e3 BC_EQ (RG w1_0_e3 15) (SLit 0))).
Lemma r_w1_0z_0 : RUN (AC w1_0_e3 BC_EQ (RG w1_0_e3 15) (SLit 0)) = (w1_0z_e0, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition w1_0n_s0 : sstate := Eval vm_compute in (AC w1_0_e3 BC_NE (RG w1_0_e3 15) (SLit 0)).
Definition w1_0n_e0 : sstate := Eval vm_compute in fst (RUN (AC w1_0_e3 BC_NE (RG w1_0_e3 15) (SLit 0))).
Lemma r_w1_0n_0 : RUN (AC w1_0_e3 BC_NE (RG w1_0_e3 15) (SLit 0)) = (w1_0n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 0%nat 10 12 44) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition w1_0n_s1 : sstate := Eval vm_compute in (AC w1_0n_e0 BC_EQ (RG w1_0n_e0 13) (SLit 0)).
Definition w1_0n_e1 : sstate := Eval vm_compute in fst (RUN (AC w1_0n_e0 BC_EQ (RG w1_0n_e0 13) (SLit 0))).
Lemma r_w1_0n_1 : RUN (AC w1_0n_e0 BC_EQ (RG w1_0n_e0 13) (SLit 0)) = (w1_0n_e1, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition w1_1_s0 : sstate := Eval vm_compute in (ssD1 1).
Definition w1_1_e0 : sstate := Eval vm_compute in fst (RUN (ssD1 1)).
Lemma r_w1_1_0 : RUN (ssD1 1) = (w1_1_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 10 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Definition w1_1_s1 : sstate := Eval vm_compute in (AC w1_1_e0 BC_GEU (RG w1_1_e0 13) (RG w1_1_e0 12)).
Definition w1_1_e1 : sstate := Eval vm_compute in fst (RUN (AC w1_1_e0 BC_GEU (RG w1_1_e0 13) (RG w1_1_e0 12))).
Lemma r_w1_1_1 : RUN (AC w1_1_e0 BC_GEU (RG w1_1_e0 13) (RG w1_1_e0 12)) = (w1_1_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 12 (-65)))). Proof. vm_compute. reflexivity. Qed.
Definition w1_1_s2 : sstate := Eval vm_compute in (AC w1_1_e1 BC_LTU (RG w1_1_e1 13) (RG w1_1_e1 22)).
Definition w1_1_e2 : sstate := Eval vm_compute in fst (RUN (AC w1_1_e1 BC_LTU (RG w1_1_e1 13) (RG w1_1_e1 22))).
Lemma r_w1_1_2 : RUN (AC w1_1_e1 BC_LTU (RG w1_1_e1 13) (RG w1_1_e1 22)) = (w1_1_e2, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 42 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition w1_1_s3 : sstate := Eval vm_compute in (set_regs_pc (set_regs_pc w1_1_e2 [((15%bv : bv 5), SOff 45 0)] 0x516c0) [((16%bv : bv 5), SOff 46 0)] 0x516c4).
Definition w1_1_e3 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc w1_1_e2 [((15%bv : bv 5), SOff 45 0)] 0x516c0) [((16%bv : bv 5), SOff 46 0)] 0x516c4)).
Lemma r_w1_1_3 : RUN (set_regs_pc (set_regs_pc w1_1_e2 [((15%bv : bv 5), SOff 45 0)] 0x516c0) [((16%bv : bv 5), SOff 46 0)] 0x516c4) = (w1_1_e3, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 46 0) (SOff 45 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition w1_1z_s0 : sstate := Eval vm_compute in (AC w1_1_e3 BC_EQ (RG w1_1_e3 15) (SLit 0)).
Definition w1_1z_e0 : sstate := Eval vm_compute in fst (RUN (AC w1_1_e3 BC_EQ (RG w1_1_e3 15) (SLit 0))).
Lemma r_w1_1z_0 : RUN (AC w1_1_e3 BC_EQ (RG w1_1_e3 15) (SLit 0)) = (w1_1z_e0, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition w1_1n_s0 : sstate := Eval vm_compute in (AC w1_1_e3 BC_NE (RG w1_1_e3 15) (SLit 0)).
Definition w1_1n_e0 : sstate := Eval vm_compute in fst (RUN (AC w1_1_e3 BC_NE (RG w1_1_e3 15) (SLit 0))).
Lemma r_w1_1n_0 : RUN (AC w1_1_e3 BC_NE (RG w1_1_e3 15) (SLit 0)) = (w1_1n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 1%nat 10 12 44) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition w1_1n_s1 : sstate := Eval vm_compute in (AC w1_1n_e0 BC_EQ (RG w1_1n_e0 13) (SLit 0)).
Definition w1_1n_e1 : sstate := Eval vm_compute in fst (RUN (AC w1_1n_e0 BC_EQ (RG w1_1n_e0 13) (SLit 0))).
Lemma r_w1_1n_1 : RUN (AC w1_1n_e0 BC_EQ (RG w1_1n_e0 13) (SLit 0)) = (w1_1n_e1, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition w1_2_s0 : sstate := Eval vm_compute in (ssD1 2).
Definition w1_2_e0 : sstate := Eval vm_compute in fst (RUN (ssD1 2)).
Lemma r_w1_2_0 : RUN (ssD1 2) = (w1_2_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 10 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Definition w1_2_s1 : sstate := Eval vm_compute in (AC w1_2_e0 BC_GEU (RG w1_2_e0 13) (RG w1_2_e0 12)).
Definition w1_2_e1 : sstate := Eval vm_compute in fst (RUN (AC w1_2_e0 BC_GEU (RG w1_2_e0 13) (RG w1_2_e0 12))).
Lemma r_w1_2_1 : RUN (AC w1_2_e0 BC_GEU (RG w1_2_e0 13) (RG w1_2_e0 12)) = (w1_2_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 12 (-65)))). Proof. vm_compute. reflexivity. Qed.
Definition w1_2_s2 : sstate := Eval vm_compute in (AC w1_2_e1 BC_LTU (RG w1_2_e1 13) (RG w1_2_e1 22)).
Definition w1_2_e2 : sstate := Eval vm_compute in fst (RUN (AC w1_2_e1 BC_LTU (RG w1_2_e1 13) (RG w1_2_e1 22))).
Lemma r_w1_2_2 : RUN (AC w1_2_e1 BC_LTU (RG w1_2_e1 13) (RG w1_2_e1 22)) = (w1_2_e2, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 42 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition w1_2_s3 : sstate := Eval vm_compute in (set_regs_pc (set_regs_pc w1_2_e2 [((15%bv : bv 5), SOff 45 0)] 0x516c0) [((16%bv : bv 5), SOff 46 0)] 0x516c4).
Definition w1_2_e3 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc w1_2_e2 [((15%bv : bv 5), SOff 45 0)] 0x516c0) [((16%bv : bv 5), SOff 46 0)] 0x516c4)).
Lemma r_w1_2_3 : RUN (set_regs_pc (set_regs_pc w1_2_e2 [((15%bv : bv 5), SOff 45 0)] 0x516c0) [((16%bv : bv 5), SOff 46 0)] 0x516c4) = (w1_2_e3, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 46 0) (SOff 45 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition w1_2z_s0 : sstate := Eval vm_compute in (AC w1_2_e3 BC_EQ (RG w1_2_e3 15) (SLit 0)).
Definition w1_2z_e0 : sstate := Eval vm_compute in fst (RUN (AC w1_2_e3 BC_EQ (RG w1_2_e3 15) (SLit 0))).
Lemma r_w1_2z_0 : RUN (AC w1_2_e3 BC_EQ (RG w1_2_e3 15) (SLit 0)) = (w1_2z_e0, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition w1_2n_s0 : sstate := Eval vm_compute in (AC w1_2_e3 BC_NE (RG w1_2_e3 15) (SLit 0)).
Definition w1_2n_e0 : sstate := Eval vm_compute in fst (RUN (AC w1_2_e3 BC_NE (RG w1_2_e3 15) (SLit 0))).
Lemma r_w1_2n_0 : RUN (AC w1_2_e3 BC_NE (RG w1_2_e3 15) (SLit 0)) = (w1_2n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 2%nat 10 12 44) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition w1_2n_s1 : sstate := Eval vm_compute in (AC w1_2n_e0 BC_EQ (RG w1_2n_e0 13) (SLit 0)).
Definition w1_2n_e1 : sstate := Eval vm_compute in fst (RUN (AC w1_2n_e0 BC_EQ (RG w1_2n_e0 13) (SLit 0))).
Lemma r_w1_2n_1 : RUN (AC w1_2n_e0 BC_EQ (RG w1_2n_e0 13) (SLit 0)) = (w1_2n_e1, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition w1_3_s0 : sstate := Eval vm_compute in (ssD1 3).
Definition w1_3_e0 : sstate := Eval vm_compute in fst (RUN (ssD1 3)).
Lemma r_w1_3_0 : RUN (ssD1 3) = (w1_3_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 10 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Definition w1_3_s1 : sstate := Eval vm_compute in (AC w1_3_e0 BC_GEU (RG w1_3_e0 13) (RG w1_3_e0 12)).
Definition w1_3_e1 : sstate := Eval vm_compute in fst (RUN (AC w1_3_e0 BC_GEU (RG w1_3_e0 13) (RG w1_3_e0 12))).
Lemma r_w1_3_1 : RUN (AC w1_3_e0 BC_GEU (RG w1_3_e0 13) (RG w1_3_e0 12)) = (w1_3_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 12 (-65)))). Proof. vm_compute. reflexivity. Qed.
Definition w1_3_s2 : sstate := Eval vm_compute in (AC w1_3_e1 BC_LTU (RG w1_3_e1 13) (RG w1_3_e1 22)).
Definition w1_3_e2 : sstate := Eval vm_compute in fst (RUN (AC w1_3_e1 BC_LTU (RG w1_3_e1 13) (RG w1_3_e1 22))).
Lemma r_w1_3_2 : RUN (AC w1_3_e1 BC_LTU (RG w1_3_e1 13) (RG w1_3_e1 22)) = (w1_3_e2, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 42 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition w1_3_s3 : sstate := Eval vm_compute in (set_regs_pc (set_regs_pc w1_3_e2 [((15%bv : bv 5), SOff 45 0)] 0x516c0) [((16%bv : bv 5), SOff 46 0)] 0x516c4).
Definition w1_3_e3 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc w1_3_e2 [((15%bv : bv 5), SOff 45 0)] 0x516c0) [((16%bv : bv 5), SOff 46 0)] 0x516c4)).
Lemma r_w1_3_3 : RUN (set_regs_pc (set_regs_pc w1_3_e2 [((15%bv : bv 5), SOff 45 0)] 0x516c0) [((16%bv : bv 5), SOff 46 0)] 0x516c4) = (w1_3_e3, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 46 0) (SOff 45 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition w1_3z_s0 : sstate := Eval vm_compute in (AC w1_3_e3 BC_EQ (RG w1_3_e3 15) (SLit 0)).
Definition w1_3z_e0 : sstate := Eval vm_compute in fst (RUN (AC w1_3_e3 BC_EQ (RG w1_3_e3 15) (SLit 0))).
Lemma r_w1_3z_0 : RUN (AC w1_3_e3 BC_EQ (RG w1_3_e3 15) (SLit 0)) = (w1_3z_e0, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition w1_3n_s0 : sstate := Eval vm_compute in (AC w1_3_e3 BC_NE (RG w1_3_e3 15) (SLit 0)).
Definition w1_3n_e0 : sstate := Eval vm_compute in fst (RUN (AC w1_3_e3 BC_NE (RG w1_3_e3 15) (SLit 0))).
Lemma r_w1_3n_0 : RUN (AC w1_3_e3 BC_NE (RG w1_3_e3 15) (SLit 0)) = (w1_3n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 3%nat 10 12 44) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition w1_3n_s1 : sstate := Eval vm_compute in (AC w1_3n_e0 BC_EQ (RG w1_3n_e0 13) (SLit 0)).
Definition w1_3n_e1 : sstate := Eval vm_compute in fst (RUN (AC w1_3n_e0 BC_EQ (RG w1_3n_e0 13) (SLit 0))).
Lemma r_w1_3n_1 : RUN (AC w1_3n_e0 BC_EQ (RG w1_3n_e0 13) (SLit 0)) = (w1_3n_e1, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition w1_4_s0 : sstate := Eval vm_compute in (ssD1 4).
Definition w1_4_e0 : sstate := Eval vm_compute in fst (RUN (ssD1 4)).
Lemma r_w1_4_0 : RUN (ssD1 4) = (w1_4_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 10 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Definition w1_4_s1 : sstate := Eval vm_compute in (AC w1_4_e0 BC_GEU (RG w1_4_e0 13) (RG w1_4_e0 12)).
Definition w1_4_e1 : sstate := Eval vm_compute in fst (RUN (AC w1_4_e0 BC_GEU (RG w1_4_e0 13) (RG w1_4_e0 12))).
Lemma r_w1_4_1 : RUN (AC w1_4_e0 BC_GEU (RG w1_4_e0 13) (RG w1_4_e0 12)) = (w1_4_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 12 (-65)))). Proof. vm_compute. reflexivity. Qed.
Definition w1_4_s2 : sstate := Eval vm_compute in (AC w1_4_e1 BC_LTU (RG w1_4_e1 13) (RG w1_4_e1 22)).
Definition w1_4_e2 : sstate := Eval vm_compute in fst (RUN (AC w1_4_e1 BC_LTU (RG w1_4_e1 13) (RG w1_4_e1 22))).
Lemma r_w1_4_2 : RUN (AC w1_4_e1 BC_LTU (RG w1_4_e1 13) (RG w1_4_e1 22)) = (w1_4_e2, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 42 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition w1_4_s3 : sstate := Eval vm_compute in (set_regs_pc (set_regs_pc w1_4_e2 [((15%bv : bv 5), SOff 45 0)] 0x516c0) [((16%bv : bv 5), SOff 46 0)] 0x516c4).
Definition w1_4_e3 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc w1_4_e2 [((15%bv : bv 5), SOff 45 0)] 0x516c0) [((16%bv : bv 5), SOff 46 0)] 0x516c4)).
Lemma r_w1_4_3 : RUN (set_regs_pc (set_regs_pc w1_4_e2 [((15%bv : bv 5), SOff 45 0)] 0x516c0) [((16%bv : bv 5), SOff 46 0)] 0x516c4) = (w1_4_e3, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 46 0) (SOff 45 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition w1_4z_s0 : sstate := Eval vm_compute in (AC w1_4_e3 BC_EQ (RG w1_4_e3 15) (SLit 0)).
Definition w1_4z_e0 : sstate := Eval vm_compute in fst (RUN (AC w1_4_e3 BC_EQ (RG w1_4_e3 15) (SLit 0))).
Lemma r_w1_4z_0 : RUN (AC w1_4_e3 BC_EQ (RG w1_4_e3 15) (SLit 0)) = (w1_4z_e0, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition w1_4n_s0 : sstate := Eval vm_compute in (AC w1_4_e3 BC_NE (RG w1_4_e3 15) (SLit 0)).
Definition w1_4n_e0 : sstate := Eval vm_compute in fst (RUN (AC w1_4_e3 BC_NE (RG w1_4_e3 15) (SLit 0))).
Lemma r_w1_4n_0 : RUN (AC w1_4_e3 BC_NE (RG w1_4_e3 15) (SLit 0)) = (w1_4n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 4%nat 10 12 44) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition w1_4n_s1 : sstate := Eval vm_compute in (AC w1_4n_e0 BC_EQ (RG w1_4n_e0 13) (SLit 0)).
Definition w1_4n_e1 : sstate := Eval vm_compute in fst (RUN (AC w1_4n_e0 BC_EQ (RG w1_4n_e0 13) (SLit 0))).
Lemma r_w1_4n_1 : RUN (AC w1_4n_e0 BC_EQ (RG w1_4n_e0 13) (SLit 0)) = (w1_4n_e1, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition w1_5_s0 : sstate := Eval vm_compute in (ssD1 5).
Definition w1_5_e0 : sstate := Eval vm_compute in fst (RUN (ssD1 5)).
Lemma r_w1_5_0 : RUN (ssD1 5) = (w1_5_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 10 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Definition w1_5_s1 : sstate := Eval vm_compute in (AC w1_5_e0 BC_GEU (RG w1_5_e0 13) (RG w1_5_e0 12)).
Definition w1_5_e1 : sstate := Eval vm_compute in fst (RUN (AC w1_5_e0 BC_GEU (RG w1_5_e0 13) (RG w1_5_e0 12))).
Lemma r_w1_5_1 : RUN (AC w1_5_e0 BC_GEU (RG w1_5_e0 13) (RG w1_5_e0 12)) = (w1_5_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 12 (-65)))). Proof. vm_compute. reflexivity. Qed.
Definition w1_5_s2 : sstate := Eval vm_compute in (AC w1_5_e1 BC_LTU (RG w1_5_e1 13) (RG w1_5_e1 22)).
Definition w1_5_e2 : sstate := Eval vm_compute in fst (RUN (AC w1_5_e1 BC_LTU (RG w1_5_e1 13) (RG w1_5_e1 22))).
Lemma r_w1_5_2 : RUN (AC w1_5_e1 BC_LTU (RG w1_5_e1 13) (RG w1_5_e1 22)) = (w1_5_e2, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 42 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition w1_5_s3 : sstate := Eval vm_compute in (set_regs_pc (set_regs_pc w1_5_e2 [((15%bv : bv 5), SOff 45 0)] 0x516c0) [((16%bv : bv 5), SOff 46 0)] 0x516c4).
Definition w1_5_e3 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc w1_5_e2 [((15%bv : bv 5), SOff 45 0)] 0x516c0) [((16%bv : bv 5), SOff 46 0)] 0x516c4)).
Lemma r_w1_5_3 : RUN (set_regs_pc (set_regs_pc w1_5_e2 [((15%bv : bv 5), SOff 45 0)] 0x516c0) [((16%bv : bv 5), SOff 46 0)] 0x516c4) = (w1_5_e3, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 46 0) (SOff 45 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition w1_5z_s0 : sstate := Eval vm_compute in (AC w1_5_e3 BC_EQ (RG w1_5_e3 15) (SLit 0)).
Definition w1_5z_e0 : sstate := Eval vm_compute in fst (RUN (AC w1_5_e3 BC_EQ (RG w1_5_e3 15) (SLit 0))).
Lemma r_w1_5z_0 : RUN (AC w1_5_e3 BC_EQ (RG w1_5_e3 15) (SLit 0)) = (w1_5z_e0, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition w1_5n_s0 : sstate := Eval vm_compute in (AC w1_5_e3 BC_NE (RG w1_5_e3 15) (SLit 0)).
Definition w1_5n_e0 : sstate := Eval vm_compute in fst (RUN (AC w1_5_e3 BC_NE (RG w1_5_e3 15) (SLit 0))).
Lemma r_w1_5n_0 : RUN (AC w1_5_e3 BC_NE (RG w1_5_e3 15) (SLit 0)) = (w1_5n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 5%nat 10 12 44) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition w1_5n_s1 : sstate := Eval vm_compute in (AC w1_5n_e0 BC_EQ (RG w1_5n_e0 13) (SLit 0)).
Definition w1_5n_e1 : sstate := Eval vm_compute in fst (RUN (AC w1_5n_e0 BC_EQ (RG w1_5n_e0 13) (SLit 0))).
Lemma r_w1_5n_1 : RUN (AC w1_5n_e0 BC_EQ (RG w1_5n_e0 13) (SLit 0)) = (w1_5n_e1, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition w1_6_s0 : sstate := Eval vm_compute in (ssD1 6).
Definition w1_6_e0 : sstate := Eval vm_compute in fst (RUN (ssD1 6)).
Lemma r_w1_6_0 : RUN (ssD1 6) = (w1_6_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 10 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Definition w1_6_s1 : sstate := Eval vm_compute in (AC w1_6_e0 BC_GEU (RG w1_6_e0 13) (RG w1_6_e0 12)).
Definition w1_6_e1 : sstate := Eval vm_compute in fst (RUN (AC w1_6_e0 BC_GEU (RG w1_6_e0 13) (RG w1_6_e0 12))).
Lemma r_w1_6_1 : RUN (AC w1_6_e0 BC_GEU (RG w1_6_e0 13) (RG w1_6_e0 12)) = (w1_6_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 12 (-65)))). Proof. vm_compute. reflexivity. Qed.
Definition w1_6_s2 : sstate := Eval vm_compute in (AC w1_6_e1 BC_LTU (RG w1_6_e1 13) (RG w1_6_e1 22)).
Definition w1_6_e2 : sstate := Eval vm_compute in fst (RUN (AC w1_6_e1 BC_LTU (RG w1_6_e1 13) (RG w1_6_e1 22))).
Lemma r_w1_6_2 : RUN (AC w1_6_e1 BC_LTU (RG w1_6_e1 13) (RG w1_6_e1 22)) = (w1_6_e2, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 42 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition w1_6_s3 : sstate := Eval vm_compute in (set_regs_pc (set_regs_pc w1_6_e2 [((15%bv : bv 5), SOff 45 0)] 0x516c0) [((16%bv : bv 5), SOff 46 0)] 0x516c4).
Definition w1_6_e3 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc w1_6_e2 [((15%bv : bv 5), SOff 45 0)] 0x516c0) [((16%bv : bv 5), SOff 46 0)] 0x516c4)).
Lemma r_w1_6_3 : RUN (set_regs_pc (set_regs_pc w1_6_e2 [((15%bv : bv 5), SOff 45 0)] 0x516c0) [((16%bv : bv 5), SOff 46 0)] 0x516c4) = (w1_6_e3, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 46 0) (SOff 45 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition w1_6z_s0 : sstate := Eval vm_compute in (AC w1_6_e3 BC_EQ (RG w1_6_e3 15) (SLit 0)).
Definition w1_6z_e0 : sstate := Eval vm_compute in fst (RUN (AC w1_6_e3 BC_EQ (RG w1_6_e3 15) (SLit 0))).
Lemma r_w1_6z_0 : RUN (AC w1_6_e3 BC_EQ (RG w1_6_e3 15) (SLit 0)) = (w1_6z_e0, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition w1_6n_s0 : sstate := Eval vm_compute in (AC w1_6_e3 BC_NE (RG w1_6_e3 15) (SLit 0)).
Definition w1_6n_e0 : sstate := Eval vm_compute in fst (RUN (AC w1_6_e3 BC_NE (RG w1_6_e3 15) (SLit 0))).
Lemma r_w1_6n_0 : RUN (AC w1_6_e3 BC_NE (RG w1_6_e3 15) (SLit 0)) = (w1_6n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 6%nat 10 12 44) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition w1_6n_s1 : sstate := Eval vm_compute in (AC w1_6n_e0 BC_EQ (RG w1_6n_e0 13) (SLit 0)).
Definition w1_6n_e1 : sstate := Eval vm_compute in fst (RUN (AC w1_6n_e0 BC_EQ (RG w1_6n_e0 13) (SLit 0))).
Lemma r_w1_6n_1 : RUN (AC w1_6n_e0 BC_EQ (RG w1_6n_e0 13) (SLit 0)) = (w1_6n_e1, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition w1_7_s0 : sstate := Eval vm_compute in (ssD1 7).
Definition w1_7_e0 : sstate := Eval vm_compute in fst (RUN (ssD1 7)).
Lemma r_w1_7_0 : RUN (ssD1 7) = (w1_7_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 10 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Definition w1_7_s1 : sstate := Eval vm_compute in (AC w1_7_e0 BC_GEU (RG w1_7_e0 13) (RG w1_7_e0 12)).
Definition w1_7_e1 : sstate := Eval vm_compute in fst (RUN (AC w1_7_e0 BC_GEU (RG w1_7_e0 13) (RG w1_7_e0 12))).
Lemma r_w1_7_1 : RUN (AC w1_7_e0 BC_GEU (RG w1_7_e0 13) (RG w1_7_e0 12)) = (w1_7_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 12 (-65)))). Proof. vm_compute. reflexivity. Qed.
Definition w1_7_s2 : sstate := Eval vm_compute in (AC w1_7_e1 BC_LTU (RG w1_7_e1 13) (RG w1_7_e1 22)).
Definition w1_7_e2 : sstate := Eval vm_compute in fst (RUN (AC w1_7_e1 BC_LTU (RG w1_7_e1 13) (RG w1_7_e1 22))).
Lemma r_w1_7_2 : RUN (AC w1_7_e1 BC_LTU (RG w1_7_e1 13) (RG w1_7_e1 22)) = (w1_7_e2, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 42 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition w1_7_s3 : sstate := Eval vm_compute in (set_regs_pc (set_regs_pc w1_7_e2 [((15%bv : bv 5), SOff 45 0)] 0x516c0) [((16%bv : bv 5), SOff 46 0)] 0x516c4).
Definition w1_7_e3 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc w1_7_e2 [((15%bv : bv 5), SOff 45 0)] 0x516c0) [((16%bv : bv 5), SOff 46 0)] 0x516c4)).
Lemma r_w1_7_3 : RUN (set_regs_pc (set_regs_pc w1_7_e2 [((15%bv : bv 5), SOff 45 0)] 0x516c0) [((16%bv : bv 5), SOff 46 0)] 0x516c4) = (w1_7_e3, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 46 0) (SOff 45 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition w1_7z_s0 : sstate := Eval vm_compute in (AC w1_7_e3 BC_EQ (RG w1_7_e3 15) (SLit 0)).
Definition w1_7z_e0 : sstate := Eval vm_compute in fst (RUN (AC w1_7_e3 BC_EQ (RG w1_7_e3 15) (SLit 0))).
Lemma r_w1_7z_0 : RUN (AC w1_7_e3 BC_EQ (RG w1_7_e3 15) (SLit 0)) = (w1_7z_e0, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition w1_7n_s0 : sstate := Eval vm_compute in (AC w1_7_e3 BC_NE (RG w1_7_e3 15) (SLit 0)).
Definition w1_7n_e0 : sstate := Eval vm_compute in fst (RUN (AC w1_7_e3 BC_NE (RG w1_7_e3 15) (SLit 0))).
Lemma r_w1_7n_0 : RUN (AC w1_7_e3 BC_NE (RG w1_7_e3 15) (SLit 0)) = (w1_7n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 7%nat 10 12 44) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition w1_7n_s1 : sstate := Eval vm_compute in (AC w1_7n_e0 BC_EQ (RG w1_7n_e0 13) (SLit 0)).
Definition w1_7n_e1 : sstate := Eval vm_compute in fst (RUN (AC w1_7n_e0 BC_EQ (RG w1_7n_e0 13) (SLit 0))).
Lemma r_w1_7n_1 : RUN (AC w1_7n_e0 BC_EQ (RG w1_7n_e0 13) (SLit 0)) = (w1_7n_e1, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition w1_8_s0 : sstate := Eval vm_compute in (ssD1 8).
Definition w1_8_e0 : sstate := Eval vm_compute in fst (RUN (ssD1 8)).
Lemma r_w1_8_0 : RUN (ssD1 8) = (w1_8_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 10 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Definition w1_8_s1 : sstate := Eval vm_compute in (AC w1_8_e0 BC_GEU (RG w1_8_e0 13) (RG w1_8_e0 12)).
Definition w1_8_e1 : sstate := Eval vm_compute in fst (RUN (AC w1_8_e0 BC_GEU (RG w1_8_e0 13) (RG w1_8_e0 12))).
Lemma r_w1_8_1 : RUN (AC w1_8_e0 BC_GEU (RG w1_8_e0 13) (RG w1_8_e0 12)) = (w1_8_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 12 (-65)))). Proof. vm_compute. reflexivity. Qed.
Definition w1_8_s2 : sstate := Eval vm_compute in (AC w1_8_e1 BC_LTU (RG w1_8_e1 13) (RG w1_8_e1 22)).
Definition w1_8_e2 : sstate := Eval vm_compute in fst (RUN (AC w1_8_e1 BC_LTU (RG w1_8_e1 13) (RG w1_8_e1 22))).
Lemma r_w1_8_2 : RUN (AC w1_8_e1 BC_LTU (RG w1_8_e1 13) (RG w1_8_e1 22)) = (w1_8_e2, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 42 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition w1_8_s3 : sstate := Eval vm_compute in (set_regs_pc (set_regs_pc w1_8_e2 [((15%bv : bv 5), SOff 45 0)] 0x516c0) [((16%bv : bv 5), SOff 46 0)] 0x516c4).
Definition w1_8_e3 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc w1_8_e2 [((15%bv : bv 5), SOff 45 0)] 0x516c0) [((16%bv : bv 5), SOff 46 0)] 0x516c4)).
Lemma r_w1_8_3 : RUN (set_regs_pc (set_regs_pc w1_8_e2 [((15%bv : bv 5), SOff 45 0)] 0x516c0) [((16%bv : bv 5), SOff 46 0)] 0x516c4) = (w1_8_e3, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 46 0) (SOff 45 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition w1_8z_s0 : sstate := Eval vm_compute in (AC w1_8_e3 BC_EQ (RG w1_8_e3 15) (SLit 0)).
Definition w1_8z_e0 : sstate := Eval vm_compute in fst (RUN (AC w1_8_e3 BC_EQ (RG w1_8_e3 15) (SLit 0))).
Lemma r_w1_8z_0 : RUN (AC w1_8_e3 BC_EQ (RG w1_8_e3 15) (SLit 0)) = (w1_8z_e0, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition w1_8n_s0 : sstate := Eval vm_compute in (AC w1_8_e3 BC_NE (RG w1_8_e3 15) (SLit 0)).
Definition w1_8n_e0 : sstate := Eval vm_compute in fst (RUN (AC w1_8_e3 BC_NE (RG w1_8_e3 15) (SLit 0))).
Lemma r_w1_8n_0 : RUN (AC w1_8_e3 BC_NE (RG w1_8_e3 15) (SLit 0)) = (w1_8n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 8%nat 10 12 44) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition w1_8n_s1 : sstate := Eval vm_compute in (AC w1_8n_e0 BC_EQ (RG w1_8n_e0 13) (SLit 0)).
Definition w1_8n_e1 : sstate := Eval vm_compute in fst (RUN (AC w1_8n_e0 BC_EQ (RG w1_8n_e0 13) (SLit 0))).
Lemma r_w1_8n_1 : RUN (AC w1_8n_e0 BC_EQ (RG w1_8n_e0 13) (SLit 0)) = (w1_8n_e1, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition w2L_s0 : sstate := Eval vm_compute in (ssD2L).
Definition w2L_e0 : sstate := Eval vm_compute in fst (RUN (ssD2L)).
Lemma r_w2L_0 : RUN (ssD2L) = (w2L_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 10 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Definition w2L_s1 : sstate := Eval vm_compute in (AC w2L_e0 BC_GEU (RG w2L_e0 13) (RG w2L_e0 12)).
Definition w2L_e1 : sstate := Eval vm_compute in fst (RUN (AC w2L_e0 BC_GEU (RG w2L_e0 13) (RG w2L_e0 12))).
Lemma r_w2L_1 : RUN (AC w2L_e0 BC_GEU (RG w2L_e0 13) (RG w2L_e0 12)) = (w2L_e1, RS_stopped (SR_branch BC_GEU (SLit 2147450879) (SAlu ALU_ADD (SOff 10 0) (SOff 12 0)))). Proof. vm_compute. reflexivity. Qed.
Definition w2L_s2 : sstate := Eval vm_compute in (AC w2L_e1 BC_GEU (SLit 2147450879) (RG w2L_e1 18)).
Definition w2L_e2 : sstate := Eval vm_compute in fst (RUN (AC w2L_e1 BC_GEU (SLit 2147450879) (RG w2L_e1 18))).
Lemma r_w2L_2 : RUN (AC w2L_e1 BC_GEU (SLit 2147450879) (RG w2L_e1 18)) = (w2L_e2, RS_stopped (SR_branch BC_GEU (SOff 10 0) (SAlu ALU_ADD (SOff 10 0) (SOff 12 0)))). Proof. vm_compute. reflexivity. Qed.
Definition w2L_s3 : sstate := Eval vm_compute in (AC w2L_e2 BC_LTU (RG w2L_e2 8) (RG w2L_e2 18)).
Definition w2L_e3 : sstate := Eval vm_compute in fst (RUN (AC w2L_e2 BC_LTU (RG w2L_e2 8) (RG w2L_e2 18))).
Lemma r_w2L_3 : RUN (AC w2L_e2 BC_LTU (RG w2L_e2 8) (RG w2L_e2 18)) = (w2L_e3, RS_stopped (SR_branch BC_EQ (SOff 44 0) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition w2Lz_s0 : sstate := Eval vm_compute in (AC w2L_e3 BC_EQ (RG w2L_e3 11) (SLit 0)).
Definition w2Lz_e0 : sstate := Eval vm_compute in fst (RUN (AC w2L_e3 BC_EQ (RG w2L_e3 11) (SLit 0))).
Lemma r_w2Lz_0 : RUN (AC w2L_e3 BC_EQ (RG w2L_e3 11) (SLit 0)) = (w2Lz_e0, RS_stopped (SR_branch BC_GEU (SOff 49 2147450880) (SOff 50 2147450880))). Proof. vm_compute. reflexivity. Qed.
Definition w2Lz_s1 : sstate := Eval vm_compute in (AC w2Lz_e0 BC_LTU (RG w2Lz_e0 19) (RG w2Lz_e0 10)).
Definition w2Lz_e1 : sstate := Eval vm_compute in fst (RUN (AC w2Lz_e0 BC_LTU (RG w2Lz_e0 19) (RG w2Lz_e0 10))).
Lemma r_w2Lz_1 : RUN (AC w2Lz_e0 BC_LTU (RG w2Lz_e0 19) (RG w2Lz_e0 10)) = (w2Lz_e1, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition w2Lz_s2 : sstate := Eval vm_compute in (ss_after_mz w2Lz_e1 (ss_mem w2Lz_e1) 56 0x542cc).
Definition w2Lz_e2 : sstate := Eval vm_compute in fst (RUN (ss_after_mz w2Lz_e1 (ss_mem w2Lz_e1) 56 0x542cc)).
Lemma r_w2Lz_2 : RUN (ss_after_mz w2Lz_e1 (ss_mem w2Lz_e1) 56 0x542cc) = (w2Lz_e2, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition w2Ln_s0 : sstate := Eval vm_compute in (AC w2L_e3 BC_NE (RG w2L_e3 11) (SLit 0)).
Definition w2Ln_e0 : sstate := Eval vm_compute in fst (RUN (AC w2L_e3 BC_NE (RG w2L_e3 11) (SLit 0))).
Lemma r_w2Ln_0 : RUN (AC w2L_e3 BC_NE (RG w2L_e3 11) (SLit 0)) = (w2Ln_e0, RS_stopped (SR_branch BC_LT (SAlu ALU_AND (SAlu ALU_ADD (SOff 10 (-1)) (SOff 12 0)) (SLit 7)) (SOff 44 0))). Proof. vm_compute. reflexivity. Qed.
Definition w2Ln_s1 : sstate := Eval vm_compute in (AC w2Ln_e0 BC_LT (RG w2Ln_e0 12) (RG w2Ln_e0 11)).
Definition w2Ln_e1 : sstate := Eval vm_compute in fst (RUN (AC w2Ln_e0 BC_LT (RG w2Ln_e0 12) (RG w2Ln_e0 11))).
Lemma r_w2Ln_1 : RUN (AC w2Ln_e0 BC_LT (RG w2Ln_e0 12) (RG w2Ln_e0 11)) = (w2Ln_e1, RS_stopped (SR_branch BC_GEU (SOff 49 2147450880) (SOff 50 2147450880))). Proof. vm_compute. reflexivity. Qed.
Definition w2Ln_s2 : sstate := Eval vm_compute in (AC w2Ln_e1 BC_LTU (RG w2Ln_e1 19) (RG w2Ln_e1 10)).
Definition w2Ln_e2 : sstate := Eval vm_compute in fst (RUN (AC w2Ln_e1 BC_LTU (RG w2Ln_e1 19) (RG w2Ln_e1 10))).
Lemma r_w2Ln_2 : RUN (AC w2Ln_e1 BC_LTU (RG w2Ln_e1 19) (RG w2Ln_e1 10)) = (w2Ln_e2, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition w2Ln_s3 : sstate := Eval vm_compute in (ss_after_mz w2Ln_e2 (ss_mem w2Ln_e2) 56 0x542cc).
Definition w2Ln_e3 : sstate := Eval vm_compute in fst (RUN (ss_after_mz w2Ln_e2 (ss_mem w2Ln_e2) 56 0x542cc)).
Lemma r_w2Ln_3 : RUN (ss_after_mz w2Ln_e2 (ss_mem w2Ln_e2) 56 0x542cc) = (w2Ln_e3, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition w2H_s0 : sstate := Eval vm_compute in (ssD2H).
Definition w2H_e0 : sstate := Eval vm_compute in fst (RUN (ssD2H)).
Lemma r_w2H_0 : RUN (ssD2H) = (w2H_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 10 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Definition w2H_s1 : sstate := Eval vm_compute in (AC w2H_e0 BC_GEU (RG w2H_e0 13) (RG w2H_e0 12)).
Definition w2H_e1 : sstate := Eval vm_compute in fst (RUN (AC w2H_e0 BC_GEU (RG w2H_e0 13) (RG w2H_e0 12))).
Lemma r_w2H_1 : RUN (AC w2H_e0 BC_GEU (RG w2H_e0 13) (RG w2H_e0 12)) = (w2H_e1, RS_stopped (SR_branch BC_LTU (SLit 140737488355327) (SAlu ALU_ADD (SOff 10 0) (SOff 12 0)))). Proof. vm_compute. reflexivity. Qed.
Definition w2H_s2 : sstate := Eval vm_compute in (AC w2H_e1 BC_GEU (SLit 140737488355327) (RG w2H_e1 18)).
Definition w2H_e2 : sstate := Eval vm_compute in fst (RUN (AC w2H_e1 BC_GEU (SLit 140737488355327) (RG w2H_e1 18))).
Lemma r_w2H_2 : RUN (AC w2H_e1 BC_GEU (SLit 140737488355327) (RG w2H_e1 18)) = (w2H_e2, RS_stopped (SR_branch BC_GEU (SOff 10 0) (SAlu ALU_ADD (SOff 10 0) (SOff 12 0)))). Proof. vm_compute. reflexivity. Qed.
Definition w2H_s3 : sstate := Eval vm_compute in (AC w2H_e2 BC_LTU (RG w2H_e2 8) (RG w2H_e2 18)).
Definition w2H_e3 : sstate := Eval vm_compute in fst (RUN (AC w2H_e2 BC_LTU (RG w2H_e2 8) (RG w2H_e2 18))).
Lemma r_w2H_3 : RUN (AC w2H_e2 BC_LTU (RG w2H_e2 8) (RG w2H_e2 18)) = (w2H_e3, RS_stopped (SR_branch BC_EQ (SOff 44 0) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition w2Hz_s0 : sstate := Eval vm_compute in (AC w2H_e3 BC_EQ (RG w2H_e3 11) (SLit 0)).
Definition w2Hz_e0 : sstate := Eval vm_compute in fst (RUN (AC w2H_e3 BC_EQ (RG w2H_e3 11) (SLit 0))).
Lemma r_w2Hz_0 : RUN (AC w2H_e3 BC_EQ (RG w2H_e3 11) (SLit 0)) = (w2Hz_e0, RS_stopped (SR_branch BC_GEU (SOff 49 2147450880) (SOff 50 2147450880))). Proof. vm_compute. reflexivity. Qed.
Definition w2Hz_s1 : sstate := Eval vm_compute in (AC w2Hz_e0 BC_LTU (RG w2Hz_e0 19) (RG w2Hz_e0 10)).
Definition w2Hz_e1 : sstate := Eval vm_compute in fst (RUN (AC w2Hz_e0 BC_LTU (RG w2Hz_e0 19) (RG w2Hz_e0 10))).
Lemma r_w2Hz_1 : RUN (AC w2Hz_e0 BC_LTU (RG w2Hz_e0 19) (RG w2Hz_e0 10)) = (w2Hz_e1, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition w2Hz_s2 : sstate := Eval vm_compute in (ss_after_mz w2Hz_e1 (ss_mem w2Hz_e1) 56 0x542cc).
Definition w2Hz_e2 : sstate := Eval vm_compute in fst (RUN (ss_after_mz w2Hz_e1 (ss_mem w2Hz_e1) 56 0x542cc)).
Lemma r_w2Hz_2 : RUN (ss_after_mz w2Hz_e1 (ss_mem w2Hz_e1) 56 0x542cc) = (w2Hz_e2, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition w2Hn_s0 : sstate := Eval vm_compute in (AC w2H_e3 BC_NE (RG w2H_e3 11) (SLit 0)).
Definition w2Hn_e0 : sstate := Eval vm_compute in fst (RUN (AC w2H_e3 BC_NE (RG w2H_e3 11) (SLit 0))).
Lemma r_w2Hn_0 : RUN (AC w2H_e3 BC_NE (RG w2H_e3 11) (SLit 0)) = (w2Hn_e0, RS_stopped (SR_branch BC_LT (SAlu ALU_AND (SAlu ALU_ADD (SOff 10 (-1)) (SOff 12 0)) (SLit 7)) (SOff 44 0))). Proof. vm_compute. reflexivity. Qed.
Definition w2Hn_s1 : sstate := Eval vm_compute in (AC w2Hn_e0 BC_LT (RG w2Hn_e0 12) (RG w2Hn_e0 11)).
Definition w2Hn_e1 : sstate := Eval vm_compute in fst (RUN (AC w2Hn_e0 BC_LT (RG w2Hn_e0 12) (RG w2Hn_e0 11))).
Lemma r_w2Hn_1 : RUN (AC w2Hn_e0 BC_LT (RG w2Hn_e0 12) (RG w2Hn_e0 11)) = (w2Hn_e1, RS_stopped (SR_branch BC_GEU (SOff 49 2147450880) (SOff 50 2147450880))). Proof. vm_compute. reflexivity. Qed.
Definition w2Hn_s2 : sstate := Eval vm_compute in (AC w2Hn_e1 BC_LTU (RG w2Hn_e1 19) (RG w2Hn_e1 10)).
Definition w2Hn_e2 : sstate := Eval vm_compute in fst (RUN (AC w2Hn_e1 BC_LTU (RG w2Hn_e1 19) (RG w2Hn_e1 10))).
Lemma r_w2Hn_2 : RUN (AC w2Hn_e1 BC_LTU (RG w2Hn_e1 19) (RG w2Hn_e1 10)) = (w2Hn_e2, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition w2Hn_s3 : sstate := Eval vm_compute in (ss_after_mz w2Hn_e2 (ss_mem w2Hn_e2) 56 0x542cc).
Definition w2Hn_e3 : sstate := Eval vm_compute in fst (RUN (ss_after_mz w2Hn_e2 (ss_mem w2Hn_e2) 56 0x542cc)).
Lemma r_w2Hn_3 : RUN (ss_after_mz w2Hn_e2 (ss_mem w2Hn_e2) 56 0x542cc) = (w2Hn_e3, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition ss_epi : sstate := mkSS MC_RA sr_atoms [YP09.mkRegion (Some 2%nat) 0 2144 0 0 stkD_chunks] None (mkFacts [(2%nat, mkAF (2^43) (2^47) 4)] [] []).
Definition epi_e : sstate := Eval vm_compute in fst (RUN ss_epi).
Lemma r_epi : RUN ss_epi = (epi_e, RS_stopped (SR_jalr (SOff 32 0))). Proof. vm_compute. reflexivity. Qed.
Definition MC_SCR : Z := 2216.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Lemma mc_tail : forall ly S (W : world tfibsegs) regs mem md (regs1 : bvmap 5 word) (mem1 : word -> option byte) mat1 d x n,
ecall_pre tfibsegs B ly S W regs mem md ->
0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 -> 0 <= x -> x + n <= 2 ^ 63 ->
dest_ok tfibsegs B ly S W regs mem d n -> src_ok tfibsegs W regs mem x n -> (d + n <= x \/ x + n <= d) ->
getr regs1 10 = w64 d -> getr regs1 11 = w64 x -> getr regs1 12 = w64 n ->
getr regs1 1 = w64 MC_RA -> getr regs1 2 = w64 (spZ regs - 2144) ->
getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
getr regs1 24 = getr regs 24 -> getr regs1 25 = getr regs 25 -> getr regs1 26 = getr regs 26 -> getr regs1 27 = getr regs 27 ->
(forall z : word, ~ (spZ regs - MC_SCR <= bv_unsigned z < spZ regs) -> mem1 z = mem z) ->
(forall a, spZ regs - MC_SCR <= a < spZ regs -> apresent (w_H W) mem1 a) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 48) 8 (bv_unsigned (getr regs 20)) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 56) 8 (bv_unsigned (getr regs 21)) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 64) 8 (bv_unsigned (getr regs 22)) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 72) 8 (bv_unsigned (getr regs 23)) ->
SRr tfibsegs W (mkCfg (mkst regs1 (Z_to_bv 64 MC_REAL) mem1 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat1 md))
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
AR tfibsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 d /\
(forall i, 0 <= i < n -> aview tfibsegs (w_H W) mem' (d + i) = aview tfibsegs (w_H W) mem (x + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros ly S W regs mem md regs1 mem1 mat1 d x n HPRE Hn Hd Hdn Hx0 Hxn HDST HSRC HDISJ G10 G11 G12 G1 G2 G3 G4 G24 G25 G26 G27
MEQ1 PRS1 V0 V1 V2 V3 V4 V5 V6 V7 V8.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof AF0x.Hwx_tfa as Hwx. unfold ESTACK, MC_SCR in *.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
set (sp0 := spZ regs) in *. assert (Hsp44 : 2 ^ 44 <= sp0 <= 2 ^ 47) by lia.
set (H := w_H W) in *.
assert (DW : forall a, d <= a < d + n -> writable_at tfibsegs (mrestrict H mem1) a /\ H (Z_to_bv 64 a) = false).
{ intros a Ha. destruct (HDST a Ha) as (Hw & _ & Hns). unfold ESTACK in Hns.
assert (Hw1 : writable_at tfibsegs (mrestrict H mem1) a).
{ apply (writable_at_same (mrestrict H mem) (mrestrict H mem1) a); [|exact Hw].
unfold mrestrict. rewrite (MEQ1 (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by lia. unfold sp0 in *. lia. }
split; [exact Hw1|]. destruct (H (Z_to_bv 64 a)) eqn:Hh; [|reflexivity].
exfalso. exact (hidden_not_writable W mem1 a ltac:(lia) Hh Hw1). }
assert (SRCM : forall a, x <= a < x + n -> mem1 (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
{ intros a Ha. destruct (HSRC a Ha) as [_ Hns]. unfold ESTACK in Hns. apply MEQ1. rewrite unsigned_lit_small by lia. unfold sp0 in *. lia. }
destruct (rdn_of_vis (mrestrict H mem1) x (Z.to_nat n) ltac:(lia) ltac:(lia)) as (bs & RDN & LEN & BS).
{ intros i Hi. rewrite (AF0x.mbyte_mrestrict_same H mem mem1 (x + i) (SRCM (x + i) ltac:(lia))).
exact (proj1 (aview_vis H mem (x + i)) (proj1 (HSRC (x + i) ltac:(lia)))). }
assert (SOK : store_ok tfibsegs (mrestrict H mem1) (w64 d) (length bs) = true).
{ rewrite LEN. apply store_ok_of_all; unfold w64; rewrite unsigned_lit_small by lia; [lia|].
intros z Hz. pose proof (proj1 (DW (bv_unsigned z) ltac:(lia))) as Wz. unfold writable_at in Wz. rewrite Z_to_bv_bv_unsigned in Wz. exact Wz. }
destruct (tfib_memcpy bs (w64 d) (w64 x) (w64 n) (mrestrict H mem1) (seg_rom tfibsegs) regs1 G10 G11 G12
ltac:(unfold w64; rewrite unsigned_lit_small by lia; lia) ltac:(rewrite LEN; exact RDN) SOK
ltac:(unfold w64; rewrite unsigned_lit_small by lia; lia) ltac:(unfold w64; rewrite unsigned_lit_small by lia; lia)
ltac:(unfold w64; rewrite !unsigned_lit_small by lia; lia))
as (regs2 & Hms & A10 & Hkeep).
rewrite G1 in Hms. replace (v_jalr (w64 MC_RA) 0) with (Z_to_bv 64 MC_RA : word) in Hms by (apply bv_eq; vm_compute; reflexivity).
change (Z_to_bv 64 tfib_A_musl_memcpy) with (Z_to_bv 64 MC_REAL) in Hms.
set (m1r := mrestrict H mem1) in *. set (m2r := wbytes m1r (w64 d) bs) in Hms.
assert (KEEP : forall r : bv 5, r <> 5%bv -> r <> 6%bv -> r <> 7%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> r <> 28%bv ->
getr regs2 r = getr regs1 r) by (intros r; apply Hkeep).
set (mem2 := munrestrict H mem1 m2r).
assert (LENZ : Z.of_nat (length bs) = n) by lia.
assert (M2out : forall z : word, ~ (d <= bv_unsigned z < d + n) -> mem2 z = mem1 z).
{ intros z Hz. subst mem2 m2r. unfold munrestrict. destruct (H z) eqn:Hh; [reflexivity|].
assert (Ew : wbytes m1r (w64 d) bs z = m1r z).
{ destruct (Z_lt_le_dec (bv_unsigned z) d) as [L|L].
- apply wbytes_below; unfold w64; rewrite ?LENZ, unsigned_lit_small by lia; lia.
- apply wbytes_above. unfold w64. rewrite LENZ, unsigned_lit_small by lia. lia. }
rewrite Ew. subst m1r. unfold mrestrict. rewrite Hh. reflexivity. }
assert (M2in : forall i, 0 <= i < n -> mem2 (Z_to_bv 64 (d + i)) = Some (nth (Z.to_nat i) bs 0%bv)).
{ intros i Hi. subst mem2. unfold munrestrict. rewrite (proj2 (DW (d + i) ltac:(lia))).
subst m2r. rewrite (wbytes_inside bs m1r (w64 d) (Z_to_bv 64 (d + i)));
unfold w64; rewrite ?LENZ, ?unsigned_lit_small by lia; [|lia|lia].
replace (Z.to_nat (d + i - d)) with (Z.to_nat i) by lia. apply nth_error_nth'. lia. }
assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 - 2216 <= a < sp0) -> aview tfibsegs H mem2 a = aview tfibsegs H mem a).
{ intros a Hr Ha Hs. apply aview_same. rewrite (M2out (Z_to_bv 64 a)), (MEQ1 (Z_to_bv 64 a)); [reflexivity| |];
rewrite unsigned_lit_small by lia; [exact Hs | exact Ha]. }
assert (MS2 : forall z : word, sp0 - 2216 <= bv_unsigned z < sp0 -> mem2 z = mem1 z).
{ intros z Hz. apply M2out. intros Hd'. destruct (HDST (bv_unsigned z) Hd') as (_ & _ & Hns). unfold ESTACK in Hns. apply Hns. unfold sp0 in *. lia. }
assert (A2 : getr regs2 2 = w64 (sp0 - 2144)) by (rewrite KEEP by (intros H'; discriminate H'); exact G2).
set (E2 := Ereg regs2 [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21; getr regs 22; getr regs 23]).
assert (E2_2 : bv_unsigned (ew E2 2) = sp0 - 2144).
{ subst E2. rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl), A2. unfold w64. apply unsigned_lit_small. lia. }
assert (VM : forall a v, val_mem tfibsegs (mrestrict H mem1) a 8 v -> sp0 - 2216 <= a -> a + 8 <= sp0 -> val_mem tfibsegs (mrestrict H mem2) a 8 v).
{ intros a v Hv Hlo Hhi. apply (val_mem_frame H mem1 mem2 a 8 v); [|exact Hv]. intros k Hk. apply MS2. rewrite unsigned_lit_small by lia. lia. }
assert (HSe : st_ok tfibsegs E2 ss_epi (restrict H (mkst regs2 (Z_to_bv 64 MC_RA) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_epi. apply (entry_st_ok_full tfibsegs);
change (Ereg regs2 [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21; getr regs 22; getr regs 23]) with E2.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
replace (base_val E2 (Some 2%nat)) with (sp0 - 2144) by (symmetry; exact E2_2).
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
unfold stkD_chunks.
assert (CK : forall (j : nat) (r : bv 5) off, nth j [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21; getr regs 22; getr regs 23] (Z_to_bv 64 0) = getr regs r ->
off = 2136 - 8 * Z.of_nat j -> Z.of_nat j < 9 ->
val_mem tfibsegs (mrestrict H mem1) (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs r)) ->
YP09.chunk_ok tfibsegs E2 (mrestrict H mem2) (sp0 - 2144) (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros j r off Hnth Hoff Hj8 Hv. eapply (chunk_ok_val tfibsegs E2 _ (sp0 - 2144) off 8 _ (bv_unsigned (getr regs r))).
- cbn [sv_denot]. subst E2. rewrite (ew_Ereg_extra regs2 _ j), Hnth, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (u64_range (getr regs r)). zside.
- zside.
- subst off. replace (sp0 - 2144 + (2136 - 8 * Z.of_nat j)) with (sp0 - 8 - 8 * Z.of_nat j) by lia. apply VM; [exact Hv | lia | lia]. }
repeat apply Forall_cons; try apply Forall_nil.
+ apply (CK 0%nat 1%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 0) with (sp0 - 8) by lia; exact V0].
+ apply (CK 1%nat 8%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 1) with (sp0 - 16) by lia; exact V1].
+ apply (CK 2%nat 9%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 2) with (sp0 - 24) by lia; exact V2].
+ apply (CK 3%nat 18%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 3) with (sp0 - 32) by lia; exact V3].
+ apply (CK 4%nat 19%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 4) with (sp0 - 40) by lia; exact V4].
+ apply (CK 5%nat 20%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 5) with (sp0 - 48) by lia; exact V5].
+ apply (CK 6%nat 21%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 6) with (sp0 - 56) by lia; exact V6].
+ apply (CK 7%nat 22%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 7) with (sp0 - 64) by lia; exact V7].
+ apply (CK 8%nat 23%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 8) with (sp0 - 72) by lia; exact V8].
- apply pairwise_disjoint_of_extents. cbn. repeat split.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2_2.
change (2 ^ 4) with 16. unfold sp0 in *. repeat split; try lia.
all: replace (spZ regs - 2144) with (spZ regs + (-134) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16. }
eapply (SRr_msteps tfibsegs Hwx W); [rewrite restrict_mkst_fx; exact Hms|].
intros model' Hsbm _. rewrite (same_but_materialized_wvb md model' Hsbm). cbn [ms_mem mkst].
change (unrestrict H mem1 (mkst regs2 (Z_to_bv 64 MC_RA) m2r (seg_rom tfibsegs))) with (mkst regs2 (Z_to_bv 64 MC_RA) mem2 (seg_rom tfibsegs)).
eapply SRr_bind; [apply (icpt_phase W E2 ss_epi epi_e _ _ _ HSe r_epi)|].
cbv beta. intros W1 c1 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
eapply (SRr_ret_at tfibsegs tbl_icpt tbl_icpt_ok Hwx W E2); [exact HS3 | reflexivity | vm_compute; reflexivity |].
intros mat'. rewrite wvb_wvb.
assert (MEQ3 : forall z, ms_mem ms3 z = mem2 z) by (intros z; apply HF3; intros Hin; destruct (in_wrange_windows E2 _ _ Hin) as (b & lo & hi & Ht & Hw); cbn in Ht; destruct Ht as [Hq|[]]; injection Hq as <- <- <-; cbn [base_val] in Hw; lia).
rreg HS3 (1%bv : bv 5) Q1. rreg HS3 (2%bv : bv 5) Q2. rreg HS3 (10%bv : bv 5) Q10.
rreg HS3 (8%bv : bv 5) Q8. rreg HS3 (9%bv : bv 5) Q9. rreg HS3 (18%bv : bv 5) Q18. rreg HS3 (19%bv : bv 5) Q19.
rreg HS3 (20%bv : bv 5) Q20. rreg HS3 (21%bv : bv 5) Q21. rreg HS3 (22%bv : bv 5) Q22. rreg HS3 (23%bv : bv 5) Q23. rreg HS3 (24%bv : bv 5) Q24.
rreg HS3 (3%bv : bv 5) Q3. rreg HS3 (4%bv : bv 5) Q4.
rreg HS3 (25%bv : bv 5) Q25. rreg HS3 (26%bv : bv 5) Q26. rreg HS3 (27%bv : bv 5) Q27.
assert (X32 : ew E2 32 = getr regs 1) by (subst E2; exact (ew_Ereg_extra regs2 _ 0)).
rewrite X32 in Q1.
replace (v_jalr (getr (ms_regs ms3) 1) 0) with (w64 (raZ regs)) by (rewrite Q1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra).
split; [reflexivity|]. exists (ms_regs ms3), (ms_mem ms3), (with_vm_backing (m_vm_lazy md) mat' md).
pose proof (same_but_materialized_frame md _ (with_vm_backing_same md mat')) as MF.
assert (AV3 : forall a, aview tfibsegs H (ms_mem ms3) a = aview tfibsegs H mem2 a) by (intros a; apply aview_same; apply MEQ3).
split; [reflexivity|].
split; [|split; [|split; [|split; [|split; [|split]]]]].
-   apply (al_frame _ _ LAWS ly S W mem md (ms_mem ms3) _ HAR).
+ intros a Hr Hown. rewrite AV3. apply AV2; [exact Hr | intros Hd'; exact (proj1 (proj2 (HDST a Hd')) Hown) |].
intros Hs. exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(unfold sp0 in *; lia) Hown).
+ intros a Hv. rewrite AV3. rewrite (AE2y.aview_mod _ mem2 a). rewrite (AE2y.aview_mod _ mem a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' d) as [L1|L1]; [| destruct (Z_lt_le_dec a' (d + n)) as [L2|L2]].
2:{ unfold aview, mbyte, mrestrict. rewrite (proj2 (DW a' ltac:(lia))). replace a' with (d + (a' - d)) by lia. rewrite (M2in (a' - d)) by lia. discriminate. }
all: destruct (Z_lt_le_dec a' (sp0 - 2216)) as [L3|L3]; [rewrite AV2 by lia; exact Hv|].
all: destruct (Z_lt_le_dec a' sp0) as [L4|L4]; [| rewrite AV2 by lia; exact Hv].
all: apply aview_some_of_apresent; apply (apresent_same H mem1 mem2 a' (MS2 (Z_to_bv 64 a') ltac:(rewrite unsigned_lit_small by lia; lia))); apply PRS1; lia.
+ apply MF. + apply MF. + apply MF.
+ exact (AE2y.hs_kept_trans _ _ _ _ (AE2y.hs_kept_trans _ _ _ _ (AE2y.hs_kept_win _ _ _ _ _ _ _ _ MEQ1 HpresE ltac:(unfold ESTACK, MC_SCR; lia) ltac:(lia)) (AE2y.hs_kept_unrestrict _ _ _)) (AE2y.hs_kept_eq _ _ _ MEQ3)).
-
intros r Hr. unfold acallee_saved in Hr.
assert (X : forall j rr, nth j [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21; getr regs 22; getr regs 23] (Z_to_bv 64 0) = getr regs rr -> ew E2 (32 + j) = getr regs rr)
by (intros jj rr Hnth; subst E2; rewrite (ew_Ereg_extra regs2 _ jj); exact Hnth).
assert (Y : forall i (rr : bv 5), Z.of_nat i = bv_unsigned rr -> ew E2 i = getr regs2 rr) by (intros ii rr Hnth; subst E2; exact (ew_Ereg_nat regs2 _ ii rr Hnth)).
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
+ replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q2. apply bv_eq. rewrite Z_to_bv_unsigned, E2_2. unfold sp0, spZ, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
pose proof (u64_range (getr regs 2)). rewrite Z.mod_small by lia. lia.
+ replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q3, (Y 3%nat 3%bv eq_refl), KEEP by (intros H'; discriminate H'). exact G3.
+ replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q4, (Y 4%nat 4%bv eq_refl), KEEP by (intros H'; discriminate H'). exact G4.
+ replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q8. exact (X 1%nat 8%bv eq_refl).
+ replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q9. exact (X 2%nat 9%bv eq_refl).
+ assert (Hc : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
* replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q18. exact (X 3%nat 18%bv eq_refl).
* replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q19. exact (X 4%nat 19%bv eq_refl).
* replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q20. exact (X 5%nat 20%bv eq_refl).
* replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q21. exact (X 6%nat 21%bv eq_refl).
* replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q22. exact (X 7%nat 22%bv eq_refl).
* replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q23. exact (X 8%nat 23%bv eq_refl).
* replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q24, (Y 24%nat 24%bv eq_refl), KEEP by (intros H'; discriminate H'). exact G24.
* replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q25, (Y 25%nat 25%bv eq_refl), KEEP by (intros H'; discriminate H'). exact G25.
* replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q26, (Y 26%nat 26%bv eq_refl), KEEP by (intros H'; discriminate H'). exact G26.
* replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q27, (Y 27%nat 27%bv eq_refl), KEEP by (intros H'; discriminate H'). exact G27.
- apply with_vm_backing_same.
- rewrite Q10. subst E2. rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl). exact A10.
- intros i Hi. rewrite AV3. rewrite <- (aview_same H mem mem1 (x + i) (SRCM (x + i) ltac:(lia))).
unfold aview. replace (mbyte tfibsegs (mrestrict H mem2) (d + i)) with (Some (nth (Z.to_nat i) bs 0%bv)).
2:{ unfold mbyte, mrestrict. rewrite (proj2 (DW (d + i) ltac:(lia))), (M2in i Hi). reflexivity. }
subst m1r. replace (x + i) with (x + Z.of_nat (Z.to_nat i)) by lia. rewrite (BS (Z.to_nat i) ltac:(lia)). reflexivity.
- intros a Hr Hd' Hs. rewrite AV3. apply AV2; [exact Hr | exact Hd' | unfold sp0 in *; lia].
- intros a Hp. pose proof Hp as [Hh [b Hb]].
assert (Hr : apresent H (ms_mem ms3) a <-> apresent H (ms_mem ms3) (a mod 2 ^ 64)).
{ unfold apresent. rewrite <- (AE2y.Z_to_bv64_of_mod a). tauto. }
apply (proj2 Hr). clear Hr.
assert (Hp' : apresent H mem (a mod 2 ^ 64)) by (unfold apresent; rewrite (AE2y.Z_to_bv64_of_mod a); exact Hp).
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
apply (apresent_same H mem2 (ms_mem ms3) a' (MEQ3 _)).
destruct (Z_lt_le_dec a' d) as [L1|L1]; [| destruct (Z_lt_le_dec a' (d + n)) as [L2|L2]].
2:{ split; [exact (proj2 (DW a' ltac:(lia)))|]. eexists. replace a' with (d + (a' - d)) by lia. apply M2in. lia. }
all: destruct (Z_lt_le_dec a' (sp0 - 2216)) as [L3|L3];
[apply (apresent_same H mem mem2 a'); [rewrite (M2out (Z_to_bv 64 a')), (MEQ1 (Z_to_bv 64 a')) by (rewrite unsigned_lit_small by lia; lia); reflexivity | exact Hp']|].
all: destruct (Z_lt_le_dec a' sp0) as [L4|L4];
[| apply (apresent_same H mem mem2 a'); [rewrite (M2out (Z_to_bv 64 a')), (MEQ1 (Z_to_bv 64 a')) by (rewrite unsigned_lit_small by lia; lia); reflexivity | exact Hp']].
all: apply (apresent_same H mem1 mem2 a' (MS2 (Z_to_bv 64 a') ltac:(rewrite unsigned_lit_small by lia; lia))); apply PRS1; lia.
Qed.
End h.
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (RG ss r) v.
Definition chunk_is (off : Z) (v : sv) (c : YP09.chunk) : bool :=
(YP09.c_off c =? off) && match YP09.c_val c with CVal n e => N.eqb n 8 && sv_eqb e v | _ => false end.
Definition has_chunk (ss : sstate) (off : Z) (v : sv) : bool :=
match ss_mem ss with r :: _ => existsb (chunk_is off v) (YP09.r_chunks r) | [] => false end.
Lemma chunk_is_sound : forall off v c, chunk_is off v c = true -> c = YP09.mkChunk off (CVal 8 v).
Proof.
intros off v [o cv] Hc. unfold chunk_is in Hc. cbn [YP09.c_off YP09.c_val] in Hc. apply andb_prop in Hc as [Ho Hv].
apply Z.eqb_eq in Ho. destruct cv as [nn e| | |]; try discriminate. apply andb_prop in Hv as [Hn He].
apply N.eqb_eq in Hn. apply sv_eqb_eq in He. subst. reflexivity.
Qed.
Definition SAVED : list (Z * Z) := [(1, -8); (8, -16); (9, -24); (18, -32); (19, -40); (20, -48); (21, -56); (22, -64); (23, -72)].
Definition shapeS (ss : sstate) : bool :=
(ss_pc ss =? MC_MID) &&
match ss_mem ss with r :: _ => obase_eqb (YP09.r_base r) (Some 2%nat) && (YP09.r_wlo r =? - MC_STK) && (YP09.r_whi r =? 0) | [] => false end &&
reg_is ss 10 (SOff 10 0) && reg_is ss 11 (SOff 11 0) && reg_is ss 12 (SOff 12 0) && reg_is ss 2 (SOff 2 (-2144)) &&
reg_is ss 19 (SAlu ALU_ADD (SOff 10 0) (SOff 12 0)) && reg_is ss 22 (SOff 12 (-65)) &&
reg_is ss 3 (SOff 3 0) && reg_is ss 4 (SOff 4 0) && reg_is ss 24 (SOff 24 0) && reg_is ss 25 (SOff 25 0) && reg_is ss 26 (SOff 26 0) && reg_is ss 27 (SOff 27 0) &&
forallb (fun p => has_chunk ss (snd p) (SOff (Z.to_nat (fst p)) 0)) SAVED.
Definition shape0 (ss : sstate) : bool :=
(ss_pc ss =? MC_REAL) &&
match ss_mem ss with r :: _ => obase_eqb (YP09.r_base r) (Some 2%nat) && (YP09.r_wlo r =? - MC_STK) && (YP09.r_whi r =? 0) | [] => false end &&
reg_is ss 10 (SOff 10 0) && reg_is ss 11 (SOff 11 0) && reg_is ss 12 (SOff 12 0) && reg_is ss 1 (SLit MC_RA) && reg_is ss 2 (SOff 2 (-2144)) &&
reg_is ss 3 (SOff 3 0) && reg_is ss 4 (SOff 4 0) && reg_is ss 24 (SOff 24 0) && reg_is ss 25 (SOff 25 0) && reg_is ss 26 (SOff 26 0) && reg_is ss 27 (SOff 27 0) &&
forallb (fun p => has_chunk ss (snd p) (SOff (Z.to_nat (fst p)) 0)) SAVED.
Definition SAVEDD : list (Z * Z) := [(32, 2136); (33, 2128); (34, 2120); (35, 2112); (36, 2104); (37, 2096); (38, 2088); (39, 2080); (40, 2072)].
Definition shapeD (ss : sstate) : bool :=
(ss_pc ss =? MC_REAL) &&
match ss_mem ss with r :: _ => obase_eqb (YP09.r_base r) (Some 2%nat) && (YP09.r_wlo r =? -64) && (YP09.r_whi r =? 2144) | [] => false end &&
reg_is ss 10 (SOff 10 0) && reg_is ss 11 (SOff 11 0) && reg_is ss 12 (SOff 12 0) && reg_is ss 1 (SLit MC_RA) && reg_is ss 2 (SOff 2 0) &&
reg_is ss 3 (SOff 3 0) && reg_is ss 4 (SOff 4 0) && reg_is ss 24 (SOff 24 0) && reg_is ss 25 (SOff 25 0) && reg_is ss 26 (SOff 26 0) && reg_is ss 27 (SOff 27 0) &&
forallb (fun p => has_chunk ss (snd p) (SOff (Z.to_nat (fst p)) 0)) SAVEDD.
Section l.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (d x n : Z).
Hypothesis HPRE : ecall_pre tfibsegs B ly S W regs mem md.
Hypothesis G10 : getr regs 10 = w64 d.
Hypothesis G11 : getr regs 11 = w64 x.
Hypothesis G12 : getr regs 12 = w64 n.
Hypothesis Hn : 0 <= n < 2 ^ 32.
Hypothesis Hd : 0 <= d.
Hypothesis Hdn : d + n <= 2 ^ 63.
Hypothesis HDST : dest_ok tfibsegs B ly S W regs mem d n.
Hypothesis HAM : amem_range d n.
Hypothesis HRA : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF d n.
Hypothesis HHULL : 0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) d n.
Hypothesis Hx0 : 0 <= x.
Hypothesis Hxn : x + n <= 2 ^ 63.
Hypothesis HSRC : src_ok tfibsegs W regs mem x n.
Hypothesis HDISJ : d + n <= x \/ x + n <= d.
Hypothesis HAMX : amem_range x n.
Hypothesis HRAX : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n.
Hypothesis HHULLX : 0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x n.
Definition POSTc : world tfibsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
AR tfibsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 d /\
(forall i, 0 <= i < n -> aview tfibsegs (w_H W) mem' (d + i) = aview tfibsegs (w_H W) mem (x + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Let sp0 : Z := spZ regs.
Let H := w_H W.
Let g0s : Z := x / 8.
Let g1s : Z := (x + n - 1) / 8.
Let dus : Z := (x + 7) / 8 * 8.
Let des : Z := (x + n) / 8 * 8.
Let gus : Z := (x + 7) / 8.
Let ges : Z := (x + n) / 8.
Let g0d : Z := d / 8.
Let g1d : Z := (d + n - 1) / 8.
Let dud : Z := (d + 7) / 8 * 8.
Let ded : Z := (d + n) / 8 * 8.
Let gud : Z := (d + 7) / 8.
Let ged : Z := (d + n) / 8.
Definition SV : list Z := [bv_unsigned (getr regs 1); bv_unsigned (getr regs 8); bv_unsigned (getr regs 9); bv_unsigned (getr regs 18); bv_unsigned (getr regs 19);
bv_unsigned (getr regs 20); bv_unsigned (getr regs 21); bv_unsigned (getr regs 22); bv_unsigned (getr regs 23); bv_unsigned (getr regs 24)].
Definition MIDP (ms : machine_state) : Prop :=
ms = mkst (ms_regs ms) (Z_to_bv 64 MC_MID) (ms_mem ms) (seg_rom tfibsegs) /\
getr (ms_regs ms) 10 = w64 d /\ getr (ms_regs ms) 11 = w64 x /\ getr (ms_regs ms) 12 = w64 n /\
getr (ms_regs ms) 2 = w64 (sp0 - 2144) /\ getr (ms_regs ms) 19 = Z_to_bv 64 (d + n) /\ getr (ms_regs ms) 22 = Z_to_bv 64 (n - 65) /\
getr (ms_regs ms) 3 = getr regs 3 /\ getr (ms_regs ms) 4 = getr regs 4 /\
getr (ms_regs ms) 24 = getr regs 24 /\ getr (ms_regs ms) 25 = getr regs 25 /\ getr (ms_regs ms) 26 = getr regs 26 /\ getr (ms_regs ms) 27 = getr regs 27 /\
(forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms z = mem z) /\
(forall a, sp0 - MC_SCR <= a < sp0 -> apresent H (ms_mem ms) a) /\
(forall j rz off, nth_error SAVED j = Some (rz, off) -> val_mem tfibsegs (mrestrict H (ms_mem ms)) (sp0 + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 rz)))).
Lemma basics : 2 ^ 44 <= sp0 <= 2 ^ 47 /\ kHighMemBeg + 4096 <= sp0 /\ sp0 mod 16 = 0 /\ d + n <= 2 ^ 47 - 1 /\ x + n <= 2 ^ 47 - 1 /\
(forall a, sp0 - 4096 <= a < sp0 -> apresent H mem a) /\ ARm B ly S (aview tfibsegs H mem).
Proof.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, ESTACK in *. subst sp0 H.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact HpresE | exact (proj1 HAR)].
Qed.
Lemma shape_regs : forall E ss ms (r : bv 5) v, st_ok tfibsegs E ss (restrict H ms) -> reg_is ss (bv_unsigned r) v = true ->
getr (ms_regs ms) r = sv_denot E v.
Proof.
intros E ss ms r v HS Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr.
apply (st_ok_reg_denot H E ss ms r HS).
Qed.
Lemma shape_chunk : forall E ss ms r0 rest off i spv, st_ok tfibsegs E ss (restrict H ms) -> ss_mem ss = r0 :: rest ->
YP09.r_base r0 = Some 2%nat -> bv_unsigned (ew E 2) = spv -> has_chunk ss off (SOff i 0) = true ->
val_mem tfibsegs (mrestrict H (ms_mem ms)) (spv + off) 8 (bv_unsigned (ew E i)).
Proof.
intros E ss ms r0 rest off i spv HS Hmem Hbase E2 Hc. unfold has_chunk in Hc. rewrite Hmem in Hc. apply existsb_exists in Hc as (c & Hin & Hc).
apply chunk_is_sound in Hc. subst c.
pose proof (st_ok_mem_ok tfibsegs E ss _ HS) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs. rewrite Hmem in Hrs.
pose proof (Forall_inv Hrs) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. rewrite Hbase in Hck. cbn [base_val] in Hck. rewrite E2 in Hck.
apply (val_of_chunk_ok tfibsegs E _ _ off 8 (SOff i 0) (bv_unsigned (ew E i)) Hck).
- cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (u64_range (ew E i)). zside.
- zside.
Qed.
Local Ltac peel H names :=
lazymatch names with
| ?n :: ?rest => let Hn := fresh n in apply andb_prop in H as [H Hn]; peel H rest
| _ => idtac
end.
Lemma finish0 : forall E ss ms mat,
st_ok tfibsegs E ss (restrict H ms) -> ss_resv ss = None -> shape0 ss = true ->
(forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r) ->
(forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms z = mem z) ->
(forall a, sp0 - MC_SCR <= a < sp0 - MC_STK -> apresent H (ms_mem ms) a) ->
SRr tfibsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) POSTc.
Proof.
intros E ss ms mat HS Hrv Hsh HE MEQ PRS.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM). unfold MC_SCR, MC_STK in *.
unfold shape0 in Hsh.
apply andb_prop in Hsh as [Hsh HSV]. apply andb_prop in Hsh as [Hsh R27]. apply andb_prop in Hsh as [Hsh R26]. apply andb_prop in Hsh as [Hsh R25]. apply andb_prop in Hsh as [Hsh R24].
apply andb_prop in Hsh as [Hsh R4]. apply andb_prop in Hsh as [Hsh R3]. apply andb_prop in Hsh as [Hsh R2]. apply andb_prop in Hsh as [Hsh R1].
apply andb_prop in Hsh as [Hsh R12]. apply andb_prop in Hsh as [Hsh R11]. apply andb_prop in Hsh as [Hsh R10]. apply andb_prop in Hsh as [Hpc Smem].
destruct (ss_mem ss) as [|r0 rest] eqn:Hmem; [discriminate|].
apply andb_prop in Smem as [Smem Hwhi]. apply andb_prop in Smem as [Hbase Hwlo].
apply obase_eqb_eq in Hbase. apply Z.eqb_eq in Hwlo. apply Z.eqb_eq in Hwhi. apply Z.eqb_eq in Hpc.
assert (E2 : bv_unsigned (ew E 2) = sp0) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (RA : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> reg_is ss (bv_unsigned r) (SOff i 0) = true -> getr (ms_regs ms) r = getr regs r).
{ intros r i Hi Hr. rewrite (shape_regs E ss ms r _ HS Hr). cbn [sv_denot]. rewrite (HE i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (CK : forall j rz off, nth_error SAVED j = Some (rz, off) -> val_mem tfibsegs (mrestrict H (ms_mem ms)) (sp0 + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 rz)))).
{ intros j rz off Hj. rewrite forallb_forall in HSV. specialize (HSV (rz, off) (nth_error_In _ _ Hj)). cbn [fst snd] in HSV.
assert (Hrz : 0 <= rz < 32) by (do 9 (destruct j as [|j]; [cbn in Hj; injection Hj as <- <-; lia|]); destruct j; discriminate).
rewrite <- (HE (Z.to_nat rz) (Z_to_bv 5 rz)).
2:{ rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia. }
exact (shape_chunk E ss ms r0 rest off (Z.to_nat rz) sp0 HS Hmem Hbase E2 HSV). }
pose proof (st_ok_restrict_mkst tfibsegs H E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape. rewrite Hshape.
apply (mc_tail B LAWS ly S W regs mem md (ms_regs ms) (ms_mem ms) mat d x n HPRE Hn Hd Hdn Hx0 Hxn HDST HSRC HDISJ).
- rewrite (shape_regs E ss ms 10%bv _ HS R10). cbn [sv_denot]. rewrite (HE 10%nat 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. exact G10.
- rewrite (shape_regs E ss ms 11%bv _ HS R11). cbn [sv_denot]. rewrite (HE 11%nat 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. exact G11.
- rewrite (shape_regs E ss ms 12%bv _ HS R12). cbn [sv_denot]. rewrite (HE 12%nat 12%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. exact G12.
- rewrite (shape_regs E ss ms 1%bv _ HS R1). reflexivity.
- rewrite (shape_regs E ss ms 2%bv _ HS R2). cbn [sv_denot]. rewrite (HE 2%nat 2%bv eq_refl). reflexivity.
- exact (RA 3%bv 3%nat eq_refl R3). - exact (RA 4%bv 4%nat eq_refl R4).
- exact (RA 24%bv 24%nat eq_refl R24). - exact (RA 25%bv 25%nat eq_refl R25). - exact (RA 26%bv 26%nat eq_refl R26). - exact (RA 27%bv 27%nat eq_refl R27).
- unfold MC_SCR. exact MEQ.
- intros a Ha. unfold MC_SCR in Ha. destruct (Z_lt_le_dec a (sp0 - 2208)) as [L|L]; [apply PRS; lia|].
apply (st_ok_window_apresent H E ss ms 0 r0 a HS ltac:(rewrite Hmem; reflexivity)); [| unfold TFIB_IMG_END, kHighMemBeg in *; lia].
rewrite Hbase, Hwlo, Hwhi. cbn [base_val]. rewrite E2. unfold MC_STK. lia.
- replace (sp0 - 8) with (sp0 + -8) by lia. exact (CK 0%nat 1 (-8) eq_refl).
- replace (sp0 - 16) with (sp0 + -16) by lia. exact (CK 1%nat 8 (-16) eq_refl).
- replace (sp0 - 24) with (sp0 + -24) by lia. exact (CK 2%nat 9 (-24) eq_refl).
- replace (sp0 - 32) with (sp0 + -32) by lia. exact (CK 3%nat 18 (-32) eq_refl).
- replace (sp0 - 40) with (sp0 + -40) by lia. exact (CK 4%nat 19 (-40) eq_refl).
- replace (sp0 - 48) with (sp0 + -48) by lia. exact (CK 5%nat 20 (-48) eq_refl).
- replace (sp0 - 56) with (sp0 + -56) by lia. exact (CK 6%nat 21 (-56) eq_refl).
- replace (sp0 - 64) with (sp0 + -64) by lia. exact (CK 7%nat 22 (-64) eq_refl).
- replace (sp0 - 72) with (sp0 + -72) by lia. exact (CK 8%nat 23 (-72) eq_refl).
Qed.
Local Ltac peel12 Hsh :=
apply andb_prop in Hsh as [Hsh HSV]; apply andb_prop in Hsh as [Hsh R27]; apply andb_prop in Hsh as [Hsh R26]; apply andb_prop in Hsh as [Hsh R25];
apply andb_prop in Hsh as [Hsh R4]; apply andb_prop in Hsh as [Hsh R3].
Lemma finishD : forall E (regsm : bvmap 5 word) ss ms mat,
st_ok tfibsegs E ss (restrict H ms) -> ss_resv ss = None -> shapeD ss = true ->
(forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regsm r) ->
(forall j, (j < 10)%nat -> ew E (32 + j) = Z_to_bv 64 (nth j SV 0)) ->
getr regsm 2 = w64 (sp0 - 2144) -> getr regsm 10 = w64 d -> getr regsm 11 = w64 x -> getr regsm 12 = w64 n ->
getr regsm 3 = getr regs 3 -> getr regsm 4 = getr regs 4 -> getr regsm 24 = getr regs 24 -> getr regsm 25 = getr regs 25 -> getr regsm 26 = getr regs 26 -> getr regsm 27 = getr regs 27 ->
(forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms z = mem z) ->
(forall a, sp0 - MC_SCR <= a < sp0 - MC_STK -> apresent H (ms_mem ms) a) ->
SRr tfibsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) POSTc.
Proof.
intros E regsm ss ms mat HS Hrv Hsh HE HSVv M2 M10 M11 M12 M3 M4 M24 M25 M26 M27 MEQ PRS.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM). unfold MC_SCR, MC_STK in *.
unfold shapeD in Hsh.
apply andb_prop in Hsh as [Hsh HSV]. apply andb_prop in Hsh as [Hsh R27]. apply andb_prop in Hsh as [Hsh R26]. apply andb_prop in Hsh as [Hsh R25]. apply andb_prop in Hsh as [Hsh R24].
apply andb_prop in Hsh as [Hsh R4]. apply andb_prop in Hsh as [Hsh R3]. apply andb_prop in Hsh as [Hsh R2]. apply andb_prop in Hsh as [Hsh R1].
apply andb_prop in Hsh as [Hsh R12]. apply andb_prop in Hsh as [Hsh R11]. apply andb_prop in Hsh as [Hsh R10]. apply andb_prop in Hsh as [Hpc Smem].
destruct (ss_mem ss) as [|r0 rest] eqn:Hmem; [discriminate|].
apply andb_prop in Smem as [Smem Hwhi]. apply andb_prop in Smem as [Hbase Hwlo].
apply obase_eqb_eq in Hbase. apply Z.eqb_eq in Hwlo. apply Z.eqb_eq in Hwhi. apply Z.eqb_eq in Hpc.
assert (E2 : bv_unsigned (ew E 2) = sp0 - 2144) by (rewrite (HE 2%nat 2%bv eq_refl), M2; unfold w64; apply unsigned_lit_small; lia).
assert (RA : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> reg_is ss (bv_unsigned r) (SOff i 0) = true -> getr (ms_regs ms) r = getr regsm r).
{ intros r i Hi Hr. rewrite (shape_regs E ss ms r _ HS Hr). cbn [sv_denot]. rewrite (HE i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (CK : forall j az off, nth_error SAVEDD j = Some (az, off) -> val_mem tfibsegs (mrestrict H (ms_mem ms)) (sp0 - 2144 + off) 8 (nth j SV 0)).
{ intros j az off Hj. rewrite forallb_forall in HSV. specialize (HSV (az, off) (nth_error_In _ _ Hj)). cbn [fst snd] in HSV.
assert (Hj10 : (j < 10)%nat /\ az = 32 + Z.of_nat j) by (do 9 (destruct j as [|j]; [cbn in Hj; injection Hj as <- <-; split; [lia|reflexivity] |]); destruct j; discriminate).
destruct Hj10 as [Hj10 ->]. replace (Z.to_nat (32 + Z.of_nat j)) with (32 + j)%nat in HSV by lia.
pose proof (shape_chunk E ss ms r0 rest off (32 + j) (sp0 - 2144) HS Hmem Hbase E2 HSV) as V.
rewrite (HSVv j Hj10) in V. rewrite unsigned_lit_small in V; [exact V|].
do 10 (destruct j as [|j]; [cbn; apply u64_range|]). lia. }
pose proof (st_ok_restrict_mkst tfibsegs H E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape. rewrite Hshape.
apply (mc_tail B LAWS ly S W regs mem md (ms_regs ms) (ms_mem ms) mat d x n HPRE Hn Hd Hdn Hx0 Hxn HDST HSRC HDISJ).
- rewrite (shape_regs E ss ms 10%bv _ HS R10). cbn [sv_denot]. rewrite (HE 10%nat 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. exact M10.
- rewrite (shape_regs E ss ms 11%bv _ HS R11). cbn [sv_denot]. rewrite (HE 11%nat 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. exact M11.
- rewrite (shape_regs E ss ms 12%bv _ HS R12). cbn [sv_denot]. rewrite (HE 12%nat 12%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. exact M12.
- rewrite (shape_regs E ss ms 1%bv _ HS R1). reflexivity.
- rewrite (shape_regs E ss ms 2%bv _ HS R2). cbn [sv_denot]. rewrite (HE 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. exact M2.
- rewrite (RA 3%bv 3%nat eq_refl R3). exact M3. - rewrite (RA 4%bv 4%nat eq_refl R4). exact M4.
- rewrite (RA 24%bv 24%nat eq_refl R24). exact M24. - rewrite (RA 25%bv 25%nat eq_refl R25). exact M25. - rewrite (RA 26%bv 26%nat eq_refl R26). exact M26. - rewrite (RA 27%bv 27%nat eq_refl R27). exact M27.
- unfold MC_SCR. exact MEQ.
- intros a Ha. unfold MC_SCR in Ha. destruct (Z_lt_le_dec a (sp0 - 2208)) as [L|L]; [apply PRS; lia|].
apply (st_ok_window_apresent H E ss ms 0 r0 a HS ltac:(rewrite Hmem; reflexivity)); [| unfold TFIB_IMG_END, kHighMemBeg in *; lia].
rewrite Hbase, Hwlo, Hwhi. cbn [base_val]. rewrite E2. lia.
- replace (spZ regs - 8) with (spZ regs - 2144 + 2136) by lia. exact (CK 0%nat 32 2136 eq_refl).
- replace (spZ regs - 16) with (spZ regs - 2144 + 2128) by lia. exact (CK 1%nat 33 2128 eq_refl).
- replace (spZ regs - 24) with (spZ regs - 2144 + 2120) by lia. exact (CK 2%nat 34 2120 eq_refl).
- replace (spZ regs - 32) with (spZ regs - 2144 + 2112) by lia. exact (CK 3%nat 35 2112 eq_refl).
- replace (spZ regs - 40) with (spZ regs - 2144 + 2104) by lia. exact (CK 4%nat 36 2104 eq_refl).
- replace (spZ regs - 48) with (spZ regs - 2144 + 2096) by lia. exact (CK 5%nat 37 2096 eq_refl).
- replace (spZ regs - 56) with (spZ regs - 2144 + 2088) by lia. exact (CK 6%nat 38 2088 eq_refl).
- replace (spZ regs - 64) with (spZ regs - 2144 + 2080) by lia. exact (CK 7%nat 39 2080 eq_refl).
- replace (spZ regs - 72) with (spZ regs - 2144 + 2072) by lia. exact (CK 8%nat 40 2072 eq_refl).
Qed.
Lemma midS : forall E ss ms,
st_ok tfibsegs E ss (restrict H ms) -> ss_resv ss = None -> shapeS ss = true ->
(forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r) ->
(forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms z = mem z) ->
(forall a, sp0 - MC_SCR <= a < sp0 - MC_STK -> apresent H (ms_mem ms) a) ->
MIDP ms.
Proof.
intros E ss ms HS Hrv Hsh HE MEQ PRS.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM). unfold MC_SCR, MC_STK in *.
unfold shapeS in Hsh.
apply andb_prop in Hsh as [Hsh HSV]. apply andb_prop in Hsh as [Hsh R27]. apply andb_prop in Hsh as [Hsh R26]. apply andb_prop in Hsh as [Hsh R25]. apply andb_prop in Hsh as [Hsh R24].
apply andb_prop in Hsh as [Hsh R4]. apply andb_prop in Hsh as [Hsh R3]. apply andb_prop in Hsh as [Hsh R22]. apply andb_prop in Hsh as [Hsh R19].
apply andb_prop in Hsh as [Hsh R2]. apply andb_prop in Hsh as [Hsh R12]. apply andb_prop in Hsh as [Hsh R11]. apply andb_prop in Hsh as [Hsh R10]. apply andb_prop in Hsh as [Hpc Smem].
destruct (ss_mem ss) as [|r0 rest] eqn:Hmem; [discriminate|].
apply andb_prop in Smem as [Smem Hwhi]. apply andb_prop in Smem as [Hbase Hwlo].
apply obase_eqb_eq in Hbase. apply Z.eqb_eq in Hwlo. apply Z.eqb_eq in Hwhi. apply Z.eqb_eq in Hpc.
assert (E2 : bv_unsigned (ew E 2) = sp0) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 d) by (rewrite (HE 10%nat 10%bv eq_refl); exact G10).
assert (E12 : ew E 12 = Z_to_bv 64 n) by (rewrite (HE 12%nat 12%bv eq_refl); exact G12).
assert (RA : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> reg_is ss (bv_unsigned r) (SOff i 0) = true -> getr (ms_regs ms) r = getr regs r).
{ intros r i Hi Hr. rewrite (shape_regs E ss ms r _ HS Hr). cbn [sv_denot]. rewrite (HE i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
unfold MIDP. unfold MC_SCR.
split; [pose proof (st_ok_restrict_mkst tfibsegs H E _ _ HS Hrv) as Hshape; rewrite Hpc in Hshape; exact Hshape|].
split; [rewrite (RA 10%bv 10%nat eq_refl R10); exact G10|]. split; [rewrite (RA 11%bv 11%nat eq_refl R11); exact G11|]. split; [rewrite (RA 12%bv 12%nat eq_refl R12); exact G12|].
split; [rewrite (shape_regs E ss ms 2%bv _ HS R2); cbn [sv_denot]; rewrite (HE 2%nat 2%bv eq_refl); reflexivity|].
split.
{ rewrite (shape_regs E ss ms 19%bv _ HS R19). rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E _)). f_equal.
change (bv_unsigned (sv_denot E ?v)) with (U E v). rewrite (U_add2 E 10 12 d n E10 E12) by lia. reflexivity. }
split; [rewrite (shape_regs E ss ms 22%bv _ HS R22); cbn [sv_denot]; rewrite E12, unsigned_lit_small by lia; reflexivity|].
split; [exact (RA 3%bv 3%nat eq_refl R3)|]. split; [exact (RA 4%bv 4%nat eq_refl R4)|].
split; [exact (RA 24%bv 24%nat eq_refl R24)|]. split; [exact (RA 25%bv 25%nat eq_refl R25)|]. split; [exact (RA 26%bv 26%nat eq_refl R26)|]. split; [exact (RA 27%bv 27%nat eq_refl R27)|].
split; [exact MEQ|]. split.
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 2208)) as [L|L]; [apply PRS; lia|].
apply (st_ok_window_apresent H E ss ms 0 r0 a HS ltac:(rewrite Hmem; reflexivity)); [| unfold TFIB_IMG_END, kHighMemBeg in *; lia].
rewrite Hbase, Hwlo, Hwhi. cbn [base_val]. rewrite E2. unfold MC_STK. lia. }
intros j rz off Hj. rewrite forallb_forall in HSV. specialize (HSV (rz, off) (nth_error_In _ _ Hj)). cbn [fst snd] in HSV.
assert (Hrz : 0 <= rz < 32) by (do 9 (destruct j as [|j]; [cbn in Hj; injection Hj as <- <-; lia|]); destruct j; discriminate).
rewrite <- (HE (Z.to_nat rz) (Z_to_bv 5 rz)).
2:{ rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia. }
exact (shape_chunk E ss ms r0 rest off (Z.to_nat rz) sp0 HS Hmem Hbase E2 HSV).
Qed.
Local Notation Env := (AE2y.Env regs).
Lemma EnvS_reg : forall extra i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew (Env extra) i = getr regs r.
Proof. intros. apply AE2y.Env_reg. assumption. Qed.
Lemma EnvS_x : forall extra j z, nth_error extra j = Some z -> ew (Env extra) (32 + j) = Z_to_bv 64 z.
Proof. intros. apply AE2y.Env_x. assumption. Qed.
Lemma EnvS2 : forall extra, bv_unsigned (ew (Env extra) 2) = sp0.
Proof. intros extra. rewrite (EnvS_reg extra 2 2%bv eq_refl). reflexivity. Qed.
Lemma EnvS10 : forall extra, ew (Env extra) 10 = Z_to_bv 64 d.
Proof. intros extra. rewrite (EnvS_reg extra 10 10%bv eq_refl). exact G10. Qed.
Lemma EnvS11 : forall extra, ew (Env extra) 11 = Z_to_bv 64 x.
Proof. intros extra. rewrite (EnvS_reg extra 11 11%bv eq_refl). exact G11. Qed.
Lemma EnvS12 : forall extra, ew (Env extra) 12 = Z_to_bv 64 n.
Proof. intros extra. rewrite (EnvS_reg extra 12 12%bv eq_refl). exact G12. Qed.
Lemma entS_stk : forall extra, region_ok tfibsegs (Env extra) (mrestrict H mem) stkS.
Proof.
intros extra. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM). unfold stkS, MC_STK.
apply (region_ok_stack tfibsegs (Env extra) _ 2 sp0 (- 2208)); [exact (EnvS2 extra) | lia | lia |].
intros a Ha. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. apply Bpres. lia.
Qed.
Lemma entS_ro : forall extra, Forall (region_ok tfibsegs (Env extra) (mrestrict H mem)) (map ro_region icpt_rodata).
Proof. intros extra. pose proof basics as (_ & _ & _ & _ & _ & _ & BM). exact (icpt_rodata_ok B TB ly S H mem (Env extra) BM). Qed.
Definition EnvD (ms : machine_state) (extra : list Z) : env := AE2y.Env (ms_regs ms) (SV ++ extra).
Lemma EnvD_reg : forall ms extra i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew (EnvD ms extra) i = getr (ms_regs ms) r.
Proof. intros. unfold EnvD. apply AE2y.Env_reg. assumption. Qed.
Lemma EnvD_sv : forall ms extra j, (j < 10)%nat -> ew (EnvD ms extra) (32 + j) = Z_to_bv 64 (nth j SV 0).
Proof.
intros ms extra j Hj. unfold EnvD. apply AE2y.Env_x. rewrite nth_error_app1 by (cbn; lia).
apply nth_error_nth'. cbn. lia.
Qed.
Lemma EnvD_x : forall ms extra j z, nth_error extra j = Some z -> ew (EnvD ms extra) (42 + j) = Z_to_bv 64 z.
Proof.
intros ms extra j z Hj. unfold EnvD. replace (42 + j)%nat with (32 + (10 + j))%nat by lia. apply AE2y.Env_x.
rewrite nth_error_app2 by (cbn; lia). replace (10 + j - length SV)%nat with j by (cbn; lia). exact Hj.
Qed.
Lemma EnvD2 : forall ms extra, MIDP ms -> bv_unsigned (ew (EnvD ms extra) 2) = sp0 - 2144.
Proof.
intros ms extra HM. rewrite (EnvD_reg ms extra 2 2%bv eq_refl). rewrite (proj1 (proj2 (proj2 (proj2 (proj2 HM))))).
pose proof basics as (Bsp & _). unfold w64. apply unsigned_lit_small. lia.
Qed.
Lemma EnvD10 : forall ms extra, MIDP ms -> ew (EnvD ms extra) 10 = Z_to_bv 64 d.
Proof. intros ms extra HM. rewrite (EnvD_reg ms extra 10 10%bv eq_refl). exact (proj1 (proj2 HM)). Qed.
Lemma EnvD11 : forall ms extra, MIDP ms -> ew (EnvD ms extra) 11 = Z_to_bv 64 x.
Proof. intros ms extra HM. rewrite (EnvD_reg ms extra 11 11%bv eq_refl). exact (proj1 (proj2 (proj2 HM))). Qed.
Lemma EnvD12 : forall ms extra, MIDP ms -> ew (EnvD ms extra) 12 = Z_to_bv 64 n.
Proof. intros ms extra HM. rewrite (EnvD_reg ms extra 12 12%bv eq_refl). exact (proj1 (proj2 (proj2 (proj2 HM)))). Qed.
Lemma entD_stk : forall ms extra, MIDP ms -> region_ok tfibsegs (EnvD ms extra) (mrestrict H (ms_mem ms)) stkD.
Proof.
intros ms extra HM. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MEQ & PRS & SAV). unfold MC_SCR in *.
unfold stkD, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
change (base_val (EnvD ms extra) (Some 2%nat)) with (bv_unsigned (ew (EnvD ms extra) 2)). rewrite (EnvD2 ms extra HM).
split; [lia|]. split; [lia|]. split; [intros o Ho; apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia | apply PRS; lia]|].
unfold stkD_chunks.
assert (CK : forall (j : nat) off rz soff, nth_error SAVED j = Some (rz, soff) -> off = 2144 + soff -> (j < 10)%nat ->
YP09.chunk_ok tfibsegs (EnvD ms extra) (mrestrict H (ms_mem ms)) (sp0 - 2144) (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros j off rz soff Hj Hoff Hj10. eapply (chunk_ok_val tfibsegs (EnvD ms extra) _ (sp0 - 2144) off 8 _ (nth j SV 0)).
- cbn [sv_denot]. rewrite (EnvD_sv ms extra j Hj10), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- do 10 (destruct j as [|j]; [cbn; apply u64_range|]). lia.
- zside.
- subst off. replace (sp0 - 2144 + (2144 + soff)) with (sp0 + soff) by lia.
replace (nth j SV 0) with (bv_unsigned (getr regs (Z_to_bv 5 rz))); [exact (SAV j rz soff Hj)|].
do 9 (destruct j as [|j]; [cbn in Hj; injection Hj as <- <-; reflexivity|]). destruct j; discriminate. }
repeat apply Forall_cons; try apply Forall_nil.
+ exact (CK 0%nat 2136 1 (-8) eq_refl eq_refl ltac:(lia)).
+ exact (CK 1%nat 2128 8 (-16) eq_refl eq_refl ltac:(lia)).
+ exact (CK 2%nat 2120 9 (-24) eq_refl eq_refl ltac:(lia)).
+ exact (CK 3%nat 2112 18 (-32) eq_refl eq_refl ltac:(lia)).
+ exact (CK 4%nat 2104 19 (-40) eq_refl eq_refl ltac:(lia)).
+ exact (CK 5%nat 2096 20 (-48) eq_refl eq_refl ltac:(lia)).
+ exact (CK 6%nat 2088 21 (-56) eq_refl eq_refl ltac:(lia)).
+ exact (CK 7%nat 2080 22 (-64) eq_refl eq_refl ltac:(lia)).
+ exact (CK 8%nat 2072 23 (-72) eq_refl eq_refl ltac:(lia)).
Qed.
Lemma entD_ro : forall ms extra, MIDP ms -> Forall (region_ok tfibsegs (EnvD ms extra) (mrestrict H (ms_mem ms))) (map ro_region icpt_rodata).
Proof.
intros ms extra HM. pose proof basics as (Bsp & Bhi & _ & _ & _ & _ & BM).
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MEQ & _). unfold MC_SCR in MEQ.
pose proof (icpt_rodata_ok B TB ly S H mem (EnvD ms extra) BM) as F0.
assert (WF : regions_wf (map ro_region icpt_rodata) = true) by (vm_compute; reflexivity).
apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) F0 r Hr) as Hr0.
pose proof (regions_wf_In _ r WF Hr) as Hwf. apply region_wf_facts in Hwf as (_ & _ & Hci).
assert (Hlit : exists e, In e icpt_rodata /\ r = ro_region e) by (apply in_map_iff in Hr as (e & <- & He); exists e; auto).
destruct Hlit as (e & He & ->).
assert (Hrange : 0 <= fst (fst e) /\ fst (fst e) + snd (fst e) <= 0x200000).
{ cbn in He. repeat (destruct He as [<-|He]; [cbn; lia|]). destruct He. }
eapply (region_ok_transport tfibsegs (EnvD ms extra) (EnvD ms extra)); [exact Hr0 | reflexivity | | | | exact Hci].
- intros c Hc. unfold ro_region in Hc. cbn [YP09.r_chunks] in Hc. apply in_map_iff in Hc as (cc & <- & _). cbn. reflexivity.
- intros a Ha. unfold ro_region in Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha.
apply AF0x.mbyte_mrestrict_same. apply MEQ. rewrite unsigned_lit_small by lia. unfold kHighMemBeg in *. lia.
- intros a Ha. unfold ro_region in Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia.
Qed.
Lemma entS0 : n = 0 -> st_ok tfibsegs (Env []) ssS0 (restrict H (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros Hn0. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
rewrite restrict_mkst_fx. unfold ssS0. unfold AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [])) with (Env []).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply entS_stk | apply entS_ro].
- apply pairwise_disjoint_of_extents. unfold stkS, icpt_rodata, ro_region, extent_of_region.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite (EnvS2 []). unfold MC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok factsS0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (EnvS2 []), (EnvS10 []), (EnvS11 []), (EnvS12 []), !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
Qed.
Definition MIDQ : world tfibsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists ms mat, c' = mkCfg ms (with_vm_backing (m_vm_lazy md) mat md) /\ MIDP ms.
Lemma pathS0 : n = 0 -> SRr tfibsegs W (cfg_at tfibsegs MC_ENTRY regs mem md) POSTc.
Proof.
intros Hn0. set (QQ := POSTc).
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
unfold cfg_at. change (w64 MC_ENTRY) with (Z_to_bv 64 MC_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold MC_SCR, MC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
set (EE := Env []). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply EnvS_reg; assumption).
pose proof (EnvS2 []) as EE2. pose proof (EnvS10 []) as EE10. pose proof (EnvS11 []) as EE11. pose proof (EnvS12 []) as EE12. fold EE in EE2, EE10, EE11, EE12.
pose proof (entS0 Hn0) as HS0. fold EE in HS0.
assert (CONT : forall msq matq, st_ok tfibsegs EE q0_c (restrict H msq) ->
(forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem msq z = mem z) ->
(forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem msq z <> None) ->
SRr tfibsegs W (mkCfg msq (with_vm_backing (m_vm_lazy md) matq md)) QQ).
{ intros ms0 mat0 HSc MEQ0' PSL0'. clear MEQ0 PSL0. rename MEQ0' into MEQ0. rename PSL0' into PSL0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HSc r_q0_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG q0_e0 13) (RG q0_e0 12) HS1 (br_ovf_false EE 11 12 x n EE11 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q0_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_GEU (RG q0_e1 13) (RG q0_e1 22) HS2 (br_cls_zero EE ltac:(rewrite EE12, Hn0; reflexivity))) as HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q0_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG q0_e2 12) (SLit 0) HS3 (br_n_zero EE ltac:(rewrite EE12, Hn0; reflexivity))) as HS3'.
change (neg_bc BC_NE) with BC_EQ in HS3'. clear HS3.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS3' r_q0_3)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). rewrite ?wvb_wvb in *.
assert (MEQ4 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z).
{ intros z Hz. rewrite (HF4 z); [apply MEQ3; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None).
{ intros z Hz. rewrite (HF4 z); [apply PSL3; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF4 HFr4.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG q0_e3 13) (RG q0_e3 12) HS4 (br_ovf_false EE 10 12 d n EE10 EE12 ltac:(lia) ltac:(lia))) as HS4'.
change (neg_bc BC_LTU) with BC_GEU in HS4'. clear HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS4' r_q0_4)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (HF5 z); [apply MEQ4; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None).
{ intros z Hz. rewrite (HF5 z); [apply PSL4; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF5 HFr5.
apply (finish0 EE q0_e4 ms5 mat5 HS5 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ5. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms5 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL5 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
}
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_q0o_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
destruct (Z.eq_dec d x) as [Hdx|Hdx].
{
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q0o_e0 10) (RG q0o_e0 11) HS1 (eq_trans (br_eq_atoms EE 10 11 d x EE10 EE11 ltac:(lia) ltac:(lia)) (proj2 (Z.eqb_eq _ _) Hdx))) as HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q0oC_0)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_dropc EE _ _ HS2) as HSq. rewrite q0oC_canon in HSq. exact (CONT ms2 mat2 HSq MEQ2 PSL2). }
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_EQ (RG q0o_e0 10) (RG q0o_e0 11) HS1 (eq_trans (br_eq_atoms EE 10 11 d x EE10 EE11 ltac:(lia) ltac:(lia)) (proj2 (Z.eqb_neq _ _) Hdx))) as HS1n.
change (neg_bc BC_EQ) with BC_NE in HS1n. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1n r_q0oA_0)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
destruct (Z_lt_le_dec x (d + n)) as [Hov|Hov].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q0oA_e0 11) (RG q0oA_e0 19) HS2 (eq_trans (br_geu_atom_add2 EE 11 10 12 x d n EE11 EE10 EE12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) (f_equal negb (proj2 (Z.ltb_lt _ _) Hov)))) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q0oB_0)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG q0oB_e0 10) (RG q0oB_e0 21) HS3 (eq_trans (br_ltu_atom_add2 EE 10 11 12 d x n EE10 EE11 EE12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) (proj2 (Z.ltb_ge d (x + n)) ltac:(lia)))) as HS3'.
change (neg_bc BC_LTU) with BC_GEU in HS3'. clear HS3.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS3' r_q0oB_1)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). rewrite ?wvb_wvb in *.
assert (MEQ4 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z).
{ intros z Hz. rewrite (HF4 z); [apply MEQ3; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None).
{ intros z Hz. rewrite (HF4 z); [apply PSL3; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF4 HFr4.
pose proof (st_ok_dropc EE _ _ HS4) as HSq. rewrite q0oB_canon in HSq. exact (CONT ms4 mat4 HSq MEQ4 PSL4).
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_GEU (RG q0oA_e0 11) (RG q0oA_e0 19) HS2 (eq_trans (br_geu_atom_add2 EE 11 10 12 x d n EE11 EE10 EE12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) (f_equal negb (proj2 (Z.ltb_ge _ _) Hov)))) as HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q0oA_1)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
pose proof (st_ok_dropc EE _ _ HS3) as HSq. rewrite q0oA_canon in HSq. exact (CONT ms3 mat3 HSq MEQ3 PSL3).
Qed.
End l.
End f.
