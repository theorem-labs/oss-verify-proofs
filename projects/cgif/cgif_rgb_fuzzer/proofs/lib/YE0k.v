(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0l YK0s YK0o YQ0k YK1d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ0a YQ04 YQ05 YQ0e YQ02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10 YP0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o YA0k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF01.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YE1j YF8r YF64 YE04 YE0v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section f. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition MS_ENTRY {imgk : img} : Z := (0x5224c + D_2c4).
Definition MS_STK : Z := 2192.
Definition MS_REAL {imgk : img} : Z := (0x9b894 + D_10ec).
Definition MS_RA {imgk : img} : Z := (0x522e8 + D_2c4).
Definition K : nat := 48.
Definition shreg1 (t : Z) : YQ0b.region :=
YQ0b.mkRegion (Some 32%nat) SB (SB + t + 1) SB SB
((if 0 <? t then [YQ0b.mkChunk SB (CZero t)] else []) ++ [YQ0b.mkChunk (SB + t) (CVal 1 (SOff 34 0))]).
Definition shregs2 : smem :=
[ YQ0b.mkRegion (Some 32%nat) SB (SB + 1) SB SB [YQ0b.mkChunk SB (CZero 1)];
YQ0b.mkRegion (Some 33%nat) SB (SB + 1) SB SB [YQ0b.mkChunk SB (CVal 1 (SOff 34 0))] ].
Definition aliases1 (t : Z) : list (sv * sv) :=
[ (SAlu ALU_SRL (SOff 10 0) (SLit 3), SOff 32 0);
(SAlu ALU_SRL (SAlu ALU_ADD (SOff 10 (-1)) (SOff 12 0)) (SLit 3), SOff 32 t) ].
Definition aliases2 : list (sv * sv) :=
[ (SAlu ALU_SRL (SOff 10 0) (SLit 3), SOff 32 0);
(SAlu ALU_SRL (SAlu ALU_ADD (SOff 10 (-1)) (SOff 12 0)) (SLit 3), SOff 33 0);
(SAlu ALU_AND (SOff 10 7) (SLit (-8)), SOff 37 0);
(SAlu ALU_AND (SAlu ALU_ADD (SOff 10 0) (SOff 12 0)) (SLit (-8)), SOff 38 0);
(SAlu ALU_SRL (SOff 37 0) (SLit 3), SOff 39 0);
(SAlu ALU_SRL (SOff 38 0) (SLit 3), SOff 40 0) ].
Definition stk : YQ0b.region := YQ0b.mkRegion (Some 2%nat) (- MS_STK) 0 (- MS_STK) 0 [].
Definition facts0 : list (nat * afact) := [(2%nat, mkAF (2^44) (2^47) 4); (10%nat, mkAF 0 (2^47) 0); (12%nat, mkAF 0 0 0)].
Definition facts1 : list (nat * afact) :=
[(2%nat, mkAF (2^44) (2^47) 4); (10%nat, mkAF 0 (2^47) 0); (12%nat, mkAF 1 64 0); (32%nat, mkAF 0 (2^44) 0); (34%nat, mkAF 0 7 0)].
Definition facts2L : list (nat * afact) :=
[(2%nat, mkAF (2^44) (2^47) 4); (10%nat, mkAF 0 0x7fff7fbe 0); (12%nat, mkAF 65 (2^32 - 1) 0);
(32%nat, mkAF 0 (2^44) 0); (33%nat, mkAF 0 (2^44) 0); (34%nat, mkAF 0 7 0);
(37%nat, mkAF 0 0x7fff7fc8 3); (38%nat, mkAF 0 0x7fff7fff 3); (39%nat, mkAF 0 (2^44) 0); (40%nat, mkAF 0 (2^44) 0)].
Definition facts2H : list (nat * afact) :=
[(2%nat, mkAF (2^44) (2^47) 4); (10%nat, mkAF 0x10007fff8000 (2^47 - 66) 0); (12%nat, mkAF 65 (2^32 - 1) 0);
(32%nat, mkAF 0 (2^44) 0); (33%nat, mkAF 0 (2^44) 0); (34%nat, mkAF 0 7 0);
(37%nat, mkAF 0x10007fff8000 (2^47 - 1) 3); (38%nat, mkAF 0x10007fff8000 (2^47 - 1) 3); (39%nat, mkAF 0 (2^44) 0); (40%nat, mkAF 0 (2^44) 0)].
Definition ss0 {imgk : img} : sstate := mkSS MS_ENTRY sr_atoms (stk :: map ro_region icpt_rodata) None (mkFacts facts0 [] []).
Definition ss1 {imgk : img} (t : Z) : sstate := mkSS MS_ENTRY sr_atoms (stk :: shreg1 t :: map ro_region icpt_rodata) None (mkFacts facts1 [] (aliases1 t)).
Definition ss2L {imgk : img} : sstate := mkSS MS_ENTRY sr_atoms (stk :: shregs2 ++ map ro_region icpt_rodata) None (mkFacts facts2L [] aliases2).
Definition ss2H {imgk : img} : sstate := mkSS MS_ENTRY sr_atoms (stk :: shregs2 ++ map ro_region icpt_rodata) None (mkFacts facts2H [] aliases2).
Definition RUN {imgk : img} (s : sstate) := sym_runN tfxsegs tbl_icpt FUEL s.
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition AC (s : sstate) (c : branch_cond) (a b : sv) : sstate := YQ09.add_cond s (mkAC c a b).
Definition p0_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((ss0)))).
Definition p0_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p0_s0)))).
Lemma r_p0_0 {imgk : img} : RUN p0_s0 = (p0_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 10 0) (SLit (-1))) (SOff 12 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p0_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p0_e0 BC_GEU (RG p0_e0 13) (RG p0_e0 12))))).
Definition p0_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p0_s1)))).
Lemma r_p0_1 {imgk : img} : RUN p0_s1 = (p0_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 12 (-65)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p0_s2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p0_e1 BC_GEU (RG p0_e1 14) (RG p0_e1 13))))).
Definition p0_e2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p0_s2)))).
Lemma r_p0_2 {imgk : img} : RUN p0_s2 = (p0_e2, RS_stopped (SR_branch BC_NE (SOff 12 0) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p0_s3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p0_e2 BC_EQ (RG p0_e2 12) (SLit 0))))).
Definition p0_e3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p0_s3)))).
Lemma r_p0_3 {imgk : img} : RUN p0_s3 = (p0_e3, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_0_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((ss1 0)))).
Definition p1_0_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_0_s0)))).
Lemma r_p1_0_0 {imgk : img} : RUN p1_0_s0 = (p1_0_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 10 0) (SLit (-1))) (SOff 12 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_0_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_0_e0 BC_GEU (RG p1_0_e0 13) (RG p1_0_e0 12))))).
Definition p1_0_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_0_s1)))).
Lemma r_p1_0_1 {imgk : img} : RUN p1_0_s1 = (p1_0_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 12 (-65)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_0_s2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_0_e1 BC_LTU (RG p1_0_e1 14) (RG p1_0_e1 13))))).
Definition p1_0_e2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_0_s2)))).
Lemma r_p1_0_2 {imgk : img} : RUN p1_0_s2 = (p1_0_e2, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_0_s3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((set_regs_pc (set_regs_pc p1_0_e2 [((16%bv : bv 5), SOff 35 0)] (0x522d0 + D_2c4)) [((17%bv : bv 5), SOff 36 0)] (0x522d4 + D_2c4))))).
Definition p1_0_e3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_0_s3)))).
Lemma r_p1_0_3 {imgk : img} : RUN p1_0_s3 = (p1_0_e3, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_0z_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_0_e3 BC_EQ (RG p1_0_e3 16) (SLit 0))))).
Definition p1_0z_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_0z_s0)))).
Lemma r_p1_0z_0 {imgk : img} : RUN p1_0z_s0 = (p1_0z_e0, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_0n_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_0_e3 BC_NE (RG p1_0_e3 16) (SLit 0))))).
Definition p1_0n_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_0n_s0)))).
Lemma r_p1_0n_0 {imgk : img} : RUN p1_0n_s0 = (p1_0n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 0%nat 10 12 34) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_0n_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_0n_e0 BC_EQ (RG p1_0n_e0 13) (SLit 0))))).
Definition p1_0n_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_0n_s1)))).
Lemma r_p1_0n_1 {imgk : img} : RUN p1_0n_s1 = (p1_0n_e1, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_1_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((ss1 1)))).
Definition p1_1_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_1_s0)))).
Lemma r_p1_1_0 {imgk : img} : RUN p1_1_s0 = (p1_1_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 10 0) (SLit (-1))) (SOff 12 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_1_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_1_e0 BC_GEU (RG p1_1_e0 13) (RG p1_1_e0 12))))).
Definition p1_1_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_1_s1)))).
Lemma r_p1_1_1 {imgk : img} : RUN p1_1_s1 = (p1_1_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 12 (-65)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_1_s2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_1_e1 BC_LTU (RG p1_1_e1 14) (RG p1_1_e1 13))))).
Definition p1_1_e2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_1_s2)))).
Lemma r_p1_1_2 {imgk : img} : RUN p1_1_s2 = (p1_1_e2, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_1_s3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((set_regs_pc (set_regs_pc p1_1_e2 [((16%bv : bv 5), SOff 35 0)] (0x522d0 + D_2c4)) [((17%bv : bv 5), SOff 36 0)] (0x522d4 + D_2c4))))).
Definition p1_1_e3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_1_s3)))).
Lemma r_p1_1_3 {imgk : img} : RUN p1_1_s3 = (p1_1_e3, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_1z_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_1_e3 BC_EQ (RG p1_1_e3 16) (SLit 0))))).
Definition p1_1z_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_1z_s0)))).
Lemma r_p1_1z_0 {imgk : img} : RUN p1_1z_s0 = (p1_1z_e0, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_1n_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_1_e3 BC_NE (RG p1_1_e3 16) (SLit 0))))).
Definition p1_1n_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_1n_s0)))).
Lemma r_p1_1n_0 {imgk : img} : RUN p1_1n_s0 = (p1_1n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 1%nat 10 12 34) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_1n_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_1n_e0 BC_EQ (RG p1_1n_e0 13) (SLit 0))))).
Definition p1_1n_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_1n_s1)))).
Lemma r_p1_1n_1 {imgk : img} : RUN p1_1n_s1 = (p1_1n_e1, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_2_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((ss1 2)))).
Definition p1_2_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_2_s0)))).
Lemma r_p1_2_0 {imgk : img} : RUN p1_2_s0 = (p1_2_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 10 0) (SLit (-1))) (SOff 12 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_2_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_2_e0 BC_GEU (RG p1_2_e0 13) (RG p1_2_e0 12))))).
Definition p1_2_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_2_s1)))).
Lemma r_p1_2_1 {imgk : img} : RUN p1_2_s1 = (p1_2_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 12 (-65)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_2_s2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_2_e1 BC_LTU (RG p1_2_e1 14) (RG p1_2_e1 13))))).
Definition p1_2_e2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_2_s2)))).
Lemma r_p1_2_2 {imgk : img} : RUN p1_2_s2 = (p1_2_e2, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_2_s3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((set_regs_pc (set_regs_pc p1_2_e2 [((16%bv : bv 5), SOff 35 0)] (0x522d0 + D_2c4)) [((17%bv : bv 5), SOff 36 0)] (0x522d4 + D_2c4))))).
Definition p1_2_e3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_2_s3)))).
Lemma r_p1_2_3 {imgk : img} : RUN p1_2_s3 = (p1_2_e3, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_2z_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_2_e3 BC_EQ (RG p1_2_e3 16) (SLit 0))))).
Definition p1_2z_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_2z_s0)))).
Lemma r_p1_2z_0 {imgk : img} : RUN p1_2z_s0 = (p1_2z_e0, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_2n_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_2_e3 BC_NE (RG p1_2_e3 16) (SLit 0))))).
Definition p1_2n_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_2n_s0)))).
Lemma r_p1_2n_0 {imgk : img} : RUN p1_2n_s0 = (p1_2n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 2%nat 10 12 34) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_2n_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_2n_e0 BC_EQ (RG p1_2n_e0 13) (SLit 0))))).
Definition p1_2n_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_2n_s1)))).
Lemma r_p1_2n_1 {imgk : img} : RUN p1_2n_s1 = (p1_2n_e1, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_3_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((ss1 3)))).
Definition p1_3_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_3_s0)))).
Lemma r_p1_3_0 {imgk : img} : RUN p1_3_s0 = (p1_3_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 10 0) (SLit (-1))) (SOff 12 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_3_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_3_e0 BC_GEU (RG p1_3_e0 13) (RG p1_3_e0 12))))).
Definition p1_3_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_3_s1)))).
Lemma r_p1_3_1 {imgk : img} : RUN p1_3_s1 = (p1_3_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 12 (-65)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_3_s2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_3_e1 BC_LTU (RG p1_3_e1 14) (RG p1_3_e1 13))))).
Definition p1_3_e2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_3_s2)))).
Lemma r_p1_3_2 {imgk : img} : RUN p1_3_s2 = (p1_3_e2, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_3_s3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((set_regs_pc (set_regs_pc p1_3_e2 [((16%bv : bv 5), SOff 35 0)] (0x522d0 + D_2c4)) [((17%bv : bv 5), SOff 36 0)] (0x522d4 + D_2c4))))).
Definition p1_3_e3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_3_s3)))).
Lemma r_p1_3_3 {imgk : img} : RUN p1_3_s3 = (p1_3_e3, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_3z_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_3_e3 BC_EQ (RG p1_3_e3 16) (SLit 0))))).
Definition p1_3z_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_3z_s0)))).
Lemma r_p1_3z_0 {imgk : img} : RUN p1_3z_s0 = (p1_3z_e0, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_3n_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_3_e3 BC_NE (RG p1_3_e3 16) (SLit 0))))).
Definition p1_3n_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_3n_s0)))).
Lemma r_p1_3n_0 {imgk : img} : RUN p1_3n_s0 = (p1_3n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 3%nat 10 12 34) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_3n_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_3n_e0 BC_EQ (RG p1_3n_e0 13) (SLit 0))))).
Definition p1_3n_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_3n_s1)))).
Lemma r_p1_3n_1 {imgk : img} : RUN p1_3n_s1 = (p1_3n_e1, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_4_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((ss1 4)))).
Definition p1_4_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_4_s0)))).
Lemma r_p1_4_0 {imgk : img} : RUN p1_4_s0 = (p1_4_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 10 0) (SLit (-1))) (SOff 12 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_4_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_4_e0 BC_GEU (RG p1_4_e0 13) (RG p1_4_e0 12))))).
Definition p1_4_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_4_s1)))).
Lemma r_p1_4_1 {imgk : img} : RUN p1_4_s1 = (p1_4_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 12 (-65)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_4_s2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_4_e1 BC_LTU (RG p1_4_e1 14) (RG p1_4_e1 13))))).
Definition p1_4_e2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_4_s2)))).
Lemma r_p1_4_2 {imgk : img} : RUN p1_4_s2 = (p1_4_e2, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_4_s3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((set_regs_pc (set_regs_pc p1_4_e2 [((16%bv : bv 5), SOff 35 0)] (0x522d0 + D_2c4)) [((17%bv : bv 5), SOff 36 0)] (0x522d4 + D_2c4))))).
Definition p1_4_e3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_4_s3)))).
Lemma r_p1_4_3 {imgk : img} : RUN p1_4_s3 = (p1_4_e3, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_4z_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_4_e3 BC_EQ (RG p1_4_e3 16) (SLit 0))))).
Definition p1_4z_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_4z_s0)))).
Lemma r_p1_4z_0 {imgk : img} : RUN p1_4z_s0 = (p1_4z_e0, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_4n_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_4_e3 BC_NE (RG p1_4_e3 16) (SLit 0))))).
Definition p1_4n_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_4n_s0)))).
Lemma r_p1_4n_0 {imgk : img} : RUN p1_4n_s0 = (p1_4n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 4%nat 10 12 34) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_4n_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_4n_e0 BC_EQ (RG p1_4n_e0 13) (SLit 0))))).
Definition p1_4n_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_4n_s1)))).
Lemma r_p1_4n_1 {imgk : img} : RUN p1_4n_s1 = (p1_4n_e1, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_5_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((ss1 5)))).
Definition p1_5_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_5_s0)))).
Lemma r_p1_5_0 {imgk : img} : RUN p1_5_s0 = (p1_5_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 10 0) (SLit (-1))) (SOff 12 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_5_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_5_e0 BC_GEU (RG p1_5_e0 13) (RG p1_5_e0 12))))).
Definition p1_5_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_5_s1)))).
Lemma r_p1_5_1 {imgk : img} : RUN p1_5_s1 = (p1_5_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 12 (-65)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_5_s2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_5_e1 BC_LTU (RG p1_5_e1 14) (RG p1_5_e1 13))))).
Definition p1_5_e2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_5_s2)))).
Lemma r_p1_5_2 {imgk : img} : RUN p1_5_s2 = (p1_5_e2, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_5_s3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((set_regs_pc (set_regs_pc p1_5_e2 [((16%bv : bv 5), SOff 35 0)] (0x522d0 + D_2c4)) [((17%bv : bv 5), SOff 36 0)] (0x522d4 + D_2c4))))).
Definition p1_5_e3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_5_s3)))).
Lemma r_p1_5_3 {imgk : img} : RUN p1_5_s3 = (p1_5_e3, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_5z_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_5_e3 BC_EQ (RG p1_5_e3 16) (SLit 0))))).
Definition p1_5z_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_5z_s0)))).
Lemma r_p1_5z_0 {imgk : img} : RUN p1_5z_s0 = (p1_5z_e0, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_5n_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_5_e3 BC_NE (RG p1_5_e3 16) (SLit 0))))).
Definition p1_5n_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_5n_s0)))).
Lemma r_p1_5n_0 {imgk : img} : RUN p1_5n_s0 = (p1_5n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 5%nat 10 12 34) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_5n_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_5n_e0 BC_EQ (RG p1_5n_e0 13) (SLit 0))))).
Definition p1_5n_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_5n_s1)))).
Lemma r_p1_5n_1 {imgk : img} : RUN p1_5n_s1 = (p1_5n_e1, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_6_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((ss1 6)))).
Definition p1_6_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_6_s0)))).
Lemma r_p1_6_0 {imgk : img} : RUN p1_6_s0 = (p1_6_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 10 0) (SLit (-1))) (SOff 12 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_6_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_6_e0 BC_GEU (RG p1_6_e0 13) (RG p1_6_e0 12))))).
Definition p1_6_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_6_s1)))).
Lemma r_p1_6_1 {imgk : img} : RUN p1_6_s1 = (p1_6_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 12 (-65)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_6_s2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_6_e1 BC_LTU (RG p1_6_e1 14) (RG p1_6_e1 13))))).
Definition p1_6_e2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_6_s2)))).
Lemma r_p1_6_2 {imgk : img} : RUN p1_6_s2 = (p1_6_e2, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_6_s3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((set_regs_pc (set_regs_pc p1_6_e2 [((16%bv : bv 5), SOff 35 0)] (0x522d0 + D_2c4)) [((17%bv : bv 5), SOff 36 0)] (0x522d4 + D_2c4))))).
Definition p1_6_e3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_6_s3)))).
Lemma r_p1_6_3 {imgk : img} : RUN p1_6_s3 = (p1_6_e3, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_6z_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_6_e3 BC_EQ (RG p1_6_e3 16) (SLit 0))))).
Definition p1_6z_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_6z_s0)))).
Lemma r_p1_6z_0 {imgk : img} : RUN p1_6z_s0 = (p1_6z_e0, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_6n_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_6_e3 BC_NE (RG p1_6_e3 16) (SLit 0))))).
Definition p1_6n_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_6n_s0)))).
Lemma r_p1_6n_0 {imgk : img} : RUN p1_6n_s0 = (p1_6n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 6%nat 10 12 34) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_6n_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_6n_e0 BC_EQ (RG p1_6n_e0 13) (SLit 0))))).
Definition p1_6n_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_6n_s1)))).
Lemma r_p1_6n_1 {imgk : img} : RUN p1_6n_s1 = (p1_6n_e1, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_7_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((ss1 7)))).
Definition p1_7_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_7_s0)))).
Lemma r_p1_7_0 {imgk : img} : RUN p1_7_s0 = (p1_7_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 10 0) (SLit (-1))) (SOff 12 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_7_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_7_e0 BC_GEU (RG p1_7_e0 13) (RG p1_7_e0 12))))).
Definition p1_7_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_7_s1)))).
Lemma r_p1_7_1 {imgk : img} : RUN p1_7_s1 = (p1_7_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 12 (-65)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_7_s2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_7_e1 BC_LTU (RG p1_7_e1 14) (RG p1_7_e1 13))))).
Definition p1_7_e2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_7_s2)))).
Lemma r_p1_7_2 {imgk : img} : RUN p1_7_s2 = (p1_7_e2, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_7_s3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((set_regs_pc (set_regs_pc p1_7_e2 [((16%bv : bv 5), SOff 35 0)] (0x522d0 + D_2c4)) [((17%bv : bv 5), SOff 36 0)] (0x522d4 + D_2c4))))).
Definition p1_7_e3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_7_s3)))).
Lemma r_p1_7_3 {imgk : img} : RUN p1_7_s3 = (p1_7_e3, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_7z_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_7_e3 BC_EQ (RG p1_7_e3 16) (SLit 0))))).
Definition p1_7z_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_7z_s0)))).
Lemma r_p1_7z_0 {imgk : img} : RUN p1_7z_s0 = (p1_7z_e0, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_7n_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_7_e3 BC_NE (RG p1_7_e3 16) (SLit 0))))).
Definition p1_7n_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_7n_s0)))).
Lemma r_p1_7n_0 {imgk : img} : RUN p1_7n_s0 = (p1_7n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 7%nat 10 12 34) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_7n_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_7n_e0 BC_EQ (RG p1_7n_e0 13) (SLit 0))))).
Definition p1_7n_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_7n_s1)))).
Lemma r_p1_7n_1 {imgk : img} : RUN p1_7n_s1 = (p1_7n_e1, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_8_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((ss1 8)))).
Definition p1_8_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_8_s0)))).
Lemma r_p1_8_0 {imgk : img} : RUN p1_8_s0 = (p1_8_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 10 0) (SLit (-1))) (SOff 12 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_8_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_8_e0 BC_GEU (RG p1_8_e0 13) (RG p1_8_e0 12))))).
Definition p1_8_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_8_s1)))).
Lemma r_p1_8_1 {imgk : img} : RUN p1_8_s1 = (p1_8_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 12 (-65)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_8_s2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_8_e1 BC_LTU (RG p1_8_e1 14) (RG p1_8_e1 13))))).
Definition p1_8_e2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_8_s2)))).
Lemma r_p1_8_2 {imgk : img} : RUN p1_8_s2 = (p1_8_e2, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_8_s3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((set_regs_pc (set_regs_pc p1_8_e2 [((16%bv : bv 5), SOff 35 0)] (0x522d0 + D_2c4)) [((17%bv : bv 5), SOff 36 0)] (0x522d4 + D_2c4))))).
Definition p1_8_e3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_8_s3)))).
Lemma r_p1_8_3 {imgk : img} : RUN p1_8_s3 = (p1_8_e3, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_8z_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_8_e3 BC_EQ (RG p1_8_e3 16) (SLit 0))))).
Definition p1_8z_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_8z_s0)))).
Lemma r_p1_8z_0 {imgk : img} : RUN p1_8z_s0 = (p1_8z_e0, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_8n_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_8_e3 BC_NE (RG p1_8_e3 16) (SLit 0))))).
Definition p1_8n_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_8n_s0)))).
Lemma r_p1_8n_0 {imgk : img} : RUN p1_8n_s0 = (p1_8n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 8%nat 10 12 34) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p1_8n_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p1_8n_e0 BC_EQ (RG p1_8n_e0 13) (SLit 0))))).
Definition p1_8n_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p1_8n_s1)))).
Lemma r_p1_8n_1 {imgk : img} : RUN p1_8n_s1 = (p1_8n_e1, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p2L_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((ss2L)))).
Definition p2L_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p2L_s0)))).
Lemma r_p2L_0 {imgk : img} : RUN p2L_s0 = (p2L_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 10 0) (SLit (-1))) (SOff 12 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p2L_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p2L_e0 BC_GEU (RG p2L_e0 13) (RG p2L_e0 12))))).
Definition p2L_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p2L_s1)))).
Lemma r_p2L_1 {imgk : img} : RUN p2L_s1 = (p2L_e1, RS_stopped (SR_branch BC_GEU (SLit 2147450879) (SAlu ALU_ADD (SOff 10 0) (SOff 12 0)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p2L_s2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p2L_e1 BC_GEU (SLit 2147450879) (RG p2L_e1 18))))).
Definition p2L_e2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p2L_s2)))).
Lemma r_p2L_2 {imgk : img} : RUN p2L_s2 = (p2L_e2, RS_stopped (SR_branch BC_GEU (SOff 10 0) (SAlu ALU_ADD (SOff 10 0) (SOff 12 0)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p2L_s3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p2L_e2 BC_LTU (RG p2L_e2 8) (RG p2L_e2 18))))).
Definition p2L_e3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p2L_s3)))).
Lemma r_p2L_3 {imgk : img} : RUN p2L_s3 = (p2L_e3, RS_stopped (SR_branch BC_EQ (SOff 34 0) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p2Lz_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p2L_e3 BC_EQ (RG p2L_e3 11) (SLit 0))))).
Definition p2Lz_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p2Lz_s0)))).
Lemma r_p2Lz_0 {imgk : img} : RUN p2Lz_s0 = (p2Lz_e0, RS_stopped (SR_branch BC_GEU (SOff 39 2147450880) (SOff 40 2147450880))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p2Lz_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p2Lz_e0 BC_LTU (RG p2Lz_e0 19) (RG p2Lz_e0 10))))).
Definition p2Lz_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p2Lz_s1)))).
Lemma r_p2Lz_1 {imgk : img} : RUN p2Lz_s1 = (p2Lz_e1, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p2Lz_s2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((ss_after_mz p2Lz_e1 (ss_mem p2Lz_e1) K (0x54de8 + D_2c4))))).
Definition p2Lz_e2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p2Lz_s2)))).
Lemma r_p2Lz_2 {imgk : img} : RUN p2Lz_s2 = (p2Lz_e2, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p2Ln_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p2L_e3 BC_NE (RG p2L_e3 11) (SLit 0))))).
Definition p2Ln_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p2Ln_s0)))).
Lemma r_p2Ln_0 {imgk : img} : RUN p2Ln_s0 = (p2Ln_e0, RS_stopped (SR_branch BC_LT (SAlu ALU_AND (SAlu ALU_ADD (SOff 10 (-1)) (SOff 12 0)) (SLit 7)) (SOff 34 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p2Ln_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p2Ln_e0 BC_LT (RG p2Ln_e0 12) (RG p2Ln_e0 11))))).
Definition p2Ln_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p2Ln_s1)))).
Lemma r_p2Ln_1 {imgk : img} : RUN p2Ln_s1 = (p2Ln_e1, RS_stopped (SR_branch BC_GEU (SOff 39 2147450880) (SOff 40 2147450880))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p2Ln_s2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p2Ln_e1 BC_LTU (RG p2Ln_e1 19) (RG p2Ln_e1 10))))).
Definition p2Ln_e2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p2Ln_s2)))).
Lemma r_p2Ln_2 {imgk : img} : RUN p2Ln_s2 = (p2Ln_e2, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p2Ln_s3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((ss_after_mz p2Ln_e2 (ss_mem p2Ln_e2) K (0x54de8 + D_2c4))))).
Definition p2Ln_e3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p2Ln_s3)))).
Lemma r_p2Ln_3 {imgk : img} : RUN p2Ln_s3 = (p2Ln_e3, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p2H_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((ss2H)))).
Definition p2H_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p2H_s0)))).
Lemma r_p2H_0 {imgk : img} : RUN p2H_s0 = (p2H_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 10 0) (SLit (-1))) (SOff 12 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p2H_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p2H_e0 BC_GEU (RG p2H_e0 13) (RG p2H_e0 12))))).
Definition p2H_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p2H_s1)))).
Lemma r_p2H_1 {imgk : img} : RUN p2H_s1 = (p2H_e1, RS_stopped (SR_branch BC_LTU (SLit 140737488355327) (SAlu ALU_ADD (SOff 10 0) (SOff 12 0)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p2H_s2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p2H_e1 BC_GEU (SLit 140737488355327) (RG p2H_e1 18))))).
Definition p2H_e2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p2H_s2)))).
Lemma r_p2H_2 {imgk : img} : RUN p2H_s2 = (p2H_e2, RS_stopped (SR_branch BC_GEU (SOff 10 0) (SAlu ALU_ADD (SOff 10 0) (SOff 12 0)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p2H_s3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p2H_e2 BC_LTU (RG p2H_e2 8) (RG p2H_e2 18))))).
Definition p2H_e3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p2H_s3)))).
Lemma r_p2H_3 {imgk : img} : RUN p2H_s3 = (p2H_e3, RS_stopped (SR_branch BC_EQ (SOff 34 0) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p2Hz_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p2H_e3 BC_EQ (RG p2H_e3 11) (SLit 0))))).
Definition p2Hz_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p2Hz_s0)))).
Lemma r_p2Hz_0 {imgk : img} : RUN p2Hz_s0 = (p2Hz_e0, RS_stopped (SR_branch BC_GEU (SOff 39 2147450880) (SOff 40 2147450880))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p2Hz_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p2Hz_e0 BC_LTU (RG p2Hz_e0 19) (RG p2Hz_e0 10))))).
Definition p2Hz_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p2Hz_s1)))).
Lemma r_p2Hz_1 {imgk : img} : RUN p2Hz_s1 = (p2Hz_e1, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p2Hz_s2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((ss_after_mz p2Hz_e1 (ss_mem p2Hz_e1) K (0x54de8 + D_2c4))))).
Definition p2Hz_e2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p2Hz_s2)))).
Lemma r_p2Hz_2 {imgk : img} : RUN p2Hz_s2 = (p2Hz_e2, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p2Hn_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p2H_e3 BC_NE (RG p2H_e3 11) (SLit 0))))).
Definition p2Hn_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p2Hn_s0)))).
Lemma r_p2Hn_0 {imgk : img} : RUN p2Hn_s0 = (p2Hn_e0, RS_stopped (SR_branch BC_LT (SAlu ALU_AND (SAlu ALU_ADD (SOff 10 (-1)) (SOff 12 0)) (SLit 7)) (SOff 34 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p2Hn_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p2Hn_e0 BC_LT (RG p2Hn_e0 12) (RG p2Hn_e0 11))))).
Definition p2Hn_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p2Hn_s1)))).
Lemma r_p2Hn_1 {imgk : img} : RUN p2Hn_s1 = (p2Hn_e1, RS_stopped (SR_branch BC_GEU (SOff 39 2147450880) (SOff 40 2147450880))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p2Hn_s2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC p2Hn_e1 BC_LTU (RG p2Hn_e1 19) (RG p2Hn_e1 10))))).
Definition p2Hn_e2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p2Hn_s2)))).
Lemma r_p2Hn_2 {imgk : img} : RUN p2Hn_s2 = (p2Hn_e2, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition p2Hn_s3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((ss_after_mz p2Hn_e2 (ss_mem p2Hn_e2) K (0x54de8 + D_2c4))))).
Definition p2Hn_e3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN p2Hn_s3)))).
Lemma r_p2Hn_3 {imgk : img} : RUN p2Hn_s3 = (p2Hn_e3, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition epi_chunks : list YQ0b.chunk :=
[YQ0b.mkChunk 2120 (CVal 8 (SOff 32 0)); YQ0b.mkChunk 2112 (CVal 8 (SOff 33 0)); YQ0b.mkChunk 2104 (CVal 8 (SOff 34 0));
YQ0b.mkChunk 2096 (CVal 8 (SOff 35 0)); YQ0b.mkChunk 2088 (CVal 8 (SOff 36 0)); YQ0b.mkChunk 2080 (CVal 8 (SOff 37 0));
YQ0b.mkChunk 2072 (CVal 8 (SOff 38 0))].
Definition ss_epi {imgk : img} : sstate := mkSS MS_RA sr_atoms [YQ0b.mkRegion (Some 2%nat) 0 2128 0 0 epi_chunks] None
(mkFacts [(2%nat, mkAF (2^43) (2^47) 4)] [] []).
Definition epi_e {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN ss_epi)))).
Lemma r_epi {imgk : img} : RUN ss_epi = (epi_e, RS_stopped (SR_jalr (SOff 32 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition MS_SCR : Z := 2200.
Section g. Context {imgk : img}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfxsegs B.
Lemma ms_tail : forall ly S (W : world tfxsegs) regs mem md (regs1 : bvmap 5 word) (mem1 : word -> option byte) mat1 d x n,
ecall_pre tfxsegs B ly S W regs mem md ->
getr regs 11 = w64 x -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
dest_ok tfxsegs B ly S W regs mem d n ->
getr regs1 10 = w64 d -> getr regs1 11 = w64 x -> getr regs1 12 = w64 n ->
getr regs1 1 = w64 MS_RA -> getr regs1 2 = w64 (spZ regs - 2128) ->
getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
getr regs1 22 = getr regs 22 -> getr regs1 23 = getr regs 23 -> getr regs1 24 = getr regs 24 -> getr regs1 25 = getr regs 25 -> getr regs1 26 = getr regs 26 -> getr regs1 27 = getr regs 27 ->
(forall z : word, ~ (spZ regs - MS_SCR <= bv_unsigned z < spZ regs) -> mem1 z = mem z) ->
(forall a, spZ regs - MS_SCR <= a < spZ regs -> apresent (w_H W) mem1 a) ->
val_mem tfxsegs (mrestrict (w_H W) mem1) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
val_mem tfxsegs (mrestrict (w_H W) mem1) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) ->
val_mem tfxsegs (mrestrict (w_H W) mem1) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
val_mem tfxsegs (mrestrict (w_H W) mem1) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
val_mem tfxsegs (mrestrict (w_H W) mem1) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) ->
val_mem tfxsegs (mrestrict (w_H W) mem1) (spZ regs - 48) 8 (bv_unsigned (getr regs 20)) ->
val_mem tfxsegs (mrestrict (w_H W) mem1) (spZ regs - 56) 8 (bv_unsigned (getr regs 21)) ->
SRr tfxsegs W (mkCfg (mkst regs1 (Z_to_bv 64 MS_REAL) mem1 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat1 md))
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfxsegs (raZ regs) regs' mem' md' /\
AR tfxsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 d /\
(forall i, 0 <= i < n -> aview tfxsegs (w_H W) mem' (d + i) = Some (x mod 256)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview tfxsegs (w_H W) mem' a = aview tfxsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros ly S W regs mem md regs1 mem1 mat1 d x n HPRE Hx Hn Hd Hdn HDST G10 G11 G12 G1 G2 G3 G4 G22 G23 G24 G25 G26 G27
MEQ1 PRS1 V0 V1 V2 V3 V4 V5 V6.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof YF8r.Hwx_tfa as Hwx. assert (HES : ESTACK = 4096) by img_refl. assert (HSC : MS_SCR = 2200) by img_refl.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (sp0 := spZ regs) in *. assert (Hsp44 : 2 ^ 44 <= sp0 <= 2 ^ 47) by (img_try (unfold kHighMemBeg in Lbeg; img_lia)).
set (H := w_H W) in *.
assert (DW : forall a, d <= a < d + n -> writable_at tfxsegs (mrestrict H mem1) a /\ H (Z_to_bv 64 a) = false).
{ intros a Ha. destruct (HDST a Ha) as (Hw & _ & Hns).
assert (Hw1 : writable_at tfxsegs (mrestrict H mem1) a).
{ img_apply (writable_at_same (mrestrict H mem) (mrestrict H mem1) a); [|img_try (img_exact Hw)].
unfold mrestrict. rewrite (MEQ1 (Z_to_bv 64 a)); [img_refl|]. rewrite unsigned_lit_small by img_lia. unfold sp0 in *. img_lia. }
split; [img_try (img_exact Hw1)|]. destruct (H (Z_to_bv 64 a)) eqn:Hh; [|img_refl].
exfalso. img_exact (hidden_not_writable W mem1 a ltac:(img_lia) Hh Hw1). }
set (nn := Z.to_nat n). assert (Hnn : Z.of_nat nn = n) by (img_try ((subst nn; cbv beta); img_lia)).
assert (SOK : store_ok tfxsegs (mrestrict H mem1) (w64 d) nn = true).
{ img_apply store_ok_of_all; unfold w64; rewrite unsigned_lit_small by img_lia; [img_lia|].
intros z Hz. pose proof (proj1 (DW (bv_unsigned z) ltac:(img_lia))) as Wz. unfold writable_at in Wz. rewrite Z_to_bv_bv_unsigned in Wz. img_exact Wz. }
destruct (tfx_memset (w64 d) (w64 x) (w64 n) nn (mrestrict H mem1) (seg_rom tfxsegs) regs1 G10 G11 G12
ltac:(img_try (unfold w64; rewrite unsigned_lit_small by img_lia; img_lia)) SOK ltac:(img_try (unfold w64; rewrite unsigned_lit_small by img_lia; img_lia)))
as (regs2 & Hms & A10 & Hkeep).
rewrite G1 in Hms. replace (v_jalr (w64 MS_RA) 0) with (Z_to_bv 64 MS_RA : word) in Hms by (img_try (img_apply bv_eq; (img_case; vm_compute); img_refl)).
img_change (Z_to_bv 64 tfx_A_musl_memset) with (Z_to_bv 64 MS_REAL) in Hms.
set (cb := Z_to_bv 8 (bv_unsigned (w64 x) mod 256)) in Hms.
set (m1r := mrestrict H mem1) in *. set (m2r := wbytes m1r (w64 d) (repeat cb nn)) in Hms.
assert (KEEP : forall r : bv 5, r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> getr regs2 r = getr regs1 r)
by (img_try (intros r; img_apply Hkeep)).
set (mem2 := munrestrict H mem1 m2r).
assert (LEN : Z.of_nat (length (repeat cb nn)) = n) by (img_try (rewrite repeat_length; img_exact Hnn)).
assert (M2out : forall z : word, ~ (d <= bv_unsigned z < d + n) -> mem2 z = mem1 z).
{ intros z Hz. (subst mem2 m2r; cbv beta). unfold munrestrict. destruct (H z) eqn:Hh; [img_refl|].
assert (Ew : wbytes m1r (w64 d) (repeat cb nn) z = m1r z).
{ destruct (Z_lt_le_dec (bv_unsigned z) d) as [L|L].
- img_apply wbytes_below; unfold w64; rewrite ?LEN, unsigned_lit_small by img_lia; img_lia.
- img_apply wbytes_above. unfold w64. rewrite LEN, unsigned_lit_small by img_lia. img_lia. }
rewrite Ew. (subst m1r; cbv beta). unfold mrestrict. rewrite Hh. img_refl. }
assert (M2in : forall i, 0 <= i < n -> mem2 (Z_to_bv 64 (d + i)) = Some cb).
{ intros i Hi. (subst mem2; cbv beta). unfold munrestrict. rewrite (proj2 (DW (d + i) ltac:(img_lia))).
(subst m2r; cbv beta). rewrite (wbytes_inside (repeat cb nn) m1r (w64 d) (Z_to_bv 64 (d + i)));
unfold w64; rewrite ?LEN, ?unsigned_lit_small by img_lia; [|img_lia|img_lia].
replace (Z.to_nat (d + i - d)) with (Z.to_nat i) by img_lia. img_apply nth_error_repeat. img_lia. }
assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 - MS_SCR <= a < sp0) -> aview tfxsegs H mem2 a = aview tfxsegs H mem a).
{ intros a Hr Ha Hs. img_apply aview_same. rewrite (M2out (Z_to_bv 64 a)), (MEQ1 (Z_to_bv 64 a)); [img_refl| |];
rewrite unsigned_lit_small by img_lia; [img_try (img_exact Hs) | img_try (img_exact Ha)]. }
assert (MS2 : forall z : word, sp0 - MS_SCR <= bv_unsigned z < sp0 -> mem2 z = mem1 z).
{ intros z Hz. img_apply M2out. intros Hd'. destruct (HDST (bv_unsigned z) Hd') as (_ & _ & Hns). img_apply Hns. unfold sp0 in *. img_lia. }
assert (A2 : getr regs2 2 = w64 (sp0 - 2128)) by (img_try (rewrite KEEP by (intros H'; discriminate H'); img_exact G2)).
set (E2 := Ereg regs2 [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21]).
assert (E2_2 : bv_unsigned (ew E2 2) = sp0 - 2128).
{ (subst E2; cbv beta). rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl), A2. unfold w64. img_apply unsigned_lit_small. img_lia. }
assert (VM : forall a v, val_mem tfxsegs (mrestrict H mem1) a 8 v -> sp0 - MS_SCR <= a -> a + 8 <= sp0 -> val_mem tfxsegs (mrestrict H mem2) a 8 v).
{ intros a v Hv Hlo Hhi. img_apply (val_mem_frame H mem1 mem2 a 8 v); [|img_try (img_exact Hv)]. intros k Hk. img_apply MS2. rewrite unsigned_lit_small by img_lia. img_lia. }
assert (HSe : st_ok tfxsegs E2 ss_epi (restrict H (mkst regs2 (Z_to_bv 64 MS_RA) mem2 (seg_rom tfxsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_epi. img_apply (entry_st_ok_full tfxsegs);
img_change (Ereg regs2 [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21]) with E2.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks].
replace (base_val E2 (Some 2%nat)) with (sp0 - 2128) by (img_try (symmetry; img_exact E2_2)).
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
unfold epi_chunks.
assert (CK : forall (j : nat) (r : bv 5) off, nth j [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21] (Z_to_bv 64 0) = getr regs r ->
off = 2120 - 8 * Z.of_nat j -> Z.of_nat j < 7 ->
val_mem tfxsegs (mrestrict H mem1) (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs r)) ->
YQ0b.chunk_ok tfxsegs E2 (mrestrict H mem2) (sp0 - 2128) (YQ0b.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros j r off Hnth Hoff Hj8 Hv. eapply (chunk_ok_val tfxsegs E2 _ (sp0 - 2128) off 8 _ (bv_unsigned (getr regs r))).
- cbn [sv_denot]. (subst E2; cbv beta). rewrite (ew_Ereg_extra regs2 _ j), Hnth, Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- pose proof (u64_range (getr regs r)). zside.
- zside.
- (subst off; cbv beta). replace (sp0 - 2128 + (2120 - 8 * Z.of_nat j)) with (sp0 - 8 - 8 * Z.of_nat j) by img_lia. img_apply VM; [img_try (img_exact Hv) | img_lia | img_lia]. }
repeat img_apply Forall_cons; try img_apply Forall_nil.
+ img_apply (CK 0%nat 1%bv); [img_refl | img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 8 - 8 * Z.of_nat 0) with (sp0 - 8) by img_lia; img_exact V0)].
+ img_apply (CK 1%nat 8%bv); [img_refl | img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 8 - 8 * Z.of_nat 1) with (sp0 - 16) by img_lia; img_exact V1)].
+ img_apply (CK 2%nat 9%bv); [img_refl | img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 8 - 8 * Z.of_nat 2) with (sp0 - 24) by img_lia; img_exact V2)].
+ img_apply (CK 3%nat 18%bv); [img_refl | img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 8 - 8 * Z.of_nat 3) with (sp0 - 32) by img_lia; img_exact V3)].
+ img_apply (CK 4%nat 19%bv); [img_refl | img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 8 - 8 * Z.of_nat 4) with (sp0 - 40) by img_lia; img_exact V4)].
+ img_apply (CK 5%nat 20%bv); [img_refl | img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 8 - 8 * Z.of_nat 5) with (sp0 - 48) by img_lia; img_exact V5)].
+ img_apply (CK 6%nat 21%bv); [img_refl | img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 8 - 8 * Z.of_nat 6) with (sp0 - 56) by img_lia; img_exact V6)].
- img_apply pairwise_disjoint_of_extents. cbn. repeat split.
- split; [|img_try (split; img_exact I)]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2_2.
img_change (2 ^ 4) with 16. unfold sp0 in *. repeat split; try img_lia.
all: replace (spZ regs - 2128) with (spZ regs + (-133) * 16) by img_lia; rewrite Z_mod_plus_full; img_exact Hal16. }
eapply (SRr_msteps tfxsegs Hwx W); [img_try (rewrite restrict_mkst_fx; img_exact Hms)|].
intros model' Hsbm _. rewrite (same_but_materialized_wvb md model' Hsbm). cbn [ms_mem mkst].
img_change (unrestrict H mem1 (mkst regs2 (Z_to_bv 64 MS_RA) m2r (seg_rom tfxsegs))) with (mkst regs2 (Z_to_bv 64 MS_RA) mem2 (seg_rom tfxsegs)).
eapply SRr_bind; [img_norm_st HSe r_epi; img_try (img_apply (icpt_phase W E2 ss_epi epi_e _ _ _ HSe r_epi))|].
cbv beta. intros W1 c1 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
eapply (SRr_ret_at tfxsegs tbl_icpt tbl_icpt_ok Hwx W E2); [img_try (img_exact HS3) | img_refl | img_try ((img_case; vm_compute); img_refl) |].
intros mat'. rewrite wvb_wvb.
assert (MEQ3 : forall z, ms_mem ms3 z = mem2 z) by (img_try (intros z; img_apply HF3; intros Hin; destruct (in_wrange_windows E2 _ _ Hin) as (b & lo & hi & Ht & Hw); cbn in Ht; destruct Ht as [Hq|[]]; injection Hq as <- <- <-; cbn [base_val] in Hw; img_lia)).
rreg HS3 (1%bv : bv 5) Q1. rreg HS3 (2%bv : bv 5) Q2. rreg HS3 (10%bv : bv 5) Q10.
rreg HS3 (8%bv : bv 5) Q8. rreg HS3 (9%bv : bv 5) Q9. rreg HS3 (18%bv : bv 5) Q18. rreg HS3 (19%bv : bv 5) Q19.
rreg HS3 (20%bv : bv 5) Q20. rreg HS3 (21%bv : bv 5) Q21. rreg HS3 (22%bv : bv 5) Q22.
rreg HS3 (3%bv : bv 5) Q3. rreg HS3 (4%bv : bv 5) Q4.
rreg HS3 (23%bv : bv 5) Q23. rreg HS3 (24%bv : bv 5) Q24. rreg HS3 (25%bv : bv 5) Q25. rreg HS3 (26%bv : bv 5) Q26. rreg HS3 (27%bv : bv 5) Q27.
assert (X32 : ew E2 32 = getr regs 1) by (img_try ((subst E2; cbv beta); img_exact (ew_Ereg_extra regs2 _ 0))).
rewrite X32 in Q1.
replace (v_jalr (getr (ms_regs ms3) 1) 0) with (w64 (raZ regs)) by (img_try (rewrite Q1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; img_exact Hra)).
split; [img_refl|]. exists (ms_regs ms3), (ms_mem ms3), (with_vm_backing (m_vm_lazy md) mat' md).
pose proof (same_but_materialized_frame md _ (with_vm_backing_same md mat')) as MF.
assert (AV3 : forall a, aview tfxsegs H (ms_mem ms3) a = aview tfxsegs H mem2 a) by (img_try (intros a; img_apply aview_same; img_apply MEQ3)).
split; [img_refl|].
split; [|img_try (split; [|split; [|split; [|split; [|split]]]])].
-   img_apply (al_frame _ _ LAWS ly S W mem md (ms_mem ms3) _ HAR).
+ intros a Hr Hown. rewrite AV3. img_apply AV2; [img_try (img_exact Hr) | img_try (intros Hd'; img_exact (proj1 (proj2 (HDST a Hd')) Hown)) |].
intros Hs. img_exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(img_try (unfold sp0 in *; img_lia)) Hown).
+ intros a Hv. rewrite AV3. rewrite (YE0v.aview_mod _ mem2 a). rewrite (YE0v.aview_mod _ mem a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (img_try (img_apply Z.mod_pos_bound; img_lia)). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' d) as [L1|L1]; [| img_try (destruct (Z_lt_le_dec a' (d + n)) as [L2|L2])].
2:{ unfold aview, mbyte, mrestrict. rewrite (proj2 (DW a' ltac:(img_lia))). replace a' with (d + (a' - d)) by img_lia. rewrite (M2in (a' - d)) by img_lia. discriminate. }
all: destruct (Z_lt_le_dec a' (sp0 - MS_SCR)) as [L3|L3]; [img_try (rewrite AV2 by img_lia; img_exact Hv)|].
all: destruct (Z_lt_le_dec a' sp0) as [L4|L4]; [| img_try (rewrite AV2 by img_lia; img_exact Hv)].
all: img_apply aview_some_of_apresent; img_apply (apresent_same H mem1 mem2 a' (MS2 (Z_to_bv 64 a') ltac:(img_try (rewrite unsigned_lit_small by img_lia; img_lia)))); img_apply PRS1; img_lia.
+ img_apply MF. + img_apply MF. + img_apply MF.
+ img_exact (YE0v.hs_kept_trans _ _ _ _ (YE0v.hs_kept_trans _ _ _ _ (YE0v.hs_kept_win _ _ _ _ _ _ _ _ MEQ1 HpresE ltac:(img_try (unfold ESTACK, MS_SCR; img_lia)) ltac:(img_lia)) (YE0v.hs_kept_unrestrict _ _ _)) (YE0v.hs_kept_eq _ _ _ MEQ3)).
-
intros r Hr. unfold acallee_saved in Hr.
assert (X : forall j rr, nth j [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21] (Z_to_bv 64 0) = getr regs rr -> ew E2 (32 + j) = getr regs rr)
by (img_try (intros jj rr Hnth; (subst E2; cbv beta); rewrite (ew_Ereg_extra regs2 _ jj); img_exact Hnth)).
assert (Y : forall i (rr : bv 5), Z.of_nat i = bv_unsigned rr -> ew E2 i = getr regs2 rr) by (img_try (intros ii rr Hnth; (subst E2; cbv beta); img_exact (ew_Ereg_nat regs2 _ ii rr Hnth))).
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
+ replace (Z_to_bv 5 2) with (2%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q2. img_apply bv_eq. rewrite Z_to_bv_unsigned, E2_2. unfold sp0, spZ, bv_wrap. img_change (bv_modulus 64) with (2 ^ 64).
pose proof (u64_range (getr regs 2)). rewrite Z.mod_small by img_lia. img_lia.
+ replace (Z_to_bv 5 3) with (3%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q3, (Y 3%nat 3%bv eq_refl), KEEP by (img_try (intros H'; discriminate H')). img_exact G3.
+ replace (Z_to_bv 5 4) with (4%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q4, (Y 4%nat 4%bv eq_refl), KEEP by (img_try (intros H'; discriminate H')). img_exact G4.
+ replace (Z_to_bv 5 8) with (8%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q8. img_exact (X 1%nat 8%bv eq_refl).
+ replace (Z_to_bv 5 9) with (9%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q9. img_exact (X 2%nat 9%bv eq_refl).
+ assert (Hc : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by img_lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
* replace (Z_to_bv 5 18) with (18%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q18. img_exact (X 3%nat 18%bv eq_refl).
* replace (Z_to_bv 5 19) with (19%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q19. img_exact (X 4%nat 19%bv eq_refl).
* replace (Z_to_bv 5 20) with (20%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q20. img_exact (X 5%nat 20%bv eq_refl).
* replace (Z_to_bv 5 21) with (21%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q21. img_exact (X 6%nat 21%bv eq_refl).
* replace (Z_to_bv 5 22) with (22%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q22, (Y 22%nat 22%bv eq_refl), KEEP by (img_try (intros H'; discriminate H')). img_exact G22.
* replace (Z_to_bv 5 23) with (23%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q23, (Y 23%nat 23%bv eq_refl), KEEP by (img_try (intros H'; discriminate H')). img_exact G23.
* replace (Z_to_bv 5 24) with (24%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q24, (Y 24%nat 24%bv eq_refl), KEEP by (img_try (intros H'; discriminate H')). img_exact G24.
* replace (Z_to_bv 5 25) with (25%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q25, (Y 25%nat 25%bv eq_refl), KEEP by (img_try (intros H'; discriminate H')). img_exact G25.
* replace (Z_to_bv 5 26) with (26%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q26, (Y 26%nat 26%bv eq_refl), KEEP by (img_try (intros H'; discriminate H')). img_exact G26.
* replace (Z_to_bv 5 27) with (27%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q27, (Y 27%nat 27%bv eq_refl), KEEP by (img_try (intros H'; discriminate H')). img_exact G27.
- img_apply with_vm_backing_same.
- rewrite Q10. (subst E2; cbv beta). rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl). img_exact A10.
- intros i Hi. rewrite AV3. unfold aview, mbyte, mrestrict. rewrite (proj2 (DW (d + i) ltac:(img_lia))), (M2in i Hi). cbn [option_map].
f_equal. (subst cb; cbv beta). unfold w64. rewrite !Z_to_bv_unsigned. unfold bv_wrap. img_change (bv_modulus 64) with (256 * 2 ^ 56). img_change (bv_modulus 8) with 256.
rewrite Z.mod_mod by img_lia. img_apply Z.mod_mod_divide. exists (2 ^ 56). img_refl.
- intros a Hr Hd' Hs. rewrite AV3. img_apply AV2; [img_try (img_exact Hr) | img_try (img_exact Hd') | img_try (unfold sp0 in *; img_lia)].
- intros a Hp. pose proof Hp as [Hh [b Hb]].
assert (Hr : apresent H (ms_mem ms3) a <-> apresent H (ms_mem ms3) (a mod 2 ^ 64)).
{ unfold apresent. rewrite <- (YE0v.Z_to_bv64_of_mod a). tauto. }
img_apply (proj2 Hr). clear Hr.
assert (Hp' : apresent H mem (a mod 2 ^ 64)) by (img_try (unfold apresent; rewrite (YE0v.Z_to_bv64_of_mod a); img_exact Hp)).
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (img_try (img_apply Z.mod_pos_bound; img_lia)). set (a' := a mod 2 ^ 64) in *.
img_apply (apresent_same H mem2 (ms_mem ms3) a' (MEQ3 _)).
destruct (Z_lt_le_dec a' d) as [L1|L1]; [| img_try (destruct (Z_lt_le_dec a' (d + n)) as [L2|L2])].
2:{ split; [img_try (img_exact (proj2 (DW a' ltac:(img_lia))))|]. exists cb. replace a' with (d + (a' - d)) by img_lia. img_apply M2in. img_lia. }
all: destruct (Z_lt_le_dec a' (sp0 - MS_SCR)) as [L3|L3];
[img_try (img_apply (apresent_same H mem mem2 a'); [rewrite (M2out (Z_to_bv 64 a')), (MEQ1 (Z_to_bv 64 a')) by (rewrite unsigned_lit_small by img_lia; img_lia); img_refl | img_exact Hp'])|].
all: destruct (Z_lt_le_dec a' sp0) as [L4|L4];
[| img_try (img_apply (apresent_same H mem mem2 a'); [rewrite (M2out (Z_to_bv 64 a')), (MEQ1 (Z_to_bv 64 a')) by (rewrite unsigned_lit_small by img_lia; img_lia); img_refl | img_exact Hp'])].
all: img_apply (apresent_same H mem1 mem2 a' (MS2 (Z_to_bv 64 a') ltac:(img_try (rewrite unsigned_lit_small by img_lia; img_lia)))); img_apply PRS1; img_lia.
Qed.
End g.
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (RG ss r) v.
Definition chunk_is {imgk : img} (off : Z) (v : sv) (c : YQ0b.chunk) : bool :=
(YQ0b.c_off c =? off) && match YQ0b.c_val c with CVal n e => N.eqb n 8 && sv_eqb e v | _ => false end.
Definition has_chunk {imgk : img} (ss : sstate) (off : Z) (v : sv) : bool :=
match ss_mem ss with r :: _ => existsb (chunk_is off v) (YQ0b.r_chunks r) | [] => false end.
Definition tail_shape {imgk : img} (ss : sstate) : bool :=
(ss_pc ss =? MS_REAL) &&
match ss_mem ss with r :: _ => obase_eqb (YQ0b.r_base r) (Some 2%nat) && (YQ0b.r_wlo r =? - MS_STK) && (YQ0b.r_whi r =? 0) | [] => false end &&
reg_is ss 10 (SOff 10 0) && reg_is ss 11 (SOff 11 0) && reg_is ss 12 (SOff 12 0) && reg_is ss 1 (SLit MS_RA) && reg_is ss 2 (SOff 2 (-2128)) &&
reg_is ss 3 (SOff 3 0) && reg_is ss 4 (SOff 4 0) && reg_is ss 23 (SOff 23 0) && reg_is ss 24 (SOff 24 0) && reg_is ss 25 (SOff 25 0) &&
reg_is ss 26 (SOff 26 0) && reg_is ss 27 (SOff 27 0) && reg_is ss 22 (SOff 22 0) &&
has_chunk ss (-8) (SOff 1 0) && has_chunk ss (-16) (SOff 8 0) && has_chunk ss (-24) (SOff 9 0) && has_chunk ss (-32) (SOff 18 0) &&
has_chunk ss (-40) (SOff 19 0) && has_chunk ss (-48) (SOff 20 0) && has_chunk ss (-56) (SOff 21 0).
Lemma chunk_is_sound {imgk : img} : forall off v c, chunk_is off v c = true -> c = YQ0b.mkChunk off (CVal 8 v).
Proof.
intros off v [o cv] Hc. unfold chunk_is in Hc. cbn [YQ0b.c_off YQ0b.c_val] in Hc. apply andb_prop in Hc as [Ho Hv].
apply Z.eqb_eq in Ho. destruct cv as [nn e| | |]; try discriminate. apply andb_prop in Hv as [Hn He].
apply N.eqb_eq in Hn. apply sv_eqb_eq in He. (subst; cbv beta). img_refl.
Qed.
Section h. Context {imgk : img}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfxsegs B.
Hypothesis TB : TfxSyms B.
Variables (ly : alayout) (S : astate) (W : world tfxsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (d x n : Z).
Hypothesis HPRE : ecall_pre tfxsegs B ly S W regs mem md.
Hypothesis G10 : getr regs 10 = w64 d.
Hypothesis G11 : getr regs 11 = w64 x.
Hypothesis G12 : getr regs 12 = w64 n.
Hypothesis Hn : 0 <= n < 2 ^ 32.
Hypothesis Hd : 0 <= d.
Hypothesis Hdn : d + n <= 2 ^ 63.
Hypothesis HDST : dest_ok tfxsegs B ly S W regs mem d n.
Hypothesis HRA : range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF d n.
Hypothesis HHULL : 0 < n -> shadow_hull_vis (aview tfxsegs (w_H W) mem) d n.
Hypothesis HAM : amem_range d n.
Definition POSTm : world tfxsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfxsegs (raZ regs) regs' mem' md' /\
AR tfxsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 d /\
(forall i, 0 <= i < n -> aview tfxsegs (w_H W) mem' (d + i) = Some (x mod 256)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview tfxsegs (w_H W) mem' a = aview tfxsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Let sp0 : Z := spZ regs.
Let H := w_H W.
Let g0 : Z := d / 8.
Let g1 : Z := (d + n - 1) / 8.
Let du : Z := (d + 7) / 8 * 8.
Let de : Z := (d + n) / 8 * 8.
Let gu : Z := (d + 7) / 8.
Let ge : Z := (d + n) / 8.
Lemma basics : 2 ^ 44 <= sp0 <= 2 ^ 47 /\ kHighMemBeg + 4096 <= sp0 /\ sp0 mod 16 = 0 /\ d + n <= 2 ^ 47 - 1 /\
(forall a, sp0 - 4096 <= a < sp0 -> apresent H mem a) /\ ARm B ly S (aview tfxsegs H mem).
Proof.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (ESTACK = 4096) by img_refl.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. (subst sp0 H; cbv beta).
split; [img_lia|]. split; [img_lia|]. split; [img_lia|]. split; [img_lia|]. split; [img_try (img_exact HpresE) | img_try (img_exact (proj1 HAR))].
Qed.
Lemma finish : forall E ss ms mat,
st_ok tfxsegs E ss (restrict H ms) -> ss_resv ss = None -> tail_shape ss = true ->
(forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r) ->
(forall z : word, ~ (sp0 - MS_SCR <= bv_unsigned z < sp0) -> ms_mem ms z = mem z) ->
(forall a, sp0 - MS_SCR <= a < sp0 - MS_STK -> apresent H (ms_mem ms) a) ->
SRr tfxsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) POSTm.
Proof.
intros E ss ms mat HS Hrv Hsh HE MEQ PRS.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM). assert (HSC : MS_SCR = 2200) by img_refl. assert (HSK : MS_STK = 2192) by img_refl.
unfold tail_shape in Hsh. apply andb_prop in Hsh as [Hsh C56]. apply andb_prop in Hsh as [Hsh C48]. apply andb_prop in Hsh as [Hsh C40]. apply andb_prop in Hsh as [Hsh C32]. apply andb_prop in Hsh as [Hsh C24]. apply andb_prop in Hsh as [Hsh C16]. apply andb_prop in Hsh as [Hsh C8]. apply andb_prop in Hsh as [Hsh R22]. apply andb_prop in Hsh as [Hsh R27]. apply andb_prop in Hsh as [Hsh R26]. apply andb_prop in Hsh as [Hsh R25]. apply andb_prop in Hsh as [Hsh R24]. apply andb_prop in Hsh as [Hsh R23]. apply andb_prop in Hsh as [Hsh R4]. apply andb_prop in Hsh as [Hsh R3]. apply andb_prop in Hsh as [Hsh R2]. apply andb_prop in Hsh as [Hsh R1]. apply andb_prop in Hsh as [Hsh R12]. apply andb_prop in Hsh as [Hsh R11]. apply andb_prop in Hsh as [Hsh R10]. apply andb_prop in Hsh as [Hsh Smem].
destruct (ss_mem ss) as [|r0 rest] eqn:Hmem; [img_try (discriminate)|].
apply andb_prop in Smem as [Smem Hwhi]. apply andb_prop in Smem as [Hbase Hwlo].
apply obase_eqb_eq in Hbase. apply Z.eqb_eq in Hwlo. apply Z.eqb_eq in Hwhi. apply Z.eqb_eq in Hsh.
assert (E2 : bv_unsigned (ew E 2) = sp0) by (img_try (rewrite (HE 2%nat 2%bv eq_refl); img_refl)).
assert (RD : forall (r : bv 5) v, reg_is ss (bv_unsigned r) v = true -> getr (ms_regs ms) r = sv_denot E v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. img_apply (st_ok_reg_denot H E ss ms r HS). }
assert (RA : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> reg_is ss (bv_unsigned r) (SOff i 0) = true -> getr (ms_regs ms) r = getr regs r).
{ intros r i Hi Hr. rewrite (RD r _ Hr). cbn [sv_denot]. rewrite (HE i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl. }
assert (CK : forall off (r : bv 5) i, Z.of_nat i = bv_unsigned r -> has_chunk ss off (SOff i 0) = true ->
val_mem tfxsegs (mrestrict H (ms_mem ms)) (sp0 + off) 8 (bv_unsigned (getr regs r))).
{ intros off r i Hi Hc. unfold has_chunk in Hc. rewrite Hmem in Hc. apply existsb_exists in Hc as (c & Hin & Hc).
apply chunk_is_sound in Hc. (subst c; cbv beta).
pose proof (st_ok_mem_ok tfxsegs E ss _ HS) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs. rewrite Hmem in Hrs.
pose proof (Forall_inv Hrs) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. rewrite Hbase in Hck. cbn [base_val] in Hck. rewrite E2 in Hck.
img_apply (val_of_chunk_ok tfxsegs E _ _ off 8 (SOff i 0) (bv_unsigned (getr regs r)) Hck).
- cbn [sv_denot]. rewrite (HE i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- pose proof (u64_range (getr regs r)). zside.
- zside. }
pose proof (st_ok_restrict_mkst tfxsegs H E _ _ HS Hrv) as Hshape. rewrite Hsh in Hshape. rewrite Hshape.
img_apply (ms_tail B LAWS ly S W regs mem md (ms_regs ms) (ms_mem ms) mat d x n HPRE G11 Hn Hd Hdn HDST).
- rewrite (RD 10%bv (SOff 10 0) R10). cbn [sv_denot]. rewrite (HE 10%nat 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. img_exact G10.
- rewrite (RD 11%bv (SOff 11 0) R11). cbn [sv_denot]. rewrite (HE 11%nat 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. img_exact G11.
- rewrite (RD 12%bv (SOff 12 0) R12). cbn [sv_denot]. rewrite (HE 12%nat 12%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. img_exact G12.
- rewrite (RD 1%bv (SLit MS_RA) R1). img_refl.
- rewrite (RD 2%bv (SOff 2 (-2128)) R2). cbn [sv_denot]. rewrite (HE 2%nat 2%bv eq_refl). img_refl.
- img_exact (RA 3%bv 3%nat eq_refl R3). - img_exact (RA 4%bv 4%nat eq_refl R4).
- img_exact (RA 22%bv 22%nat eq_refl R22). - img_exact (RA 23%bv 23%nat eq_refl R23). - img_exact (RA 24%bv 24%nat eq_refl R24). - img_exact (RA 25%bv 25%nat eq_refl R25).
- img_exact (RA 26%bv 26%nat eq_refl R26). - img_exact (RA 27%bv 27%nat eq_refl R27).
- img_exact MEQ.
- intros a Ha. destruct (Z_lt_le_dec a (sp0 - MS_STK)) as [L|L]; [img_try (img_apply PRS; img_lia)|].
img_apply (st_ok_window_apresent H E ss ms 0 r0 a HS ltac:(img_try (rewrite Hmem; img_refl))); [| img_try (unfold TFX_IMG_END, kHighMemBeg in *; img_lia)].
rewrite Hbase, Hwlo, Hwhi. cbn [base_val]. rewrite E2. img_lia.
- replace (sp0 - 8) with (sp0 + -8) by img_lia. img_exact (CK (-8) 1%bv 1%nat eq_refl C8).
- replace (sp0 - 16) with (sp0 + -16) by img_lia. img_exact (CK (-16) 8%bv 8%nat eq_refl C16).
- replace (sp0 - 24) with (sp0 + -24) by img_lia. img_exact (CK (-24) 9%bv 9%nat eq_refl C24).
- replace (sp0 - 32) with (sp0 + -32) by img_lia. img_exact (CK (-32) 18%bv 18%nat eq_refl C32).
- replace (sp0 - 40) with (sp0 + -40) by img_lia. img_exact (CK (-40) 19%bv 19%nat eq_refl C40).
- replace (sp0 - 48) with (sp0 + -48) by img_lia. img_exact (CK (-48) 20%bv 20%nat eq_refl C48).
- replace (sp0 - 56) with (sp0 + -56) by img_lia. img_exact (CK (-56) 21%bv 21%nat eq_refl C56).
Qed.
Local Notation Env := (YE0v.Env regs).
Local Notation Env_reg := (YE0v.Env_reg regs).
Local Notation Env_x := (YE0v.Env_x regs).
Lemma Env2 : forall extra, bv_unsigned (ew (Env extra) 2) = sp0.
Proof. intros extra. rewrite (Env_reg extra 2 2%bv eq_refl). img_refl. Qed.
Lemma Env10 : forall extra, ew (Env extra) 10 = Z_to_bv 64 d.
Proof. intros extra. rewrite (Env_reg extra 10 10%bv eq_refl). img_exact G10. Qed.
Lemma Env12 : forall extra, ew (Env extra) 12 = Z_to_bv 64 n.
Proof. intros extra. rewrite (Env_reg extra 12 12%bv eq_refl). img_exact G12. Qed.
Lemma ent_stk : forall extra, region_ok tfxsegs (Env extra) (mrestrict H mem) stk.
Proof.
intros extra. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM). unfold stk, MS_STK.
img_apply (region_ok_stack tfxsegs (Env extra) _ 2 sp0 (- 2192)); [img_try (img_exact (Env2 extra)) | img_lia | img_lia |].
intros a Ha. img_apply YF8r.apresent_writable; [img_try (unfold YF8r.TFX_IMG_END, kHighMemBeg in *; img_lia)|]. img_apply Bpres. img_lia.
Qed.
Lemma ent_ro : forall extra, Forall (region_ok tfxsegs (Env extra) (mrestrict H mem)) (map ro_region icpt_rodata).
Proof. intros extra. pose proof basics as (_ & _ & _ & _ & _ & BM). img_exact (icpt_rodata_ok B TB ly S H mem (Env extra) BM). Qed.
Lemma ent0 : n = 0 -> st_ok tfxsegs (Env []) ss0 (restrict H (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfxsegs))).
Proof.
intros Hn0. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM).
rewrite restrict_mkst_fx. unfold ss0. unfold YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs (map (Z_to_bv 64) [])) with (Env []).
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [img_try (img_apply ent_stk) | img_try (img_apply ent_ro)].
- img_apply pairwise_disjoint_of_extents. unfold stk, icpt_rodata, ro_region, extent_of_region.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite (Env2 []). unfold MS_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; img_lia.
- split; [|img_try (split; img_exact I)]. cbn [f_atoms atoms_ok facts0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (Env2 []), (Env10 []), (Env12 []), !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. repeat split; try img_lia; img_apply Z.mod_1_r.
Qed.
  (* [comment removed for export] *)
  Tactic Notation "icpt_l1t_0" ident(Wk) ident(ck) ident(msk) ident(matk) ident(HSk) ident(HFk) ident(HFrk) ident(MEQk) hyp(MEQp) constr(EE) hyp(EE2) :=
    cbv beta; intros Wk ck _ (-> & msk & matk & -> & HSk & HFk & HFrk); rewrite ?wvb_wvb in *;
    assert (MEQk : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem msk z = mem z);
    [ intros z Hz; rewrite (HFk z); [img_try (img_apply MEQp; unfold MS_STK, MS_SCR in *; img_lia)|]; intros Hin;
      unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [img_try ((img_case; vm_compute); img_refl)|]; unfold MS_STK, MS_SCR in *; img_lia | ];
    clear HFk HFrk.

Lemma path0 : n = 0 -> SRr tfxsegs W (cfg_at tfxsegs MS_ENTRY regs mem md) POSTm.
Proof.
intros Hn0.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM). assert (HSC : MS_SCR = 2200) by img_refl.
unfold cfg_at. img_change (w64 MS_ENTRY) with (Z_to_bv 64 MS_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfxsegs)) z = mem z) by (img_try (intros; img_refl)).
set (EE := Env []). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (img_try (intros; img_apply Env_reg; assumption)).
pose proof (Env2 []) as EE2. pose proof (Env10 []) as EE10. pose proof (Env12 []) as EE12. fold EE in EE2, EE10, EE12.
pose proof (ent0 Hn0) as HS0. fold EE in HS0.
eapply SRr_bind; [img_norm_st HS0 r_p0_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS0 r_p0_0))|].
icpt_l1t_0 W1 c1 ms1 mat1 HS1 HF1 HFr1 MEQ1 MEQ0 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_LTU (RG p0_e0 13) (RG p0_e0 12) HS1 (br_ovf_false EE 10 12 d n EE10 EE12 ltac:(img_lia) ltac:(img_lia))) as HS1'.
img_change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [img_norm_st HS1' r_p0_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS1' r_p0_1))|].
icpt_l1t_0 W2 c2 ms2 mat2 HS2 HF2 HFr2 MEQ2 MEQ1 EE EE2.
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_GEU (RG p0_e1 14) (RG p0_e1 13) HS2 (br_cls_zero EE ltac:(img_try (rewrite EE12, Hn0; img_refl)))) as HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_p0_2; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS2' r_p0_2))|].
icpt_l1t_0 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 MEQ2 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_NE (RG p0_e2 12) (SLit 0) HS3 (br_n_zero EE ltac:(img_try (rewrite EE12, Hn0; img_refl)))) as HS3'.
img_change (neg_bc BC_NE) with BC_EQ in HS3'. clear HS3.
eapply SRr_bind; [img_norm_st HS3' r_p0_3; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS3' r_p0_3))|].
icpt_l1t_0 W4 c4 ms4 mat4 HS4 HF4 HFr4 MEQ4 MEQ3 EE EE2.
img_apply (finish EE p0_e3 ms4 mat4 HS4 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EEreg).
- intros z Hz. img_apply MEQ4. unfold MS_SCR, MS_STK in *. img_lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; img_apply (apresent_same H mem (ms_mem ms4) a); [img_try (img_apply MEQ4; rewrite unsigned_lit_small by img_lia; img_lia) | img_try (img_apply Bpres; img_lia)].
Qed.
Lemma ent1_0 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 0 -> aview tfxsegs H mem (SB + g1) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfxsegs (Env [g0; g1; b1; q1; q2]) (ss1 0) (restrict H (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfxsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
pose proof (Env2 [g0; g1; b1; q1; q2]) as E2. pose proof (Env10 [g0; g1; b1; q1; q2]) as E10. pose proof (Env12 [g0; g1; b1; q1; q2]) as E12.
fold EE in E2, E10, E12.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod d 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound d 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (d + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hg1hi : g1 < 2 ^ 44) by img_lia.
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
rewrite restrict_mkst_fx. unfold ss1. unfold EE, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2])) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [img_try (img_apply ent_stk) | img_try (img_apply Forall_cons; [| img_apply ent_ro])].
unfold shreg1, region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
img_change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_try (unfold kHighMemBeg in *; img_lia)|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
repeat img_apply Forall_cons; try img_apply Forall_nil.
all: first
[ img_apply chunk_ok_zero; intros i Hi; rewrite (YF8r.aview_byte H mem _ 0); [img_refl|];
rewrite <- (ra_granule_zero (aview tfxsegs H mem) d n (g0 + i) HRA ltac:(img_lia) Hd); unfold SB; f_equal; img_lia
| eapply (chunk_ok_val tfxsegs EE _ g0 _ 1 (SOff 34 0) b1); [img_try (cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (zside) | img_try (zside) |];
img_apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; img_lia ].
- img_apply pairwise_disjoint_of_extents. unfold stk, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by img_lia. unfold MS_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; img_lia.
- split; [|img_try (split; [img_exact I|])].
+ cbn [f_atoms atoms_ok facts1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E12, E32, E34, !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. repeat split; try img_lia; img_apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|img_try (split; [|img_exact I])].
* img_apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 32 g0 E32) by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 32 g0 0 E32) by img_lia. (subst g0 g1; cbv beta). img_lia.
Qed.
Lemma ent1_1 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 1 -> aview tfxsegs H mem (SB + g1) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfxsegs (Env [g0; g1; b1; q1; q2]) (ss1 1) (restrict H (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfxsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
pose proof (Env2 [g0; g1; b1; q1; q2]) as E2. pose proof (Env10 [g0; g1; b1; q1; q2]) as E10. pose proof (Env12 [g0; g1; b1; q1; q2]) as E12.
fold EE in E2, E10, E12.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod d 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound d 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (d + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hg1hi : g1 < 2 ^ 44) by img_lia.
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
rewrite restrict_mkst_fx. unfold ss1. unfold EE, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2])) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [img_try (img_apply ent_stk) | img_try (img_apply Forall_cons; [| img_apply ent_ro])].
unfold shreg1, region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
img_change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_try (unfold kHighMemBeg in *; img_lia)|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
repeat img_apply Forall_cons; try img_apply Forall_nil.
all: first
[ img_apply chunk_ok_zero; intros i Hi; rewrite (YF8r.aview_byte H mem _ 0); [img_refl|];
rewrite <- (ra_granule_zero (aview tfxsegs H mem) d n (g0 + i) HRA ltac:(img_lia) Hd); unfold SB; f_equal; img_lia
| eapply (chunk_ok_val tfxsegs EE _ g0 _ 1 (SOff 34 0) b1); [img_try (cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (zside) | img_try (zside) |];
img_apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; img_lia ].
- img_apply pairwise_disjoint_of_extents. unfold stk, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by img_lia. unfold MS_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; img_lia.
- split; [|img_try (split; [img_exact I|])].
+ cbn [f_atoms atoms_ok facts1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E12, E32, E34, !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. repeat split; try img_lia; img_apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|img_try (split; [|img_exact I])].
* img_apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 32 g0 E32) by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 32 g0 1 E32) by img_lia. (subst g0 g1; cbv beta). img_lia.
Qed.
Lemma ent1_2 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 2 -> aview tfxsegs H mem (SB + g1) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfxsegs (Env [g0; g1; b1; q1; q2]) (ss1 2) (restrict H (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfxsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
pose proof (Env2 [g0; g1; b1; q1; q2]) as E2. pose proof (Env10 [g0; g1; b1; q1; q2]) as E10. pose proof (Env12 [g0; g1; b1; q1; q2]) as E12.
fold EE in E2, E10, E12.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod d 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound d 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (d + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hg1hi : g1 < 2 ^ 44) by img_lia.
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
rewrite restrict_mkst_fx. unfold ss1. unfold EE, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2])) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [img_try (img_apply ent_stk) | img_try (img_apply Forall_cons; [| img_apply ent_ro])].
unfold shreg1, region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
img_change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_try (unfold kHighMemBeg in *; img_lia)|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
repeat img_apply Forall_cons; try img_apply Forall_nil.
all: first
[ img_apply chunk_ok_zero; intros i Hi; rewrite (YF8r.aview_byte H mem _ 0); [img_refl|];
rewrite <- (ra_granule_zero (aview tfxsegs H mem) d n (g0 + i) HRA ltac:(img_lia) Hd); unfold SB; f_equal; img_lia
| eapply (chunk_ok_val tfxsegs EE _ g0 _ 1 (SOff 34 0) b1); [img_try (cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (zside) | img_try (zside) |];
img_apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; img_lia ].
- img_apply pairwise_disjoint_of_extents. unfold stk, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by img_lia. unfold MS_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; img_lia.
- split; [|img_try (split; [img_exact I|])].
+ cbn [f_atoms atoms_ok facts1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E12, E32, E34, !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. repeat split; try img_lia; img_apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|img_try (split; [|img_exact I])].
* img_apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 32 g0 E32) by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 32 g0 2 E32) by img_lia. (subst g0 g1; cbv beta). img_lia.
Qed.
Lemma ent1_3 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 3 -> aview tfxsegs H mem (SB + g1) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfxsegs (Env [g0; g1; b1; q1; q2]) (ss1 3) (restrict H (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfxsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
pose proof (Env2 [g0; g1; b1; q1; q2]) as E2. pose proof (Env10 [g0; g1; b1; q1; q2]) as E10. pose proof (Env12 [g0; g1; b1; q1; q2]) as E12.
fold EE in E2, E10, E12.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod d 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound d 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (d + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hg1hi : g1 < 2 ^ 44) by img_lia.
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
rewrite restrict_mkst_fx. unfold ss1. unfold EE, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2])) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [img_try (img_apply ent_stk) | img_try (img_apply Forall_cons; [| img_apply ent_ro])].
unfold shreg1, region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
img_change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_try (unfold kHighMemBeg in *; img_lia)|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
repeat img_apply Forall_cons; try img_apply Forall_nil.
all: first
[ img_apply chunk_ok_zero; intros i Hi; rewrite (YF8r.aview_byte H mem _ 0); [img_refl|];
rewrite <- (ra_granule_zero (aview tfxsegs H mem) d n (g0 + i) HRA ltac:(img_lia) Hd); unfold SB; f_equal; img_lia
| eapply (chunk_ok_val tfxsegs EE _ g0 _ 1 (SOff 34 0) b1); [img_try (cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (zside) | img_try (zside) |];
img_apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; img_lia ].
- img_apply pairwise_disjoint_of_extents. unfold stk, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by img_lia. unfold MS_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; img_lia.
- split; [|img_try (split; [img_exact I|])].
+ cbn [f_atoms atoms_ok facts1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E12, E32, E34, !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. repeat split; try img_lia; img_apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|img_try (split; [|img_exact I])].
* img_apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 32 g0 E32) by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 32 g0 3 E32) by img_lia. (subst g0 g1; cbv beta). img_lia.
Qed.
Lemma ent1_4 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 4 -> aview tfxsegs H mem (SB + g1) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfxsegs (Env [g0; g1; b1; q1; q2]) (ss1 4) (restrict H (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfxsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
pose proof (Env2 [g0; g1; b1; q1; q2]) as E2. pose proof (Env10 [g0; g1; b1; q1; q2]) as E10. pose proof (Env12 [g0; g1; b1; q1; q2]) as E12.
fold EE in E2, E10, E12.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod d 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound d 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (d + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hg1hi : g1 < 2 ^ 44) by img_lia.
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
rewrite restrict_mkst_fx. unfold ss1. unfold EE, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2])) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [img_try (img_apply ent_stk) | img_try (img_apply Forall_cons; [| img_apply ent_ro])].
unfold shreg1, region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
img_change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_try (unfold kHighMemBeg in *; img_lia)|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
repeat img_apply Forall_cons; try img_apply Forall_nil.
all: first
[ img_apply chunk_ok_zero; intros i Hi; rewrite (YF8r.aview_byte H mem _ 0); [img_refl|];
rewrite <- (ra_granule_zero (aview tfxsegs H mem) d n (g0 + i) HRA ltac:(img_lia) Hd); unfold SB; f_equal; img_lia
| eapply (chunk_ok_val tfxsegs EE _ g0 _ 1 (SOff 34 0) b1); [img_try (cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (zside) | img_try (zside) |];
img_apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; img_lia ].
- img_apply pairwise_disjoint_of_extents. unfold stk, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by img_lia. unfold MS_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; img_lia.
- split; [|img_try (split; [img_exact I|])].
+ cbn [f_atoms atoms_ok facts1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E12, E32, E34, !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. repeat split; try img_lia; img_apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|img_try (split; [|img_exact I])].
* img_apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 32 g0 E32) by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 32 g0 4 E32) by img_lia. (subst g0 g1; cbv beta). img_lia.
Qed.
Lemma ent1_5 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 5 -> aview tfxsegs H mem (SB + g1) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfxsegs (Env [g0; g1; b1; q1; q2]) (ss1 5) (restrict H (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfxsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
pose proof (Env2 [g0; g1; b1; q1; q2]) as E2. pose proof (Env10 [g0; g1; b1; q1; q2]) as E10. pose proof (Env12 [g0; g1; b1; q1; q2]) as E12.
fold EE in E2, E10, E12.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod d 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound d 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (d + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hg1hi : g1 < 2 ^ 44) by img_lia.
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
rewrite restrict_mkst_fx. unfold ss1. unfold EE, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2])) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [img_try (img_apply ent_stk) | img_try (img_apply Forall_cons; [| img_apply ent_ro])].
unfold shreg1, region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
img_change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_try (unfold kHighMemBeg in *; img_lia)|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
repeat img_apply Forall_cons; try img_apply Forall_nil.
all: first
[ img_apply chunk_ok_zero; intros i Hi; rewrite (YF8r.aview_byte H mem _ 0); [img_refl|];
rewrite <- (ra_granule_zero (aview tfxsegs H mem) d n (g0 + i) HRA ltac:(img_lia) Hd); unfold SB; f_equal; img_lia
| eapply (chunk_ok_val tfxsegs EE _ g0 _ 1 (SOff 34 0) b1); [img_try (cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (zside) | img_try (zside) |];
img_apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; img_lia ].
- img_apply pairwise_disjoint_of_extents. unfold stk, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by img_lia. unfold MS_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; img_lia.
- split; [|img_try (split; [img_exact I|])].
+ cbn [f_atoms atoms_ok facts1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E12, E32, E34, !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. repeat split; try img_lia; img_apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|img_try (split; [|img_exact I])].
* img_apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 32 g0 E32) by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 32 g0 5 E32) by img_lia. (subst g0 g1; cbv beta). img_lia.
Qed.
Lemma ent1_6 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 6 -> aview tfxsegs H mem (SB + g1) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfxsegs (Env [g0; g1; b1; q1; q2]) (ss1 6) (restrict H (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfxsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
pose proof (Env2 [g0; g1; b1; q1; q2]) as E2. pose proof (Env10 [g0; g1; b1; q1; q2]) as E10. pose proof (Env12 [g0; g1; b1; q1; q2]) as E12.
fold EE in E2, E10, E12.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod d 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound d 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (d + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hg1hi : g1 < 2 ^ 44) by img_lia.
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
rewrite restrict_mkst_fx. unfold ss1. unfold EE, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2])) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [img_try (img_apply ent_stk) | img_try (img_apply Forall_cons; [| img_apply ent_ro])].
unfold shreg1, region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
img_change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_try (unfold kHighMemBeg in *; img_lia)|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
repeat img_apply Forall_cons; try img_apply Forall_nil.
all: first
[ img_apply chunk_ok_zero; intros i Hi; rewrite (YF8r.aview_byte H mem _ 0); [img_refl|];
rewrite <- (ra_granule_zero (aview tfxsegs H mem) d n (g0 + i) HRA ltac:(img_lia) Hd); unfold SB; f_equal; img_lia
| eapply (chunk_ok_val tfxsegs EE _ g0 _ 1 (SOff 34 0) b1); [img_try (cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (zside) | img_try (zside) |];
img_apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; img_lia ].
- img_apply pairwise_disjoint_of_extents. unfold stk, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by img_lia. unfold MS_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; img_lia.
- split; [|img_try (split; [img_exact I|])].
+ cbn [f_atoms atoms_ok facts1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E12, E32, E34, !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. repeat split; try img_lia; img_apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|img_try (split; [|img_exact I])].
* img_apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 32 g0 E32) by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 32 g0 6 E32) by img_lia. (subst g0 g1; cbv beta). img_lia.
Qed.
Lemma ent1_7 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 7 -> aview tfxsegs H mem (SB + g1) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfxsegs (Env [g0; g1; b1; q1; q2]) (ss1 7) (restrict H (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfxsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
pose proof (Env2 [g0; g1; b1; q1; q2]) as E2. pose proof (Env10 [g0; g1; b1; q1; q2]) as E10. pose proof (Env12 [g0; g1; b1; q1; q2]) as E12.
fold EE in E2, E10, E12.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod d 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound d 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (d + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hg1hi : g1 < 2 ^ 44) by img_lia.
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
rewrite restrict_mkst_fx. unfold ss1. unfold EE, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2])) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [img_try (img_apply ent_stk) | img_try (img_apply Forall_cons; [| img_apply ent_ro])].
unfold shreg1, region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
img_change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_try (unfold kHighMemBeg in *; img_lia)|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
repeat img_apply Forall_cons; try img_apply Forall_nil.
all: first
[ img_apply chunk_ok_zero; intros i Hi; rewrite (YF8r.aview_byte H mem _ 0); [img_refl|];
rewrite <- (ra_granule_zero (aview tfxsegs H mem) d n (g0 + i) HRA ltac:(img_lia) Hd); unfold SB; f_equal; img_lia
| eapply (chunk_ok_val tfxsegs EE _ g0 _ 1 (SOff 34 0) b1); [img_try (cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (zside) | img_try (zside) |];
img_apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; img_lia ].
- img_apply pairwise_disjoint_of_extents. unfold stk, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by img_lia. unfold MS_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; img_lia.
- split; [|img_try (split; [img_exact I|])].
+ cbn [f_atoms atoms_ok facts1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E12, E32, E34, !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. repeat split; try img_lia; img_apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|img_try (split; [|img_exact I])].
* img_apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 32 g0 E32) by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 32 g0 7 E32) by img_lia. (subst g0 g1; cbv beta). img_lia.
Qed.
Lemma ent1_8 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 8 -> aview tfxsegs H mem (SB + g1) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfxsegs (Env [g0; g1; b1; q1; q2]) (ss1 8) (restrict H (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfxsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
pose proof (Env2 [g0; g1; b1; q1; q2]) as E2. pose proof (Env10 [g0; g1; b1; q1; q2]) as E10. pose proof (Env12 [g0; g1; b1; q1; q2]) as E12.
fold EE in E2, E10, E12.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod d 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound d 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (d + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hg1hi : g1 < 2 ^ 44) by img_lia.
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
rewrite restrict_mkst_fx. unfold ss1. unfold EE, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2])) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [img_try (img_apply ent_stk) | img_try (img_apply Forall_cons; [| img_apply ent_ro])].
unfold shreg1, region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
img_change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_try (unfold kHighMemBeg in *; img_lia)|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
repeat img_apply Forall_cons; try img_apply Forall_nil.
all: first
[ img_apply chunk_ok_zero; intros i Hi; rewrite (YF8r.aview_byte H mem _ 0); [img_refl|];
rewrite <- (ra_granule_zero (aview tfxsegs H mem) d n (g0 + i) HRA ltac:(img_lia) Hd); unfold SB; f_equal; img_lia
| eapply (chunk_ok_val tfxsegs EE _ g0 _ 1 (SOff 34 0) b1); [img_try (cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (zside) | img_try (zside) |];
img_apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; img_lia ].
- img_apply pairwise_disjoint_of_extents. unfold stk, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by img_lia. unfold MS_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; img_lia.
- split; [|img_try (split; [img_exact I|])].
+ cbn [f_atoms atoms_ok facts1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E12, E32, E34, !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. repeat split; try img_lia; img_apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|img_try (split; [|img_exact I])].
* img_apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 32 g0 E32) by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 32 g0 8 E32) by img_lia. (subst g0 g1; cbv beta). img_lia.
Qed.
End h.
End f.
