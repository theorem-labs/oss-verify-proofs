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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YE1j YF8r YE04 YE0v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section e. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition RC_ENTRY {imgk : img} : Z := (0x44f80 + D_2c4).
Definition RC_END {imgk : img} : Z := (0x44ee0 + D_2c4).
Definition RC_STK : Z := 64.
Definition RC_SCR : Z := 72.
Lemma br_cls64_small : forall E (pn : nat) n, ew E pn = Z_to_bv 64 n -> 1 <= n <= 64 ->
branch_taken BC_LTU (sv_denot E (SOff pn (-65))) (sv_denot E (SLit 18446744073709551552)) = false.
Proof.
intros E pn n Hn Rn. rewrite branch_ltu_U, U_SLit, U_SOff, Hn, unsigned_lit_small by img_lia.
unfold zcanon, M64. img_change (18446744073709551552 mod 2 ^ 64) with (2 ^ 64 - 64).
replace ((n + -65) mod 2 ^ 64) with (n - 65 + 2 ^ 64).
2:{ replace (n + -65) with ((n - 65 + 2 ^ 64) + (-1) * 2 ^ 64) by img_lia. rewrite Z.mod_add by img_lia. symmetry. img_apply Z.mod_small. img_lia. }
img_apply Z.ltb_ge. img_lia.
Qed.
Lemma br_cls64_big : forall E (pn : nat) n, ew E pn = Z_to_bv 64 n -> 65 <= n < 2 ^ 63 ->
branch_taken BC_LTU (sv_denot E (SOff pn (-65))) (sv_denot E (SLit 18446744073709551552)) = true.
Proof.
intros E pn n Hn Rn. rewrite branch_ltu_U, U_SLit, U_SOff, Hn, unsigned_lit_small by img_lia.
unfold zcanon, M64. img_change (18446744073709551552 mod 2 ^ 64) with (2 ^ 64 - 64). rewrite Z.mod_small by img_lia.
img_apply Z.ltb_lt. img_lia.
Qed.
Lemma br_novf_geu : forall E (pa pn : nat) d n, ew E pa = Z_to_bv 64 d -> ew E pn = Z_to_bv 64 n -> 0 <= d <= 2 ^ 47 -> 0 <= n < 2 ^ 63 ->
branch_taken BC_GEU (sv_denot E (SAlu ALU_XOR (SOff pa 0) (SLit (-1)))) (sv_denot E (SOff pn 0)) = true.
Proof.
intros E pa pn d n Hd Hn Rd Rn. rewrite branch_geu_U, U_not, (U_atom E pa d Hd), (U_atom E pn n Hn) by img_lia.
cbn [negb]. rewrite (proj2 (Z.ltb_ge _ _)) by img_lia. img_refl.
Qed.
Lemma br_cls65_small : forall E (pn : nat) n, ew E pn = Z_to_bv 64 n -> 1 <= n <= 64 ->
branch_taken BC_GEU (sv_denot E (SLit 18446744073709551551)) (sv_denot E (SOff pn (-65))) = false.
Proof.
intros E pn n Hn Rn. rewrite branch_geu_U, U_SLit, U_SOff, Hn, unsigned_lit_small by img_lia.
unfold zcanon, M64. img_change (18446744073709551551 mod 2 ^ 64) with (2 ^ 64 - 65).
replace ((n + -65) mod 2 ^ 64) with (n - 65 + 2 ^ 64).
2:{ replace (n + -65) with ((n - 65 + 2 ^ 64) + (-1) * 2 ^ 64) by img_lia. rewrite Z.mod_add by img_lia. symmetry. img_apply Z.mod_small. img_lia. }
cbn [negb]. replace (2 ^ 64 - 65 <? n - 65 + 2 ^ 64) with true by (img_try (symmetry; img_apply Z.ltb_lt; img_lia)). img_refl.
Qed.
Lemma br_geu_false : forall E (pa pb : nat) a b, ew E pa = Z_to_bv 64 a -> ew E pb = Z_to_bv 64 b -> 0 <= a < b -> b < 2 ^ 64 ->
branch_taken BC_GEU (sv_denot E (SOff pa 0)) (sv_denot E (SOff pb 0)) = false.
Proof.
intros E pa pb a b Ha Hb Hab Hb64. rewrite branch_geu_U, (U_atom E pa a Ha), (U_atom E pb b Hb) by img_lia.
cbn [negb]. rewrite (proj2 (Z.ltb_lt _ _)) by img_lia. img_refl.
Qed.
Lemma br_hull_eq : forall E (p1 p2 : nat) q1 q2, ew E p1 = Z_to_bv 64 q1 -> ew E p2 = Z_to_bv 64 q2 -> 0 <= q1 < 2 ^ 64 -> 0 <= q2 < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SAlu ALU_OR (SOff p2 0) (SOff p1 0))) (sv_denot E (SLit 0)) = (Z.lor q2 q1 =? 0).
Proof.
intros E p1 p2 q1 q2 H1 H2 R1 R2. rewrite <- (negb_involutive (branch_taken BC_EQ _ _)).
change (negb (branch_taken BC_EQ ?a ?b)) with (branch_taken BC_NE a b). rewrite (br_hull E p1 p2 q1 q2 H1 H2 R1 R2). img_apply negb_involutive.
Qed.
Definition shreg1 (t : Z) : YQ0b.region :=
YQ0b.mkRegion (Some 32%nat) SB (SB + t + 1) SB SB
((if 0 <? t then [YQ0b.mkChunk SB (CZero t)] else []) ++ [YQ0b.mkChunk (SB + t) (CVal 1 (SOff 34 0))]).
Definition shregs2 : smem :=
[ YQ0b.mkRegion (Some 32%nat) SB (SB + 1) SB SB [YQ0b.mkChunk SB (CZero 1)];
YQ0b.mkRegion (Some 33%nat) SB (SB + 1) SB SB [YQ0b.mkChunk SB (CVal 1 (SOff 34 0))] ].
Definition aliases1 (t : Z) : list (sv * sv) :=
[ (SAlu ALU_SRL (SOff 22 0) (SLit 3), SOff 32 0);
(SAlu ALU_SRL (SAlu ALU_ADD (SOff 22 (-1)) (SOff 41 0)) (SLit 3), SOff 32 t) ].
Definition aliases2 : list (sv * sv) :=
[ (SAlu ALU_SRL (SOff 22 0) (SLit 3), SOff 32 0);
(SAlu ALU_SRL (SAlu ALU_ADD (SOff 22 (-1)) (SOff 41 0)) (SLit 3), SOff 33 0);
(SAlu ALU_AND (SOff 22 7) (SLit (-8)), SOff 37 0);
(SAlu ALU_AND (SAlu ALU_ADD (SOff 22 0) (SOff 41 0)) (SLit (-8)), SOff 38 0);
(SAlu ALU_SRL (SOff 37 0) (SLit 3), SOff 39 0);
(SAlu ALU_SRL (SOff 38 0) (SLit 3), SOff 40 0) ].
Definition stkR : YQ0b.region := YQ0b.mkRegion (Some 2%nat) (- RC_STK) 0 (- RC_STK) 0 [].
Definition factsR1 : list (nat * afact) :=
[(2%nat, mkAF (2^44) (2^47) 4); (22%nat, mkAF 0 (2^47) 0); (41%nat, mkAF 1 64 0); (32%nat, mkAF 0 (2^44) 0); (34%nat, mkAF 0 7 0)].
Definition factsR2L : list (nat * afact) :=
[(2%nat, mkAF (2^44) (2^47) 4); (22%nat, mkAF 0 0x7fff7fbe 0); (41%nat, mkAF 65 (2^32 - 1) 0);
(32%nat, mkAF 0 (2^44) 0); (33%nat, mkAF 0 (2^44) 0); (34%nat, mkAF 0 7 0);
(37%nat, mkAF 0 0x7fff7fc8 3); (38%nat, mkAF 0 0x7fff7fff 3); (39%nat, mkAF 0 (2^44) 0); (40%nat, mkAF 0 (2^44) 0)].
Definition factsR2H : list (nat * afact) :=
[(2%nat, mkAF (2^44) (2^47) 4); (22%nat, mkAF 0x10007fff8000 (2^47 - 66) 0); (41%nat, mkAF 65 (2^32 - 1) 0);
(32%nat, mkAF 0 (2^44) 0); (33%nat, mkAF 0 (2^44) 0); (34%nat, mkAF 0 7 0);
(37%nat, mkAF 0x10007fff8000 (2^47 - 1) 3); (38%nat, mkAF 0x10007fff8000 (2^47 - 1) 3); (39%nat, mkAF 0 (2^44) 0); (40%nat, mkAF 0 (2^44) 0)].
Definition regsP : list sv := Eval vm_compute in (firstn 10 sr_atoms ++ [SOff 41 (-1)] ++ skipn 11 sr_atoms).
Definition ssR1 {imgk : img} (t : Z) : sstate := mkSS RC_ENTRY regsP (stkR :: shreg1 t :: map ro_region icpt_rodata) None (mkFacts factsR1 [] (aliases1 t)).
Definition ssR2L {imgk : img} : sstate := mkSS RC_ENTRY regsP (stkR :: shregs2 ++ map ro_region icpt_rodata) None (mkFacts factsR2L [] aliases2).
Definition ssR2H {imgk : img} : sstate := mkSS RC_ENTRY regsP (stkR :: shregs2 ++ map ro_region icpt_rodata) None (mkFacts factsR2H [] aliases2).
Definition RUN {imgk : img} (s : sstate) := sym_runN tfxsegs tbl_icpt FUEL s.
Definition RUNTO {imgk : img} (s : sstate) := sym_run_toN tfxsegs tbl_icpt FUEL RC_END s.
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition AC (s : sstate) (c : branch_cond) (a b : sv) : sstate := YQ09.add_cond s (mkAC c a b).
Definition r1_0_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((ssR1 0)))).
Definition r1_0_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (ssR1 0))))).
Lemma r_r1_0_0 {imgk : img} : RUN (ssR1 0) = (r1_0_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 22 0) (SLit (-1))) (SOff 41 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_0_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_0_e0 BC_GEU (RG r1_0_e0 10) (RG r1_0_e0 23))))).
Definition r1_0_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r1_0_e0 BC_GEU (RG r1_0_e0 10) (RG r1_0_e0 23)))))).
Lemma r_r1_0_1 {imgk : img} : RUN (AC r1_0_e0 BC_GEU (RG r1_0_e0 10) (RG r1_0_e0 23)) = (r1_0_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 41 (-65)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_0_s2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_0_e1 BC_LTU (RG r1_0_e1 11) (RG r1_0_e1 10))))).
Definition r1_0_e2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r1_0_e1 BC_LTU (RG r1_0_e1 11) (RG r1_0_e1 10)))))).
Lemma r_r1_0_2 {imgk : img} : RUN (AC r1_0_e1 BC_LTU (RG r1_0_e1 11) (RG r1_0_e1 10)) = (r1_0_e2, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_0_s3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((set_regs_pc (set_regs_pc r1_0_e2 [((13%bv : bv 5), SOff 35 0)] (0x44fc8 + D_2c4)) [((14%bv : bv 5), SOff 36 0)] (0x44fcc + D_2c4))))).
Definition r1_0_e3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (set_regs_pc (set_regs_pc r1_0_e2 [((13%bv : bv 5), SOff 35 0)] (0x44fc8 + D_2c4)) [((14%bv : bv 5), SOff 36 0)] (0x44fcc + D_2c4)))))).
Lemma r_r1_0_3 {imgk : img} : RUN (set_regs_pc (set_regs_pc r1_0_e2 [((13%bv : bv 5), SOff 35 0)] (0x44fc8 + D_2c4)) [((14%bv : bv 5), SOff 36 0)] (0x44fcc + D_2c4)) = (r1_0_e3, RS_stopped (SR_branch BC_EQ (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_0z_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_0_e3 BC_EQ (RG r1_0_e3 13) (SLit 0))))).
Definition r1_0z_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUNTO (AC r1_0_e3 BC_EQ (RG r1_0_e3 13) (SLit 0)))))).
Lemma r_r1_0z_0 {imgk : img} : RUNTO (AC r1_0_e3 BC_EQ (RG r1_0_e3 13) (SLit 0)) = (r1_0z_e0, RS_running). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_0n_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_0_e3 BC_NE (RG r1_0_e3 13) (SLit 0))))).
Definition r1_0n_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r1_0_e3 BC_NE (RG r1_0_e3 13) (SLit 0)))))).
Lemma r_r1_0n_0 {imgk : img} : RUN (AC r1_0_e3 BC_NE (RG r1_0_e3 13) (SLit 0)) = (r1_0n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 0%nat 22 41 34) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_0n_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_0n_e0 BC_EQ (RG r1_0n_e0 10) (SLit 0))))).
Definition r1_0n_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUNTO (AC r1_0n_e0 BC_EQ (RG r1_0n_e0 10) (SLit 0)))))).
Lemma r_r1_0n_1 {imgk : img} : RUNTO (AC r1_0n_e0 BC_EQ (RG r1_0n_e0 10) (SLit 0)) = (r1_0n_e1, RS_running). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_1_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((ssR1 1)))).
Definition r1_1_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (ssR1 1))))).
Lemma r_r1_1_0 {imgk : img} : RUN (ssR1 1) = (r1_1_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 22 0) (SLit (-1))) (SOff 41 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_1_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_1_e0 BC_GEU (RG r1_1_e0 10) (RG r1_1_e0 23))))).
Definition r1_1_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r1_1_e0 BC_GEU (RG r1_1_e0 10) (RG r1_1_e0 23)))))).
Lemma r_r1_1_1 {imgk : img} : RUN (AC r1_1_e0 BC_GEU (RG r1_1_e0 10) (RG r1_1_e0 23)) = (r1_1_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 41 (-65)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_1_s2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_1_e1 BC_LTU (RG r1_1_e1 11) (RG r1_1_e1 10))))).
Definition r1_1_e2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r1_1_e1 BC_LTU (RG r1_1_e1 11) (RG r1_1_e1 10)))))).
Lemma r_r1_1_2 {imgk : img} : RUN (AC r1_1_e1 BC_LTU (RG r1_1_e1 11) (RG r1_1_e1 10)) = (r1_1_e2, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_1_s3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((set_regs_pc (set_regs_pc r1_1_e2 [((13%bv : bv 5), SOff 35 0)] (0x44fc8 + D_2c4)) [((14%bv : bv 5), SOff 36 0)] (0x44fcc + D_2c4))))).
Definition r1_1_e3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (set_regs_pc (set_regs_pc r1_1_e2 [((13%bv : bv 5), SOff 35 0)] (0x44fc8 + D_2c4)) [((14%bv : bv 5), SOff 36 0)] (0x44fcc + D_2c4)))))).
Lemma r_r1_1_3 {imgk : img} : RUN (set_regs_pc (set_regs_pc r1_1_e2 [((13%bv : bv 5), SOff 35 0)] (0x44fc8 + D_2c4)) [((14%bv : bv 5), SOff 36 0)] (0x44fcc + D_2c4)) = (r1_1_e3, RS_stopped (SR_branch BC_EQ (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_1z_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_1_e3 BC_EQ (RG r1_1_e3 13) (SLit 0))))).
Definition r1_1z_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUNTO (AC r1_1_e3 BC_EQ (RG r1_1_e3 13) (SLit 0)))))).
Lemma r_r1_1z_0 {imgk : img} : RUNTO (AC r1_1_e3 BC_EQ (RG r1_1_e3 13) (SLit 0)) = (r1_1z_e0, RS_running). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_1n_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_1_e3 BC_NE (RG r1_1_e3 13) (SLit 0))))).
Definition r1_1n_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r1_1_e3 BC_NE (RG r1_1_e3 13) (SLit 0)))))).
Lemma r_r1_1n_0 {imgk : img} : RUN (AC r1_1_e3 BC_NE (RG r1_1_e3 13) (SLit 0)) = (r1_1n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 1%nat 22 41 34) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_1n_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_1n_e0 BC_EQ (RG r1_1n_e0 10) (SLit 0))))).
Definition r1_1n_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUNTO (AC r1_1n_e0 BC_EQ (RG r1_1n_e0 10) (SLit 0)))))).
Lemma r_r1_1n_1 {imgk : img} : RUNTO (AC r1_1n_e0 BC_EQ (RG r1_1n_e0 10) (SLit 0)) = (r1_1n_e1, RS_running). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_2_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((ssR1 2)))).
Definition r1_2_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (ssR1 2))))).
Lemma r_r1_2_0 {imgk : img} : RUN (ssR1 2) = (r1_2_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 22 0) (SLit (-1))) (SOff 41 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_2_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_2_e0 BC_GEU (RG r1_2_e0 10) (RG r1_2_e0 23))))).
Definition r1_2_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r1_2_e0 BC_GEU (RG r1_2_e0 10) (RG r1_2_e0 23)))))).
Lemma r_r1_2_1 {imgk : img} : RUN (AC r1_2_e0 BC_GEU (RG r1_2_e0 10) (RG r1_2_e0 23)) = (r1_2_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 41 (-65)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_2_s2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_2_e1 BC_LTU (RG r1_2_e1 11) (RG r1_2_e1 10))))).
Definition r1_2_e2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r1_2_e1 BC_LTU (RG r1_2_e1 11) (RG r1_2_e1 10)))))).
Lemma r_r1_2_2 {imgk : img} : RUN (AC r1_2_e1 BC_LTU (RG r1_2_e1 11) (RG r1_2_e1 10)) = (r1_2_e2, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_2_s3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((set_regs_pc (set_regs_pc r1_2_e2 [((13%bv : bv 5), SOff 35 0)] (0x44fc8 + D_2c4)) [((14%bv : bv 5), SOff 36 0)] (0x44fcc + D_2c4))))).
Definition r1_2_e3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (set_regs_pc (set_regs_pc r1_2_e2 [((13%bv : bv 5), SOff 35 0)] (0x44fc8 + D_2c4)) [((14%bv : bv 5), SOff 36 0)] (0x44fcc + D_2c4)))))).
Lemma r_r1_2_3 {imgk : img} : RUN (set_regs_pc (set_regs_pc r1_2_e2 [((13%bv : bv 5), SOff 35 0)] (0x44fc8 + D_2c4)) [((14%bv : bv 5), SOff 36 0)] (0x44fcc + D_2c4)) = (r1_2_e3, RS_stopped (SR_branch BC_EQ (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_2z_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_2_e3 BC_EQ (RG r1_2_e3 13) (SLit 0))))).
Definition r1_2z_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUNTO (AC r1_2_e3 BC_EQ (RG r1_2_e3 13) (SLit 0)))))).
Lemma r_r1_2z_0 {imgk : img} : RUNTO (AC r1_2_e3 BC_EQ (RG r1_2_e3 13) (SLit 0)) = (r1_2z_e0, RS_running). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_2n_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_2_e3 BC_NE (RG r1_2_e3 13) (SLit 0))))).
Definition r1_2n_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r1_2_e3 BC_NE (RG r1_2_e3 13) (SLit 0)))))).
Lemma r_r1_2n_0 {imgk : img} : RUN (AC r1_2_e3 BC_NE (RG r1_2_e3 13) (SLit 0)) = (r1_2n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 2%nat 22 41 34) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_2n_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_2n_e0 BC_EQ (RG r1_2n_e0 10) (SLit 0))))).
Definition r1_2n_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUNTO (AC r1_2n_e0 BC_EQ (RG r1_2n_e0 10) (SLit 0)))))).
Lemma r_r1_2n_1 {imgk : img} : RUNTO (AC r1_2n_e0 BC_EQ (RG r1_2n_e0 10) (SLit 0)) = (r1_2n_e1, RS_running). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_3_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((ssR1 3)))).
Definition r1_3_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (ssR1 3))))).
Lemma r_r1_3_0 {imgk : img} : RUN (ssR1 3) = (r1_3_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 22 0) (SLit (-1))) (SOff 41 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_3_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_3_e0 BC_GEU (RG r1_3_e0 10) (RG r1_3_e0 23))))).
Definition r1_3_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r1_3_e0 BC_GEU (RG r1_3_e0 10) (RG r1_3_e0 23)))))).
Lemma r_r1_3_1 {imgk : img} : RUN (AC r1_3_e0 BC_GEU (RG r1_3_e0 10) (RG r1_3_e0 23)) = (r1_3_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 41 (-65)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_3_s2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_3_e1 BC_LTU (RG r1_3_e1 11) (RG r1_3_e1 10))))).
Definition r1_3_e2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r1_3_e1 BC_LTU (RG r1_3_e1 11) (RG r1_3_e1 10)))))).
Lemma r_r1_3_2 {imgk : img} : RUN (AC r1_3_e1 BC_LTU (RG r1_3_e1 11) (RG r1_3_e1 10)) = (r1_3_e2, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_3_s3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((set_regs_pc (set_regs_pc r1_3_e2 [((13%bv : bv 5), SOff 35 0)] (0x44fc8 + D_2c4)) [((14%bv : bv 5), SOff 36 0)] (0x44fcc + D_2c4))))).
Definition r1_3_e3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (set_regs_pc (set_regs_pc r1_3_e2 [((13%bv : bv 5), SOff 35 0)] (0x44fc8 + D_2c4)) [((14%bv : bv 5), SOff 36 0)] (0x44fcc + D_2c4)))))).
Lemma r_r1_3_3 {imgk : img} : RUN (set_regs_pc (set_regs_pc r1_3_e2 [((13%bv : bv 5), SOff 35 0)] (0x44fc8 + D_2c4)) [((14%bv : bv 5), SOff 36 0)] (0x44fcc + D_2c4)) = (r1_3_e3, RS_stopped (SR_branch BC_EQ (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_3z_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_3_e3 BC_EQ (RG r1_3_e3 13) (SLit 0))))).
Definition r1_3z_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUNTO (AC r1_3_e3 BC_EQ (RG r1_3_e3 13) (SLit 0)))))).
Lemma r_r1_3z_0 {imgk : img} : RUNTO (AC r1_3_e3 BC_EQ (RG r1_3_e3 13) (SLit 0)) = (r1_3z_e0, RS_running). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_3n_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_3_e3 BC_NE (RG r1_3_e3 13) (SLit 0))))).
Definition r1_3n_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r1_3_e3 BC_NE (RG r1_3_e3 13) (SLit 0)))))).
Lemma r_r1_3n_0 {imgk : img} : RUN (AC r1_3_e3 BC_NE (RG r1_3_e3 13) (SLit 0)) = (r1_3n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 3%nat 22 41 34) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_3n_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_3n_e0 BC_EQ (RG r1_3n_e0 10) (SLit 0))))).
Definition r1_3n_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUNTO (AC r1_3n_e0 BC_EQ (RG r1_3n_e0 10) (SLit 0)))))).
Lemma r_r1_3n_1 {imgk : img} : RUNTO (AC r1_3n_e0 BC_EQ (RG r1_3n_e0 10) (SLit 0)) = (r1_3n_e1, RS_running). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_4_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((ssR1 4)))).
Definition r1_4_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (ssR1 4))))).
Lemma r_r1_4_0 {imgk : img} : RUN (ssR1 4) = (r1_4_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 22 0) (SLit (-1))) (SOff 41 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_4_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_4_e0 BC_GEU (RG r1_4_e0 10) (RG r1_4_e0 23))))).
Definition r1_4_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r1_4_e0 BC_GEU (RG r1_4_e0 10) (RG r1_4_e0 23)))))).
Lemma r_r1_4_1 {imgk : img} : RUN (AC r1_4_e0 BC_GEU (RG r1_4_e0 10) (RG r1_4_e0 23)) = (r1_4_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 41 (-65)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_4_s2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_4_e1 BC_LTU (RG r1_4_e1 11) (RG r1_4_e1 10))))).
Definition r1_4_e2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r1_4_e1 BC_LTU (RG r1_4_e1 11) (RG r1_4_e1 10)))))).
Lemma r_r1_4_2 {imgk : img} : RUN (AC r1_4_e1 BC_LTU (RG r1_4_e1 11) (RG r1_4_e1 10)) = (r1_4_e2, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_4_s3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((set_regs_pc (set_regs_pc r1_4_e2 [((13%bv : bv 5), SOff 35 0)] (0x44fc8 + D_2c4)) [((14%bv : bv 5), SOff 36 0)] (0x44fcc + D_2c4))))).
Definition r1_4_e3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (set_regs_pc (set_regs_pc r1_4_e2 [((13%bv : bv 5), SOff 35 0)] (0x44fc8 + D_2c4)) [((14%bv : bv 5), SOff 36 0)] (0x44fcc + D_2c4)))))).
Lemma r_r1_4_3 {imgk : img} : RUN (set_regs_pc (set_regs_pc r1_4_e2 [((13%bv : bv 5), SOff 35 0)] (0x44fc8 + D_2c4)) [((14%bv : bv 5), SOff 36 0)] (0x44fcc + D_2c4)) = (r1_4_e3, RS_stopped (SR_branch BC_EQ (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_4z_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_4_e3 BC_EQ (RG r1_4_e3 13) (SLit 0))))).
Definition r1_4z_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUNTO (AC r1_4_e3 BC_EQ (RG r1_4_e3 13) (SLit 0)))))).
Lemma r_r1_4z_0 {imgk : img} : RUNTO (AC r1_4_e3 BC_EQ (RG r1_4_e3 13) (SLit 0)) = (r1_4z_e0, RS_running). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_4n_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_4_e3 BC_NE (RG r1_4_e3 13) (SLit 0))))).
Definition r1_4n_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r1_4_e3 BC_NE (RG r1_4_e3 13) (SLit 0)))))).
Lemma r_r1_4n_0 {imgk : img} : RUN (AC r1_4_e3 BC_NE (RG r1_4_e3 13) (SLit 0)) = (r1_4n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 4%nat 22 41 34) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_4n_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_4n_e0 BC_EQ (RG r1_4n_e0 10) (SLit 0))))).
Definition r1_4n_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUNTO (AC r1_4n_e0 BC_EQ (RG r1_4n_e0 10) (SLit 0)))))).
Lemma r_r1_4n_1 {imgk : img} : RUNTO (AC r1_4n_e0 BC_EQ (RG r1_4n_e0 10) (SLit 0)) = (r1_4n_e1, RS_running). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_5_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((ssR1 5)))).
Definition r1_5_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (ssR1 5))))).
Lemma r_r1_5_0 {imgk : img} : RUN (ssR1 5) = (r1_5_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 22 0) (SLit (-1))) (SOff 41 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_5_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_5_e0 BC_GEU (RG r1_5_e0 10) (RG r1_5_e0 23))))).
Definition r1_5_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r1_5_e0 BC_GEU (RG r1_5_e0 10) (RG r1_5_e0 23)))))).
Lemma r_r1_5_1 {imgk : img} : RUN (AC r1_5_e0 BC_GEU (RG r1_5_e0 10) (RG r1_5_e0 23)) = (r1_5_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 41 (-65)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_5_s2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_5_e1 BC_LTU (RG r1_5_e1 11) (RG r1_5_e1 10))))).
Definition r1_5_e2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r1_5_e1 BC_LTU (RG r1_5_e1 11) (RG r1_5_e1 10)))))).
Lemma r_r1_5_2 {imgk : img} : RUN (AC r1_5_e1 BC_LTU (RG r1_5_e1 11) (RG r1_5_e1 10)) = (r1_5_e2, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_5_s3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((set_regs_pc (set_regs_pc r1_5_e2 [((13%bv : bv 5), SOff 35 0)] (0x44fc8 + D_2c4)) [((14%bv : bv 5), SOff 36 0)] (0x44fcc + D_2c4))))).
Definition r1_5_e3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (set_regs_pc (set_regs_pc r1_5_e2 [((13%bv : bv 5), SOff 35 0)] (0x44fc8 + D_2c4)) [((14%bv : bv 5), SOff 36 0)] (0x44fcc + D_2c4)))))).
Lemma r_r1_5_3 {imgk : img} : RUN (set_regs_pc (set_regs_pc r1_5_e2 [((13%bv : bv 5), SOff 35 0)] (0x44fc8 + D_2c4)) [((14%bv : bv 5), SOff 36 0)] (0x44fcc + D_2c4)) = (r1_5_e3, RS_stopped (SR_branch BC_EQ (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_5z_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_5_e3 BC_EQ (RG r1_5_e3 13) (SLit 0))))).
Definition r1_5z_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUNTO (AC r1_5_e3 BC_EQ (RG r1_5_e3 13) (SLit 0)))))).
Lemma r_r1_5z_0 {imgk : img} : RUNTO (AC r1_5_e3 BC_EQ (RG r1_5_e3 13) (SLit 0)) = (r1_5z_e0, RS_running). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_5n_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_5_e3 BC_NE (RG r1_5_e3 13) (SLit 0))))).
Definition r1_5n_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r1_5_e3 BC_NE (RG r1_5_e3 13) (SLit 0)))))).
Lemma r_r1_5n_0 {imgk : img} : RUN (AC r1_5_e3 BC_NE (RG r1_5_e3 13) (SLit 0)) = (r1_5n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 5%nat 22 41 34) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_5n_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_5n_e0 BC_EQ (RG r1_5n_e0 10) (SLit 0))))).
Definition r1_5n_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUNTO (AC r1_5n_e0 BC_EQ (RG r1_5n_e0 10) (SLit 0)))))).
Lemma r_r1_5n_1 {imgk : img} : RUNTO (AC r1_5n_e0 BC_EQ (RG r1_5n_e0 10) (SLit 0)) = (r1_5n_e1, RS_running). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_6_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((ssR1 6)))).
Definition r1_6_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (ssR1 6))))).
Lemma r_r1_6_0 {imgk : img} : RUN (ssR1 6) = (r1_6_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 22 0) (SLit (-1))) (SOff 41 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_6_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_6_e0 BC_GEU (RG r1_6_e0 10) (RG r1_6_e0 23))))).
Definition r1_6_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r1_6_e0 BC_GEU (RG r1_6_e0 10) (RG r1_6_e0 23)))))).
Lemma r_r1_6_1 {imgk : img} : RUN (AC r1_6_e0 BC_GEU (RG r1_6_e0 10) (RG r1_6_e0 23)) = (r1_6_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 41 (-65)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_6_s2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_6_e1 BC_LTU (RG r1_6_e1 11) (RG r1_6_e1 10))))).
Definition r1_6_e2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r1_6_e1 BC_LTU (RG r1_6_e1 11) (RG r1_6_e1 10)))))).
Lemma r_r1_6_2 {imgk : img} : RUN (AC r1_6_e1 BC_LTU (RG r1_6_e1 11) (RG r1_6_e1 10)) = (r1_6_e2, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_6_s3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((set_regs_pc (set_regs_pc r1_6_e2 [((13%bv : bv 5), SOff 35 0)] (0x44fc8 + D_2c4)) [((14%bv : bv 5), SOff 36 0)] (0x44fcc + D_2c4))))).
Definition r1_6_e3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (set_regs_pc (set_regs_pc r1_6_e2 [((13%bv : bv 5), SOff 35 0)] (0x44fc8 + D_2c4)) [((14%bv : bv 5), SOff 36 0)] (0x44fcc + D_2c4)))))).
Lemma r_r1_6_3 {imgk : img} : RUN (set_regs_pc (set_regs_pc r1_6_e2 [((13%bv : bv 5), SOff 35 0)] (0x44fc8 + D_2c4)) [((14%bv : bv 5), SOff 36 0)] (0x44fcc + D_2c4)) = (r1_6_e3, RS_stopped (SR_branch BC_EQ (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_6z_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_6_e3 BC_EQ (RG r1_6_e3 13) (SLit 0))))).
Definition r1_6z_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUNTO (AC r1_6_e3 BC_EQ (RG r1_6_e3 13) (SLit 0)))))).
Lemma r_r1_6z_0 {imgk : img} : RUNTO (AC r1_6_e3 BC_EQ (RG r1_6_e3 13) (SLit 0)) = (r1_6z_e0, RS_running). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_6n_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_6_e3 BC_NE (RG r1_6_e3 13) (SLit 0))))).
Definition r1_6n_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r1_6_e3 BC_NE (RG r1_6_e3 13) (SLit 0)))))).
Lemma r_r1_6n_0 {imgk : img} : RUN (AC r1_6_e3 BC_NE (RG r1_6_e3 13) (SLit 0)) = (r1_6n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 6%nat 22 41 34) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_6n_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_6n_e0 BC_EQ (RG r1_6n_e0 10) (SLit 0))))).
Definition r1_6n_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUNTO (AC r1_6n_e0 BC_EQ (RG r1_6n_e0 10) (SLit 0)))))).
Lemma r_r1_6n_1 {imgk : img} : RUNTO (AC r1_6n_e0 BC_EQ (RG r1_6n_e0 10) (SLit 0)) = (r1_6n_e1, RS_running). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_7_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((ssR1 7)))).
Definition r1_7_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (ssR1 7))))).
Lemma r_r1_7_0 {imgk : img} : RUN (ssR1 7) = (r1_7_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 22 0) (SLit (-1))) (SOff 41 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_7_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_7_e0 BC_GEU (RG r1_7_e0 10) (RG r1_7_e0 23))))).
Definition r1_7_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r1_7_e0 BC_GEU (RG r1_7_e0 10) (RG r1_7_e0 23)))))).
Lemma r_r1_7_1 {imgk : img} : RUN (AC r1_7_e0 BC_GEU (RG r1_7_e0 10) (RG r1_7_e0 23)) = (r1_7_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 41 (-65)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_7_s2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_7_e1 BC_LTU (RG r1_7_e1 11) (RG r1_7_e1 10))))).
Definition r1_7_e2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r1_7_e1 BC_LTU (RG r1_7_e1 11) (RG r1_7_e1 10)))))).
Lemma r_r1_7_2 {imgk : img} : RUN (AC r1_7_e1 BC_LTU (RG r1_7_e1 11) (RG r1_7_e1 10)) = (r1_7_e2, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_7_s3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((set_regs_pc (set_regs_pc r1_7_e2 [((13%bv : bv 5), SOff 35 0)] (0x44fc8 + D_2c4)) [((14%bv : bv 5), SOff 36 0)] (0x44fcc + D_2c4))))).
Definition r1_7_e3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (set_regs_pc (set_regs_pc r1_7_e2 [((13%bv : bv 5), SOff 35 0)] (0x44fc8 + D_2c4)) [((14%bv : bv 5), SOff 36 0)] (0x44fcc + D_2c4)))))).
Lemma r_r1_7_3 {imgk : img} : RUN (set_regs_pc (set_regs_pc r1_7_e2 [((13%bv : bv 5), SOff 35 0)] (0x44fc8 + D_2c4)) [((14%bv : bv 5), SOff 36 0)] (0x44fcc + D_2c4)) = (r1_7_e3, RS_stopped (SR_branch BC_EQ (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_7z_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_7_e3 BC_EQ (RG r1_7_e3 13) (SLit 0))))).
Definition r1_7z_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUNTO (AC r1_7_e3 BC_EQ (RG r1_7_e3 13) (SLit 0)))))).
Lemma r_r1_7z_0 {imgk : img} : RUNTO (AC r1_7_e3 BC_EQ (RG r1_7_e3 13) (SLit 0)) = (r1_7z_e0, RS_running). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_7n_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_7_e3 BC_NE (RG r1_7_e3 13) (SLit 0))))).
Definition r1_7n_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r1_7_e3 BC_NE (RG r1_7_e3 13) (SLit 0)))))).
Lemma r_r1_7n_0 {imgk : img} : RUN (AC r1_7_e3 BC_NE (RG r1_7_e3 13) (SLit 0)) = (r1_7n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 7%nat 22 41 34) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_7n_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_7n_e0 BC_EQ (RG r1_7n_e0 10) (SLit 0))))).
Definition r1_7n_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUNTO (AC r1_7n_e0 BC_EQ (RG r1_7n_e0 10) (SLit 0)))))).
Lemma r_r1_7n_1 {imgk : img} : RUNTO (AC r1_7n_e0 BC_EQ (RG r1_7n_e0 10) (SLit 0)) = (r1_7n_e1, RS_running). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_8_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((ssR1 8)))).
Definition r1_8_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (ssR1 8))))).
Lemma r_r1_8_0 {imgk : img} : RUN (ssR1 8) = (r1_8_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 22 0) (SLit (-1))) (SOff 41 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_8_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_8_e0 BC_GEU (RG r1_8_e0 10) (RG r1_8_e0 23))))).
Definition r1_8_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r1_8_e0 BC_GEU (RG r1_8_e0 10) (RG r1_8_e0 23)))))).
Lemma r_r1_8_1 {imgk : img} : RUN (AC r1_8_e0 BC_GEU (RG r1_8_e0 10) (RG r1_8_e0 23)) = (r1_8_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 41 (-65)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_8_s2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_8_e1 BC_LTU (RG r1_8_e1 11) (RG r1_8_e1 10))))).
Definition r1_8_e2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r1_8_e1 BC_LTU (RG r1_8_e1 11) (RG r1_8_e1 10)))))).
Lemma r_r1_8_2 {imgk : img} : RUN (AC r1_8_e1 BC_LTU (RG r1_8_e1 11) (RG r1_8_e1 10)) = (r1_8_e2, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_8_s3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((set_regs_pc (set_regs_pc r1_8_e2 [((13%bv : bv 5), SOff 35 0)] (0x44fc8 + D_2c4)) [((14%bv : bv 5), SOff 36 0)] (0x44fcc + D_2c4))))).
Definition r1_8_e3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (set_regs_pc (set_regs_pc r1_8_e2 [((13%bv : bv 5), SOff 35 0)] (0x44fc8 + D_2c4)) [((14%bv : bv 5), SOff 36 0)] (0x44fcc + D_2c4)))))).
Lemma r_r1_8_3 {imgk : img} : RUN (set_regs_pc (set_regs_pc r1_8_e2 [((13%bv : bv 5), SOff 35 0)] (0x44fc8 + D_2c4)) [((14%bv : bv 5), SOff 36 0)] (0x44fcc + D_2c4)) = (r1_8_e3, RS_stopped (SR_branch BC_EQ (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_8z_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_8_e3 BC_EQ (RG r1_8_e3 13) (SLit 0))))).
Definition r1_8z_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUNTO (AC r1_8_e3 BC_EQ (RG r1_8_e3 13) (SLit 0)))))).
Lemma r_r1_8z_0 {imgk : img} : RUNTO (AC r1_8_e3 BC_EQ (RG r1_8_e3 13) (SLit 0)) = (r1_8z_e0, RS_running). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_8n_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_8_e3 BC_NE (RG r1_8_e3 13) (SLit 0))))).
Definition r1_8n_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r1_8_e3 BC_NE (RG r1_8_e3 13) (SLit 0)))))).
Lemma r_r1_8n_0 {imgk : img} : RUN (AC r1_8_e3 BC_NE (RG r1_8_e3 13) (SLit 0)) = (r1_8n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 8%nat 22 41 34) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r1_8n_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r1_8n_e0 BC_EQ (RG r1_8n_e0 10) (SLit 0))))).
Definition r1_8n_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUNTO (AC r1_8n_e0 BC_EQ (RG r1_8n_e0 10) (SLit 0)))))).
Lemma r_r1_8n_1 {imgk : img} : RUNTO (AC r1_8n_e0 BC_EQ (RG r1_8n_e0 10) (SLit 0)) = (r1_8n_e1, RS_running). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r2L_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((ssR2L)))).
Definition r2L_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (ssR2L))))).
Lemma r_r2L_0 {imgk : img} : RUN (ssR2L) = (r2L_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 22 0) (SLit (-1))) (SOff 41 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r2L_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r2L_e0 BC_GEU (RG r2L_e0 10) (RG r2L_e0 23))))).
Definition r2L_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r2L_e0 BC_GEU (RG r2L_e0 10) (RG r2L_e0 23)))))).
Lemma r_r2L_1 {imgk : img} : RUN (AC r2L_e0 BC_GEU (RG r2L_e0 10) (RG r2L_e0 23)) = (r2L_e1, RS_stopped (SR_branch BC_GEU (SLit 2147450879) (SAlu ALU_ADD (SOff 22 0) (SOff 41 0)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r2L_s2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r2L_e1 BC_GEU (SLit 2147450879) (RG r2L_e1 18))))).
Definition r2L_e2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r2L_e1 BC_GEU (SLit 2147450879) (RG r2L_e1 18)))))).
Lemma r_r2L_2 {imgk : img} : RUN (AC r2L_e1 BC_GEU (SLit 2147450879) (RG r2L_e1 18)) = (r2L_e2, RS_stopped (SR_branch BC_GEU (SOff 22 0) (SAlu ALU_ADD (SOff 22 0) (SOff 41 0)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r2L_s3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r2L_e2 BC_LTU (RG r2L_e2 8) (RG r2L_e2 18))))).
Definition r2L_e3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r2L_e2 BC_LTU (RG r2L_e2 8) (RG r2L_e2 18)))))).
Lemma r_r2L_3 {imgk : img} : RUN (AC r2L_e2 BC_LTU (RG r2L_e2 8) (RG r2L_e2 18)) = (r2L_e3, RS_stopped (SR_branch BC_EQ (SOff 34 0) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r2Lz_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r2L_e3 BC_EQ (RG r2L_e3 11) (SLit 0))))).
Definition r2Lz_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r2L_e3 BC_EQ (RG r2L_e3 11) (SLit 0)))))).
Lemma r_r2Lz_0 {imgk : img} : RUN (AC r2L_e3 BC_EQ (RG r2L_e3 11) (SLit 0)) = (r2Lz_e0, RS_stopped (SR_branch BC_GEU (SOff 39 2147450880) (SOff 40 2147450880))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r2Lz_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r2Lz_e0 BC_LTU (RG r2Lz_e0 19) (RG r2Lz_e0 10))))).
Definition r2Lz_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r2Lz_e0 BC_LTU (RG r2Lz_e0 19) (RG r2Lz_e0 10)))))).
Lemma r_r2Lz_1 {imgk : img} : RUN (AC r2Lz_e0 BC_LTU (RG r2Lz_e0 19) (RG r2Lz_e0 10)) = (r2Lz_e1, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r2Lz_s2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((ss_after_mz r2Lz_e1 (ss_mem r2Lz_e1) 56 (0x54de8 + D_2c4))))).
Definition r2Lz_e2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUNTO (ss_after_mz r2Lz_e1 (ss_mem r2Lz_e1) 56 (0x54de8 + D_2c4)))))).
Lemma r_r2Lz_2 {imgk : img} : RUNTO (ss_after_mz r2Lz_e1 (ss_mem r2Lz_e1) 56 (0x54de8 + D_2c4)) = (r2Lz_e2, RS_running). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r2Ln_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r2L_e3 BC_NE (RG r2L_e3 11) (SLit 0))))).
Definition r2Ln_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r2L_e3 BC_NE (RG r2L_e3 11) (SLit 0)))))).
Lemma r_r2Ln_0 {imgk : img} : RUN (AC r2L_e3 BC_NE (RG r2L_e3 11) (SLit 0)) = (r2Ln_e0, RS_stopped (SR_branch BC_LT (SAlu ALU_AND (SAlu ALU_ADD (SOff 22 (-1)) (SOff 41 0)) (SLit 7)) (SOff 34 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r2Ln_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r2Ln_e0 BC_LT (RG r2Ln_e0 12) (RG r2Ln_e0 11))))).
Definition r2Ln_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r2Ln_e0 BC_LT (RG r2Ln_e0 12) (RG r2Ln_e0 11)))))).
Lemma r_r2Ln_1 {imgk : img} : RUN (AC r2Ln_e0 BC_LT (RG r2Ln_e0 12) (RG r2Ln_e0 11)) = (r2Ln_e1, RS_stopped (SR_branch BC_GEU (SOff 39 2147450880) (SOff 40 2147450880))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r2Ln_s2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r2Ln_e1 BC_LTU (RG r2Ln_e1 19) (RG r2Ln_e1 10))))).
Definition r2Ln_e2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r2Ln_e1 BC_LTU (RG r2Ln_e1 19) (RG r2Ln_e1 10)))))).
Lemma r_r2Ln_2 {imgk : img} : RUN (AC r2Ln_e1 BC_LTU (RG r2Ln_e1 19) (RG r2Ln_e1 10)) = (r2Ln_e2, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r2Ln_s3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((ss_after_mz r2Ln_e2 (ss_mem r2Ln_e2) 56 (0x54de8 + D_2c4))))).
Definition r2Ln_e3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUNTO (ss_after_mz r2Ln_e2 (ss_mem r2Ln_e2) 56 (0x54de8 + D_2c4)))))).
Lemma r_r2Ln_3 {imgk : img} : RUNTO (ss_after_mz r2Ln_e2 (ss_mem r2Ln_e2) 56 (0x54de8 + D_2c4)) = (r2Ln_e3, RS_running). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r2H_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((ssR2H)))).
Definition r2H_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (ssR2H))))).
Lemma r_r2H_0 {imgk : img} : RUN (ssR2H) = (r2H_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 22 0) (SLit (-1))) (SOff 41 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r2H_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r2H_e0 BC_GEU (RG r2H_e0 10) (RG r2H_e0 23))))).
Definition r2H_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r2H_e0 BC_GEU (RG r2H_e0 10) (RG r2H_e0 23)))))).
Lemma r_r2H_1 {imgk : img} : RUN (AC r2H_e0 BC_GEU (RG r2H_e0 10) (RG r2H_e0 23)) = (r2H_e1, RS_stopped (SR_branch BC_LTU (SLit 140737488355327) (SAlu ALU_ADD (SOff 22 0) (SOff 41 0)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r2H_s2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r2H_e1 BC_GEU (SLit 140737488355327) (RG r2H_e1 18))))).
Definition r2H_e2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r2H_e1 BC_GEU (SLit 140737488355327) (RG r2H_e1 18)))))).
Lemma r_r2H_2 {imgk : img} : RUN (AC r2H_e1 BC_GEU (SLit 140737488355327) (RG r2H_e1 18)) = (r2H_e2, RS_stopped (SR_branch BC_GEU (SOff 22 0) (SAlu ALU_ADD (SOff 22 0) (SOff 41 0)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r2H_s3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r2H_e2 BC_LTU (RG r2H_e2 8) (RG r2H_e2 18))))).
Definition r2H_e3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r2H_e2 BC_LTU (RG r2H_e2 8) (RG r2H_e2 18)))))).
Lemma r_r2H_3 {imgk : img} : RUN (AC r2H_e2 BC_LTU (RG r2H_e2 8) (RG r2H_e2 18)) = (r2H_e3, RS_stopped (SR_branch BC_EQ (SOff 34 0) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r2Hz_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r2H_e3 BC_EQ (RG r2H_e3 11) (SLit 0))))).
Definition r2Hz_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r2H_e3 BC_EQ (RG r2H_e3 11) (SLit 0)))))).
Lemma r_r2Hz_0 {imgk : img} : RUN (AC r2H_e3 BC_EQ (RG r2H_e3 11) (SLit 0)) = (r2Hz_e0, RS_stopped (SR_branch BC_GEU (SOff 39 2147450880) (SOff 40 2147450880))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r2Hz_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r2Hz_e0 BC_LTU (RG r2Hz_e0 19) (RG r2Hz_e0 10))))).
Definition r2Hz_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r2Hz_e0 BC_LTU (RG r2Hz_e0 19) (RG r2Hz_e0 10)))))).
Lemma r_r2Hz_1 {imgk : img} : RUN (AC r2Hz_e0 BC_LTU (RG r2Hz_e0 19) (RG r2Hz_e0 10)) = (r2Hz_e1, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r2Hz_s2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((ss_after_mz r2Hz_e1 (ss_mem r2Hz_e1) 56 (0x54de8 + D_2c4))))).
Definition r2Hz_e2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUNTO (ss_after_mz r2Hz_e1 (ss_mem r2Hz_e1) 56 (0x54de8 + D_2c4)))))).
Lemma r_r2Hz_2 {imgk : img} : RUNTO (ss_after_mz r2Hz_e1 (ss_mem r2Hz_e1) 56 (0x54de8 + D_2c4)) = (r2Hz_e2, RS_running). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r2Hn_s0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r2H_e3 BC_NE (RG r2H_e3 11) (SLit 0))))).
Definition r2Hn_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r2H_e3 BC_NE (RG r2H_e3 11) (SLit 0)))))).
Lemma r_r2Hn_0 {imgk : img} : RUN (AC r2H_e3 BC_NE (RG r2H_e3 11) (SLit 0)) = (r2Hn_e0, RS_stopped (SR_branch BC_LT (SAlu ALU_AND (SAlu ALU_ADD (SOff 22 (-1)) (SOff 41 0)) (SLit 7)) (SOff 34 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r2Hn_s1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r2Hn_e0 BC_LT (RG r2Hn_e0 12) (RG r2Hn_e0 11))))).
Definition r2Hn_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r2Hn_e0 BC_LT (RG r2Hn_e0 12) (RG r2Hn_e0 11)))))).
Lemma r_r2Hn_1 {imgk : img} : RUN (AC r2Hn_e0 BC_LT (RG r2Hn_e0 12) (RG r2Hn_e0 11)) = (r2Hn_e1, RS_stopped (SR_branch BC_GEU (SOff 39 2147450880) (SOff 40 2147450880))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r2Hn_s2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((AC r2Hn_e1 BC_LTU (RG r2Hn_e1 19) (RG r2Hn_e1 10))))).
Definition r2Hn_e2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC r2Hn_e1 BC_LTU (RG r2Hn_e1 19) (RG r2Hn_e1 10)))))).
Lemma r_r2Hn_2 {imgk : img} : RUN (AC r2Hn_e1 BC_LTU (RG r2Hn_e1 19) (RG r2Hn_e1 10)) = (r2Hn_e2, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition r2Hn_s3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((ss_after_mz r2Hn_e2 (ss_mem r2Hn_e2) 56 (0x54de8 + D_2c4))))).
Definition r2Hn_e3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUNTO (ss_after_mz r2Hn_e2 (ss_mem r2Hn_e2) 56 (0x54de8 + D_2c4)))))).
Lemma r_r2Hn_3 {imgk : img} : RUNTO (ss_after_mz r2Hn_e2 (ss_mem r2Hn_e2) 56 (0x54de8 + D_2c4)) = (r2Hn_e3, RS_running). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (RG ss r) v.
Definition KEPT : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 27].
Definition shapeR {imgk : img} (ss : sstate) : bool :=
(ss_pc ss =? RC_END) &&
match ss_mem ss with r :: _ => obase_eqb (YQ0b.r_base r) (Some 2%nat) && (YQ0b.r_wlo r =? - RC_STK) && (YQ0b.r_whi r =? 0) | [] => false end &&
forallb (fun r => reg_is ss r (SOff (Z.to_nat r) 0)) KEPT.
Section f. Context {imgk : img}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfxsegs B.
Hypothesis TB : TfxSyms B.
Variables (ly : alayout) (S : astate) (W : world tfxsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (p n : Z).
Hypothesis HAR : AR tfxsegs B ly S W mem md.
Hypothesis Hal : spZ regs mod 16 = 0.
Hypothesis Hslo : ly_stk_lo ly + RC_SCR <= spZ regs.
Hypothesis Hshi : spZ regs <= ly_stk_hi ly.
Hypothesis HpresS : forall a, spZ regs - RC_SCR <= a < spZ regs -> apresent (w_H W) mem a.
Hypothesis GN : getr regs 10 = w64 (n - 1).
Hypothesis GP : getr regs 22 = w64 p.
Hypothesis Hp1 : 0 < p.
Hypothesis Hn : 1 <= n < 2 ^ 32.
Hypothesis Hp : 0 <= p.
Hypothesis Hpn : p + n <= 2 ^ 63.
Hypothesis HAM : amem_range p n.
Hypothesis HRA : range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF p n.
Hypothesis HHULL : shadow_hull_vis (aview tfxsegs (w_H W) mem) p n.
Definition POSTr : world tfxsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfxsegs RC_END regs' mem' md' /\
AR tfxsegs B ly S W mem' md' /\
(forall r, acallee_saved r -> r <> 23 -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
same_but_materialized md md' /\
True /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - RC_SCR <= a < spZ regs) -> aview tfxsegs (w_H W) mem' a = aview tfxsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
(forall z : word, ~ (spZ regs - RC_SCR <= bv_unsigned z < spZ regs) -> mem' z = mem z).
Let sp0 : Z := spZ regs.
Let H := w_H W.
Let g0 : Z := p / 8.
Let g1 : Z := (p + n - 1) / 8.
Let du : Z := (p + 7) / 8 * 8.
Let de : Z := (p + n) / 8 * 8.
Let gu : Z := (p + 7) / 8.
Let ge : Z := (p + n) / 8.
Lemma basics : 2 ^ 44 <= sp0 <= 2 ^ 47 /\ kHighMemBeg + 72 <= sp0 /\ sp0 mod 16 = 0 /\ p + n <= 2 ^ 47 - 1 /\
(forall a, sp0 - 72 <= a < sp0 -> apresent H mem a) /\ ARm B ly S (aview tfxsegs H mem).
Proof.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
pose proof Hslo as Hslo'. pose proof Hshi as Hshi'. pose proof HAM as HAM'.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, RC_SCR in *. (subst sp0 H; cbv beta).
split; [img_lia|]. split; [img_lia|]. split; [img_try (img_exact Hal)|]. split; [img_lia|]. split; [img_try (img_exact HpresS) | img_try (img_exact (proj1 HAR))].
Qed.
Lemma finishR : forall E ss ms mat,
st_ok tfxsegs E ss (restrict H ms) -> ss_resv ss = None -> shapeR ss = true ->
(forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r) ->
(forall z : word, ~ (sp0 - RC_SCR <= bv_unsigned z < sp0) -> ms_mem ms z = mem z) ->
(forall a, sp0 - RC_SCR <= a < sp0 - RC_STK -> apresent H (ms_mem ms) a) ->
POSTr W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)).
Proof.
intros E ss ms mat HS Hrv Hsh HE MEQ PRS.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
pose proof Hslo as Hslo'. pose proof Hshi as Hstop. unfold RC_SCR, RC_STK in *.
unfold shapeR in Hsh. apply andb_prop in Hsh as [Hsh HK]. apply andb_prop in Hsh as [Hpc Smem].
destruct (ss_mem ss) as [|r0 rest] eqn:Hmem; [img_try (discriminate)|].
apply andb_prop in Smem as [Smem Hwhi]. apply andb_prop in Smem as [Hbase Hwlo].
apply obase_eqb_eq in Hbase. apply Z.eqb_eq in Hwlo. apply Z.eqb_eq in Hwhi. apply Z.eqb_eq in Hpc.
assert (E2 : bv_unsigned (ew E 2) = sp0) by (img_try (rewrite (HE 2%nat 2%bv eq_refl); img_refl)).
assert (RD : forall (r : bv 5) v, reg_is ss (bv_unsigned r) v = true -> getr (ms_regs ms) r = sv_denot E v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. img_apply (st_ok_reg_denot H E ss ms r HS). }
pose proof (st_ok_restrict_mkst tfxsegs H E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape.
assert (AV : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 72 <= a < sp0) -> aview tfxsegs H (ms_mem ms) a = aview tfxsegs H mem a).
{ intros a Hr Ha. img_apply aview_same. img_apply MEQ. rewrite unsigned_lit_small by img_lia. img_exact Ha. }
assert (PW : forall a, sp0 - 64 <= a < sp0 -> apresent H (ms_mem ms) a).
{ intros a Ha. img_apply (st_ok_window_apresent H E ss ms 0 r0 a HS ltac:(img_try (rewrite Hmem; img_refl))); [| img_try (unfold TFX_IMG_END, kHighMemBeg in *; img_lia)].
rewrite Hbase, Hwlo, Hwhi. cbn [base_val]. rewrite E2. unfold RC_STK. img_lia. }
assert (PM : forall a, apresent H mem a -> apresent H (ms_mem ms) a).
{ intros a Hpa. pose proof Hpa as [Hh [b Hb]].
rewrite (YE0v.apresent_mod _ (ms_mem ms) a). rewrite (YE0v.apresent_mod _ mem a) in Hpa.
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (img_try (img_apply Z.mod_pos_bound; img_lia)). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 72)) as [L1|L1]; [img_try (img_apply (apresent_same H mem (ms_mem ms) a'); [img_apply MEQ; rewrite unsigned_lit_small by img_lia; img_lia | img_exact Hpa])|].
destruct (Z_lt_le_dec a' (sp0 - 64)) as [L2|L2]; [img_try (img_apply PRS; img_lia)|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [img_try (img_apply PW; img_lia)|].
img_apply (apresent_same H mem (ms_mem ms) a'); [img_try (img_apply MEQ; rewrite unsigned_lit_small by img_lia; img_lia) | img_try (img_exact Hpa)]. }
split; [img_refl|]. exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md) mat md).
split; [img_try (rewrite Hshape; img_refl)|].
split; [|img_try (split; [|split; [|split; [|split; [|split]]]])].
-
img_apply (al_frame _ _ LAWS ly S W mem md (ms_mem ms) _ HAR).
+ intros a Hr Hown. img_apply AV; [img_try (img_exact Hr)|]. intros Hs. img_exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(img_lia) Hown).
+ intros a Hv. rewrite (YE0v.aview_mod _ (ms_mem ms) a). rewrite (YE0v.aview_mod _ mem a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (img_try (img_apply Z.mod_pos_bound; img_lia)). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 72)) as [L1|L1]; [img_try (rewrite AV by img_lia; img_exact Hv)|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [| img_try (rewrite AV by img_lia; img_exact Hv)].
img_apply aview_some_of_apresent. destruct (Z_lt_le_dec a' (sp0 - 64)); [img_try (img_apply PRS; img_lia) | img_try (img_apply PW; img_lia)].
+ img_apply (same_but_materialized_frame md _ (with_vm_backing_same md mat)).
+ img_apply (same_but_materialized_frame md _ (with_vm_backing_same md mat)).
+ img_apply (same_but_materialized_frame md _ (with_vm_backing_same md mat)).
+ img_exact (YE0v.hs_kept_win _ _ _ _ _ _ _ _ MEQ Bpres ltac:(img_lia) ltac:(img_lia)).
-
intros r Hr H23. unfold acallee_saved in Hr. rewrite forallb_forall in HK.
assert (Hin : In r KEPT) by (img_try (unfold KEPT; cbn; img_lia)).
specialize (HK r Hin). cbn beta in HK.
assert (Hr32 : 0 <= r < 32) by img_lia.
rewrite (RD (Z_to_bv 5 r) (SOff (Z.to_nat r) 0)).
2:{ rewrite Z_to_bv_unsigned. unfold bv_wrap. img_change (bv_modulus 5) with 32. rewrite Z.mod_small by img_lia. img_exact HK. }
cbn [sv_denot]. rewrite (HE (Z.to_nat r) (Z_to_bv 5 r)), Z.add_0_r, Z_to_bv_bv_unsigned; [img_refl|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. img_change (bv_modulus 5) with 32. rewrite Z.mod_small by img_lia. img_lia.
- img_apply with_vm_backing_same.
- img_exact I.
- intros a Hr Hs. img_apply AV; [img_try (img_exact Hr) | img_try (img_exact Hs)].
- img_exact PM.
- intros z Hz. img_apply MEQ. img_exact Hz.
Qed.
Local Notation Env := (YE0v.Env regs).
Lemma Env_reg : forall extra i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew (Env extra) i = getr regs r.
Proof. intros. img_apply YE0v.Env_reg. assumption. Qed.
Lemma Env_x : forall extra j z, nth_error extra j = Some z -> ew (Env extra) (32 + j) = Z_to_bv 64 z.
Proof. intros. img_apply YE0v.Env_x. assumption. Qed.
Lemma Env2 : forall extra, bv_unsigned (ew (Env extra) 2) = sp0.
Proof. intros extra. rewrite (Env_reg extra 2 2%bv eq_refl). img_refl. Qed.
Lemma EnvP : forall extra, ew (Env extra) 22 = Z_to_bv 64 p.
Proof. intros extra. rewrite (Env_reg extra 22 22%bv eq_refl). img_exact GP. Qed.
Lemma EnvN : forall extra, nth_error extra 9 = Some n -> ew (Env extra) 41 = Z_to_bv 64 n.
Proof. intros extra He. img_exact (Env_x extra 9 n He). Qed.
Lemma ent_stk : forall extra, region_ok tfxsegs (Env extra) (mrestrict H mem) stkR.
Proof.
intros extra. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM). unfold stkR, RC_STK.
img_apply (region_ok_stack tfxsegs (Env extra) _ 2 sp0 (- 64)); [img_try (img_exact (Env2 extra)) | img_lia | img_lia |].
intros a Ha. img_apply YF8r.apresent_writable; [img_try (unfold YF8r.TFX_IMG_END, kHighMemBeg in *; img_lia)|]. img_apply Bpres. img_lia.
Qed.
Lemma ent_ro : forall extra, Forall (region_ok tfxsegs (Env extra) (mrestrict H mem)) (map ro_region icpt_rodata).
Proof. intros extra. pose proof basics as (_ & _ & _ & _ & _ & BM). img_exact (rodata_ok B TB icpt_rodata ly S H mem (Env extra) (icpt_rodata_chk ly) BM). Qed.
Lemma ent1_0 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 0 -> aview tfxsegs H mem (SB + g1) = Some b1 -> saddr_ok (p + n - 1) b1 ->
st_ok tfxsegs (Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) (ssR1 0) (restrict H (mkst regs (Z_to_bv 64 RC_ENTRY) mem (seg_rom tfxsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E9. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as E10.
fold EE in E2, E9, E10.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod p 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound p 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (p + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
rewrite restrict_mkst_fx. unfold ssR1.
apply (st_ok_regs tfxsegs EE (mkSS RC_ENTRY sr_atoms (stkR :: shreg1 0 :: map ro_region icpt_rodata) None (mkFacts factsR1 [] (aliases1 0))) _ regsP).
2:{ img_apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := img_ev (sr_get a r) in img_change (sr_get a r) with v;
let v2 := img_ev (sr_get b r2) in img_change (sr_get b r2) with v2 end;
first [ img_refl | (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E10, unsigned_lit_small by img_lia; unfold EE; rewrite (YE0v.Env_reg regs _ 10 10%bv eq_refl), GN; unfold w64; first [img_refl | f_equal; img_lia | symmetry; f_equal; img_lia]) ] |]).
destruct Hr. }
unfold EE, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2; 0; 0; 0; 0; n])) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [img_try (img_apply ent_stk) | img_try (img_apply Forall_cons; [| img_apply ent_ro])].
unfold shreg1, region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
img_change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_try (unfold kHighMemBeg in *; img_lia)|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
repeat img_apply Forall_cons; try img_apply Forall_nil.
all: first
[ img_apply chunk_ok_zero; intros i Hi; rewrite (YF8r.aview_byte H mem _ 0); [img_refl|];
rewrite <- (ra_granule_zero (aview tfxsegs H mem) p n (g0 + i) HRA ltac:(img_lia) Hp); unfold SB; f_equal; img_lia
| eapply (chunk_ok_val tfxsegs EE _ g0 _ 1 (SOff 34 0) b1); [img_try (cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (zside) | img_try (zside) |];
img_apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; img_lia ].
- img_apply pairwise_disjoint_of_extents. unfold stkR, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by img_lia. unfold RC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; img_lia.
- split; [|img_try (split; [img_exact I|])].
+ cbn [f_atoms atoms_ok factsR1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E9, E10, E32, E34, !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. repeat split; try img_lia; img_apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|img_try (split; [|img_exact I])].
* img_apply U_inj. rewrite U_srl3, (U_atom EE 22 p E9), (U_atom EE 32 g0 E32) by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_dn1 EE 22 41 p n E9 E10), (U_atom_off EE 32 g0 0 E32) by img_lia. (subst g0 g1; cbv beta). img_lia.
Qed.
Lemma ent1_1 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 1 -> aview tfxsegs H mem (SB + g1) = Some b1 -> saddr_ok (p + n - 1) b1 ->
st_ok tfxsegs (Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) (ssR1 1) (restrict H (mkst regs (Z_to_bv 64 RC_ENTRY) mem (seg_rom tfxsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E9. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as E10.
fold EE in E2, E9, E10.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod p 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound p 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (p + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
rewrite restrict_mkst_fx. unfold ssR1.
apply (st_ok_regs tfxsegs EE (mkSS RC_ENTRY sr_atoms (stkR :: shreg1 1 :: map ro_region icpt_rodata) None (mkFacts factsR1 [] (aliases1 1))) _ regsP).
2:{ img_apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := img_ev (sr_get a r) in img_change (sr_get a r) with v;
let v2 := img_ev (sr_get b r2) in img_change (sr_get b r2) with v2 end;
first [ img_refl | (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E10, unsigned_lit_small by img_lia; unfold EE; rewrite (YE0v.Env_reg regs _ 10 10%bv eq_refl), GN; unfold w64; first [img_refl | f_equal; img_lia | symmetry; f_equal; img_lia]) ] |]).
destruct Hr. }
unfold EE, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2; 0; 0; 0; 0; n])) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [img_try (img_apply ent_stk) | img_try (img_apply Forall_cons; [| img_apply ent_ro])].
unfold shreg1, region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
img_change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_try (unfold kHighMemBeg in *; img_lia)|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
repeat img_apply Forall_cons; try img_apply Forall_nil.
all: first
[ img_apply chunk_ok_zero; intros i Hi; rewrite (YF8r.aview_byte H mem _ 0); [img_refl|];
rewrite <- (ra_granule_zero (aview tfxsegs H mem) p n (g0 + i) HRA ltac:(img_lia) Hp); unfold SB; f_equal; img_lia
| eapply (chunk_ok_val tfxsegs EE _ g0 _ 1 (SOff 34 0) b1); [img_try (cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (zside) | img_try (zside) |];
img_apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; img_lia ].
- img_apply pairwise_disjoint_of_extents. unfold stkR, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by img_lia. unfold RC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; img_lia.
- split; [|img_try (split; [img_exact I|])].
+ cbn [f_atoms atoms_ok factsR1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E9, E10, E32, E34, !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. repeat split; try img_lia; img_apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|img_try (split; [|img_exact I])].
* img_apply U_inj. rewrite U_srl3, (U_atom EE 22 p E9), (U_atom EE 32 g0 E32) by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_dn1 EE 22 41 p n E9 E10), (U_atom_off EE 32 g0 1 E32) by img_lia. (subst g0 g1; cbv beta). img_lia.
Qed.
Lemma ent1_2 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 2 -> aview tfxsegs H mem (SB + g1) = Some b1 -> saddr_ok (p + n - 1) b1 ->
st_ok tfxsegs (Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) (ssR1 2) (restrict H (mkst regs (Z_to_bv 64 RC_ENTRY) mem (seg_rom tfxsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E9. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as E10.
fold EE in E2, E9, E10.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod p 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound p 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (p + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
rewrite restrict_mkst_fx. unfold ssR1.
apply (st_ok_regs tfxsegs EE (mkSS RC_ENTRY sr_atoms (stkR :: shreg1 2 :: map ro_region icpt_rodata) None (mkFacts factsR1 [] (aliases1 2))) _ regsP).
2:{ img_apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := img_ev (sr_get a r) in img_change (sr_get a r) with v;
let v2 := img_ev (sr_get b r2) in img_change (sr_get b r2) with v2 end;
first [ img_refl | (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E10, unsigned_lit_small by img_lia; unfold EE; rewrite (YE0v.Env_reg regs _ 10 10%bv eq_refl), GN; unfold w64; first [img_refl | f_equal; img_lia | symmetry; f_equal; img_lia]) ] |]).
destruct Hr. }
unfold EE, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2; 0; 0; 0; 0; n])) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [img_try (img_apply ent_stk) | img_try (img_apply Forall_cons; [| img_apply ent_ro])].
unfold shreg1, region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
img_change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_try (unfold kHighMemBeg in *; img_lia)|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
repeat img_apply Forall_cons; try img_apply Forall_nil.
all: first
[ img_apply chunk_ok_zero; intros i Hi; rewrite (YF8r.aview_byte H mem _ 0); [img_refl|];
rewrite <- (ra_granule_zero (aview tfxsegs H mem) p n (g0 + i) HRA ltac:(img_lia) Hp); unfold SB; f_equal; img_lia
| eapply (chunk_ok_val tfxsegs EE _ g0 _ 1 (SOff 34 0) b1); [img_try (cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (zside) | img_try (zside) |];
img_apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; img_lia ].
- img_apply pairwise_disjoint_of_extents. unfold stkR, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by img_lia. unfold RC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; img_lia.
- split; [|img_try (split; [img_exact I|])].
+ cbn [f_atoms atoms_ok factsR1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E9, E10, E32, E34, !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. repeat split; try img_lia; img_apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|img_try (split; [|img_exact I])].
* img_apply U_inj. rewrite U_srl3, (U_atom EE 22 p E9), (U_atom EE 32 g0 E32) by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_dn1 EE 22 41 p n E9 E10), (U_atom_off EE 32 g0 2 E32) by img_lia. (subst g0 g1; cbv beta). img_lia.
Qed.
Lemma ent1_3 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 3 -> aview tfxsegs H mem (SB + g1) = Some b1 -> saddr_ok (p + n - 1) b1 ->
st_ok tfxsegs (Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) (ssR1 3) (restrict H (mkst regs (Z_to_bv 64 RC_ENTRY) mem (seg_rom tfxsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E9. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as E10.
fold EE in E2, E9, E10.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod p 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound p 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (p + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
rewrite restrict_mkst_fx. unfold ssR1.
apply (st_ok_regs tfxsegs EE (mkSS RC_ENTRY sr_atoms (stkR :: shreg1 3 :: map ro_region icpt_rodata) None (mkFacts factsR1 [] (aliases1 3))) _ regsP).
2:{ img_apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := img_ev (sr_get a r) in img_change (sr_get a r) with v;
let v2 := img_ev (sr_get b r2) in img_change (sr_get b r2) with v2 end;
first [ img_refl | (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E10, unsigned_lit_small by img_lia; unfold EE; rewrite (YE0v.Env_reg regs _ 10 10%bv eq_refl), GN; unfold w64; first [img_refl | f_equal; img_lia | symmetry; f_equal; img_lia]) ] |]).
destruct Hr. }
unfold EE, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2; 0; 0; 0; 0; n])) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [img_try (img_apply ent_stk) | img_try (img_apply Forall_cons; [| img_apply ent_ro])].
unfold shreg1, region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
img_change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_try (unfold kHighMemBeg in *; img_lia)|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
repeat img_apply Forall_cons; try img_apply Forall_nil.
all: first
[ img_apply chunk_ok_zero; intros i Hi; rewrite (YF8r.aview_byte H mem _ 0); [img_refl|];
rewrite <- (ra_granule_zero (aview tfxsegs H mem) p n (g0 + i) HRA ltac:(img_lia) Hp); unfold SB; f_equal; img_lia
| eapply (chunk_ok_val tfxsegs EE _ g0 _ 1 (SOff 34 0) b1); [img_try (cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (zside) | img_try (zside) |];
img_apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; img_lia ].
- img_apply pairwise_disjoint_of_extents. unfold stkR, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by img_lia. unfold RC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; img_lia.
- split; [|img_try (split; [img_exact I|])].
+ cbn [f_atoms atoms_ok factsR1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E9, E10, E32, E34, !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. repeat split; try img_lia; img_apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|img_try (split; [|img_exact I])].
* img_apply U_inj. rewrite U_srl3, (U_atom EE 22 p E9), (U_atom EE 32 g0 E32) by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_dn1 EE 22 41 p n E9 E10), (U_atom_off EE 32 g0 3 E32) by img_lia. (subst g0 g1; cbv beta). img_lia.
Qed.
Lemma ent1_4 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 4 -> aview tfxsegs H mem (SB + g1) = Some b1 -> saddr_ok (p + n - 1) b1 ->
st_ok tfxsegs (Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) (ssR1 4) (restrict H (mkst regs (Z_to_bv 64 RC_ENTRY) mem (seg_rom tfxsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E9. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as E10.
fold EE in E2, E9, E10.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod p 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound p 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (p + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
rewrite restrict_mkst_fx. unfold ssR1.
apply (st_ok_regs tfxsegs EE (mkSS RC_ENTRY sr_atoms (stkR :: shreg1 4 :: map ro_region icpt_rodata) None (mkFacts factsR1 [] (aliases1 4))) _ regsP).
2:{ img_apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := img_ev (sr_get a r) in img_change (sr_get a r) with v;
let v2 := img_ev (sr_get b r2) in img_change (sr_get b r2) with v2 end;
first [ img_refl | (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E10, unsigned_lit_small by img_lia; unfold EE; rewrite (YE0v.Env_reg regs _ 10 10%bv eq_refl), GN; unfold w64; first [img_refl | f_equal; img_lia | symmetry; f_equal; img_lia]) ] |]).
destruct Hr. }
unfold EE, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2; 0; 0; 0; 0; n])) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [img_try (img_apply ent_stk) | img_try (img_apply Forall_cons; [| img_apply ent_ro])].
unfold shreg1, region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
img_change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_try (unfold kHighMemBeg in *; img_lia)|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
repeat img_apply Forall_cons; try img_apply Forall_nil.
all: first
[ img_apply chunk_ok_zero; intros i Hi; rewrite (YF8r.aview_byte H mem _ 0); [img_refl|];
rewrite <- (ra_granule_zero (aview tfxsegs H mem) p n (g0 + i) HRA ltac:(img_lia) Hp); unfold SB; f_equal; img_lia
| eapply (chunk_ok_val tfxsegs EE _ g0 _ 1 (SOff 34 0) b1); [img_try (cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (zside) | img_try (zside) |];
img_apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; img_lia ].
- img_apply pairwise_disjoint_of_extents. unfold stkR, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by img_lia. unfold RC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; img_lia.
- split; [|img_try (split; [img_exact I|])].
+ cbn [f_atoms atoms_ok factsR1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E9, E10, E32, E34, !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. repeat split; try img_lia; img_apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|img_try (split; [|img_exact I])].
* img_apply U_inj. rewrite U_srl3, (U_atom EE 22 p E9), (U_atom EE 32 g0 E32) by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_dn1 EE 22 41 p n E9 E10), (U_atom_off EE 32 g0 4 E32) by img_lia. (subst g0 g1; cbv beta). img_lia.
Qed.
Lemma ent1_5 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 5 -> aview tfxsegs H mem (SB + g1) = Some b1 -> saddr_ok (p + n - 1) b1 ->
st_ok tfxsegs (Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) (ssR1 5) (restrict H (mkst regs (Z_to_bv 64 RC_ENTRY) mem (seg_rom tfxsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E9. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as E10.
fold EE in E2, E9, E10.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod p 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound p 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (p + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
rewrite restrict_mkst_fx. unfold ssR1.
apply (st_ok_regs tfxsegs EE (mkSS RC_ENTRY sr_atoms (stkR :: shreg1 5 :: map ro_region icpt_rodata) None (mkFacts factsR1 [] (aliases1 5))) _ regsP).
2:{ img_apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := img_ev (sr_get a r) in img_change (sr_get a r) with v;
let v2 := img_ev (sr_get b r2) in img_change (sr_get b r2) with v2 end;
first [ img_refl | (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E10, unsigned_lit_small by img_lia; unfold EE; rewrite (YE0v.Env_reg regs _ 10 10%bv eq_refl), GN; unfold w64; first [img_refl | f_equal; img_lia | symmetry; f_equal; img_lia]) ] |]).
destruct Hr. }
unfold EE, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2; 0; 0; 0; 0; n])) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [img_try (img_apply ent_stk) | img_try (img_apply Forall_cons; [| img_apply ent_ro])].
unfold shreg1, region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
img_change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_try (unfold kHighMemBeg in *; img_lia)|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
repeat img_apply Forall_cons; try img_apply Forall_nil.
all: first
[ img_apply chunk_ok_zero; intros i Hi; rewrite (YF8r.aview_byte H mem _ 0); [img_refl|];
rewrite <- (ra_granule_zero (aview tfxsegs H mem) p n (g0 + i) HRA ltac:(img_lia) Hp); unfold SB; f_equal; img_lia
| eapply (chunk_ok_val tfxsegs EE _ g0 _ 1 (SOff 34 0) b1); [img_try (cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (zside) | img_try (zside) |];
img_apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; img_lia ].
- img_apply pairwise_disjoint_of_extents. unfold stkR, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by img_lia. unfold RC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; img_lia.
- split; [|img_try (split; [img_exact I|])].
+ cbn [f_atoms atoms_ok factsR1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E9, E10, E32, E34, !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. repeat split; try img_lia; img_apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|img_try (split; [|img_exact I])].
* img_apply U_inj. rewrite U_srl3, (U_atom EE 22 p E9), (U_atom EE 32 g0 E32) by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_dn1 EE 22 41 p n E9 E10), (U_atom_off EE 32 g0 5 E32) by img_lia. (subst g0 g1; cbv beta). img_lia.
Qed.
Lemma ent1_6 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 6 -> aview tfxsegs H mem (SB + g1) = Some b1 -> saddr_ok (p + n - 1) b1 ->
st_ok tfxsegs (Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) (ssR1 6) (restrict H (mkst regs (Z_to_bv 64 RC_ENTRY) mem (seg_rom tfxsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E9. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as E10.
fold EE in E2, E9, E10.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod p 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound p 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (p + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
rewrite restrict_mkst_fx. unfold ssR1.
apply (st_ok_regs tfxsegs EE (mkSS RC_ENTRY sr_atoms (stkR :: shreg1 6 :: map ro_region icpt_rodata) None (mkFacts factsR1 [] (aliases1 6))) _ regsP).
2:{ img_apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := img_ev (sr_get a r) in img_change (sr_get a r) with v;
let v2 := img_ev (sr_get b r2) in img_change (sr_get b r2) with v2 end;
first [ img_refl | (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E10, unsigned_lit_small by img_lia; unfold EE; rewrite (YE0v.Env_reg regs _ 10 10%bv eq_refl), GN; unfold w64; first [img_refl | f_equal; img_lia | symmetry; f_equal; img_lia]) ] |]).
destruct Hr. }
unfold EE, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2; 0; 0; 0; 0; n])) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [img_try (img_apply ent_stk) | img_try (img_apply Forall_cons; [| img_apply ent_ro])].
unfold shreg1, region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
img_change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_try (unfold kHighMemBeg in *; img_lia)|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
repeat img_apply Forall_cons; try img_apply Forall_nil.
all: first
[ img_apply chunk_ok_zero; intros i Hi; rewrite (YF8r.aview_byte H mem _ 0); [img_refl|];
rewrite <- (ra_granule_zero (aview tfxsegs H mem) p n (g0 + i) HRA ltac:(img_lia) Hp); unfold SB; f_equal; img_lia
| eapply (chunk_ok_val tfxsegs EE _ g0 _ 1 (SOff 34 0) b1); [img_try (cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (zside) | img_try (zside) |];
img_apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; img_lia ].
- img_apply pairwise_disjoint_of_extents. unfold stkR, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by img_lia. unfold RC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; img_lia.
- split; [|img_try (split; [img_exact I|])].
+ cbn [f_atoms atoms_ok factsR1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E9, E10, E32, E34, !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. repeat split; try img_lia; img_apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|img_try (split; [|img_exact I])].
* img_apply U_inj. rewrite U_srl3, (U_atom EE 22 p E9), (U_atom EE 32 g0 E32) by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_dn1 EE 22 41 p n E9 E10), (U_atom_off EE 32 g0 6 E32) by img_lia. (subst g0 g1; cbv beta). img_lia.
Qed.
Lemma ent1_7 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 7 -> aview tfxsegs H mem (SB + g1) = Some b1 -> saddr_ok (p + n - 1) b1 ->
st_ok tfxsegs (Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) (ssR1 7) (restrict H (mkst regs (Z_to_bv 64 RC_ENTRY) mem (seg_rom tfxsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E9. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as E10.
fold EE in E2, E9, E10.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod p 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound p 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (p + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
rewrite restrict_mkst_fx. unfold ssR1.
apply (st_ok_regs tfxsegs EE (mkSS RC_ENTRY sr_atoms (stkR :: shreg1 7 :: map ro_region icpt_rodata) None (mkFacts factsR1 [] (aliases1 7))) _ regsP).
2:{ img_apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := img_ev (sr_get a r) in img_change (sr_get a r) with v;
let v2 := img_ev (sr_get b r2) in img_change (sr_get b r2) with v2 end;
first [ img_refl | (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E10, unsigned_lit_small by img_lia; unfold EE; rewrite (YE0v.Env_reg regs _ 10 10%bv eq_refl), GN; unfold w64; first [img_refl | f_equal; img_lia | symmetry; f_equal; img_lia]) ] |]).
destruct Hr. }
unfold EE, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2; 0; 0; 0; 0; n])) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [img_try (img_apply ent_stk) | img_try (img_apply Forall_cons; [| img_apply ent_ro])].
unfold shreg1, region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
img_change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_try (unfold kHighMemBeg in *; img_lia)|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
repeat img_apply Forall_cons; try img_apply Forall_nil.
all: first
[ img_apply chunk_ok_zero; intros i Hi; rewrite (YF8r.aview_byte H mem _ 0); [img_refl|];
rewrite <- (ra_granule_zero (aview tfxsegs H mem) p n (g0 + i) HRA ltac:(img_lia) Hp); unfold SB; f_equal; img_lia
| eapply (chunk_ok_val tfxsegs EE _ g0 _ 1 (SOff 34 0) b1); [img_try (cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (zside) | img_try (zside) |];
img_apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; img_lia ].
- img_apply pairwise_disjoint_of_extents. unfold stkR, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by img_lia. unfold RC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; img_lia.
- split; [|img_try (split; [img_exact I|])].
+ cbn [f_atoms atoms_ok factsR1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E9, E10, E32, E34, !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. repeat split; try img_lia; img_apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|img_try (split; [|img_exact I])].
* img_apply U_inj. rewrite U_srl3, (U_atom EE 22 p E9), (U_atom EE 32 g0 E32) by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_dn1 EE 22 41 p n E9 E10), (U_atom_off EE 32 g0 7 E32) by img_lia. (subst g0 g1; cbv beta). img_lia.
Qed.
Lemma ent1_8 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 8 -> aview tfxsegs H mem (SB + g1) = Some b1 -> saddr_ok (p + n - 1) b1 ->
st_ok tfxsegs (Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) (ssR1 8) (restrict H (mkst regs (Z_to_bv 64 RC_ENTRY) mem (seg_rom tfxsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E9. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as E10.
fold EE in E2, E9, E10.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod p 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound p 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (p + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
rewrite restrict_mkst_fx. unfold ssR1.
apply (st_ok_regs tfxsegs EE (mkSS RC_ENTRY sr_atoms (stkR :: shreg1 8 :: map ro_region icpt_rodata) None (mkFacts factsR1 [] (aliases1 8))) _ regsP).
2:{ img_apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := img_ev (sr_get a r) in img_change (sr_get a r) with v;
let v2 := img_ev (sr_get b r2) in img_change (sr_get b r2) with v2 end;
first [ img_refl | (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E10, unsigned_lit_small by img_lia; unfold EE; rewrite (YE0v.Env_reg regs _ 10 10%bv eq_refl), GN; unfold w64; first [img_refl | f_equal; img_lia | symmetry; f_equal; img_lia]) ] |]).
destruct Hr. }
unfold EE, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2; 0; 0; 0; 0; n])) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [img_try (img_apply ent_stk) | img_try (img_apply Forall_cons; [| img_apply ent_ro])].
unfold shreg1, region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
img_change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_try (unfold kHighMemBeg in *; img_lia)|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
repeat img_apply Forall_cons; try img_apply Forall_nil.
all: first
[ img_apply chunk_ok_zero; intros i Hi; rewrite (YF8r.aview_byte H mem _ 0); [img_refl|];
rewrite <- (ra_granule_zero (aview tfxsegs H mem) p n (g0 + i) HRA ltac:(img_lia) Hp); unfold SB; f_equal; img_lia
| eapply (chunk_ok_val tfxsegs EE _ g0 _ 1 (SOff 34 0) b1); [img_try (cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (zside) | img_try (zside) |];
img_apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; img_lia ].
- img_apply pairwise_disjoint_of_extents. unfold stkR, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by img_lia. unfold RC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; img_lia.
- split; [|img_try (split; [img_exact I|])].
+ cbn [f_atoms atoms_ok factsR1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E9, E10, E32, E34, !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. repeat split; try img_lia; img_apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|img_try (split; [|img_exact I])].
* img_apply U_inj. rewrite U_srl3, (U_atom EE 22 p E9), (U_atom EE 32 g0 E32) by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_dn1 EE 22 41 p n E9 E10), (U_atom_off EE 32 g0 8 E32) by img_lia. (subst g0 g1; cbv beta). img_lia.
Qed.
Lemma ent2L : forall b1, 64 < n -> p + n <= kLowMemEnd - 1 -> aview tfxsegs H mem (SB + g1) = Some b1 -> saddr_ok (p + n - 1) b1 ->
st_ok tfxsegs (Env [g0; g1; b1; 0; 0; du; de; gu; ge; n]) ssR2L (restrict H (mkst regs (Z_to_bv 64 RC_ENTRY) mem (seg_rom tfxsegs))).
Proof.
intros b1 Hn64 Hrg Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM). unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg.
set (EE := Env [g0; g1; b1; 0; 0; du; de; gu; ge; n]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E33 : ew EE 33 = Z_to_bv 64 g1) by (img_try (img_apply (Env_x _ 1); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
assert (E37 : ew EE 37 = Z_to_bv 64 du) by (img_try (img_apply (Env_x _ 5); img_refl)).
assert (E38 : ew EE 38 = Z_to_bv 64 de) by (img_try (img_apply (Env_x _ 6); img_refl)).
assert (E39 : ew EE 39 = Z_to_bv 64 gu) by (img_try (img_apply (Env_x _ 7); img_refl)).
assert (E40 : ew EE 40 = Z_to_bv 64 ge) by (img_try (img_apply (Env_x _ 8); img_refl)).
pose proof (Env2 [g0; g1; b1; 0; 0; du; de; gu; ge; n]) as E2. pose proof (EnvP [g0; g1; b1; 0; 0; du; de; gu; ge; n]) as E9. pose proof (EnvN [g0; g1; b1; 0; 0; du; de; gu; ge; n] eq_refl) as E10.
fold EE in E2, E9, E10.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod p 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound p 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (p + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hgu : 8 * gu <= p + 7 < 8 * gu + 8 /\ du = 8 * gu) by (img_try ((subst gu du; cbv beta); pose proof (Z.div_mod (p + 7) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (p + 7) 8 ltac:(img_lia)); img_lia)).
assert (Hge : 8 * ge <= p + n < 8 * ge + 8 /\ de = 8 * ge) by (img_try ((subst ge de; cbv beta); pose proof (Z.div_mod (p + n) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (p + n) 8 ltac:(img_lia)); img_lia)).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
rewrite restrict_mkst_fx. unfold ssR2L.
img_apply (st_ok_regs tfxsegs EE (mkSS RC_ENTRY sr_atoms (stkR :: shregs2 ++ map ro_region icpt_rodata) None (mkFacts factsR2L [] aliases2)) _ regsP).
2:{ img_apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := img_ev (sr_get a r) in img_change (sr_get a r) with v;
let v2 := img_ev (sr_get b r2) in img_change (sr_get b r2) with v2 end;
first [ img_refl | (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E10, unsigned_lit_small by img_lia; unfold EE; rewrite (YE0v.Env_reg regs _ 10 10%bv eq_refl), GN; unfold w64; first [img_refl | f_equal; img_lia | symmetry; f_equal; img_lia]) ] |]).
destruct Hr. }
unfold EE, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; 0; 0; du; de; gu; ge; n])) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [img_try (img_apply ent_stk) | img_try (img_apply Forall_cons; [| img_apply Forall_cons; [| img_apply ent_ro]])].
+ unfold region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks].
img_change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply chunk_ok_zero. intros i Hi. rewrite (YF8r.aview_byte H mem _ 0); [img_refl|].
rewrite <- (ra_granule_zero (aview tfxsegs H mem) p n g0 HRA ltac:(img_lia) Hp). unfold SB. f_equal. img_lia.
+ unfold region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks].
img_change (base_val EE (Some 33%nat)) with (bv_unsigned (ew EE 33)). rewrite E33, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
eapply (chunk_ok_val tfxsegs EE _ g1 _ 1 (SOff 34 0) b1); [img_try (cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (zside) | img_try (zside) |].
img_apply val_mem1_of_aview. rewrite <- Hb1. unfold SB. f_equal. img_lia.
- img_apply pairwise_disjoint_of_extents. unfold stkR, shregs2, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite E2, E32, E33, !unsigned_lit_small by img_lia. unfold RC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; img_lia.
- split; [|img_try (split; [img_exact I|])].
+ cbn [f_atoms atoms_ok factsR2L]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E9, E10, E32, E33, E34, E37, E38, E39, E40, !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. img_change (2 ^ 3) with 8. repeat split; try img_lia; try img_apply Z.mod_1_r.
all: first [rewrite (proj2 Hgu) | rewrite (proj2 Hge)]; rewrite Z.mul_comm; img_apply Z_mod_mult.
+ cbn [f_alias aliases2 alias_ok]. split; [|img_try (split; [|split; [|split; [|split; [|split; [|img_exact I]]]]])].
* img_apply U_inj. rewrite U_srl3, (U_atom EE 22 p E9), (U_atom EE 32 g0 E32) by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_dn1 EE 22 41 p n E9 E10), (U_atom EE 33 g1 E33) by img_lia. img_refl.
* img_apply U_inj. rewrite U_and_m8, (U_atom_off EE 22 p 7 E9), (U_atom EE 37 du E37) by img_lia. pose proof (Z.div_mod (p + 7) 8 ltac:(img_lia)). img_lia.
* img_apply U_inj. rewrite U_and_m8, (U_add2 EE 22 41 p n E9 E10), (U_atom EE 38 de E38) by img_lia. pose proof (Z.div_mod (p + n) 8 ltac:(img_lia)). img_lia.
* img_apply U_inj. rewrite U_srl3, (U_atom EE 37 du E37), (U_atom EE 39 gu E39) by img_lia. rewrite (proj2 Hgu), Z.mul_comm, Z.div_mul by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_atom EE 38 de E38), (U_atom EE 40 ge E40) by img_lia. rewrite (proj2 Hge), Z.mul_comm, Z.div_mul by img_lia. img_refl.
Qed.
Lemma ent2H : forall b1, 64 < n -> kHighMemBeg <= p /\ p + n <= kHighMemEnd - 1 -> aview tfxsegs H mem (SB + g1) = Some b1 -> saddr_ok (p + n - 1) b1 ->
st_ok tfxsegs (Env [g0; g1; b1; 0; 0; du; de; gu; ge; n]) ssR2H (restrict H (mkst regs (Z_to_bv 64 RC_ENTRY) mem (seg_rom tfxsegs))).
Proof.
intros b1 Hn64 Hrg Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM). unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg.
set (EE := Env [g0; g1; b1; 0; 0; du; de; gu; ge; n]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E33 : ew EE 33 = Z_to_bv 64 g1) by (img_try (img_apply (Env_x _ 1); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
assert (E37 : ew EE 37 = Z_to_bv 64 du) by (img_try (img_apply (Env_x _ 5); img_refl)).
assert (E38 : ew EE 38 = Z_to_bv 64 de) by (img_try (img_apply (Env_x _ 6); img_refl)).
assert (E39 : ew EE 39 = Z_to_bv 64 gu) by (img_try (img_apply (Env_x _ 7); img_refl)).
assert (E40 : ew EE 40 = Z_to_bv 64 ge) by (img_try (img_apply (Env_x _ 8); img_refl)).
pose proof (Env2 [g0; g1; b1; 0; 0; du; de; gu; ge; n]) as E2. pose proof (EnvP [g0; g1; b1; 0; 0; du; de; gu; ge; n]) as E9. pose proof (EnvN [g0; g1; b1; 0; 0; du; de; gu; ge; n] eq_refl) as E10.
fold EE in E2, E9, E10.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod p 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound p 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (p + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hgu : 8 * gu <= p + 7 < 8 * gu + 8 /\ du = 8 * gu) by (img_try ((subst gu du; cbv beta); pose proof (Z.div_mod (p + 7) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (p + 7) 8 ltac:(img_lia)); img_lia)).
assert (Hge : 8 * ge <= p + n < 8 * ge + 8 /\ de = 8 * ge) by (img_try ((subst ge de; cbv beta); pose proof (Z.div_mod (p + n) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (p + n) 8 ltac:(img_lia)); img_lia)).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
rewrite restrict_mkst_fx. unfold ssR2H.
img_apply (st_ok_regs tfxsegs EE (mkSS RC_ENTRY sr_atoms (stkR :: shregs2 ++ map ro_region icpt_rodata) None (mkFacts factsR2H [] aliases2)) _ regsP).
2:{ img_apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := img_ev (sr_get a r) in img_change (sr_get a r) with v;
let v2 := img_ev (sr_get b r2) in img_change (sr_get b r2) with v2 end;
first [ img_refl | (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E10, unsigned_lit_small by img_lia; unfold EE; rewrite (YE0v.Env_reg regs _ 10 10%bv eq_refl), GN; unfold w64; first [img_refl | f_equal; img_lia | symmetry; f_equal; img_lia]) ] |]).
destruct Hr. }
unfold EE, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; 0; 0; du; de; gu; ge; n])) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [img_try (img_apply ent_stk) | img_try (img_apply Forall_cons; [| img_apply Forall_cons; [| img_apply ent_ro]])].
+ unfold region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks].
img_change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply chunk_ok_zero. intros i Hi. rewrite (YF8r.aview_byte H mem _ 0); [img_refl|].
rewrite <- (ra_granule_zero (aview tfxsegs H mem) p n g0 HRA ltac:(img_lia) Hp). unfold SB. f_equal. img_lia.
+ unfold region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks].
img_change (base_val EE (Some 33%nat)) with (bv_unsigned (ew EE 33)). rewrite E33, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
eapply (chunk_ok_val tfxsegs EE _ g1 _ 1 (SOff 34 0) b1); [img_try (cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (zside) | img_try (zside) |].
img_apply val_mem1_of_aview. rewrite <- Hb1. unfold SB. f_equal. img_lia.
- img_apply pairwise_disjoint_of_extents. unfold stkR, shregs2, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite E2, E32, E33, !unsigned_lit_small by img_lia. unfold RC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; img_lia.
- split; [|img_try (split; [img_exact I|])].
+ cbn [f_atoms atoms_ok factsR2H]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E9, E10, E32, E33, E34, E37, E38, E39, E40, !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. img_change (2 ^ 3) with 8. repeat split; try img_lia; try img_apply Z.mod_1_r.
all: first [rewrite (proj2 Hgu) | rewrite (proj2 Hge)]; rewrite Z.mul_comm; img_apply Z_mod_mult.
+ cbn [f_alias aliases2 alias_ok]. split; [|img_try (split; [|split; [|split; [|split; [|split; [|img_exact I]]]]])].
* img_apply U_inj. rewrite U_srl3, (U_atom EE 22 p E9), (U_atom EE 32 g0 E32) by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_dn1 EE 22 41 p n E9 E10), (U_atom EE 33 g1 E33) by img_lia. img_refl.
* img_apply U_inj. rewrite U_and_m8, (U_atom_off EE 22 p 7 E9), (U_atom EE 37 du E37) by img_lia. pose proof (Z.div_mod (p + 7) 8 ltac:(img_lia)). img_lia.
* img_apply U_inj. rewrite U_and_m8, (U_add2 EE 22 41 p n E9 E10), (U_atom EE 38 de E38) by img_lia. pose proof (Z.div_mod (p + n) 8 ltac:(img_lia)). img_lia.
* img_apply U_inj. rewrite U_srl3, (U_atom EE 37 du E37), (U_atom EE 39 gu E39) by img_lia. rewrite (proj2 Hgu), Z.mul_comm, Z.div_mul by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_atom EE 38 de E38), (U_atom EE 40 ge E40) by img_lia. rewrite (proj2 Hge), Z.mul_comm, Z.div_mul by img_lia. img_refl.
Qed.
  (* [comment removed for export] *)
  Tactic Notation "icpt_l1t_0" ident(Wk) ident(ck) ident(msk) ident(matk) ident(HSk) ident(HFk) ident(HFrk) ident(MEQk) ident(PSLk) hyp(MEQp) hyp(PSLp) constr(EE) hyp(EE2) :=
    cbv beta; intros Wk ck _ (-> & msk & matk & -> & HSk & HFk & HFrk); rewrite ?wvb_wvb in *;
    assert (MEQk : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem msk z = mem z);
    [ intros z Hz; rewrite (HFk z); [img_try (img_apply MEQp; unfold RC_STK, RC_SCR in *; img_lia)|]; intros Hin;
      unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [img_try ((img_case; vm_compute); img_refl)|]; unfold RC_STK, RC_SCR in *; img_lia | ];
    assert (PSLk : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem msk z <> None);
    [ intros z Hz; rewrite (HFk z); [img_try (img_apply PSLp; img_exact Hz)|]; intros Hin;
      unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [img_try ((img_case; vm_compute); img_refl)|]; unfold RC_STK, RC_SCR in *; img_lia | ];
    clear HFk HFrk.
  Tactic Notation "icpt_l1t_1" ident(Wk) ident(ck) ident(msk) ident(matk) ident(HSk) ident(HFk) ident(HFrk) ident(MEQk) ident(PSLk) hyp(MEQp) hyp(PSLp) constr(EE) hyp(EE2) :=
    cbv beta; intros Wk ck _ (-> & msk & matk & -> & HSk & HFk & HFrk); rewrite ?wvb_wvb in *;
    assert (MEQk : forall z : word, ~ (sp0 - RC_SCR <= bv_unsigned z < sp0) -> ms_mem msk z = mem z);
    [ intros z Hz; rewrite (HFk z); [img_try (img_apply MEQp; unfold RC_STK, RC_SCR in *; img_lia)|]; intros Hin;
      unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [img_try ((img_case; vm_compute); img_refl)|]; unfold RC_STK, RC_SCR in *; img_lia | ];
    assert (PSLk : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem msk z <> None);
    [ intros z Hz; rewrite (HFk z); [img_try (img_apply PSLp; img_exact Hz)|]; intros Hin;
      unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [img_try ((img_case; vm_compute); img_refl)|]; unfold RC_STK, RC_SCR in *; img_lia | ];
    clear HFk HFrk.
  Tactic Notation "icpt_l1t_2" ident(Wk) ident(ck) ident(msk) ident(matk) ident(HSk) ident(HMk) ident(MEQk) ident(PSLk) hyp(MEQp) hyp(PSLp) hyp(CL0) hyp(CL2) :=
    cbv beta; intros Wk ck _ (-> & msk & matk & -> & HSk & HMk);
    assert (MEQk : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem msk z = mem z) by (img_try (intros z Hz; rewrite HMk; img_apply MEQp; img_exact Hz));
    assert (PSLk : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem msk z <> None) by (img_try (intros z Hz; rewrite HMk; img_apply PSLp; img_exact Hz));
    clear CL0 HMk CL2.

Lemma path1_0 : n <= 64 -> g1 - g0 = 0 -> SRr tfxsegs W (cfg_at tfxsegs RC_ENTRY regs mem md) POSTr.
Proof.
intros Hn64' Ht. assert (Hn64 : 1 <= n <= 64) by img_lia.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
unfold cfg_at. img_change (w64 RC_ENTRY) with (Z_to_bv 64 RC_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 RC_ENTRY) mem (seg_rom tfxsegs)) z = mem z) by (img_try (intros; img_refl)).
assert (PSL0 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem (mkst regs (Z_to_bv 64 RC_ENTRY) mem (seg_rom tfxsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold RC_SCR, RC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(img_lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod p 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound p 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (p + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hg1hi : g1 < 2 ^ 44) by img_lia.
destruct (ra_last (aview tfxsegs H mem) p n HRA ltac:(img_lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
pose proof HHULL as HH.
set (h1 := (g0 + 2147450880) / 8 * 8). set (h2 := (g1 + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0 + 2147450880 < h1 + 8) by (img_try ((subst h1; cbv beta); pose proof (Z.div_mod (g0 + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g0 + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh2 : h2 <= g1 + 2147450880 < h2 + 8) by (img_try ((subst h2; cbv beta); pose proof (Z.div_mod (g1 + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g1 + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh12 : h1 <= h2) by (img_try ((subst h1 h2; cbv beta); img_apply Z.mul_le_mono_nonneg_r; [img_lia|]; img_apply Z.div_le_mono; img_lia)).
assert (Hsh1 : shadow_addr p / 8 * 8 = h1) by (img_try ((subst h1; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g0; cbv beta); f_equal; f_equal; img_lia)).
assert (Hsh2 : shadow_addr (p + n - 1) / 8 * 8 = h2) by (img_try ((subst h2; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g1; cbv beta); f_equal; f_equal; img_lia)).
destruct (hull_rdword H mem p n h1 HH ltac:(img_lia) ltac:(img_lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem p n h2 HH ltac:(img_lia) ltac:(img_lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (img_try (intros; img_apply Env_reg; assumption)).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EE2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EEP. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as EEN. fold EE in EE2, EEP, EEN.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (img_try (img_apply (Env_x _ 3); img_refl)).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (img_try (img_apply (Env_x _ 4); img_refl)).
pose proof (ent1_0 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [img_norm_st HS0 r_r1_0_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS0 r_r1_0_0))|].
icpt_l1t_0 W1 c1 ms1 mat1 HS1 HF1 HFr1 MEQ1 PSL1 MEQ0 PSL0 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_LTU (RG r1_0_e0 10) (RG r1_0_e0 23) HS1 (br_ovf_false EE 22 41 p n EEP EEN ltac:(img_lia) ltac:(img_lia))) as HS1'.
img_change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [img_norm_st HS1' r_r1_0_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS1' r_r1_0_1))|].
icpt_l1t_0 W2 c2 ms2 mat2 HS2 HF2 HFr2 MEQ2 PSL2 MEQ1 PSL1 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG r1_0_e1 11) (RG r1_0_e1 10) HS2 (br_cls65_small EE 41 n EEN Hn64)) as HS2'.
img_change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_r1_0_2; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS2' r_r1_0_2))|].
icpt_l1t_0 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 PSL3 MEQ2 PSL2 EE EE2.
assert (HW4 : rdword (aview tfxsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq1)].
intros i Hi. img_apply aview_same. img_apply MEQ3. rewrite unsigned_lit_small by img_lia. unfold RC_STK, RC_SCR, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (img_apply (icpt_ld8 W EE (r1_0_e2) ms3 _ 13%bv 13%bv 439939 h1 35 56 HS3 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (U_hull_addr EE 32 g0 2147450880 E32 ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW4))|].
icpt_l1t_2 W4 c4 ms4 mat4 HS4 HM4 MEQ4 PSL4 MEQ3 PSL3 HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450880 E32) by img_lia. f_equal. (subst h2; cbv beta). replace (g0 + 2147450880) with (g1 + 2147450880) by img_lia. img_refl. }
assert (HW5 : rdword (aview tfxsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq2)].
intros i Hi. img_apply aview_same. img_apply MEQ4. rewrite unsigned_lit_small by img_lia. unfold RC_STK, RC_SCR, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (apply (icpt_ld8 W EE (set_regs_pc r1_0_e2 [((13%bv : bv 5), SOff 35 0)] (ss_pc r1_0_e2 + 4)) ms4 _ 14%bv 14%bv 472835 h2 36 56 HS4 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (Hrs2) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW5))|].
icpt_l1t_2 W5 c5 ms5 mat5 HS5 HM5 MEQ5 PSL5 MEQ4 PSL4 HW5 HS4.
eapply SRr_bind; [img_norm_st HS5 r_r1_0_3; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS5 r_r1_0_3))|].
icpt_l1t_0 W6 c6 ms6 mat6 HS6 HF6 HFr6 MEQ6 PSL6 MEQ5 PSL5 EE EE2.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_EQ (RG r1_0_e3 13) (SLit 0) HS6 (eq_trans (br_hull_eq EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (proj2 (Z.eqb_eq _ _) Hq))) as HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_r1_0z_0; img_try (img_apply (icpt_phase_to W EE RC_END _ _ _ _ _ HS6' r_r1_0z_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 PSL7 MEQ6 PSL6 EE EE2.
img_apply SRr_ret. img_apply (finishR EE r1_0z_e0 ms7 mat7 HS7 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EEreg).
- intros z Hz. img_apply MEQ7. unfold RC_SCR, RC_STK in *. img_lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
+
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_EQ (RG r1_0_e3 13) (SLit 0) HS6 (eq_trans (br_hull_eq EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (proj2 (Z.eqb_neq _ _) Hq))) as HS6'.
img_change (neg_bc BC_EQ) with BC_NE in HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_r1_0n_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS6' r_r1_0n_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 PSL7 MEQ6 PSL6 EE EE2.
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_EQ (RG r1_0n_e0 10) (SLit 0) HS7 (qc_flag_zero EE 0%nat 22 41 34 p n b1 EEP EEN E34 Hp ltac:(img_lia) Hpn ltac:(img_lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [img_norm_st HS7' r_r1_0n_1; img_try (img_apply (icpt_phase_to W EE RC_END _ _ _ _ _ HS7' r_r1_0n_1))|].
icpt_l1t_0 W8 c8 ms8 mat8 HS8 HF8 HFr8 MEQ8 PSL8 MEQ7 PSL7 EE EE2.
img_apply SRr_ret. img_apply (finishR EE r1_0n_e1 ms8 mat8 HS8 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EEreg).
- intros z Hz. img_apply MEQ8. unfold RC_SCR, RC_STK in *. img_lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
Qed.
Lemma path1_1 : n <= 64 -> g1 - g0 = 1 -> SRr tfxsegs W (cfg_at tfxsegs RC_ENTRY regs mem md) POSTr.
Proof.
intros Hn64' Ht. assert (Hn64 : 1 <= n <= 64) by img_lia.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
unfold cfg_at. img_change (w64 RC_ENTRY) with (Z_to_bv 64 RC_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 RC_ENTRY) mem (seg_rom tfxsegs)) z = mem z) by (img_try (intros; img_refl)).
assert (PSL0 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem (mkst regs (Z_to_bv 64 RC_ENTRY) mem (seg_rom tfxsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold RC_SCR, RC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(img_lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod p 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound p 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (p + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hg1hi : g1 < 2 ^ 44) by img_lia.
destruct (ra_last (aview tfxsegs H mem) p n HRA ltac:(img_lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
pose proof HHULL as HH.
set (h1 := (g0 + 2147450880) / 8 * 8). set (h2 := (g1 + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0 + 2147450880 < h1 + 8) by (img_try ((subst h1; cbv beta); pose proof (Z.div_mod (g0 + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g0 + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh2 : h2 <= g1 + 2147450880 < h2 + 8) by (img_try ((subst h2; cbv beta); pose proof (Z.div_mod (g1 + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g1 + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh12 : h1 <= h2) by (img_try ((subst h1 h2; cbv beta); img_apply Z.mul_le_mono_nonneg_r; [img_lia|]; img_apply Z.div_le_mono; img_lia)).
assert (Hsh1 : shadow_addr p / 8 * 8 = h1) by (img_try ((subst h1; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g0; cbv beta); f_equal; f_equal; img_lia)).
assert (Hsh2 : shadow_addr (p + n - 1) / 8 * 8 = h2) by (img_try ((subst h2; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g1; cbv beta); f_equal; f_equal; img_lia)).
destruct (hull_rdword H mem p n h1 HH ltac:(img_lia) ltac:(img_lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem p n h2 HH ltac:(img_lia) ltac:(img_lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (img_try (intros; img_apply Env_reg; assumption)).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EE2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EEP. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as EEN. fold EE in EE2, EEP, EEN.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (img_try (img_apply (Env_x _ 3); img_refl)).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (img_try (img_apply (Env_x _ 4); img_refl)).
pose proof (ent1_1 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [img_norm_st HS0 r_r1_1_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS0 r_r1_1_0))|].
icpt_l1t_0 W1 c1 ms1 mat1 HS1 HF1 HFr1 MEQ1 PSL1 MEQ0 PSL0 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_LTU (RG r1_1_e0 10) (RG r1_1_e0 23) HS1 (br_ovf_false EE 22 41 p n EEP EEN ltac:(img_lia) ltac:(img_lia))) as HS1'.
img_change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [img_norm_st HS1' r_r1_1_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS1' r_r1_1_1))|].
icpt_l1t_0 W2 c2 ms2 mat2 HS2 HF2 HFr2 MEQ2 PSL2 MEQ1 PSL1 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG r1_1_e1 11) (RG r1_1_e1 10) HS2 (br_cls65_small EE 41 n EEN Hn64)) as HS2'.
img_change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_r1_1_2; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS2' r_r1_1_2))|].
icpt_l1t_0 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 PSL3 MEQ2 PSL2 EE EE2.
assert (HW4 : rdword (aview tfxsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq1)].
intros i Hi. img_apply aview_same. img_apply MEQ3. rewrite unsigned_lit_small by img_lia. unfold RC_STK, RC_SCR, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (img_apply (icpt_ld8 W EE (r1_1_e2) ms3 _ 13%bv 13%bv 439939 h1 35 56 HS3 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (U_hull_addr EE 32 g0 2147450880 E32 ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW4))|].
icpt_l1t_2 W4 c4 ms4 mat4 HS4 HM4 MEQ4 PSL4 MEQ3 PSL3 HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450881) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450881 E32) by img_lia. f_equal. (subst h2; cbv beta). replace (g0 + 2147450881) with (g1 + 2147450880) by img_lia. img_refl. }
assert (HW5 : rdword (aview tfxsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq2)].
intros i Hi. img_apply aview_same. img_apply MEQ4. rewrite unsigned_lit_small by img_lia. unfold RC_STK, RC_SCR, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (apply (icpt_ld8 W EE (set_regs_pc r1_1_e2 [((13%bv : bv 5), SOff 35 0)] (ss_pc r1_1_e2 + 4)) ms4 _ 14%bv 14%bv 472835 h2 36 56 HS4 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (Hrs2) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW5))|].
icpt_l1t_2 W5 c5 ms5 mat5 HS5 HM5 MEQ5 PSL5 MEQ4 PSL4 HW5 HS4.
eapply SRr_bind; [img_norm_st HS5 r_r1_1_3; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS5 r_r1_1_3))|].
icpt_l1t_0 W6 c6 ms6 mat6 HS6 HF6 HFr6 MEQ6 PSL6 MEQ5 PSL5 EE EE2.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_EQ (RG r1_1_e3 13) (SLit 0) HS6 (eq_trans (br_hull_eq EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (proj2 (Z.eqb_eq _ _) Hq))) as HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_r1_1z_0; img_try (img_apply (icpt_phase_to W EE RC_END _ _ _ _ _ HS6' r_r1_1z_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 PSL7 MEQ6 PSL6 EE EE2.
img_apply SRr_ret. img_apply (finishR EE r1_1z_e0 ms7 mat7 HS7 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EEreg).
- intros z Hz. img_apply MEQ7. unfold RC_SCR, RC_STK in *. img_lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
+
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_EQ (RG r1_1_e3 13) (SLit 0) HS6 (eq_trans (br_hull_eq EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (proj2 (Z.eqb_neq _ _) Hq))) as HS6'.
img_change (neg_bc BC_EQ) with BC_NE in HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_r1_1n_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS6' r_r1_1n_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 PSL7 MEQ6 PSL6 EE EE2.
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_EQ (RG r1_1n_e0 10) (SLit 0) HS7 (qc_flag_zero EE 1%nat 22 41 34 p n b1 EEP EEN E34 Hp ltac:(img_lia) Hpn ltac:(img_lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [img_norm_st HS7' r_r1_1n_1; img_try (img_apply (icpt_phase_to W EE RC_END _ _ _ _ _ HS7' r_r1_1n_1))|].
icpt_l1t_0 W8 c8 ms8 mat8 HS8 HF8 HFr8 MEQ8 PSL8 MEQ7 PSL7 EE EE2.
img_apply SRr_ret. img_apply (finishR EE r1_1n_e1 ms8 mat8 HS8 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EEreg).
- intros z Hz. img_apply MEQ8. unfold RC_SCR, RC_STK in *. img_lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
Qed.
Lemma path1_2 : n <= 64 -> g1 - g0 = 2 -> SRr tfxsegs W (cfg_at tfxsegs RC_ENTRY regs mem md) POSTr.
Proof.
intros Hn64' Ht. assert (Hn64 : 1 <= n <= 64) by img_lia.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
unfold cfg_at. img_change (w64 RC_ENTRY) with (Z_to_bv 64 RC_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 RC_ENTRY) mem (seg_rom tfxsegs)) z = mem z) by (img_try (intros; img_refl)).
assert (PSL0 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem (mkst regs (Z_to_bv 64 RC_ENTRY) mem (seg_rom tfxsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold RC_SCR, RC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(img_lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod p 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound p 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (p + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hg1hi : g1 < 2 ^ 44) by img_lia.
destruct (ra_last (aview tfxsegs H mem) p n HRA ltac:(img_lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
pose proof HHULL as HH.
set (h1 := (g0 + 2147450880) / 8 * 8). set (h2 := (g1 + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0 + 2147450880 < h1 + 8) by (img_try ((subst h1; cbv beta); pose proof (Z.div_mod (g0 + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g0 + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh2 : h2 <= g1 + 2147450880 < h2 + 8) by (img_try ((subst h2; cbv beta); pose proof (Z.div_mod (g1 + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g1 + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh12 : h1 <= h2) by (img_try ((subst h1 h2; cbv beta); img_apply Z.mul_le_mono_nonneg_r; [img_lia|]; img_apply Z.div_le_mono; img_lia)).
assert (Hsh1 : shadow_addr p / 8 * 8 = h1) by (img_try ((subst h1; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g0; cbv beta); f_equal; f_equal; img_lia)).
assert (Hsh2 : shadow_addr (p + n - 1) / 8 * 8 = h2) by (img_try ((subst h2; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g1; cbv beta); f_equal; f_equal; img_lia)).
destruct (hull_rdword H mem p n h1 HH ltac:(img_lia) ltac:(img_lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem p n h2 HH ltac:(img_lia) ltac:(img_lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (img_try (intros; img_apply Env_reg; assumption)).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EE2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EEP. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as EEN. fold EE in EE2, EEP, EEN.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (img_try (img_apply (Env_x _ 3); img_refl)).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (img_try (img_apply (Env_x _ 4); img_refl)).
pose proof (ent1_2 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [img_norm_st HS0 r_r1_2_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS0 r_r1_2_0))|].
icpt_l1t_0 W1 c1 ms1 mat1 HS1 HF1 HFr1 MEQ1 PSL1 MEQ0 PSL0 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_LTU (RG r1_2_e0 10) (RG r1_2_e0 23) HS1 (br_ovf_false EE 22 41 p n EEP EEN ltac:(img_lia) ltac:(img_lia))) as HS1'.
img_change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [img_norm_st HS1' r_r1_2_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS1' r_r1_2_1))|].
icpt_l1t_0 W2 c2 ms2 mat2 HS2 HF2 HFr2 MEQ2 PSL2 MEQ1 PSL1 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG r1_2_e1 11) (RG r1_2_e1 10) HS2 (br_cls65_small EE 41 n EEN Hn64)) as HS2'.
img_change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_r1_2_2; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS2' r_r1_2_2))|].
icpt_l1t_0 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 PSL3 MEQ2 PSL2 EE EE2.
assert (HW4 : rdword (aview tfxsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq1)].
intros i Hi. img_apply aview_same. img_apply MEQ3. rewrite unsigned_lit_small by img_lia. unfold RC_STK, RC_SCR, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (img_apply (icpt_ld8 W EE (r1_2_e2) ms3 _ 13%bv 13%bv 439939 h1 35 56 HS3 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (U_hull_addr EE 32 g0 2147450880 E32 ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW4))|].
icpt_l1t_2 W4 c4 ms4 mat4 HS4 HM4 MEQ4 PSL4 MEQ3 PSL3 HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450882) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450882 E32) by img_lia. f_equal. (subst h2; cbv beta). replace (g0 + 2147450882) with (g1 + 2147450880) by img_lia. img_refl. }
assert (HW5 : rdword (aview tfxsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq2)].
intros i Hi. img_apply aview_same. img_apply MEQ4. rewrite unsigned_lit_small by img_lia. unfold RC_STK, RC_SCR, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (apply (icpt_ld8 W EE (set_regs_pc r1_2_e2 [((13%bv : bv 5), SOff 35 0)] (ss_pc r1_2_e2 + 4)) ms4 _ 14%bv 14%bv 472835 h2 36 56 HS4 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (Hrs2) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW5))|].
icpt_l1t_2 W5 c5 ms5 mat5 HS5 HM5 MEQ5 PSL5 MEQ4 PSL4 HW5 HS4.
eapply SRr_bind; [img_norm_st HS5 r_r1_2_3; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS5 r_r1_2_3))|].
icpt_l1t_0 W6 c6 ms6 mat6 HS6 HF6 HFr6 MEQ6 PSL6 MEQ5 PSL5 EE EE2.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_EQ (RG r1_2_e3 13) (SLit 0) HS6 (eq_trans (br_hull_eq EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (proj2 (Z.eqb_eq _ _) Hq))) as HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_r1_2z_0; img_try (img_apply (icpt_phase_to W EE RC_END _ _ _ _ _ HS6' r_r1_2z_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 PSL7 MEQ6 PSL6 EE EE2.
img_apply SRr_ret. img_apply (finishR EE r1_2z_e0 ms7 mat7 HS7 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EEreg).
- intros z Hz. img_apply MEQ7. unfold RC_SCR, RC_STK in *. img_lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
+
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_EQ (RG r1_2_e3 13) (SLit 0) HS6 (eq_trans (br_hull_eq EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (proj2 (Z.eqb_neq _ _) Hq))) as HS6'.
img_change (neg_bc BC_EQ) with BC_NE in HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_r1_2n_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS6' r_r1_2n_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 PSL7 MEQ6 PSL6 EE EE2.
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_EQ (RG r1_2n_e0 10) (SLit 0) HS7 (qc_flag_zero EE 2%nat 22 41 34 p n b1 EEP EEN E34 Hp ltac:(img_lia) Hpn ltac:(img_lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [img_norm_st HS7' r_r1_2n_1; img_try (img_apply (icpt_phase_to W EE RC_END _ _ _ _ _ HS7' r_r1_2n_1))|].
icpt_l1t_0 W8 c8 ms8 mat8 HS8 HF8 HFr8 MEQ8 PSL8 MEQ7 PSL7 EE EE2.
img_apply SRr_ret. img_apply (finishR EE r1_2n_e1 ms8 mat8 HS8 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EEreg).
- intros z Hz. img_apply MEQ8. unfold RC_SCR, RC_STK in *. img_lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
Qed.
Lemma path1_3 : n <= 64 -> g1 - g0 = 3 -> SRr tfxsegs W (cfg_at tfxsegs RC_ENTRY regs mem md) POSTr.
Proof.
intros Hn64' Ht. assert (Hn64 : 1 <= n <= 64) by img_lia.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
unfold cfg_at. img_change (w64 RC_ENTRY) with (Z_to_bv 64 RC_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 RC_ENTRY) mem (seg_rom tfxsegs)) z = mem z) by (img_try (intros; img_refl)).
assert (PSL0 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem (mkst regs (Z_to_bv 64 RC_ENTRY) mem (seg_rom tfxsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold RC_SCR, RC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(img_lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod p 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound p 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (p + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hg1hi : g1 < 2 ^ 44) by img_lia.
destruct (ra_last (aview tfxsegs H mem) p n HRA ltac:(img_lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
pose proof HHULL as HH.
set (h1 := (g0 + 2147450880) / 8 * 8). set (h2 := (g1 + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0 + 2147450880 < h1 + 8) by (img_try ((subst h1; cbv beta); pose proof (Z.div_mod (g0 + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g0 + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh2 : h2 <= g1 + 2147450880 < h2 + 8) by (img_try ((subst h2; cbv beta); pose proof (Z.div_mod (g1 + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g1 + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh12 : h1 <= h2) by (img_try ((subst h1 h2; cbv beta); img_apply Z.mul_le_mono_nonneg_r; [img_lia|]; img_apply Z.div_le_mono; img_lia)).
assert (Hsh1 : shadow_addr p / 8 * 8 = h1) by (img_try ((subst h1; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g0; cbv beta); f_equal; f_equal; img_lia)).
assert (Hsh2 : shadow_addr (p + n - 1) / 8 * 8 = h2) by (img_try ((subst h2; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g1; cbv beta); f_equal; f_equal; img_lia)).
destruct (hull_rdword H mem p n h1 HH ltac:(img_lia) ltac:(img_lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem p n h2 HH ltac:(img_lia) ltac:(img_lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (img_try (intros; img_apply Env_reg; assumption)).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EE2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EEP. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as EEN. fold EE in EE2, EEP, EEN.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (img_try (img_apply (Env_x _ 3); img_refl)).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (img_try (img_apply (Env_x _ 4); img_refl)).
pose proof (ent1_3 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [img_norm_st HS0 r_r1_3_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS0 r_r1_3_0))|].
icpt_l1t_0 W1 c1 ms1 mat1 HS1 HF1 HFr1 MEQ1 PSL1 MEQ0 PSL0 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_LTU (RG r1_3_e0 10) (RG r1_3_e0 23) HS1 (br_ovf_false EE 22 41 p n EEP EEN ltac:(img_lia) ltac:(img_lia))) as HS1'.
img_change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [img_norm_st HS1' r_r1_3_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS1' r_r1_3_1))|].
icpt_l1t_0 W2 c2 ms2 mat2 HS2 HF2 HFr2 MEQ2 PSL2 MEQ1 PSL1 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG r1_3_e1 11) (RG r1_3_e1 10) HS2 (br_cls65_small EE 41 n EEN Hn64)) as HS2'.
img_change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_r1_3_2; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS2' r_r1_3_2))|].
icpt_l1t_0 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 PSL3 MEQ2 PSL2 EE EE2.
assert (HW4 : rdword (aview tfxsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq1)].
intros i Hi. img_apply aview_same. img_apply MEQ3. rewrite unsigned_lit_small by img_lia. unfold RC_STK, RC_SCR, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (img_apply (icpt_ld8 W EE (r1_3_e2) ms3 _ 13%bv 13%bv 439939 h1 35 56 HS3 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (U_hull_addr EE 32 g0 2147450880 E32 ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW4))|].
icpt_l1t_2 W4 c4 ms4 mat4 HS4 HM4 MEQ4 PSL4 MEQ3 PSL3 HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450883) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450883 E32) by img_lia. f_equal. (subst h2; cbv beta). replace (g0 + 2147450883) with (g1 + 2147450880) by img_lia. img_refl. }
assert (HW5 : rdword (aview tfxsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq2)].
intros i Hi. img_apply aview_same. img_apply MEQ4. rewrite unsigned_lit_small by img_lia. unfold RC_STK, RC_SCR, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (apply (icpt_ld8 W EE (set_regs_pc r1_3_e2 [((13%bv : bv 5), SOff 35 0)] (ss_pc r1_3_e2 + 4)) ms4 _ 14%bv 14%bv 472835 h2 36 56 HS4 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (Hrs2) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW5))|].
icpt_l1t_2 W5 c5 ms5 mat5 HS5 HM5 MEQ5 PSL5 MEQ4 PSL4 HW5 HS4.
eapply SRr_bind; [img_norm_st HS5 r_r1_3_3; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS5 r_r1_3_3))|].
icpt_l1t_0 W6 c6 ms6 mat6 HS6 HF6 HFr6 MEQ6 PSL6 MEQ5 PSL5 EE EE2.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_EQ (RG r1_3_e3 13) (SLit 0) HS6 (eq_trans (br_hull_eq EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (proj2 (Z.eqb_eq _ _) Hq))) as HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_r1_3z_0; img_try (img_apply (icpt_phase_to W EE RC_END _ _ _ _ _ HS6' r_r1_3z_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 PSL7 MEQ6 PSL6 EE EE2.
img_apply SRr_ret. img_apply (finishR EE r1_3z_e0 ms7 mat7 HS7 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EEreg).
- intros z Hz. img_apply MEQ7. unfold RC_SCR, RC_STK in *. img_lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
+
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_EQ (RG r1_3_e3 13) (SLit 0) HS6 (eq_trans (br_hull_eq EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (proj2 (Z.eqb_neq _ _) Hq))) as HS6'.
img_change (neg_bc BC_EQ) with BC_NE in HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_r1_3n_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS6' r_r1_3n_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 PSL7 MEQ6 PSL6 EE EE2.
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_EQ (RG r1_3n_e0 10) (SLit 0) HS7 (qc_flag_zero EE 3%nat 22 41 34 p n b1 EEP EEN E34 Hp ltac:(img_lia) Hpn ltac:(img_lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [img_norm_st HS7' r_r1_3n_1; img_try (img_apply (icpt_phase_to W EE RC_END _ _ _ _ _ HS7' r_r1_3n_1))|].
icpt_l1t_0 W8 c8 ms8 mat8 HS8 HF8 HFr8 MEQ8 PSL8 MEQ7 PSL7 EE EE2.
img_apply SRr_ret. img_apply (finishR EE r1_3n_e1 ms8 mat8 HS8 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EEreg).
- intros z Hz. img_apply MEQ8. unfold RC_SCR, RC_STK in *. img_lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
Qed.
Lemma path1_4 : n <= 64 -> g1 - g0 = 4 -> SRr tfxsegs W (cfg_at tfxsegs RC_ENTRY regs mem md) POSTr.
Proof.
intros Hn64' Ht. assert (Hn64 : 1 <= n <= 64) by img_lia.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
unfold cfg_at. img_change (w64 RC_ENTRY) with (Z_to_bv 64 RC_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 RC_ENTRY) mem (seg_rom tfxsegs)) z = mem z) by (img_try (intros; img_refl)).
assert (PSL0 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem (mkst regs (Z_to_bv 64 RC_ENTRY) mem (seg_rom tfxsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold RC_SCR, RC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(img_lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod p 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound p 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (p + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hg1hi : g1 < 2 ^ 44) by img_lia.
destruct (ra_last (aview tfxsegs H mem) p n HRA ltac:(img_lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
pose proof HHULL as HH.
set (h1 := (g0 + 2147450880) / 8 * 8). set (h2 := (g1 + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0 + 2147450880 < h1 + 8) by (img_try ((subst h1; cbv beta); pose proof (Z.div_mod (g0 + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g0 + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh2 : h2 <= g1 + 2147450880 < h2 + 8) by (img_try ((subst h2; cbv beta); pose proof (Z.div_mod (g1 + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g1 + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh12 : h1 <= h2) by (img_try ((subst h1 h2; cbv beta); img_apply Z.mul_le_mono_nonneg_r; [img_lia|]; img_apply Z.div_le_mono; img_lia)).
assert (Hsh1 : shadow_addr p / 8 * 8 = h1) by (img_try ((subst h1; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g0; cbv beta); f_equal; f_equal; img_lia)).
assert (Hsh2 : shadow_addr (p + n - 1) / 8 * 8 = h2) by (img_try ((subst h2; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g1; cbv beta); f_equal; f_equal; img_lia)).
destruct (hull_rdword H mem p n h1 HH ltac:(img_lia) ltac:(img_lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem p n h2 HH ltac:(img_lia) ltac:(img_lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (img_try (intros; img_apply Env_reg; assumption)).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EE2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EEP. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as EEN. fold EE in EE2, EEP, EEN.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (img_try (img_apply (Env_x _ 3); img_refl)).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (img_try (img_apply (Env_x _ 4); img_refl)).
pose proof (ent1_4 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [img_norm_st HS0 r_r1_4_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS0 r_r1_4_0))|].
icpt_l1t_0 W1 c1 ms1 mat1 HS1 HF1 HFr1 MEQ1 PSL1 MEQ0 PSL0 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_LTU (RG r1_4_e0 10) (RG r1_4_e0 23) HS1 (br_ovf_false EE 22 41 p n EEP EEN ltac:(img_lia) ltac:(img_lia))) as HS1'.
img_change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [img_norm_st HS1' r_r1_4_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS1' r_r1_4_1))|].
icpt_l1t_0 W2 c2 ms2 mat2 HS2 HF2 HFr2 MEQ2 PSL2 MEQ1 PSL1 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG r1_4_e1 11) (RG r1_4_e1 10) HS2 (br_cls65_small EE 41 n EEN Hn64)) as HS2'.
img_change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_r1_4_2; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS2' r_r1_4_2))|].
icpt_l1t_0 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 PSL3 MEQ2 PSL2 EE EE2.
assert (HW4 : rdword (aview tfxsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq1)].
intros i Hi. img_apply aview_same. img_apply MEQ3. rewrite unsigned_lit_small by img_lia. unfold RC_STK, RC_SCR, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (img_apply (icpt_ld8 W EE (r1_4_e2) ms3 _ 13%bv 13%bv 439939 h1 35 56 HS3 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (U_hull_addr EE 32 g0 2147450880 E32 ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW4))|].
icpt_l1t_2 W4 c4 ms4 mat4 HS4 HM4 MEQ4 PSL4 MEQ3 PSL3 HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450884) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450884 E32) by img_lia. f_equal. (subst h2; cbv beta). replace (g0 + 2147450884) with (g1 + 2147450880) by img_lia. img_refl. }
assert (HW5 : rdword (aview tfxsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq2)].
intros i Hi. img_apply aview_same. img_apply MEQ4. rewrite unsigned_lit_small by img_lia. unfold RC_STK, RC_SCR, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (apply (icpt_ld8 W EE (set_regs_pc r1_4_e2 [((13%bv : bv 5), SOff 35 0)] (ss_pc r1_4_e2 + 4)) ms4 _ 14%bv 14%bv 472835 h2 36 56 HS4 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (Hrs2) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW5))|].
icpt_l1t_2 W5 c5 ms5 mat5 HS5 HM5 MEQ5 PSL5 MEQ4 PSL4 HW5 HS4.
eapply SRr_bind; [img_norm_st HS5 r_r1_4_3; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS5 r_r1_4_3))|].
icpt_l1t_0 W6 c6 ms6 mat6 HS6 HF6 HFr6 MEQ6 PSL6 MEQ5 PSL5 EE EE2.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_EQ (RG r1_4_e3 13) (SLit 0) HS6 (eq_trans (br_hull_eq EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (proj2 (Z.eqb_eq _ _) Hq))) as HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_r1_4z_0; img_try (img_apply (icpt_phase_to W EE RC_END _ _ _ _ _ HS6' r_r1_4z_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 PSL7 MEQ6 PSL6 EE EE2.
img_apply SRr_ret. img_apply (finishR EE r1_4z_e0 ms7 mat7 HS7 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EEreg).
- intros z Hz. img_apply MEQ7. unfold RC_SCR, RC_STK in *. img_lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
+
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_EQ (RG r1_4_e3 13) (SLit 0) HS6 (eq_trans (br_hull_eq EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (proj2 (Z.eqb_neq _ _) Hq))) as HS6'.
img_change (neg_bc BC_EQ) with BC_NE in HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_r1_4n_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS6' r_r1_4n_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 PSL7 MEQ6 PSL6 EE EE2.
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_EQ (RG r1_4n_e0 10) (SLit 0) HS7 (qc_flag_zero EE 4%nat 22 41 34 p n b1 EEP EEN E34 Hp ltac:(img_lia) Hpn ltac:(img_lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [img_norm_st HS7' r_r1_4n_1; img_try (img_apply (icpt_phase_to W EE RC_END _ _ _ _ _ HS7' r_r1_4n_1))|].
icpt_l1t_0 W8 c8 ms8 mat8 HS8 HF8 HFr8 MEQ8 PSL8 MEQ7 PSL7 EE EE2.
img_apply SRr_ret. img_apply (finishR EE r1_4n_e1 ms8 mat8 HS8 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EEreg).
- intros z Hz. img_apply MEQ8. unfold RC_SCR, RC_STK in *. img_lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
Qed.
Lemma path1_5 : n <= 64 -> g1 - g0 = 5 -> SRr tfxsegs W (cfg_at tfxsegs RC_ENTRY regs mem md) POSTr.
Proof.
intros Hn64' Ht. assert (Hn64 : 1 <= n <= 64) by img_lia.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
unfold cfg_at. img_change (w64 RC_ENTRY) with (Z_to_bv 64 RC_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 RC_ENTRY) mem (seg_rom tfxsegs)) z = mem z) by (img_try (intros; img_refl)).
assert (PSL0 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem (mkst regs (Z_to_bv 64 RC_ENTRY) mem (seg_rom tfxsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold RC_SCR, RC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(img_lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod p 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound p 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (p + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hg1hi : g1 < 2 ^ 44) by img_lia.
destruct (ra_last (aview tfxsegs H mem) p n HRA ltac:(img_lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
pose proof HHULL as HH.
set (h1 := (g0 + 2147450880) / 8 * 8). set (h2 := (g1 + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0 + 2147450880 < h1 + 8) by (img_try ((subst h1; cbv beta); pose proof (Z.div_mod (g0 + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g0 + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh2 : h2 <= g1 + 2147450880 < h2 + 8) by (img_try ((subst h2; cbv beta); pose proof (Z.div_mod (g1 + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g1 + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh12 : h1 <= h2) by (img_try ((subst h1 h2; cbv beta); img_apply Z.mul_le_mono_nonneg_r; [img_lia|]; img_apply Z.div_le_mono; img_lia)).
assert (Hsh1 : shadow_addr p / 8 * 8 = h1) by (img_try ((subst h1; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g0; cbv beta); f_equal; f_equal; img_lia)).
assert (Hsh2 : shadow_addr (p + n - 1) / 8 * 8 = h2) by (img_try ((subst h2; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g1; cbv beta); f_equal; f_equal; img_lia)).
destruct (hull_rdword H mem p n h1 HH ltac:(img_lia) ltac:(img_lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem p n h2 HH ltac:(img_lia) ltac:(img_lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (img_try (intros; img_apply Env_reg; assumption)).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EE2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EEP. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as EEN. fold EE in EE2, EEP, EEN.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (img_try (img_apply (Env_x _ 3); img_refl)).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (img_try (img_apply (Env_x _ 4); img_refl)).
pose proof (ent1_5 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [img_norm_st HS0 r_r1_5_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS0 r_r1_5_0))|].
icpt_l1t_0 W1 c1 ms1 mat1 HS1 HF1 HFr1 MEQ1 PSL1 MEQ0 PSL0 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_LTU (RG r1_5_e0 10) (RG r1_5_e0 23) HS1 (br_ovf_false EE 22 41 p n EEP EEN ltac:(img_lia) ltac:(img_lia))) as HS1'.
img_change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [img_norm_st HS1' r_r1_5_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS1' r_r1_5_1))|].
icpt_l1t_0 W2 c2 ms2 mat2 HS2 HF2 HFr2 MEQ2 PSL2 MEQ1 PSL1 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG r1_5_e1 11) (RG r1_5_e1 10) HS2 (br_cls65_small EE 41 n EEN Hn64)) as HS2'.
img_change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_r1_5_2; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS2' r_r1_5_2))|].
icpt_l1t_0 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 PSL3 MEQ2 PSL2 EE EE2.
assert (HW4 : rdword (aview tfxsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq1)].
intros i Hi. img_apply aview_same. img_apply MEQ3. rewrite unsigned_lit_small by img_lia. unfold RC_STK, RC_SCR, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (img_apply (icpt_ld8 W EE (r1_5_e2) ms3 _ 13%bv 13%bv 439939 h1 35 56 HS3 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (U_hull_addr EE 32 g0 2147450880 E32 ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW4))|].
icpt_l1t_2 W4 c4 ms4 mat4 HS4 HM4 MEQ4 PSL4 MEQ3 PSL3 HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450885) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450885 E32) by img_lia. f_equal. (subst h2; cbv beta). replace (g0 + 2147450885) with (g1 + 2147450880) by img_lia. img_refl. }
assert (HW5 : rdword (aview tfxsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq2)].
intros i Hi. img_apply aview_same. img_apply MEQ4. rewrite unsigned_lit_small by img_lia. unfold RC_STK, RC_SCR, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (apply (icpt_ld8 W EE (set_regs_pc r1_5_e2 [((13%bv : bv 5), SOff 35 0)] (ss_pc r1_5_e2 + 4)) ms4 _ 14%bv 14%bv 472835 h2 36 56 HS4 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (Hrs2) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW5))|].
icpt_l1t_2 W5 c5 ms5 mat5 HS5 HM5 MEQ5 PSL5 MEQ4 PSL4 HW5 HS4.
eapply SRr_bind; [img_norm_st HS5 r_r1_5_3; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS5 r_r1_5_3))|].
icpt_l1t_0 W6 c6 ms6 mat6 HS6 HF6 HFr6 MEQ6 PSL6 MEQ5 PSL5 EE EE2.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_EQ (RG r1_5_e3 13) (SLit 0) HS6 (eq_trans (br_hull_eq EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (proj2 (Z.eqb_eq _ _) Hq))) as HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_r1_5z_0; img_try (img_apply (icpt_phase_to W EE RC_END _ _ _ _ _ HS6' r_r1_5z_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 PSL7 MEQ6 PSL6 EE EE2.
img_apply SRr_ret. img_apply (finishR EE r1_5z_e0 ms7 mat7 HS7 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EEreg).
- intros z Hz. img_apply MEQ7. unfold RC_SCR, RC_STK in *. img_lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
+
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_EQ (RG r1_5_e3 13) (SLit 0) HS6 (eq_trans (br_hull_eq EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (proj2 (Z.eqb_neq _ _) Hq))) as HS6'.
img_change (neg_bc BC_EQ) with BC_NE in HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_r1_5n_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS6' r_r1_5n_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 PSL7 MEQ6 PSL6 EE EE2.
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_EQ (RG r1_5n_e0 10) (SLit 0) HS7 (qc_flag_zero EE 5%nat 22 41 34 p n b1 EEP EEN E34 Hp ltac:(img_lia) Hpn ltac:(img_lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [img_norm_st HS7' r_r1_5n_1; img_try (img_apply (icpt_phase_to W EE RC_END _ _ _ _ _ HS7' r_r1_5n_1))|].
icpt_l1t_0 W8 c8 ms8 mat8 HS8 HF8 HFr8 MEQ8 PSL8 MEQ7 PSL7 EE EE2.
img_apply SRr_ret. img_apply (finishR EE r1_5n_e1 ms8 mat8 HS8 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EEreg).
- intros z Hz. img_apply MEQ8. unfold RC_SCR, RC_STK in *. img_lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
Qed.
Lemma path1_6 : n <= 64 -> g1 - g0 = 6 -> SRr tfxsegs W (cfg_at tfxsegs RC_ENTRY regs mem md) POSTr.
Proof.
intros Hn64' Ht. assert (Hn64 : 1 <= n <= 64) by img_lia.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
unfold cfg_at. img_change (w64 RC_ENTRY) with (Z_to_bv 64 RC_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 RC_ENTRY) mem (seg_rom tfxsegs)) z = mem z) by (img_try (intros; img_refl)).
assert (PSL0 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem (mkst regs (Z_to_bv 64 RC_ENTRY) mem (seg_rom tfxsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold RC_SCR, RC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(img_lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod p 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound p 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (p + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hg1hi : g1 < 2 ^ 44) by img_lia.
destruct (ra_last (aview tfxsegs H mem) p n HRA ltac:(img_lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
pose proof HHULL as HH.
set (h1 := (g0 + 2147450880) / 8 * 8). set (h2 := (g1 + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0 + 2147450880 < h1 + 8) by (img_try ((subst h1; cbv beta); pose proof (Z.div_mod (g0 + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g0 + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh2 : h2 <= g1 + 2147450880 < h2 + 8) by (img_try ((subst h2; cbv beta); pose proof (Z.div_mod (g1 + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g1 + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh12 : h1 <= h2) by (img_try ((subst h1 h2; cbv beta); img_apply Z.mul_le_mono_nonneg_r; [img_lia|]; img_apply Z.div_le_mono; img_lia)).
assert (Hsh1 : shadow_addr p / 8 * 8 = h1) by (img_try ((subst h1; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g0; cbv beta); f_equal; f_equal; img_lia)).
assert (Hsh2 : shadow_addr (p + n - 1) / 8 * 8 = h2) by (img_try ((subst h2; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g1; cbv beta); f_equal; f_equal; img_lia)).
destruct (hull_rdword H mem p n h1 HH ltac:(img_lia) ltac:(img_lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem p n h2 HH ltac:(img_lia) ltac:(img_lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (img_try (intros; img_apply Env_reg; assumption)).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EE2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EEP. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as EEN. fold EE in EE2, EEP, EEN.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (img_try (img_apply (Env_x _ 3); img_refl)).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (img_try (img_apply (Env_x _ 4); img_refl)).
pose proof (ent1_6 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [img_norm_st HS0 r_r1_6_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS0 r_r1_6_0))|].
icpt_l1t_0 W1 c1 ms1 mat1 HS1 HF1 HFr1 MEQ1 PSL1 MEQ0 PSL0 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_LTU (RG r1_6_e0 10) (RG r1_6_e0 23) HS1 (br_ovf_false EE 22 41 p n EEP EEN ltac:(img_lia) ltac:(img_lia))) as HS1'.
img_change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [img_norm_st HS1' r_r1_6_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS1' r_r1_6_1))|].
icpt_l1t_0 W2 c2 ms2 mat2 HS2 HF2 HFr2 MEQ2 PSL2 MEQ1 PSL1 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG r1_6_e1 11) (RG r1_6_e1 10) HS2 (br_cls65_small EE 41 n EEN Hn64)) as HS2'.
img_change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_r1_6_2; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS2' r_r1_6_2))|].
icpt_l1t_0 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 PSL3 MEQ2 PSL2 EE EE2.
assert (HW4 : rdword (aview tfxsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq1)].
intros i Hi. img_apply aview_same. img_apply MEQ3. rewrite unsigned_lit_small by img_lia. unfold RC_STK, RC_SCR, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (img_apply (icpt_ld8 W EE (r1_6_e2) ms3 _ 13%bv 13%bv 439939 h1 35 56 HS3 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (U_hull_addr EE 32 g0 2147450880 E32 ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW4))|].
icpt_l1t_2 W4 c4 ms4 mat4 HS4 HM4 MEQ4 PSL4 MEQ3 PSL3 HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450886) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450886 E32) by img_lia. f_equal. (subst h2; cbv beta). replace (g0 + 2147450886) with (g1 + 2147450880) by img_lia. img_refl. }
assert (HW5 : rdword (aview tfxsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq2)].
intros i Hi. img_apply aview_same. img_apply MEQ4. rewrite unsigned_lit_small by img_lia. unfold RC_STK, RC_SCR, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (apply (icpt_ld8 W EE (set_regs_pc r1_6_e2 [((13%bv : bv 5), SOff 35 0)] (ss_pc r1_6_e2 + 4)) ms4 _ 14%bv 14%bv 472835 h2 36 56 HS4 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (Hrs2) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW5))|].
icpt_l1t_2 W5 c5 ms5 mat5 HS5 HM5 MEQ5 PSL5 MEQ4 PSL4 HW5 HS4.
eapply SRr_bind; [img_norm_st HS5 r_r1_6_3; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS5 r_r1_6_3))|].
icpt_l1t_0 W6 c6 ms6 mat6 HS6 HF6 HFr6 MEQ6 PSL6 MEQ5 PSL5 EE EE2.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_EQ (RG r1_6_e3 13) (SLit 0) HS6 (eq_trans (br_hull_eq EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (proj2 (Z.eqb_eq _ _) Hq))) as HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_r1_6z_0; img_try (img_apply (icpt_phase_to W EE RC_END _ _ _ _ _ HS6' r_r1_6z_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 PSL7 MEQ6 PSL6 EE EE2.
img_apply SRr_ret. img_apply (finishR EE r1_6z_e0 ms7 mat7 HS7 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EEreg).
- intros z Hz. img_apply MEQ7. unfold RC_SCR, RC_STK in *. img_lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
+
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_EQ (RG r1_6_e3 13) (SLit 0) HS6 (eq_trans (br_hull_eq EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (proj2 (Z.eqb_neq _ _) Hq))) as HS6'.
img_change (neg_bc BC_EQ) with BC_NE in HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_r1_6n_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS6' r_r1_6n_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 PSL7 MEQ6 PSL6 EE EE2.
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_EQ (RG r1_6n_e0 10) (SLit 0) HS7 (qc_flag_zero EE 6%nat 22 41 34 p n b1 EEP EEN E34 Hp ltac:(img_lia) Hpn ltac:(img_lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [img_norm_st HS7' r_r1_6n_1; img_try (img_apply (icpt_phase_to W EE RC_END _ _ _ _ _ HS7' r_r1_6n_1))|].
icpt_l1t_0 W8 c8 ms8 mat8 HS8 HF8 HFr8 MEQ8 PSL8 MEQ7 PSL7 EE EE2.
img_apply SRr_ret. img_apply (finishR EE r1_6n_e1 ms8 mat8 HS8 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EEreg).
- intros z Hz. img_apply MEQ8. unfold RC_SCR, RC_STK in *. img_lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
Qed.
Lemma path1_7 : n <= 64 -> g1 - g0 = 7 -> SRr tfxsegs W (cfg_at tfxsegs RC_ENTRY regs mem md) POSTr.
Proof.
intros Hn64' Ht. assert (Hn64 : 1 <= n <= 64) by img_lia.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
unfold cfg_at. img_change (w64 RC_ENTRY) with (Z_to_bv 64 RC_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 RC_ENTRY) mem (seg_rom tfxsegs)) z = mem z) by (img_try (intros; img_refl)).
assert (PSL0 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem (mkst regs (Z_to_bv 64 RC_ENTRY) mem (seg_rom tfxsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold RC_SCR, RC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(img_lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod p 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound p 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (p + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hg1hi : g1 < 2 ^ 44) by img_lia.
destruct (ra_last (aview tfxsegs H mem) p n HRA ltac:(img_lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
pose proof HHULL as HH.
set (h1 := (g0 + 2147450880) / 8 * 8). set (h2 := (g1 + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0 + 2147450880 < h1 + 8) by (img_try ((subst h1; cbv beta); pose proof (Z.div_mod (g0 + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g0 + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh2 : h2 <= g1 + 2147450880 < h2 + 8) by (img_try ((subst h2; cbv beta); pose proof (Z.div_mod (g1 + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g1 + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh12 : h1 <= h2) by (img_try ((subst h1 h2; cbv beta); img_apply Z.mul_le_mono_nonneg_r; [img_lia|]; img_apply Z.div_le_mono; img_lia)).
assert (Hsh1 : shadow_addr p / 8 * 8 = h1) by (img_try ((subst h1; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g0; cbv beta); f_equal; f_equal; img_lia)).
assert (Hsh2 : shadow_addr (p + n - 1) / 8 * 8 = h2) by (img_try ((subst h2; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g1; cbv beta); f_equal; f_equal; img_lia)).
destruct (hull_rdword H mem p n h1 HH ltac:(img_lia) ltac:(img_lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem p n h2 HH ltac:(img_lia) ltac:(img_lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (img_try (intros; img_apply Env_reg; assumption)).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EE2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EEP. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as EEN. fold EE in EE2, EEP, EEN.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (img_try (img_apply (Env_x _ 3); img_refl)).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (img_try (img_apply (Env_x _ 4); img_refl)).
pose proof (ent1_7 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [img_norm_st HS0 r_r1_7_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS0 r_r1_7_0))|].
icpt_l1t_0 W1 c1 ms1 mat1 HS1 HF1 HFr1 MEQ1 PSL1 MEQ0 PSL0 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_LTU (RG r1_7_e0 10) (RG r1_7_e0 23) HS1 (br_ovf_false EE 22 41 p n EEP EEN ltac:(img_lia) ltac:(img_lia))) as HS1'.
img_change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [img_norm_st HS1' r_r1_7_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS1' r_r1_7_1))|].
icpt_l1t_0 W2 c2 ms2 mat2 HS2 HF2 HFr2 MEQ2 PSL2 MEQ1 PSL1 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG r1_7_e1 11) (RG r1_7_e1 10) HS2 (br_cls65_small EE 41 n EEN Hn64)) as HS2'.
img_change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_r1_7_2; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS2' r_r1_7_2))|].
icpt_l1t_0 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 PSL3 MEQ2 PSL2 EE EE2.
assert (HW4 : rdword (aview tfxsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq1)].
intros i Hi. img_apply aview_same. img_apply MEQ3. rewrite unsigned_lit_small by img_lia. unfold RC_STK, RC_SCR, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (img_apply (icpt_ld8 W EE (r1_7_e2) ms3 _ 13%bv 13%bv 439939 h1 35 56 HS3 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (U_hull_addr EE 32 g0 2147450880 E32 ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW4))|].
icpt_l1t_2 W4 c4 ms4 mat4 HS4 HM4 MEQ4 PSL4 MEQ3 PSL3 HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450887) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450887 E32) by img_lia. f_equal. (subst h2; cbv beta). replace (g0 + 2147450887) with (g1 + 2147450880) by img_lia. img_refl. }
assert (HW5 : rdword (aview tfxsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq2)].
intros i Hi. img_apply aview_same. img_apply MEQ4. rewrite unsigned_lit_small by img_lia. unfold RC_STK, RC_SCR, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (apply (icpt_ld8 W EE (set_regs_pc r1_7_e2 [((13%bv : bv 5), SOff 35 0)] (ss_pc r1_7_e2 + 4)) ms4 _ 14%bv 14%bv 472835 h2 36 56 HS4 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (Hrs2) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW5))|].
icpt_l1t_2 W5 c5 ms5 mat5 HS5 HM5 MEQ5 PSL5 MEQ4 PSL4 HW5 HS4.
eapply SRr_bind; [img_norm_st HS5 r_r1_7_3; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS5 r_r1_7_3))|].
icpt_l1t_0 W6 c6 ms6 mat6 HS6 HF6 HFr6 MEQ6 PSL6 MEQ5 PSL5 EE EE2.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_EQ (RG r1_7_e3 13) (SLit 0) HS6 (eq_trans (br_hull_eq EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (proj2 (Z.eqb_eq _ _) Hq))) as HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_r1_7z_0; img_try (img_apply (icpt_phase_to W EE RC_END _ _ _ _ _ HS6' r_r1_7z_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 PSL7 MEQ6 PSL6 EE EE2.
img_apply SRr_ret. img_apply (finishR EE r1_7z_e0 ms7 mat7 HS7 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EEreg).
- intros z Hz. img_apply MEQ7. unfold RC_SCR, RC_STK in *. img_lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
+
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_EQ (RG r1_7_e3 13) (SLit 0) HS6 (eq_trans (br_hull_eq EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (proj2 (Z.eqb_neq _ _) Hq))) as HS6'.
img_change (neg_bc BC_EQ) with BC_NE in HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_r1_7n_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS6' r_r1_7n_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 PSL7 MEQ6 PSL6 EE EE2.
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_EQ (RG r1_7n_e0 10) (SLit 0) HS7 (qc_flag_zero EE 7%nat 22 41 34 p n b1 EEP EEN E34 Hp ltac:(img_lia) Hpn ltac:(img_lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [img_norm_st HS7' r_r1_7n_1; img_try (img_apply (icpt_phase_to W EE RC_END _ _ _ _ _ HS7' r_r1_7n_1))|].
icpt_l1t_0 W8 c8 ms8 mat8 HS8 HF8 HFr8 MEQ8 PSL8 MEQ7 PSL7 EE EE2.
img_apply SRr_ret. img_apply (finishR EE r1_7n_e1 ms8 mat8 HS8 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EEreg).
- intros z Hz. img_apply MEQ8. unfold RC_SCR, RC_STK in *. img_lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
Qed.
Lemma path1_8 : n <= 64 -> g1 - g0 = 8 -> SRr tfxsegs W (cfg_at tfxsegs RC_ENTRY regs mem md) POSTr.
Proof.
intros Hn64' Ht. assert (Hn64 : 1 <= n <= 64) by img_lia.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
unfold cfg_at. img_change (w64 RC_ENTRY) with (Z_to_bv 64 RC_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 RC_ENTRY) mem (seg_rom tfxsegs)) z = mem z) by (img_try (intros; img_refl)).
assert (PSL0 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem (mkst regs (Z_to_bv 64 RC_ENTRY) mem (seg_rom tfxsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold RC_SCR, RC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(img_lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod p 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound p 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (p + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hg1hi : g1 < 2 ^ 44) by img_lia.
destruct (ra_last (aview tfxsegs H mem) p n HRA ltac:(img_lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
pose proof HHULL as HH.
set (h1 := (g0 + 2147450880) / 8 * 8). set (h2 := (g1 + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0 + 2147450880 < h1 + 8) by (img_try ((subst h1; cbv beta); pose proof (Z.div_mod (g0 + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g0 + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh2 : h2 <= g1 + 2147450880 < h2 + 8) by (img_try ((subst h2; cbv beta); pose proof (Z.div_mod (g1 + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g1 + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh12 : h1 <= h2) by (img_try ((subst h1 h2; cbv beta); img_apply Z.mul_le_mono_nonneg_r; [img_lia|]; img_apply Z.div_le_mono; img_lia)).
assert (Hsh1 : shadow_addr p / 8 * 8 = h1) by (img_try ((subst h1; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g0; cbv beta); f_equal; f_equal; img_lia)).
assert (Hsh2 : shadow_addr (p + n - 1) / 8 * 8 = h2) by (img_try ((subst h2; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g1; cbv beta); f_equal; f_equal; img_lia)).
destruct (hull_rdword H mem p n h1 HH ltac:(img_lia) ltac:(img_lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem p n h2 HH ltac:(img_lia) ltac:(img_lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (img_try (intros; img_apply Env_reg; assumption)).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EE2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EEP. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as EEN. fold EE in EE2, EEP, EEN.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (img_try (img_apply (Env_x _ 3); img_refl)).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (img_try (img_apply (Env_x _ 4); img_refl)).
pose proof (ent1_8 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [img_norm_st HS0 r_r1_8_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS0 r_r1_8_0))|].
icpt_l1t_0 W1 c1 ms1 mat1 HS1 HF1 HFr1 MEQ1 PSL1 MEQ0 PSL0 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_LTU (RG r1_8_e0 10) (RG r1_8_e0 23) HS1 (br_ovf_false EE 22 41 p n EEP EEN ltac:(img_lia) ltac:(img_lia))) as HS1'.
img_change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [img_norm_st HS1' r_r1_8_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS1' r_r1_8_1))|].
icpt_l1t_0 W2 c2 ms2 mat2 HS2 HF2 HFr2 MEQ2 PSL2 MEQ1 PSL1 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG r1_8_e1 11) (RG r1_8_e1 10) HS2 (br_cls65_small EE 41 n EEN Hn64)) as HS2'.
img_change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_r1_8_2; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS2' r_r1_8_2))|].
icpt_l1t_0 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 PSL3 MEQ2 PSL2 EE EE2.
assert (HW4 : rdword (aview tfxsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq1)].
intros i Hi. img_apply aview_same. img_apply MEQ3. rewrite unsigned_lit_small by img_lia. unfold RC_STK, RC_SCR, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (img_apply (icpt_ld8 W EE (r1_8_e2) ms3 _ 13%bv 13%bv 439939 h1 35 56 HS3 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (U_hull_addr EE 32 g0 2147450880 E32 ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW4))|].
icpt_l1t_2 W4 c4 ms4 mat4 HS4 HM4 MEQ4 PSL4 MEQ3 PSL3 HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450888) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450888 E32) by img_lia. f_equal. (subst h2; cbv beta). replace (g0 + 2147450888) with (g1 + 2147450880) by img_lia. img_refl. }
assert (HW5 : rdword (aview tfxsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq2)].
intros i Hi. img_apply aview_same. img_apply MEQ4. rewrite unsigned_lit_small by img_lia. unfold RC_STK, RC_SCR, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (apply (icpt_ld8 W EE (set_regs_pc r1_8_e2 [((13%bv : bv 5), SOff 35 0)] (ss_pc r1_8_e2 + 4)) ms4 _ 14%bv 14%bv 472835 h2 36 56 HS4 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (Hrs2) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW5))|].
icpt_l1t_2 W5 c5 ms5 mat5 HS5 HM5 MEQ5 PSL5 MEQ4 PSL4 HW5 HS4.
eapply SRr_bind; [img_norm_st HS5 r_r1_8_3; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS5 r_r1_8_3))|].
icpt_l1t_0 W6 c6 ms6 mat6 HS6 HF6 HFr6 MEQ6 PSL6 MEQ5 PSL5 EE EE2.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_EQ (RG r1_8_e3 13) (SLit 0) HS6 (eq_trans (br_hull_eq EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (proj2 (Z.eqb_eq _ _) Hq))) as HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_r1_8z_0; img_try (img_apply (icpt_phase_to W EE RC_END _ _ _ _ _ HS6' r_r1_8z_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 PSL7 MEQ6 PSL6 EE EE2.
img_apply SRr_ret. img_apply (finishR EE r1_8z_e0 ms7 mat7 HS7 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EEreg).
- intros z Hz. img_apply MEQ7. unfold RC_SCR, RC_STK in *. img_lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
+
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_EQ (RG r1_8_e3 13) (SLit 0) HS6 (eq_trans (br_hull_eq EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (proj2 (Z.eqb_neq _ _) Hq))) as HS6'.
img_change (neg_bc BC_EQ) with BC_NE in HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_r1_8n_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS6' r_r1_8n_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 PSL7 MEQ6 PSL6 EE EE2.
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_EQ (RG r1_8n_e0 10) (SLit 0) HS7 (qc_flag_zero EE 8%nat 22 41 34 p n b1 EEP EEN E34 Hp ltac:(img_lia) Hpn ltac:(img_lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [img_norm_st HS7' r_r1_8n_1; img_try (img_apply (icpt_phase_to W EE RC_END _ _ _ _ _ HS7' r_r1_8n_1))|].
icpt_l1t_0 W8 c8 ms8 mat8 HS8 HF8 HFr8 MEQ8 PSL8 MEQ7 PSL7 EE EE2.
img_apply SRr_ret. img_apply (finishR EE r1_8n_e1 ms8 mat8 HS8 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EEreg).
- intros z Hz. img_apply MEQ8. unfold RC_SCR, RC_STK in *. img_lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
Qed.
Lemma path2L : 64 < n -> p + n <= kLowMemEnd - 1 -> SRr tfxsegs W (cfg_at tfxsegs RC_ENTRY regs mem md) POSTr.
Proof.
intros Hn64 Hrg.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
unfold cfg_at. img_change (w64 RC_ENTRY) with (Z_to_bv 64 RC_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 RC_ENTRY) mem (seg_rom tfxsegs)) z = mem z) by (img_try (intros; img_refl)).
assert (PSL0 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem (mkst regs (Z_to_bv 64 RC_ENTRY) mem (seg_rom tfxsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold RC_SCR, RC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(img_lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
pose proof Hrg as Hrg'. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg'.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod p 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound p 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (p + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hg1hi : g1 < 2 ^ 44) by img_lia.
destruct (ra_last (aview tfxsegs H mem) p n HRA ltac:(img_lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hgu : 8 * gu <= p + 7 < 8 * gu + 8 /\ du = 8 * gu) by (img_try ((subst gu du; cbv beta); pose proof (Z.div_mod (p + 7) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (p + 7) 8 ltac:(img_lia)); img_lia)).
assert (Hge : 8 * ge <= p + n < 8 * ge + 8 /\ de = 8 * ge) by (img_try ((subst ge de; cbv beta); pose proof (Z.div_mod (p + n) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (p + n) 8 ltac:(img_lia)); img_lia)).
set (EE := Env [g0; g1; b1; 0; 0; du; de; gu; ge; n]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (img_try (intros; img_apply Env_reg; assumption)).
pose proof (Env2 [g0; g1; b1; 0; 0; du; de; gu; ge; n]) as EE2. pose proof (EnvP [g0; g1; b1; 0; 0; du; de; gu; ge; n]) as EEP. pose proof (EnvN [g0; g1; b1; 0; 0; du; de; gu; ge; n] eq_refl) as EEN. fold EE in EE2, EEP, EEN.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E33 : ew EE 33 = Z_to_bv 64 g1) by (img_try (img_apply (Env_x _ 1); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
assert (E39 : ew EE 39 = Z_to_bv 64 gu) by (img_try (img_apply (Env_x _ 7); img_refl)).
assert (E40 : ew EE 40 = Z_to_bv 64 ge) by (img_try (img_apply (Env_x _ 8); img_refl)).
assert (E32u : bv_unsigned (ew EE 32) = g0) by (img_try (rewrite E32; img_apply unsigned_lit_small; img_lia)).
assert (E33u : bv_unsigned (ew EE 33) = g1) by (img_try (rewrite E33; img_apply unsigned_lit_small; img_lia)).
pose proof (ent2L b1 Hn64 Hrg Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [img_norm_st HS0 r_r2L_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS0 r_r2L_0))|].
icpt_l1t_0 W1 c1 ms1 mat1 HS1 HF1 HFr1 MEQ1 PSL1 MEQ0 PSL0 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_LTU (RG r2L_e0 10) (RG r2L_e0 23) HS1 (br_ovf_false EE 22 41 p n EEP EEN ltac:(img_lia) ltac:(img_lia))) as HS1'.
img_change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [img_norm_st HS1' r_r2L_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS1' r_r2L_1))|].
icpt_l1t_0 W2 c2 ms2 mat2 HS2 HF2 HFr2 MEQ2 PSL2 MEQ1 PSL1 EE EE2.
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_GEU (SLit 2147450879) (RG r2L_e1 18) HS2 (br_end_low EE 22 41 p n EEP EEN Hp ltac:(img_lia) ltac:(img_try (unfold kLowMemEnd in *; img_lia)))) as HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_r2L_2; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS2' r_r2L_2))|].
icpt_l1t_0 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 PSL3 MEQ2 PSL2 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG r2L_e2 8) (RG r2L_e2 18) HS3 (br_beg_lt_end EE 22 41 p n EEP EEN Hp ltac:(img_lia) ltac:(img_lia))) as HS3'.
img_change (neg_bc BC_GEU) with BC_LTU in HS3'. clear HS3.
eapply SRr_bind; [img_norm_st HS3' r_r2L_3; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS3' r_r2L_3))|].
icpt_l1t_0 W4 c4 ms4 mat4 HS4 HF4 HFr4 MEQ4 PSL4 MEQ3 PSL3 EE EE2.
destruct (Z.eq_dec b1 0) as [Hbz|Hbz].
+
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_EQ (RG r2L_e3 11) (SLit 0) HS4 (rp_b1_zero EE 34 ltac:(img_try (rewrite E34, Hbz; img_refl)))) as HS4'. clear HS4.
eapply SRr_bind; [img_norm_st HS4' r_r2Lz_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS4' r_r2Lz_0))|].
icpt_l1t_0 W5 c5 ms5 mat5 HS5 HF5 HFr5 MEQ5 PSL5 MEQ4 PSL4 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG r2Lz_e0 19) (RG r2Lz_e0 10) HS5 (br_sbeg_lt_send EE 39 40 gu ge E39 E40 ltac:(img_lia) ltac:(img_try (unfold SB; img_lia)))) as HS5'.
img_change (neg_bc BC_GEU) with BC_LTU in HS5'. clear HS5.
eapply SRr_bind; [img_norm_st HS5' r_r2Lz_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS5' r_r2Lz_1))|].
icpt_l1t_0 W6 c6 ms6 mat6 HS6 HF6 HFr6 MEQ6 PSL6 MEQ5 PSL5 EE EE2.
assert (SLW : forall z, sp0 - 64 - 8 <= z < sp0 - 64 -> writable_at tfxsegs (mrestrict H (ms_mem ms6)) z).
{ intros z Hz. img_apply YF8r.apresent_writable; [img_try (unfold YF8r.TFX_IMG_END, kHighMemBeg in *; img_lia)|]. unfold RC_SCR, RC_STK in *.
destruct (ms_mem ms6 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| img_try (exfalso; img_exact (PSL6 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
split; [img_try (img_exact (proj1 (Bpres z ltac:(img_lia)))) | img_try (exists b; img_exact Eb)]. }
assert (SZERO : forall a, gu + SB <= a < gu + SB + (ge - gu) -> aview tfxsegs H (ms_mem ms6) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms6) a) by (img_try (img_apply MEQ6; rewrite unsigned_lit_small by img_lia; unfold RC_STK, RC_SCR, kHighMemBeg in *; img_lia)).
replace a with (SB + (a - SB)) by img_lia. img_apply (ra_granule_zero (aview tfxsegs H mem) p n (a - SB) HRA); [img_try (unfold SB in *; img_lia) | img_try (img_exact Hp)]. }
assert (R10 : sv_denot EE (RG r2Lz_e1 10) = Z_to_bv 64 (gu + SB)).
{ img_change (sv_denot EE (RG r2Lz_e1 10)) with (sv_denot EE (SOff 39 SB)). cbn [sv_denot]. rewrite E39, unsigned_lit_small by img_lia. img_refl. }
assert (R11 : sv_denot EE (RG r2Lz_e1 11) = Z_to_bv 64 (ge - gu)).
{ img_change (sv_denot EE (RG r2Lz_e1 11)) with (sv_denot EE (SAlu ALU_ADD (SMd M_MUL (SOff 39 0) (SLit (-1))) (SOff 40 0))). img_exact (U_mz_len EE 39 40 gu ge E39 E40 ltac:(img_lia) ltac:(img_lia)). }
assert (R2 : sv_denot EE (RG r2Lz_e1 2) = Z_to_bv 64 (sp0 - 64)).
{ img_change (sv_denot EE (RG r2Lz_e1 2)) with (sv_denot EE (SOff 2 (-64))). cbn [sv_denot]. rewrite EE2. f_equal; img_lia. }
assert (R1 : sv_denot EE (RG r2Lz_e1 1) = Z_to_bv 64 (347624 + D_2c4)).
{ img_change (sv_denot EE (RG r2Lz_e1 1)) with (sv_denot EE (SLit (347624 + D_2c4))). img_apply bv_eq. img_case; vm_compute. all: img_refl. }
assert (HOFF : Forall (fun r => 0 <= base_val EE (YQ0b.r_base r) + YQ0b.r_lo r /\ base_val EE (YQ0b.r_base r) + YQ0b.r_hi r <= 2 ^ 64 /\
(base_val EE (YQ0b.r_base r) + YQ0b.r_hi r <= sp0 - 64 - 8 \/ sp0 - 64 <= base_val EE (YQ0b.r_base r) + YQ0b.r_lo r) /\
YQ0b.r_lo r <= YQ0b.r_wlo r /\ YQ0b.r_whi r <= YQ0b.r_hi r) (ss_mem r2Lz_e1)).
{ cbn [ss_mem r2Lz_e1]. repeat (img_apply Forall_cons); try img_apply Forall_nil.
all: cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite ?EE2, ?E32u, ?E33u; unfold RC_STK, SB, kHighMemBeg in *; repeat split; img_lia. }
eapply SRr_bind; [img_try (img_exact (icpt_memisz W EE r2Lz_e1 ms6 _ 56 (ss_mem r2Lz_e1) (gu + SB) (ge - gu) (sp0 - 64) (347624 + D_2c4) HS6 eq_refl eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) (submem_refl _)
R10 R11 R2 R1 ltac:(img_lia) ltac:(unfold SB; img_lia) ltac:(unfold SB, kHighMemBeg in *; img_lia) ltac:(unfold TFX_IMG_END, kHighMemBeg in *; img_lia) ltac:(img_lia)
(ret_ok_lit (347624 + D_2c4) ltac:(img_lia) ltac:(img_eqrefl_m)) ltac:(left; unfold SB, kHighMemBeg in *; img_lia) SLW SZERO HOFF))|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HM7 & HP7). rewrite ?wvb_wvb in *.
set (EE' := havoc EE 56 (map (getr (ms_regs ms7)) MZ_CLOB)) in HS7.
assert (EE'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE' i = getr regs r).
{ intros i r Hi. (subst EE'; cbv beta). rewrite ew_havoc_old by (img_try (pose proof (u5_range r); img_lia)). img_apply EEreg. img_exact Hi. }
assert (EE'2 : bv_unsigned (ew EE' 2) = sp0) by (img_try ((subst EE'; cbv beta); rewrite ew_havoc_old by img_lia; img_exact EE2)).
assert (EE'N : ew EE' 41 = Z_to_bv 64 n) by (img_try ((subst EE'; cbv beta); rewrite ew_havoc_old by img_lia; img_exact EEN)).
assert (MEQ7 : forall z : word, ~ (sp0 - RC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HM7 z) by (img_try (unfold RC_SCR in *; img_lia)). img_apply MEQ6. unfold RC_SCR, RC_STK in *. img_lia. }
assert (PSL7 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. img_apply HP7. unfold RC_SCR, RC_STK in *. img_lia. }
clear HM7 HP7 SLW SZERO R10 R11 R2 R1 HOFF HS6.
eapply SRr_bind; [img_norm_st HS7 r_r2Lz_2; img_try (img_apply (icpt_phase_to W EE' RC_END _ _ _ _ _ HS7 r_r2Lz_2))|].
icpt_l1t_1 W8 c8 ms8 mat8 HS8 HF8 HFr8 MEQ8 PSL8 MEQ7 PSL7 EE' EE'2.
img_apply SRr_ret. img_apply (finishR EE' r2Lz_e2 ms8 mat8 HS8 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EE'reg).
- intros z Hz. img_apply MEQ8. unfold RC_SCR, RC_STK in *. img_lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
+
assert (Hlt : (p + n - 1) mod 8 < b1 < 8) by (img_try (destruct Hok as [Hz0 | [Hlt Hb]]; [img_try (exfalso; img_exact (Hbz Hz0)) | img_lia])).
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_EQ (RG r2L_e3 11) (SLit 0) HS4 (rp_b1_nonzero EE 34 b1 E34 ltac:(img_lia))) as HS4'.
img_change (neg_bc BC_EQ) with BC_NE in HS4'. clear HS4.
eapply SRr_bind; [img_norm_st HS4' r_r2Ln_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS4' r_r2Ln_0))|].
icpt_l1t_0 W5 c5 ms5 mat5 HS5 HF5 HFr5 MEQ5 PSL5 MEQ4 PSL4 EE EE2.
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_LT (RG r2Ln_e0 12) (RG r2Ln_e0 11) HS5 (rp_blt_last EE 22 41 34 p n b1 EEP EEN E34 Hp ltac:(img_lia) Hpn Hlt)) as HS5'. clear HS5.
eapply SRr_bind; [img_norm_st HS5' r_r2Ln_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS5' r_r2Ln_1))|].
icpt_l1t_0 W6 c6 ms6 mat6 HS6 HF6 HFr6 MEQ6 PSL6 MEQ5 PSL5 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG r2Ln_e1 19) (RG r2Ln_e1 10) HS6 (br_sbeg_lt_send EE 39 40 gu ge E39 E40 ltac:(img_lia) ltac:(img_try (unfold SB; img_lia)))) as HS6'.
img_change (neg_bc BC_GEU) with BC_LTU in HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_r2Ln_2; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS6' r_r2Ln_2))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 PSL7 MEQ6 PSL6 EE EE2.
assert (SLW : forall z, sp0 - 64 - 8 <= z < sp0 - 64 -> writable_at tfxsegs (mrestrict H (ms_mem ms7)) z).
{ intros z Hz. img_apply YF8r.apresent_writable; [img_try (unfold YF8r.TFX_IMG_END, kHighMemBeg in *; img_lia)|]. unfold RC_SCR, RC_STK in *.
destruct (ms_mem ms7 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| img_try (exfalso; img_exact (PSL7 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
split; [img_try (img_exact (proj1 (Bpres z ltac:(img_lia)))) | img_try (exists b; img_exact Eb)]. }
assert (SZERO : forall a, gu + SB <= a < gu + SB + (ge - gu) -> aview tfxsegs H (ms_mem ms7) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms7) a) by (img_try (img_apply MEQ7; rewrite unsigned_lit_small by img_lia; unfold RC_STK, RC_SCR, kHighMemBeg in *; img_lia)).
replace a with (SB + (a - SB)) by img_lia. img_apply (ra_granule_zero (aview tfxsegs H mem) p n (a - SB) HRA); [img_try (unfold SB in *; img_lia) | img_try (img_exact Hp)]. }
assert (R10 : sv_denot EE (RG r2Ln_e2 10) = Z_to_bv 64 (gu + SB)).
{ img_change (sv_denot EE (RG r2Ln_e2 10)) with (sv_denot EE (SOff 39 SB)). cbn [sv_denot]. rewrite E39, unsigned_lit_small by img_lia. img_refl. }
assert (R11 : sv_denot EE (RG r2Ln_e2 11) = Z_to_bv 64 (ge - gu)).
{ img_change (sv_denot EE (RG r2Ln_e2 11)) with (sv_denot EE (SAlu ALU_ADD (SMd M_MUL (SOff 39 0) (SLit (-1))) (SOff 40 0))). img_exact (U_mz_len EE 39 40 gu ge E39 E40 ltac:(img_lia) ltac:(img_lia)). }
assert (R2 : sv_denot EE (RG r2Ln_e2 2) = Z_to_bv 64 (sp0 - 64)).
{ img_change (sv_denot EE (RG r2Ln_e2 2)) with (sv_denot EE (SOff 2 (-64))). cbn [sv_denot]. rewrite EE2. f_equal; img_lia. }
assert (R1 : sv_denot EE (RG r2Ln_e2 1) = Z_to_bv 64 (347624 + D_2c4)).
{ img_change (sv_denot EE (RG r2Ln_e2 1)) with (sv_denot EE (SLit (347624 + D_2c4))). img_apply bv_eq. img_case; vm_compute. all: img_refl. }
assert (HOFF : Forall (fun r => 0 <= base_val EE (YQ0b.r_base r) + YQ0b.r_lo r /\ base_val EE (YQ0b.r_base r) + YQ0b.r_hi r <= 2 ^ 64 /\
(base_val EE (YQ0b.r_base r) + YQ0b.r_hi r <= sp0 - 64 - 8 \/ sp0 - 64 <= base_val EE (YQ0b.r_base r) + YQ0b.r_lo r) /\
YQ0b.r_lo r <= YQ0b.r_wlo r /\ YQ0b.r_whi r <= YQ0b.r_hi r) (ss_mem r2Ln_e2)).
{ cbn [ss_mem r2Ln_e2]. repeat (img_apply Forall_cons); try img_apply Forall_nil.
all: cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite ?EE2, ?E32u, ?E33u; unfold RC_STK, SB, kHighMemBeg in *; repeat split; img_lia. }
eapply SRr_bind; [img_try (img_exact (icpt_memisz W EE r2Ln_e2 ms7 _ 56 (ss_mem r2Ln_e2) (gu + SB) (ge - gu) (sp0 - 64) (347624 + D_2c4) HS7 eq_refl eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) (submem_refl _)
R10 R11 R2 R1 ltac:(img_lia) ltac:(unfold SB; img_lia) ltac:(unfold SB, kHighMemBeg in *; img_lia) ltac:(unfold TFX_IMG_END, kHighMemBeg in *; img_lia) ltac:(img_lia)
(ret_ok_lit (347624 + D_2c4) ltac:(img_lia) ltac:(img_eqrefl_m)) ltac:(left; unfold SB, kHighMemBeg in *; img_lia) SLW SZERO HOFF))|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HM8 & HP8). rewrite ?wvb_wvb in *.
set (EE' := havoc EE 56 (map (getr (ms_regs ms8)) MZ_CLOB)) in HS8.
assert (EE'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE' i = getr regs r).
{ intros i r Hi. (subst EE'; cbv beta). rewrite ew_havoc_old by (img_try (pose proof (u5_range r); img_lia)). img_apply EEreg. img_exact Hi. }
assert (EE'2 : bv_unsigned (ew EE' 2) = sp0) by (img_try ((subst EE'; cbv beta); rewrite ew_havoc_old by img_lia; img_exact EE2)).
assert (EE'N : ew EE' 41 = Z_to_bv 64 n) by (img_try ((subst EE'; cbv beta); rewrite ew_havoc_old by img_lia; img_exact EEN)).
assert (MEQ8 : forall z : word, ~ (sp0 - RC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HM8 z) by (img_try (unfold RC_SCR in *; img_lia)). img_apply MEQ7. unfold RC_SCR, RC_STK in *. img_lia. }
assert (PSL8 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. img_apply HP8. unfold RC_SCR, RC_STK in *. img_lia. }
clear HM8 HP8 SLW SZERO R10 R11 R2 R1 HOFF HS7.
eapply SRr_bind; [img_norm_st HS8 r_r2Ln_3; img_try (img_apply (icpt_phase_to W EE' RC_END _ _ _ _ _ HS8 r_r2Ln_3))|].
icpt_l1t_1 W9 c9 ms9 mat9 HS9 HF9 HFr9 MEQ9 PSL9 MEQ8 PSL8 EE' EE'2.
img_apply SRr_ret. img_apply (finishR EE' r2Ln_e3 ms9 mat9 HS9 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EE'reg).
- intros z Hz. img_apply MEQ9. unfold RC_SCR, RC_STK in *. img_lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms9 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL9 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
Qed.
Lemma path2H : 64 < n -> kHighMemBeg <= p /\ p + n <= kHighMemEnd - 1 -> SRr tfxsegs W (cfg_at tfxsegs RC_ENTRY regs mem md) POSTr.
Proof.
intros Hn64 Hrg.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
unfold cfg_at. img_change (w64 RC_ENTRY) with (Z_to_bv 64 RC_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 RC_ENTRY) mem (seg_rom tfxsegs)) z = mem z) by (img_try (intros; img_refl)).
assert (PSL0 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem (mkst regs (Z_to_bv 64 RC_ENTRY) mem (seg_rom tfxsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold RC_SCR, RC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(img_lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
pose proof Hrg as Hrg'. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg'.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod p 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound p 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (p + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hg1hi : g1 < 2 ^ 44) by img_lia.
destruct (ra_last (aview tfxsegs H mem) p n HRA ltac:(img_lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hgu : 8 * gu <= p + 7 < 8 * gu + 8 /\ du = 8 * gu) by (img_try ((subst gu du; cbv beta); pose proof (Z.div_mod (p + 7) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (p + 7) 8 ltac:(img_lia)); img_lia)).
assert (Hge : 8 * ge <= p + n < 8 * ge + 8 /\ de = 8 * ge) by (img_try ((subst ge de; cbv beta); pose proof (Z.div_mod (p + n) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (p + n) 8 ltac:(img_lia)); img_lia)).
set (EE := Env [g0; g1; b1; 0; 0; du; de; gu; ge; n]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (img_try (intros; img_apply Env_reg; assumption)).
pose proof (Env2 [g0; g1; b1; 0; 0; du; de; gu; ge; n]) as EE2. pose proof (EnvP [g0; g1; b1; 0; 0; du; de; gu; ge; n]) as EEP. pose proof (EnvN [g0; g1; b1; 0; 0; du; de; gu; ge; n] eq_refl) as EEN. fold EE in EE2, EEP, EEN.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E33 : ew EE 33 = Z_to_bv 64 g1) by (img_try (img_apply (Env_x _ 1); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
assert (E39 : ew EE 39 = Z_to_bv 64 gu) by (img_try (img_apply (Env_x _ 7); img_refl)).
assert (E40 : ew EE 40 = Z_to_bv 64 ge) by (img_try (img_apply (Env_x _ 8); img_refl)).
assert (E32u : bv_unsigned (ew EE 32) = g0) by (img_try (rewrite E32; img_apply unsigned_lit_small; img_lia)).
assert (E33u : bv_unsigned (ew EE 33) = g1) by (img_try (rewrite E33; img_apply unsigned_lit_small; img_lia)).
pose proof (ent2H b1 Hn64 Hrg Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [img_norm_st HS0 r_r2H_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS0 r_r2H_0))|].
icpt_l1t_0 W1 c1 ms1 mat1 HS1 HF1 HFr1 MEQ1 PSL1 MEQ0 PSL0 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_LTU (RG r2H_e0 10) (RG r2H_e0 23) HS1 (br_ovf_false EE 22 41 p n EEP EEN ltac:(img_lia) ltac:(img_lia))) as HS1'.
img_change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [img_norm_st HS1' r_r2H_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS1' r_r2H_1))|].
icpt_l1t_0 W2 c2 ms2 mat2 HS2 HF2 HFr2 MEQ2 PSL2 MEQ1 PSL1 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_LTU (SLit 140737488355327) (RG r2H_e1 18) HS2 (br_end_high EE 22 41 p n EEP EEN Hp ltac:(img_lia) ltac:(img_try (unfold kHighMemEnd in *; img_lia)))) as HS2'.
img_change (neg_bc BC_LTU) with BC_GEU in HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_r2H_2; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS2' r_r2H_2))|].
icpt_l1t_0 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 PSL3 MEQ2 PSL2 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG r2H_e2 8) (RG r2H_e2 18) HS3 (br_beg_lt_end EE 22 41 p n EEP EEN Hp ltac:(img_lia) ltac:(img_lia))) as HS3'.
img_change (neg_bc BC_GEU) with BC_LTU in HS3'. clear HS3.
eapply SRr_bind; [img_norm_st HS3' r_r2H_3; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS3' r_r2H_3))|].
icpt_l1t_0 W4 c4 ms4 mat4 HS4 HF4 HFr4 MEQ4 PSL4 MEQ3 PSL3 EE EE2.
destruct (Z.eq_dec b1 0) as [Hbz|Hbz].
+
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_EQ (RG r2H_e3 11) (SLit 0) HS4 (rp_b1_zero EE 34 ltac:(img_try (rewrite E34, Hbz; img_refl)))) as HS4'. clear HS4.
eapply SRr_bind; [img_norm_st HS4' r_r2Hz_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS4' r_r2Hz_0))|].
icpt_l1t_0 W5 c5 ms5 mat5 HS5 HF5 HFr5 MEQ5 PSL5 MEQ4 PSL4 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG r2Hz_e0 19) (RG r2Hz_e0 10) HS5 (br_sbeg_lt_send EE 39 40 gu ge E39 E40 ltac:(img_lia) ltac:(img_try (unfold SB; img_lia)))) as HS5'.
img_change (neg_bc BC_GEU) with BC_LTU in HS5'. clear HS5.
eapply SRr_bind; [img_norm_st HS5' r_r2Hz_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS5' r_r2Hz_1))|].
icpt_l1t_0 W6 c6 ms6 mat6 HS6 HF6 HFr6 MEQ6 PSL6 MEQ5 PSL5 EE EE2.
assert (SLW : forall z, sp0 - 64 - 8 <= z < sp0 - 64 -> writable_at tfxsegs (mrestrict H (ms_mem ms6)) z).
{ intros z Hz. img_apply YF8r.apresent_writable; [img_try (unfold YF8r.TFX_IMG_END, kHighMemBeg in *; img_lia)|]. unfold RC_SCR, RC_STK in *.
destruct (ms_mem ms6 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| img_try (exfalso; img_exact (PSL6 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
split; [img_try (img_exact (proj1 (Bpres z ltac:(img_lia)))) | img_try (exists b; img_exact Eb)]. }
assert (SZERO : forall a, gu + SB <= a < gu + SB + (ge - gu) -> aview tfxsegs H (ms_mem ms6) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms6) a) by (img_try (img_apply MEQ6; rewrite unsigned_lit_small by img_lia; unfold RC_STK, RC_SCR, kHighMemBeg in *; img_lia)).
replace a with (SB + (a - SB)) by img_lia. img_apply (ra_granule_zero (aview tfxsegs H mem) p n (a - SB) HRA); [img_try (unfold SB in *; img_lia) | img_try (img_exact Hp)]. }
assert (R10 : sv_denot EE (RG r2Hz_e1 10) = Z_to_bv 64 (gu + SB)).
{ img_change (sv_denot EE (RG r2Hz_e1 10)) with (sv_denot EE (SOff 39 SB)). cbn [sv_denot]. rewrite E39, unsigned_lit_small by img_lia. img_refl. }
assert (R11 : sv_denot EE (RG r2Hz_e1 11) = Z_to_bv 64 (ge - gu)).
{ img_change (sv_denot EE (RG r2Hz_e1 11)) with (sv_denot EE (SAlu ALU_ADD (SMd M_MUL (SOff 39 0) (SLit (-1))) (SOff 40 0))). img_exact (U_mz_len EE 39 40 gu ge E39 E40 ltac:(img_lia) ltac:(img_lia)). }
assert (R2 : sv_denot EE (RG r2Hz_e1 2) = Z_to_bv 64 (sp0 - 64)).
{ img_change (sv_denot EE (RG r2Hz_e1 2)) with (sv_denot EE (SOff 2 (-64))). cbn [sv_denot]. rewrite EE2. f_equal; img_lia. }
assert (R1 : sv_denot EE (RG r2Hz_e1 1) = Z_to_bv 64 (347624 + D_2c4)).
{ img_change (sv_denot EE (RG r2Hz_e1 1)) with (sv_denot EE (SLit (347624 + D_2c4))). img_apply bv_eq. img_case; vm_compute. all: img_refl. }
assert (HOFF : Forall (fun r => 0 <= base_val EE (YQ0b.r_base r) + YQ0b.r_lo r /\ base_val EE (YQ0b.r_base r) + YQ0b.r_hi r <= 2 ^ 64 /\
(base_val EE (YQ0b.r_base r) + YQ0b.r_hi r <= sp0 - 64 - 8 \/ sp0 - 64 <= base_val EE (YQ0b.r_base r) + YQ0b.r_lo r) /\
YQ0b.r_lo r <= YQ0b.r_wlo r /\ YQ0b.r_whi r <= YQ0b.r_hi r) (ss_mem r2Hz_e1)).
{ cbn [ss_mem r2Hz_e1]. repeat (img_apply Forall_cons); try img_apply Forall_nil.
all: cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite ?EE2, ?E32u, ?E33u; unfold RC_STK, SB, kHighMemBeg in *; repeat split; img_lia. }
eapply SRr_bind; [img_try (img_exact (icpt_memisz W EE r2Hz_e1 ms6 _ 56 (ss_mem r2Hz_e1) (gu + SB) (ge - gu) (sp0 - 64) (347624 + D_2c4) HS6 eq_refl eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) (submem_refl _)
R10 R11 R2 R1 ltac:(img_lia) ltac:(unfold SB; img_lia) ltac:(unfold SB, kHighMemBeg in *; img_lia) ltac:(unfold TFX_IMG_END, kHighMemBeg in *; img_lia) ltac:(img_lia)
(ret_ok_lit (347624 + D_2c4) ltac:(img_lia) ltac:(img_eqrefl_m)) ltac:(left; unfold SB, kHighMemBeg in *; img_lia) SLW SZERO HOFF))|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HM7 & HP7). rewrite ?wvb_wvb in *.
set (EE' := havoc EE 56 (map (getr (ms_regs ms7)) MZ_CLOB)) in HS7.
assert (EE'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE' i = getr regs r).
{ intros i r Hi. (subst EE'; cbv beta). rewrite ew_havoc_old by (img_try (pose proof (u5_range r); img_lia)). img_apply EEreg. img_exact Hi. }
assert (EE'2 : bv_unsigned (ew EE' 2) = sp0) by (img_try ((subst EE'; cbv beta); rewrite ew_havoc_old by img_lia; img_exact EE2)).
assert (EE'N : ew EE' 41 = Z_to_bv 64 n) by (img_try ((subst EE'; cbv beta); rewrite ew_havoc_old by img_lia; img_exact EEN)).
assert (MEQ7 : forall z : word, ~ (sp0 - RC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HM7 z) by (img_try (unfold RC_SCR in *; img_lia)). img_apply MEQ6. unfold RC_SCR, RC_STK in *. img_lia. }
assert (PSL7 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. img_apply HP7. unfold RC_SCR, RC_STK in *. img_lia. }
clear HM7 HP7 SLW SZERO R10 R11 R2 R1 HOFF HS6.
eapply SRr_bind; [img_norm_st HS7 r_r2Hz_2; img_try (img_apply (icpt_phase_to W EE' RC_END _ _ _ _ _ HS7 r_r2Hz_2))|].
icpt_l1t_1 W8 c8 ms8 mat8 HS8 HF8 HFr8 MEQ8 PSL8 MEQ7 PSL7 EE' EE'2.
img_apply SRr_ret. img_apply (finishR EE' r2Hz_e2 ms8 mat8 HS8 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EE'reg).
- intros z Hz. img_apply MEQ8. unfold RC_SCR, RC_STK in *. img_lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
+
assert (Hlt : (p + n - 1) mod 8 < b1 < 8) by (img_try (destruct Hok as [Hz0 | [Hlt Hb]]; [img_try (exfalso; img_exact (Hbz Hz0)) | img_lia])).
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_EQ (RG r2H_e3 11) (SLit 0) HS4 (rp_b1_nonzero EE 34 b1 E34 ltac:(img_lia))) as HS4'.
img_change (neg_bc BC_EQ) with BC_NE in HS4'. clear HS4.
eapply SRr_bind; [img_norm_st HS4' r_r2Hn_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS4' r_r2Hn_0))|].
icpt_l1t_0 W5 c5 ms5 mat5 HS5 HF5 HFr5 MEQ5 PSL5 MEQ4 PSL4 EE EE2.
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_LT (RG r2Hn_e0 12) (RG r2Hn_e0 11) HS5 (rp_blt_last EE 22 41 34 p n b1 EEP EEN E34 Hp ltac:(img_lia) Hpn Hlt)) as HS5'. clear HS5.
eapply SRr_bind; [img_norm_st HS5' r_r2Hn_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS5' r_r2Hn_1))|].
icpt_l1t_0 W6 c6 ms6 mat6 HS6 HF6 HFr6 MEQ6 PSL6 MEQ5 PSL5 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG r2Hn_e1 19) (RG r2Hn_e1 10) HS6 (br_sbeg_lt_send EE 39 40 gu ge E39 E40 ltac:(img_lia) ltac:(img_try (unfold SB; img_lia)))) as HS6'.
img_change (neg_bc BC_GEU) with BC_LTU in HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_r2Hn_2; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS6' r_r2Hn_2))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 PSL7 MEQ6 PSL6 EE EE2.
assert (SLW : forall z, sp0 - 64 - 8 <= z < sp0 - 64 -> writable_at tfxsegs (mrestrict H (ms_mem ms7)) z).
{ intros z Hz. img_apply YF8r.apresent_writable; [img_try (unfold YF8r.TFX_IMG_END, kHighMemBeg in *; img_lia)|]. unfold RC_SCR, RC_STK in *.
destruct (ms_mem ms7 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| img_try (exfalso; img_exact (PSL7 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
split; [img_try (img_exact (proj1 (Bpres z ltac:(img_lia)))) | img_try (exists b; img_exact Eb)]. }
assert (SZERO : forall a, gu + SB <= a < gu + SB + (ge - gu) -> aview tfxsegs H (ms_mem ms7) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms7) a) by (img_try (img_apply MEQ7; rewrite unsigned_lit_small by img_lia; unfold RC_STK, RC_SCR, kHighMemBeg in *; img_lia)).
replace a with (SB + (a - SB)) by img_lia. img_apply (ra_granule_zero (aview tfxsegs H mem) p n (a - SB) HRA); [img_try (unfold SB in *; img_lia) | img_try (img_exact Hp)]. }
assert (R10 : sv_denot EE (RG r2Hn_e2 10) = Z_to_bv 64 (gu + SB)).
{ img_change (sv_denot EE (RG r2Hn_e2 10)) with (sv_denot EE (SOff 39 SB)). cbn [sv_denot]. rewrite E39, unsigned_lit_small by img_lia. img_refl. }
assert (R11 : sv_denot EE (RG r2Hn_e2 11) = Z_to_bv 64 (ge - gu)).
{ img_change (sv_denot EE (RG r2Hn_e2 11)) with (sv_denot EE (SAlu ALU_ADD (SMd M_MUL (SOff 39 0) (SLit (-1))) (SOff 40 0))). img_exact (U_mz_len EE 39 40 gu ge E39 E40 ltac:(img_lia) ltac:(img_lia)). }
assert (R2 : sv_denot EE (RG r2Hn_e2 2) = Z_to_bv 64 (sp0 - 64)).
{ img_change (sv_denot EE (RG r2Hn_e2 2)) with (sv_denot EE (SOff 2 (-64))). cbn [sv_denot]. rewrite EE2. f_equal; img_lia. }
assert (R1 : sv_denot EE (RG r2Hn_e2 1) = Z_to_bv 64 (347624 + D_2c4)).
{ img_change (sv_denot EE (RG r2Hn_e2 1)) with (sv_denot EE (SLit (347624 + D_2c4))). img_apply bv_eq. img_case; vm_compute. all: img_refl. }
assert (HOFF : Forall (fun r => 0 <= base_val EE (YQ0b.r_base r) + YQ0b.r_lo r /\ base_val EE (YQ0b.r_base r) + YQ0b.r_hi r <= 2 ^ 64 /\
(base_val EE (YQ0b.r_base r) + YQ0b.r_hi r <= sp0 - 64 - 8 \/ sp0 - 64 <= base_val EE (YQ0b.r_base r) + YQ0b.r_lo r) /\
YQ0b.r_lo r <= YQ0b.r_wlo r /\ YQ0b.r_whi r <= YQ0b.r_hi r) (ss_mem r2Hn_e2)).
{ cbn [ss_mem r2Hn_e2]. repeat (img_apply Forall_cons); try img_apply Forall_nil.
all: cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite ?EE2, ?E32u, ?E33u; unfold RC_STK, SB, kHighMemBeg in *; repeat split; img_lia. }
eapply SRr_bind; [img_try (img_exact (icpt_memisz W EE r2Hn_e2 ms7 _ 56 (ss_mem r2Hn_e2) (gu + SB) (ge - gu) (sp0 - 64) (347624 + D_2c4) HS7 eq_refl eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) (submem_refl _)
R10 R11 R2 R1 ltac:(img_lia) ltac:(unfold SB; img_lia) ltac:(unfold SB, kHighMemBeg in *; img_lia) ltac:(unfold TFX_IMG_END, kHighMemBeg in *; img_lia) ltac:(img_lia)
(ret_ok_lit (347624 + D_2c4) ltac:(img_lia) ltac:(img_eqrefl_m)) ltac:(left; unfold SB, kHighMemBeg in *; img_lia) SLW SZERO HOFF))|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HM8 & HP8). rewrite ?wvb_wvb in *.
set (EE' := havoc EE 56 (map (getr (ms_regs ms8)) MZ_CLOB)) in HS8.
assert (EE'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE' i = getr regs r).
{ intros i r Hi. (subst EE'; cbv beta). rewrite ew_havoc_old by (img_try (pose proof (u5_range r); img_lia)). img_apply EEreg. img_exact Hi. }
assert (EE'2 : bv_unsigned (ew EE' 2) = sp0) by (img_try ((subst EE'; cbv beta); rewrite ew_havoc_old by img_lia; img_exact EE2)).
assert (EE'N : ew EE' 41 = Z_to_bv 64 n) by (img_try ((subst EE'; cbv beta); rewrite ew_havoc_old by img_lia; img_exact EEN)).
assert (MEQ8 : forall z : word, ~ (sp0 - RC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HM8 z) by (img_try (unfold RC_SCR in *; img_lia)). img_apply MEQ7. unfold RC_SCR, RC_STK in *. img_lia. }
assert (PSL8 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. img_apply HP8. unfold RC_SCR, RC_STK in *. img_lia. }
clear HM8 HP8 SLW SZERO R10 R11 R2 R1 HOFF HS7.
eapply SRr_bind; [img_norm_st HS8 r_r2Hn_3; img_try (img_apply (icpt_phase_to W EE' RC_END _ _ _ _ _ HS8 r_r2Hn_3))|].
icpt_l1t_1 W9 c9 ms9 mat9 HS9 HF9 HFr9 MEQ9 PSL9 MEQ8 PSL8 EE' EE'2.
img_apply SRr_ret. img_apply (finishR EE' r2Hn_e3 ms9 mat9 HS9 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EE'reg).
- intros z Hz. img_apply MEQ9. unfold RC_SCR, RC_STK in *. img_lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms9 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL9 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
Qed.
Lemma t_cases : forall t, 0 <= t <= 8 -> t = 0 \/ t = 1 \/ t = 2 \/ t = 3 \/ t = 4 \/ t = 5 \/ t = 6 \/ t = 7 \/ t = 8.
Proof. intros t Ht. img_lia. Qed.
Theorem pfs_check_srr : SRr tfxsegs W (cfg_at tfxsegs RC_ENTRY regs mem md) POSTr.
Proof.
destruct (Z_le_gt_dec n 64) as [Hle|Hgt].
- assert (Hg0 : 8 * g0 <= p < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); pose proof (Z.div_mod p 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound p 8 ltac:(img_lia)); img_lia)).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (p + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(img_lia)); img_lia)).
destruct (t_cases (g1 - g0) ltac:(img_lia)) as [Ht|[Ht|[Ht|[Ht|[Ht|[Ht|[Ht|[Ht|Ht]]]]]]]];
[img_try (img_apply path1_0) | img_try (img_apply path1_1) | img_try (img_apply path1_2) | img_try (img_apply path1_3) | img_try (img_apply path1_4) | img_try (img_apply path1_5) | img_try (img_apply path1_6) | img_try (img_apply path1_7) | img_try (img_apply path1_8)]; assumption.
- destruct HAM as [HL|HH]; [img_try (img_apply path2L; [img_lia | img_exact HL]) | img_try (img_apply path2H; [img_lia | img_exact HH])].
Qed.
End f.
End e.
