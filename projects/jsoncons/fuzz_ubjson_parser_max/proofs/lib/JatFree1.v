(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac RefMemcpyLib As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac JatLeaf JatAllocG.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatFree1 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.As0Tables.AsanTab."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatFree1.FPX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0B"; "1bool"; "1option"; "1true"; "2I"; "2and"; "2eq"; "3Z"; "0L"; "4bvmap"; "0M"; "5Wn"; "5apart"; "5cell"; "5wr"; "6zrange"]; ["7msteps"; "8at_"; "8ret_ok"; "9art_cas23w_ok"; "9art_enq_mem"; ":getr"; ":mkst"; ":regupd"; ":v_and"; ":v_sllw"; ":v_xor"; ";loaded_segments"; "<forallb"; "=add"; "=div"; "=land"]; ["=le"; "=lt"; "=modulo"; "=mul"; "=pow"; "=sub"; "0a"; "0b1"; "0bsz"; "0c"; "0cnt"; "0csz"; "0fx"; "0j"; "0m"; "0raw"]; ["0regs"; "0rom"; "0size"; "0sp"; ">BV"; ">Z_to_bv"; ">bv"; ">bv_unsigned"; "0w"; "0x"; "0x0"; "0x1"; "0x2"; "0y"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Lemma zb8_eq : ltac2:(TCodec.tc2 tcn__JatFree1 "D'7'6&Q2r2+X0%3221r1%5213%73831'QFy8%211&QEr3%2241%325<%?3521p091pSLB1pSDC1").
Proof. intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. exact H. Qed.
Lemma at_lit : ltac2:(TCodec.tc2 tcn__JatFree1 "Q0'7&Q0zr2%3221&Q1&Mr4r3%3221&Q4+2+R0%3221%9251'6'QFyR0%211&A&QEr5%2251%421@%B23A%5281%;3831p0=1p0H1p0I1pRLN1pR>O1").
Proof.
intros a j Ha Hj H. unfold at_. rewrite art_u_lit by lia. reflexivity.
Qed.
Lemma cell4_split : ltac2:(TCodec.tc2 tcn__JatFree1 "QN'QFyR0%211'2y8%511%311p051'7&Q0zr2%3221&Q1&Mr3+4%3221&Q4+2+R0%3221%9251'5%?2>9+Q0%8271%>2<1%5241&=&Kr6r5u4r4%6554321r7u1&Q2+X0%2281%<5;5:41+1%M2<1&N%12=6%8217%B5A;4:1%Q22AMu2+RPP0%72C1%G5F@431%N261%O2=1p0D1p0L1p0Q31p0Q>1pSBQC1pR>QD1pFQF1").
Proof.
intros M a w Ha Ha' Hw C. unfold cell in *. unfold word_to_le_bytes in *.
rewrite (art_u_lit w) in C by lia.
split; [|split].
- pose proof (rdn_sub _ M 4 (Z_to_bv 64 a) _ 0 1 C ltac:(lia)) as R. rewrite at_lit in R by lia. change (Z.of_nat 0) with 0 in R. rewrite Z.add_0_r in R.
rewrite R. cbn [sub firstn skipn Z_to_le_bytes]. rewrite art_u_lit by (pose proof (Z.mod_pos_bound w 256); lia).
do 2 f_equal. apply zb8_eq. rewrite Z.mod_mod by lia. reflexivity.
- pose proof (rdn_sub _ M 4 (Z_to_bv 64 a) _ 1 1 C ltac:(lia)) as R. rewrite at_lit in R by lia. change (Z.of_nat 1) with 1 in R.
rewrite R. cbn [sub firstn skipn Z_to_le_bytes]. rewrite art_u_lit by (pose proof (Z.mod_pos_bound (w / 256) 256); lia).
do 2 f_equal. apply zb8_eq. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
- pose proof (rdn_sub _ M 4 (Z_to_bv 64 a) _ 2 2 C ltac:(lia)) as R. rewrite at_lit in R by lia. change (Z.of_nat 2) with 2 in R.
rewrite R. cbn [sub firstn skipn Z_to_le_bytes]. rewrite art_u_lit by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. rewrite !Z.div_div by lia. change (256 * 256) with 65536.
reflexivity.
Qed.
Lemma cell4_join : ltac2:(TCodec.tc2 tcn__JatFree1 "R3'QFyR0%211'2y8%511%311p051'7&Q0zr4%3221&Q1&Mr5+4%3221&Q4+2+R0%3221%9251'5%?2>9+X0%=2;1%4231+RPP0%@2>1%7261&=&Kr:r9u1r8%6554321r;+1%J271%:593165r<%M25Hu2%>5=3219r=u4&Q3%12H@%Q42<1%32GA%Q6221%F5E7;61p091p0>1p0C1p0K1p0O1p0Q01p0Q61p0QA1pSJQF1pSHQG1pSFQH1pR>QI1pFQK1").
Proof.
intros M a x0 x1 x2 Ha Ha' H0 H1 H2 C0 C1 C2. unfold cell in *. unfold word_to_le_bytes in *.
rewrite (art_u_lit x0) in C0 by lia. rewrite (art_u_lit x1) in C1 by lia. rewrite (art_u_lit x2) in C2 by lia. rewrite art_u_lit by lia.
change 4%nat with (1 + (1 + 2))%nat. erewrite rdn_app; [|exact C0|].
2:{ replace (Z_to_bv 64 a + nat_to_word 1)%bv with (Z_to_bv 64 (a + 1) : word).
2:{ apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). cbn [Z.of_nat Pos.of_succ_nat].
rewrite (Z.mod_small a), (Z.mod_small 1) by lia. rewrite Z.mod_small by lia. reflexivity. }
erewrite rdn_app; [reflexivity|exact C1|].
replace (Z_to_bv 64 (a + 1) + nat_to_word 1)%bv with (Z_to_bv 64 (a + 2) : word); [exact C2|].
apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). cbn [Z.of_nat Pos.of_succ_nat].
rewrite (Z.mod_small (a + 1)), (Z.mod_small 1) by lia. rewrite !Z.mod_small by lia. lia. }
cbn [Z_to_le_bytes app Nat.add]. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
set (w := x0 + 256 * x1 + 65536 * x2) in *.
assert (E0 : w mod 256 = x0 mod 256). { subst w. replace (x0 + 256 * x1 + 65536 * x2) with (x0 + (x1 + 256 * x2) * 256) by lia. rewrite Z_mod_plus_full. reflexivity. }
assert (E1 : w / 256 = x1 + 256 * x2). { subst w. replace (x0 + 256 * x1 + 65536 * x2) with (x0 + (x1 + 256 * x2) * 256) by lia. rewrite Z_div_plus_full by lia. rewrite Z.div_small by lia. lia. }
assert (E2 : w / 256 / 256 = x2). { rewrite E1. replace (x1 + 256 * x2) with (x1 + x2 * 256) by lia. rewrite Z_div_plus_full by lia. rewrite Z.div_small by lia. lia. }
do 2 f_equal; [symmetry; apply zb8_eq; exact E0|]. f_equal; [apply zb8_eq; rewrite E1; replace (x1 + 256 * x2) with (x1 + x2 * 256) by lia; rewrite Z_mod_plus_full; reflexivity|].
rewrite E2. reflexivity.
Qed.
Tactic Notation "recell_hit" integer(k) := do k (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia.
Ltac showst := lazymatch goal with |- msteps _ (mkst ?R ?P ?MM _) _ => idtac "REGS" R; idtac "PC" P; idtac "MEM" MM end; fail "SHOWST".
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_run_free_hooks_fn := (ltac2:(TCodec.tc2 tcn__JatFree1 "SC&9y5'QFyR0%211%5241'2y8%611%311p061'7'6&Er5(QD+1(4%33A21%6251r2%93A21&Br3%211r7+2%<3J1:%?231&QE%12K7%C3K31&Q0+Q0r4%3221&Q1&Q4+R0%22=1%42J1&M+VbTP0%221:r6%=221&>&Kr:&Q5%12IA%54431B&=r;+Qian8u8z%55:4321'@&FvQ<r=+`nPL%Q@3QL1Q>/01QLr<%756521=&G%137QBDr9%Q92R31%433Q<1+8%QJ3R81QH%QM2=1%83421+9%QN3R<1QL%R12A1%<3421+:%R23R@1R0%QE2R?J%@3421+;%R63RD1R4%C3314&;%Q72C@&QG%12RGQ:%44Q4J31+@%Q<2H1%52RKD%84Q8421+H%Q@2L1%92ROD%<4Q<421%Q95Q8>QD1Q?%Q;3QFQ31p0Q=1p0QD1p0QK1p0R11p0R71p0R<1p0RD1p0RH1pS8S31pS0S;1pS4S61pFS71pS2S=1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_run_free_hooks_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_run_free_hooks_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_run_free_hooks_fn) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_run_free_hooks_fn) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_run_free_hooks_fn) 4%nat 0%nat).
Lemma art_run_free_hooks_fn : ltac:(sec_stmt2 constr:(SEC_T_art_run_free_hooks_fn) 5%nat 0%nat).
Proof using Type regs M rom raw sp.
intros H1 Hret H2 Hsp Hsp' IMG W Ch.
zstep (ltac:(oF' 0x8781c%Z)) (ltac:(oD' 0x8781c%Z)).
zsd (ltac:(oF' 0x87820%Z)) (ltac:(oD' 0x87820%Z)) (sp - 8) (U raw) ltac:(rewok W).
zsd (ltac:(oF' 0x87824%Z)) (ltac:(oD' 0x87824%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W).
zsd (ltac:(oF' 0x87828%Z)) (ltac:(oD' 0x87828%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W).
zstep (ltac:(oF' 0x8782c%Z)) (ltac:(oD' 0x8782c%Z)).
stepn (ltac:(oF' 0x87830%Z)) (ltac:(oD' 0x87830%Z)).
zstep (ltac:(oF' 0x878c8%Z)) (ltac:(oD' 0x878c8%Z)).
stepjr (ltac:(oF' 0x878cc%Z)) (ltac:(oD' 0x878cc%Z)) (0x87834 : bv 64)%bv ltac:(gres; bveq).
zbtk (ltac:(oF' 0x87834%Z)) (ltac:(oD' 0x87834%Z)).
zstep (ltac:(oF' 0x87850%Z)) (ltac:(oD' 0x87850%Z)).
stepn (ltac:(oF' 0x87854%Z)) (ltac:(oD' 0x87854%Z)).
stepjr (ltac:(oF' 0x878d0%Z)) (ltac:(oD' 0x878d0%Z)) (0x87858 : bv 64)%bv ltac:(gres; bveq).
zstep (ltac:(oF' 0x87858%Z)) (ltac:(oD' 0x87858%Z)). zstep (ltac:(oF' 0x8785c%Z)) (ltac:(oD' 0x8785c%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (Ch' : cellA X (0x1cc7c0 + 8) 8 0) by (recell Ch);
assert (Cra : cellA X (sp - 8) 8 (U raw)) by (do 2 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia);
assert (Cs0 : cellA X (sp - 16) 8 (U (getr regs 8))) by (do 1 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia);
assert (Cs1 : cellA X (sp - 24) 8 (U (getr regs 9))) by (apply cell_Wn_hit; lia) end.
zld (ltac:(oF' 0x87860%Z)) (ltac:(oD' 0x87860%Z)) (0x1cc7c0 + 8) Ch'.
zbtk (ltac:(oF' 0x87864%Z)) (ltac:(oD' 0x87864%Z)).
zstep (ltac:(oF' 0x878b0%Z)) (ltac:(oD' 0x878b0%Z)).
zld (ltac:(oF' 0x878b4%Z)) (ltac:(oD' 0x878b4%Z)) (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x878b8%Z)) (ltac:(oD' 0x878b8%Z)) (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x878bc%Z)) (ltac:(oD' 0x878bc%Z)) (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
zstep (ltac:(oF' 0x878c0%Z)) (ltac:(oD' 0x878c0%Z)).
stepret (ltac:(oF' 0x878c4%Z)) (ltac:(oD' 0x878c4%Z)) raw ltac:(rwH; reflexivity).
zret.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_int_alloc_fn := (ltac2:(TCodec.tc2 tcn__JatFree1 "T1&9y5'QFyR0%211%5241'2y8%611%311p061'7'6&Er5(QD+1(4%33A21%6251r2%93A21&Br3%211r7+2%<3J1:%?231&QE%12K7%C3K31&Q0+Q@r4%3221&Q1&Q4+R0%22=1%42J1&M+VbTP0%221:r6%=221&>&Kr:&Q5%12IA%54431B&=r;+QiYl8u1%459321Q8'@&FvQ<r=+`dP8%Q?3QK1Q=/01QKr<%756521<&G%137QACr9%Q82R21%433Q;1+8%QI3R71QG%QL2=1%83421+9%QM3R;1QK%R02A1%<3421+:%R13R?1QO+QW_h0%QE2R?1%A3531+B%R63RD1R4%R92J1%E3421+C%R:3RH1R8%R=2N1%I3421&;u8%Q=2JG&QG%12RMQ@%544Q131+@%QB2O1%52S1K%948421+H%QF2Q31%92S5K%=4<421+Q0%QJ2Q71%=2S9F%A4@421+Q8%QN2Q;1%A2S=F%E4D421%QH5QGGR21QM%QJ3R4QB1p0QL1p0R21p0R91p0R?1p0RE1p0RJ1p0S21p0S61pS8SA1pS0SI1pS4SD1pFSE1pS2SK1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_int_alloc_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_int_alloc_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_int_alloc_fn) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_int_alloc_fn) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_int_alloc_fn) 4%nat 0%nat).
Lemma art_int_alloc_fn : ltac:(sec_stmt2 constr:(SEC_T_art_int_alloc_fn) 5%nat 0%nat).
Proof using Type regs M rom raw sp.
intros H1 Hret H2 Hsp Hsp' IMG W Ci.
zstep (ltac:(oF' 0x85008%Z)) (ltac:(oD' 0x85008%Z)).
zsd (ltac:(oF' 0x8500c%Z)) (ltac:(oD' 0x8500c%Z)) (sp - 8) (U raw) ltac:(rewok W).
zsd (ltac:(oF' 0x85010%Z)) (ltac:(oD' 0x85010%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W).
zsd (ltac:(oF' 0x85014%Z)) (ltac:(oD' 0x85014%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W).
zsd (ltac:(oF' 0x85018%Z)) (ltac:(oD' 0x85018%Z)) (sp - 32) (U (getr regs 18)) ltac:(rewok W).
zsd (ltac:(oF' 0x8501c%Z)) (ltac:(oD' 0x8501c%Z)) (sp - 40) (U (getr regs 19)) ltac:(rewok W).
zstep (ltac:(oF' 0x85020%Z)) (ltac:(oD' 0x85020%Z)). zstep (ltac:(oF' 0x85024%Z)) (ltac:(oD' 0x85024%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (Ci' : cellA X 0x1ca788 1 1) by (recell Ci);
assert (Cra : cellA X (sp - 8) 8 (U raw)) by (recell_hit 4);
assert (Cs0 : cellA X (sp - 16) 8 (U (getr regs 8))) by (recell_hit 3);
assert (Cs1 : cellA X (sp - 24) 8 (U (getr regs 9))) by (recell_hit 2);
assert (Cs2 : cellA X (sp - 32) 8 (U (getr regs 18))) by (recell_hit 1);
assert (Cs3 : cellA X (sp - 40) 8 (U (getr regs 19))) by (recell_hit 0) end.
zlb (ltac:(oF' 0x85028%Z)) (ltac:(oD' 0x85028%Z)) 0x1ca788 Ci'.
stepfence (ltac:(oF' 0x8502c%Z)) (ltac:(oD' 0x8502c%Z)).
zbtk (ltac:(oF' 0x85030%Z)) (ltac:(oD' 0x85030%Z)).
zstep (ltac:(oF' 0x8512c%Z)) (ltac:(oD' 0x8512c%Z)). zstep (ltac:(oF' 0x85130%Z)) (ltac:(oD' 0x85130%Z)).
zld (ltac:(oF' 0x85134%Z)) (ltac:(oD' 0x85134%Z)) (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x85138%Z)) (ltac:(oD' 0x85138%Z)) (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x8513c%Z)) (ltac:(oD' 0x8513c%Z)) (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x85140%Z)) (ltac:(oD' 0x85140%Z)) (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x85144%Z)) (ltac:(oD' 0x85144%Z)) (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
zstep (ltac:(oF' 0x85148%Z)) (ltac:(oD' 0x85148%Z)).
stepret (ltac:(oF' 0x8514c%Z)) (ltac:(oD' 0x8514c%Z)) raw ltac:(rwH; reflexivity).
zret.
Qed.
End SE.
#[local] Ltac wpc := lazymatch goal with |- msteps _ (mkstr _ ?p _ _ _) _ => wlit p | |- msteps _ (mkst _ ?p _ _) _ => wlit p end.
#[using="Type"] Lemma art_sllw_0 : ltac2:(TCodec.tc2 tcn__JatFree1 "Q>'7'5&Q0zr2%3221&Q1&Q4+2+O%3221%5271%;271&Q3r3+8%3221+R0%;2:1%=231'6&Q2r4+4%3221%53I1F'QFyR0%211&I&QEr6%2251r5+3%L2K1%G231%72:1%9261%C3;17p0?1p0F1p0Q51p0O1pRNQ<1pSDQ=1").
Proof.
intros x m Hx Hm Hm' Hm4. unfold v_sllw. rewrite !art_u_lit by lia.
replace (m * 2 ^ 3 mod 32) with 0.
2:{ pose proof (Z.div_mod m 4 ltac:(lia)) as E. rewrite Hm4 in E. replace (m * 2 ^ 3) with ((m / 4) * 32) by lia. rewrite Z_mod_mult. reflexivity. }
rewrite Z.shiftl_0_r. f_equal. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
rewrite (Z.mod_small (x + 2 ^ 31)) by lia. lia.
Qed.
Definition art_cas23w_ok (b1 : Z) : bool :=
bv_eqb (v_xor (Z_to_bv 64 (2 + 256 * b1)) (v_and (v_xor (Z_to_bv 64 (2 + 256 * b1)) (Z_to_bv 64 3)) (Z_to_bv 64 255))) (Z_to_bv 64 (3 + 256 * b1)).
#[using="Type"] Lemma art_cas23w_all : ltac2:(TCodec.tc2 tcn__JatFree1 "<'6'1&L'7&C&?z+X0%3221%73651(3%;3:21").
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma art_cas23w : ltac2:(TCodec.tc2 tcn__JatFree1 "Q4'7'5&Q0zr1%3221&Q1+X0%2241%8241'6'QFyR0%211&J&QE&M+2&Q3r2%22=1%5241%72:1&H+3%:2=1%<241+WO%=2@1%6231%@281%?27;%A2D1%G3D31p0I1pR@Q31").
Proof.
intros b1 Hb. pose proof art_cas23w_all as H. rewrite forallb_forall in H.
specialize (H b1 ltac:(unfold AsanTab.zrange; apply AsanTab.in_ziota; rewrite Z2Nat.id by lia; lia)). unfold art_cas23w_ok, bv_eqb in H.
apply Z.eqb_eq in H. apply bv_eq. exact H.
Qed.
#[using="Type"] Lemma art_land_m4 : ltac2:(TCodec.tc2 tcn__JatFree1 "J'7'5&Q0zr1%3221&Q1&Q4+2+R0%3221%5271%;271'6&Or2+_oooooooooooL%3221&Q3&N+4%2261%4212%:3G61p0<1pSDI1").
Proof.
intros x Hx. change 18446744073709551612 with (Z.shiftl (Z.ones 62) 2).
change 4 with (2 ^ 2). rewrite <- Z.shiftr_div_pow2, <- Z.shiftl_mul_pow2 by lia.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
destruct (Z.lt_ge_cases i 2) as [L|G].
- rewrite !Z.shiftl_spec_low by lia. apply Bool.andb_false_r.
- rewrite !Z.shiftl_spec_high by lia. rewrite Z.shiftr_spec by lia. rewrite Z.testbit_ones by lia.
replace (i - 2 + 2) with i by lia.
destruct (Z.lt_ge_cases i 64) as [L2|G2].
+ replace ((0 <=? i - 2) && (i - 2 <? 62))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
apply Bool.andb_true_r.
+ assert (Tf : Z.testbit x i = false).
{ destruct (Z.eq_dec x 0) as [->|NZ]. apply Z.testbit_0_l. apply Z.bits_above_log2; [lia|].
apply Z.lt_le_trans with (m := 64); [|lia]. apply Z.log2_lt_pow2; lia. }
rewrite Tf. reflexivity.
Qed.
Section SE.
Local Abbreviation SEC_T_art_cas23_fn := (ltac2:(TCodec.tc2 tcn__JatFree1 "SO&9y5'QFyR0%211%5241'2y8%611%311p061'7'6&Er5(QD+B(4%33A21%6251&QEr2%22C1%;3C41&Q0+@r3%3221&Q1&Mr4%2216&Q4+2+Q?%3221%8251&Q2%12H=z%L3M21'5%B23L+X0%@2N1%4231&=&Kr9r7u4&Q3r6%22:1%I2E1%9587651&>r:r8+4%44=321'@&FvQ<r<+ZVZH%QC3QO1QA/01QOr;%756521<&G+:%QI3R71QG+3%Q:2Q91%H2K1%QH2R91%73=51+;%R03R>1QN%QL2R=7%;3421+<%R43RB1R2%Q12Q9J%QH2QD1%R22RC1%A3641+=%R:3RH1R8%R62RGQ:%E3421+>%R>3RL1R<%R:2RKQM%I3421+?%RB3S01R@+WO%R?2S01%N3531%RF3S4R<RD%Q0321F+A%RI3S71RG%RE2S6R2%Q43421+ZV\H%RM3S91RK/01S9&;%RB2Q6K%24QNQ<R01%QC5QB741QH%QE3R3Q=1p0QG1p0QM1p0R81p0R>1p0RC1p0RM1p0S21pR@S?1pRNS@1pS4SB1pFSC1pS2SI1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_cas23_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_cas23_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_cas23_fn) 2%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_art_cas23_fn) 3%nat 0%nat).
Variable b1 : ltac:(sec_ty2 constr:(SEC_T_art_cas23_fn) 4%nat 0%nat).
Lemma art_cas23_fn : ltac:(sec_stmt2 constr:(SEC_T_art_cas23_fn) 5%nat 0%nat).
Proof using Type regs M rom m b1.
intros H18 Hm Hm' Hm16 Hb1 Chw Whw.
assert (Hm4 : m mod 4 = 0). { pose proof (Z.div_mod m 16 ltac:(lia)) as E. rewrite Hm16 in E. rewrite E. replace (16 * (m / 16) + 0) with ((4 * (m / 16)) * 4) by lia. apply Z_mod_mult. }
stepn (ltac:(oF' 0x51958%Z)) (ltac:(oD' 0x51958%Z)). rwH. unfold v_andi. rewrite art_u_lit by lia. change (bv_wrap 64 (-4)) with 18446744073709551612. rewrite art_land_m4 by lia.
replace (m / 4 * 4) with m by (pose proof (Z.div_mod m 4 ltac:(lia)); lia).
stepn (ltac:(oF' 0x5195c%Z)) (ltac:(oD' 0x5195c%Z)). rwH. rewrite art_zb_slli by lia.
zstep (ltac:(oF' 0x51960%Z)) (ltac:(oD' 0x51960%Z)). zstep (ltac:(oF' 0x51964%Z)) (ltac:(oD' 0x51964%Z)). zstep (ltac:(oF' 0x51968%Z)) (ltac:(oD' 0x51968%Z)).
stepn (ltac:(oF' 0x5196c%Z)) (ltac:(oD' 0x5196c%Z)). rwH. rewrite art_sllw_0 by lia.
stepn (ltac:(oF' 0x51970%Z)) (ltac:(oD' 0x51970%Z)). rwH. rewrite art_sllw_0 by lia.
stepn (ltac:(oF' 0x51974%Z)) (ltac:(oD' 0x51974%Z)). rwH. rewrite art_sllw_0 by lia.
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Whw' : wok Asan.M.loaded_segments X m 4) by (rewok Whw) end.
chain_step; [reflexivity
| eapply (art_step_lr_w _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 m) _ (Z_to_bv 64 (2 + 256 * b1)));
[exact (ltac:(oF' 0x51978%Z)) | reflexivity | exact (ltac:(oD' 0x51978%Z)) | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hm4
| exact Chw | apply art_bytes4; lia ]
| ]. wpc. rewrite art_v_lw_small by lia.
chain_step; [reflexivity | eapply art_step_and_r; [exact (ltac:(oF' 0x5197c%Z)) | reflexivity | exact (ltac:(oD' 0x5197c%Z)) | reflexivity] | ]. wpc.
gres. rewrite (art_zb_and (2 + 256 * b1) 255) by lia.
replace (Z.land (2 + 256 * b1) 255) with 2.
2:{ change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256. replace (2 + 256 * b1) with (2 + b1 * 256) by lia. rewrite Z_mod_plus_full. reflexivity. }
chain_step; [reflexivity
| eapply art_step_branch_ft_r; [exact (ltac:(oF' 0x51980%Z)) | reflexivity | exact (ltac:(oD' 0x51980%Z)) | cbn [Sem.branch_taken]; gres; rwH; unfold bv_eqb; rewrite Z.eqb_refl; reflexivity ]
| ]. wpc.
chain_step; [reflexivity | eapply art_step_xor_r; [exact (ltac:(oF' 0x51984%Z)) | reflexivity | exact (ltac:(oD' 0x51984%Z)) | reflexivity] | ]. wpc.
chain_step; [reflexivity | eapply art_step_and_r; [exact (ltac:(oF' 0x51988%Z)) | reflexivity | exact (ltac:(oD' 0x51988%Z)) | reflexivity] | ]. wpc.
chain_step; [reflexivity | eapply art_step_xor_r; [exact (ltac:(oF' 0x5198c%Z)) | reflexivity | exact (ltac:(oD' 0x5198c%Z)) | reflexivity] | ]. wpc.
gres.
rewrite art_cas23w by lia.
chain_step; [reflexivity
| eapply (art_step_sc_w_ok _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 m));
[exact (ltac:(oF' 0x51990%Z)) | reflexivity | exact (ltac:(oD' 0x51990%Z)) | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hm4 | gres; rwH; reflexivity
| exact Whw' ]
| ]. wpc.
change (wbytes ?M0 (Z_to_bv 64 m) (word_to_le_bytes 4 (Z_to_bv 64 (3 + 256 * b1)))) with (Wn 4 M0 m (3 + 256 * b1)).
zbft (ltac:(oF' 0x51994%Z)) (ltac:(oD' 0x51994%Z)).
zret.
Qed.
End SE.
Definition art_enq_mem (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) (B cnt bsz csz c m size : Z) : word -> option byte :=
(Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18))) (sp - 40) (U (getr regs 19))) (sp - 48) (U (getr regs 20))) (sp - 56) (U (getr regs 21))) (B + 8) (bsz + size)) (B + 16) (cnt + 1)) (B + 24 + 8 * cnt) m) (c + 24) (csz + size)).
Section SE.
Local Abbreviation SEC_T_art_enqueue_fn := (ltac2:(TCodec.tc2 tcn__JatFree1 "WC&9y5'QFyR0%211%5241'2y8%611%311p061'7'6&Er=(QD+1(4%33A21%6251r:%93A21&Br;%211r?+2%<3J1:%?231&QE%12K7%C3K31r@+:%C3Q11A%F231%H3Q016rA+=%H3Q61F%K231r6%=2Q71%O3Q731rB+>%O3Q=1M%Q2231%Q43Q<16&Q0+R0%221J&Q1&Q4%12L4%32G1&M+VbTP0%2218%:21Fz%<21H+Q0%72C1%<21:%@25ErC+XP0%<221%A21?'5%F2QG5+QO%D2Q?1%F281%5241%K2@:+oM%J2<1%9231rD%I21Q<%N21L%Q22G3rE%M21C%Q221Q0rF%Q72L1%Q522Q3%D221&<&Q5rN%221Q<rM%542Q>1Q2rO%621Q@%841QA4Q0%943Q67Q1&>&KrQ4rQ1%=21QG%54431QHrQ5+H%QE251+8%:49421rQ6%<4;19Q>&=rQ7rQ3u8%45@321>rQ8+@%R12B1%85D3156rQ9rQ2%;5G2481rQ:%R72DA%>5J21;4rQ;%R:2?F%A5M21>7'@&FvQ<rQ=+ZhZH%SJ3T61SH/01T6rQ<%756521;&G%137SL@%SB2T<D%332SE1%T23T@Q3T0%T52;1%63321+9%T63TD1T4%T92?1%:3421+;%T:3TH1T8%S22Q6QB%SN2TH1%?3531+<%T?3TM1T=&Q3+3%S<2T71%32QG1%S;2Q@1%T72U11%H3971+?%TH3U61TF%S@2QMTH%T<2U61%M3531%TL3U:QCTJ%T?2U9QI%Q03321+A%U03U>1TN%TC2U=S3%Q43421+B%U43UB1U2%U72Q=1%Q83421+C%U83UF1U6%U;2QA1%Q<3421+D%U<3UJ1U:%U?2QE1%Q@3421+E%U@3UN1U>%UC2QI1%QD3421&D%1;QHR8R5QLR@RHRLR?R<R7RK%QO5QN3R61R3%R13ROQI1p0R31p0R71p0R;1p0R?1p0RD1p0RJ1p0RM1p0S31p0S:1p0S<1p0S@1p0SG1p0SO1p0SM1p0T11p0T31p0T:1p0T81p0T=1p0TD1p0TI1p0TK1p0TO1p0U21p0U71p0U<1p0U@1p0UF1p0UN1p0V41p0V<1p0V@1pS6VK1pRNVL1pRHVM1pRBVN1pRFVO1pBW01p2W11pRDW21pS8W31pS0W;1pS4W61pFW71pS2W=1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_enqueue_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_enqueue_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_enqueue_fn) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_enqueue_fn) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_enqueue_fn) 4%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_enqueue_fn) 5%nat 0%nat).
Variable B : ltac:(sec_ty2 constr:(SEC_T_art_enqueue_fn) 6%nat 0%nat).
Variable L : ltac:(sec_ty2 constr:(SEC_T_art_enqueue_fn) 7%nat 0%nat).
Variable cnt : ltac:(sec_ty2 constr:(SEC_T_art_enqueue_fn) 8%nat 0%nat).
Variable bsz : ltac:(sec_ty2 constr:(SEC_T_art_enqueue_fn) 9%nat 0%nat).
Variable csz : ltac:(sec_ty2 constr:(SEC_T_art_enqueue_fn) 10%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_art_enqueue_fn) 11%nat 0%nat).
Variable size : ltac:(sec_ty2 constr:(SEC_T_art_enqueue_fn) 12%nat 0%nat).
Lemma art_enqueue_fn : ltac:(sec_stmt2 constr:(SEC_T_art_enqueue_fn) 13%nat 0%nat).
Proof using Type regs M rom raw sp c B L cnt bsz csz m size.
intros H1 Hret H2 H10 H13 H14 Hsp Hsp' IMG Hc Hc' HB HB' HL Hcnt Hbsz Hbsz' Hcsz Hcsz' Hsize Hm A1 A2 A3 W Wc WB CL CB Ccnt Cbsz Ccsz.
zstep (ltac:(oF' 0x56158%Z)) (ltac:(oD' 0x56158%Z)).
zsd (ltac:(oF' 0x5615c%Z)) (ltac:(oD' 0x5615c%Z)) (sp - 8) (U raw) ltac:(rewok W).
zsd (ltac:(oF' 0x56160%Z)) (ltac:(oD' 0x56160%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W).
zsd (ltac:(oF' 0x56164%Z)) (ltac:(oD' 0x56164%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W).
zsd (ltac:(oF' 0x56168%Z)) (ltac:(oD' 0x56168%Z)) (sp - 32) (U (getr regs 18)) ltac:(rewok W).
zsd (ltac:(oF' 0x5616c%Z)) (ltac:(oD' 0x5616c%Z)) (sp - 40) (U (getr regs 19)) ltac:(rewok W).
zsd (ltac:(oF' 0x56170%Z)) (ltac:(oD' 0x56170%Z)) (sp - 48) (U (getr regs 20)) ltac:(rewok W).
zsd (ltac:(oF' 0x56174%Z)) (ltac:(oD' 0x56174%Z)) (sp - 56) (U (getr regs 21)) ltac:(rewok W).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (CL' : cellA X c 8 L) by (unfold apart in *; recell CL);
assert (CB' : cellA X (c + 16) 8 B) by (unfold apart in *; recell CB);
assert (Ccnt' : cellA X (B + 16) 8 cnt) by (unfold apart in *; recell Ccnt);
assert (Cbsz' : cellA X (B + 8) 8 bsz) by (unfold apart in *; recell Cbsz) end.
zld (ltac:(oF' 0x56178%Z)) (ltac:(oD' 0x56178%Z)) c CL'.
zbft (ltac:(oF' 0x5617c%Z)) (ltac:(oD' 0x5617c%Z)).
zld (ltac:(oF' 0x56180%Z)) (ltac:(oD' 0x56180%Z)) (c + 16) CB'.
zld (ltac:(oF' 0x56184%Z)) (ltac:(oD' 0x56184%Z)) (B + 16) Ccnt'.
zstep (ltac:(oF' 0x56188%Z)) (ltac:(oD' 0x56188%Z)).
zbtk (ltac:(oF' 0x5618c%Z)) (ltac:(oD' 0x5618c%Z)).
zbft (ltac:(oF' 0x56214%Z)) (ltac:(oD' 0x56214%Z)).
zld (ltac:(oF' 0x56218%Z)) (ltac:(oD' 0x56218%Z)) (B + 8) Cbsz'.
zstep (ltac:(oF' 0x5621c%Z)) (ltac:(oD' 0x5621c%Z)). zstep (ltac:(oF' 0x56220%Z)) (ltac:(oD' 0x56220%Z)). zstep (ltac:(oF' 0x56224%Z)) (ltac:(oD' 0x56224%Z)). zstep (ltac:(oF' 0x56228%Z)) (ltac:(oD' 0x56228%Z)).
zsd (ltac:(oF' 0x5622c%Z)) (ltac:(oD' 0x5622c%Z)) (B + 8) (bsz + size) ltac:(unfold apart in *; rewok WB).
zsd (ltac:(oF' 0x56230%Z)) (ltac:(oD' 0x56230%Z)) (B + 16) (cnt + 1) ltac:(unfold apart in *; rewok WB).
zsd (ltac:(oF' 0x56234%Z)) (ltac:(oD' 0x56234%Z)) (B + 24 + 8 * cnt) m ltac:(unfold apart in *; rewok WB).
stepn (ltac:(oF' 0x56238%Z)) (ltac:(oD' 0x56238%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (Ccsz' : cellA X (c + 24) 8 csz) by (unfold apart in *; recell Ccsz) end.
zld (ltac:(oF' 0x56248%Z)) (ltac:(oD' 0x56248%Z)) (c + 24) Ccsz'.
zstep (ltac:(oF' 0x5624c%Z)) (ltac:(oD' 0x5624c%Z)).
zsd (ltac:(oF' 0x56250%Z)) (ltac:(oD' 0x56250%Z)) (c + 24) (csz + size) ltac:(unfold apart in *; rewok Wc).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (Cra : cellA X (sp - 8) 8 (U raw)) by (unfold apart in *; zcell);
assert (Cs0 : cellA X (sp - 16) 8 (U (getr regs 8))) by (unfold apart in *; zcell);
assert (Cs1 : cellA X (sp - 24) 8 (U (getr regs 9))) by (unfold apart in *; zcell);
assert (Cs2 : cellA X (sp - 32) 8 (U (getr regs 18))) by (unfold apart in *; zcell);
assert (Cs3 : cellA X (sp - 40) 8 (U (getr regs 19))) by (unfold apart in *; zcell);
assert (Cs4 : cellA X (sp - 48) 8 (U (getr regs 20))) by (unfold apart in *; zcell);
assert (Cs5 : cellA X (sp - 56) 8 (U (getr regs 21))) by (unfold apart in *; zcell) end.
zld (ltac:(oF' 0x56254%Z)) (ltac:(oD' 0x56254%Z)) (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x56258%Z)) (ltac:(oD' 0x56258%Z)) (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x5625c%Z)) (ltac:(oD' 0x5625c%Z)) (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x56260%Z)) (ltac:(oD' 0x56260%Z)) (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x56264%Z)) (ltac:(oD' 0x56264%Z)) (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x56268%Z)) (ltac:(oD' 0x56268%Z)) (sp - 48) Cs4. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x5626c%Z)) (ltac:(oD' 0x5626c%Z)) (sp - 56) Cs5. rewrite Z_to_bv_bv_unsigned.
zstep (ltac:(oF' 0x56270%Z)) (ltac:(oD' 0x56270%Z)).
stepret (ltac:(oF' 0x56274%Z)) (ltac:(oD' 0x56274%Z)) raw ltac:(rwH; reflexivity).
unfold art_enq_mem. zret.
Qed.
End SE.
End FPX.
