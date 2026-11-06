(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib MemSplit As0StepLib Jb0RegionPoisoned.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Jb0DiagStrlen () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1app"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "2I"; "2and"; "2eq"; "2ex"; "3add"; "4le"; "4lt"; "5nth"]; ["6Z"; "7bvmap"; "0M"; "8msteps"; "9ret_ok"; ":getr"; ":mkst"; ":rdn"; ";keeps_cs"; "<loaded_segments"; "=add"; "=le"; "=lt"; "=of_nat"; "=pow"; "0a"]; ["0bs"; "0fx"; "0j"; "0n"; "0p"; "0q"; "0regs"; "0regs'"; "0ret"; "0rom"; ">BV"; ">Z_to_bv"; ">bv"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
Section FPX_1. Context {fx : PropExec.FPState}.
#[local] Ltac unorm :=
repeat match goal with
| |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
end.
#[local] Ltac cond :=
rwH; unfold at_, v_addi, v_add, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
#[local] Ltac wval :=
gres; rwH; unfold at_, v_addi, v_add, v_sub; imm_norm; unorm; first [reflexivity | f_equal; lia].
Lemma rdn_byte_at : ltac2:(TCodec.tc2 tcn__Jb0DiagStrlen "R4'Q<yR0%211'7y8%511%311p051'@'5'4%116':%:12&G&Ir5&Q;r4%22B1r3%746521(0r2%22=1%=3<41&>%1249&Kzr6%3221&L&Jr7&M%11B%4231&N+2+R0%3221%:251r9r8%:1M%=221%N2Q>1u1%Q34Q2621(2&?%Q32Q@G%24Q@Q5G1(6%11QB%63QC31%Q32Q>1%Q>3Q=91p0A1p0M1p0Q21p0Q51pR6QF1pR2QE1pR8QH1pR0QJ1pQ6QL1").
Proof.
intros M a n bs j H Hj Ha Hn.
pose proof (rdn_nth ASEGS M n (Z_to_bv 64 a) bs j H Hj) as R.
replace (Z_to_bv 64 a + nat_to_word j) with (Z_to_bv 64 (a + Z.of_nat j)) in R; [exact R|].
apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r. reflexivity.
Qed.
Section ISL.
Variable M rom : word -> option byte.
Variable p : Z.
Variable bs : list byte.
Hypothesis Hp : (0 <= p)%Z /\ (p + Z.of_nat (length bs) + 1 < 2 ^ 63)%Z.
Hypothesis HS : rdn ASEGS M (Z_to_bv 64 p) (length bs + 1) = Some (bs ++ [Z_to_bv 8 0]).
Hypothesis HNZ : forall j, (j < length bs)%nat -> bv_unsigned (nth j bs (Z_to_bv 8 0)) <> 0%Z.
#[local] Notation n := (Z.of_nat (length bs)).
Lemma byte_j : ltac2:(TCodec.tc2 tcn__Jb0DiagStrlen "Q='5'=r1&3'Q<y8%211vQ0%5221%8271':'7'4%117%311&G&IvB&Q;yR0&JvQ4&Mr2%211%5241%8271u1%=4<;21(0(2&?&1z%@2M1(6%11N%73O31%63Q0O1%84Q1@15%:3Q214%<2L1%Q03L>1p0Q21pR6Q<1").
Proof. intros j Hj. apply (rdn_byte_at M p (length bs + 1)); [exact HS | lia | lia | lia]. Qed.
Lemma isl_loop : ltac2:(TCodec.tc2 tcn__Jb0DiagStrlen "R@'5&Ay5'Q<yR0%211%5241&Dr2%211':&Er4(Q:+1(8%33>21%6251r3%93>21r5+:%93D17%<231&Q;vQ4%22F1%A3F41r6+;%A3L1?%D231&M%11E%:2N1%I3N41&<r8%22B1&3y8%Q611vQ0%4221%Q23Q<61';'9'C&I&FvQ1r9+a[i@%Q83QA1Q6/01QAvBvQ9%8576321r1%:591F43%=3<31%QB23Q7%N1C%Q72QK1%QF3QK31&H%12?8%E231%F281qR@QO1%I2R01p0K1p0Q51p0Q>1p0QG1p0R21pR6R<1pRBR81pR>R81pR<R?1").
Proof.
induction q as [|q IH]; intros regs ret j Hret H1 H10 H11 Hq.
-
assert (B : rdn ASEGS M (Z_to_bv 64 (p + Z.of_nat j)) 1%nat = Some [Z_to_bv 8 0]).
{ rewrite (byte_j j) by lia. rewrite app_nth2 by lia. replace (j - length bs)%nat with 0%nat by lia. reflexivity. }
eexists. split.
+ stepiv (ltac:(oF' 0x8af30%Z)) (ltac:(oD' 0x8af30%Z)) (Z_to_bv 64 (p + Z.of_nat j)) ltac:(wval).
chain_step; [reflexivity | eapply step_lbu; [exact (ltac:(oF' 0x8af34%Z)) | reflexivity | exact (ltac:(oD' 0x8af34%Z)) | gres; rwH; imm_norm; rewrite ?v_addi_0; exact B] | step_simpl; vnorm].
stepiv (ltac:(oF' 0x8af38%Z)) (ltac:(oD' 0x8af38%Z)) (Z_to_bv 64 (Z.of_nat j + 1)) ltac:(wval).
stepb_ft (ltac:(oF' 0x8af3c%Z)) (ltac:(oD' 0x8af3c%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x8af40%Z)) (ltac:(oD' 0x8af40%Z)) (Z_to_bv 64 n) ltac:(wval).
stepret (ltac:(oF' 0x8af44%Z)) (ltac:(oD' 0x8af44%Z)) ret ltac:(rwH; reflexivity).
apply mst_refl.
+ split; [gres; reflexivity | solve_keeps_cs].
- assert (B : rdn ASEGS M (Z_to_bv 64 (p + Z.of_nat j)) 1%nat = Some [nth j bs (Z_to_bv 8 0)]).
{ rewrite (byte_j j) by lia. rewrite app_nth1 by lia. reflexivity. }
pose proof (HNZ j ltac:(lia)) as NZ. pose proof (u8_range (nth j bs (Z_to_bv 8 0))) as R8.
eapply (runs_trans ASEGS _ (fun r => mkst r (0x8af30 : word) M rom)
(fun r => getr r 1 = ret /\ getr r 10 = Z_to_bv 64 p /\ getr r 11 = Z_to_bv 64 (Z.of_nat (Datatypes.S j)) /\ keeps_cs regs r)).
+ eexists. split.
* stepiv (ltac:(oF' 0x8af30%Z)) (ltac:(oD' 0x8af30%Z)) (Z_to_bv 64 (p + Z.of_nat j)) ltac:(wval).
chain_step; [reflexivity | eapply step_lbu; [exact (ltac:(oF' 0x8af34%Z)) | reflexivity | exact (ltac:(oD' 0x8af34%Z)) | gres; rwH; imm_norm; rewrite ?v_addi_0; exact B] | step_simpl; vnorm].
stepiv (ltac:(oF' 0x8af38%Z)) (ltac:(oD' 0x8af38%Z)) (Z_to_bv 64 (Z.of_nat j + 1)) ltac:(wval).
stepb_tk (ltac:(oF' 0x8af3c%Z)) (ltac:(oD' 0x8af3c%Z)) ltac:(cond).
apply mst_refl.
* cbv beta. repeat split; gres; rwH; try reflexivity; try (f_equal; lia). solve_keeps_cs.
+ cbv beta. intros r1 (R1 & R10 & R11 & K1).
destruct (IH r1 ret (Datatypes.S j) Hret R1 R10 R11 ltac:(lia)) as (r2 & RUN & V & K2).
exists r2. split; [exact RUN | split; [exact V | eapply keeps_cs_trans; eassumption]].
Qed.
Theorem internal_strlen_run : ltac2:(TCodec.tc2 tcn__Jb0DiagStrlen "R0&Ay5'Q<yR0%211%5241&Dr1%211':&Er3(Q:+1(8%33>21%6251r2%93>21r4+:%93D17%<231&Q;vQ4%22F1%A3F41';'9'C&I&FvQ1r6+a[i<%G3Q01E/01Q0vBvQ9%8576321r5%:59Q2143%=3<31%Q12Q4F&M&3y8%Q=11vQ0%4221%611%L2Q@1%Q;3Q@91&H%12EQ?%K231%L2>1qR@QD1%O2QE1p0Q11p0Q:1p0QE1pRBQJ1pR>QJ1").
Proof.
intros regs ret Hret H1 H10.
eapply (runs_trans ASEGS _ (fun r => mkst r (0x8af30 : word) M rom)
(fun r => getr r 1 = ret /\ getr r 10 = Z_to_bv 64 p /\ getr r 11 = Z_to_bv 64 (Z.of_nat 0) /\ keeps_cs regs r)).
- eexists. split.
+ stepn (ltac:(oF' 0x8af2c%Z)) (ltac:(oD' 0x8af2c%Z)). apply mst_refl.
+ cbv beta. repeat split; gres; rwH; try reflexivity. solve_keeps_cs.
- cbv beta. intros r1 (R1 & R10 & R11 & K1).
destruct (isl_loop (length bs) r1 ret 0%nat Hret R1 R10 R11 ltac:(lia)) as (r2 & RUN & V & K2).
exists r2. split; [exact RUN | split; [exact V | eapply keeps_cs_trans; eassumption]].
Qed.
End ISL.
End FPX_1.
