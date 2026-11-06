(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SumsLib AsanMaxVAK AsanMaxVA_codeKB0.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__AsanMaxVAWalkKB0 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanMaxVAK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanMaxVAWalkKB0."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SumsLib."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2I"; "2and"; "2eq"; "2ex"; "3Z"; "4bvmap"; "5smear_step"; "6asan_maxva_entry"; "6asanreflect_fx"; "6maxva_clob"; "6maxva_words"; "7msteps"; "8at_"; "8regs_agree"; "9getr"]; ["9mkst"; "9v_or"; "9v_srli"; ":code_at"; ";loaded_segments"; "<In"; "=le"; "=lor"; "=lt"; "=pow"; "=shiftr"; "=sub"; "0a"; "0b"; "0base"; "0mem"]; ["0n"; "0r"; "0regs"; "0regs'"; "0rom"; "0s"; "0segs"; ">BV"; ">Z_to_bv"; ">bv"; ">bv_unsigned"; "0ua"; "0ub"; "0v"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma Zlor_lt_pow2 : ltac2:(TCodec.tc2 tcn__AsanMaxVAWalkKB0 "Q0'5'2&Fzr3%3221&H&I+2r1%3221%5271%;271r2%7261%92;1%?2;1&Gr6r5%3221%C2B1r4%@2?1%B241%H241p0E1p0;1p0@1pR2M1pRJN1pRHO1").
Proof. intros ua ub n.
intros Ha Hb Hn. split; [apply Z.lor_nonneg; lia|].
destruct (Z.eq_dec ua 0) as [->|Na]; [rewrite Z.lor_0_l; lia|].
destruct (Z.eq_dec ub 0) as [->|Nb]; [rewrite Z.lor_0_r; lia|].
assert (Hpos : (0 < Z.lor ua ub)%Z).
{ pose proof (Z.lor_nonneg ua ub). assert (Z.lor ua ub <> 0%Z) by (rewrite Z.lor_eq_0_iff; lia). lia. }
apply (proj2 (Z.log2_lt_pow2 (Z.lor ua ub) n Hpos)).
rewrite Z.log2_lor by lia. apply Z.max_lub_lt; [apply (proj1 (Z.log2_lt_pow2 ua n ltac:(lia)))| apply (proj1 (Z.log2_lt_pow2 ub n ltac:(lia)))]; lia.
Qed.
Lemma v_or_unsigned_t : ltac2:(TCodec.tc2 tcn__AsanMaxVAWalkKB0 "B'Q9yR0%211'3'5&Q:&Ar2r1%3221%5291&G%72;5%82<5%3221%<3;51pQL>1pQJ?1").
Proof. intros a b.
unfold v_or. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
pose proof (bv_unsigned_in_range 64 a) as Ha. pose proof (bv_unsigned_in_range 64 b) as Hb.
unfold bv_modulus in *. apply Zlor_lt_pow2; lia.
Qed.
Lemma v_srli_unsigned_t : ltac2:(TCodec.tc2 tcn__AsanMaxVAWalkKB0 "F'Q9yR0%211'5&Fzr1%3221'3&Q:&Br3r2%3221%52=1&J%72?5%2215%:3?41p0<1pR<A1pQJC1").
Proof. intros a s.
intros Hs. unfold v_srli. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
pose proof (bv_unsigned_in_range 64 a) as Ha. unfold bv_modulus in *.
split; [apply Z.shiftr_nonneg; lia|].
rewrite Z.shiftr_div_pow2 by lia. apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
pose proof (Z.pow_pos_nonneg 2 s). nia.
Qed.
Lemma u_smw : ltac2:(TCodec.tc2 tcn__AsanMaxVAWalkKB0 "G'5'Q9yR0%211&Fzr2%3221'3&Q:&A&Br3%2271%4281%62=1&7%82?;%2261%;3C41p0=1pRLB1pR<F1").
Proof. intros s v. intros Hs. unfold smear_step. rewrite v_or_unsigned_t, v_srli_unsigned_t by lia. reflexivity. Qed.
Lemma smear_word : ltac2:(TCodec.tc2 tcn__AsanMaxVAWalkKB0 "Q>'Q9yR0%211'2&F&I+2+Q>%3221&Q:r1%22:1%8241&H+Q?%:291%3251%>251'3&Ar2&B+1%2231%5241%421C%7221+4%7221%:231+8%:221%=231+@%=221%@231+Q0%@221%C231&Q8&K%12JC%32Q91%I3Q951p0K1pRNQ;1").
Proof. intros x.
intros Hx. apply bv_eq. rewrite Z_to_bv_unsigned.
rewrite (u_smw 32) by lia. rewrite (u_smw 16) by lia. rewrite (u_smw 8) by lia.
rewrite (u_smw 4) by lia. rewrite (u_smw 2) by lia. rewrite (u_smw 1) by lia.
change (bv_wrap 64 (2 ^ 47 - 1)) with (2 ^ 47 - 1)%Z.
exact (smear6_eq (bv_unsigned x) Hx).
Qed.
Definition maxva_words : list (bv 32) :=
[W_8c43c; W_8c440; W_8c444; W_8c448; W_8c44c; W_8c450; W_8c454; W_8c458; W_8c45c; W_8c460; W_8c464; W_8c468; W_8c46c; W_8c470; W_8c474; W_8c478; W_8c47c; W_8c480; W_8c484; W_8c488; W_8c48c; W_8c490; W_8c494; W_8c498; W_8c49c; W_8c4a0; W_8c4a4; W_8c4a8; W_8c4ac; W_8c4b0; W_8c4b4; W_8c4b8; W_8c4bc; W_8c4c0; W_8c4c4; W_8c4c8; W_8c4cc; W_8c4d0; W_8c4d4; W_8c4d8; W_8c4dc; W_8c4e0; W_8c4e4; W_8c4e8; W_8c4ec].
Definition maxva_clob : list reg := [10; 11; 12; 13; 14; 15].
Section MAXVA.
Variable segs : list Segment.
Variable base : word.
Variable mem : word -> option byte.
Variable rom : word -> option byte.
Hypothesis HCODE : code_at segs base 0 maxva_words.
Lemma smearva_run : ltac2:(TCodec.tc2 tcn__AsanMaxVAWalkKB0 "S8&6y5'Q9yR0%211%5241'3&?r2(Q7+:(1%33;21%6251r1%93;21'2&F&I+2+Q>%3221&Q:%12D?%7231&H+Q?%9281%3251%=251'4'<vQ6&@&9r5&=vNz%3221vOvQ4%9587321+UD%8271%<5;O154%?3>41%Q82Q1Q3&Q8&K+1%22H1%42QA1%Q?3QA61+;%Q>3QF1Q<%QA2Q:1+_oooooooooooO%:2QG1%QE3QG31+<%QD3QL1QB%QG2Q@1+SV\icV\icV\iC%@2QM1%QK3QM31+=%QJ3R21QH%QM2QF1+nSh_QlW`nSh?%F2R31%R13R331+>%R03R81QN%R32QL1+RPXQPTP`RPX1%L2R91%R73R931+?%R63R>1R4%R92R21+WoonPPPPPPPP0%Q22R?1%R=3R?31&>%RC1RD&E&:%233R:1qR441%631QGR<%R;281%R<2?1%R=2F1%R>2M1%R?2Q41%R@2Q;1%RA2QC1qR8RM1%R52RN1p0R71p0RF1pRNS21pR6S21").
Proof.
intros regs x Hx Hr.
pose proof HCODE as HC; cbv [code_at maxva_words] in HC.
repeat match type of HC with context [at_ base (?a + ?b)%Z] => let c := eval vm_compute in (a + b)%Z in change (a + b)%Z with c in HC end.
destruct HC as (C0 & C4 & C8 & C12 & C16 & C20 & C24 & C28 & C32 & C36 & C40 & C44 & C48 & C52 & C56 & C60 & C64 & C68 & C72 & C76 & C80 & C84 & C88 & C92 & C96 & C100 & C104 & C108 & C112 & C116 & C120 & C124 & C128 & C132 & C136 & C140 & C144 & C148 & C152 & C156 & C160 & C164 & C168 & C172 & C176 & _).
eexists. split.
an C0 (ltac:(oD' 0x8c43c%Z)).
an C4 (ltac:(oD' 0x8c440%Z)).
an C8 (ltac:(oD' 0x8c444%Z)).
an C12 (ltac:(oD' 0x8c448%Z)).
an C16 (ltac:(oD' 0x8c44c%Z)).
an C20 (ltac:(oD' 0x8c450%Z)).
an C24 (ltac:(oD' 0x8c454%Z)).
an C28 (ltac:(oD' 0x8c458%Z)).
an C32 (ltac:(oD' 0x8c45c%Z)).
an C36 (ltac:(oD' 0x8c460%Z)).
an C40 (ltac:(oD' 0x8c464%Z)).
an C44 (ltac:(oD' 0x8c468%Z)).
an C48 (ltac:(oD' 0x8c46c%Z)).
an C52 (ltac:(oD' 0x8c470%Z)).
an C56 (ltac:(oD' 0x8c474%Z)).
an C60 (ltac:(oD' 0x8c478%Z)).
an C64 (ltac:(oD' 0x8c47c%Z)).
an C68 (ltac:(oD' 0x8c480%Z)).
an C72 (ltac:(oD' 0x8c484%Z)).
an C76 (ltac:(oD' 0x8c488%Z)).
an C80 (ltac:(oD' 0x8c48c%Z)).
an C84 (ltac:(oD' 0x8c490%Z)).
an C88 (ltac:(oD' 0x8c494%Z)).
an C92 (ltac:(oD' 0x8c498%Z)).
an C96 (ltac:(oD' 0x8c49c%Z)).
an C100 (ltac:(oD' 0x8c4a0%Z)).
an C104 (ltac:(oD' 0x8c4a4%Z)).
an C108 (ltac:(oD' 0x8c4a8%Z)).
rewrite (smear_word x Hr).
an C112 (ltac:(oD' 0x8c4ac%Z)).
an C116 (ltac:(oD' 0x8c4b0%Z)).
an C120 (ltac:(oD' 0x8c4b4%Z)).
an C124 (ltac:(oD' 0x8c4b8%Z)).
an C128 (ltac:(oD' 0x8c4bc%Z)).
an C132 (ltac:(oD' 0x8c4c0%Z)).
an C136 (ltac:(oD' 0x8c4c4%Z)).
an C140 (ltac:(oD' 0x8c4c8%Z)).
an C144 (ltac:(oD' 0x8c4cc%Z)).
an C148 (ltac:(oD' 0x8c4d0%Z)).
an C152 (ltac:(oD' 0x8c4d4%Z)).
an C156 (ltac:(oD' 0x8c4d8%Z)).
an C160 (ltac:(oD' 0x8c4dc%Z)).
an C164 (ltac:(oD' 0x8c4e0%Z)).
an C168 (ltac:(oD' 0x8c4e4%Z)).
an C172 (ltac:(oD' 0x8c4e8%Z)).
an C176 (ltac:(oD' 0x8c4ec%Z)).
apply mst_refl.
- repeat match goal with |- _ /\ _ => split end;
[gres; apply bv_eq; reflexivity| gres; reflexivity| gres; reflexivity| gres; reflexivity| gres; reflexivity| gres; reflexivity
| unfold maxva_clob; solve_regs_agree].
Qed.
End MAXVA.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
Definition asan_maxva_entry : word := 0x8c43c.
Lemma asan_maxva_code : ltac2:(TCodec.tc2 tcn__AsanMaxVAWalkKB0 "6&C&D&8z&;%544321").
Proof. unfold maxva_words. code_at_vm. Qed.
Theorem asan_smearva : ltac2:(TCodec.tc2 tcn__AsanMaxVAWalkKB0 "S='Q9yR0%211'0y8%511%311p051&6y5%2218'3&?r2(Q7+:(1%33821%6251r1%93B21'2&F&I+2+Q>%3221&Q:%12K?%7231&H+Q?%9281%3251%=251'4'<&D&@&9r5&8r7r6%6554321&=+UD%2261%:59M165%=3<51%Q62OQ1&Q8&K+1%22F1%42QF1%Q=3QF61+;%Q<3QA1Q:%Q?2Q81+_oooooooooooO%:2QL1%QC3QL31+<%QB3QG1Q@%QE2Q>1+SV\icV\icV\iC%@2R21%QI3R231+=%QH3QM1QF%QK2QD1+nSh_QlW`nSh?%F2R81%QO3R831+>%QN3R31QL%R12QJ1+RPXQPTP`RPX1%L2R>1%R53R>31+?%R43R91R2%R72R01+WoonPPPPPPPP0%Q22RD1%R;3RD31&>%RH1R?&E&:%233R81qR441%631QER:%R9281%R:2?1%R;2F1%R<2M1%R=2Q41%R>2Q;1%R?2QC1qR8RK1%R32RL1p0R51p0RD1pRNS71pR6S01pR:S41pR0S51").
Proof. intros mem rom regs x Hx Hr. pose proof (smearva_run _ _ mem rom asan_maxva_code regs x Hx Hr) as R. rewrite at_0 in R. exact R. Qed.
