(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StoreOk AgentLib
SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 RefMemcpyLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__LibTail () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymDrive."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1app"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "2I"; "2and"; "2eq"; "2not"; "3add"; "4lt"; "5nth"]; ["6Z"; "0E"; "7Segment"; "8ALU_ADD"; "8ALU_SLTU"; "8ALU_SUB"; "8ALU_XOR"; "8M_MUL"; "9bv_eqb"; "9bv_lts"; "9bv_ltu"; "9bvmap"; "0R"; ":getr"; ":rdn"; ":v_add"]; [":v_addiw"; ":v_mul"; ":v_sltu"; ":v_sub"; ":v_xor"; ";callee_saved"; "<junk_vals"; "=EAlu"; "=EAluw"; "=ELit"; "=EMd"; "=EVar"; "=SA"; "=adenot"; "=edenot"; "=env"]; ["=ev"; "=expr"; ">vals_ev"; "?In"; "@add"; "@eqb"; "@le"; "@lt"; "@ltb"; "@modulo"; "@mul"; "@of_nat"; "@pow"; "@sub"; "0a"; "0b"]; ["0b1"; "0b2"; "0bs"; "0d"; "0i"; "0j"; "0k"; "0k'"; "0m"; "0n"; "0n1"; "0n2"; "0segs"; "ABV"; "AZ_to_bv"; "Abv"]; ["Abv_unsigned"; "0vals"; "0w"; "0w'"; "0x"; "0y"; "0z"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.
Lemma zbv_mod : ltac2:(TCodec.tc2 tcn__LibTail "A'@';'R?yR0%211&R>&QIr1&QL+2+R0%3221%6251%82:1%92;7%>3;21pU>@1").
Proof.
intros z. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. apply Z.mod_mod. lia.
Qed.
Lemma vadd_ZZ : ltac2:(TCodec.tc2 tcn__LibTail "B'@';'R?yR0%211&O&R>r2%2251r1%4271%6231&QD%1264%82;1%>3;41pU<@1pU:A1").
Proof.
intros x y. unfold v_add. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
rewrite <- zbv_mod, <- Z.add_mod by lia. apply zbv_mod.
Qed.
Lemma vsub_ZZ : ltac2:(TCodec.tc2 tcn__LibTail "B'@';'R?yR0%211&Q3&R>r2%2251r1%4271%6231&QM%1264%82;1%>3;41pU<@1pU:A1").
Proof.
intros x y. unfold v_sub. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
rewrite <- zbv_mod, <- Zminus_mod. apply zbv_mod.
Qed.
Lemma vmul_ZZ : ltac2:(TCodec.tc2 tcn__LibTail "B'@';'R?yR0%211&Q1&R>r2%2251r1%4271%6231&QJ%1264%82;1%>3;41pU<@1pU:A1").
Proof.
intros x y. unfold v_mul. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
rewrite <- zbv_mod, <- Z.mul_mod by lia. apply zbv_mod.
Qed.
Lemma word_Z : ltac2:(TCodec.tc2 tcn__LibTail ";'R?yR0%211';r1&R>&R@%1263%3271%63751pU681").
Proof. intros w. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma vadd_wZ : ltac2:(TCodec.tc2 tcn__LibTail "C'R?yR0%211'@';&Or2&R>r1%2281%5241&QD&R@%12<7%3216%82>1%<3>61pU<>1pU6@1").
Proof. intros w y. rewrite (word_Z w) at 1. apply vadd_ZZ. Qed.
Lemma vadd_Zw : ltac2:(TCodec.tc2 tcn__LibTail "C'@'R?yR0%211';&O&R>r2%2261r1%5221&QD&R@%12;4%3271%92=1%<3=61pU6>1pU:B1").
Proof. intros x w. rewrite (word_Z w) at 1. apply vadd_ZZ. Qed.
Lemma vadd_ww : ltac2:(TCodec.tc2 tcn__LibTail "B'R?yR0%211';&Or2r1%3221&R>&QD&R@%12:6%22;6%4221%62=1%<3=81pU8>1pU6?1").
Proof. intros. reflexivity. Qed.
Lemma vsub_wZ : ltac2:(TCodec.tc2 tcn__LibTail "C'R?yR0%211'@';&Q3r2&R>r1%2281%5241&QM&R@%12<7%3216%82>1%<3>61pU<>1pU6@1").
Proof. intros w y. rewrite (word_Z w) at 1. apply vsub_ZZ. Qed.
Lemma vsub_Zw : ltac2:(TCodec.tc2 tcn__LibTail "C'@'R?yR0%211';&Q3&R>r2%2261r1%5221&QM&R@%12;4%3271%92=1%<3=61pU6>1pU:B1").
Proof. intros x w. rewrite (word_Z w) at 1. apply vsub_ZZ. Qed.
Lemma vmul_wZ : ltac2:(TCodec.tc2 tcn__LibTail "C'R?yR0%211'@';&Q1r2&R>r1%2281%5241&QJ&R@%12<7%3216%82>1%<3>61pU<>1pU6@1").
Proof. intros w y. rewrite (word_Z w) at 1. apply vmul_ZZ. Qed.
Lemma vmul_Zw : ltac2:(TCodec.tc2 tcn__LibTail "C'@'R?yR0%211';&Q1&R>r2%2261r1%5221&QJ&R@%12;4%3271%92=1%<3=61pU6>1pU:B1").
Proof. intros x w. rewrite (word_Z w) at 1. apply vmul_ZZ. Qed.
Lemma ed_add : ltac2:(TCodec.tc2 tcn__LibTail "F'Q?'QA';'R?yR0%211&Q>r3(Q7(Cr2r1%43321%7261&O%9285%:295%3221%@3=51pT0B1pSNC1pQ4E1").
Proof. intros. cbn [edenot]. apply alu_add. Qed.
Lemma ed_sub : ltac2:(TCodec.tc2 tcn__LibTail "F'Q?'QA';'R?yR0%211&Q>r3(Q7(Er2r1%43321%7261&Q3%9285%:295%3221%@3=51pT0B1pSNC1pQ4E1").
Proof. intros. cbn [edenot]. apply alu_sub. Qed.
Lemma ed_mul : ltac2:(TCodec.tc2 tcn__LibTail "F'Q?'QA';'R?yR0%211&Q>r3(Q:(Gr2r1%43321%7261&Q1%9285%:295%3221%@3=51pT0B1pSNC1pQ4E1").
Proof. intros. cbn [edenot]. apply m_mul. Qed.
Lemma ed_xor : ltac2:(TCodec.tc2 tcn__LibTail "F'Q?'QA';'R?yR0%211&Q>r3(Q7(Fr2r1%43321%7261&Q4%9285%:295%3221%@3=51pT0B1pSNC1pQ4E1").
Proof. intros. cbn [edenot]. apply alu_xor. Qed.
Lemma ed_sltu : ltac2:(TCodec.tc2 tcn__LibTail "F'Q?'QA';'R?yR0%211&Q>r3(Q7(Dr2r1%43321%7261&Q2%9285%:295%3221%@3=51pT0B1pSNC1pQ4E1").
Proof. intros. cbn [edenot]. apply alu_sltu. Qed.
Lemma ed_lit : ltac2:(TCodec.tc2 tcn__LibTail "A'Q?'@';'R?yR0%211&Q>r2(Q9r1%211%5241&R>%1294%<3931pU>>1pQ4@1").
Proof. reflexivity. Qed.
Lemma ed_var : ltac2:(TCodec.tc2 tcn__LibTail "A'Q?'6';'R?yR0%211&Q>r2(Q;r1%211%5241&Q@%1264%<3931pTD>1pQ4@1").
Proof. reflexivity. Qed.
End FPX_1.
Ltac not_arith t :=
lazymatch t with
| v_add _ _ => fail | v_sub _ _ => fail | v_mul _ _ => fail | Z_to_bv _ _ => fail
| _ => idtac
end.
Ltac ed_lin pins :=
rewrite ?ed_add, ?ed_sub, ?ed_mul, ?ed_lit, ?ed_var, ?alu_add, ?alu_sub, ?m_mul; cbn [ev];
pins;
repeat match goal with
| |- context [v_add (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (vadd_ZZ x y)
| |- context [v_sub (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (vsub_ZZ x y)
| |- context [v_mul (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (vmul_ZZ x y)
| |- context [v_add ?w (Z_to_bv 64 ?y)] => not_arith w; rewrite (vadd_wZ w y)
| |- context [v_add (Z_to_bv 64 ?x) ?w] => not_arith w; rewrite (vadd_Zw x w)
| |- context [v_sub ?w (Z_to_bv 64 ?y)] => not_arith w; rewrite (vsub_wZ w y)
| |- context [v_sub (Z_to_bv 64 ?x) ?w] => not_arith w; rewrite (vsub_Zw x w)
| |- context [v_mul ?w (Z_to_bv 64 ?y)] => not_arith w; rewrite (vmul_wZ w y)
| |- context [v_mul (Z_to_bv 64 ?x) ?w] => not_arith w; rewrite (vmul_Zw x w)
| |- context [v_add ?w ?w'] => not_arith w; not_arith w'; rewrite (vadd_ww w w')
end.
Ltac ed_lin_in H pins :=
rewrite ?ed_add, ?ed_sub, ?ed_mul, ?ed_lit, ?ed_var, ?alu_add, ?alu_sub, ?m_mul in H; cbn [ev] in H;
pins;
repeat match type of H with
| context [v_add (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (vadd_ZZ x y) in H
| context [v_sub (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (vsub_ZZ x y) in H
| context [v_mul (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (vmul_ZZ x y) in H
| context [v_add ?w (Z_to_bv 64 ?y)] => not_arith w; rewrite (vadd_wZ w y) in H
| context [v_add (Z_to_bv 64 ?x) ?w] => not_arith w; rewrite (vadd_Zw x w) in H
| context [v_sub ?w (Z_to_bv 64 ?y)] => not_arith w; rewrite (vsub_wZ w y) in H
| context [v_sub (Z_to_bv 64 ?x) ?w] => not_arith w; rewrite (vsub_Zw x w) in H
| context [v_mul ?w (Z_to_bv 64 ?y)] => not_arith w; rewrite (vmul_wZ w y) in H
| context [v_mul (Z_to_bv 64 ?x) ?w] => not_arith w; rewrite (vmul_Zw x w) in H
| context [v_add ?w ?w'] => not_arith w; not_arith w'; rewrite (vadd_ww w w') in H
end.
Section FPX_2. Context {fx : PropExec.FPState}.
Lemma adenot_off_shift : ltac2:(TCodec.tc2 tcn__LibTail "QF'Q?'QA'@';r1&QDr3r2%3221%63751&QFz&R@yR0&Q>r6r5%3221%6251r4%?221%;2:1&QGr7%:219%=2<1%E21:&QL+2+R0%3221%9251'R?%11D&R>&Q=r8(Q<%12?G%4231%L2K1%Q421I%82M1%62DH%9281%Q:3<31p0?1p0J1p0Q71pT@Q?1pT8Q@1pT>QA1pT0QC1pQ4QE1").
Proof.
intros E b k d k' -> H0 H1. unfold adenot, v_addi. cbn [a_base a_off]. rewrite u_small by lia.
f_equal. lia.
Qed.
Lemma eqb_ZZ : ltac2:(TCodec.tc2 tcn__LibTail "N'@':&QFzr2%3221&QG&QL+2+R0%3221%5271%;271';'2&HyR0&R>r4%2231r3%4251%73631&QE%1264%<3;31p0>1p0?1pT0L1pSNM1").
Proof. intros. unfold bv_eqb. rewrite !u_small by lia. reflexivity. Qed.
Lemma ltu_ZZ : ltac2:(TCodec.tc2 tcn__LibTail "N'@':&QFzr2%3221&QG&QL+2+R0%3221%5271%;271';'2&JyR0&R>r4%2231r3%4251%73631&QH%1264%<3;31p0>1p0?1pT0L1pSNM1").
Proof. intros. unfold bv_ltu. rewrite !u_small by lia. reflexivity. Qed.
Lemma lts_ZZ : ltac2:(TCodec.tc2 tcn__LibTail "N'@':&QFzr2%3221&QG&QL+2+QO%3221%5271%;271';'2&IyR0&R>r4%2231r3%4251%73631&QH%1264%<3;31p0>1p0?1pT0L1pSNM1").
Proof.
intros a b Ha Hb. unfold bv_lts. rewrite !bv_signed_small; rewrite ?u_small; try lia.
all: change (bv_half_modulus 64) with (2 ^ 63)%Z; lia.
Qed.
End FPX_2.
Ltac unorm :=
repeat match goal with
| |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
lazymatch z with
| context [bv_unsigned (Z_to_bv 64 _)] => fail
| _ => rewrite (u_small z) by lia
end
end.
Section FPX_3. Context {fx : PropExec.FPState}.
Lemma rdn_app_Z : ltac2:(TCodec.tc2 tcn__LibTail "R5'5'B%211'R?yR0%211'8y8%511%311p051'@'6%=15';%912&Nr7r6&R>r5%22A1r4%746521(0r2%22=1%=3<41r8&QD&QK%11;%32>1%>2M1%B46A1<%E3D19&QFz%221E&QG%:1G%<2=1&QL+2+R0%3221%7251r;r:r9%O2Q>1&=%12HQ3%Q546531&1%13Q?Q5Q3%Q02Q;1%Q;3Q:41p0<1p0E1p0I1p0Q21pT4QA1pT2QB1pTHQD1pTFQE1pSNQG1pTBQI1pTJR21").
Proof.
intros segs m a n1 n2 b1 b2 H1 H2 Ha Hn.
apply rdn_app; [exact H1|]. rewrite w_add_nat, u_small by lia. exact H2.
Qed.
Lemma callee_saved_no0 : ltac2:(TCodec.tc2 tcn__LibTail "=&<&QC'R?y5%211(R=z(9%33521/015&Q5%:3721%<11").
Proof.
unfold callee_saved. intros Hin.
repeat (destruct Hin as [Hin|Hin]; [apply (f_equal bv_unsigned) in Hin; cbn in Hin; discriminate Hin|]).
exact Hin.
Qed.
Lemma vals_ev_junk : ltac2:(TCodec.tc2 tcn__LibTail "Q6'5'R?yR0%211%411&Ky5%2214'6&>r1uQ0%3221';&QB&1r4&Q6r3%211%53A41&=&4%12D7r2%4221%<261&M&R>&QK%116%32I1%52>1%D3N71p0F1pT:K1pQJM1pU4Q11").
Proof.
intros vals R i Hi. rewrite vals_ev_app_r. unfold vals_ev, junk_vals.
rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
Qed.
Lemma v_addiw_id_errno : ltac2:(TCodec.tc2 tcn__LibTail "G'R?yR0%211&QF&QM&QL+2+R0%3221+SoO%6221&R@r1%22<1%;241';&Q0r2z%3221%53B13p071pU:D1").
Proof.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
intros x Hx. pose proof (u64_range x) as Hr. unfold v_addiw. rewrite Z.add_0_r.
apply bv_eq. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31)%Z. change (bv_modulus 32) with (2 ^ 32)%Z.
replace ((bv_unsigned x + 2 ^ 31) mod 2 ^ 32)%Z with (bv_unsigned x + 2 ^ 31 - 2 ^ 64)%Z by
(apply Z.mod_unique with (q := (2 ^ 32)%Z); lia).
symmetry. apply Z.mod_unique with (q := (-1)%Z); lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
Lemma edenot_addw0_errno : ltac2:(TCodec.tc2 tcn__LibTail "Q2'Q?'QA&QF&QM&QL+2+R0%3221+SoO%6221&R@yR0&Q>r2r1%3221%6251%?281';'R?%119r3(Q8(C(Q9z%211%534>1%@271%A28@%<3:21p0>1pSNO1pQ4Q11").
Proof.
intros E a Ha. cbn [edenot]. rewrite low32_zero_sext, w_addiw.
change (bv_signed (0 : bv 12)) with 0%Z. apply v_addiw_id_errno. exact Ha.
Qed.
Lemma rdn_byte_Z : ltac2:(TCodec.tc2 tcn__LibTail "R7'5'B%211'R?yR0%211'8y8%511%311p051'@'6%=15';%912&Nr6r5&R>r4%22A1r3%746521(0r2%22=1%=3<41&>%1249&QFz%221?&QG&QDr7&QK%11A%4231&QL+2+R0%3221%:251r:r9r8%;1M%>221%N2Q=1u1%Q347621(3&?%Q32Q?G%24Q?Q5Q61(7%11QA%63QB31%Q32Q>1%Q>3Q=91p0B1p0N1p0Q21p0Q51pT<QE1pT6QE1pTDQG1pSNQI1pTBQK1pTJR41").
Proof.
intros segs m a n bs j H Hj Ha Hn.
pose proof (rdn_nth segs m n (Z_to_bv 64 a) bs j H Hj) as R. rewrite w_add_nat, u_small in R by lia. exact R.
Qed.
Lemma nth_app_l : forall {A} (l l' : list A) (d : A) j, (j < length l)%nat -> nth j (l ++ l') d = nth j l d.
Proof. intros. apply app_nth1. assumption. Qed.
Lemma In_nth_neq : forall {A} (l : list A) (x d : A) j, ~ In x l -> (j < length l)%nat -> nth j l d <> x.
Proof. intros A l x d j Hn Hj E. apply Hn. rewrite <- E. apply nth_In. exact Hj. Qed.
End FPX_3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
