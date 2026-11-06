(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Export StartupTac RefMemcpyLib.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__SumsLib () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.DecodeC."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SumsLib.FPX_2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SumsLib.FPX_2.MEMK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SumsLib.FPX_2.MSETK."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1cons"; "1false"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2I"; "2and"; "2eq"; "2or"; "3repeat"]; ["4Z"; "5Segment"; "6MachineOk"; "6fetch_word"; "6is_ecall"; "6machine_result"; "6machine_state"; "6step"; "6store_ok"; "6word_to_le_bytes"; "7decode_any"; "8ALU_OR"; "8Op"; "8SZ1"; "8Store"; "8instr"]; ["9bv_eqb"; "9bvmap"; ":wbytes"; ";at_"; "<getr"; "<mkst"; "<rdn"; "<regupd"; "<v_add"; "<v_addi"; "<v_or"; "<v_slli"; "=M8"; ">b_"; ">memk"; "?msetk"]; ["=b_"; "@add"; "@land"; "@le"; "@lor"; "@lt"; "@modulo"; "@mul"; "@of_nat"; "@pow"; "@shiftr"; "0a"; "0b"; "0bs"; "0c"; "0d"]; ["0dst"; "0e"; "0fx"; "0imm"; "0j"; "0k"; "0k0"; "0m"; "0mem"; "0mem0"; "0n"; "0pc"; "0rd"; "0regs"; "0rom"; "0rs1"]; ["0rs2"; "0s"; "0segs"; "0src"; "ABV"; "AZ_to_bv"; "Abv"; "Abv_signed"; "Abv_unsigned"; "0v"; "0w"; "0x"; "0y"; "0z"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FPX_1. Context {fx : PropExec.FPState}.
Fixpoint code_at (segs : list Segment) (base : word) (off : Z) (ws : list (bv 32)) : Prop :=
match ws with
| [] => True
| w :: ws' => fetch_word segs (at_ base off) = Some w /\ code_at segs base (off + 4)%Z ws'
end.
End FPX_1.
Ltac code_at_vm :=
cbn [code_at Z.add Pos.add Pos.succ];
repeat split;
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Ltac zlit_at :=
repeat match goal with
| |- context [at_ ?b (?x + ?y)%Z] =>
is_Z_lit x; is_Z_lit y;
let z := eval cbv in (x + y)%Z in change (at_ b (x + y)%Z) with (at_ b z)
end.
Ltac rwH :=
repeat match goal with
| H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
end.
Ltac fold_at_vars :=
repeat match goal with
| |- context [v_addi ?b ?e] => is_var b; change (v_addi b e) with (at_ b e)
end.
Ltac vn :=
gres; rwH; imm_norm; unfold btgt;
rewrite ?at_addi; rewrite ?v_addi_0, ?v_add_0_r, ?v_add_0_l;
fold_at_vars; rewrite ?at_addi; zlit_at; vals_lit.
Ltac pcn := vn.
Ltac an F D :=
lazymatch type of D with
| decode_any _ = Some (Jal _ _, _) => stepj F D; vn
| _ => stepi F D; vn
end.
Ltac av F D v tac := stepiv F D v ltac:(gres; rwH; imm_norm; tac); vn.
Ltac ab_tk F D tac :=
chain_step;
[ reflexivity
| lazymatch type of D with
| decode_any _ = Some (Branch BC_EQ _ _ _, _) => eapply step_beq_tk
| decode_any _ = Some (Branch BC_NE _ _ _, _) => eapply step_bne_tk
| decode_any _ = Some (Branch BC_LT _ _ _, _) => eapply step_blt_tk
| decode_any _ = Some (Branch BC_GE _ _ _, _) => eapply step_bge_tk
| decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_tk
| decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_tk
end;
[ exact F | reflexivity | exact D | gres; rwH; imm_norm; tac ]
| step_simpl; vn ].
Ltac ab_ft F D tac :=
chain_step;
[ reflexivity
| lazymatch type of D with
| decode_any _ = Some (Branch BC_EQ _ _ _, _) => eapply step_beq_ft
| decode_any _ = Some (Branch BC_NE _ _ _, _) => eapply step_bne_ft
| decode_any _ = Some (Branch BC_LT _ _ _, _) => eapply step_blt_ft
| decode_any _ = Some (Branch BC_GE _ _ _, _) => eapply step_bge_ft
| decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_ft
| decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_ft
end;
[ exact F | reflexivity | exact D | gres; rwH; imm_norm; tac ]
| step_simpl; vn ].
Ltac aret F D k :=
stepjr F D k ltac:(gres; rwH; reflexivity);
imm_norm;
try lazymatch goal with
| Hk : ret_ok k |- _ => rewrite (Hk : v_jalr k 0 = k)
end.
Ltac condz :=
rwH; unfold at_, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; unorm; lia.
Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try reflexivity; try (f_equal; lia).
Section FPX_2. Context {fx : PropExec.FPState}.
Lemma at_fold : ltac2:(TCodec.tc2 tcn__SumsLib "B'RFyR0%211'@'=&RE&QA&RHr2%2281r1%5221%72;1&Q3%1264%;3=31pT0=1pSH?1").
Proof. reflexivity. Qed.
Lemma v_add_at : ltac2:(TCodec.tc2 tcn__SumsLib "M'RFyR0%211'@'<&QCzr1%3221&QE&QI+2+R0%3221%5271%;271'=&Q8r3&REr2%22D1%5241&Q3%1264%93G31p0;1pULH1pSHJ1").
Proof. intros a z Hz. unfold v_add, at_. rewrite (u_Z2bv z) by lia. reflexivity. Qed.
Lemma at_eq_u : ltac2:(TCodec.tc2 tcn__SumsLib "Q8'RFyR0%211'@'<&QCz&QA&RHr3%2291r2%5221%8271&QE&QI+2+R0%3221%5271%@271r4%>2E1%@21<%C2B1%;227%F221'=&Q3r5%2219%322F%53N21%63N4<p021p091p0@1pT4Q21pT0Q31pSHQ51").
Proof.
intros a d e Hd He H. apply (f_equal bv_unsigned) in H. rewrite !at_u in H by lia. lia.
Qed.
Record cpyH (segs : list Segment) (mem0 : word -> option byte) (dst src : word) (n : Z) (bs : list byte) : Prop := CPYH {
cHn : (0 <= n)%Z;
cHlen : length bs = Z.to_nat n;
cHsrc : rdn segs mem0 src (length bs) = Some bs;
cHdst : store_ok segs mem0 dst (length bs) = true;
cHdisj : (bv_unsigned dst + n <= bv_unsigned src \/ bv_unsigned src + n <= bv_unsigned dst)%Z;
cHnws : (bv_unsigned src + n < 2 ^ 64)%Z;
cHnwd : (bv_unsigned dst + n < 2 ^ 64)%Z }.
Section MEMK.
Variable segs : list Segment.
Variable mem0 : word -> option byte.
Variables dst src : word.
Variable n : Z.
Variable bs : list byte.
Hypothesis HOK : cpyH segs mem0 dst src n bs.
Let Hn := cHn _ _ _ _ _ _ HOK.
Let Hlen := cHlen _ _ _ _ _ _ HOK.
Let Hsrc := cHsrc _ _ _ _ _ _ HOK.
Let Hdst := cHdst _ _ _ _ _ _ HOK.
Let Hdisj := cHdisj _ _ _ _ _ _ HOK.
Let Hnws := cHnws _ _ _ _ _ _ HOK.
Let Hnwd := cHnwd _ _ _ _ _ _ HOK.
Definition memk (k : Z) : word -> option byte := wbytes mem0 dst (firstn (Z.to_nat k) bs).
Definition b_ (j : Z) : byte := nth (Z.to_nat j) bs (Z_to_bv 8 0).
Lemma memk_0 : ltac2:(TCodec.tc2 tcn__SumsLib ">'='RFyR0%211'7y8%511%311p051&Q>z%211vR9%=3521").
Proof. reflexivity. Qed.
Lemma memk_n : ltac2:(TCodec.tc2 tcn__SumsLib "B'='RFyR0%211'7y8%511%311p051&Q>vR:%211&Q2vR9vR0vQM%43321%A3961").
Proof. unfold memk. rewrite <- Hlen, firstn_all. reflexivity. Qed.
Lemma rd_src1 : ltac2:(TCodec.tc2 tcn__SumsLib "Q?'@'<&QCzr2%3221vR:%5231%7231&QAr3+1%3221%;217'='7'4'RFy8%211%411%611&Q6vRB&Q>r5%211&Q3vRCr4%3221u1%:49621(0(2&Q=%117(6%11C%53D31%72D1%K3D91p0M1p0Q61p0Q41pT:Q=1pT<Q>1").
Proof.
intros k j Hk Hj H1. unfold memk, b_.
pose proof (u64_range src). pose proof (u64_range dst).
rewrite rdn_wbytes_out.
- replace (at_ src j) with (at_ src (Z.of_nat (Z.to_nat j))) by (f_equal; lia).
rewrite (rdn_sub segs mem0 (length bs) src bs (Z.to_nat j) 1 Hsrc) by (rewrite Hlen; lia).
rewrite sub_nth by (rewrite Hlen; lia). reflexivity.
- rewrite length_firstn, Hlen, at_u; cbn; lia.
- rewrite at_u; cbn; lia.
- rewrite length_firstn, Hlen. lia.
Qed.
Lemma wr_dst : ltac2:(TCodec.tc2 tcn__SumsLib "Q0'@'5&QCzr2%3221&QAr3&QH%115%4231vR:%:221'='1&HvRB&Q>r5%211&Q3vR0r4%3221%94851A(:%=3<21p0?1p0G1pT@L1pT:N1pT<O1").
Proof.
intros k j m Hj Hm. unfold memk.
apply (store_ok_at segs mem0 dst (length bs)); try assumption; rewrite ?Hlen; lia.
Qed.
Lemma memk_extend1 : ltac2:(TCodec.tc2 tcn__SumsLib "Q8'@&QCzr1%3221&QAr2+1%3221vR:%9221'='RFyR0%211'7y8%511%311p051&Q2&Q>r3%211&Q3vR0%2214(2&Q=%117(6%11>%53?31%=3:71%M2<K%>11%I3A31p0K1p0Q21pT<Q71").
Proof.
intros k Hk H1. unfold memk, b_.
replace (at_ dst k) with (at_ dst (Z.of_nat (Z.to_nat k))) by (f_equal; lia).
rewrite <- sub_nth by (rewrite Hlen; lia).
rewrite wbytes_extend' by (rewrite Hlen; lia). f_equal. f_equal. lia.
Qed.
Lemma mc_lbu : forall regs pc rom w rd rs (imm : bv 12) k j0 j,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
getr regs rs = at_ src j0 -> (j0 + bv_signed imm = j)%Z ->
(0 <= k <= n)%Z -> (0 <= j)%Z -> (j + 1 <= n)%Z ->
RiscvSemantics.step segs (mkst regs pc (memk k) rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 (bv_unsigned (b_ j)))) (v_addi pc 4) (memk k) rom).
Proof.
intros regs pc rom w rd rs imm k j0 j Hf He Hd Hrs Hj Hk Hj0 Hj1.
eapply step_lbu; [exact Hf | exact He | exact Hd |].
rewrite Hrs, at_addi, Hj. apply rd_src1; lia.
Qed.
Lemma mc_sb : ltac2:(TCodec.tc2 tcn__SumsLib "SI&Q1y5'RFyR0%211%5241'7y8%611%311p061yQ0%:11%;1<y<%=11'@'=%<16&CvRBr9%3221(0r7%22=1%93841'1&Dr8%211(3%?3521'9'O%221C%N11&J%11A(8(N(Mr6%342>C1+4%64;M21%G2;1%N3;91&Q4r=%221M&Q3vR0r5%3221%Q63QC51&QA&RG%12Q<M%32A1%Q;3Q<1Q4r?r:%?221%Q?3QL1F&RE&RH%12R0Q;%32QM1&Q=%11QA%QF3QO31&QCz%221<r;+1%E221vR:%7221'E'F%211&G&Q5vR2rCrB&Q>r<%211rA%8576521%:2R91(B&Q9%129QD%Q928E%:11%?5>=318%62C1%RD3C81p0G1p0M1p0Q11p0Q91p0Q>1p0QD1p0QM1p0R=1p0RD1pUDS;1pT>S01pT<S11pT8S31pU2S61pU0S71pUFS91pTNS<1pTHSC1pTLSC1").
Proof.
intros regs pc rom w rs1 rs2 imm k k0 v Hf He Hd Hrs1 Hk Hrs2 Hb Hk0 Hk1.
rewrite <- (memk_extend1 k) by lia.
eapply MmapSim.step_sb_at; [exact Hf | exact He | exact Hd | | exact Hrs2 | exact Hb |].
- rewrite Hrs1, at_addi, Hk. reflexivity.
- apply wr_dst; cbn; lia.
Qed.
End MEMK.
Lemma sb_val_b : ltac2:(TCodec.tc2 tcn__SumsLib "E'4'RFy8%211%411'@'=&RE&RHyR0&Q@r2r1%3221%62<1%8261%8271%:2?1%<3?15pT:>1pSL@1").
Proof.
intros bs j. pose proof (u8_range (b_ bs j)). rewrite u_Z2bv by lia. apply Z_to_bv_bv_unsigned.
Qed.
Section MSETK.
Variable segs : list Segment.
Variable mem0 : word -> option byte.
Variable s : word.
Variable n : Z.
Variable b : byte.
Hypothesis Hn : (0 <= n)%Z.
Hypothesis Hnw : (bv_unsigned s + n < 2 ^ 64)%Z.
Hypothesis Hok : store_ok segs mem0 s (Z.to_nat n) = true.
Definition msetk (k : Z) : word -> option byte := wbytes mem0 s (repeat b (Z.to_nat k)).
Lemma msetk_0 : ltac2:(TCodec.tc2 tcn__SumsLib ">'='RFyR0%211'7y8%511%311p051&Q?z%211vR9%=3521").
Proof. reflexivity. Qed.
Lemma wr_s : ltac2:(TCodec.tc2 tcn__SumsLib "Q0'@'5&QCzr2%3221&QAr3&QH%115%4231vR:%:221'='1&HvRB&Q?r5%211&Q3vRAr4%3221%94851A(:%=3<21p0?1p0G1pT@L1pT:N1pT<O1").
Proof.
intros k j m Hj Hm. unfold msetk.
apply (store_ok_at segs mem0 s (Z.to_nat n)); try assumption; lia.
Qed.
Lemma msetk_extend : ltac2:(TCodec.tc2 tcn__SumsLib "Q3'@'5&QCzr2%3221'='RFyR0%211'7y8%511%311p051&Q2&Q?r3%211&Q3vRA%2214&?vQL%23<1D%:3741&QA&QH%11H%32<1%>11%I3A61p0K1pT@Q01pT<Q21").
Proof.
intros k m Hk. unfold msetk.
replace (Z.to_nat (k + Z.of_nat m)) with (Z.to_nat k + m)%nat by lia.
rewrite repeat_app, wbytes_app, repeat_length. f_equal. f_equal. lia.
Qed.
Lemma msetk_extend1 : ltac2:(TCodec.tc2 tcn__SumsLib "Q2'@&QCzr1%3221'='RFyR0%211'7y8%511%311p051&Q2&Q?r2%211&Q3vRA%2214(2vQL(6%11=%43>31%<3961&QA+1%22=1%?11%J3B51p0L1pT<Q11").
Proof. intros k Hk. apply (msetk_extend k 1). exact Hk. Qed.
End MSETK.
Lemma land_shl_disjoint : ltac2:(TCodec.tc2 tcn__SumsLib "O'@&QCzr3%3221r2%5241'<r4%8271&QE&QI+2%221:%4261%8261'=&QB&QGr6%928<%3221r5%6221%83H1Fp0:1p0D1p0G1pT<L1pSJM1pSHN1").
Proof.
intros a b k Ha Hk Hb. apply Z.bits_inj'. intros i Hi.
rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases i k) as [Hl|Hh].
- rewrite Z.mul_pow2_bits_low by lia. reflexivity.
- rewrite (Z_testbit_high k b i) by lia. apply Bool.andb_false_r.
Qed.
Lemma lor_shl_disjoint : ltac2:(TCodec.tc2 tcn__SumsLib "Q1'@&QCzr3%3221r2%5241'<r4%8271&QE&QI+2%221:%4261%8261'=&QD&QGr6%928<%3221r5%6221&QA%1243%:3J31p0<1p0F1p0I1pT<N1pSJO1pSHQ01").
Proof.
intros a b k Ha Hk Hb.
rewrite <- Z.lxor_lor by (apply land_shl_disjoint; lia).
symmetry. apply Z.add_nocarry_lxor. apply land_shl_disjoint; lia.
Qed.
Lemma v_slli_mul : ltac2:(TCodec.tc2 tcn__SumsLib "J'RFyR0%211'@&QCzr1%3221'=&Q;r3r2%3221&RE&QG&RH%12?6&QI+2%2218%6241%82D1%>3D:1p0@1pT<E1pUHG1").
Proof. intros x k Hk. unfold v_slli. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.
Lemma v_or_shl : ltac2:(TCodec.tc2 tcn__SumsLib "Q='RFyR0%211'@&QCzr2%3221&QE&QGr4&QI+2r3%3221%6251+R0%6251%:231&RHr6%22D1%;2:<%?221'=&Q:&REr5%A2@1%D291%42M1r7%7221&QA%?2Q13%2261%:2Q31%=3Q351p0?1p0E1p0Q11p0Q21pT<Q71pSHQ81pUHQ:1").
Proof.
intros x a k Ha Hk Hak Hx. pose proof (u64_range x). unfold v_or.
pose proof (Z.pow_nonneg 2 k ltac:(lia)).
rewrite u_Z2bv by nia. rewrite lor_shl_disjoint by lia. reflexivity.
Qed.
Definition M8 : Z := 72340172838076673.
Lemma M8_digit : ltac2:(TCodec.tc2 tcn__SumsLib "QB'@'<&QCzr2%3221&QE+X0%2241%8241'>'=%13<89+1%33>:1+2%53@<1+3%73B>1+4%93D@1+5%;3FB1+6%=3HD1+7%?3JF1%A231%B261%C291%D2<1%E2?1%F2B1%G2E1&QF&QJ&QGr4&Q<%3221+8r3%6221%8241%:21Q5%Q23Q=18p0=1p0Q61pT<Q@1pSNQA1").
Proof.
intros c k Hc Hk. unfold M8. rewrite Z.shiftr_div_pow2 by lia.
assert (G : forall Mhi Mlo B, (0 < B)%Z -> (Mhi * B + Mlo = 72340172838076673)%Z -> (0 <= Mlo)%Z ->
(255 * Mlo < B)%Z -> (Mhi mod 256 = 1)%Z ->
(c * 72340172838076673 / B mod 256 = c)%Z).
{ intros Mhi Mlo B HB HM Hlo Hlt Hm1.
replace (c * 72340172838076673)%Z with (c * Mhi * B + c * Mlo)%Z by nia.
rewrite Z.div_add_l by lia. rewrite (Z.div_small (c * Mlo) B) by nia.
rewrite Z.add_0_r, <- Zmult_mod_idemp_r, Hm1, Z.mul_1_r. apply Z.mod_small. lia. }
destruct Hk as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]].
- apply (G 72340172838076673 0 1)%Z; reflexivity || lia.
- apply (G 282578800148737 1 (2^8))%Z; try reflexivity; lia.
- apply (G 1103823438081 257 (2^16))%Z; try reflexivity; lia.
- apply (G 4311810305 65793 (2^24))%Z; try reflexivity; lia.
- apply (G 16843009 16843009 (2^32))%Z; try reflexivity; lia.
- apply (G 65793 4311810305 (2^40))%Z; try reflexivity; lia.
- apply (G 257 1103823438081 (2^48))%Z; try reflexivity; lia.
- apply (G 1 282578800148737 (2^56))%Z; try reflexivity; lia.
Qed.
Lemma byte_eq_mod : ltac2:(TCodec.tc2 tcn__SumsLib "D'@'=&QFr2+X0%3221r1%5213%73831'RFy8%211&REr3%2241%325<%?3521p091pUJB1pUHC1").
Proof. intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. exact H. Qed.
Lemma rep8_bytes : ltac2:(TCodec.tc2 tcn__SumsLib "Q0'@'<&QCzr1%3221&QE+X0%2241%8241'='4'RFy8%211%411&Iu8&REyR0&QGr2&Q<%3221%6251%9281&?%92>6%23>1;%C3>41p0E1pSNO1").
Proof.
intros c Hc. unfold word_to_le_bytes. rewrite u_Z2bv by (unfold M8; lia).
cbn [Z_to_le_bytes repeat]. rewrite !Z.shiftr_shiftr by lia. cbn [Z.add Pos.add Pos.succ].
pose proof (M8_digit c) as D.
repeat match goal with
| |- (_ :: _) = (_ :: _) => f_equal
| |- Z_to_bv 8 _ = Z_to_bv 8 _ => apply byte_eq_mod; rewrite (Z.mod_small c 256) by lia
| |- [] = [] => reflexivity
end.
- rewrite <- (D 0%Z) at 2 by lia. rewrite Z.shiftr_0_r || (cbn [Z.mul]; rewrite Z.shiftr_0_r). reflexivity.
- apply (D 1%Z); lia.
- apply (D 2%Z); lia.
- apply (D 3%Z); lia.
- apply (D 4%Z); lia.
- apply (D 5%Z); lia.
- apply (D 6%Z); lia.
- apply (D 7%Z); lia.
Qed.
Lemma sb_byte_u : ltac2:(TCodec.tc2 tcn__SumsLib "A'RFyR0%211'=y8%511&RE&RHr1%2281%4261&QF+X0%2241%82:1%<3:51pSN>1").
Proof. intros c. apply byte_eq_mod. rewrite Z.mod_mod by lia. reflexivity. Qed.
Lemma step_or_at : ltac2:(TCodec.tc2 tcn__SumsLib "S4'4'A%211&Q1y5'RFyR0%211%5241'7y8%611%311p061yQ0%:11%;1<'=%913&Cr:r8%3221(0r5%22:1%93841'1&Dr6%211(3%?3521'9'O'@%3221%L11&Jr7%211(8(L(Kr4%342@E1+4%64=<21%I2<1%Q03<91&Q0(RDz(;%33QB21%53QC@1%Q73M1I&Q:&Q4r=%221E%322Q0%5221%Q>3QH1Q7'E'F%211&Gr?&Q5vR2r>r<r;%5543?21%8271(B&Q7r9%2381QB&Q9%12FQ3%=5<31:9%72B1%R33B91p0F1p0N1p0Q61p0QH1p0QO1pUDRC1pU2R;1pU0R<1pTJR=1pUFR?1pTNRB1pTBRC1pTHRJ1pTLRJ1pU6S11").
Proof.
intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
rewrite (step_or segs regs pc mem rom w rd rs1 rs2 Hf He Hd).
rewrite Hrd, Hv. reflexivity.
Qed.
End FPX_2.
Ltac av_or F D vv tac :=
chain_step;
[ reflexivity
| eapply step_or_at with (v := vv); [ exact F | reflexivity | exact D | reflexivity | gres; rwH; imm_norm; tac ]
| step_simpl ]; vn.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
