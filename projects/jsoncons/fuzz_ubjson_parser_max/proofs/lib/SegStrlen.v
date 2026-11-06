(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim MuslStrlen RefMemcpyLib Js0MemcpyBase Js0Memchr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__SegStrlen () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SegStrlen."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SegStrlen.FPX_0."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SegStrlen.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SegStrlen.FPX_1.SLEN."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.musl.Js0Memchr."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1O"; "1Some"; "1bool"; "1cons"; "1false"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "2not"]; ["2or"; "3lt"; "4nth"; "5Z"; "0K"; "6bvmap"; "7msteps"; "8at_"; "8ret_ok"; "9c_eq"; "9getr"; "9mkst"; "9rdn"; "9regupd"; "9v_andi"; "9v_sub"]; [";sl_agree"; "=KE"; "=b_"; "=sb_"; "<TWs"; "<slenH"; ":sl_agree"; ":sl_clob"; ">Hc"; ">LDv"; ">Mc"; ">TW"; "?loaded_segments"; "@In"; "Aadd"; "Adiv"]; ["Ale"; "Alt"; "Amodulo"; "Aof_nat"; "Apow"; "Asub"; "0buf"; "0fx"; "0i"; "0j"; "0m"; "0mem"; "0r"; "0r1"; "0r2"; "0r3"]; ["0rd"; "0regs"; "0regs'"; "0ret"; "0rom"; "0s"; "BBV"; "BZ_to_bv"; "Bbv"; "Bbv_unsigned"; "0v"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition sl_clob : list reg := [10; 11; 12; 13; 14; 15; 16]%bv.
Section FPX_0. Context {fx : PropExec.FPState}.
Definition sl_agree (regs regs' : bvmap 5 word) : Prop := regs_agree (fun r => In r sl_clob) regs regs'.
Lemma sl_agree_refl : ltac2:(TCodec.tc2 tcn__SegStrlen ":&Ey5'R8yR0%211%5241&Q0r1%2211pT441").
Proof. intros regs. apply regs_agree_refl. Qed.
Lemma sl_agree_trans : ltac2:(TCodec.tc2 tcn__SegStrlen "A&Ey5'R8yR0%211%5241&Q0r3r2%3221r5%5214p031p041pT091pSN:1pSL;1").
Proof. intros r1 r2 r3. apply regs_agree_trans. Qed.
Lemma sl_agree_upd : ltac2:(TCodec.tc2 tcn__SegStrlen "I&Ey5'R8yR0%211%5241%415&Q0r4r3%3221&Q=&Q7%23741r6&Mr5%23198%;241p061p0:1pTFA1pT2@1pT6B1pT4C1").
Proof. intros regs regs' rd v H Hin. apply regs_agree_upd; assumption. Qed.
Lemma sl_agree_getr : ltac2:(TCodec.tc2 tcn__SegStrlen "L&Ey5'R8yR0%211%5241%415&Q0r3r2%3221&?&Q=&Q7%23851%411'=&Jr4%221;r5%421=%63B31p081p0>1pSJC1pT6E1pT4F1").
Proof. intros regs regs' r H Hn. apply H. exact Hn. Qed.
End FPX_0.
Ltac in_sl_clob := cbn [sl_clob In]; repeat first [ left; reflexivity | right ].
Ltac solve_sl_agree :=
repeat (apply sl_agree_upd; [| in_sl_clob]); first [apply sl_agree_refl | assumption].
Section FPX_1. Context {fx : PropExec.FPState}.
Definition TWs (x : word) : word := v_and (v_or (v_sub (Z_to_bv 64 Mc) x) x) (Z_to_bv 64 Hc).
Lemma TWs_TW : ltac2:(TCodec.tc2 tcn__SegStrlen ";'R8yR0%211'=&Q4r1%211&Q;%113%63731pTH81").
Proof. intros x. unfold TWs, TW. rewrite !v_xor_0. reflexivity. Qed.
Lemma v_sub_at : ltac2:(TCodec.tc2 tcn__SegStrlen "M'R8yR0%211'C'<&Q@zr1%3221&QA&QD+2+R0%3221%5271%;271'=&O&Gr3r2%3221%5213&R7%12G4%93G31p0;1pQ:H1pT<J1").
Proof.
intros s K HK. unfold v_sub, at_. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64)%Z.
rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.
Lemma v_sub_self : ltac2:(TCodec.tc2 tcn__SegStrlen "<'R8yR0%211'=&Or1%2211&R7z%2281%73841pT<91").
Proof. intros s. unfold v_sub. rewrite Z.sub_diag. reflexivity. Qed.
Lemma andi7_u : ltac2:(TCodec.tc2 tcn__SegStrlen "Q6'R8yR0%211'C'<&Q@z&Q>&R9r2%2291r1%5221%8271&QA&QD+2+R0%3221%5271%@271'=&N&Gr3%221@+7%5221%D2K1&QB%F2M6%H21F+8%4221%=3O61p0?1pSDQ11pT<Q31").
Proof.
intros s j Hj. rewrite u_andi by lia. rewrite at_u by lia.
change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity.
Qed.
Record slenH (mem : word -> option byte) (s : word) (buf : list byte) (K : Z) : Prop := SLENH {
Hbuf : rdn RSEGS mem s (length buf) = Some buf;
Hwin : ((bv_unsigned s + K) / 8 * 8 + 8 <= bv_unsigned s + Z.of_nat (length buf))%Z;
Hnw : (bv_unsigned s + Z.of_nat (length buf) < 2 ^ 64)%Z;
HK0 : (0 <= K)%Z;
Hzero : bv_unsigned (nth (Z.to_nat K) buf (Z_to_bv 8 0)) = 0%Z;
Hnz : forall j, (j < Z.to_nat K)%nat -> bv_unsigned (nth j buf (Z_to_bv 8 0)) <> 0%Z;
Hro : rodata_clear mem }.
Section SLEN.
Variable mem : word -> option byte.
Variable s : word.
Variable buf : list byte.
Variable K : Z.
Variable rom : word -> option byte.
Hypothesis HOK : slenH mem s buf K.
#[local] Abbreviation L := (Z.of_nat (length buf)).
Definition b_ (j : Z) : byte := nth (Z.to_nat j) buf (Z_to_bv 8 0).
Definition sb_ (j : Z) (m : nat) : list byte := sub buf (Z.to_nat j) m.
Let Hbuf := Hbuf _ _ _ _ HOK.
Let Hwin : ((bv_unsigned s + K) / 8 * 8 + 8 <= bv_unsigned s + L)%Z := Hwin _ _ _ _ HOK.
Let Hnw : (bv_unsigned s + L < 2 ^ 64)%Z := Hnw _ _ _ _ HOK.
Let HK0 : (0 <= K)%Z := HK0 _ _ _ _ HOK.
Let Hro := Hro _ _ _ _ HOK.
Lemma KL : ltac2:(TCodec.tc2 tcn__SegStrlen ">&Q@&Q>vD+1%3221&QC&5'R8y8%211vQF%5221%711%=291").
Proof.
clear -Hwin HK0. pose proof (u64_range s).
pose proof (Z.div_mod (bv_unsigned s + K) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (bv_unsigned s + K) 8 ltac:(lia)). lia.
Qed.
Definition KE : Z := ((bv_unsigned s + K) / 8 * 8 + 8 - bv_unsigned s)%Z.
Lemma KE_facts : ltac2:(TCodec.tc2 tcn__SegStrlen "Q2'<&Q@&Q>vD+1%3221&Q1%6221+8%7261%9241%;241&QC&5'R8y8%211vQF%5221%711%C2>1'='C&QB&R9yR0vR5%3221%J21F%621Ez%:3921%Q02<1%Q12F1").
Proof.
unfold KE. clear -Hwin HK0. pose proof (u64_range s).
pose proof (Z.div_mod (bv_unsigned s + K) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (bv_unsigned s + K) 8 ltac:(lia)).
repeat split; try lia.
replace (bv_unsigned s + ((bv_unsigned s + K) / 8 * 8 + 8 - bv_unsigned s))%Z
with (8 + ((bv_unsigned s + K) / 8) * 8)%Z by lia.
rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma bz : ltac2:(TCodec.tc2 tcn__SegStrlen ":'='C&R9y8&Q2vD%211%5241z%93821").
Proof. exact (Hzero _ _ _ _ HOK). Qed.
Lemma bnz : ltac2:(TCodec.tc2 tcn__SegStrlen "F'C'<&Q@zr1%3221&QAvD%2241%8241&?'=&R9y8&Q2r2%211%5241%73B1?%911p0;1pSDE1").
Proof. intros j Hj. unfold b_. apply (Hnz _ _ _ _ HOK). lia. Qed.
Lemma rd_w : ltac2:(TCodec.tc2 tcn__SegStrlen "Q9'C'7&Q@zr2%3221&Q>r3&QC%115%4231&5'R8y8%211vQF%5221%911%@281'='9'6%118%311&L&Q<vQK&GvR5r4%3221%74651H(1&Q3%125K%32=1%A3=51p0C1p0Q11pSFQ61pSDQ81").
Proof.
intros j m Hj Hm. unfold sb_.
replace (at_ s j) with (at_ s (Z.of_nat (Z.to_nat j))) by (f_equal; lia).
apply (rdn_sub RSEGS mem (length buf)); [exact Hbuf | lia].
Qed.
Lemma rd_b : ltac2:(TCodec.tc2 tcn__SegStrlen "Q<'C&Q@zr1%3221&Q>r2+1%3221&QC&5'R8y8%211vQF%5221%711%@291'='9'6%118%311&L&Q<vQK&GvR5r3%3221u1%847621(1(3&Q2%117(8%11H%53I31%72B1%F3B91p0H1p0Q61pSDQ;1").
Proof.
intros j Hj H1. rewrite (rd_w j 1) by lia. unfold sb_, b_.
rewrite sub_nth; [reflexivity | lia].
Qed.
Lemma sb_len : ltac2:(TCodec.tc2 tcn__SegStrlen "M'C'7&Q@zr2%3221&Q>r3&QC%115%4231&5'R8y8%211vQF%5221%911%@281'=&Q3r4%221?%<291%53G1Ap071p0E1pSFJ1pSDL1").
Proof. intros j m Hj Hm. unfold sb_. apply sub_length. lia. Qed.
Lemma sb_nth : ltac2:(TCodec.tc2 tcn__SegStrlen "Q8'C'7&Q@zr2%3221&Au8%2241&Q>r4+8%3221&QC&5'R8y8%211vQF%5221%711%C291'=&B&Q3r5%221C&R7%12<I%64<C31&Q2%B1E%G271%311%<3A51p0>1p0L1p0Q01pSBQ51pSDQ71").
Proof.
intros j i Hj Hi H8. unfold sb_, b_. rewrite nth_sub by lia. f_equal. lia.
Qed.
Lemma m_lbu : forall regs pc w rd rs (imm : bv 12) j0 j,
fetch_word RSEGS pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
getr regs rs = at_ s j0 -> (j0 + bv_signed imm = j)%Z ->
(0 <= j)%Z -> (j + 1 <= L)%Z ->
RiscvSemantics.step RSEGS (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LBv (b_ j))) (v_addi pc 4) mem rom).
Proof.
intros regs pc w rd rs imm j0 j Hf He Hd Hrs Hj Hj0 Hj1.
eapply step_lbu; [exact Hf | exact He | exact Hd |].
rewrite Hrs, at_addi, Hj. apply rd_b; lia.
Qed.
Lemma m_ld : forall regs pc w rd rs (imm : bv 12) j0 j,
fetch_word RSEGS pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ8 true rd rs imm, 4%Z) ->
getr regs rs = at_ s j0 -> (j0 + bv_signed imm = j)%Z ->
(0 <= j)%Z -> (j + 8 <= L)%Z ->
RiscvSemantics.step RSEGS (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LDv (sb_ j 8))) (v_addi pc 4) mem rom).
Proof.
intros regs pc w rd rs imm j0 j Hf He Hd Hrs Hj Hj0 Hj8.
eapply step_ld; [exact Hf | exact He | exact Hd | |].
- rewrite Hrs, at_addi, Hj. apply (rd_w j 8); lia.
- symmetry. apply u_LDv. apply sb_len; lia.
Qed.
Lemma al_room : ltac2:(TCodec.tc2 tcn__SegStrlen "L'C'=&QB&Q>&R9yR0vR5%3221r1%6221+8%9221z%<3=21'<&Q@r2%2251vD%4231%6231r3%C21<&Q1%9221p051p0=1pSDK1").
Proof.
intros j Hal Hj. unfold KE. clear -Hal Hj HK0. pose proof (u64_range s).
pose proof (Z.div_mod (bv_unsigned s + K) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (bv_unsigned s + K) 8 ltac:(lia)).
pose proof (Z.div_mod (bv_unsigned s + j) 8 ltac:(lia)).
assert ((bv_unsigned s + j) / 8 <= (bv_unsigned s + K) / 8)%Z by (apply Z.div_le_mono; lia).
lia.
Qed.
Lemma tw_hit : ltac2:(TCodec.tc2 tcn__SegStrlen "Q@'C'<&Q@zr1%3221vD%5231%7231&QA&Q>r2+8%3221%5281r3%6214&QC&5'R8y8%211vQF%5221%711%G291'='2&I&Q4&Q9&Q3r4u8%3221%511%711&R7yR0&Q8%3221%=251(4%A3@21p0C1p0O1p0Q61pSDQ?1").
Proof.
intros j Hj HKj HL. rewrite TWs_TW.
apply (TW_haszero _ (Z.to_nat (K - j))).
- apply sb_len; lia.
- lia.
- rewrite sb_nth by lia. rewrite <- bz. f_equal. unfold b_. f_equal. lia.
- intros jj Hjj. rewrite sb_nth by lia. apply bnz. lia.
Qed.
Lemma tw_miss : ltac2:(TCodec.tc2 tcn__SegStrlen "Q<'C&Q@zr1%3221&Q>r2+8%3221vD%9221r3%7215&QC&5'R8y8%211vQF%5221%711%D291'='2&I&Q4&Q9&Q3r4u8%3221%511%711&R7yR0&Q8%3221%=251(:%A3@21p0C1p0O1p0Q61pSDQ;1").
Proof.
intros j Hj HKj HL. rewrite TWs_TW. apply TW_nozero.
- apply sb_len; lia.
- intros i Hi. rewrite sb_nth by lia. apply bnz. lia.
Qed.
Ltac mlbu F D jj :=
chain_step; [reflexivity
| eapply m_lbu with (j := jj);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; first [reflexivity | f_equal; lia] | imm_norm; lia | lia | lia]
| step_simpl]; vnorm.
Ltac mld F D jj :=
chain_step; [reflexivity
| eapply m_ld with (j := jj);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; first [reflexivity | f_equal; lia] | imm_norm; lia | lia | lia]
| step_simpl]; vnorm.
Ltac condb :=
rwH; rewrite ?getr_zero; rewrite c_eq_LBv_0;
first [ apply Z.eqb_eq; rewrite <- bz; f_equal; f_equal; lia
| apply Z.eqb_neq; apply bnz; lia ].
Ltac cond := try unfold v_addi; cond_lia.
Ltac condw lem :=
rwH;
lazymatch goal with |- c_eq (v_and (v_or (v_sub _ ?x) _) _) _ = ?b =>
change (c_eq (TWs x) (Z_to_bv 64 Hc) = b) end;
apply lem; lia.
Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try reflexivity; try (rewrite ?at_0; reflexivity);
try (f_equal; lia); try (unfold v_addi; unorm; f_equal; lia); try solve_sl_agree.
Lemma t_loop : ltac2:(TCodec.tc2 tcn__SegStrlen "RJ'7&Ey5'R8yR0%211%5241'C&Hr2%211'=&Jr4(R6+1(;%33?21%6251r3%93?21r5+:%93E17%<231vR5%?3E21r6+<%?3K1=%B231&G%127C%F3L31r7+;%F3Q21D%I231&QE%12BH%92?1%N3Q441'<&Q@z%221BvD%42D1%6231&QCr:%211%>26B%Q:3Q>21'>'F&Q<&KvQGr;+eWQD%Q?3QI1Q=/01QIvQKvR4%8576321r1%:591A43%=3<31%QI23Q>&R7%12R3I%QM3R331&Q6%12?8%Q1231%Q2281qT6R71%H2R81p0J1p0Q01p0Q81p0QA1p0QI1p0R01p0R;1pSDR?1pT8RB1pT4RB1pSBRI1").
Proof.
pose proof KL as HKL. pose proof (u64_range s) as Hs.
induction i as [|i IH]; intros regs ret j Hret H1 H10 H12 H11 Hj Hi.
-
eexists. split.
+ mlbu (ltac:(oF' 0xa9c34%Z)) (ltac:(oD' 0xa9c34%Z)) j.
stepn (ltac:(oF' 0xa9c38%Z)) (ltac:(oD' 0xa9c38%Z)).
stepn (ltac:(oF' 0xa9c3c%Z)) (ltac:(oD' 0xa9c3c%Z)).
stepb_ft (ltac:(oF' 0xa9c40%Z)) (ltac:(oD' 0xa9c40%Z)) ltac:(condb).
stepiv (ltac:(oF' 0xa9c44%Z)) (ltac:(oD' 0xa9c44%Z)) (Z_to_bv 64 K)
ltac:(gres; rwH; rewrite ?at_addi; replace (j - 1 + 1)%Z with K by lia; apply v_sub_at; lia).
stepret (ltac:(oF' 0xa9c48%Z)) (ltac:(oD' 0xa9c48%Z)) ret ltac:(rwH; reflexivity).
apply mst_refl.
+ post.
-
eapply (runs_trans RSEGS _ (fun r => mkst r (0xa9c34 : word) mem rom)
(fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 12 = at_ s (j + 1) /\ getr r 11 = at_ s (j + 1 - 1)
/\ sl_agree regs r)).
+ eexists. split.
* mlbu (ltac:(oF' 0xa9c34%Z)) (ltac:(oD' 0xa9c34%Z)) j.
stepn (ltac:(oF' 0xa9c38%Z)) (ltac:(oD' 0xa9c38%Z)).
stepn (ltac:(oF' 0xa9c3c%Z)) (ltac:(oD' 0xa9c3c%Z)).
stepb_tk (ltac:(oF' 0xa9c40%Z)) (ltac:(oD' 0xa9c40%Z)) ltac:(condb).
apply mst_refl.
* post.
+ cbv beta. intros r1 (R1 & R10 & R12 & R11 & KC).
destruct (IH r1 ret (j + 1)%Z Hret R1 R10 R12 R11 ltac:(lia) ltac:(lia)) as (r2 & RUN & A10 & K2).
exists r2. split; [exact RUN | split; [exact A10 | eapply sl_agree_trans; eassumption]].
Qed.
Lemma w_loop : ltac2:(TCodec.tc2 tcn__SegStrlen "SH'7&Ey5'R8yR0%211%5241'C&Hr2%211'=&Jr4(R6+1(;%33?21%6251r3%93?21r5+:%93E17%<231vR5%?3E21r6+<%?3K1=%B231&G&QE+8%22E1%42:1%I3O61r7+;%I3Q51G%L231+9%:2E1%<2B1%Q13Q741r8+=%Q13Q=1O%Q4231&R7&Q:%22Q?1%Q93Q?41r9+>%Q93QE1Q7%Q<231&Q8%92QF1%Q@3QF31'<&Q@z%221BvD%42D1%6231&QB&Q>&R9%12R2Q=%321B%521Q7%QN3R21;&QCr=%211&Q?r:%Q?2?1%321Q?%R63R:51'>'F&Q<&KvQGr>+eWPH%R;3RE1R9/01REvQKvR4%8576321r1%:591D43%=3<31%RE23R:%QA2RNQ2%RH3RN21&Q6%12>7%Q:231%Q;271qT6S21%G2S31p0I1p0Q21p0Q:1p0QB1p0QJ1p0R31p0R<1p0RG1p0RN1p0S91pSDS=1pT8S@1pT4S@1pSBSG1").
Proof.
pose proof KL as HKL. pose proof KE_facts as (HKE1 & HKE2 & HKE3). pose proof (u64_range s) as Hs.
induction i as [|i IH]; intros regs ret j Hret H1 H10 H12 H11 H13 H14 Hj Hal Hi;
pose proof (al_room j Hal Hj) as HR.
-
assert (HKj : (K < j + 8)%Z).
{ clear -Hi Hj. pose proof (Z.div_mod (K - j) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (K - j) 8 ltac:(lia)). lia. }
eapply (runs_trans RSEGS _ (fun r => mkst r (0xa9c34 : word) mem rom)
(fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 12 = at_ s j /\ getr r 11 = at_ s (j - 1)
/\ sl_agree regs r)).
+ eexists. split.
* mld (ltac:(oF' 0xa9c18%Z)) (ltac:(oD' 0xa9c18%Z)) j.
stepn (ltac:(oF' 0xa9c1c%Z)) (ltac:(oD' 0xa9c1c%Z)).
stepn (ltac:(oF' 0xa9c20%Z)) (ltac:(oD' 0xa9c20%Z)).
stepn (ltac:(oF' 0xa9c24%Z)) (ltac:(oD' 0xa9c24%Z)).
stepn (ltac:(oF' 0xa9c28%Z)) (ltac:(oD' 0xa9c28%Z)).
stepn (ltac:(oF' 0xa9c2c%Z)) (ltac:(oD' 0xa9c2c%Z)).
stepb_ft (ltac:(oF' 0xa9c30%Z)) (ltac:(oD' 0xa9c30%Z)) ltac:(condw tw_hit).
apply mst_refl.
* post.
+ cbv beta. intros r1 (R1 & R10 & R12 & R11 & KC).
destruct (t_loop (Z.to_nat (K - j)) r1 ret j Hret R1 R10 R12 R11 ltac:(lia) ltac:(lia)) as (r2 & RUN & A10 & K2).
exists r2. split; [exact RUN | split; [exact A10 | eapply sl_agree_trans; eassumption]].
-
assert (HKj : (j + 8 <= K)%Z).
{ clear -Hi Hj. pose proof (Z.div_mod (K - j) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (K - j) 8 ltac:(lia)). lia. }
eapply (runs_trans RSEGS _ (fun r => mkst r (0xa9c18 : word) mem rom)
(fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 12 = at_ s (j + 8 - 8) /\ getr r 11 = at_ s (j + 8 - 9)
/\ getr r 13 = Z_to_bv 64 Mc /\ getr r 14 = Z_to_bv 64 Hc /\ sl_agree regs r)).
+ eexists. split.
* mld (ltac:(oF' 0xa9c18%Z)) (ltac:(oD' 0xa9c18%Z)) j.
stepn (ltac:(oF' 0xa9c1c%Z)) (ltac:(oD' 0xa9c1c%Z)).
stepn (ltac:(oF' 0xa9c20%Z)) (ltac:(oD' 0xa9c20%Z)).
stepn (ltac:(oF' 0xa9c24%Z)) (ltac:(oD' 0xa9c24%Z)).
stepn (ltac:(oF' 0xa9c28%Z)) (ltac:(oD' 0xa9c28%Z)).
stepn (ltac:(oF' 0xa9c2c%Z)) (ltac:(oD' 0xa9c2c%Z)).
stepb_tk (ltac:(oF' 0xa9c30%Z)) (ltac:(oD' 0xa9c30%Z)) ltac:(condw tw_miss).
apply mst_refl.
* post.
+ cbv beta. intros r1 (R1 & R10 & R12 & R11 & R13 & R14 & KC).
destruct (IH r1 ret (j + 8)%Z Hret R1 R10 R12 R11 R13 R14 ltac:(lia)
ltac:(rewrite Z.add_assoc, <- Zplus_mod_idemp_l, Hal; reflexivity)
ltac:(clear -Hi HKj; pose proof (Z.div_mod (K - j) 8 ltac:(lia));
pose proof (Z.mod_pos_bound (K - j) 8 ltac:(lia));
pose proof (Z.div_mod (K - (j + 8)) 8 ltac:(lia));
pose proof (Z.mod_pos_bound (K - (j + 8)) 8 ltac:(lia)); nia))
as (r2 & RUN & A10 & K2).
exists r2. split; [exact RUN | split; [exact A10 | eapply sl_agree_trans; eassumption]].
Qed.
Ltac ldc F D vv RD :=
chain_step; [reflexivity
| eapply step_ld with (v := vv);
[exact F | reflexivity | exact D
| gres; imm_norm;
lazymatch goal with |- rdn _ _ ?a _ = _ =>
lazymatch type of RD with rdn _ _ ?c _ = _ =>
replace a with c by (apply bv_eq; vm_compute; reflexivity) end end;
exact RD
| assumption ]
| step_simpl]; vnorm.
Lemma a_entry : ltac2:(TCodec.tc2 tcn__SegStrlen "RC&Ey5'R8yR0%211%5241'C&Hr2%211'=&Jr4(R6+1(;%33?21%6251r3%93?21r5+:%93E17%<231vR5%?3E21r6+<%?3K1=%B231&G%127C%F3L31'<&Q@z%221@vD%42B1%6231&QB&Q>&R9%12Q8C%321B+8%6221%Q53Q91<'>'F&Q<&KvQGr:+eWP0%Q:3QD1Q8/01QDvQKvR4%8576321r1r9%;5:2154%>3=41%QE24Q:&R7%12QOM%QI3QO31&Q6%12@9%Q5231%Q6281qT6R31%I2R41p0K1p0Q41p0Q<1p0QD1p0QK1p0R61pSDR:1pT8R=1pT4R=1").
Proof.
intros regs ret j Hret H1 H10 H12 Hj Hal.
pose proof KL as HKL. pose proof (u64_range s) as Hs.
destruct (rd_const_M mem Hro) as (bsM & RM & EM).
destruct (rd_const_H mem Hro) as (bsH & RH & EH).
eapply (runs_trans RSEGS _ (fun r => mkst r (0xa9c18 : word) mem rom)
(fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 12 = at_ s (j - 8) /\ getr r 11 = at_ s (j - 9)
/\ getr r 13 = Z_to_bv 64 Mc /\ getr r 14 = Z_to_bv 64 Hc /\ sl_agree regs r)).
- eexists. split.
+ stepn (ltac:(oF' 0xa9c00%Z)) (ltac:(oD' 0xa9c00%Z)).
stepn (ltac:(oF' 0xa9c04%Z)) (ltac:(oD' 0xa9c04%Z)).
ldc (ltac:(oF' 0xa9c08%Z)) (ltac:(oD' 0xa9c08%Z)) (Z_to_bv 64 Mc) RM.
ldc (ltac:(oF' 0xa9c0c%Z)) (ltac:(oD' 0xa9c0c%Z)) (Z_to_bv 64 Hc) RH.
stepn (ltac:(oF' 0xa9c10%Z)) (ltac:(oD' 0xa9c10%Z)).
stepn (ltac:(oF' 0xa9c14%Z)) (ltac:(oD' 0xa9c14%Z)).
apply mst_refl.
+ post.
- cbv beta. intros r1 (R1 & R10 & R12 & R11 & R13 & R14 & KC).
destruct (w_loop (Z.to_nat ((K - j) / 8)) r1 ret j Hret R1 R10 R12 R11 R13 R14 Hj Hal
ltac:(clear -Hj; pose proof (Z.div_pos (K - j) 8); lia)) as (r2 & RUN & A10 & K2).
exists r2. split; [exact RUN | split; [exact A10 | eapply sl_agree_trans; eassumption]].
Qed.
Lemma h_loop : ltac2:(TCodec.tc2 tcn__SegStrlen "S;'7&Ey5'R8yR0%211%5241'C&Hr2%211'=&Jr4(R6+1(;%33?21%6251r3%93?21r5+:%93E17%<231vR5%?3E21r6+;%?3K1=%B231&G%127C%F3L31r7+<%F3Q21D%I231&Q>%12BH%92?1%N3Q441'<&Q@z%221B&QAvD%22E1%7241'@&?&QB&R9%12QBM%A21E%B21Q9+8%6221%Q@3QD1?%911&QCr:%211%J216%QF3QJ18%H261(0%QI3R461%K21:%D241'>'F&Q<&KvQGr;+eVo0%R03R:1QN/01R:vQKvR4%8576321r1%:591F43%=3<31%R:23QO&R7%12RDQ9%R>3RD31&Q6%12?8%QB231%QC281qT6RH1%H2RI1p0J1p0Q@1p0QI1p0R21p0R:1p0RA1p0RL1pSDS01pT8S31pT4S31pSBS:1").
Proof.
pose proof KL as HKL. pose proof (u64_range s) as Hs.
induction i as [|i IH]; intros regs ret j Hret H1 H10 H11 H12 Hj Hi;
pose proof (Z.mod_pos_bound (bv_unsigned s + j + 1) 8 ltac:(lia)) as HM1.
-
assert (Hal : ((bv_unsigned s + j + 1) mod 8 = 0)%Z) by (clear -Hi HM1; lia).
eapply (runs_trans RSEGS _ (fun r => mkst r (0xa9c00 : word) mem rom)
(fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 12 = at_ s (j + 1) /\ sl_agree regs r)).
+ eexists. split.
* stepn (ltac:(oF' 0xa9be0%Z)) (ltac:(oD' 0xa9be0%Z)).
stepn (ltac:(oF' 0xa9be4%Z)) (ltac:(oD' 0xa9be4%Z)).
stepb_tk (ltac:(oF' 0xa9be8%Z)) (ltac:(oD' 0xa9be8%Z))
ltac:(rwH; rewrite ?at_addi; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_eq;
rewrite Z.add_assoc; exact Hal).
apply mst_refl.
* post.
+ cbv beta. intros r1 (R1 & R10 & R12 & KC).
destruct (a_entry r1 ret (j + 1)%Z Hret R1 R10 R12 ltac:(lia) ltac:(rewrite Z.add_assoc; exact Hal))
as (r2 & RUN & A10 & K2).
exists r2. split; [exact RUN | split; [exact A10 | eapply sl_agree_trans; eassumption]].
-
assert (Hna : ((bv_unsigned s + j + 1) mod 8 = 7 - Z.of_nat i)%Z /\ ((bv_unsigned s + j + 1) mod 8 <> 0)%Z) by (clear -Hi; lia).
destruct Hna as [Hna Hnz0].
destruct (Z.eq_dec (j + 1) K) as [HjK|HjK].
+
eexists. split.
* stepn (ltac:(oF' 0xa9be0%Z)) (ltac:(oD' 0xa9be0%Z)).
stepn (ltac:(oF' 0xa9be4%Z)) (ltac:(oD' 0xa9be4%Z)).
stepb_ft (ltac:(oF' 0xa9be8%Z)) (ltac:(oD' 0xa9be8%Z))
ltac:(rwH; rewrite ?at_addi; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_neq;
rewrite Z.add_assoc; lia).
mlbu (ltac:(oF' 0xa9bec%Z)) (ltac:(oD' 0xa9bec%Z)) (j + 1)%Z.
stepn (ltac:(oF' 0xa9bf0%Z)) (ltac:(oD' 0xa9bf0%Z)).
stepn (ltac:(oF' 0xa9bf4%Z)) (ltac:(oD' 0xa9bf4%Z)).
stepb_ft (ltac:(oF' 0xa9bf8%Z)) (ltac:(oD' 0xa9bf8%Z)) ltac:(condb).
stepn (ltac:(oF' 0xa9bfc%Z)) (ltac:(oD' 0xa9bfc%Z)).
stepiv (ltac:(oF' 0xa9c44%Z)) (ltac:(oD' 0xa9c44%Z)) (Z_to_bv 64 K)
ltac:(gres; rwH; rewrite ?at_addi; rewrite HjK; apply v_sub_at; lia).
stepret (ltac:(oF' 0xa9c48%Z)) (ltac:(oD' 0xa9c48%Z)) ret ltac:(rwH; reflexivity).
apply mst_refl.
* post.
+
eapply (runs_trans RSEGS _ (fun r => mkst r (0xa9be0 : word) mem rom)
(fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 11 = at_ s (j + 1) /\ getr r 12 = at_ s (j + 1 + 1)
/\ sl_agree regs r)).
* eexists. split.
-- stepn (ltac:(oF' 0xa9be0%Z)) (ltac:(oD' 0xa9be0%Z)).
stepn (ltac:(oF' 0xa9be4%Z)) (ltac:(oD' 0xa9be4%Z)).
stepb_ft (ltac:(oF' 0xa9be8%Z)) (ltac:(oD' 0xa9be8%Z))
ltac:(rwH; rewrite ?at_addi; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_neq;
rewrite Z.add_assoc; lia).
mlbu (ltac:(oF' 0xa9bec%Z)) (ltac:(oD' 0xa9bec%Z)) (j + 1)%Z.
stepn (ltac:(oF' 0xa9bf0%Z)) (ltac:(oD' 0xa9bf0%Z)).
stepn (ltac:(oF' 0xa9bf4%Z)) (ltac:(oD' 0xa9bf4%Z)).
stepb_tk (ltac:(oF' 0xa9bf8%Z)) (ltac:(oD' 0xa9bf8%Z)) ltac:(condb).
apply mst_refl.
-- post.
* cbv beta. intros r1 (R1 & R10 & R11 & R12 & KC).
assert (HM : ((bv_unsigned s + (j + 1) + 1) mod 8 = ((bv_unsigned s + j + 1) mod 8 + 1) mod 8)%Z).
{ clear -Hs Hj. replace (bv_unsigned s + (j + 1) + 1)%Z with (bv_unsigned s + j + 1 + 1)%Z by lia.
rewrite <- (Zplus_mod_idemp_l (bv_unsigned s + j + 1)). reflexivity. }
destruct (IH r1 ret (j + 1)%Z Hret R1 R10 R11 R12 ltac:(lia)) as (r2 & RUN & A10 & K2).
{ rewrite HM, Hna. clear -Hna Hnz0 HM1. destruct i as [|i].
- right. split; [reflexivity|]. reflexivity.
- left. rewrite Z.mod_small by lia. lia. }
exists r2. split; [exact RUN | split; [exact A10 | eapply sl_agree_trans; eassumption]].
Qed.
Lemma strlen_run : ltac2:(TCodec.tc2 tcn__SegStrlen "QI&Ey5'R8yR0%211%5241&Hr1%211'=&Jr3(R6+1(;%33>21%6251r2%93>21r4+:%93D17%<231vR5%?3D21'>'<'F&Q<&KvQGr6+eVn4%E3N1C/01NvQKvR4%8576321r5%:59Q0143%=3<31%O2Q2D&R7vD%22Q91%Q43Q941&Q6%12@Q8%F231%G291qT6Q=1%J2Q>1p0L1p0Q31p0Q>1pT8QC1pT4QC1").
Proof.
intros regs ret Hret H1 H10.
pose proof KL as HKL. pose proof (u64_range s) as Hs.
pose proof (Z.mod_pos_bound (bv_unsigned s) 8 ltac:(lia)) as HM.
assert (E0 : exists j0 : Z, j0 = 0%Z) by (exists 0%Z; reflexivity). destruct E0 as [j0 Hj0].
rewrite <- (at_0 s), <- Hj0 in H10.
destruct (Z.eq_dec (bv_unsigned s mod 8) 0) as [Hal|Hal].
-
eapply (runs_trans RSEGS _ (fun r => mkst r (0xa9c00 : word) mem rom)
(fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 12 = at_ s 0 /\ sl_agree regs r)).
+ eexists. split.
* stepn (ltac:(oF' 0xa9bc4%Z)) (ltac:(oD' 0xa9bc4%Z)).
stepn (ltac:(oF' 0xa9bc8%Z)) (ltac:(oD' 0xa9bc8%Z)).
stepb_tk (ltac:(oF' 0xa9bcc%Z)) (ltac:(oD' 0xa9bcc%Z))
ltac:(rwH; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_eq;
rewrite Hj0, Z.add_0_r; exact Hal).
apply mst_refl.
* post; rewrite ?Hj0, ?at_0; reflexivity.
+ cbv beta. intros r1 (R1 & R10 & R12 & KC).
destruct (a_entry r1 ret 0 Hret R1 R10 R12 ltac:(lia) ltac:(rewrite Z.add_0_r; exact Hal))
as (r2 & RUN & A10 & K2).
exists r2. split; [exact RUN | split; [exact A10 | eapply sl_agree_trans; eassumption]].
- destruct (Z.eq_dec K 0) as [HK|HK].
+
eexists. split.
* stepn (ltac:(oF' 0xa9bc4%Z)) (ltac:(oD' 0xa9bc4%Z)).
stepn (ltac:(oF' 0xa9bc8%Z)) (ltac:(oD' 0xa9bc8%Z)).
stepb_ft (ltac:(oF' 0xa9bcc%Z)) (ltac:(oD' 0xa9bcc%Z))
ltac:(rwH; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_neq;
rewrite Hj0, Z.add_0_r; exact Hal).
mlbu (ltac:(oF' 0xa9bd0%Z)) (ltac:(oD' 0xa9bd0%Z)) j0.
stepb_tk (ltac:(oF' 0xa9bd4%Z)) (ltac:(oD' 0xa9bd4%Z)) ltac:(condb).
stepiv (ltac:(oF' 0xa9c4c%Z)) (ltac:(oD' 0xa9c4c%Z)) (Z_to_bv 64 K)
ltac:(gres; rwH; rewrite HK; apply v_sub_self).
stepret (ltac:(oF' 0xa9c50%Z)) (ltac:(oD' 0xa9c50%Z)) ret ltac:(rwH; reflexivity).
apply mst_refl.
* post; rewrite ?Hj0, ?at_0; reflexivity.
+
eapply (runs_trans RSEGS _ (fun r => mkst r (0xa9be0 : word) mem rom)
(fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 11 = at_ s 0 /\ getr r 12 = at_ s (0 + 1)
/\ sl_agree regs r)).
* eexists. split.
-- stepn (ltac:(oF' 0xa9bc4%Z)) (ltac:(oD' 0xa9bc4%Z)).
stepn (ltac:(oF' 0xa9bc8%Z)) (ltac:(oD' 0xa9bc8%Z)).
stepb_ft (ltac:(oF' 0xa9bcc%Z)) (ltac:(oD' 0xa9bcc%Z))
ltac:(rwH; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_neq;
rewrite Hj0, Z.add_0_r; exact Hal).
mlbu (ltac:(oF' 0xa9bd0%Z)) (ltac:(oD' 0xa9bd0%Z)) j0.
stepb_ft (ltac:(oF' 0xa9bd4%Z)) (ltac:(oD' 0xa9bd4%Z)) ltac:(condb).
stepn (ltac:(oF' 0xa9bd8%Z)) (ltac:(oD' 0xa9bd8%Z)).
stepn (ltac:(oF' 0xa9bdc%Z)) (ltac:(oD' 0xa9bdc%Z)).
apply mst_refl.
-- post; rewrite ?Hj0, ?at_0; reflexivity.
* cbv beta. intros r1 (R1 & R10 & R11 & R12 & KC).
pose proof (Z.mod_pos_bound (bv_unsigned s + 1) 8 ltac:(lia)) as HM1.
destruct (h_loop (Z.to_nat ((8 - (bv_unsigned s + 1) mod 8) mod 8)) r1 ret 0 Hret R1 R10 R11 R12 ltac:(lia))
as (r2 & RUN & A10 & K2).
{ rewrite Z.add_0_r.
destruct (Z.eq_dec ((bv_unsigned s + 1) mod 8) 0) as [Hz|Hz].
- right. rewrite Hz. split; [reflexivity | reflexivity].
- left. split; [exact Hz|]. rewrite Z2Nat.id by (apply Z.mod_pos_bound; lia). rewrite Z.mod_small by lia. lia. }
exists r2. split; [exact RUN | split; [exact A10 | eapply sl_agree_trans; eassumption]].
Qed.
End SLEN.
Theorem ref_strlen : ltac2:(TCodec.tc2 tcn__SegStrlen "R9'R8yR0%211'9y8%511%311p051'6%114'C&Ey5%221;'Q5r7r6r5r4%544321&Hr2%211'=&J(R6+1(;%33@21%52;1r3%83M21+:%83E16%:2A1r9%=3Q221'>'<'F&Q<&KvQG+eVn4%C3Q;1A/01Q;r<r8%756Q1321r1%9581Q243%<3;31&Q6%12Q64%N25E&R7%12QGE%Q23QG31%D251%E281qT6Q?1%H2Q@1p0J1p0Q01p0Q:1p0Q>1pT8R01pT4QF1pT:QM1pQ:QK1pS>QM1pT<R51pSHR11").
Proof.
intros mem s buf K rom regs ret HOK Hret H1 H10.
destruct (strlen_run mem s buf K rom HOK regs ret Hret H1 H10) as (r & RUN & A10 & KC).
exists r. split; [exact RUN | split; [exact KC | exact A10]].
Qed.
End FPX_1.
