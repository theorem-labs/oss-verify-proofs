(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib MemSplit MemsetLib As0StepLib Jb0MemIsZero Jb0RegionPoisoned.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import Jb0SumsMemset_code Jb0SumsMemset.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Jb0AsanMemset () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.DecodeC."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0AsanMemset."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0AsanMemset.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0AsanMemset.FPX_1.AMS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0RegionPoisoned."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.MemsetLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1cons"; "1false"; "1list"; "1nat"; "1negb"; "1nil"; "1option"; "1orb"; "1pair"; "1prod"; "1true"; "2I"; "2and"; "2eq"]; ["2ex"; "2not"; "3repeat"; "4Z"; "0L"; "5bytes_le_to_Z"; "6Segment"; "7MachineOk"; "7fetch_word"; "7is_ecall"; "7machine_result"; "7machine_state"; "7step"; "7store_ok"; "7word_to_le_bytes"; "8decode_any"]; ["9ALU_AND"; "9ALU_OR"; "9ALU_SLT"; "9ALU_SLTU"; "9Op"; "9instr"; ":bv_eqb"; ":bvmap"; "0M"; "0M'"; "0M1"; "0M2"; "0Mj"; ";wbytes"; "<msteps"; "=ret_ok"]; ["@FR"; "@M8"; "@c1_post"; "@c2_post"; "@c2qa_post"; "@out_agree"; "@ql_inv"; "@ql_post"; "@slots_ok"; "?RIPL"; "?ms_icpt_globs"; ">memb"; "AHIGHEND"; "ASB"; "Aframe_only"; "Akeeps_but"]; ["Art_layout_globs"; "Bcbyte"; "Bms_agree"; "Cgetr"; "Cmkst"; "Crdn"; "Cregupd"; "Cv_addi"; "Cv_and"; "Cv_or"; "Cv_slt"; "Cv_sltu"; "Dcallee_saved"; "Dkeeps_cs"; "Emem_grows"; "Floaded_segments"]; ["GIn"; "Hadd"; "Hdiv"; "Hland"; "Hle"; "Hlor"; "Hlt"; "Hlxor"; "Hmodulo"; "Hof_nat"; "Hpow"; "Hsub"; "Hto_nat"; "0a"; "0b"; "0bs"]; ["0cv"; "0f"; "0fa"; "0fx"; "0i"; "0j"; "0k"; "0kL"; "0l"; "0la"; "0mem"; "0mem0"; "0n"; "0p"; "0pc"; "0q"]; ["0r"; "0r1"; "0r2"; "0ra"; "0rd"; "0regs"; "0regs'"; "0regs0"; "0rg"; "0rom"; "0rs1"; "0rs2"; "0s"; "0segs"; "0sp"; "IBV"]; ["IZ_to_bv"; "Ibv"; "Ibv_unsigned"; "0u0"; "0u1"; "0v"; "0w"; "0w0"; "0w1"; "0x"; "0z"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := L5FastLia.plia.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
Lemma lxor_ones64 : ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "H'C'>&RDzr1%3221&RF&RJ+2+R0%3221%5271%;271'?&RGr2&RK+1%2281%5241%4225%83E21p0:1pULG1").
Proof.
intros a Ha.
replace (2 ^ 64 - 1 - a)%Z with ((Z.lnot a) mod 2 ^ 64)%Z.
2:{ unfold Z.lnot. replace (Z.pred (- a)) with ((2 ^ 64 - 1 - a) + (-1) * 2 ^ 64)%Z by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
apply Z.bits_inj'. intros i Hi.
rewrite Z.lxor_spec.
destruct (Z.lt_ge_cases i 64) as [Hlt|Hge].
- rewrite Z.mod_pow2_bits_low by lia. rewrite Z.lnot_spec by lia.
replace (2 ^ 64 - 1)%Z with (Z.ones 64) by reflexivity. rewrite Z.ones_spec_low by lia.
apply Bool.xorb_true_r.
- rewrite Z.mod_pow2_bits_high by lia.
replace (2 ^ 64 - 1)%Z with (Z.ones 64) by reflexivity. rewrite Z.ones_spec_high by lia.
rewrite (Z.bits_above_log2 a i); [reflexivity| lia |].
assert (Z.log2 a < 64)%Z; [|lia].
destruct (Z.eq_dec a 0) as [->|Hnz]; [cbn; lia|].
apply Z.log2_lt_pow2; lia.
Qed.
Lemma land255_small : ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "B'C'>&RDzr1%3221&RF+X0%2241%8241'?&RCr2+WO%3221%53?13p071pULA1").
Proof. intros a Ha. change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma lor_bound64 : ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "H'C'>&RDzr2%3221&RF&RJ+2+R0%3221%5271%;271&REr4r3%3221%?2>1%<228%B221p081p091pUNF1pULG1").
Proof.
intros a b Ha Hb. split; [apply Z.lor_nonneg; lia|].
destruct (Z.eq_dec a 0) as [->|Ha0]; [rewrite Z.lor_0_l; lia|].
destruct (Z.eq_dec b 0) as [->|Hb0]; [rewrite Z.lor_0_r; lia|].
assert (Hl : (Z.log2 (Z.lor a b) < 64)%Z).
{ rewrite Z.log2_lor by lia. apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia. }
assert (Hnn : (0 <= Z.lor a b)%Z) by (apply Z.lor_nonneg; lia).
destruct (Z.eq_dec (Z.lor a b) 0) as [E|NE]; [lia|].
apply Z.log2_lt_pow2; lia.
Qed.
Lemma zbv_wrap_up : ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "A'C'?'T1yR0%211&T0r1%2241&RA&RJ+2+R0%3221%5271%92;1%>3;81pXF@1").
Proof.
intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
replace (z + 2 ^ 64)%Z with (z + 1 * 2 ^ 64)%Z by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma bytes8_range : ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "Q:'4'F%211'T1yR0%211'8y8%511%311p051%;13'?%712&R5r4r3r2u8%544321(0r1%22;1%;3:41'>&RDz&E%11;%4231&RF&RJ+2+R0%3221%5271%<271p0>1pV0K1pULQ21pRBN1pWLQ71").
Proof.
intros segs M a bs H. pose proof (rdn_length _ _ _ _ _ H) as L. pose proof (bytes_le_to_Z_bound bs) as B.
pose proof (bytes_le_to_Z_nonneg bs). rewrite L in B. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in B. lia.
Qed.
Definition memb (r : reg) (L : list reg) : bool := existsb (fun x => bv_eqb x r) L.
Lemma memb_true : ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "C'T1y5%211'4%112'?'1&QKr2r1%3221(<%73621&R@r3%23=17p041pQ:=1pW2@1").
Proof.
intros r L H. unfold memb in H. apply existsb_exists in H. destruct H as (x & Hx & E).
unfold bv_eqb in E. apply Z.eqb_eq in E. apply bv_eq in E. subst x. exact Hx.
Qed.
Lemma memb_false : ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "E'T1y5%211'4%112'?'1&QKr2r1%3221(3%73621&A&R@r3%23>18%411p061pQ:?1pW2B1").
Proof.
intros r L H Hin. unfold memb in H.
assert (T : existsb (fun x => bv_eqb x r) L = true) by (apply existsb_exists; exists r; split; [exact Hin | unfold bv_eqb; apply Z.eqb_refl]).
rewrite T in H. discriminate.
Qed.
Lemma keeps_but_updb : ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "Q6'4'T1y5%211%411&Q7yR0%611%3261&QOr5r4r3%43321'?'1&9&QKr6%2271&6&R<%52:1%311%8251(<%<3;21r7&R6%13CBA%E33<1p051p0C1pX<J1pW:O1pW>K1pW<L1pQ:Q11").
Proof.
intros L regs regs' rd v K Hb. apply keeps_but_upd; [exact K|].
destruct (memb rd L) eqn:E1; [left; apply memb_true; exact E1|].
destruct (memb rd callee_saved) eqn:E2; [cbn in Hb; discriminate|]. right. apply memb_false. exact E2.
Qed.
Ltac solve_keeps_but :=
repeat (apply keeps_but_updb; [| reflexivity ]);
first [apply keeps_but_refl | assumption | apply keeps_but_cs; assumption].
Section FPX_0. Context {fx : PropExec.FPState}.
#[using="Type"] Lemma step_or_at : ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "S4'4'F%211&Q7y5'T1yR0%211%5241'8y8%611%311p061yQ0%:11%;1<'?%913&Hr:r8%3221(0r5%22:1%93841'1&Ir6%211(3%?3521';'Q5'C%3221%L11&Or7%211(:(Q4(Q1r4%342@E1+4%64=<21%I2<1%Q03<91&Q6(SOz(=%33QB21%53QC@1%Q73M1I&R9&R3r=%221E%322Q0%5221%Q>3QH1Q7'J'K%211&Lr?&R4vS3r>r<r;%5543?21%8271(G&R6r9%2381QB&R7%12FQ3%=5<31:9%72B1%R33B91p0F1p0N1p0Q61p0QH1p0QO1pX<RC1pWHR;1pWFR<1pW:R=1pX>R?1pWDRB1pVFRC1pVNRJ1pW<RJ1pWLS11").
Proof. intros * Hf He Hd Hrd Hv. rewrite (step_or segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity. Qed.
#[using="Type"] Lemma step_and_at : ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "S4'4'F%211&Q7y5'T1yR0%211%5241'8y8%611%311p061yQ0%:11%;1<'?%913&Hr:r8%3221(0r5%22:1%93841'1&Ir6%211(3%?3521';'Q5'C%3221%L11&Or7%211(:(Q4(Q0r4%342@E1+4%64=<21%I2<1%Q03<91&Q6(SOz(=%33QB21%53QC@1%Q73M1I&R8&R3r=%221E%322Q0%5221%Q>3QH1Q7'J'K%211&Lr?&R4vS3r>r<r;%5543?21%8271(G&R6r9%2381QB&R7%12FQ3%=5<31:9%72B1%R33B91p0F1p0N1p0Q61p0QH1p0QO1pX<RC1pWHR;1pWFR<1pW:R=1pX>R?1pWDRB1pVFRC1pVNRJ1pW<RJ1pWLS11").
Proof. intros * Hf He Hd Hrd Hv. rewrite (step_and segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity. Qed.
#[using="Type"] Lemma step_slt_at : ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "S4'4'F%211&Q7y5'T1yR0%211%5241'8y8%611%311p061yQ0%:11%;1<'?%913&Hr:r8%3221(0r5%22:1%93841'1&Ir6%211(3%?3521';'Q5'C%3221%L11&Or7%211(:(Q4(Q2r4%342@E1+4%64=<21%I2<1%Q03<91&Q6(SOz(=%33QB21%53QC@1%Q73M1I&R:&R3r=%221E%322Q0%5221%Q>3QH1Q7'J'K%211&Lr?&R4vS3r>r<r;%5543?21%8271(G&R6r9%2381QB&R7%12FQ3%=5<31:9%72B1%R33B91p0F1p0N1p0Q61p0QH1p0QO1pX<RC1pWHR;1pWFR<1pW:R=1pX>R?1pWDRB1pVFRC1pVNRJ1pW<RJ1pWLS11").
Proof. intros * Hf He Hd Hrd Hv. rewrite (step_slt segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity. Qed.
#[using="Type"] Lemma step_sltu_at : ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "S4'4'F%211&Q7y5'T1yR0%211%5241'8y8%611%311p061yQ0%:11%;1<'?%913&Hr:r8%3221(0r5%22:1%93841'1&Ir6%211(3%?3521';'Q5'C%3221%L11&Or7%211(:(Q4(Q3r4%342@E1+4%64=<21%I2<1%Q03<91&Q6(SOz(=%33QB21%53QC@1%Q73M1I&R;&R3r=%221E%322Q0%5221%Q>3QH1Q7'J'K%211&Lr?&R4vS3r>r<r;%5543?21%8271(G&R6r9%2381QB&R7%12FQ3%=5<31:9%72B1%R33B91p0F1p0N1p0Q61p0QH1p0QO1pX<RC1pWHR;1pWFR<1pW:R=1pX>R?1pWDRB1pVFRC1pVNRJ1pW<RJ1pWLS11").
Proof. intros * Hf He Hd Hrd Hv. rewrite (step_sltu segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity. Qed.
End FPX_0.
Ltac stepov F D vv tac :=
chain_step;
[ reflexivity
| lazymatch type of D with
| decode_any _ = Some (Op ALU_OR _ _ _, _) => eapply step_or_at with (v := vv)
| decode_any _ = Some (Op ALU_AND _ _ _, _) => eapply step_and_at with (v := vv)
| decode_any _ = Some (Op ALU_SLT _ _ _, _) => eapply step_slt_at with (v := vv)
| decode_any _ = Some (Op ALU_SLTU _ _ _, _) => eapply step_sltu_at with (v := vv)
end;
[ exact F | reflexivity | exact D | reflexivity | tac ]
| step_simpl ].
Section FPX_1. Context {fx : PropExec.FPState}.
Definition ms_icpt_globs (M : word -> option byte) : Prop :=
rdn ASEGS M (0x134f08 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13d719)) /\
rdn ASEGS M (0x13d719 : word) 1%nat = Some [Z_to_bv 8 1] /\
rdn ASEGS M (0x1363b0 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x126be8)).
#[local] Ltac rwH :=
repeat match goal with
| H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
end.
#[local] Ltac unorm :=
repeat match goal with
| |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
end.
#[local] Ltac cond :=
rwH; unfold at_, v_addi, v_add, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
#[local] Ltac wval :=
gres; rwH; unfold at_, v_addi, v_add, v_sub, v_srli; imm_norm; unorm; rewrite ?Z.shiftr_div_pow2 by lia;
try change (2 ^ 3)%Z with 8%Z; first [reflexivity | f_equal; lia].
#[local] Definition RIPL : list reg := [1; 2; 8; 9; 18; 19; 20; 21]%bv.
Section AMS.
Variable mem0 : word -> option byte.
Variable rom : word -> option byte.
Variables sp ra cv : word.
Variables p n s kL f l fa la : Z.
Hypothesis Hs_def : bv_unsigned sp = s.
Hypothesis Hf_def : f = (SB + p / 8)%Z.
Hypothesis Hl_def : l = (SB + (p + n - 1) / 8)%Z.
Hypothesis Hfa_def : fa = (f - f mod 8)%Z.
Hypothesis Hla_def : la = (l - l mod 8)%Z.
Hypothesis Hn : (0 <= n <= 2 ^ 40)%Z.
Hypothesis Happ : (0 <= p /\ p + n + 8 <= LOWEND)%Z \/ (HIGHBEG <= p /\ p + n + 8 <= HIGHEND)%Z.
Hypothesis Hs : (0x1000000 <= s - 2200)%Z /\ (s < 2 ^ 64)%Z.
Hypothesis Hshs : (l + 8 <= s - 2200)%Z.
Hypothesis Hdisj : (0 < n -> p + n <= s - 2200 \/ s <= p)%Z.
Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (s - 2200)) 2200%nat = true.
Hypothesis Hdst : store_ok ASEGS mem0 (Z_to_bv 64 p) (Z.to_nat n) = true.
Hypothesis Hret : ret_ok ra.
Hypothesis HG : rt_layout_globs mem0.
Hypothesis HI : ms_icpt_globs mem0.
Hypothesis HZ : (0 < n)%Z -> forall x : word, (f <= bv_unsigned x < l)%Z -> mem0 x = Some (Z_to_bv 8 0).
Hypothesis HL : (0 < n)%Z -> mem0 (Z_to_bv 64 l) = Some (Z_to_bv 8 kL).
Hypothesis HkL : kL = 0%Z \/ ((p + n - 1) mod 8 < kL <= 7)%Z.
Hypothesis HW : (0 < n <= 64)%Z -> exists w0 w1, rdn ASEGS mem0 (Z_to_bv 64 fa) 8%nat = Some w0 /\ rdn ASEGS mem0 (Z_to_bv 64 la) 8%nat = Some w1.
#[using="Hs_def"] Lemma sp_s : ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "9'?'T1yR0%211vSN&T0vSL%2251%83541"). Proof. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.
#[using="f l Hn Happ"] Lemma p_facts : ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "N'>&RDzvS=%3221&RAvS<%2241+8%4221&QL%:221&RB%12:5%=2<1%>225%@221&RF%12@<&RK+1%22>1%:21>%F2:1%G22>%I221p081%K2;1%L2A1%M2I1").
Proof.
unfold LOWEND, HIGHBEG, HIGHEND in *. destruct Happ as [[H1 H2]|[H1 H2]];
(repeat split; [lia | lia | apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia | intros; apply Z.div_le_mono; lia | intros; apply Z.div_le_upper_bound; lia]).
Qed.
Definition out_agree (M : word -> option byte) : Prop :=
forall x : word, (bv_unsigned x < s - 2200 \/ s <= bv_unsigned x)%Z -> M x = mem0 x.
#[using="Type"] Lemma out_agree_refl : ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "3&QEvS;%211"). Proof. intros x _. reflexivity. Qed.
#[using="p n f l Hn Hs"] Lemma out_agree_w : ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "Q5'T1yR0%211'8y8%511%311p051'C&QEr3%211'>&RD+8%2215+RTH%4271%6231&Q=r5&T0&RKvSLr4%3221%52I1&Nu8%221C%;3:41%F11p0>1p0F1pX<Q01pV>K1pRBM1").
Proof.
intros M k v HF Hk x Hx. pose proof (u64_range x).
destruct Hx as [Hx|Hx].
- rewrite wbytes_below; [apply HF; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | unorm; lia].
- rewrite wbytes_above; [apply HF; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia].
Qed.
#[using="p n f l Hn Hs"] Lemma out_agree_rdn : ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "Q:'T1yR0%211'8y8%511%311p051'5&QEr3%211&RD&RA&T2%12>5&RIr2%211%6241&RKvSL+RTH%3221%<251'?'4%11F%I11&R5&R?r5r4%44321GvS;%64513I%;3831p0=1p0K1pV>O1pULQ61pRBQ21").
Proof. intros M a k HF Ha. apply rdn_ext; [lia|]. intros x Hx. apply HF. lia. Qed.
#[using="p n f l Hn Hs HG HI"] Lemma out_agree_globs : ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "D'T1yR0%211'8y8%511%311p051&QEr1%211'>&R0r2%211&QJ%113%6231p081pRB<1").
Proof.
intros M HF. destruct HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). destruct HI as (I1 & I2 & I3).
unfold rt_layout_globs, ms_icpt_globs. rewrite !(out_agree_rdn M) by (first [exact HF | cbn [Z.of_nat Pos.to_nat]; imm_norm; lia]).
repeat split; assumption.
Qed.
Section SE.
Local Abbreviation SEC_T_out_agree_store_ok := (ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "Q:'T1yR0%211'8y8%511%311p051'C'5&R>vS;r3%3221'>&RD&RIr2%211%4217+RTH%6291%8231'?'1&M&R?r5&T0&RKvSLr4%3221%52Q01%94871F(<%=3<21p0?1p0I1pV<N1pV>Q01pRBQ21")) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SEC_T_out_agree_store_ok) 0%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_out_agree_store_ok) 1%nat 0%nat).
Variable j : ltac:(sec_ty2 constr:(SEC_T_out_agree_store_ok) 2%nat 0%nat).
Lemma out_agree_store_ok : ltac:(sec_stmt2 constr:(SEC_T_out_agree_store_ok) 3%nat 0%nat).
Proof using p n f l Hn Hs Hok M k j.
intros HGr Hk.
apply (store_ok_mono _ _ mem0 M _ HGr).
apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 2200)) _ 2200%nat); [unorm; cbn [Z.of_nat Pos.to_nat]; lia | exact Hok | unorm; lia | unorm; cbn [Z.of_nat Pos.to_nat]; lia].
Qed.
End SE.
#[local] Ltac grows := first [apply mem_grows_refl | eapply mem_grows_trans; [ | apply wbytes_grows ]; grows].
#[local] Ltac fsok := apply out_agree_store_ok; [grows | cbn [Z.of_nat Pos.to_nat]; lia].
#[local] Ltac oagree := repeat (apply out_agree_w; [|lia]); apply out_agree_refl.
Definition M8 (rg : bvmap 5 word) : word -> option byte :=
wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem0
(Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra))
(Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr rg 8)))
(Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr rg 9)))
(Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr rg 18)))
(Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr rg 19)))
(Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr rg 20)))
(Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr rg 21)).
#[using="p n f l Hn Hs"] Lemma M8_out_agree : ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "<&Q7y5'T1yR0%211%5241&QE&QAr1%211%411pWB61"). Proof. intros rg. unfold M8. oagree. Qed.
#[using="Type"] Lemma M8_grows : ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "=&Q7y5'T1yR0%211%5241&R>vS;&QAr1%211%5241pWB71"). Proof. intros rg. unfold M8. grows. Qed.
Definition slots_ok (regs0 : bvmap 5 word) (M : word -> option byte) : Prop :=
rdn ASEGS M (Z_to_bv 64 (s - 8)) 8%nat = Some (word_to_le_bytes 8 ra) /\
rdn ASEGS M (Z_to_bv 64 (s - 16)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 8)) /\
rdn ASEGS M (Z_to_bv 64 (s - 24)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 9)) /\
rdn ASEGS M (Z_to_bv 64 (s - 32)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 18)) /\
rdn ASEGS M (Z_to_bv 64 (s - 40)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 19)) /\
rdn ASEGS M (Z_to_bv 64 (s - 48)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 20)) /\
rdn ASEGS M (Z_to_bv 64 (s - 56)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 21)).
Definition FR (regs0 : bvmap 5 word) (M : word -> option byte) : Prop := out_agree M /\ mem_grows mem0 M /\ slots_ok regs0 M.
#[local] Ltac peel :=
rewrite rdn_wbytes_out;
[ | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | cbn [Z.of_nat Pos.to_nat]; unorm; lia
| rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia ].
#[local] Ltac slot := repeat peel; apply rdn_wbytes_hit8; unorm; lia.
Section SE.
Local Abbreviation SEC_T_M8_FR := (ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "<&Q7y5'T1yR0%211%5241&Q@r1&QA%112%4231pW@61")) (only parsing).
Variable regs0 : ltac:(sec_ty2 constr:(SEC_T_M8_FR) 0%nat 0%nat).
Lemma M8_FR : ltac:(sec_stmt2 constr:(SEC_T_M8_FR) 1%nat 0%nat).
Proof using p n f l Hn Hs regs0.
split; [apply M8_out_agree | split; [apply M8_grows|]]. unfold M8. repeat split; slot. Qed.
End SE.
Definition c1_post (regs rg : bvmap 5 word) : Prop :=
getr rg 10 = Z_to_bv 64 p /\ getr rg 11 = cv /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 s
/\ getr rg 2 = Z_to_bv 64 (s - 2128) /\ getr rg 1 = ra.
Section SE.
Local Abbreviation SEC_T_c1_run := (ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "R>&Q7y5'T1yR0%211%5241'?&R3r1(SO+:(=%33;21%6251&T0vS=%22=1%;3=41r2+;%;3C19%>231vS0%A3C21r3+<%A3I1?%D231vS<%?2J1%H3J31r4+2%H3Q01F%K231vSN%N3Q021r5+1%N3Q61L%Q1231vSC%Q43Q621'@'>'Q>&R?&R4vS3r7+^ne8%Q:3Q@1Q8/01Q@vS;vSI%8576321+^ng0%Q@3QF1Q>/01QF&QA%11;%>5=QE317%A3@71&QB%12?QH&QO&QI%231BQK%H241%I271qW>R11%L2R21p0N1p0Q51p0Q<1p0QD1p0QK1pW<R81")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_c1_run) 0%nat 0%nat).
Lemma c1_run : ltac:(sec_stmt2 constr:(SEC_T_c1_run) 1%nat 0%nat).
Proof using f l Hs_def Hn Hs Hok HG HI regs.
intros H10 H11 H12 H2 H1.
rewrite sp_s in H2.
pose proof (out_agree_globs (M8 regs) (M8_out_agree regs)) as ((G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8) & (I1 & I2 & I3)).
unfold M8 in *.
eexists. split.
- stepiv (ltac:(oF' 0x77aa8%Z)) (ltac:(oD' 0x77aa8%Z)) (Z_to_bv 64 (s - 2032)) ltac:(wval).
stepsd (ltac:(oF' 0x77aac%Z)) (ltac:(oD' 0x77aac%Z)) (Z_to_bv 64 (s - 8)) ra ltac:(fsok).
stepsd (ltac:(oF' 0x77ab0%Z)) (ltac:(oD' 0x77ab0%Z)) (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(fsok).
stepsd (ltac:(oF' 0x77ab4%Z)) (ltac:(oD' 0x77ab4%Z)) (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(fsok).
stepsd (ltac:(oF' 0x77ab8%Z)) (ltac:(oD' 0x77ab8%Z)) (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(fsok).
stepsd (ltac:(oF' 0x77abc%Z)) (ltac:(oD' 0x77abc%Z)) (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(fsok).
stepsd (ltac:(oF' 0x77ac0%Z)) (ltac:(oD' 0x77ac0%Z)) (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(fsok).
stepsd (ltac:(oF' 0x77ac4%Z)) (ltac:(oD' 0x77ac4%Z)) (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(fsok).
stepiv (ltac:(oF' 0x77ac8%Z)) (ltac:(oD' 0x77ac8%Z)) (Z_to_bv 64 s) ltac:(wval).
stepiv (ltac:(oF' 0x77acc%Z)) (ltac:(oD' 0x77acc%Z)) (Z_to_bv 64 (s - 2128)) ltac:(wval).
stepn (ltac:(oF' 0x77ad0%Z)) (ltac:(oD' 0x77ad0%Z)).
mld (ltac:(oF' 0x77ad4%Z)) (ltac:(oD' 0x77ad4%Z)) (0x134f08 : word) I1.
mlbu (ltac:(oF' 0x77ad8%Z)) (ltac:(oD' 0x77ad8%Z)) (0x13d719 : word) I2.
stepb_ft (ltac:(oF' 0x77adc%Z)) (ltac:(oD' 0x77adc%Z)) ltac:(cond).
apply mst_refl.
- unfold c1_post. split; [repeat split; gres; rwH; try reflexivity | solve_keeps_but].
Qed.
End SE.
Definition c2_post (rg : bvmap 5 word) : Prop :=
getr rg 10 = Z_to_bv 64 p /\ getr rg 11 = cv /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 2 = Z_to_bv 64 (s - 2128).
#[local] Ltac xval := gres; rwH; unfold v_xori; imm_norm; unorm; rewrite lxor_ones64 by lia; first [reflexivity | f_equal; lia].
#[using="Type"] Lemma ret_ok_77c90 : ltac2:(TCodec.tc2 tcn__Jb0AsanMemset ":&Q?(SOyR0+^oT@(=%43321'T1%115/031%911"). Proof. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_c2z_run := (ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "QB&Q7y5'T1yR0%211%5241&QBr2r1%3221'?'CvS<z%43321'@'>'Q>&R?&R4vS3r4(SO+^ng0(=%33F21/01F&QAr5%211vSI%<5;:521+^niH%;3N19/01N%@5?K165%C3B51&QC%11N&QO&QI%231DQ1%J241%K271qW>Q71%N2Q81p0Q01p0Q61pW<Q;1pW@Q<1")) (only parsing).
Variable regs0 : ltac:(sec_ty2 constr:(SEC_T_c2z_run) 0%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_c2z_run) 1%nat 0%nat).
Lemma c2z_run : ltac:(sec_stmt2 constr:(SEC_T_c2z_run) 2%nat 0%nat).
Proof using f l Hn Happ Hs regs0 regs.
intros (H10 & H11 & H12 & H8 & H2 & H1) Hn0.
pose proof p_facts as (Pp & Ppn & Pp8 & Pq). unfold HIGHEND in *.
eexists. split.
- stepiv (ltac:(oF' 0x77ae0%Z)) (ltac:(oD' 0x77ae0%Z)) (Z_to_bv 64 (2 ^ 64 - 1 - p)) ltac:(xval).
stepiv (ltac:(oF' 0x77ae4%Z)) (ltac:(oD' 0x77ae4%Z)) (Z_to_bv 64 (s - 2048)) ltac:(wval).
stepiv (ltac:(oF' 0x77ae8%Z)) (ltac:(oD' 0x77ae8%Z)) (Z_to_bv 64 (s - 2128)) ltac:(wval).
stepb_ft (ltac:(oF' 0x77aec%Z)) (ltac:(oD' 0x77aec%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x77af0%Z)) (ltac:(oD' 0x77af0%Z)) (Z_to_bv 64 (2 ^ 64 - 65))
ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; rewrite (zbv_wrap_up (n + - 65)); f_equal; lia).
stepn (ltac:(oF' 0x77af4%Z)) (ltac:(oD' 0x77af4%Z)).
stepb_tk (ltac:(oF' 0x77af8%Z)) (ltac:(oD' 0x77af8%Z)) ltac:(cond).
stepb_ft (ltac:(oF' 0x77c40%Z)) (ltac:(oD' 0x77c40%Z)) ltac:(cond).
stepn (ltac:(oF' 0x77c44%Z)) (ltac:(oD' 0x77c44%Z)).
apply mst_refl.
- unfold c2_post. split; [repeat split; gres; rwH; reflexivity | solve_keeps_but].
Qed.
End SE.
#[using="p n f l Hn Hs"] Lemma rdn_slot_ext : ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "QE'T1yR0%211'8y8%511%311p051'C'>&RD&RKvSL+RR@%3221&T2r1%22@1%8241&RF%1238%<231'?r5r2%211r4%113%63F31p081pXDL1+8%F218%G29D%I221'4%11O%Q211&R5&R?&T0r3%O2N1%32Q:1u8%746F21%847D32%I3:21p0>1p0C1pV>Q:1pRHQ<1pRFQ=1").
Proof.
intros M1 M2 k HE Hk. apply rdn_ext; [unorm; cbn [Z.of_nat Pos.to_nat]; lia|].
intros x Hx. rewrite u_Z2bv in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx. apply HE. lia.
Qed.
#[using="p n f l Hn Hs"] Lemma slots_ok_ext : ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "Q:&Q7y5'T1yR0%211%5241'8y8%611%311p061'>&RD&RKvSL+RR@%3221&T2r1%22@1%8241&RF%1238%<231'?r3r2%211r4%113%63E31p081pXDL1&QH%1269r5%321;p031p061pRHM1pRFN1pW@Q41").
Proof.
intros regs0 M1 M2 HE (R1 & R2 & R3 & R4 & R5 & R6 & R7). unfold slots_ok.
rewrite !(rdn_slot_ext M2 M1) by (first [exact HE | lia]). repeat split; assumption.
Qed.
#[using="p n f l Hn Hs"] Lemma FR_region : ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "Q0&Q7y5'T1yR0%211%5241'8y8%611%311p061&QN&QAr2%211&RKvSL+RR@%3221r1%93621&R>r3%;11%321;&Q@r4%2215p041p091pRDD1pW@J1").
Proof.
intros regs0 M' HF HGr. pose proof (M8_FR regs0) as (O8 & G8 & R8).
split; [|split].
- intros x Hx. rewrite (HF x) by lia. apply O8. exact Hx.
- eapply mem_grows_trans; [exact G8 | exact HGr].
- apply (slots_ok_ext regs0 (M8 regs0) M'); [|exact R8]. intros x Hx. apply HF. lia.
Qed.
Section SE.
Local Abbreviation SEC_T_c2r_run := (ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "QK&Q7y5'T1yR0%211%5241&QBr2r1%3221&RF+R0vS<%3221'@'8y8%?11%311p0?1'>'Q>&R?&R4vS3r5(SO+^ng0(=%33J21/01J&QAr6%211vSI%<5;:521+^niH%;3Q219/01Q2%@5?Q01O5%C3B51&QC%11Q3&QO&QI%231DQ6&Q@%12?Q7%L231%M271%N2:1qRDQ01%Q62Q11qW>Q@1%Q82QA1p0Q:1p0Q?1pW<QD1pW@QE1")) (only parsing).
Variable regs0 : ltac:(sec_ty2 constr:(SEC_T_c2r_run) 0%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_c2r_run) 1%nat 0%nat).
Lemma c2r_run : ltac:(sec_stmt2 constr:(SEC_T_c2r_run) 2%nat 0%nat).
Proof using kL f l fa la Hf_def Hl_def Hn Happ Hs Hshs Hok HG HI HZ HL HkL HW regs0 regs.
intros (H10 & H11 & H12 & H8 & H2 & H1) Hn64.
pose proof p_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)).
unfold HIGHEND in *.
assert (S1 : exists r1, msteps ASEGS (mkst regs (0x77ae0 : word) (M8 regs0) rom) (mkst r1 (0x7ae38 : word) (M8 regs0) rom)
/\ (getr r1 10 = Z_to_bv 64 p /\ getr r1 11 = Z_to_bv 64 n /\ getr r1 2 = Z_to_bv 64 (s - 2128) /\ getr r1 1 = (0x77c90 : word)
/\ getr r1 9 = Z_to_bv 64 p /\ getr r1 21 = cv /\ getr r1 18 = Z_to_bv 64 n /\ keeps_but RIPL regs r1)).
{ eexists. split.
- stepiv (ltac:(oF' 0x77ae0%Z)) (ltac:(oD' 0x77ae0%Z)) (Z_to_bv 64 (2 ^ 64 - 1 - p)) ltac:(xval).
stepiv (ltac:(oF' 0x77ae4%Z)) (ltac:(oD' 0x77ae4%Z)) (Z_to_bv 64 (s - 2048)) ltac:(wval).
stepiv (ltac:(oF' 0x77ae8%Z)) (ltac:(oD' 0x77ae8%Z)) (Z_to_bv 64 (s - 2128)) ltac:(wval).
stepb_ft (ltac:(oF' 0x77aec%Z)) (ltac:(oD' 0x77aec%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x77af0%Z)) (ltac:(oD' 0x77af0%Z)) (Z_to_bv 64 (n - 65)) ltac:(wval).
stepn (ltac:(oF' 0x77af4%Z)) (ltac:(oD' 0x77af4%Z)).
stepb_tk (ltac:(oF' 0x77af8%Z)) (ltac:(oD' 0x77af8%Z)) ltac:(cond).
stepb_tk (ltac:(oF' 0x77c40%Z)) (ltac:(oD' 0x77c40%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x77c7c%Z)) (ltac:(oD' 0x77c7c%Z)) (Z_to_bv 64 p) ltac:(wval).
stepiv (ltac:(oF' 0x77c80%Z)) (ltac:(oD' 0x77c80%Z)) cv ltac:(gres; rwH; apply v_addi_0).
stepiv (ltac:(oF' 0x77c84%Z)) (ltac:(oD' 0x77c84%Z)) (Z_to_bv 64 n) ltac:(wval).
stepiv (ltac:(oF' 0x77c88%Z)) (ltac:(oD' 0x77c88%Z)) (Z_to_bv 64 n) ltac:(wval).
stepn (ltac:(oF' 0x77c8c%Z)) (ltac:(oD' 0x77c8c%Z)).
apply mst_refl.
- repeat split; gres; rwH; try reflexivity; try (apply bv_eq; reflexivity). solve_keeps_but. }
destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q2 & Q1 & Q9 & Q21 & Q18 & K1).
pose proof (out_agree_globs (M8 regs0) (M8_out_agree regs0)) as (HG8 & _).
pose proof (region_is_poisoned_run (M8 regs0) rom (Z_to_bv 64 (s - 2128)) (0x77c90 : word) p n (s - 2128)
ltac:(unorm; reflexivity) ltac:(lia) Happ ltac:(lia) ltac:(unfold SB in *; lia)
ltac:(replace (s - 2128 - 72)%Z with (s - 2200)%Z by lia; apply out_agree_store_ok; [apply M8_grows | cbn; lia])
ret_ok_77c90 HG8 kL) as RP.
specialize (RP ltac:(intros x Hx; rewrite (M8_out_agree regs0 x) by (unfold SB in *; lia); apply HZ; [lia | unfold SB in *; lia])).
specialize (RP ltac:(rewrite (M8_out_agree regs0) by (unfold SB in *; unorm; lia); rewrite <- Hl_def; apply HL; lia) HkL).
destruct (RP r1 Q10 Q11 Q2 Q1) as (r2 & M2 & RUN2 & V10 & V2 & V1 & K2 & F2 & G2).
assert (S9 : getr r2 9 = Z_to_bv 64 p) by (rewrite (K2 9%bv) by (cbv; tauto); exact Q9).
assert (S18 : getr r2 18 = Z_to_bv 64 n) by (rewrite (K2 18%bv) by (cbv; tauto); exact Q18).
assert (S21 : getr r2 21 = cv) by (rewrite (K2 21%bv) by (cbv; tauto); exact Q21).
eexists. exists M2. split; [|split; [|split; [|apply FR_region; assumption]]].
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
stepiv (ltac:(oF' 0x77c90%Z)) (ltac:(oD' 0x77c90%Z)) cv ltac:(gres; rwH; apply v_addi_0).
stepiv (ltac:(oF' 0x77c94%Z)) (ltac:(oD' 0x77c94%Z)) (Z_to_bv 64 n) ltac:(wval).
stepiv (ltac:(oF' 0x77c98%Z)) (ltac:(oD' 0x77c98%Z)) (Z_to_bv 64 0) ltac:(wval).
stepiv (ltac:(oF' 0x77c9c%Z)) (ltac:(oD' 0x77c9c%Z)) (Z_to_bv 64 p) ltac:(wval).
stepb_tk (ltac:(oF' 0x77ca0%Z)) (ltac:(oD' 0x77ca0%Z)) ltac:(cond).
apply mst_refl.
- unfold c2_post. repeat split; gres; rwH; reflexivity.
- eapply keeps_but_trans; [exact K1|]. solve_keeps_but.
Qed.
End SE.
#[using="p Hf_def Hl_def Hfa_def Hla_def Hn Happ Hshs"] Lemma fl_facts : ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "Q<&RFzvS<%3221'>&RD&QMvS1%3221vS8%5231%7231&RA+8%2251&RKvSL+RTH%3221%>251+7%62>1vS2%B221%C22A%E221%;2A6vS9%G221%H22D%J221'?'C&RH%12<E%4331Q2%329G%6351Q4%Q2231%Q3291%Q42?1%Q52F1%Q62O1p0Q81").
Proof.
intros Hn0. pose proof p_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq Hn0). unfold SB, HIGHEND in *.
pose proof (Z.mod_pos_bound f 8 ltac:(lia)). pose proof (Z.mod_pos_bound l 8 ltac:(lia)).
pose proof (Z.div_mod f 8 ltac:(lia)). pose proof (Z.div_mod l 8 ltac:(lia)).
repeat split; try lia.
- rewrite Hfa_def. replace (f - f mod 8)%Z with (8 * (f / 8))%Z by lia. rewrite Z.mul_comm. apply Z_mod_mult.
- rewrite Hla_def. replace (l - l mod 8)%Z with (8 * (l / 8))%Z by lia. rewrite Z.mul_comm. apply Z_mod_mult.
Qed.
#[using="p f l Hf_def Hl_def Hfa_def Hla_def Hn Happ Hs Hshs HW"] Lemma rdnW_M8 : ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "R0&Q7y5'T1yR0%211%5241'>&RFzvS<%3221&RD+R0%2241%8241'@'4y8%@11%311'?'8%113&R5&R?&QAr4%211&T0vS2%22K1u8%948521(0r2%22@1%@3>41vS9%:2Q31%@4?<18r1%82F1%F3D31&E%11:%Q22Q51&RJ+2%221Q4%Q:251%Q<251%81;%Q92Q<1%Q>225%Q@221%QA251%QB2>1%QC2E1qXBQ71%Q<2Q81qX@Q91%Q>2Q:1p0Q@1pW@QJ1").
Proof.
intros regs0 Hn64. pose proof (fl_facts ltac:(lia)) as (F1 & F2 & F3 & F4 & F5 & F6). unfold SB in *.
destruct (HW Hn64) as (w0 & w1 & R0 & R1). exists w0, w1.
rewrite !(out_agree_rdn (M8 regs0)) by (first [apply M8_out_agree | unorm; cbn [Z.of_nat Pos.to_nat]; lia]).
split; [exact R0 | split; [exact R1 | split; [exact (bytes8_range _ _ _ _ R0) | exact (bytes8_range _ _ _ _ R1)]]].
Qed.
#[using="p fa la Hf_def Hl_def Hfa_def Hla_def Hn Happ Hs Hshs HZ"] Lemma rdn1_M8 : ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "Q@&Q7y5'T1yR0%211%5241'C&RFzvS<%3221'>&RDvS1r2%3221vS8%:231%7231'?'8'4y8%E11%311%511&R5&R?&QAr4%211&T0r3%22N1u1%948521(0(2%72@N(7%11A%43B31%62B1%H3B81p0J1p0Q31pXFQ81pW@Q:1").
Proof.
intros regs0 z Hn0 Hz. pose proof (fl_facts ltac:(lia)) as (F1 & F2 & _). unfold SB in *.
cbn [rdn]. rewrite (M8_out_agree regs0) by (unorm; lia). rewrite (HZ Hn0) by (unorm; lia). reflexivity.
Qed.
#[using="p f fa la Hf_def Hl_def Hfa_def Hla_def Hn Happ Hs Hshs HL"] Lemma rdnL_M8 : ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "Q<&Q7y5'T1yR0%211%5241'C&RFzvS<%3221'?r2vS8%33821'8'4y8%@11%311%511&R5&R?&QAr4%211&T0r3%22I1u1%948521(0(2vS7%82A1(7%11B%53C31%72C1%L3C91p0J1p0O1pXFQ41pW@Q61").
Proof.
intros regs0 z Hn0 ->. pose proof (fl_facts ltac:(lia)) as (F1 & F2 & _). unfold SB in *.
cbn [rdn]. rewrite (M8_out_agree regs0) by (unorm; lia). rewrite (HL Hn0). reflexivity.
Qed.
#[local] Ltac maddr z := match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 z) by (symmetry; wval) end.
#[local] Ltac mlbu0 F D z :=
chain_step; [reflexivity
| eapply step_lbu; [exact F | reflexivity | exact D | maddr z; apply rdn1_M8; lia]
| step_simpl; vnorm].
#[local] Ltac mlbk F D z :=
chain_step; [reflexivity
| eapply step_lb; [exact F | reflexivity | exact D | maddr z; apply rdnL_M8; lia]
| step_simpl; vnorm; rewrite (v_lb_k kL ltac:(lia))].
#[local] Ltac mldw F D z R w :=
chain_step; [reflexivity
| eapply step_ld with (bs := w) (v := Z_to_bv 64 (bytes_le_to_Z w)); [exact F | reflexivity | exact D | maddr z; exact R | unorm; reflexivity]
| step_simpl; vnorm].
Definition c2qa_post (u0 u1 : Z) (rg : bvmap 5 word) : Prop :=
getr rg 13 = Z_to_bv 64 f /\ getr rg 14 = Z_to_bv 64 l /\ getr rg 15 = Z_to_bv 64 (p + n - 1) /\ getr rg 16 = Z_to_bv 64 (Z.lor u1 u0)
/\ getr rg 10 = Z_to_bv 64 p /\ getr rg 11 = cv /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 2 = Z_to_bv 64 (s - 2128).
Section SE.
Local Abbreviation SEC_T_c2qa_run := (ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "S0&Q7y5'T1yR0%211%5241'4y8%611%311&QBr4r3%3221'>&RFzvS<%3221&RD+R0%2241%8241'?'8%11@&R5&R?&QAr6%211&T0vS2%22N1u8%948521(0%12LJ%?3=31r7%<11vS9%;2Q71%A4@319%E3C17&E%11A%L2O1&RJ+2%221N%Q4251%Q6251'@'Q>&R4vS3r:(SO+^ng0(=%33QJ21/01QJr;%Q411vSI%;5:9421r1+^niD%;3R219/01R2%@5?4176%B3Q=61&QDr9%N11r8%Q011%5331;&QO&QI%231H>%R4241%R52;1qW>R?1%Q02R@1p0Q21p0Q31p0Q<1p0QC1p0R41p0R>1pXBRC1pX@RD1pW<RI1pW@RJ1")) (only parsing).
Variable regs0 : ltac:(sec_ty2 constr:(SEC_T_c2qa_run) 0%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_c2qa_run) 1%nat 0%nat).
Variable w0 : ltac:(sec_ty2 constr:(SEC_T_c2qa_run) 2%nat 0%nat).
Variable w1 : ltac:(sec_ty2 constr:(SEC_T_c2qa_run) 3%nat 0%nat).
Lemma c2qa_run : ltac:(sec_stmt2 constr:(SEC_T_c2qa_run) 4%nat 0%nat).
Proof using Hf_def Hl_def Hfa_def Hla_def Hn Happ Hs Hshs HG HI regs0 regs w0 w1.
intros (H10 & H11 & H12 & H8 & H2 & H1) Hn64 R0 R1 B0 B1.
pose proof p_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)).
pose proof (fl_facts ltac:(lia)) as (F1 & F2 & F3 & F4 & F5 & F6).
pose proof (out_agree_globs (M8 regs0) (M8_out_agree regs0)) as ((G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8) & _).
unfold SB, HIGHEND in *.
pose proof (Z.div_mod p 8 ltac:(lia)) as Dp. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Mp.
pose proof (Z.mod_pos_bound f 8 ltac:(lia)) as Mf. pose proof (Z.mod_pos_bound l 8 ltac:(lia)) as Ml.
pose proof (lor_bound64 (bytes_le_to_Z w1) (bytes_le_to_Z w0) B1 B0) as BL.
eexists. split.
- stepiv (ltac:(oF' 0x77ae0%Z)) (ltac:(oD' 0x77ae0%Z)) (Z_to_bv 64 (2 ^ 64 - 1 - p)) ltac:(xval).
stepiv (ltac:(oF' 0x77ae4%Z)) (ltac:(oD' 0x77ae4%Z)) (Z_to_bv 64 (s - 2048)) ltac:(wval).
stepiv (ltac:(oF' 0x77ae8%Z)) (ltac:(oD' 0x77ae8%Z)) (Z_to_bv 64 (s - 2128)) ltac:(wval).
stepb_ft (ltac:(oF' 0x77aec%Z)) (ltac:(oD' 0x77aec%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x77af0%Z)) (ltac:(oD' 0x77af0%Z)) (Z_to_bv 64 (2 ^ 64 + n - 65))
ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; rewrite (zbv_wrap_up (n + - 65)); f_equal; lia).
stepn (ltac:(oF' 0x77af4%Z)) (ltac:(oD' 0x77af4%Z)).
stepb_ft (ltac:(oF' 0x77af8%Z)) (ltac:(oD' 0x77af8%Z)) ltac:(cond).
stepn (ltac:(oF' 0x77afc%Z)) (ltac:(oD' 0x77afc%Z)).
mld (ltac:(oF' 0x77b00%Z)) (ltac:(oD' 0x77b00%Z)) (0x1343a0 : word) G1.
stepiv (ltac:(oF' 0x77b04%Z)) (ltac:(oD' 0x77b04%Z)) (Z_to_bv 64 (p + n)) ltac:(wval).
mld (ltac:(oF' 0x77b08%Z)) (ltac:(oD' 0x77b08%Z)) (0x13ca38 : word) G2.
stepiv (ltac:(oF' 0x77b0c%Z)) (ltac:(oD' 0x77b0c%Z)) (Z_to_bv 64 (p / 8)) ltac:(wval).
stepiv (ltac:(oF' 0x77b10%Z)) (ltac:(oD' 0x77b10%Z)) (Z_to_bv 64 (p + n - 1)) ltac:(wval).
stepiv (ltac:(oF' 0x77b14%Z)) (ltac:(oD' 0x77b14%Z)) (Z_to_bv 64 ((p + n - 1) / 8)) ltac:(wval).
stepiv (ltac:(oF' 0x77b18%Z)) (ltac:(oD' 0x77b18%Z)) (Z_to_bv 64 f) ltac:(wval).
stepiv (ltac:(oF' 0x77b1c%Z)) (ltac:(oD' 0x77b1c%Z)) (Z_to_bv 64 l) ltac:(wval).
stepiv (ltac:(oF' 0x77b20%Z)) (ltac:(oD' 0x77b20%Z)) (Z_to_bv 64 fa)
ltac:(gres; rwH; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; f_equal; lia).
stepiv (ltac:(oF' 0x77b24%Z)) (ltac:(oD' 0x77b24%Z)) (Z_to_bv 64 la)
ltac:(gres; rwH; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; f_equal; lia).
mldw (ltac:(oF' 0x77b28%Z)) (ltac:(oD' 0x77b28%Z)) fa R0 w0.
mldw (ltac:(oF' 0x77b2c%Z)) (ltac:(oD' 0x77b2c%Z)) la R1 w1.
stepov (ltac:(oF' 0x77b30%Z)) (ltac:(oD' 0x77b30%Z)) (Z_to_bv 64 (Z.lor (bytes_le_to_Z w1) (bytes_le_to_Z w0))) ltac:(gres; rwH; unfold v_or; unorm; reflexivity).
apply mst_refl.
- unfold c2qa_post, SB. split; [repeat split; gres; rwH; try reflexivity; f_equal; lia | solve_keeps_but].
Qed.
End SE.
Definition ql_inv (rg : bvmap 5 word) (i : Z) : Prop :=
getr rg 13 = Z_to_bv 64 (f + i) /\ getr rg 14 = Z_to_bv 64 l /\ getr rg 15 = Z_to_bv 64 0
/\ getr rg 10 = Z_to_bv 64 p /\ getr rg 11 = cv /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 2 = Z_to_bv 64 (s - 2128).
Definition ql_post (rg : bvmap 5 word) : Prop :=
getr rg 15 = Z_to_bv 64 0 /\ getr rg 10 = Z_to_bv 64 p /\ getr rg 11 = cv /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 2 = Z_to_bv 64 (s - 2128).
#[local] Ltac post := repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try solve_keeps_but.
#[local] Ltac vlit := gres; rwH; apply bv_eq; vm_compute; reflexivity.
Section SE.
Local Abbreviation SEC_T_qloop_run := (ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "R7&Q7y5'T1yR0%211%5241'5'C&RFzvS<%3221&QFr3r2%3221&RD%1284'?&RAvS1r4%3221&RIr6%211%7241+1%9221vS8%<3G21'@'>'Q>&R?&R4vS3r7(SO+^oS4(=%33Q621/01Q6&QAr9%211vSI%<5;:521r1+^oSD%<3Q?1:/01Q?%A5@4176%D3C61&QG%117&QO&QI%231E:%K241%L271qW>QH1%O2QI1p0Q11p0Q?1p0QB1p0QG1pV:QL1pW<QO1pW0QO1pW@R11")) (only parsing).
Variable regs0 : ltac:(sec_ty2 constr:(SEC_T_qloop_run) 0%nat 0%nat).
Lemma qloop_run : ltac:(sec_stmt2 constr:(SEC_T_qloop_run) 1%nat 0%nat).
Proof using fa la Hf_def Hl_def Hfa_def Hla_def Hn Happ Hs Hshs HZ regs0.
intros q.
induction q as [|q IH]; intros regs i Hn0 (H13 & H14 & H15 & H10 & H11 & H12 & H2) Hi Hq;
pose proof (fl_facts Hn0) as (F1 & F2 & _); unfold SB in *.
- eexists. split.
+ mlbu0 (ltac:(oF' 0x77c64%Z)) (ltac:(oD' 0x77c64%Z)) (f + i)%Z.
stepiv (ltac:(oF' 0x77c68%Z)) (ltac:(oD' 0x77c68%Z)) (Z_to_bv 64 (f + i + 1)) ltac:(wval).
stepov (ltac:(oF' 0x77c6c%Z)) (ltac:(oD' 0x77c6c%Z)) (Z_to_bv 64 0) ltac:(vlit).
stepb_ft (ltac:(oF' 0x77c70%Z)) (ltac:(oD' 0x77c70%Z)) ltac:(cond).
apply mst_refl.
+ unfold ql_post. post.
- eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x77c64 : word) (M8 regs0) rom) (fun rg => ql_inv rg (i + 1) /\ keeps_but RIPL regs rg)).
+ eexists. split.
* mlbu0 (ltac:(oF' 0x77c64%Z)) (ltac:(oD' 0x77c64%Z)) (f + i)%Z.
stepiv (ltac:(oF' 0x77c68%Z)) (ltac:(oD' 0x77c68%Z)) (Z_to_bv 64 (f + i + 1)) ltac:(wval).
stepov (ltac:(oF' 0x77c6c%Z)) (ltac:(oD' 0x77c6c%Z)) (Z_to_bv 64 0) ltac:(vlit).
stepb_tk (ltac:(oF' 0x77c70%Z)) (ltac:(oD' 0x77c70%Z)) ltac:(cond).
apply mst_refl.
* unfold ql_inv. post.
+ cbv beta. intros r1 (I1 & K1).
destruct (IH r1 (i + 1)%Z Hn0 I1 ltac:(lia) ltac:(lia)) as (r2 & RUN & P2 & K2).
exists r2. split; [exact RUN | split; [exact P2 | eapply keeps_but_trans; eassumption]].
Qed.
End SE.
#[using="Type"] Lemma c2qf_run : ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "R2&Q7y5'T1yR0%211%5241'C&QDr2r1r3%43321'>&RDz&RE%1286%4231&RF&RJ+2+R0%3221%5271%<271'?r4%<2A1%33F1>'@'Q>&R?&R4vS3r7(SO+^niD(=%33Q321/01Q3&QAr8%211vSI%<5;:521+^niH%;3Q;19/01Q;%@5?Q7165%C3B51&QC%11Q:&QO&QI%231DQ=%Q;241%Q<271qW>QD1%M2QE1p0O1p0Q41p0QB1pX:QH1pX8QI1pW<QK1pW@QL1").
Proof.
intros regs0 regs u0 u1 (H13 & H14 & H15 & H16 & H10 & H11 & H12 & H2) BL E.
eexists. split.
- stepb_ft (ltac:(oF' 0x77b34%Z)) (ltac:(oD' 0x77b34%Z)) ltac:(cond).
apply mst_refl.
- unfold c2_post. post.
Qed.
Section SE.
Local Abbreviation SEC_T_c2qs_run := (ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "R:&Q7y5'T1yR0%211%5241'C&QDr2r1r3%43321'>&RFzvS<%3221&RD+R0%2241%8241&REr4%22=1%72:1&RJ+2%2219%?251%A251&A'?r5%<2;1%33L1D%511'@'Q>&R?&R4vS3r8(SO+^niD(=%33Q:21/01Q:&QAr9%211vSI%<5;:521+^niH%;3QB19/01QB%@5?Q>165%C3B51&QC%11QA&QO&QI%231DQD%QB241%QC271qW>QK1%M2QL1p0O1p0Q61p0Q@1p0QJ1pX:R01pX8R11pW<R31pW@R41")) (only parsing).
Variable regs0 : ltac:(sec_ty2 constr:(SEC_T_c2qs_run) 0%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_c2qs_run) 1%nat 0%nat).
Variable u0 : ltac:(sec_ty2 constr:(SEC_T_c2qs_run) 2%nat 0%nat).
Variable u1 : ltac:(sec_ty2 constr:(SEC_T_c2qs_run) 3%nat 0%nat).
Lemma c2qs_run : ltac:(sec_stmt2 constr:(SEC_T_c2qs_run) 4%nat 0%nat).
Proof using kL fa la Hf_def Hl_def Hfa_def Hla_def Hn Happ Hs Hshs HZ HL HkL regs0 regs u0 u1.
intros (H13 & H14 & H15 & H16 & H10 & H11 & H12 & H2) Hn64 BL NE.
pose proof p_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)).
pose proof (fl_facts ltac:(lia)) as (F1 & F2 & F3 & F4 & F5 & F6). unfold SB, HIGHEND in *.
pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)) as Mq.
eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x77c60 : word) (M8 regs0) rom) (fun rg => ql_inv rg 0 /\ keeps_but RIPL regs rg)).
{ destruct HkL as [K0|K7].
- eexists. split.
+ stepb_tk (ltac:(oF' 0x77b34%Z)) (ltac:(oD' 0x77b34%Z)) ltac:(cond).
mlbk (ltac:(oF' 0x77c48%Z)) (ltac:(oD' 0x77c48%Z)) l.
stepiv (ltac:(oF' 0x77c4c%Z)) (ltac:(oD' 0x77c4c%Z)) (Z_to_bv 64 ((p + n - 1) mod 8))
ltac:(gres; rwH; unfold v_andi; imm_norm; unorm; rewrite land7_mod8; reflexivity).
stepov (ltac:(oF' 0x77c50%Z)) (ltac:(oD' 0x77c50%Z)) (Z_to_bv 64 0)
ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (0 <? kL)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
stepov (ltac:(oF' 0x77c54%Z)) (ltac:(oD' 0x77c54%Z)) (Z_to_bv 64 0)
ltac:(gres; rwH; unfold v_slt, c_lts, bv_lts; rewrite !signed64_small by lia;
replace ((p + n - 1) mod 8 <? kL)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
stepiv (ltac:(oF' 0x77c58%Z)) (ltac:(oD' 0x77c58%Z)) (Z_to_bv 64 1) ltac:(vlit).
stepov (ltac:(oF' 0x77c5c%Z)) (ltac:(oD' 0x77c5c%Z)) (Z_to_bv 64 0) ltac:(vlit).
apply mst_refl.
+ unfold ql_inv. post.
- eexists. split.
+ stepb_tk (ltac:(oF' 0x77b34%Z)) (ltac:(oD' 0x77b34%Z)) ltac:(cond).
mlbk (ltac:(oF' 0x77c48%Z)) (ltac:(oD' 0x77c48%Z)) l.
stepiv (ltac:(oF' 0x77c4c%Z)) (ltac:(oD' 0x77c4c%Z)) (Z_to_bv 64 ((p + n - 1) mod 8))
ltac:(gres; rwH; unfold v_andi; imm_norm; unorm; rewrite land7_mod8; reflexivity).
stepov (ltac:(oF' 0x77c50%Z)) (ltac:(oD' 0x77c50%Z)) (Z_to_bv 64 1)
ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (0 <? kL)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
stepov (ltac:(oF' 0x77c54%Z)) (ltac:(oD' 0x77c54%Z)) (Z_to_bv 64 1)
ltac:(gres; rwH; unfold v_slt, c_lts, bv_lts; rewrite !signed64_small by lia;
replace ((p + n - 1) mod 8 <? kL)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
stepiv (ltac:(oF' 0x77c58%Z)) (ltac:(oD' 0x77c58%Z)) (Z_to_bv 64 0) ltac:(vlit).
stepov (ltac:(oF' 0x77c5c%Z)) (ltac:(oD' 0x77c5c%Z)) (Z_to_bv 64 0) ltac:(vlit).
apply mst_refl.
+ unfold ql_inv. post. }
cbv beta. intros r1 ((I13 & I14 & I15 & I10 & I11 & I12 & I2) & K1).
eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x77c74 : word) (M8 regs0) rom) (fun rg => ql_post rg /\ keeps_but RIPL regs rg)).
{ destruct (Z.lt_ge_cases f l) as [Hfl|Hfl].
- eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x77c64 : word) (M8 regs0) rom) (fun rg => ql_inv rg 0 /\ keeps_but RIPL regs rg)).
+ eexists. split.
* stepb_ft (ltac:(oF' 0x77c60%Z)) (ltac:(oD' 0x77c60%Z)) ltac:(cond).
apply mst_refl.
* split; [unfold ql_inv; repeat split; assumption | exact K1].
+ cbv beta. intros r2 (I2' & K2).
destruct (qloop_run regs0 (Z.to_nat (l - f - 1)) r2 0 ltac:(lia) I2' ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (r3 & RUN3 & P3 & K3).
exists r3. split; [exact RUN3 | split; [exact P3 | eapply keeps_but_trans; eassumption]].
- eexists. split.
+ stepb_tk (ltac:(oF' 0x77c60%Z)) (ltac:(oD' 0x77c60%Z)) ltac:(cond).
apply mst_refl.
+ split; [unfold ql_post; repeat split; assumption | exact K1]. }
cbv beta. intros r4 ((J15 & J10 & J11 & J12 & J2) & K4).
eexists. split.
- stepiv (ltac:(oF' 0x77c74%Z)) (ltac:(oD' 0x77c74%Z)) (Z_to_bv 64 0) ltac:(vlit).
stepb_tk (ltac:(oF' 0x77c78%Z)) (ltac:(oD' 0x77c78%Z)) ltac:(cond).
apply mst_refl.
- unfold c2_post. split; [repeat split; gres; rwH; reflexivity|]. eapply keeps_but_trans; [exact K4|]. solve_keeps_but.
Qed.
End SE.
#[using="kL f l fa la Hf_def Hl_def Hfa_def Hla_def Hn Happ Hs Hshs Hok HG HI HZ HL HkL HW"] Lemma c2_run : ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "QF&Q7y5'T1yR0%211%5241&QBr2r1%3221'@'8y8%;11%311p0;1'>'Q>&R?&R4vS3r4(SO+^ng0(=%33F21/01F&QAr5%211vSI%<5;:521+^niH%;3N19/01N%@5?L1K5%C3B51&QC%11O&QO&QI%231DQ2&Q@%12?Q3%L231%M271%N2:1qRDQ01%Q62Q11qW>Q<1%Q82Q=1p0Q:1pW<Q?1pW@Q@1").
Proof.
intros regs0 regs P1.
destruct (Z.eq_dec n 0) as [Hn0|Hn0].
{ destruct (c2z_run regs0 regs P1 Hn0) as (r2 & RUN2 & P2 & K2). exists r2, (M8 regs0).
split; [exact RUN2 | split; [exact P2 | split; [exact K2 | apply M8_FR]]]. }
destruct (Z.le_gt_cases n 64) as [Hle|Hgt].
- destruct (rdnW_M8 regs0 ltac:(lia)) as (w0 & w1 & R0 & R1 & B0 & B1).
destruct (c2qa_run regs0 regs w0 w1 P1 ltac:(lia) R0 R1 B0 B1) as (r2 & RUN2 & P2 & K2).
pose proof (lor_bound64 _ _ B1 B0) as BL.
destruct (Z.eq_dec (Z.lor (bytes_le_to_Z w1) (bytes_le_to_Z w0)) 0) as [E|NE].
+ destruct (c2qf_run regs0 r2 _ _ P2 BL E) as (r3 & RUN3 & P3 & K3). exists r3, (M8 regs0).
split; [eapply msteps_trans; [exact RUN2 | exact RUN3] | split; [exact P3 | split; [eapply keeps_but_trans; eassumption | apply M8_FR]]].
+ destruct (c2qs_run regs0 r2 _ _ P2 ltac:(lia) BL NE) as (r3 & RUN3 & P3 & K3). exists r3, (M8 regs0).
split; [eapply msteps_trans; [exact RUN2 | exact RUN3] | split; [exact P3 | split; [eapply keeps_but_trans; eassumption | apply M8_FR]]].
- exact (c2r_run regs0 regs P1 Hgt).
Qed.
#[using="Type"] Lemma ret_ok_77b44 : ltac2:(TCodec.tc2 tcn__Jb0AsanMemset ":&Q?(SOyR0+^nj4(=%43321'T1%115/031%911"). Proof. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma keeps_but_ms : ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "E'4'T1y5%211%411&Q7yR0%611%3261&R2r2r1%3221&QOr4r3%33216p051pW6:1pW4;1pQ:@1").
Proof. intros L r1 r2 AG. apply keeps_but_cs. apply keeps_keeps_cs. apply ms_agree_keeps. exact AG. Qed.
#[local] Notation MS M := (wbytes M (Z_to_bv 64 p) (repeat (cbyte cv) (Z.to_nat n))) (only parsing).
#[using="f l Hn Happ Hs Hdisj"] Lemma slots_ok_ms : ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "Q1&Q7y5'T1yR0%211%5241'8y8%611%311p061&QHr2r1%3221r3&Q=&T0vS=%22@1&B&R1vS0%211&RLvS<%211%73C41%<3@91%B2>1p0@1pRBE1pW@K1").
Proof.
intros regs0 M R. pose proof p_facts as (Pp & Ppn & _). unfold HIGHEND in *.
apply (slots_ok_ext regs0 M); [|exact R]. intros x Hx. pose proof (u64_range x).
destruct (Z_lt_le_dec 0 n) as [Np|Nz]; [| first [ rewrite (proj1 (length_zero_iff_nil bs) ltac:(lia)); reflexivity | replace (Z.to_nat n) with 0%nat by lia; reflexivity ] ].
destruct (Hdisj Np) as [Hd|Hd].
- apply wbytes_above. rewrite repeat_length. unorm. lia.
- apply wbytes_below; [rewrite repeat_length; unorm; lia | unorm; lia].
Qed.
Section SE.
Local Abbreviation SEC_T_c3_run := (ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "SB&Q7y5'T1yR0%211%5241'8y8%611%311p061&QCr2%211&Q@r4%2214'@'>'Q>&R?&R4vS3r5(SO+^niH(=%33H21/01HvSI%95872?1r1vSC&Q=&T0vS=%22Q11&B&R1vS0%211&RLvS<%211%73Q441%<3N91%I5H?>1A%L3KA1'?&R3+:%K3QB1I%32E1%53QA1A+2%O3QF1M%72I1vSN%:3QF21+1%Q43QK1Q2%<2N1%>3QJ1N+8%Q83QO1Q6%@2Q21r6%B213%D3R031+9%Q>3R51Q<%F2Q81%G262%I3R521+B%QC3R:1QA%K2Q=1%L2;2%N3R:21+C%QH3R?1QF%Q02QB1%Q12@2%Q33R?21+D%QM3RD1QK%Q52QG1%Q62E2%Q83RD21+E%R23RI1R0%Q:2QL1%Q;2J2%Q=3RI21&QO&QI%231R9R1%R?241%R@2:1%RA2@1%RB2F1%RC2L1%RD2Q21%RE2Q91%RF2Q>1%RG2QD1%RH2QK1qW>S61%RK2S71p0RM1p0S11pRBS51pW<S;1pW@S<1")) (only parsing).
Variable regs0 : ltac:(sec_ty2 constr:(SEC_T_c3_run) 0%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_c3_run) 1%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_c3_run) 2%nat 0%nat).
Lemma c3_run : ltac:(sec_stmt2 constr:(SEC_T_c3_run) 3%nat 0%nat).
Proof using kL f l fa la Hs_def Hn Happ Hs Hdisj Hdst Hret HG HI HkL HW regs0 regs M.
intros (H10 & H11 & H12 & H2) (HO & HGr & HR).
pose proof p_facts as (Pp & Ppn & _). unfold HIGHEND in *.
pose proof (out_agree_globs M HO) as (_ & (I1 & I2 & I3)).
assert (S1 : exists r1, msteps ASEGS (mkst regs (0x77b38 : word) M rom) (mkst r1 (0x126be8 : word) M rom)
/\ (getr r1 10 = Z_to_bv 64 p /\ getr r1 11 = cv /\ getr r1 12 = Z_to_bv 64 n /\ getr r1 1 = (0x77b44 : word)
/\ getr r1 2 = Z_to_bv 64 (s - 2128) /\ keeps_but RIPL regs r1)).
{ eexists. split.
- stepn (ltac:(oF' 0x77b38%Z)) (ltac:(oD' 0x77b38%Z)).
mld (ltac:(oF' 0x77b3c%Z)) (ltac:(oD' 0x77b3c%Z)) (0x1363b0 : word) I3.
stepjr (ltac:(oF' 0x77b40%Z)) (ltac:(oD' 0x77b40%Z)) (Z_to_bv 64 0x126be8) ltac:(gres; reflexivity).
vnorm. apply mst_refl.
- repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q12 & Q1 & Q2 & K1).
replace (0x126be8 : word) with (Z_to_bv 64 ms_base) in RUN1 by (apply bv_eq; vm_compute; reflexivity).
pose proof (memset_summary M (Z_to_bv 64 p) cv (0x77b44 : word) n rom ltac:(lia) ltac:(unorm; lia)
ltac:(apply (store_ok_mono _ _ mem0 M _ HGr); exact Hdst) ret_ok_77b44 r1 Q10 Q11 Q12 Q1) as (r2 & RUN2 & V10 & AG).
pose proof (slots_ok_ms regs0 M HR) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
assert (V2 : getr r2 2 = Z_to_bv 64 (s - 2128)) by (rewrite (ms_agree_getr _ _ 2%bv AG) by (cbv; intuition discriminate); exact Q2).
assert (V1 : getr r2 1 = (0x77b44 : word)) by (rewrite (ms_agree_getr _ _ 1%bv AG) by (cbv; intuition discriminate); exact Q1).
eexists. split.
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
stepiv (ltac:(oF' 0x77b44%Z)) (ltac:(oD' 0x77b44%Z)) (Z_to_bv 64 (s - 2032)) ltac:(wval).
stepld (ltac:(oF' 0x77b48%Z)) (ltac:(oD' 0x77b48%Z)) ra ltac:(maddr (s - 8)%Z; exact R1).
stepld (ltac:(oF' 0x77b4c%Z)) (ltac:(oD' 0x77b4c%Z)) (getr regs0 8) ltac:(maddr (s - 16)%Z; exact R2).
stepld (ltac:(oF' 0x77b50%Z)) (ltac:(oD' 0x77b50%Z)) (getr regs0 9) ltac:(maddr (s - 24)%Z; exact R3).
stepld (ltac:(oF' 0x77b54%Z)) (ltac:(oD' 0x77b54%Z)) (getr regs0 18) ltac:(maddr (s - 32)%Z; exact R4).
stepld (ltac:(oF' 0x77b58%Z)) (ltac:(oD' 0x77b58%Z)) (getr regs0 19) ltac:(maddr (s - 40)%Z; exact R5).
stepld (ltac:(oF' 0x77b5c%Z)) (ltac:(oD' 0x77b5c%Z)) (getr regs0 20) ltac:(maddr (s - 48)%Z; exact R6).
stepld (ltac:(oF' 0x77b60%Z)) (ltac:(oD' 0x77b60%Z)) (getr regs0 21) ltac:(maddr (s - 56)%Z; exact R7).
stepiv (ltac:(oF' 0x77b64%Z)) (ltac:(oD' 0x77b64%Z)) (Z_to_bv 64 s) ltac:(wval).
stepret (ltac:(oF' 0x77b68%Z)) (ltac:(oD' 0x77b68%Z)) ra ltac:(rwH; reflexivity).
apply mst_refl.
- repeat split; gres; try reflexivity; [exact V10 | symmetry; apply sp_s |].
eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [apply keeps_but_ms; exact AG|]. solve_keeps_but.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_asan_memset_run := (ltac2:(TCodec.tc2 tcn__Jb0AsanMemset "S3&Q7y5'T1yR0%211%5241'?&R3r1(SO+:(=%33;21%6251&T0vS=%22=1%;3=41r2+;%;3C19%>231vS0%A3C21r3+<%A3I1?%D231vS<%?2J1%H3J31r4+2%H3Q01F%K231vSN%N3Q021r5+1%N3Q61L%Q1231vSC%Q43Q621'@'8y8%Q<11%311p0Q<1'>'Q>&R?&R4vS3r8+^ne8%Q?3QE1Q=/01QEvS;vSI%8576321&Q=&B&R1%11Q:&RL%11Q6%53E31%73QLQD1%A5@QCL1:%D3C:1%R02QEQK%R23R41QH%R22QGQ8%R43R61Q7%R42QIQ4%R63R81Q3&R=%12HQL&QE%11R8&R>%12HR:%Q2231%Q3261%Q4291%Q52<1%Q62?1%Q72B1qRJQ91%Q?2Q:1qW>RF1%QA2RG1p0QC1p0QJ1p0R11p0R91p0R@1pW<RM1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_asan_memset_run) 0%nat 0%nat).
Theorem asan_memset_run : ltac:(sec_stmt2 constr:(SEC_T_asan_memset_run) 1%nat 0%nat).
Proof using kL f l fa la Hs_def Hf_def Hl_def Hfa_def Hla_def Hn Happ Hs Hshs Hdisj Hok Hdst Hret HG HI HZ HL HkL HW regs.
intros H10 H11 H12 H2 H1.
destruct (c1_run regs H10 H11 H12 H2 H1) as (r1 & RUN1 & P1 & K1).
destruct (c2_run regs r1 P1) as (r2 & M2 & RUN2 & P2 & K2 & F2).
destruct (c3_run regs r2 M2 P2 F2) as (r3 & RUN3 & Q10 & Q2 & Q1 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & K3).
exists r3, M2. split.
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
- assert (KB : keeps_but RIPL regs r3).
{ eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [exact K2|]. exact K3. }
destruct F2 as (HO & HGr & _).
repeat split; try assumption.
intros r Hr. destruct (decide (r = 1%bv)) as [->|N1]; [rewrite Q1, H1; reflexivity|].
destruct (decide (r = 2%bv)) as [->|N2]; [rewrite Q2, H2; reflexivity|].
destruct (decide (r = 8%bv)) as [->|N8]; [exact Q8|]. destruct (decide (r = 9%bv)) as [->|N9]; [exact Q9|].
destruct (decide (r = 18%bv)) as [->|N18]; [exact Q18|]. destruct (decide (r = 19%bv)) as [->|N19]; [exact Q19|].
destruct (decide (r = 20%bv)) as [->|N20]; [exact Q20|]. destruct (decide (r = 21%bv)) as [->|N21]; [exact Q21|].
apply KB; [exact Hr|]. cbv. intuition congruence.
Qed.
End SE.
End AMS.
End FPX_1.
