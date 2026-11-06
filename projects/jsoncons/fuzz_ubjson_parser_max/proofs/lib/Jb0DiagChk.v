(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib MemSplit As0StepLib Jb0MemIsZero Jb0RegionPoisoned Jb0AsanMemset Jb0AsanMemcpy Jb0DiagStrlen.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Jb0DiagChk () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DiagChk.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DiagChk.FPX_1.CHK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0RegionPoisoned."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1cons"; "1list"; "1nat"; "1nil"; "1option"; "2I"; "2and"; "2eq"; "2ex"; "3repeat"; "4Z"; "5word_to_le_bytes"; "6bvmap"; "0M"; "0M'"]; ["0N"; "7msteps"; "8ret_ok"; ":frame72"; "9chk_pre"; "9frame72"; ";HIGHEND"; ";SB"; ";keeps_but"; "<getr"; "<mkst"; "<rdn"; "=keeps_cs"; ">loaded_segments"; "?add"; "?div"]; ["?le"; "?lt"; "?of_nat"; "?pow"; "?sub"; "0a"; "0fS"; "0faS"; "0fx"; "0i"; "0lS"; "0laS"; "0m"; "0maxlen"; "0n"; "0p"]; ["0ra"; "0regs"; "0regs'"; "0rom"; "0s"; "@BV"; "@Z_to_bv"; "@bv"; "@bv_unsigned"]]).
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
#[local] Ltac xval := gres; rwH; unfold v_xori; imm_norm; unorm; rewrite lxor_ones64 by lia; first [reflexivity | f_equal; lia].
#[local] Ltac aval := gres; rwH; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; f_equal; lia.
Lemma rdn_zeros : ltac2:(TCodec.tc2 tcn__Jb0DiagChk "QN'QGyR0%211'5y8%511%311p051'3&Q0&N&QHr1%22<1&Q2r2%211%7241&Q3+2+R0%3221%=251';'7z%A21>&Q1r4%?11%32B1%7251'8r6&QF%H2Q27%J21E%32Q41%511(0%62Q4?%22Q41%:3Q441p0<1pRDE1'2%11Q9%Q<11&K&Mr5r3%44321H&:%13QA>J%@291%H3941p0=1p0Q41pR<QI1pRNQD1pRJQF1").
Proof.
intros m n; induction n as [|n IH]; intros a Hnw Hall; [reflexivity|].
cbn [rdn repeat].
pose proof (Hall 0%Z ltac:(lia)) as H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. rewrite H0.
destruct n as [|n'].
- reflexivity.
- assert (Hu1 : bv_unsigned (a + 1)%bv = (bv_unsigned a + 1)%Z).
{ rewrite bv_add_unsigned. change (bv_unsigned (1 : word)) with 1%Z. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
pose proof (u64_range a). apply Z.mod_small. lia. }
rewrite (IH (a + 1)%bv); [reflexivity | rewrite Hu1; lia |].
intros i Hi. rewrite Hu1. replace (bv_unsigned a + 1 + i)%Z with (bv_unsigned a + (1 + i))%Z by lia. apply Hall. lia.
Qed.
#[local] Ltac maddr z := match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 z) by (symmetry; wval) end.
#[local] Ltac mldw F D z R w :=
chain_step; [reflexivity
| eapply step_ld with (bs := w) (v := Z_to_bv 64 (bytes_le_to_Z w)); [exact F | reflexivity | exact D | maddr z; exact R | unorm; reflexivity]
| step_simpl; vnorm].
Section CHK.
Variable M rom : word -> option byte.
Variables p N s : Z.
Hypothesis HN : (0 < N <= 2 ^ 40)%Z.
Hypothesis Happ : in_app8 p N.
Hypothesis Hp0 : (0 < p)%Z.
Hypothesis Hs : (0x1000000 <= s - 72)%Z /\ (s < 2 ^ 64)%Z.
Hypothesis Hsh : (SB + (p + N - 1) / 8 + 8 <= s - 72)%Z.
Hypothesis Hok : store_ok ASEGS M (Z_to_bv 64 (s - 72)) 72%nat = true.
Hypothesis HG : rt_layout_globs M.
Hypothesis HZ : forall x : word, (SB + p / 8 - 7 <= bv_unsigned x < Z.min (SB + (p + N - 1) / 8 + 8) (SB + 2 ^ 44))%Z -> M x = Some (Z_to_bv 8 0).
Variables fS lS faS laS : Z.
Hypothesis HfS_def : fS = (SB + p / 8)%Z. Hypothesis HlS_def : lS = (SB + (p + N - 1) / 8)%Z.
Hypothesis HfaS_def : faS = (fS - fS mod 8)%Z. Hypothesis HlaS_def : laS = (lS - lS mod 8)%Z.
Lemma p_facts : ltac2:(TCodec.tc2 tcn__Jb0DiagChk "Q0'7&Q0zvQ?%3221&Nv@%2241+8%4221&F%:221&O%12:5%=2<1%>225%@221&Q4+1%22<1%821<%D281&Q3+2+Q<%3221%9218%J271%L271%M2=1%N2C1%O2K1").
Proof.
unfold in_app8, LOWEND, HIGHBEG, HIGHEND in *. destruct Happ as [[H1 H2]|[H1 H2]];
(repeat split; [lia | lia | apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia | apply Z.div_le_mono; lia | apply Z.div_le_upper_bound; lia]).
Qed.
Lemma fl_facts : ltac2:(TCodec.tc2 tcn__Jb0DiagChk "Q9'7&Q0&GvQ6%3221vQ:%5231%7231&Q4+7%2271vQ7%;221%<22:%>221%72:6vQ;%@221%A22=%C221&N+8%22A1vQD+R8%A221%I241%72@6&Q3+2+Q<%3221%<2N1%Q0261%>2B=%Q2213%Q4231%Q52;1%Q62C1%Q72I1%Q82Q11").
Proof.
pose proof p_facts as (Pp & Ppn & Pp8 & Pq). unfold SB, HIGHEND in *.
pose proof (Z.mod_pos_bound fS 8 ltac:(lia)). pose proof (Z.mod_pos_bound lS 8 ltac:(lia)).
pose proof (Z.div_mod fS 8 ltac:(lia)). pose proof (Z.div_mod lS 8 ltac:(lia)). repeat split; lia.
Qed.
Lemma zero_word : ltac2:(TCodec.tc2 tcn__Jb0DiagChk "QB';&Q0&Q4vQ6+7%3221r1%6221r2vQ:%9221&Nr3+8%3221&G&Q3+2+Q<%3221%9251%D271'8'5'2'QGy8%211%411%611&K&Mv>&QFyR0r4%3221u8%847621(0&:z%92@1%33@16%52@1%G3@71p0I1p0Q51p0Q91pR<QA1").
Proof.
intros a Ha Hb Hc. pose proof fl_facts as (F1 & _ & _ & F5). pose proof p_facts as (Pp & Ppn & Pp8 & Pq). unfold SB, HIGHEND in *.
apply rdn_zeros; [unorm; cbn; lia|].
intros i Hi. unorm. apply HZ. unfold SB. cbn in Hi. unorm. lia.
Qed.
Lemma ret_ok_66ec0 : ltac2:(TCodec.tc2 tcn__Jb0DiagChk ":&B(QEyR0+\kf0(6%43321'QG%115/031%911"). Proof. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_chk1_fast := (ltac2:(TCodec.tc2 tcn__Jb0DiagChk "R2&=y5'QGyR0%211%5241&Q0v@+R0%3221'8&Ir2(QE+:(6%33?21%6251&QF&Q4+1%22>1%42C1%=3C61r3+F%=3I1;%@231vQ?%;2J1%D3J31'9'7'A&M&JvQ8r5+\ka<%J3Q41H/01Q4v>vQC%8576321r1+\k\<%Q13Q;1O/01Q;%=5<4176%@3?61&H(1%QB1QC+G%Q93QE1Q7(4%114%63531%831E>%K2:1qS6QG1%N2QH1p0Q01p0Q81p0QG1pS4QL1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_chk1_fast) 0%nat 0%nat).
Lemma chk1_fast : ltac:(sec_stmt2 constr:(SEC_T_chk1_fast) 1%nat 0%nat).
Proof.
intros Hn64 H10 H22.
pose proof p_facts as (Pp & Ppn & Pp8 & Pq). pose proof fl_facts as (F1 & F3 & F4 & F5).
destruct HG as (G1 & G2 & _).
unfold SB, HIGHEND in *.
pose proof (zero_word faS ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) as R0. pose proof (zero_word laS ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) as R1.
eexists. split.
- stepiv (ltac:(oF' 0x66e2c%Z)) (ltac:(oD' 0x66e2c%Z)) (Z_to_bv 64 N) ltac:(wval).
stepiv (ltac:(oF' 0x66e30%Z)) (ltac:(oD' 0x66e30%Z)) (Z_to_bv 64 (2 ^ 64 - 1 - p)) ltac:(xval).
stepb_ft (ltac:(oF' 0x66e34%Z)) (ltac:(oD' 0x66e34%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x66e38%Z)) (ltac:(oD' 0x66e38%Z)) (Z_to_bv 64 (2 ^ 64 + N - 65)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; rewrite (zbv_wrap_up (N + - 65)); f_equal; lia).
stepn (ltac:(oF' 0x66e3c%Z)) (ltac:(oD' 0x66e3c%Z)).
stepb_ft (ltac:(oF' 0x66e40%Z)) (ltac:(oD' 0x66e40%Z)) ltac:(cond).
stepn (ltac:(oF' 0x66e44%Z)) (ltac:(oD' 0x66e44%Z)).
mld (ltac:(oF' 0x66e48%Z)) (ltac:(oD' 0x66e48%Z)) (0x1343a0 : word) G1.
stepiv (ltac:(oF' 0x66e4c%Z)) (ltac:(oD' 0x66e4c%Z)) (Z_to_bv 64 (p + N)) ltac:(wval).
mld (ltac:(oF' 0x66e50%Z)) (ltac:(oD' 0x66e50%Z)) (0x13ca38 : word) G2.
stepiv (ltac:(oF' 0x66e54%Z)) (ltac:(oD' 0x66e54%Z)) (Z_to_bv 64 (p / 8)) ltac:(wval).
stepiv (ltac:(oF' 0x66e58%Z)) (ltac:(oD' 0x66e58%Z)) (Z_to_bv 64 (p + N - 1)) ltac:(wval).
stepiv (ltac:(oF' 0x66e5c%Z)) (ltac:(oD' 0x66e5c%Z)) (Z_to_bv 64 ((p + N - 1) / 8)) ltac:(wval).
stepiv (ltac:(oF' 0x66e60%Z)) (ltac:(oD' 0x66e60%Z)) (Z_to_bv 64 fS) ltac:(wval).
stepiv (ltac:(oF' 0x66e64%Z)) (ltac:(oD' 0x66e64%Z)) (Z_to_bv 64 lS) ltac:(wval).
stepiv (ltac:(oF' 0x66e68%Z)) (ltac:(oD' 0x66e68%Z)) (Z_to_bv 64 faS) ltac:(aval).
stepiv (ltac:(oF' 0x66e6c%Z)) (ltac:(oD' 0x66e6c%Z)) (Z_to_bv 64 laS) ltac:(aval).
mldw (ltac:(oF' 0x66e70%Z)) (ltac:(oD' 0x66e70%Z)) faS R0 (repeat (Z_to_bv 8 0 : byte) 8).
mldw (ltac:(oF' 0x66e74%Z)) (ltac:(oD' 0x66e74%Z)) laS R1 (repeat (Z_to_bv 8 0 : byte) 8).
stepov (ltac:(oF' 0x66e78%Z)) (ltac:(oD' 0x66e78%Z)) (Z_to_bv 64 0) ltac:(gres; rwH; reflexivity).
stepb_tk (ltac:(oF' 0x66e7c%Z)) (ltac:(oD' 0x66e7c%Z)) ltac:(cond).
apply mst_refl.
- solve_keeps_but.
Qed.
End SE.
Definition frame72 (M' : word -> option byte) : Prop :=
(forall x : word, (bv_unsigned x < s - 72 \/ s <= bv_unsigned x)%Z -> M' x = M x) /\ mem_grows M M'.
Lemma frame72_refl : ltac2:(TCodec.tc2 tcn__Jb0DiagChk "3&Cv>%211"). Proof. split; [intros x _; reflexivity | apply mem_grows_refl]. Qed.
Section SE.
Local Abbreviation SEC_T_region_call := (ltac2:(TCodec.tc2 tcn__Jb0DiagChk "RH&=y5'QGyR0%211%5241&Q1+R0v@%3221&Br2%211'8&Ir4(QE+:(6%33B21%6251&QFvQ?%22D1%;3D41r5+;%;3J19%>231%82JE%A3J21r6+2%A3Q01?%D231vQD%?2Q11%H3Q131r7+1%H3Q71F%K231%M3Q61;'9'5y8%Q<11%311p0Q<1'7'A&M&JvQ8r:+_[aH%Q83QE1Q6/01QEv>vQC%8576321r9r1%;5:QD214%>3=41%QC2QFQ>z%Q>2R01%QG3R031&L%12@QK&C%11:%H231%I261%J2;1qQ0L1%Q22M1qS6R91%Q42R:1p0Q61p0Q<1p0QD1p0QK1p0R81p0R<1pS2RB1pS4RB1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_region_call) 0%nat 0%nat).
Variable ra : ltac:(sec_ty2 constr:(SEC_T_region_call) 1%nat 0%nat).
Lemma region_call : ltac:(sec_stmt2 constr:(SEC_T_region_call) 2%nat 0%nat).
Proof.
intros Hn64 Hret H10 H11 H2 H1.
pose proof p_facts as (Pp & Ppn & Pp8 & Pq). pose proof fl_facts as (F1 & F3 & F4 & F5). unfold SB, HIGHEND in *.
destruct (region_is_poisoned_run M rom (Z_to_bv 64 s) ra p N s ltac:(unorm; reflexivity) HN Happ Hs ltac:(unfold SB; lia) Hok Hret HG 0%Z
ltac:(intros x Hx; apply HZ; unfold SB in *; lia)
ltac:(apply HZ; unfold SB in *; unorm; lia)
ltac:(left; reflexivity) regs H10 H11 H2 H1) as (r2 & M2 & RUN & V10 & V2 & V1 & K2 & FO & GR).
exists r2, M2. split; [exact RUN | split; [exact V10 | split; [exact K2 | split; [exact FO | exact GR]]]].
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_chk1_region := (ltac2:(TCodec.tc2 tcn__Jb0DiagChk "RF&=y5'QGyR0%211%5241&Q1+R0v@%3221'8&Ir2(QE+:(6%33?21%6251&QF&Q4+1%22=1%42C1%=3C61r3+F%=3I1;%@231vQ?%;2J1%D3J31r4+2%D3Q01B%G231vQD%B2Q11%K3Q131'9'5y8%Q711%311p0Q71'7'A&M&JvQ8r7+\ka<%Q63Q@1Q4/01Q@v>vQC%8576321+\k\<%Q<3QF1Q:/01QFr1%=5<Q@216%@3?61&H(1%QN1QO%QD3R0Q=QB+G%QF3R21QD(4%115%73631%83761%:31GQL&C%11?%O231%Q02?1qQ0Q21%Q82Q31qS6R:1%Q:2R;1p0Q<1p0QD1p0QL1p0R;1pS4R@1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_chk1_region) 0%nat 0%nat).
Lemma chk1_region : ltac:(sec_stmt2 constr:(SEC_T_chk1_region) 1%nat 0%nat).
Proof.
intros Hn64 H10 H22 H2.
pose proof p_facts as (Pp & Ppn & Pp8 & Pq). unfold SB, HIGHEND in *.
assert (S1 : exists r1, msteps ASEGS (mkst regs (0x66e2c : word) M rom) (mkst r1 (0x7ae38 : word) M rom)
/\ (getr r1 10 = Z_to_bv 64 p /\ getr r1 11 = Z_to_bv 64 N /\ getr r1 2 = Z_to_bv 64 s /\ getr r1 1 = (0x66ec0 : word) /\ keeps_but [1; 23]%bv regs r1)).
{ eexists. split.
- stepiv (ltac:(oF' 0x66e2c%Z)) (ltac:(oD' 0x66e2c%Z)) (Z_to_bv 64 N) ltac:(wval).
stepiv (ltac:(oF' 0x66e30%Z)) (ltac:(oD' 0x66e30%Z)) (Z_to_bv 64 (2 ^ 64 - 1 - p)) ltac:(xval).
stepb_ft (ltac:(oF' 0x66e34%Z)) (ltac:(oD' 0x66e34%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x66e38%Z)) (ltac:(oD' 0x66e38%Z)) (Z_to_bv 64 (N - 65)) ltac:(wval).
stepn (ltac:(oF' 0x66e3c%Z)) (ltac:(oD' 0x66e3c%Z)).
stepb_tk (ltac:(oF' 0x66e40%Z)) (ltac:(oD' 0x66e40%Z)) ltac:(cond).
stepb_tk (ltac:(oF' 0x67100%Z)) (ltac:(oD' 0x67100%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x66eb4%Z)) (ltac:(oD' 0x66eb4%Z)) (Z_to_bv 64 p) ltac:(wval).
stepiv (ltac:(oF' 0x66eb8%Z)) (ltac:(oD' 0x66eb8%Z)) (Z_to_bv 64 N) ltac:(wval).
stepn (ltac:(oF' 0x66ebc%Z)) (ltac:(oD' 0x66ebc%Z)).
apply mst_refl.
- repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q2 & Q1 & K1).
destruct (region_call r1 (0x66ec0 : word) Hn64 ret_ok_66ec0 Q10 Q11 Q2 Q1) as (r2 & M2 & RUN2 & V10 & K2 & FR2).
eexists. exists M2. split; [|split; [|exact FR2]].
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
stepb_tk (ltac:(oF' 0x66ec0%Z)) (ltac:(oD' 0x66ec0%Z)) ltac:(cond).
apply mst_refl.
- eapply keeps_but_trans; [exact K1|]. solve_keeps_but.
Qed.
End SE.
Theorem chk1_run : ltac2:(TCodec.tc2 tcn__Jb0DiagChk "RA&=y5'QGyR0%211%5241'8&Ir1(QE+:(6%33;21%6251&QF&Q4v@+1%3221%52@1%>3@71r2+F%>3F1<%A231vQ?%<2G1%E3G31r3+2%E3M1C%H231vQD%C2N1%L3N31'9'5y8%Q411%311p0Q41'7'A&M&JvQ8r6+\ka<%Q73Q=1Q5/01Q=v>vQC%8576321+\k\<%Q=3QC1Q;/01QC%<5;Q31Q@5%?3>51&H(1%QJ1QK%QD3QLQ<QB+G%QF3QN1QD(4%115%73631%83761%:31FQ?&C%11QN%N231%O2?1qQ0Q11%Q72Q21qS6R61%Q92R71p0Q;1p0QC1p0QK1pS4R;1").
Proof.
intros regs H10 H22 H2. destruct (Z_le_gt_dec N 64) as [Hle|Hgt].
- destruct (chk1_fast regs Hle H10 H22) as (r & RUN & K). exists r, M. split; [exact RUN | split; [|exact frame72_refl]].
intros x Hx Hn. apply K; [exact Hx|]. intros [E|[]]. apply Hn. right. left. exact E.
- apply chk1_region; [lia | assumption..].
Qed.
Lemma ret_ok_64b90 : ltac2:(TCodec.tc2 tcn__Jb0DiagChk ":&B(QEyR0+\bl@(6%43321'QG%115/031%911"). Proof. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_chk2_fast := (ltac2:(TCodec.tc2 tcn__Jb0DiagChk "R?&=y5'QGyR0%211%5241&Q0v@+R0%3221'8&Ir2(QE+:(6%33?21%6251&QF&Q4&NvQ?%221?+1%5221%72F1%@3F91r3+B%@3L1>%C231%=2L:%F3L21r4+D%F3Q21D%I231%C2Q2>%L3Q221'9'7'A&M&JvQ8r6+\b_H%Q23Q<1Q0/01Q<v>vQC%8576321r1+\bbH%Q93QC1Q7/01QC%=5<4176%@3?61%Q?26Q:%QA3QG1Q2&H(1%QL1QM+9%QC3QO1QA(4%114%635Q01%73641%931HA%N2;1%O2>1qS6R31%Q22R41p0Q41p0Q;1p0QB1p0R41pS4R91")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_chk2_fast) 0%nat 0%nat).
Lemma chk2_fast : ltac:(sec_stmt2 constr:(SEC_T_chk2_fast) 1%nat 0%nat).
Proof.
intros Hn64 H10 H18 H20.
pose proof p_facts as (Pp & Ppn & Pp8 & Pq). pose proof fl_facts as (F1 & F3 & F4 & F5).
destruct HG as (G1 & G2 & _).
unfold SB, HIGHEND in *.
pose proof (zero_word faS ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) as R0. pose proof (zero_word laS ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) as R1.
eexists. split.
- stepb_ft (ltac:(oF' 0x649f8%Z)) (ltac:(oD' 0x649f8%Z)) ltac:(cond).
stepb_tk (ltac:(oF' 0x649fc%Z)) (ltac:(oD' 0x649fc%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x64ab4%Z)) (ltac:(oD' 0x64ab4%Z)) (Z_to_bv 64 (N - 1)) ltac:(wval).
stepiv (ltac:(oF' 0x64ab8%Z)) (ltac:(oD' 0x64ab8%Z)) (Z_to_bv 64 N) ltac:(wval).
stepiv (ltac:(oF' 0x64abc%Z)) (ltac:(oD' 0x64abc%Z)) (Z_to_bv 64 (2 ^ 64 - 1 - p)) ltac:(xval).
stepn (ltac:(oF' 0x64ac0%Z)) (ltac:(oD' 0x64ac0%Z)).
stepn (ltac:(oF' 0x64ac4%Z)) (ltac:(oD' 0x64ac4%Z)).
stepb_tk (ltac:(oF' 0x64ac8%Z)) (ltac:(oD' 0x64ac8%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x64a10%Z)) (ltac:(oD' 0x64a10%Z)) (Z_to_bv 64 (2 ^ 64 + N - 65)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; rewrite (zbv_wrap_up (N + - 65)); f_equal; lia).
stepn (ltac:(oF' 0x64a14%Z)) (ltac:(oD' 0x64a14%Z)).
stepb_ft (ltac:(oF' 0x64a18%Z)) (ltac:(oD' 0x64a18%Z)) ltac:(cond).
stepn (ltac:(oF' 0x64a1c%Z)) (ltac:(oD' 0x64a1c%Z)).
mld (ltac:(oF' 0x64a20%Z)) (ltac:(oD' 0x64a20%Z)) (0x1343a0 : word) G1.
stepiv (ltac:(oF' 0x64a24%Z)) (ltac:(oD' 0x64a24%Z)) (Z_to_bv 64 (p + N)) ltac:(wval).
mld (ltac:(oF' 0x64a28%Z)) (ltac:(oD' 0x64a28%Z)) (0x13ca38 : word) G2.
stepiv (ltac:(oF' 0x64a2c%Z)) (ltac:(oD' 0x64a2c%Z)) (Z_to_bv 64 (p / 8)) ltac:(wval).
stepiv (ltac:(oF' 0x64a30%Z)) (ltac:(oD' 0x64a30%Z)) (Z_to_bv 64 (p + N - 1)) ltac:(wval).
stepiv (ltac:(oF' 0x64a34%Z)) (ltac:(oD' 0x64a34%Z)) (Z_to_bv 64 ((p + N - 1) / 8)) ltac:(wval).
stepiv (ltac:(oF' 0x64a38%Z)) (ltac:(oD' 0x64a38%Z)) (Z_to_bv 64 fS) ltac:(wval).
stepiv (ltac:(oF' 0x64a3c%Z)) (ltac:(oD' 0x64a3c%Z)) (Z_to_bv 64 lS) ltac:(wval).
stepiv (ltac:(oF' 0x64a40%Z)) (ltac:(oD' 0x64a40%Z)) (Z_to_bv 64 faS) ltac:(aval).
stepiv (ltac:(oF' 0x64a44%Z)) (ltac:(oD' 0x64a44%Z)) (Z_to_bv 64 laS) ltac:(aval).
mldw (ltac:(oF' 0x64a48%Z)) (ltac:(oD' 0x64a48%Z)) faS R0 (repeat (Z_to_bv 8 0 : byte) 8).
mldw (ltac:(oF' 0x64a4c%Z)) (ltac:(oD' 0x64a4c%Z)) laS R1 (repeat (Z_to_bv 8 0 : byte) 8).
stepov (ltac:(oF' 0x64a50%Z)) (ltac:(oD' 0x64a50%Z)) (Z_to_bv 64 0) ltac:(gres; rwH; reflexivity).
stepb_ft (ltac:(oF' 0x64a54%Z)) (ltac:(oD' 0x64a54%Z)) ltac:(cond).
apply mst_refl.
- split; [gres; rwH; reflexivity | solve_keeps_but].
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_chk2_region := (ltac2:(TCodec.tc2 tcn__Jb0DiagChk "S5&=y5'QGyR0%211%5241&Q1+R0v@%3221'8&Ir2(QE+:(6%33?21%6251&QF&Q4&NvQ?%221>+1%5221%72F1%@3F91r3+B%@3L1>%C231%=2L:%F3L21r4+D%F3Q21D%I231%C2Q2>%L3Q221r5+2%L3Q81J%O231vQD%J2Q91%Q33Q931'9'5y8%Q?11%311p0Q?1'7'A&M&JvQ8r8+\b_H%Q>3QH1Q</01QHv>vQC%8576321+\bbH%QD3QN1QB/01QNr1%=5<QH216%@3?61&H(1%R61R7%QL3R8QBQJ+9%QN3R:1QL+E%R03R<1QN(4%117%93831%:39Q>1%;3:QE1%<3;81%=3<;1%?31LR9&C%11D%Q4231%Q52QO1%Q62E1qQ0Q81%Q>2Q91qS6RH1%Q@2RI1p0QB1p0QJ1p0R11p0R81p0RJ1pS4RO1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_chk2_region) 0%nat 0%nat).
Lemma chk2_region : ltac:(sec_stmt2 constr:(SEC_T_chk2_region) 1%nat 0%nat).
Proof.
intros Hn64 H10 H18 H20 H2.
pose proof p_facts as (Pp & Ppn & Pp8 & Pq). unfold SB, HIGHEND in *.
assert (S1 : exists r1, msteps ASEGS (mkst regs (0x649f8 : word) M rom) (mkst r1 (0x7ae38 : word) M rom)
/\ (getr r1 10 = Z_to_bv 64 p /\ getr r1 11 = Z_to_bv 64 N /\ getr r1 2 = Z_to_bv 64 s /\ getr r1 1 = (0x64b90 : word)
/\ getr r1 21 = Z_to_bv 64 (p + N - 1) /\ keeps_but [1; 9; 18; 20; 21]%bv regs r1)).
{ eexists. split.
- stepb_ft (ltac:(oF' 0x649f8%Z)) (ltac:(oD' 0x649f8%Z)) ltac:(cond).
stepb_tk (ltac:(oF' 0x649fc%Z)) (ltac:(oD' 0x649fc%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x64ab4%Z)) (ltac:(oD' 0x64ab4%Z)) (Z_to_bv 64 (N - 1)) ltac:(wval).
stepiv (ltac:(oF' 0x64ab8%Z)) (ltac:(oD' 0x64ab8%Z)) (Z_to_bv 64 N) ltac:(wval).
stepiv (ltac:(oF' 0x64abc%Z)) (ltac:(oD' 0x64abc%Z)) (Z_to_bv 64 (2 ^ 64 - 1 - p)) ltac:(xval).
stepn (ltac:(oF' 0x64ac0%Z)) (ltac:(oD' 0x64ac0%Z)).
stepn (ltac:(oF' 0x64ac4%Z)) (ltac:(oD' 0x64ac4%Z)).
stepb_tk (ltac:(oF' 0x64ac8%Z)) (ltac:(oD' 0x64ac8%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x64a10%Z)) (ltac:(oD' 0x64a10%Z)) (Z_to_bv 64 (N - 65)) ltac:(wval).
stepn (ltac:(oF' 0x64a14%Z)) (ltac:(oD' 0x64a14%Z)).
stepb_tk (ltac:(oF' 0x64a18%Z)) (ltac:(oD' 0x64a18%Z)) ltac:(cond).
stepb_tk (ltac:(oF' 0x64b44%Z)) (ltac:(oD' 0x64b44%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x64b80%Z)) (ltac:(oD' 0x64b80%Z)) (Z_to_bv 64 (p + N - 1)) ltac:(wval).
stepiv (ltac:(oF' 0x64b84%Z)) (ltac:(oD' 0x64b84%Z)) (Z_to_bv 64 p) ltac:(wval).
stepiv (ltac:(oF' 0x64b88%Z)) (ltac:(oD' 0x64b88%Z)) (Z_to_bv 64 N) ltac:(wval).
stepn (ltac:(oF' 0x64b8c%Z)) (ltac:(oD' 0x64b8c%Z)).
apply mst_refl.
- repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q2 & Q1 & Q21 & K1).
destruct (region_call r1 (0x64b90 : word) Hn64 ret_ok_64b90 Q10 Q11 Q2 Q1) as (r2 & M2 & RUN2 & V10 & K2 & FR2).
assert (S21 : getr r2 21 = Z_to_bv 64 (p + N - 1)) by (rewrite (K2 21%bv) by (cbv; tauto); exact Q21).
eexists. exists M2. split; [|split; [|split; [|exact FR2]]].
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
stepiv (ltac:(oF' 0x64b90%Z)) (ltac:(oD' 0x64b90%Z)) (Z_to_bv 64 0) ltac:(wval).
stepiv (ltac:(oF' 0x64b94%Z)) (ltac:(oD' 0x64b94%Z)) (Z_to_bv 64 (p + N - 1)) ltac:(wval).
stepb_tk (ltac:(oF' 0x64b98%Z)) (ltac:(oD' 0x64b98%Z)) ltac:(cond).
apply mst_refl.
- gres; rwH; reflexivity.
- eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [apply keeps_but_cs; exact K2|]. solve_keeps_but.
Qed.
End SE.
Theorem chk2_run : ltac2:(TCodec.tc2 tcn__Jb0DiagChk "S2&=y5'QGyR0%211%5241'8&Ir1(QE+:(6%33;21%6251&QF&Q4&NvQ?v@%3221+1%6221%82C1%A3C:1r2+B%A3I1?%D231%>2I;%G3I21r3+D%G3O1E%J231%D2O>%M3O21r4+2%M3Q51K%Q0231vQD%K2Q61%Q43Q631'9'5y8%Q<11%311p0Q<1'7'A&M&JvQ8r7+\b_H%Q?3QE1Q=/01QEv>vQC%8576321+\bbH%QE3QK1QC/01QK%<5;Q81QH5%?3>51%QK2Q:QF%QM3QO1Q=&H(1%R41R5%QN3R6QCQL+9%R03R81QN+E%R23R:1R0(4%117%93831%:39Q?1%;3:QF1%<3;81%=3<;1%?31MQK&C%11R=%Q5231%Q62D1%Q72G1qQ0Q91%Q?2Q:1qS6RF1%QA2RG1p0QC1p0QK1p0R21p0R91pS4RL1").
Proof.
intros regs H10 H18 H20 H2. destruct (Z_le_gt_dec N 64) as [Hle|Hgt].
- destruct (chk2_fast regs Hle H10 H18 H20) as (r & RUN & V & K). exists r, M. split; [exact RUN | split; [exact V | split; [|exact frame72_refl]]].
intros x Hx Hn. apply K; [exact Hx|]. intros [E|[E|[]]]; apply Hn; subst x; cbv; tauto.
- apply chk2_region; [lia | assumption..].
Qed.
Lemma ret_ok_6321c : ltac2:(TCodec.tc2 tcn__Jb0DiagChk ":&B(QEyR0+\\`L(6%43321'QG%115/031%911"). Proof. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
Variable maxlen : Z.
Hypothesis Hmax : (N < maxlen < 2 ^ 63)%Z.
Hypothesis HFL : rdn ASEGS M (0x134390 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1ce568)).
Hypothesis HRS : rdn ASEGS M (0x1ce663 : word) 1%nat = Some [Z_to_bv 8 1].
Section SE.
Local Abbreviation SEC_T_chk3_head := (ltac2:(TCodec.tc2 tcn__Jb0DiagChk "RN&=y5'QGyR0%211%5241'8&Ir1(QE+:(6%33;21%6251&QF&Q4v@+1%3221%52@1%>3@71r2+9%>3F1<%A231%;2F8%D3F21r3+B%D3L1B%G231vQ?%B2M1%K3M31r4+C%K3Q31I%N231vQ=%I2Q41%Q23Q431'9'7'A&M&JvQ8r6+\\U<%Q83Q>1Q6/01Q>v>vQC%8576321+\\VH%Q>3QD1Q</01QD%<5;QA165%?3>51%QD2QCQ4%Q>2QIQ<%QG3QI21%QG2QFQ1%QI3QK1O+2%QH3R01QF%QK2QJ1%QL2D2%QN3R021&H(1%R51R6+D%R03R81QN+E%R23R:1R0(4%116%83731%93861%:39QI1%<31Q2R9%Q82>1%Q92D1%Q:2G1%Q;2R11%Q<2L1qS6RB1%Q?2RC1p0QA1p0QI1p0R11p0R81pS4RH1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_chk3_head) 0%nat 0%nat).
Lemma chk3_head : ltac:(sec_stmt2 constr:(SEC_T_chk3_head) 1%nat 0%nat).
Proof.
intros H10 H9 H18 H19.
pose proof p_facts as (Pp & Ppn & Pp8 & Pq). unfold SB, HIGHEND in *.
eexists. split.
- stepb_ft (ltac:(oF' 0x630ac%Z)) (ltac:(oD' 0x630ac%Z)) ltac:(cond).
stepn (ltac:(oF' 0x630b0%Z)) (ltac:(oD' 0x630b0%Z)).
mld (ltac:(oF' 0x630b4%Z)) (ltac:(oD' 0x630b4%Z)) (0x134390 : word) HFL.
mlbu (ltac:(oF' 0x630b8%Z)) (ltac:(oD' 0x630b8%Z)) (0x1ce663 : word) HRS.
stepb_ft (ltac:(oF' 0x630bc%Z)) (ltac:(oD' 0x630bc%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x630c0%Z)) (ltac:(oD' 0x630c0%Z)) (Z_to_bv 64 N) ltac:(wval).
stepb_ft (ltac:(oF' 0x630c4%Z)) (ltac:(oD' 0x630c4%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x630c8%Z)) (ltac:(oD' 0x630c8%Z)) (Z_to_bv 64 (2 ^ 64 - 1 - p)) ltac:(xval).
stepn (ltac:(oF' 0x630cc%Z)) (ltac:(oD' 0x630cc%Z)).
stepn (ltac:(oF' 0x630d0%Z)) (ltac:(oD' 0x630d0%Z)).
stepb_ft (ltac:(oF' 0x630d4%Z)) (ltac:(oD' 0x630d4%Z)) ltac:(cond).
apply mst_refl.
- repeat split; gres; rwH; try reflexivity. solve_keeps_but.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_chk3_fast := (ltac2:(TCodec.tc2 tcn__Jb0DiagChk "R8&=y5'QGyR0%211%5241&Q0v@+R0%3221'8&Ir2(QE+:(6%33?21%6251&QF&Q4+1%22>1%42C1%=3C61r3+9%=3I1;%@231%:2IE%C3I21r4+B%C3O1A%F231vQ?%A2Q01%J3Q031'9'7'A&M&JvQ8r6+\\VH%Q03Q:1N/01Q:v>vQC%8576321r1+\\Y0%Q73QA1Q5/01QA%=5<4176%@3?61%Q=26Q8%Q?3QE1Q3&H(4%QJ1QK%211%431C<%I261%J291qS6QL1%M2QM1p0O1p0Q71p0Q>1p0QM1pS4R21")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_chk3_fast) 0%nat 0%nat).
Lemma chk3_fast : ltac:(sec_stmt2 constr:(SEC_T_chk3_fast) 1%nat 0%nat).
Proof.
intros Hn64 H10 H9 H18.
pose proof p_facts as (Pp & Ppn & Pp8 & Pq). pose proof fl_facts as (F1 & F3 & F4 & F5).
destruct HG as (G1 & G2 & _).
unfold SB, HIGHEND in *.
pose proof (zero_word faS ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) as R0. pose proof (zero_word laS ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) as R1.
eexists. split.
- stepiv (ltac:(oF' 0x630d8%Z)) (ltac:(oD' 0x630d8%Z)) (Z_to_bv 64 (2 ^ 64 + N - 65)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; rewrite (zbv_wrap_up (N + - 65)); f_equal; lia).
stepn (ltac:(oF' 0x630dc%Z)) (ltac:(oD' 0x630dc%Z)).
stepb_ft (ltac:(oF' 0x630e0%Z)) (ltac:(oD' 0x630e0%Z)) ltac:(cond).
stepn (ltac:(oF' 0x630e4%Z)) (ltac:(oD' 0x630e4%Z)).
mld (ltac:(oF' 0x630e8%Z)) (ltac:(oD' 0x630e8%Z)) (0x1343a0 : word) G1.
stepiv (ltac:(oF' 0x630ec%Z)) (ltac:(oD' 0x630ec%Z)) (Z_to_bv 64 (p + N)) ltac:(wval).
mld (ltac:(oF' 0x630f0%Z)) (ltac:(oD' 0x630f0%Z)) (0x13ca38 : word) G2.
stepiv (ltac:(oF' 0x630f4%Z)) (ltac:(oD' 0x630f4%Z)) (Z_to_bv 64 (p / 8)) ltac:(wval).
stepiv (ltac:(oF' 0x630f8%Z)) (ltac:(oD' 0x630f8%Z)) (Z_to_bv 64 (p + N - 1)) ltac:(wval).
stepiv (ltac:(oF' 0x630fc%Z)) (ltac:(oD' 0x630fc%Z)) (Z_to_bv 64 ((p + N - 1) / 8)) ltac:(wval).
stepiv (ltac:(oF' 0x63100%Z)) (ltac:(oD' 0x63100%Z)) (Z_to_bv 64 fS) ltac:(wval).
stepiv (ltac:(oF' 0x63104%Z)) (ltac:(oD' 0x63104%Z)) (Z_to_bv 64 lS) ltac:(wval).
stepiv (ltac:(oF' 0x63108%Z)) (ltac:(oD' 0x63108%Z)) (Z_to_bv 64 faS) ltac:(aval).
stepiv (ltac:(oF' 0x6310c%Z)) (ltac:(oD' 0x6310c%Z)) (Z_to_bv 64 laS) ltac:(aval).
mldw (ltac:(oF' 0x63110%Z)) (ltac:(oD' 0x63110%Z)) faS R0 (repeat (Z_to_bv 8 0 : byte) 8).
mldw (ltac:(oF' 0x63114%Z)) (ltac:(oD' 0x63114%Z)) laS R1 (repeat (Z_to_bv 8 0 : byte) 8).
stepov (ltac:(oF' 0x63118%Z)) (ltac:(oD' 0x63118%Z)) (Z_to_bv 64 0) ltac:(gres; rwH; reflexivity).
stepb_ft (ltac:(oF' 0x6311c%Z)) (ltac:(oD' 0x6311c%Z)) ltac:(cond).
apply mst_refl.
- split; [gres; rwH; reflexivity | solve_keeps_but].
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_chk3_region := (ltac2:(TCodec.tc2 tcn__Jb0DiagChk "RO&=y5'QGyR0%211%5241&Q1+R0v@%3221'8&Ir2(QE+:(6%33?21%6251&QF&Q4+1%22=1%42C1%=3C61r3+9%=3I1;%@231%:2ID%C3I21r4+B%C3O1A%F231vQ?%A2Q01%J3Q031r5+2%J3Q61H%M231vQD%H2Q71%Q13Q731'9'5y8%Q=11%311p0Q=1'7'A&M&JvQ8r8+\\VH%Q<3QF1Q:/01QFv>vQC%8576321+\\Y0%QB3QL1Q@/01QLr1%=5<QF216%@3?61&H(1%R41R5%QJ3R6QCQH+F%QL3R81QJ(4%115%73631%837Q=1%93871%;31HR3&C%11@%Q0231%Q12QL1%Q22A1qQ0Q41%Q:2Q51qS6RB1%Q<2RC1p0Q>1p0QF1p0QN1p0R51p0RD1pS4RI1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_chk3_region) 0%nat 0%nat).
Lemma chk3_region : ltac:(sec_stmt2 constr:(SEC_T_chk3_region) 1%nat 0%nat).
Proof.
intros Hn64 H10 H9 H18 H2.
pose proof p_facts as (Pp & Ppn & Pp8 & Pq). unfold SB, HIGHEND in *.
assert (S1 : exists r1, msteps ASEGS (mkst regs (0x630d8 : word) M rom) (mkst r1 (0x7ae38 : word) M rom)
/\ (getr r1 10 = Z_to_bv 64 p /\ getr r1 11 = Z_to_bv 64 N /\ getr r1 2 = Z_to_bv 64 s /\ getr r1 1 = (0x6321c : word)
/\ getr r1 22 = Z_to_bv 64 (N - 1) /\ keeps_but [1; 18; 22]%bv regs r1)).
{ eexists. split.
- stepiv (ltac:(oF' 0x630d8%Z)) (ltac:(oD' 0x630d8%Z)) (Z_to_bv 64 (N - 65)) ltac:(wval).
stepn (ltac:(oF' 0x630dc%Z)) (ltac:(oD' 0x630dc%Z)).
stepb_tk (ltac:(oF' 0x630e0%Z)) (ltac:(oD' 0x630e0%Z)) ltac:(cond).
stepb_tk (ltac:(oF' 0x631d0%Z)) (ltac:(oD' 0x631d0%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x6320c%Z)) (ltac:(oD' 0x6320c%Z)) (Z_to_bv 64 (N - 1)) ltac:(wval).
stepiv (ltac:(oF' 0x63210%Z)) (ltac:(oD' 0x63210%Z)) (Z_to_bv 64 p) ltac:(wval).
stepiv (ltac:(oF' 0x63214%Z)) (ltac:(oD' 0x63214%Z)) (Z_to_bv 64 N) ltac:(wval).
stepn (ltac:(oF' 0x63218%Z)) (ltac:(oD' 0x63218%Z)).
apply mst_refl.
- repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q2 & Q1 & Q22 & K1).
destruct (region_call r1 (0x6321c : word) Hn64 ret_ok_6321c Q10 Q11 Q2 Q1) as (r2 & M2 & RUN2 & V10 & K2 & FR2).
assert (S22 : getr r2 22 = Z_to_bv 64 (N - 1)) by (rewrite (K2 22%bv) by (cbv; tauto); exact Q22).
eexists. exists M2. split; [|split; [|split; [|exact FR2]]].
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
stepiv (ltac:(oF' 0x6321c%Z)) (ltac:(oD' 0x6321c%Z)) (Z_to_bv 64 0) ltac:(wval).
stepiv (ltac:(oF' 0x63220%Z)) (ltac:(oD' 0x63220%Z)) (Z_to_bv 64 (N - 1)) ltac:(wval).
stepb_tk (ltac:(oF' 0x63224%Z)) (ltac:(oD' 0x63224%Z)) ltac:(cond).
apply mst_refl.
- gres; rwH; reflexivity.
- eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [apply keeps_but_cs; exact K2|]. solve_keeps_but.
Qed.
End SE.
Theorem chk3_run : ltac2:(TCodec.tc2 tcn__Jb0DiagChk "S;&=y5'QGyR0%211%5241'8&Ir1(QE+:(6%33;21%6251&QF&Q4v@+1%3221%52@1%>3@71r2+9%>3F1<%A231%;2F8%D3F21r3+B%D3L1B%G231vQ?%B2M1%K3M31r4+C%K3Q31I%N231vQ=%I2Q41%Q23Q431r5+2%Q23Q:1Q0%Q5231vQD%Q02Q;1%Q93Q;31'9'5y8%QA11%311p0QA1'7'A&M&JvQ8r8+\\U<%QD3QJ1QB/01QJv>vQC%8576321+\\Y0%QJ3R01QH/01R0%<5;Q@1QM5%?3>51%R02QBQK%R23R41QE&H(1%R91R:%R33R;QKR1+D%R53R=1R3+E%R73R?1R5+F%R93RA1R7(4%119%;3:31%<3;61%=3<91%>3=QK1%?3>R21%@3?>1%B31Q0R6&C%11RE%Q8231%Q92G1%Q:2J1qQ0Q<1%QB2Q=1qS6RN1%QD2RO1p0QF1p0QN1p0R61p0R>1p0RE1pS4S51").
Proof.
intros regs H10 H9 H18 H19 H2.
destruct (chk3_head regs H10 H9 H18 H19) as (r0 & RUN0 & A10 & A9 & A18 & A2 & K0). rewrite H2 in A2.
assert (KW : forall L r r', keeps_but L r r' -> incl L [1; 9; 18; 20; 21; 22]%bv -> keeps_but [1; 9; 18; 20; 21; 22]%bv r r').
{ intros L r r' K I x Hx Hn. apply K; [exact Hx|]. intros Hin. apply Hn. apply I. exact Hin. }
destruct (Z_le_gt_dec N 64) as [Hle|Hgt].
- destruct (chk3_fast r0 Hle A10 A9 A18) as (r & RUN & V & K). exists r, M.
split; [eapply msteps_trans; [exact RUN0 | exact RUN] | split; [exact V | split; [|exact frame72_refl]]].
eapply keeps_but_trans; [apply (KW _ _ _ K0) | apply (KW _ _ _ K)]; intros x Hx; cbn in Hx |- *; tauto.
- destruct (chk3_region r0 ltac:(lia) A10 A9 A18 A2) as (r & M' & RUN & V & K & FR). exists r, M'.
split; [eapply msteps_trans; [exact RUN0 | exact RUN] | split; [exact V | split; [|exact FR]]].
eapply keeps_but_trans; [apply (KW _ _ _ K0) | apply (KW _ _ _ K)]; intros x Hx; cbn in Hx |- *; tauto.
Qed.
End CHK.
Definition chk_pre (M : word -> option byte) (p N s : Z) : Prop :=
(0 < N <= 2 ^ 40)%Z /\ in_app8 p N /\ (0 < p)%Z /\ ((0x1000000 <= s - 72)%Z /\ (s < 2 ^ 64)%Z) /\ (SB + (p + N - 1) / 8 + 8 <= s - 72)%Z
/\ store_ok ASEGS M (Z_to_bv 64 (s - 72)) 72%nat = true /\ rt_layout_globs M
/\ (forall x : word, (SB + p / 8 - 7 <= bv_unsigned x < Z.min (SB + (p + N - 1) / 8 + 8) (SB + 2 ^ 44))%Z -> M x = Some (Z_to_bv 8 0)).
Theorem chk1 : ltac2:(TCodec.tc2 tcn__Jb0DiagChk "RK'QGyR0%211'5y8%511%311p051';&=y5%2219&Dr6r4r3r2%544321'8&I(QE+:(6%33=21%5281&QF&Q4+1%22>1%42L1%<3L61+F%<3F1:%>2B1%92Q1E%A3Q121+2%A3K1?%C2H1r5%?2Q71%G3Q731'9'7'A&M&JvQ8r7+\ka<%N3QA1L/01QAr<r;%8576321+\k\<%Q43QG1Q2/01QGr1%=5<Q;216%@3?61&H(1%QO1QE%Q<3QFQ5Q:+G%Q>3QH1Q<(4%115%73631%83761%:31GQG&Er8%23F1@%Q0241%Q12@1qQ0R61%Q42R71qS6R41%Q62R51p0Q81p0Q?1p0QE1p0R31pS4R:1pS:R>1pQ2R?1pS0R@1pS8RB1pNRC1").
Proof.
intros M rom p N s regs (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
exact (chk1_run M rom p N s A1 A2 A3 A4 A5 A6 A7 A8 _ _ _ _ eq_refl eq_refl eq_refl eq_refl regs).
Qed.
Theorem chk2 : ltac2:(TCodec.tc2 tcn__Jb0DiagChk "S>'QGyR0%211'5y8%511%311p051';&=y5%2219&Dr6r4r3r2%544321'8&I(QE+:(6%33=21%5281&QF&Q4&Nr5%221?+1%5221%72O1%?3O91+B%?3I1=%A2E1%<2Q4H%D3Q421+D%D3N1B%F2K1%A2Q9<%I3Q921+2%I3Q31G%K2B1%M3Q=1:'9'7'A&M&JvQ8r8+\b_H%Q43QG1Q2/01QGr=r<%8576321+\bbH%Q:3QM1Q8/01QMr1%=5<QA216%@3?61r;r:%Q:221%Q<21Q8%Q>2R61%QF3R6Q@1&H(1%R;1R1%QH3R2Q>QF+9%QJ3R41QH+E%QL3R61QJ(4%117%93831%:39Q<1%;3:QB1%<3;81%=3<;1%?31Q2R8&Er9%23Q11K%Q;241%Q<2E1%Q=2L1qQ0RH1%Q@2RI1qS6RF1%QB2RG1p0QD1p0QI1p0QO1p0R51p0RF1pS4RM1pS:S11pQ2S21pS0S31pS8S51pNS61").
Proof.
intros M rom p N s regs (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
exact (chk2_run M rom p N s A1 A2 A3 A4 A5 A6 A7 A8 _ _ _ _ eq_refl eq_refl eq_refl eq_refl regs).
Qed.
Theorem chk3 : ltac2:(TCodec.tc2 tcn__Jb0DiagChk "TN'QGyR0%211'5y8%511%311p051';&=y5%2219&Dr7r5r4r3%544321'7&Q1%1264&Q3+2+QO%3221%6291%8261'8'2%11H%K11&K&Mr9(QE+QV`l@(6%33Q421/01Q4u8%948721(0&<&QF+Qii[8%22Q<1%4271%62B1%E3B81r:+Qiic3%A3QB1?/01QBu1%G4F521(1+1%>2QE1(4%11QF%53QG31%D2Q01%Q33Q081&I+:%O3QG1M%32QD1&Q4r8%221=%K2R51%Q<3R551r6+9%Q83R01Q6%<231%Q12R;D%QB3R;21+B%Q=3R51Q;%A2R31r;%Q72RA1%QH3RA31+C%QC3R;1QA%G2B1%Q<2RFQF%QM3RF21%QG3R?R3QE%K2QI1%R03RI19'9'A&JvQ8r<+\\U<%R03S11QN/01S1rBrA%8576321r2+\\Y0%R73S81R5/01S8r1%>5=5217%@3R=71%Q?27Q=r?%Q=21QH%R62S@1%RG3S@41&H%SD1S:%RC3S;QMRA+D%RE3S=1RC+E%RG3S?1RE+F%RI3SA1RG%R218%R63921%R73:51%R83;81%R93<QA1%R:3=QG1%R;3>=1%@31Q3L&Er>%23Q21K%SE241%SF2F1%SG2L1qQ0T31%Q?2T41qS6T11%QA2T21p0QC1p0QG1p0QM1p0R41p0R;1p0RE1p0S41p0SK1p0T51pS4T<1pRLT@1pS:TA1pQ2TB1pS0TC1pS8TE1pNTF1").
Proof.
intros M rom p N s maxlen regs (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8) B1 B2 B3.
exact (chk3_run M rom p N s A1 A2 A3 A4 A5 A6 A7 A8 _ _ _ _ eq_refl eq_refl eq_refl eq_refl maxlen B1 B2 B3 regs).
Qed.
Lemma ret_ok_66e2c : ltac2:(TCodec.tc2 tcn__Jb0DiagChk ":&B(QEyR0+\ka<(6%43321'QG%115/031%911"). Proof. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
Theorem strlen_chk1 : forall M rom p s (bs : list byte) regs,
rdn ASEGS M (Z_to_bv 64 p) (length bs + 1) = Some (bs ++ [Z_to_bv 8 0]) ->
(forall j, (j < length bs)%nat -> bv_unsigned (nth j bs (Z_to_bv 8 0)) <> 0%Z) ->
chk_pre M p (Z.of_nat (length bs) + 1) s ->
getr regs 10 = Z_to_bv 64 p -> getr regs 22 = Z_to_bv 64 p -> getr regs 2 = Z_to_bv 64 s ->
exists regs' M',
msteps ASEGS (mkst regs (0x66e28 : word) M rom) (mkst regs' (0x66d8c : word) M' rom)
/\ keeps_but [1; 23]%bv regs regs' /\ frame72 M s M'.
Proof.
intros M rom p s bs regs HS HNZ CP H10 H22 H2.
assert (Hp : (0 <= p)%Z /\ (p + Z.of_nat (length bs) + 1 < 2 ^ 63)%Z).
{ destruct CP as (_ & A2 & _). unfold in_app8, LOWEND, HIGHBEG, HIGHEND in A2. lia. }
assert (S1 : exists r1, msteps ASEGS (mkst regs (0x66e28 : word) M rom) (mkst r1 (0x8af2c : word) M rom)
/\ (getr r1 1 = (0x66e2c : word) /\ getr r1 10 = Z_to_bv 64 p /\ getr r1 22 = Z_to_bv 64 p /\ getr r1 2 = Z_to_bv 64 s /\ keeps_but [1; 23]%bv regs r1)).
{ eexists. split.
+ stepn (ltac:(oF' 0x66e28%Z)) (ltac:(oD' 0x66e28%Z)). apply mst_refl.
+ repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
destruct S1 as (r1 & RUN1 & R1 & R10 & R22 & R2 & K1).
{
destruct (internal_strlen_run M rom p bs Hp HS HNZ r1 (0x66e2c : word) ret_ok_66e2c R1 R10) as (r2 & RUN2 & V10 & K2).
assert (S22 : getr r2 22 = Z_to_bv 64 p) by (rewrite (K2 22%bv) by (cbv; tauto); exact R22).
assert (S2 : getr r2 2 = Z_to_bv 64 s) by (rewrite (K2 2%bv) by (cbv; tauto); exact R2).
destruct (chk1 M rom p (Z.of_nat (length bs) + 1) s r2 CP ltac:(rewrite V10; f_equal; lia) S22 S2) as (r3 & M3 & RUN3 & K3 & FR3).
exists r3, M3. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2 | exact RUN3]|]. split; [|exact FR3].
eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [apply keeps_but_cs; exact K2 | exact K3]. }
Qed.
End FPX_1.
