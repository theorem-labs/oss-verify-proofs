(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import MemsetLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanMemset_codeK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__AsanMemset1K () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanMemset1K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanMemset1K.Walk."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanMemset1K.Walk.Aligned."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanMemset_codeK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.MemsetLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1cons"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "2I"; "2and"; "2eq"; "2ex"; "3Z"; "0L"; "4bvmap"; "0M"; "7LB"]; ["7LC"; "7LD"; "6L2"; "6L6"; "6L8"; "5asanreflect_fx"; "8ms_base"; "9msteps"; ":at_"; ";c32"; ";c64"; ";cbyte"; ";cfill"; ";ms_agree"; "<getr"; "<mkst"]; ["=loaded_segments"; ">add"; ">le"; ">lt"; ">mul"; ">of_nat"; ">sub"; "0a"; "0cv"; "0d"; "0k"; "0mem0"; "0n"; "0n1"; "0q"; "0r"]; ["0regs"; "0regs'"; "0ret"; "0rom"; "0s4"; "?BV"; "?Z_to_bv"; "?bv"]]).
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
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
rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
#[local] Ltac pclits :=
repeat match goal with
| |- context [Z_to_bv 64 (ms_base + ?o)%Z] => wlit_replace (Z_to_bv 64 (ms_base + o)%Z)
end.
#[local] Ltac stepat L F D vv tac :=
chain_step; [reflexivity | eapply L with (v := vv); [exact F | reflexivity | exact D | reflexivity | tac] | step_simpl].
Section Walk.
Variable mem0 : word -> option byte.
Variables d cv ret : word.
Variable n : Z.
Variable rom : word -> option byte.
Hypothesis Hn : (0 <= n)%Z.
Hypothesis Hnw : (bv_unsigned d + n < 2 ^ 64)%Z.
Hypothesis Hok : store_ok MSEGS mem0 d (Z.to_nat n) = true.
Hypothesis Hret : ret_ok ret.
#[local] Abbreviation CF := (cfill mem0 d n (cbyte cv)).
#[local] Abbreviation PC o := (Z_to_bv 64 (ms_base + o)).
#[local] Ltac msb F D oo :=
chain_step; [reflexivity
| eapply (cf_sb MSEGS mem0 d n cv Hnw Hok) with (o := oo);
[exact F | reflexivity | exact D
| gres; rwH; rewrite ?at_addi; reflexivity
| imm_norm; lia
| gres; rwH; reflexivity
| lia | lia]
| step_simpl].
#[local] Ltac msw F D oo :=
chain_step; [reflexivity
| eapply (cf_sw MSEGS mem0 d n cv Hnw Hok) with (o := oo);
[exact F | reflexivity | exact D
| gres; rwH; rewrite ?at_addi; reflexivity
| imm_norm; lia
| gres; rwH; reflexivity
| apply wleb4_c32
| lia | lia]
| step_simpl].
#[local] Ltac msd F D oo :=
chain_step; [reflexivity
| eapply (cf_sd MSEGS mem0 d n cv Hnw Hok) with (o := oo);
[exact F | reflexivity | exact D
| gres; rwH; rewrite ?at_addi; reflexivity
| imm_norm; lia
| gres; rwH; reflexivity
| apply wleb8_c64
| lia | lia]
| step_simpl].
#[local] Ltac mret := stepret Fo_0f4 Do_0f4 ret ltac:(rwH; reflexivity).
#[local] Ltac post := repeat split; gres; rwH; try reflexivity; solve_ms_agree.
Definition L2 : list (Z * Z) := [(n-1,1); (0,1)]%Z.
Definition L6 : list (Z * Z) := [(n-2,1); (n-3,1); (2,1); (1,1); (n-1,1); (0,1)]%Z.
Definition L8 : list (Z * Z) := [(n-4,1); (3,1); (n-2,1); (n-3,1); (2,1); (1,1); (n-1,1); (0,1)]%Z.
Lemma A_exit0 : ltac2:(TCodec.tc2 tcn__AsanMemset1K "R=&=y5'QGyR0%211%5241'9&Nr1(QE+:(7%33;21%6251&HvQ9z%3221%<3>51r2+;%<3D1:%?231vQ8%B3D21r3+<%B3J1@%E231&QFvQ<%22L1%J3L41r4+1%J3Q21H%M231vQB%Q03Q221';%Q231:H':'8'G&Q0&O&Er7&Q1&F%221Q2%F2Q@1&LvQ;&K%11Q0(3'6%12CC%311%857Q=N51vQC%A5@?;21%B5AQGJ32%E3D21&M%12CQJ%I2QA1%J241qS4R01%M2R11p0O1p0Q21p0Q91p0QB1p0QI1pS2R71").
Proof.
intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
eexists. split.
- stepb_tk Fo_000 Do_000 ltac:(cond).
mret.
apply mst_refl.
- post.
Qed.
Lemma A_exit2 : ltac2:(TCodec.tc2 tcn__AsanMemset1K "RC&=y5'QGyR0%211%5241'9&Nr1(QE+:(7%33;21%6251&HvQ9z%3221%<3>51r2+;%<3D1:%?231vQ8%B3D21r3+<%B3J1@%E231&QFvQ<%22L1%J3L41r4+1%J3Q21H%M231vQB%Q03Q221'8&Q2%127;+2%32=1%5231':'G&Q0&O&Er7&Q1&F%221Q5%I2QC1&LvQ;&K%11Q3(3'6';%2211%411%958QAQ261vQC%B5A@<21&B%=5<QEQ6:1%E5DQMQ014%H3G41&M%12FR0%Q22QG1%Q3241qS4R61%O2R71p0Q11p0Q81p0Q?1p0QH1p0QO1pS2R=1").
Proof.
intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
eexists. split.
- stepb_ft Fo_000 Do_000 ltac:(cond).
msb Fo_004 Do_004 0%Z.
stepiv Fo_008 Do_008 (at_ d n) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).
stepn Fo_00c Do_00c.
msb Fo_010 Do_010 (n-1)%Z.
stepb_tk Fo_014 Do_014 ltac:(cond).
mret.
apply mst_refl.
- post.
Qed.
Lemma A_exit6 : ltac2:(TCodec.tc2 tcn__AsanMemset1K "RD&=y5'QGyR0%211%5241'9&Nr1(QE+:(7%33;21%6251&HvQ9z%3221%<3>51r2+;%<3D1:%?231vQ8%B3D21r3+<%B3J1@%E231&QFvQ<%22L1%J3L41r4+1%J3Q21H%M231vQB%Q03Q221'8&Q2+3%221<+6%42>1%6231':'G&Q0&O&Er7&Q1&F%221Q6%J2QD1&LvQ;&K%11Q4(3'6';%2211%411%958QBQ361vQC%B5A@<21&C%=5<QFQ7:1%E5DQNQ114%H3G41&M%12FR1%Q32QH1%Q4241qS4R71%O2R81p0Q11p0Q91p0Q@1p0QI1p0R01pS2R>1").
Proof.
intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
eexists. split.
- stepb_ft Fo_000 Do_000 ltac:(cond).
msb Fo_004 Do_004 0%Z.
stepiv Fo_008 Do_008 (at_ d n) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).
stepn Fo_00c Do_00c.
msb Fo_010 Do_010 (n-1)%Z.
stepb_ft Fo_014 Do_014 ltac:(cond).
msb Fo_018 Do_018 1%Z.
msb Fo_01c Do_01c 2%Z.
stepn Fo_020 Do_020.
msb Fo_024 Do_024 (n-3)%Z.
msb Fo_028 Do_028 (n-2)%Z.
stepb_tk Fo_02c Do_02c ltac:(cond).
mret.
apply mst_refl.
- post.
Qed.
Lemma A_exit8 : ltac2:(TCodec.tc2 tcn__AsanMemset1K "RD&=y5'QGyR0%211%5241'9&Nr1(QE+:(7%33;21%6251&HvQ9z%3221%<3>51r2+;%<3D1:%?231vQ8%B3D21r3+<%B3J1@%E231&QFvQ<%22L1%J3L41r4+1%J3Q21H%M231vQB%Q03Q221'8&Q2+7%221<+8%42>1%6231':'G&Q0&O&Er7&Q1&F%221Q6%J2QD1&LvQ;&K%11Q4(3'6';%2211%411%958QBQ361vQC%B5A@<21&D%=5<QFQ7:1%E5DQNQ114%H3G41&M%12FR1%Q32QH1%Q4241qS4R71%O2R81p0Q11p0Q91p0Q@1p0QI1p0R01pS2R>1").
Proof.
intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
eexists. split.
- stepb_ft Fo_000 Do_000 ltac:(cond).
msb Fo_004 Do_004 0%Z.
stepiv Fo_008 Do_008 (at_ d n) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).
stepn Fo_00c Do_00c.
msb Fo_010 Do_010 (n-1)%Z.
stepb_ft Fo_014 Do_014 ltac:(cond).
msb Fo_018 Do_018 1%Z.
msb Fo_01c Do_01c 2%Z.
stepn Fo_020 Do_020.
msb Fo_024 Do_024 (n-3)%Z.
msb Fo_028 Do_028 (n-2)%Z.
stepb_ft Fo_02c Do_02c ltac:(cond).
msb Fo_030 Do_030 3%Z.
stepn Fo_034 Do_034.
msb Fo_038 Do_038 (n-4)%Z.
stepb_tk Fo_03c Do_03c ltac:(cond).
mret.
apply mst_refl.
- post.
Qed.
Lemma A_cont : ltac2:(TCodec.tc2 tcn__AsanMemset1K "S9&=y5'QGyR0%211%5241'9&Nr1(QE+:(7%33;21%6251&HvQ9z%3221%<3>51r2+;%<3D1:%?231vQ8%B3D21r3+<%B3J1@%E231&QFvQ<%22L1%J3L41r4+1%J3Q21H%M231vQB%Q03Q221&Q2+9%221;':'8'G&Q0&O&Er7&Q1&F%221Q3%G2QA1&LvQ;&K%11Q1(3'6';%2211%411%958Q?Q061vQC%B5A@<21+R0%A2@1%Q62R01&D%@5?QFQ7=1%H5GQN317%K3J71%R12R0QC%R33R51QB%R32R2Q?%R53R71Q<+=%R43R<1R2%R72R61%R12R0QA%R:3R<21+?%R93RA1R7%R<2R;1%QG2RAQ<%R?3RA21%R?2R>QC%RA3RC1QB&M%12Q9RA%Q?231%Q@261%QA2<1%QB2B1%QC2E1%QD2R=1%QE2I1qS4RL1%QH2RM1p0QJ1p0QN1p0R51p0R>1p0RE1pS2S31").
Proof.
intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
eexists. split.
- stepb_ft Fo_000 Do_000 ltac:(cond).
msb Fo_004 Do_004 0%Z.
stepiv Fo_008 Do_008 (at_ d n) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).
stepn Fo_00c Do_00c.
msb Fo_010 Do_010 (n-1)%Z.
stepb_ft Fo_014 Do_014 ltac:(cond).
msb Fo_018 Do_018 1%Z.
msb Fo_01c Do_01c 2%Z.
stepn Fo_020 Do_020.
msb Fo_024 Do_024 (n-3)%Z.
msb Fo_028 Do_028 (n-2)%Z.
stepb_ft Fo_02c Do_02c ltac:(cond).
msb Fo_030 Do_030 3%Z.
stepn Fo_034 Do_034.
msb Fo_038 Do_038 (n-4)%Z.
stepb_ft Fo_03c Do_03c ltac:(cond).
apply mst_refl.
- post.
Qed.
Section Aligned.
Variables k n1 : Z.
Hypothesis Hk : (0 <= k <= 3)%Z.
Hypothesis Hn1 : (n - k - 3 <= n1 <= n - k)%Z.
Hypothesis Hkv : v_andi (v_subw (Z_to_bv 64 0) d) 3 = Z_to_bv 64 k.
Hypothesis Hn1v : v_andi (Z_to_bv 64 (n - k)) (-4) = Z_to_bv 64 n1.
Definition LB : list (Z * Z) := ((k+n1-4,4) :: (k,4) :: L8)%Z.
Definition LC : list (Z * Z) := ((k+n1-8,4) :: (k+n1-12,4) :: (k+8,4) :: (k+4,4) :: LB)%Z.
Definition LD (s4 : Z) : list (Z * Z) :=
((k+n1-16,4) :: (k+n1-20,4) :: (k+n1-24,4) :: (k+n1-28,4)
:: (k+24,4) :: (k+20,4) :: (k+16,4) :: (k+12,4) :: LC)%Z.
#[local] Ltac blockB :=
stepn Fo_040 Do_040;
stepn Fo_044 Do_044;
stepn Fo_048 Do_048;
stepiv Fo_04c Do_04c (Z_to_bv 64 k) ltac:(gres; rwH; imm_norm; rewrite at_0; exact Hkv);
stepn Fo_050 Do_050;
stepiv Fo_054 Do_054 (Z_to_bv 64 (n - k)) ltac:(gres; rwH; apply ms_v_sub_ZZ; lia);
stepiv Fo_058 Do_058 (at_ d k) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia);
stepn Fo_05c Do_05c;
stepiv Fo_060 Do_060 (Z_to_bv 64 n1) ltac:(gres; rwH; imm_norm; exact Hn1v);
stepat ms_step_mulhu_at Fo_064 Do_064 (c32 cv) ltac:(gres; rwH; apply mulhu_c32; unorm; reflexivity);
msw Fo_068 Do_068 k;
stepiv Fo_06c Do_06c (at_ d (k + n1)) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; reflexivity);
msw Fo_070 Do_070 (k + n1 - 4)%Z.
Lemma B_exit : ltac2:(TCodec.tc2 tcn__AsanMemset1K "S0&=y5'QGyR0%211%5241'9&Nr1(QE+:(7%33;21%6251&HvQ9z%3221%<3>51r2+;%<3D1:%?231vQ8%B3D21r3+<%B3J1@%E231&QFvQ<%22L1%J3L41r4+=%J3Q21H%M231%G2F7%Q03Q221r5+?%Q03Q81N%Q3231+9%?2Q91%Q73Q931r6+1%Q73Q?1Q5%Q:231vQB%Q=3Q?21&Q2%12:G&Q3vQ=%221=':'8'G&Q0&O&Er:&Q1&F+R0%3221%Q72R11&LvQ;&K%11QA&D%554QKQ<21vQC%?5>=821&?%958QOQ@61%B5AR7M14%E3D41&M%12CR:%I2R11%J241qS4R@1%M2RA1p0O1p0Q31p0Q61p0Q=1p0QE1p0QL1p0R51p0R<1pS2RJ1").
Proof.
intros regs H10 H11 H12 H13 H15 H1 Hn9 Hc. pose proof (u64_range d) as Hd. pclits.
eexists. split.
- blockB.
stepb_tk Fo_074 Do_074 ltac:(cond).
mret.
apply mst_refl.
- post.
Qed.
Lemma B_cont : ltac2:(TCodec.tc2 tcn__AsanMemset1K "SJ&=y5'QGyR0%211%5241'9&Nr1(QE+:(7%33;21%6251&HvQ9z%3221%<3>51r2+;%<3D1:%?231vQ8%B3D21r3+<%B3J1@%E231&QFvQ<%22L1%J3L41r4+=%J3Q21H%M231%G2F7%Q03Q221r5+?%Q03Q81N%Q3231+9%?2Q91%Q73Q931r6+1%Q73Q?1Q5%Q:231vQB%Q=3Q?21&Q2%12:GvQ=%32<1':'8'G&Q0&O&Er:&Q1&F+R0%3221%Q62R01&LvQ;&K%11Q@&D%554QJQ;21vQC%?5>=821+SH%>2=1%QA2R;1&?%<5;R1QB91%E5DR9317%H3G71%R<2R;QNvQ:%R72R61%R@3RB31%R@2R?QL&I%11R2%RD3RF31%RD2RCQH%M28Q6%R?2R>1%RH3RJ31+>%RG3RO1RE%RJ2RI1%R52ROQ<%RM3RO21%RM2RLQD%RO3S11QC&M%12Q9RO%Q?231%Q@261%QA2<1%QB2A1%QC2F1%QD2RK1%QE2L1qS4S:1%QH2S;1p0QJ1p0QM1p0R01p0R71p0R?1p0RF1p0RO1p0S61pS2SD1").
Proof.
intros regs H10 H11 H12 H13 H15 H1 Hn9 Hc. pose proof (u64_range d) as Hd. pclits.
eexists. split.
- blockB.
stepb_ft Fo_074 Do_074 ltac:(cond).
apply mst_refl.
- post.
Qed.
#[local] Ltac blockC :=
msw Fo_078 Do_078 (k + 4)%Z;
msw Fo_07c Do_07c (k + 8)%Z;
stepn Fo_080 Do_080;
msw Fo_084 Do_084 (k + n1 - 12)%Z;
msw Fo_088 Do_088 (k + n1 - 8)%Z.
Lemma C_exit : ltac2:(TCodec.tc2 tcn__AsanMemset1K "S7&=y5'QGyR0%211%5241'9&Nr1(QE+:(7%33;21%6251&HvQ9z%3221%<3>51r2+;%<3D1:%?231vQ:%:291%C3E31r3+<%C3K1A%F231&IvQ8%211%K3M41r4+=%K3Q31I%N231&Q1vQ=%22A1%K2J1%Q43Q651r5+>%Q43Q<1Q2%Q7231&QF%12Q=9%Q;3Q=31r6+1%Q;3QC1Q9%Q>231vQB%QA3QC21&Q2+9vQ<%3221%42Q1E&Q3+I%22H1':'8'G&Q0&O&Er;&F+SH%Q3221%K2R71&LvQ;&K%11Q?&?%554R1F21vQC%>5=<821&@%958R5J61%A5@R=O14%D3C41&M%12BR@%H2R71%I241qS4RF1%L2RG1p0N1p0Q21p0Q41p0Q91p0Q@1p0QH1p0R21p0R;1p0RC1pS2S11").
Proof.
intros regs H10 H11 H12 H13 H14 H1 Hn9 Hn1' Hc. pose proof (u64_range d) as Hd. pclits.
eexists. split.
- blockC.
stepb_tk Fo_08c Do_08c ltac:(cond).
mret.
apply mst_refl.
- post.
Qed.
Lemma C_cont : ltac2:(TCodec.tc2 tcn__AsanMemset1K "SF&=y5'QGyR0%211%5241'9&Nr1(QE+:(7%33;21%6251&HvQ9z%3221%<3>51r2+;%<3D1:%?231vQ:%:291%C3E31r3+<%C3K1A%F231&IvQ8%211%K3M41r4+=%K3Q31I%N231&Q1vQ=%22A1%K2J1%Q43Q651r5+>%Q43Q<1Q2%Q7231&QF%12Q=9%Q;3Q=31r6+1%Q;3QC1Q9%Q>231vQB%QA3QC21&Q2+9vQ<%3221+I%521F':'8'G&Q0&O&Er:&F+SH%Q1221%I2R51&LvQ;&K%11Q=&?%554QOD21vQC%>5=<821+T@%Q<2=1%Q42R@1&@%<5;R6K91%D5CR>317%G3F71%RA2R@R3%RC3RE1R1%RC2RBQN%RE3RG1QK%RE2RDQH%RG3RI1QD%RG2RFQA%RI3RK1Q?%RI2RHQ<%RK3RM1Q;&M%12ORK%Q5231%Q6261%Q7291%Q82<1%Q92?1%Q:2RG1%Q;2C1qS4S61%Q>2S71p0Q@1p0QC1p0QH1p0QO1p0R71p0RA1p0RJ1p0S21pS2S@1").
Proof.
intros regs H10 H11 H12 H13 H14 H1 Hn9 Hc. pose proof (u64_range d) as Hd. pclits.
eexists. split.
- blockC.
stepb_ft Fo_08c Do_08c ltac:(cond).
apply mst_refl.
- post.
Qed.
Section D.
Variable s4 : Z.
Hypothesis Hs4 : (s4 = 0 \/ s4 = 4)%Z.
Hypothesis Hs4v : v_andi (at_ d k) 4 = Z_to_bv 64 s4.
#[local] Ltac blockD :=
msw Fo_090 Do_090 (k + 12)%Z;
msw Fo_094 Do_094 (k + 16)%Z;
msw Fo_098 Do_098 (k + 20)%Z;
msw Fo_09c Do_09c (k + 24)%Z;
stepiv Fo_0a0 Do_0a0 (Z_to_bv 64 s4) ltac:(gres; rwH; imm_norm; exact Hs4v);
stepn Fo_0a4 Do_0a4;
stepiv Fo_0a8 Do_0a8 (Z_to_bv 64 (s4 + 24)) ltac:(gres; rwH; imm_norm; apply ms_v_addi_Z; lia);
stepiv Fo_0ac Do_0ac (Z_to_bv 64 (n1 - s4 - 24)) ltac:(gres; rwH; rewrite ms_v_sub_ZZ by lia; f_equal; lia);
msw Fo_0b0 Do_0b0 (k + n1 - 28)%Z;
msw Fo_0b4 Do_0b4 (k + n1 - 24)%Z;
msw Fo_0b8 Do_0b8 (k + n1 - 20)%Z;
msw Fo_0bc Do_0bc (k + n1 - 16)%Z.
Lemma D_exit : ltac2:(TCodec.tc2 tcn__AsanMemset1K "S>&=y5'QGyR0%211%5241'9&Nr1(QE+:(7%33;21%6251&HvQ9z%3221%<3>51r2+;%<3D1:%?231vQ:%:291%C3E31r3+<%C3K1A%F231&IvQ8%211%K3M41r4+=%K3Q31I%N231&Q1vQ=%22A1%K2J1%Q43Q651r5+>%Q43Q<1Q2%Q7231&QF%12Q=9%Q;3Q=31r6+1%Q;3QC1Q9%Q>231vQB%QA3QC21&Q2+9vQ<%3221+L%521F&Q3&Q6vQD%22J1+H%4221+Q0%7221':'8'G&Q0&O&Er;&F+T@%Q9221%Q12R=1&LvQ;&K%11QE&@%554R7L21vQC%>5=<821&A%11J%:59R<Q171%B5ARDQ615%E3D51&M%12CRG%I2R>1%J241qS4RM1%M2RN1p0O1p0Q81p0Q;1p0Q@1p0QG1p0QO1p0R91p0RB1p0RJ1pS2S81").
Proof.
intros regs H10 H11 H12 H13 H14 H1 Hn9 Hn1' Hc. pose proof (u64_range d) as Hd. pclits.
eexists. split.
- blockD.
stepb_tk Fo_0c0 Do_0c0 ltac:(cond).
mret.
apply mst_refl.
- post.
Qed.
Lemma D_cont : ltac2:(TCodec.tc2 tcn__AsanMemset1K "T4&=y5'QGyR0%211%5241'9&Nr1(QE+:(7%33;21%6251&HvQ9z%3221%<3>51r2+;%<3D1:%?231vQ:%:291%C3E31r3+<%C3K1A%F231&IvQ8%211%K3M41r4+=%K3Q31I%N231&Q1vQ=%22A1%K2J1%Q43Q651r5+>%Q43Q<1Q2%Q7231&QF%12Q=9%Q;3Q=31r6+1%Q;3QC1Q9%Q>231vQB%QA3QC21&Q2+9vQ<%3221+L%521F+Q0&Q6vQD%22J1+H%4221%<261':'8'G&Q0&O&Er;&F+T@%Q8221%Q02R<1&LvQ;&K%11QD&@%554R6K21vQC%>5=<821+V4%QC2=1%Q;2RG1&A%11L%=5<R>Q3:1%E5DRF418%H3G81%RI2RHR;%RK3RM1R9%RK2RJR6%RM3RO1R3%RM2RLQG%QF2S2Q2%S03S221+?%RO3S71RM%S22S11%R42Q:Q8%QL2S81%S63S831%S62S5QI%S83S:1QH&M%12Q5S8%Q;231%Q<261%Q=2=1%Q>2A1%Q?2D1%Q@2S41%QA2H1qS4SC1%QD2SD1p0QF1p0QN1p0R11p0R61p0R=1p0RE1p0RO1p0S81p0S@1pS2SN1").
Proof.
intros regs H10 H11 H12 H13 H14 H1 Hn9 Hn1' Hc. pose proof (u64_range d) as Hd. pclits.
eexists. split.
- blockD.
stepb_ft Fo_0c0 Do_0c0 ltac:(cond).
apply mst_refl.
- post.
Qed.
Lemma E_run : ltac2:(TCodec.tc2 tcn__AsanMemset1K "T;&=y5'QGyR0%211%5241'1'6';%2211%411'9&Nr2(QE+:(7%33@21%6251&HvQ9z%3221%<3C51r3+;%<3I1:%?231vQ:%:291%C3J31r4+<%C3Q01A%F231&IvQ8%211%K3Q241r5+>%K3Q81I%N231&QF&Q6vQ=vQD%3221+H%5221%72Q?1%Q83Q?91r6+?%Q83QE1Q6%Q;231&Q1%12;9%?2QG1%Q@3QG41r7+1%Q@3QM1Q>%QC231vQB%QF3QM21&Q2+9vQ<%3221+L%521J':'8'G&Q0&O&Er;&F+V4%I221%Q72R?1&LvQ;&K%11QBr:%554R4D21vQC%>5=<821r1+VH%Q52>1%QC2RK1%C5B4176%F3E61%RE26R@%RG3RN1R<%RG28R9%Q<2R8QF%Q=21QE%RC2RB1%RL3S341%RL2=R7&J%11R6%S03S731+=%RO3S<1RM%S22C1+O%R52S=1%S63S=31%S62GR9%S83S?1R1%S82IQF%S:3SA1QE&M%12Q9L%Q?231%Q@261%QA291%QB2@1%QC2E1%QD2K1%QE2N1qS4SJ1%QH2SK1p0QJ1p0QM1p0R21p0R91p0RB1p0S01p0S91p0SA1pJSO1pS2T51").
Proof.
intros regs L H10 H11 H12 H14 H15 H1 Hn9 Hn1'. pose proof (u64_range d) as Hd. pclits.
eexists. split.
- stepiv Fo_0c4 Do_0c4 (c32h cv) ltac:(gres; rwH; imm_norm; apply slli32_c32).
stepiv Fo_0c8 Do_0c8 (at_ d (k + s4 + 24)) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).
stepiv Fo_0cc Do_0cc (c32 cv) ltac:(gres; rwH; imm_norm; apply srli32_c32h);
stepat ms_step_or_at Fo_0d0 Do_0d0 (c64 cv) ltac:(gres; rwH; apply or_c64).
stepn Fo_0d4 Do_0d4.
apply mst_refl.
- post.
Qed.
End D.
End Aligned.
#[local] Ltac ms_cov_eq :=
intros i Hi; rewrite !ms_cov_cons;
match goal with |- _ = ?rhs => match rhs with context [ms_cov ?L i] => destruct (ms_cov L i) end end;
rewrite ?orb_true_r, ?orb_false_r; [reflexivity|];
apply eq_true_iff_eq; rewrite !orb_true_iff, !ms_inb_true; lia.
Lemma loop_run : ltac2:(TCodec.tc2 tcn__AsanMemset1K "T9'2&=y5'QGyR0%211%5241'1'6';%2211%411'9&Nr4(QE+:(7%33@21%6251&HvQ9z%3221%<3C51r5+;%<3I1:%?231r3%:291%C3J31r6+<%C3Q01A%F231&JvQ8%211%K3Q241r7+=%K3Q81I%N231&QF+O%22Q:1%Q33Q:41r8+>%Q33Q@1Q1%Q6231%82Q@K%Q93Q@21r9+1%Q93QF1Q7%Q<231vQB%Q?3QF21&Q2%12Q7=&Q1%129?vQ<%5221'8&Q4+Q0&Q5r=%211%:21A%6251%>21D&Q3%>238%22G1%<241':'G&Q0&O&Er>&F+VH%I221%Q<2RD1&LvQ;&K%11QG%453R8M1GvQC%=5<;721r1+WD%Q42=1%QG2RO1(0(5r<r?%Q311%Q;21QB%Q72Q61%64S2S251%83S21Q6%D5CRHQ=A1%L5K>;1@%O3N@1%S32@RN%S53S<1RJ%S52BQJ%S73S>1QI&M%12Q1E%QD231%QE261%QF291qS4SC1%Q;2SD1p0Q=1p0QK1p0R01p0R31p0R:1p0RA1p0RJ1p0S31p0S;1pS0SK1pR@SL1pJSK1pS2T11pRNT81").
Proof.
induction q as [|q IH]; intros regs L a r H10 H11 H12 H13 H14 H1 Ha Har Hq;
pose proof (u64_range d) as Hd; pclits.
-
eexists. split.
+ msd Fo_0d8 Do_0d8 a.
msd Fo_0dc Do_0dc (a + 8)%Z.
msd Fo_0e0 Do_0e0 (a + 16)%Z.
msd Fo_0e4 Do_0e4 (a + 24)%Z.
stepiv Fo_0e8 Do_0e8 (Z_to_bv 64 (r - 32)) ltac:(gres; rwH; imm_norm; rewrite ms_v_addi_Z by lia; f_equal; lia).
stepiv Fo_0ec Do_0ec (at_ d (a + 32)) ltac:(gres; rwH; imm_norm; rewrite at_addi; reflexivity).
stepb_ft Fo_0f0 Do_0f0 ltac:(cond).
replace (CF ((a + 24, 8) :: (a + 16, 8) :: (a + 8, 8) :: (a, 8) :: L))%Z
with (CF ((a, 32 * (Z.of_nat 0 + 1))%Z :: L)) by (apply cfill_ext; ms_cov_eq).
apply mst_refl.
+ post.
- eapply (runs_trans MSEGS _
(fun rg => mkst rg (PC 0xd8) (CF ((a + 24, 8) :: (a + 16, 8) :: (a + 8, 8) :: (a, 8) :: L))%Z rom)
(fun rg => getr rg 10 = at_ d 0 /\ getr rg 11 = at_ d (a + 32) /\ getr rg 12 = c64 cv
/\ getr rg 13 = Z_to_bv 64 31 /\ getr rg 14 = Z_to_bv 64 (r - 32) /\ getr rg 1 = ret
/\ ms_agree regs rg)).
+ cbv beta. pclits. eexists. split.
* msd Fo_0d8 Do_0d8 a.
msd Fo_0dc Do_0dc (a + 8)%Z.
msd Fo_0e0 Do_0e0 (a + 16)%Z.
msd Fo_0e4 Do_0e4 (a + 24)%Z.
stepiv Fo_0e8 Do_0e8 (Z_to_bv 64 (r - 32)) ltac:(gres; rwH; imm_norm; rewrite ms_v_addi_Z by lia; f_equal; lia).
stepiv Fo_0ec Do_0ec (at_ d (a + 32)) ltac:(gres; rwH; imm_norm; rewrite at_addi; reflexivity).
stepb_tk Fo_0f0 Do_0f0 ltac:(cond).
apply mst_refl.
* post.
+ cbv beta. intros r1 (R10 & R11 & R12 & R13 & R14 & R1 & AG).
destruct (IH r1 ((a + 24, 8) :: (a + 16, 8) :: (a + 8, 8) :: (a, 8) :: L)%Z (a + 32)%Z (r - 32)%Z
R10 R11 R12 R13 R14 R1 ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P10 & P1 & AG2).
exists r2. split.
* replace (CF ((a, 32 * (Z.of_nat (S q) + 1))%Z :: L))
with (CF ((a + 32, 32 * (Z.of_nat q + 1))%Z :: ((a + 24, 8) :: (a + 16, 8) :: (a + 8, 8) :: (a, 8) :: L)%Z))
by (apply cfill_ext; ms_cov_eq).
revert RUN. pclits. intros RUN. exact RUN.
* repeat split; try assumption. eapply ms_agree_trans; eassumption.
Qed.
Lemma ret_run : ltac2:(TCodec.tc2 tcn__AsanMemset1K "Q?&=y5'QGyR0%211%5241'4y8%611%311p061'9&Nr2(QE+1(7%33@21%6251vQB%93@21':'8'G&Q0&O&Er4&QF&Q1&F+WD%3221%52N1r3vQC%;5:9321r1%=5<1C43%@3?31%M3Q33=%C221qS4Q51%F2Q61p0H1pNQ31pS2Q91").
Proof.
intros regs M H1. pclits. eexists. split.
- mret. apply mst_refl.
- reflexivity.
Qed.
End Walk.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
