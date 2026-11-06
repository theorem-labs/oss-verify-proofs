(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SumsLib Sums_codeK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__AsanMemIsZeroK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanMemIsZeroK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanMemIsZeroK.MEMISZERO."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SumsLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ZStores."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0C"; "1Some"; "1bool"; "1cons"; "1list"; "1nat"; "1nil"; "1option"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3repeat"]; ["4Z"; "5Segment"; "6store_ok"; "6word_to_le_bytes"; "7bvmap"; "0N"; "9dAB"; "9dAE"; "9mem1"; "8asan_mem_is_zero_entry"; "8asanreflect_fx"; "8memisz_clob"; "8memisz_clob'"; "8memisz_words"; ":wbytes"; ";msteps"]; ["<at_"; "<regs_agree"; "<regset"; "<ret_ok"; "=getr"; "=mkst"; "=rdn"; "=regupd"; "=v_andi"; ">code_at"; "?zeros"; "@loaded_segments"; "AIn"; "Badd"; "Bland"; "Ble"]; ["Blt"; "Bmin"; "Bmodulo"; "Bmul"; "Bof_nat"; "Bpow"; "Bsub"; "0a"; "0b"; "0base"; "0beg"; "0cnt"; "0d"; "0i"; "0j"; "0l"]; ["0l'"; "0m"; "0mem"; "0n"; "0p"; "0q"; "0r"; "0ra"; "0regs"; "0regs'"; "0ret"; "0rom"; "0segs"; "0sp"; "CBV"; "CZ_to_bv"]; ["Cbv"; "Cbv_unsigned"; "0v"; "0x"]]).
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition memisz_words : list (bv 32) :=
[W_103e8c; W_103e90; W_103e94; W_103e98; W_103e9c; W_103ea0; W_103ea4; W_103ea8;
W_103eac; W_103eb0; W_103eb4; W_103eb8; W_103ebc; W_103ec0; W_103ec4; W_103ec8;
W_103ecc; W_103ed0; W_103ed4; W_103ed8; W_103edc; W_103ee0; W_103ee4; W_103ee8;
W_103eec; W_103ef0; W_103ef4; W_103ef8; W_103efc; W_103f00; W_103f04; W_103f08;
W_103f0c; W_103f10; W_103f14; W_103f18; W_103f1c; W_103f20; W_103f24].
Definition memisz_clob : list reg := [10; 11; 12; 13; 14; 15; 16].
Definition memisz_clob' : list reg := [1; 2; 10; 11; 12; 13; 14; 15; 16].
Lemma land_m8 : ltac2:(TCodec.tc2 tcn__AsanMemIsZeroK "L'@':&Q?zr1%3221&Q@&QE+2+R0%3221%5271%;271';&Q>r2&QF+3%;2:1%3291%6251&QB+8%2281%8291%<3I51p0>1pS@K1").
Proof.
intros a Ha.
replace (2 ^ 64 - 2 ^ 3)%Z with (Z.ldiff (Z.ones 64) (Z.ones 3)).
2:{ rewrite Z.ldiff_land, <- Z.sub_land_same_l, Z.land_ones by lia.
rewrite Z.ones_mod_pow2 by lia. rewrite !Z.ones_equiv. lia. }
rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia.
rewrite Z.mod_small by lia.
rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
pose proof (Z.div_mod a (2 ^ 3) ltac:(lia)). change (2 ^ 3)%Z with 8%Z in *. lia.
Qed.
Lemma v_andi_m8 : ltac2:(TCodec.tc2 tcn__AsanMemIsZeroK "Q8'R@yR0%211'@':&Q?z&Q=&RAr2%2291r1%5221%8271&Q@&QE+2+R0%3221%5271%@271';&Q8&Q0r3%221@-8%5221&QF&QB%F2M6%H21F+8%4221%62I1%<2;1%?3Q291p0A1pSJQ31pS@Q51").
Proof.
intros a d Hd. unfold v_andi, at_. f_equal.
change (bv_wrap 64 (-8)) with (2 ^ 64 - 2 ^ 3)%Z.
rewrite u_Z2bv by lia. rewrite land_m8 by lia. lia.
Qed.
Lemma rdn_all1 : ltac2:(TCodec.tc2 tcn__AsanMemIsZeroK "R4'4'A%211'R@yR0%211'7y8%511%311p051'5&Q?&Q=&RAr2%22<1&QDr3%211%7241&QE+2+R0%3221%=251':r4%>2H1r1%@2J1%C231&Q@r5%A11%F271%4261%;261';%Q71O%Q211&Q6r8r7u1%4432N1(1(3(6%11Q9%33Q:G1%52<1%>3<71p0@1pU8QA1r6%?4=1MG&?%13QBQ8I%=2D1%F3D41p071p0Q51pSBQG1pS@QK1pT8QF1pT4QH1pTJR11").
Proof.
intros segs m n; induction n as [|n IH]; intros a b Hnw Hall; [reflexivity|].
pose proof (Hall a ltac:(lia)) as R. cbn [rdn repeat] in R |- *.
destruct (match m a with Some b0 => Some b0 | None => seg_rom segs a end) as [b0|]; [|discriminate].
injection R as ->.
destruct n as [|n'].
- reflexivity.
- assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
rewrite (IH (a + 1) b) by (rewrite Hu1; first [lia | intros x Hx; apply Hall; lia]).
reflexivity.
Qed.
Lemma regs_agree_upd_same : ltac2:(TCodec.tc2 tcn__AsanMemIsZeroK "Q7&Q2&Dy5'R@yR0%211%5241%415&Q1r5r4r3%43321';&Q4%1264r2%43<21&=(R>z(9%33D21%:3@=1%611r8r7&Q7r6%231DC%F3541p071p0?1p0E1pU6M1pT>L1pTDN1pTBO1p2Q61").
Proof.
intros C regs regs' r v AG Hv Hnz x Hx.
destruct (decide (x = r)) as [->|Hne].
- rewrite getr_same by exact Hnz. symmetry. exact Hv.
- rewrite getr_other by exact Hne. apply AG, Hx.
Qed.
Lemma regs_agree_strengthen : ltac2:(TCodec.tc2 tcn__AsanMemIsZeroK "Q:'4'R@y5%211%411&DyR0%611%3261&Q1&Q<r1r4%33:21qT>;1r2%73215r5%83?71&=r7%;3B61%311';&Q4r3%2291r6%4213%63F31p081p0=1pT>M1%G3NF=qT>O1%J31G:p041p0E1pTDN1pTBO1pT2Q41pT0Q51").
Proof.
intros l l' regs regs' AG E r Hr.
destruct (In_dec (fun x y : reg => decide (x = y)) r l') as [Hin|Hnin].
- apply E; assumption.
- apply AG, Hnin.
Qed.
Section MEMISZERO.
Variable segs : list Segment.
Variable base : word.
Variable mem : word -> option byte.
Variables beg sp : word.
Variable N : Z.
Variable rom : word -> option byte.
Hypothesis HCODE : code_at segs base 0 memisz_words.
Hypothesis HN : (0 <= N <= 2 ^ 40)%Z.
Hypothesis Hnw : (bv_unsigned beg + N + 8 <= 2 ^ 64)%Z.
Hypothesis Hsp : (16 <= bv_unsigned sp)%Z.
Hypothesis Hstk : store_ok segs mem (at_ sp (-8)) 8 = true.
Hypothesis Hdisj : (bv_unsigned beg + N <= bv_unsigned sp - 8 \/ bv_unsigned sp <= bv_unsigned beg)%Z.
Hypothesis Hz : forall a : word,
(bv_unsigned beg <= bv_unsigned a < bv_unsigned beg + N)%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0].
#[local] Abbreviation B := (bv_unsigned beg).
#[local] Abbreviation Z0 := (Z_to_bv 64 0).
#[local] Abbreviation CL := (fun r => In r memisz_clob').
Definition dAB : Z := 7 - (B + 7) mod 8.
Definition dAE : Z := N - (B + N) mod 8.
Definition mem1 (ra : word) : word -> option byte := wbytes mem (at_ sp (-8)) (word_to_le_bytes 8 ra).
Lemma dAB_range : ltac2:(TCodec.tc2 tcn__AsanMemIsZeroK "8':&Q?z&F%3221+7%5231%7231").
Proof. unfold dAB. pose proof (Z.mod_pos_bound (B + 7) 8 ltac:(lia)). lia. Qed.
Lemma dAE_range : ltac2:(TCodec.tc2 tcn__AsanMemIsZeroK "C':&Q?&QFvE+7%3221&G%6221%7225%9221z&Q=&RAyR0vQJ%3221%521:%@271%B291").
Proof.
unfold dAE. pose proof (u64_range beg). pose proof (Z.mod_pos_bound (B + N) 8 ltac:(lia)).
pose proof (Z.div_mod (B + N) 8 ltac:(lia)). nia.
Qed.
Lemma rd1 : ltac2:(TCodec.tc2 tcn__AsanMemIsZeroK "Q;'R@yR0%211'@':&Q?zr1%3221&Q@vE%2241%8241';'7'4y8%A11%311%511&Q6vR<&Hr3%211&Q0vQJr2%3221u1%:49621(1(3&R?%12BL(6%11C%53D31%72D1%J3D91p0L1pSNQ61pT@Q81").
Proof.
intros ra j Hj. pose proof (u64_range beg). pose proof (u64_range sp). unfold mem1.
rewrite rdn_wbytes_out; rewrite ?length_N_to_le_bytes, ?at_u; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; try lia.
apply Hz. rewrite at_u; lia.
Qed.
Lemma rd8 : ltac2:(TCodec.tc2 tcn__AsanMemIsZeroK "Q9'R@yR0%211'@&Q?zr1%3221&Q=r2+8%3221vE%9221';'7'4y8%B11%311%511&Q6vR<&Hr4%211&Q0vQJr3%3221u8%:49621(1&Q:%114%32@1%F3@51p0H1p0O1pSNQ41pT@Q61").
Proof.
intros ra j Hj H8. pose proof (u64_range beg). unfold zeros. apply rdn_all1; [rewrite at_u; cbn; lia|].
intros x Hx. rewrite at_u in Hx by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx.
replace x with (at_ beg (bv_unsigned x - B)).
- apply rd1. lia.
- unfold at_. rewrite <- (Z_to_bv_bv_unsigned 64 x) at 2. f_equal. lia.
Qed.
Lemma rd_ra : ltac2:(TCodec.tc2 tcn__AsanMemIsZeroK "K'R@yR0%211';'7'4y8%711%311%511&Q6vR<&Hr1%211&Q0vR=-8%3221u8%:49621(1&C%124:%32@1%F3@51pT@H1").
Proof. intros ra. unfold mem1. apply rdn_wbytes_hit8. pose proof (u64_range sp). rewrite at_u; lia. Qed.
Ltac get_code :=
let HC := fresh "HC" in
pose proof HCODE as HC; cbn [code_at memisz_words Z.add Pos.add Pos.succ] in HC;
destruct HC as (C0 & C4 & C8 & C12 & C16 & C20 & C24 & C28 & C32 & C36 & C40 & C44 & C48 & C52 & C56
& C60 & C64 & C68 & C72 & C76 & C80 & C84 & C88 & C92 & C96 & C100 & C104 & C108 & C112
& C116 & C120 & C124 & C128 & C132 & C136 & C140 & C144 & C148 & C152 & _).
Ltac mlbu F D :=
chain_step; [reflexivity
| eapply step_lbu with (b := Z_to_bv 8 0);
[exact F | reflexivity | exact D
| gres; rwH; imm_norm; rewrite ?at_addi; apply rd1; lia]
| step_simpl]; vn.
Ltac mld F D :=
chain_step; [reflexivity
| eapply step_ld with (bs := zeros 8) (v := Z_to_bv 64 0);
[exact F | reflexivity | exact D
| gres; rwH; imm_norm; rewrite ?at_addi; apply rd8; lia
| reflexivity]
| step_simpl]; vn.
Ltac ra_solve :=
repeat (first [ apply regs_agree_upd; [in_list|]
| apply regs_agree_upd_same; [| rwH; rewrite ?at_0; reflexivity | let X := fresh in intros X; discriminate X] ]);
first [apply regs_agree_refl | assumption].
Lemma fin_run : ltac2:(TCodec.tc2 tcn__AsanMemIsZeroK "R<&Dy5'R@yR0%211%5241&Q3r1%211';&Q4r3(R>+2(9%33>21%6251&Q0vR=-@%3221%<3A51r4+;%<3G1:%?231&R?z%22I1%D3I41'<':'OvR<&Q5&Jr6vQI+T<%F221&Hr5%211vR;%:598521%;5:Q6432%>3=21&Q1%Q>1Q?&Q<&L%233Q<1qT>41%631AQ>+:%Q;3QF1Q9%Q>2QA1+1%Q02QG1%QB3QG31%QB2QEQ=%QD3QI1Q;%QB3QM5Q@%QE2QH1%QG3QL1G%Q2241%Q3271%Q42>1%Q52F1qTDR01%Q82R11p0Q:1p0QC1p0R11pTFR61pTBR61").
Proof.
get_code. intros regs ret Hret H2 H11. pose proof (u64_range sp).
eexists. split; [|split; [|split; [|split]]].
- an C140 D_103f18.
chain_step; [reflexivity
| eapply step_ld with (v := ret);
[exact C144 | reflexivity | exact D_103f1c
| gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; apply rd_ra
| apply bytes_le_to_Z_8]
| step_simpl]; vn.
an C148 D_103f20.
aret C152 D_103f24 ret.
apply mst_refl.
- unfold memisz_clob'. solve_regs_agree.
- gres. reflexivity.
- gres. rewrite ?at_0. reflexivity.
- gres. reflexivity.
Qed.
Lemma ep_loop : ltac2:(TCodec.tc2 tcn__AsanMemIsZeroK "SB'5&Dy5'R@yR0%211%5241'@&Q3r3%211';&Q4r5(R>+2(9%33?21%6251&Q0vR=-@%3221%<3B51r6+;%<3H1:%?231&R?z%22J1%D3J41r7+<%D3Q01B%G231vQJ%B21H%K3Q131r8+>%K3Q71I%N231%?2Q7N%Q13Q721&Q?%12A>+1%321@&Q=r9%221<vE%8221&QDr=%211&QF%128;%Q@3QD31'<':'OvR<&Q5&Jr>vQI+SH%QB221&H%11@vR;%9587421r1%;5:1D43%>3=31&Q1%R;1R<&Q<&L%23371qT>41%631A9+:%R73RC1R5%R:2<1%QK2RCQ8%R=3RC21%R=2?R8%R?3RE1R6%R=3RIQ<R;%R@2B1%RB3RH1Q6%Q1241%Q2271%Q32=1%Q42E1qTDRL1%Q72RM1p0Q91p0Q@1p0QF1p0QI1p0QL1p0R31p0R;1p0RD1p0S21pSHS61pT<S71pTFS:1pTBS:1pSLSA1").
Proof.
get_code. pose proof (u64_range beg) as Hb.
induction i as [|i IH]; intros regs ret q cnt Hret H2 H11 H12 H14 Hq Hc Hqc Hi.
- eapply (runs_trans segs _ (fun r => mkst r (at_ base 140) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 11 = Z0 /\ regs_agree CL regs r)).
+ eexists. split.
* mlbu C120 D_103f04.
av C124 D_103f08 (Z_to_bv 64 (cnt - 1)) ltac:(unfold v_addi; unorm; f_equal; lia).
an C128 D_103f0c.
an C132 D_103f10.
ab_ft C136 D_103f14 ltac:(condz).
apply mst_refl.
* post. unfold memisz_clob'. solve_regs_agree.
+ cbv beta. intros r1 (R2 & R11 & AG).
destruct (fin_run r1 ret Hret R2 R11) as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
- eapply (runs_trans segs _ (fun r => mkst r (at_ base 120) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 11 = Z0 /\ getr r 12 = at_ beg (q + 1)
/\ getr r 14 = Z_to_bv 64 (cnt - 1) /\ regs_agree CL regs r)).
+ eexists. split.
* mlbu C120 D_103f04.
av C124 D_103f08 (Z_to_bv 64 (cnt - 1)) ltac:(unfold v_addi; unorm; f_equal; lia).
an C128 D_103f0c.
an C132 D_103f10.
ab_tk C136 D_103f14 ltac:(condz).
apply mst_refl.
* post. unfold memisz_clob'. solve_regs_agree.
+ cbv beta. intros r1 (R2 & R11 & R12 & R14 & AG).
destruct (IH r1 ret (q + 1)%Z (cnt - 1)%Z Hret R2 R11 R12 R14 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
Qed.
Lemma tail_run : ltac2:(TCodec.tc2 tcn__AsanMemIsZeroK "S1&Dy5'R@yR0%211%5241&Q3r1%211';&Q4r3(R>+2(9%33>21%6251&Q0vR=-@%3221%<3A51r4+:%<3G1:%?231vQJ%B3G21r5+;%B3M1@%E231&R?z%22O1%J3O41r6+<%J3Q51H%M231&G%H2?1%Q13Q631r7+>%Q13Q<1O%Q4231vE%O2F1%Q83Q=31'<':'OvR<&Q5&Jr9vQI+S<%Q:221&Hr8%211vR;%:598521%;5:QJ432%>3=21&Q1%R21R3&Q<&L%233R01qT>41%631AR2%R02R3QB+1%Q<2R91%R43R931%R42R7QO%R63R;1QM%R43R?5R2%R72R:1%R93R>1E%Q0241%Q1271%Q22<1%Q32D1qTDRB1%Q62RC1p0Q81p0Q@1p0QH1p0R11p0R81p0RF1pTFRK1pTBRK1").
Proof.
get_code. intros regs ret Hret H2 H10 H11 H12 H14.
pose proof (u64_range beg) as Hb. pose proof dAE_range as HdAE.
destruct (Z.lt_ge_cases dAE 0) as [Hneg|Hnn].
-
eapply (runs_trans segs _ (fun r => mkst r (at_ base 140) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 11 = Z0 /\ regs_agree CL regs r)).
+ eexists. split.
* ab_tk C108 D_103ef8 ltac:(rewrite <- (at_0 beg) at 2; condz).
apply mst_refl.
* post; apply regs_agree_refl.
+ cbv beta. intros r1 (R2 & R11 & AG).
destruct (fin_run r1 ret Hret R2 R11) as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
- destruct (Z.lt_ge_cases dAE N) as [Hlt|Hge].
+
eapply (runs_trans segs _ (fun r => mkst r (at_ base 120) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
/\ getr r 14 = Z_to_bv 64 (N - dAE) /\ regs_agree CL regs r)).
* eexists. split.
-- ab_ft C108 D_103ef8 ltac:(rewrite <- (at_0 beg) at 2; condz).
ab_ft C112 D_103efc ltac:(condz).
av C116 D_103f00 (Z_to_bv 64 (N - dAE)) ltac:(unfold v_sub, at_; unorm; f_equal; lia).
apply mst_refl.
-- post. unfold memisz_clob'. solve_regs_agree.
* cbv beta. intros r1 (R2 & R11 & R12 & R14 & AG).
destruct (ep_loop (Z.to_nat (N - dAE - 1)) r1 ret dAE (N - dAE) Hret R2 R11 R12 R14
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
+
eapply (runs_trans segs _ (fun r => mkst r (at_ base 140) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 11 = Z0 /\ regs_agree CL regs r)).
* eexists. split.
-- ab_ft C108 D_103ef8 ltac:(rewrite <- (at_0 beg) at 2; condz).
ab_tk C112 D_103efc ltac:(condz).
apply mst_refl.
-- post; apply regs_agree_refl.
* cbv beta. intros r1 (R2 & R11 & AG).
destruct (fin_run r1 ret Hret R2 R11) as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
Qed.
Lemma w_loop : ltac2:(TCodec.tc2 tcn__AsanMemIsZeroK "SO'5&Dy5'R@yR0%211%5241'@&Q3r2%211';&Q4r4(R>+2(9%33?21%6251&Q0vR=-@%3221%<3B51r5+:%<3H1:%?231vQJ%B3H21r6+;%B3N1@%E231&R?z%22Q01%J3Q041r7+<%J3Q61H%M231&G%H2?1%Q13Q731r8+>%Q13Q=1O%Q4231vE%O2F1%Q83Q>31r9+?%Q83QD1Q6%Q;231%Q52LB%Q>3QD21&Q?%12H>&Q=+8%22:1%521E&QC&QDr=%211%4217&QFr:%22M1%321;%QN3R251'<':'OvR<&Q5&Jr>vQI+RL%R0221&H%11CvR;%9587421r1%;5:1G43%>3=31&Q1%RI1RJ&Q<&L%23371qT>41%631A9%RF2:R8+1%R22S01%RJ3S031%RJ2>RE%RL3S21RC%RJ3S65RH%RM2A1%RO3S51Q8%Q0241%Q1271%Q22<1%Q32D1qTDS91%Q62S:1p0Q81p0QC1p0QH1p0QK1p0R21p0R:1p0RB1p0RK1p0S21p0S@1pT:SD1pTFSG1pTBSG1pSLSN1").
Proof.
get_code. pose proof (u64_range beg) as Hb. pose proof dAE_range as HdAE.
induction i as [|i IH]; intros regs ret p Hret H2 H10 H11 H12 H14 H15 Hp Hp8 Hi.
- eapply (runs_trans segs _ (fun r => mkst r (at_ base 108) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
/\ getr r 14 = at_ beg N /\ regs_agree CL regs r)).
+ eexists. split.
* mld C92 D_103ee8.
an C96 D_103eec.
an C100 D_103ef0.
ab_ft C104 D_103ef4 ltac:(condz).
apply mst_refl.
* post. unfold memisz_clob'. solve_regs_agree.
+ cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & AG).
destruct (tail_run r1 ret Hret R2 R10 R11 R12 R14) as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
- eapply (runs_trans segs _ (fun r => mkst r (at_ base 92) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
/\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg (p + 8) /\ regs_agree CL regs r)).
+ eexists. split.
* mld C92 D_103ee8.
an C96 D_103eec.
an C100 D_103ef0.
ab_tk C104 D_103ef4 ltac:(condz).
apply mst_refl.
* post. unfold memisz_clob'. solve_regs_agree.
+ cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & R15 & AG).
destruct (IH r1 ret (p + 8)%Z Hret R2 R10 R11 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(lia))
as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
Qed.
Lemma mid_run : ltac2:(TCodec.tc2 tcn__AsanMemIsZeroK "S9&Dy5'R@yR0%211%5241&Q3r1%211';&Q4r3(R>+2(9%33>21%6251&Q0vR=-@%3221%<3A51r4+:%<3G1:%?231vQJ%B3G21r5+;%B3M1@%E231&R?z%22O1%J3O41r6+<%J3Q51H%M231&G%H2?1%Q13Q631r7+>%Q13Q<1O%Q4231vE%O2F1%Q83Q=31r8+?%Q83QC1Q6%Q;231&F%Q62M1%Q?3QD31'<':'OvR<&Q5&Jr:vQI+RH%QA221&Hr9%211vR;%:598521%;5:R1432%>3=21&Q1%R91R:&Q<&L%233R71qT>41%631AR9%R72R:QI+1%QC2R@1%R;3R@31%R;2R>R6%R=3RB1R4%R;3RF5R9%R>2RA1%R@3RE1E%Q0241%Q1271%Q22<1%Q32D1qTDRI1%Q62RJ1p0Q81p0Q@1p0QH1p0R01p0R91p0R@1p0RN1pTFS31pTBS31").
Proof.
get_code. intros regs ret Hret H2 H10 H11 H12 H14 H15.
pose proof (u64_range beg) as Hb. pose proof dAE_range as HdAE. pose proof dAB_range as HdAB.
destruct (Z.lt_ge_cases dAB dAE) as [Hlt|Hge].
-
assert (Hi : exists i : nat, (Z.of_nat i * 8 = dAE - dAB - 8)%Z).
{ unfold dAB, dAE in *.
pose proof (Z.div_mod (B + 7) 8 ltac:(lia)). pose proof (Z.div_mod (B + N) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (B + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (B + N) 8 ltac:(lia)).
exists (Z.to_nat ((B + N) / 8 - (B + 7) / 8 - 1)). nia. }
destruct Hi as (i & Hi).
eapply (runs_trans segs _ (fun r => mkst r (at_ base 92) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
/\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB /\ regs_agree CL regs r)).
+ eexists. split.
* ab_ft C88 D_103ee4 ltac:(condz).
apply mst_refl.
* post; apply regs_agree_refl.
+ cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & R15 & AG).
destruct (w_loop i r1 ret dAB Hret R2 R10 R11 R12 R14 R15 ltac:(lia) ltac:(lia) Hi)
as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
- eapply (runs_trans segs _ (fun r => mkst r (at_ base 108) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
/\ getr r 14 = at_ beg N /\ regs_agree CL regs r)).
+ eexists. split.
* ab_tk C88 D_103ee4 ltac:(condz).
apply mst_refl.
* post; apply regs_agree_refl.
+ cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & AG).
destruct (tail_run r1 ret Hret R2 R10 R11 R12 R14) as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
Qed.
Lemma pro_loop : ltac2:(TCodec.tc2 tcn__AsanMemIsZeroK "T:'5&Dy5'R@yR0%211%5241'@&Q3r2%211';&Q4r4(R>+2(9%33?21%6251&Q0vR=-@%3221%<3B51r5+:%<3H1:%?231vQJ%B3H21r6+;%B3N1@%E231&R?z%22Q01%J3Q041r7+<%J3Q61H%M231&G%H2?1%Q13Q731r8+=%Q13Q=1O%Q4231&Q=+1%22E1%Q12H1%Q:3Q@51r9+>%Q:3QF1Q8%Q=231vE%Q82O1%QA3QG31r:+?%QA3QM1Q?%QD231&F%Q?2Q61%QH3QN31&Q?%12Q2?&Q@%12:6r;%321?&QDr?%211&QF&QA%12>E%321Nr<%5221%R83R<71'<':'OvR<&Q5&Jr@vQI+R0%R:221&H%11DvR;%9587421r1%;5:1H43%>3=31&Q1%S31S4&Q<&L%23371qT>41%631A9%S02:RB%R;2S9QK%S33S921%S32=RN%S53S;1RL%S33S?QOS1%S62@1%S83S>1Q8%O241%Q0271%Q12;1%Q22C1qTDSB1%Q52SC1p0Q71p0QB1p0QE1p0QH1p0QK1p0R31p0R;1p0RE1p0RM1p0S61p0S=1p0SK1pSNSO1pTFT21pTBT21pSLT91").
Proof.
get_code. pose proof (u64_range beg) as Hb. pose proof dAE_range as HdAE. pose proof dAB_range as HdAB.
induction i as [|i IH]; intros regs ret j Hret H2 H10 H11 H12 H13 H14 H15 Hj HjA HjN Hi.
-
destruct (Z.eq_dec (j + 1) dAB) as [HA|HA].
+ eapply (runs_trans segs _ (fun r => mkst r (at_ base 88) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
/\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB /\ regs_agree CL regs r)).
* eexists. split.
-- an C64 D_103ecc.
mlbu C68 D_103ed0.
an C72 D_103ed4.
ab_tk C76 D_103ed8 ltac:(condz).
apply mst_refl.
-- post. unfold memisz_clob'. solve_regs_agree.
* cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & R15 & AG).
destruct (mid_run r1 ret Hret R2 R10 R11 R12 R14 R15) as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
+ eapply (runs_trans segs _ (fun r => mkst r (at_ base 88) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
/\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB /\ regs_agree CL regs r)).
* eexists. split.
-- an C64 D_103ecc.
mlbu C68 D_103ed0.
an C72 D_103ed4.
ab_ft C76 D_103ed8 ltac:(condz).
an C80 D_103edc.
ab_ft C84 D_103ee0 ltac:(condz).
apply mst_refl.
-- post. unfold memisz_clob'. solve_regs_agree.
* cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & R15 & AG).
destruct (mid_run r1 ret Hret R2 R10 R11 R12 R14 R15) as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
- eapply (runs_trans segs _ (fun r => mkst r (at_ base 64) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
/\ getr r 13 = at_ beg (j + 1 + 1) /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB
/\ regs_agree CL regs r)).
+ eexists. split.
* an C64 D_103ecc.
mlbu C68 D_103ed0.
an C72 D_103ed4.
ab_ft C76 D_103ed8 ltac:(condz).
an C80 D_103edc.
ab_tk C84 D_103ee0 ltac:(condz).
apply mst_refl.
* post. unfold memisz_clob'. solve_regs_agree.
+ cbv beta. intros r1 (R2 & R10 & R11 & R12 & R13 & R14 & R15 & AG).
destruct (IH r1 ret (j + 1)%Z Hret R2 R10 R11 R12 R13 R14 R15 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
Qed.
Theorem mem_is_zero_run : ltac2:(TCodec.tc2 tcn__AsanMemIsZeroK "RE&Dy5'R@yR0%211%5241&Q3r1%211';&Q4r3(R>+1(9%33>21%6251r2%93>21r4+2%93D17%<231vR=%?3D21r5+:%?3J1=%B231vQJ%E3J21r6+;%E3Q01C%H231&R?vE%22Q21%M3Q241'<':'OvR<&Q5&Jr8&Q0vQIz%3221vR2vR;%9587321r7&H%112%=5<QA315%@3?51&Q1%QI1QJ&Q<&K%233QG1qT>41%631CQI%QG2QJQ6%O2QOQE%QJ3QO21%QJ2QMQ?%QL3R11Q>%QL2QOQG%QN3R31B%Q0231%Q1261%Q22:1%Q32B1qTDR71%Q62R81p0Q81p0QA1p0QH1p0QO1p0R:1pTFR?1pTBR?1").
Proof.
get_code. intros regs ret Hret H1 H2 H10 H11.
pose proof (u64_range beg) as Hb. pose proof (u64_range sp) as Hs.
pose proof dAE_range as HdAE. pose proof dAB_range as HdAB.
eapply (runs_trans segs _ (fun r => mkst r (at_ base 48) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
/\ getr r 13 = Z_to_bv 64 N /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB
/\ regs_agree CL regs r)).
{ eexists. split.
- an C0 D_103e8c.
chain_step; [reflexivity
| eapply step_sd_at with (a := at_ sp (-8)) (v := ret);
[exact C4 | reflexivity | exact D_103e90
| gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; reflexivity
| gres; rwH; reflexivity
| exact Hstk]
| step_simpl]; change (wbytes mem (at_ sp (-8)) (word_to_le_bytes 8 ret)) with (mem1 ret); vn.
an C8 D_103e94.
an C12 D_103e98.
an C16 D_103e9c.
an C20 D_103ea0.
ab_ft C24 D_103ea4 ltac:(condz).
an C28 D_103ea8.
av C32 D_103eac (at_ beg N) ltac:(apply v_add_at; lia).
an C36 D_103eb0.
av C40 D_103eb4 (at_ beg dAB) ltac:(rewrite v_andi_m8 by lia; unfold dAB; f_equal; lia).
av C44 D_103eb8 (at_ beg dAE) ltac:(rewrite v_andi_m8 by lia; unfold dAE; reflexivity).
apply mst_refl.
- post. unfold memisz_clob'. solve_regs_agree. }
cbv beta. intros r0 (R2 & R10 & R11 & R12 & R13 & R14 & R15 & AG0).
enough (G : exists regs',
msteps segs (mkst r0 (at_ base 48) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
/\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret).
{ destruct G as (r' & RUN & AG & P10 & P2 & P1). exists r'. split; [exact RUN|]. split; [|repeat split; assumption].
apply (regs_agree_strengthen memisz_clob memisz_clob'); [exact AG|].
intros r Hr Hnr. unfold memisz_clob', memisz_clob in *. cbn [In] in Hr.
destruct Hr as [<-|[<-|Hr]]; [rewrite P1, H1; reflexivity | rewrite P2, H2; reflexivity |].
exfalso. apply Hnr. cbn [In]. tauto. }
destruct (Z.eq_dec dAB 0) as [HA0|HA0].
-
eapply (runs_trans segs _ (fun r => mkst r (at_ base 88) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
/\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB /\ regs_agree CL regs r)).
+ eexists. split.
* ab_tk C48 D_103ebc ltac:(rewrite <- (at_0 beg) at 1; condz).
apply mst_refl.
* post; exact AG0.
+ cbv beta. intros r1 (S2 & S10 & S11 & S12 & S14 & S15 & AG).
destruct (mid_run r1 ret Hret S2 S10 S11 S12 S14 S15) as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
- destruct (Z.eq_dec N 0) as [HN0|HN0].
+
eapply (runs_trans segs _ (fun r => mkst r (at_ base 88) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
/\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB /\ regs_agree CL regs r)).
* eexists. split.
-- ab_ft C48 D_103ebc ltac:(rewrite <- (at_0 beg) at 1; condz).
ab_tk C52 D_103ec0 ltac:(condz).
apply mst_refl.
-- post; exact AG0.
* cbv beta. intros r1 (S2 & S10 & S11 & S12 & S14 & S15 & AG).
destruct (mid_run r1 ret Hret S2 S10 S11 S12 S14 S15) as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
+
eapply (runs_trans segs _ (fun r => mkst r (at_ base 64) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
/\ getr r 13 = at_ beg (0 + 1) /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB
/\ regs_agree CL regs r)).
* eexists. split.
-- ab_ft C48 D_103ebc ltac:(rewrite <- (at_0 beg) at 1; condz).
ab_ft C52 D_103ec0 ltac:(condz).
an C56 D_103ec4.
an C60 D_103ec8.
apply mst_refl.
-- post. unfold memisz_clob'. ra_chain.
* cbv beta. intros r1 (S2 & S10 & S11 & S12 & S13 & S14 & S15 & AG).
destruct (pro_loop (Z.to_nat (Z.min dAB N - 1)) r1 ret 0 Hret S2 S10 S11 S12 S13 S14 S15
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
Qed.
End MEMISZERO.
Lemma slot_at : ltac2:(TCodec.tc2 tcn__AsanMemIsZeroK "G'R@yR0%211&Q?+@&RAr1%2261%5241';&Q0r2-8%3221&R?&QF%;2?5+8%3221%52B1%;3B71p0=1pTLD1").
Proof. intros sp Hsp. unfold at_. f_equal; lia. Qed.
Theorem mem_is_zero_summary : ltac2:(TCodec.tc2 tcn__AsanMemIsZeroK "U?'4'A%211'R@yR0%211'7y8%511%311p051'@&Dy5%2219&Q9r9r8z&M%544321':&Q?r5%2261&QE+2+Q8%3221%7261%9261&Q=&RA%12M@r6%4221+8%6221+R0%>2=1%B231+@%D219';'2&Br=r;&R?&QF%B2Q>Q2%221?%42Q@1u8%948721(8%=3<21'>%J2QF;%L21Q;r:%M2QI1%=21J%Q9241%Q:236%8221%Q22QNDr1%Q42R01%Q?231&Q@%Q825H%2241%QD241%R:1R2%R511&Q6rAr?r2u1%544321(1(3%Q42R=R2(6%11R>%43R?31%62>1%Q>3>81p0A1pS@RF1&Q3%11R<&Q4(R>+1(9%33RE21%52Q71%QI3RO1RD%63RHR;4%82QG1r>%QM3S321r<+:%<3RN1:%>231r@%R33S921+;%A3S31?%C2R31%R22S>Q4%R83S>21'<'OrF&Q5&JrErD%453Q=21>&NrB%RN2SJ1%R>21RK%R@2SL1&C%12R=K%73931%=5<R1M1G%@3?:1&Q1%T41SJ&Q<&K%233R71qT>41%631QNR9%Q?2R:Q2%RN2T:Q>%S43T:21%QB2R=Q;%S63T<1D%QD2R?Q@%S83T>1Q<%SO231%T0261%T12:1%T22B1qTDT:1%Q52T;1p0Q71p0Q=1p0QD1p0QI1p0R11p0R41p0RO1p0S91p0SH1p0SK1p0T61p0TA1pTFU11pTBTI1pTHTN1pQ<TN1pTLU51pSFU61pT6U21pSDU81pTJU<1").
Proof.
intros segs base mem beg sp N rom regs ret HC HN Hnw Hsp Hstk Hdisj Hz.
rewrite <- (slot_at sp Hsp) in Hstk |- *. rewrite <- (at_0 base).
apply (mem_is_zero_run segs base mem beg sp N rom HC HN Hnw Hsp Hstk Hdisj Hz).
Qed.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
Definition asan_mem_is_zero_entry : word := 0x8b054.
Lemma asan_mem_is_zero_code : ltac2:(TCodec.tc2 tcn__AsanMemIsZeroK "6&Q9&Q;&Iz&M%544321").
Proof. unfold memisz_words. code_at_vm. Qed.
Theorem asan_mem_is_zero : ltac2:(TCodec.tc2 tcn__AsanMemIsZeroK "U6'R@yR0%211'7y8%511%311p051'@&Dy5%2219':&Q?zr4%3221&QE+2+Q8%3221%8261%:261&Q=&RAr7%22I1r5%5221+8%7221+R0%?2>1%D231+@%F219';'2&B&Q;r:&R?&QFr8%D2Q;1%321@%52Q=1u8%:49821(8%>3=21'>%L2QC<%N21:r9%O2QF1%>21K%Q<241%Q=236%8221r<%Q52QL1r1%Q72QN1%QC231&Q@%Q;25J%2241%QH241'4%11R1%R411&Q6r>r2u1%44Q5321(1(3%Q62R;R1(6%11R<%43R=31%62=1%Q@3=81p0A1pS@RD1&Q3%11QO&Q4(R>+1(9%33RC21%52Q81%QK3RM1QD%63RFR>4%82QI1r=%QO3S121r;+:%<3RL1:%>231r?%R53S721+;%A3S11?%C2Q@1%R42S<Q4%R:3S<21'<'O&Q5&J&IrC%453Q<21=&NrA%S02SG1%R?21RL%RA2SI1&C%12R=J%73931%=5<R0L1F%?3RH:1&Q1%T11SG&Q<&K%233R61qT>41%631QMR8%Q>2R9Q1%RO2T7Q=%S53T721%QA2R<Q:%S73T91D%QC2R>Q?%S93T;1Q;%T2231%T3261%T42:1%T52B1qTDT71%Q42T81p0Q61p0Q<1p0QC1p0QH1p0R01p0R31p0RO1p0S91p0SI1p0SL1p0T81pTFTM1pTBTE1pTHTJ1pQ<TJ1pTLU11pSFU21pT6TN1").
Proof.
intros mem beg sp N rom regs ret.
apply (mem_is_zero_summary _ _ mem beg sp N rom regs ret asan_mem_is_zero_code).
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
