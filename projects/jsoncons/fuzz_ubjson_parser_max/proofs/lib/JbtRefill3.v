(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac JbtLeaf JbtAllocG JbtCachePop JbtCombAlloc JbtCombAllocHit JbtClassId JbtFree1 JbtRefill1 JbtRefill2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtRefill3 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "3Z"; "4bvmap"; "0M"; "5Wn"; "5apart"; "5cell"; "5wok"; "5wr"; "6msteps"; "7ret_ok"]; ["8getr"; "8mkst"; "8regupd"; "8v_srliw"; "9loaded_segments"; ":add"; ":div"; ":le"; ":lt"; ":modulo"; ":mul"; ":pow"; ":sub"; "0al"; "0c"; "0ca"]; ["0ch"; "0cnt"; "0csz"; "0fx"; "0g8"; "0g9"; "0ia"; "0k"; "0mc"; "0n"; "0pcp"; "0r"; "0raw"; "0regs"; "0regs'"; "0rom"]; ["0sp"; "0spb"; "0st"; ";BV"; ";Z_to_bv"; ";bv"; ";bv_unsigned"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Set Printing Depth 1000000. Set Printing Width 10000.
Ltac showst := lazymatch goal with |- msteps _ (mkst ?R ?P ?MM _) _ => idtac "REGS" R; idtac "PC" P; idtac "MEM" MM | |- ?G => idtac "GOAL" G end; fail "SHOWST".
Ltac zlhu F D a HYP :=
chain_step; [reflexivity | eapply step_lhu; [exact F | reflexivity | exact D | zaddr a; exact HYP | apply art_bytes2; lia ] | step_simpl; vnorm].
Lemma art_srliw_small : ltac2:(TCodec.tc2 tcn__JbtRefill3 "Q0'6'2&Gzr2%3221&H&K+2+O%3221%5271%;271'3'QEyR0%211&C&QDr4%2251r3%5221&F%A2@3%2261%82;1%>3;51p0G1p0A1pR@N1pS@O1").
Proof.
intros x k Hx Hk. unfold v_srliw. rewrite art_u_lit by lia. f_equal.
unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). rewrite (Z.mod_small x) by lia. rewrite Z.shiftr_div_pow2 by lia.
assert (0 <= x / 2 ^ k <= x). { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. rewrite <- (Z.mul_1_l x) at 1. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.pow_le_mono_r with (b := 0) || idtac; pose proof (Z.pow_pos_nonneg 2 k); lia. }
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32). rewrite Z.mod_small by lia. lia.
Qed.
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_refill_a_fn := (ltac2:(TCodec.tc2 tcn__JbtRefill3 "V6&7y5'QEyR0%211%5241'0y8%611%311p061'6'3&@r9(QC+1(1%33A21%6251r6%93A21r:+2%93G17%<231&QD%12H7%@3H31r;+:%@3N1>%C231%E3M16r<+;%E3Q31C%H231&Er7&J+R@%221F%5241%B2Q91%Q13Q981r=+<%Q13Q?1O%Q4231%Q63Q>1Gr>+=%Q63QD1Q4%Q9231r8%N2QE1%Q=3QE31&G+Q0%221O&H&K+R0%22Q91%42O1+Vb\P0%M218%:21F+TP0%<21H%Q12D2%;218'2%@2QJG+O%B2I1%4231z%E21L%C2M@%8221%H2QKO+@%J2Q11%<231&:&LrC%221NrB%542Q01F&=&DrGrD%921Q5%54431Q6&;rH%QL2QK<%QO261+4%R1221u4rA%85=7321'>&AvQ3rJ+ZkZL%S13S=1RO/01S=rI%756521@&B+Zk\L%S73SC1S5/01SC%43:S61rF%Q321QO%S12SH1%834S41+8%S?3SM1S=rE%RH2RGQ1%RK221%S82SO1%?3751+9%SF3T41SD&F%12Q=S@%S>2T51%E3641%S@2T7QB%G32S<1+R`0%S72>1%SD2T;1%K34S;1%SF2T=QA%M32S11%S<2AQO%SI2T@1%Q033RO1+>%T73TE1T5%Q3331?+ZkbL%T:3TF1T8/01TF&9u8%R62Q4Q0&QF%12TLR1%544Q>31%R:2Q8R>%TE2QDQ4%52U01%948431+H%R?2Q=1%TJ2QIQ2%:2U51%>4=531%QN5QMC@1R7%R03R>QH1p0R21p0R<1p0RC1p0RJ1p0RO1p0S41p0S:1p0S=1p0S@1p0SD1p0SJ1p0SN1p0T61p0T<1p0TI1p0TO1p0U71pRBUB1pR>UC1pQNUD1pR0UE1pS2UF1pRJUN1pS0UI1pBUJ1pRLV01")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_refill_a_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_refill_a_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_refill_a_fn) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_refill_a_fn) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_refill_a_fn) 4%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_refill_a_fn) 5%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_refill_a_fn) 6%nat 0%nat).
Variable ia : ltac:(sec_ty2 constr:(SEC_T_art_refill_a_fn) 7%nat 0%nat).
Variable mc : ltac:(sec_ty2 constr:(SEC_T_art_refill_a_fn) 8%nat 0%nat).
Lemma art_refill_a_fn : ltac:(sec_stmt2 constr:(SEC_T_art_refill_a_fn) 9%nat 0%nat).
Proof using Type regs M rom raw sp ca c ia mc.
intros H1 H2 H10 H11 H12 H13 Hsp Hsp' IMG Hca Hca' Hc Hia Hmc A W Cmc.
zstep (ltac:(oF' 0x56d5c%Z)) (ltac:(oD' 0x56d5c%Z)).
zsd (ltac:(oF' 0x56d60%Z)) (ltac:(oD' 0x56d60%Z)) (sp - 8) (U raw) ltac:(rewok W). zsd (ltac:(oF' 0x56d64%Z)) (ltac:(oD' 0x56d64%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W). zsd (ltac:(oF' 0x56d68%Z)) (ltac:(oD' 0x56d68%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W).
zstep (ltac:(oF' 0x56d6c%Z)) (ltac:(oD' 0x56d6c%Z)). zstep (ltac:(oF' 0x56d70%Z)) (ltac:(oD' 0x56d70%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmc' : cellA X (ca + 80 * c + 4) 4 mc) by (unfold apart in A; zcell) end.
zlw (ltac:(oF' 0x56d74%Z)) (ltac:(oD' 0x56d74%Z)) (ca + 80 * c + 4) Cmc'.
zbft (ltac:(oF' 0x56d78%Z)) (ltac:(oD' 0x56d78%Z)).
stepn (ltac:(oF' 0x56d7c%Z)) (ltac:(oD' 0x56d7c%Z)). rwH. rewrite art_srliw_small by lia. change (2 ^ 1) with 2.
zstep (ltac:(oF' 0x56d80%Z)) (ltac:(oD' 0x56d80%Z)). zstep (ltac:(oF' 0x56d84%Z)) (ltac:(oD' 0x56d84%Z)). zstep (ltac:(oF' 0x56d88%Z)) (ltac:(oD' 0x56d88%Z)). zstep (ltac:(oF' 0x56d8c%Z)) (ltac:(oD' 0x56d8c%Z)). zstep (ltac:(oF' 0x56d90%Z)) (ltac:(oD' 0x56d90%Z)). zstep (ltac:(oF' 0x56d94%Z)) (ltac:(oD' 0x56d94%Z)).
stepn (ltac:(oF' 0x56d98%Z)) (ltac:(oD' 0x56d98%Z)).
zret.
Qed.
End SE.
#[using="Type"] Lemma art_refill_b_fn : ltac2:(TCodec.tc2 tcn__JbtRefill3 "TD&7y5'QEyR0%211%5241'0y8%611%311p061'6'3&@r9(QC+2(1%33A21%6251&QD&Lr5+Q0%3221%52F1%>3F71r:+8%>3L1<%A231%;2L9%D3L21r;+9%D3Q21B%G231%I3Q116r<+:%I3Q71G%L231+1%G2Q81%Q03Q831&G%12GQ0&H&K+R0%22Q21%42H1+TP0%821J&E+R@%22G1%:217'2z%?21K+O%>2Q>1%@2N1%6241&?r?%211%G29N%F2OC%<221&:rA%QD21QBr@%442QD1D&=&DrE+4%443281&;rFrC%QO21QHu8&QFrD%22RE1%85<7541rG+@%R7251%<5@318ErH+H%R;2B1%@5D31<I'>&AvQ3rJ+Zk\L%RH3S41RF/01S4rI%756521<&B%RM3S;R2RK%2381C%RJ2S;L%432RM1%RL2S=M%632RD1rB%RO2S@1%933RA1&9u4%241>Q9Q0%E5D4N1J%G3Q<?1p0I1p0N1p0Q31p0Q=1p0QC1p0QI1p0QJ1p0QN1p0R21p0R:1p0R?1p0RB1p0RH1p0RK1p0S31p0S91p0S@1pR<T01pR:T11pRDT21pRFT31pS2T41pRJT<1pS0T71pBT81pRLT>1").
Proof.
intros regs M rom raw sp pcp n g8 g9 H2 H8 H9 H10 Hsp Hsp' Hp Hp' Hn Hret Hg8 Hg9 A W C8 C16 C24.
zbft (ltac:(oF' 0x56d9c%Z)) (ltac:(oD' 0x56d9c%Z)).
zsw (ltac:(oF' 0x56da0%Z)) (ltac:(oD' 0x56da0%Z)) pcp n ltac:(rewok W).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C8' : cellA X (sp - 8) 8 (U raw)) by (unfold apart in A; zcell); assert (C16' : cellA X (sp - 16) 8 g8) by (unfold apart in A; zcell);
assert (C24' : cellA X (sp - 24) 8 g9) by (unfold apart in A; zcell) end.
zld (ltac:(oF' 0x56da4%Z)) (ltac:(oD' 0x56da4%Z)) (sp - 8) C8'. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x56da8%Z)) (ltac:(oD' 0x56da8%Z)) (sp - 16) C16'. zld (ltac:(oF' 0x56dac%Z)) (ltac:(oD' 0x56dac%Z)) (sp - 24) C24'.
zstep (ltac:(oF' 0x56db0%Z)) (ltac:(oD' 0x56db0%Z)).
stepret (ltac:(oF' 0x56db4%Z)) (ltac:(oD' 0x56db4%Z)) raw ltac:(rwH; reflexivity).
zret.
Qed.
Section SE.
Local Abbreviation SEC_T_art_miss_a_fn := (ltac2:(TCodec.tc2 tcn__JbtRefill3 "T;&7y5'QEyR0%211%5241'0y8%611%311p061'6'3&@r7(QC+8(1%33A21%6251&QDr4%22C1%;3C41r8+:%;3I19%>231r3%92J1%B3J31r9+;%B3Q01@%E231r5%@2Q11%I3Q131r:+=%I3Q71G%L231%N3Q61D'2&G+1%221F+O%42H1%6231z%721K&H&E+TP0%22H1&K+2+R0%3221%8251%A2;N%:2O3%D221&;&Dr?r<&J+R@r=%3221%C251u4%:59821H'>&AvQ3rA+Zim0%R13R=1QO/01R=r@%756521A&B%R63RDQ8R4+ZjUL%R83RD1R6/01RD%53;41+9%R<3RJ1R:r>%I2H1%Q92H1%R;2RL1%<3751%R=2RNK%>32R81%?31R24+<%RF3S41RD%RB2S3Q3%C3421%RD2S5<%E32R11+B%RL3S:1RJr;%RI2S:1%J3531+C%S13S?1RO%M331@+D%S43SB1S2%Q0331>+ZkZL%S73SC1S5/01SC%Q<5Q;41Q6QF%Q>3QHQ61p0Q@1p0QL1p0QM1p0R11p0R;1p0R>1p0RF1p0RL1p0S41p0S<1pQLSI1pR>SJ1pR0SK1pQNSL1pS0SN1pBSO1pRLT51")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_miss_a_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_miss_a_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_miss_a_fn) 2%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_miss_a_fn) 3%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_miss_a_fn) 4%nat 0%nat).
Variable ia : ltac:(sec_ty2 constr:(SEC_T_art_miss_a_fn) 5%nat 0%nat).
Variable al : ltac:(sec_ty2 constr:(SEC_T_art_miss_a_fn) 6%nat 0%nat).
Lemma art_miss_a_fn : ltac:(sec_stmt2 constr:(SEC_T_art_miss_a_fn) 7%nat 0%nat).
Proof using Type regs M rom c ca ia al.
intros H8 H10 H11 H13 Hc Hca Hca' Hia Hal Ccnt.
zbft (ltac:(oF' 0x567a0%Z)) (ltac:(oD' 0x567a0%Z)).
zstep (ltac:(oF' 0x567a4%Z)) (ltac:(oD' 0x567a4%Z)).
zbft (ltac:(oF' 0x567a8%Z)) (ltac:(oD' 0x567a8%Z)).
zstep (ltac:(oF' 0x567ac%Z)) (ltac:(oD' 0x567ac%Z)). zstep (ltac:(oF' 0x567b0%Z)) (ltac:(oD' 0x567b0%Z)). zstep (ltac:(oF' 0x567b4%Z)) (ltac:(oD' 0x567b4%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Ccnt' : cellA X (ca + c * 80) 4 0) by (replace (ca + c * 80) with (ca + 80 * c) by lia; exact Ccnt) end.
zlw (ltac:(oF' 0x567b8%Z)) (ltac:(oD' 0x567b8%Z)) (ca + c * 80) Ccnt'.
zbtk (ltac:(oF' 0x567bc%Z)) (ltac:(oD' 0x567bc%Z)).
zstep (ltac:(oF' 0x5689c%Z)) (ltac:(oD' 0x5689c%Z)). zstep (ltac:(oF' 0x568a0%Z)) (ltac:(oD' 0x568a0%Z)). zstep (ltac:(oF' 0x568a4%Z)) (ltac:(oD' 0x568a4%Z)). zstep (ltac:(oF' 0x568a8%Z)) (ltac:(oD' 0x568a8%Z)). zstep (ltac:(oF' 0x568ac%Z)) (ltac:(oD' 0x568ac%Z)). zstep (ltac:(oF' 0x568b0%Z)) (ltac:(oD' 0x568b0%Z)). zstep (ltac:(oF' 0x568b4%Z)) (ltac:(oD' 0x568b4%Z)).
stepn (ltac:(oF' 0x568b8%Z)) (ltac:(oD' 0x568b8%Z)).
zret.
Qed.
End SE.
#[using="Type"] Lemma art_miss_b_fn : ltac2:(TCodec.tc2 tcn__JbtRefill3 "SF&7y5'QEyR0%211%5241'0y8%611%311p061'6'3&@r8(QC+:(1%33A21%6251&QD+1%22C1%;3C41r9+9%;3I19%>231r6%92J1%B3J31r:+B%B3Q01@%E231r5%@2Q11%I3Q131r;+C%I3Q71G%L231%N3Q616r<+D%N3Q<1L%Q1231%Q33Q;1;&Gz%221C&H&E+R@%22@1&K+2+R0%3221%8251'2%=2Q8G+O%8271%=2J1%5241&;&Dr?r=u4%554321L'>&AvQ3rA+ZjUL%QN3R:1QL/01R:r@%756521<&B%QN2R?QC%238R11+;%R63RD1R4%R22RCQ@%63421+<%R:3RH1R8%R62RGE%:3421+=%R>3RL1R<%R:2RKQC%>3421+Zin0%RB3RN1R@/01RN%J5I41DO%L3Q1D1p0N1p0Q51p0Q<1p0QF1p0QJ1p0R01p0R61p0R>1p0RF1pR>S31pR0S41pQLS51pRDS61pRFS71pS0S91pBS:1pRLS@1").
Proof.
intros regs M rom pcp n al ca ia H10 H9 H18 H19 H20 Hp Hp' Hn Cn.
zbft (ltac:(oF' 0x568bc%Z)) (ltac:(oD' 0x568bc%Z)).
zlw (ltac:(oF' 0x568c0%Z)) (ltac:(oD' 0x568c0%Z)) pcp Cn.
zstep (ltac:(oF' 0x568c4%Z)) (ltac:(oD' 0x568c4%Z)). zstep (ltac:(oF' 0x568c8%Z)) (ltac:(oD' 0x568c8%Z)). zstep (ltac:(oF' 0x568cc%Z)) (ltac:(oD' 0x568cc%Z)).
stepn (ltac:(oF' 0x568d0%Z)) (ltac:(oD' 0x568d0%Z)).
zret.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section SE.
Local Abbreviation SEC_T_art_cache_pop50 := (ltac2:(TCodec.tc2 tcn__JbtRefill3 "W@&7y5'QEyR0%211%5241'0y8%611%311p061'6'3&@r;(QC+8(1%33A21%6251&QDr8%22C1%;3C41r<+9%;3I19%>231&E&J+R@r9%3221%52<1%>2O1%G3O81r=+;%G3Q51E%J231%D2Q59%M3Q521r>+:%M3Q;1K%Q0231%Q23Q:16r?+<%Q23Q@1Q0%Q5231%Q73Q?1;'2&G+1%221C+O%42E1%6231z%721H&H+TP0%Q32E1&K+2+R0%3221%7251&I%12GQF%QK3QL1<%C2=Ir@%Q>21<%>218%G2F3+@%I251%K231%K2E7%D28>%N221+Q0%D2C1%H2<1%Q2261&;&DrJrGrH%QO2QN1%R1231%R221R>u8rD%:598321rKrI%R72R61%R92:1%R:21I+4&LrF%221QD%R>241%R@261u4%G5F<21>rL+R`@%RE2>1%K5J31CBrM%RH2AQ1%N5M21FE&<rN%RK2RJ9%RM2G1%44Q231=rO%S02=<%74Q521N&:%S22S18%S42=1%S52BQ>%442K1SB%S72<C%S82AQA%742SE1SE'4'>&AvQ3rQ4+Zin0%SM3T91SK/01T9rQ3rQ2%8576321r1+ZioL%T43T@1T2/01T@&9rQ0rQ1%SK2SJ1%SM231%QB2Q3S4%64Q>=21%T026Q<%T12QKQ:%94QO321%G5F>;1@%I3R8@1%TD2@SE%T52;R>%T72R:1%T72QERG%T9221%TB2U31%TK3U361%U61U7&5%TN32ITH%211r2%U1351TC%511r3%U4381T4%811r4%U73;1T=%;11r5%U:3>1T5%>11r6+>%U;3UI1U9%U?3C31%C11r7%UA2U91rQ;%UC213%UE3UM31p061p0<1p0@1p0D1p0H1p0L1pRHQ01%TE2Q21%TF2Q:1qRNV61%R62V71p0R81p0R<1p0RB1p0RF1p0RL1p0S01p0S51p0SC1p0T31p0T41p0T11p0T61p0T:1p0T?1p0TC1p0TE1p0TI1p0U21p0U51p0U=1p0UC1p0UI1p0V01p0V=1pS4VJ1pS6VK1pR2VL1pR6VM1pR4VN1pR>VO1pR0W01pQNW11pS0W31pBW41pRLW:1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_cache_pop50) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_cache_pop50) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_cache_pop50) 2%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_cache_pop50) 3%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_cache_pop50) 4%nat 0%nat).
Variable ia : ltac:(sec_ty2 constr:(SEC_T_art_cache_pop50) 5%nat 0%nat).
Variable cnt : ltac:(sec_ty2 constr:(SEC_T_art_cache_pop50) 6%nat 0%nat).
Variable csz : ltac:(sec_ty2 constr:(SEC_T_art_cache_pop50) 7%nat 0%nat).
Variable ch : ltac:(sec_ty2 constr:(SEC_T_art_cache_pop50) 8%nat 0%nat).
Variable st : ltac:(sec_ty2 constr:(SEC_T_art_cache_pop50) 9%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_cache_pop50) 10%nat 0%nat).
Lemma art_cache_pop50 : ltac:(sec_stmt2 constr:(SEC_T_art_cache_pop50) 11%nat 0%nat).
Proof using Type regs M rom c ca ia cnt csz ch st spb.
intros H8 H9 H11 H10 H12 Hc Hca Hca' Hca8 Hia Hia' Hcnt Hcsz Hch Hst Hspb
Ccsz Cch Cst Cspb Wcnt Wst Ap1 Ap2.
eexists. split.
- zstep (ltac:(oF' 0x567c0%Z)) (ltac:(oD' 0x567c0%Z)).
zstep (ltac:(oF' 0x567c4%Z)) (ltac:(oD' 0x567c4%Z)).
zstep (ltac:(oF' 0x567c8%Z)) (ltac:(oD' 0x567c8%Z)).
zsw (ltac:(oF' 0x567cc%Z)) (ltac:(oD' 0x567cc%Z)) (ca + 80 * c) (cnt - 1) ltac:(exact Wcnt).
zstep (ltac:(oF' 0x567d0%Z)) (ltac:(oD' 0x567d0%Z)).
assert (Ccsz1 : cellA (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 80 * c + 8) 8 csz) by recell Ccsz.
assert (Cch1 : cellA (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 80 * c + 16 + 4 * (cnt - 1)) 4 ch) by recell Cch.
assert (Cst1 : cellA (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 2576) 8 st) by recell Cst.
assert (Wst1 : wokA (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 2576) 8) by rewok Wst.
zld (ltac:(oF' 0x567d4%Z)) (ltac:(oD' 0x567d4%Z)) (ca + 80 * c + 8) Ccsz1.
stepn (ltac:(oF' 0x567d8%Z)) (ltac:(oD' 0x567d8%Z)). rewrite (art_zb_srli_exact _ 30 (4 * (cnt - 1))) by lia.
zstep (ltac:(oF' 0x567dc%Z)) (ltac:(oD' 0x567dc%Z)).
zlwu (ltac:(oF' 0x567e0%Z)) (ltac:(oD' 0x567e0%Z)) (ca + 80 * c + 16 + 4 * (cnt - 1)) Cch1.
zamoadd_d (ltac:(oF' 0x567e4%Z)) (ltac:(oD' 0x567e4%Z)) (ca + 2576) st csz Cst1 ltac:(exact Wst1).
assert (Cspb2 : cellA (Wn 8 (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 2576) (st + csz)) (ia + 32) 8 spb) by recell Cspb.
zld (ltac:(oF' 0x567e8%Z)) (ltac:(oD' 0x567e8%Z)) (ia + 32) Cspb2.
zstep (ltac:(oF' 0x567ec%Z)) (ltac:(oD' 0x567ec%Z)).
zstep (ltac:(oF' 0x567f0%Z)) (ltac:(oD' 0x567f0%Z)).
zstep (ltac:(oF' 0x567f4%Z)) (ltac:(oD' 0x567f4%Z)).
zstep (ltac:(oF' 0x567f8%Z)) (ltac:(oD' 0x567f8%Z)).
apply mst_refl.
- split; [gres; f_equal; lia|].
intros r N8 N9 N10 N11 N12 N14; gres; try reflexivity; repeat (rewrite getr_other by (assumption || (symmetry; assumption) || reg_neq_tac)); reflexivity.
Qed.
End SE.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
End FPX.
