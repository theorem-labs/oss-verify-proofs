(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AsanPlanSoundSums L5Defs L5Core PmModel PmModelFacts.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmCertKitG () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.DecodeC."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1bool"; "1cons"; "1false"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2I"; "2and"; "2eq"]; ["2ex"; "2not"; "3repeat"; "4Z"; "5fetch_word"; "5is_ecall"; "6decode_any"; "7Load"; "7SZ1"; "7SZ4"; "7instr"; "8bvmap"; "0M"; "0R"; "9msteps"; ":defined"]; [":img_clear"; ":u32_at"; ":u64_at"; ":u8_at"; ";zeros_at"; "<FPState"; "<getr"; "<mkst"; "<rdn"; "<regupd"; "<seg_rom"; "=add"; "=le"; "=lt"; "=modulo"; "=of_nat"]; ["=pow"; "0W"; "0a"; "0a'"; "0a0"; "0b"; "0bs"; "0fx"; "0hi"; "0i"; "0imm"; "0k"; "0l"; "0lo"; "0n"; "0n'"]; ["0pc"; "0rd"; "0rs"; "0segs"; ">NoDup"; "?BV"; "?Z_to_bv"; "?bv"; "?bv_signed"; "?bv_unsigned"; "0v"; "0w"; "0x"; "0y"]]).
Module PMCG.
Section G.
Variable segs : list Segment.
Lemma rdn_some : ltac2:(TCodec.tc2 tcn__PmCertKitG "R4'R7yR0%211'9y8%511%311p051'7'C&Q<zr1%3221&Q;r2&Q?r3%211%5241&Q@+2+R0%3221%>251'>&Q=r5%<11%32A1%52A1&A'?r7&R6%E28D%22Q31%411(0%11Q2%83Q231%:11p0<1pSDQ21'@'6%11Q9%Q<11&Q8vR3%@2QAGr6%443C21(1%128Q:%G3831&5%12QDQ=%J3QB17%Q2241qS>>1%A2?1p0C1p0Q71p0QC1pS6QH1pSNQJ1pQJQL1").
Proof. intros M.
induction n as [|n IH]; intros a Ha Hn D. { exists []. split; reflexivity. }
cbn [rdn]. pose proof (D 0 ltac:(lia)) as D0. rewrite Z.add_0_r in D0.
destruct (M (Z_to_bv 64 a)) as [b0|] eqn:E0; [|exfalso; apply D0; reflexivity].
rewrite (L5C.add1_lit a).
destruct (IH (a + 1) ltac:(lia) ltac:(lia)) as (bs & E & Hl).
{ intros i Hi. replace (a + 1 + i) with (a + (i + 1)) by lia. apply D. lia. }
rewrite E. exists (b0 :: bs). split; [reflexivity| cbn; rewrite Hl; reflexivity].
Qed.
Lemma u64_of_defined : ltac2:(TCodec.tc2 tcn__PmCertKitG "Q<'R7yR0%211'9y8%511%311p051'C&Q<zr1%3221&Q;r2+8%3221&Q@+2+R0%3221%<251&Or4r3%3321:'@'>&Q=%12B9%32B1&Q2vR3r6r5%44321H%9261qTHM1%<2N1p0>1p0C1p0M1pS6Q21pQJQ41").
Proof. intros M a.
intros Ha Hn D. destruct (rdn_some M 8%nat a Ha ltac:(cbn; lia) ltac:(intros i Hi; apply D; cbn in Hi; lia)) as (bs & E & Hl).
exists (bytes_le_to_Z bs). pose proof (AX2S.bytes_le_to_Z_bound bs) as Hb. rewrite Hl in Hb. cbn in Hb.
split; [lia|]. unfold L5.u64_at. rewrite E. f_equal. symmetry. apply APSX.word_to_le_bytes_of_bytes_n; [exact Hl| lia].
Qed.
Lemma u8_of_defined : ltac2:(TCodec.tc2 tcn__PmCertKitG "Q='R7yR0%211'9y8%511%311p051'C&Q<zr1%3221&Q;r2+1%3221&Q@+2+R0%3221%<251&Or4r3%3321:'@'>&Q=+X0%22C1%42C1&Q3vR3r6r5%44321I%:261qS<N1%=2O1p0?1p0D1p0N1pS6Q31pQJQ51").
Proof. intros M a.
intros Ha Hn D. destruct (rdn_some M 1%nat a Ha ltac:(cbn; lia) ltac:(intros i Hi; apply D; cbn in Hi; lia)) as (bs & E & Hl).
destruct bs as [|b0 [|]]; cbn in Hl; try discriminate. exists (bv_unsigned b0).
pose proof (bv_unsigned_in_range 8 b0) as B. change (bv_modulus 8) with 256 in B. split; [exact B|].
unfold L5.u8_at. rewrite E. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma u8_at_fun : ltac2:(TCodec.tc2 tcn__PmCertKitG "M'R7yR0%211'9y8%511%311p051'C&Q3vR3r4r3r2%544321r5%746153'?&Q>+X0%2291%3292%53>21p071p0:1pTLA1pTJB1pS6C1pQJE1").
Proof. intros M a x y.
unfold L5.u8_at. intros Hx Hy. rewrite Hx in Hy.
assert (Hb : Z_to_bv 8 x = Z_to_bv 8 y) by congruence.
assert (E : bv_unsigned (Z_to_bv 8 x) = bv_unsigned (Z_to_bv 8 y)) by (rewrite Hb; reflexivity).
rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E. exact E.
Qed.
Lemma u8_of_u64_eq : ltac2:(TCodec.tc2 tcn__PmCertKitG "Q='R7yR0%211'9y8%511%311p051'C'>&Q<zr2%3221&Q=&Q@+2+R0%3221%5271%;271+X0%82:1%>2:1&Q2vR3r6r5r4%544321&Q3r7%247164'?&Q>%129>%33L19p051p091p0@1p0D1pTFQ11pTHQ21pS6Q31pQJQ51").
Proof. intros M a w v.
intros Hw Hv H8 H1. pose proof (PMF.u8_of_u64 segs M a w Hw H8) as H1'. pose proof (u8_at_fun M a _ _ H1' H1) as E.
rewrite Z.mod_mod in E by lia. rewrite E. apply Z.mod_small. lia.
Qed.
Lemma rdn_zeros : ltac2:(TCodec.tc2 tcn__PmCertKitG "QN'R7yR0%211'9y8%511%311p051'7'C&Q<zr1%3221&Q;r2&Q?r3%211%5241&Q@+2+R0%3221%>251'>&Q=r5%<11%32A1%52A1'?r7&R6%D27C%22Q21%411(1%52Q2K%22Q21%93Q241p0;1pSDQ11'6%11Q7%Q:11&Q8vR3r6r4%A2QA1%54431H&B%13Q@?J%A2:1%H3:41p0>1p0Q11p0Q=1pS6QB1pSHQD1pQJQF1").
Proof. intros M.
induction k as [|k IH]; intros a Ha Hk Z0. { reflexivity. }
cbn [rdn repeat]. pose proof (Z0 0 ltac:(lia)) as E0. rewrite Z.add_0_r in E0. rewrite E0.
rewrite (L5C.add1_lit a). rewrite (IH (a + 1)); [reflexivity| lia| lia|].
intros i Hi. replace (a + 1 + i) with (a + (i + 1)) by lia. apply Z0. lia.
Qed.
Lemma u64_of_zeros : ltac2:(TCodec.tc2 tcn__PmCertKitG "Q3'R7yR0%211'9y8%511%311p051'C&Q4r2r1+8%43321&Q<z%2216&Q;r3%2217&Q@+2+R0%3221%:251&Q2vR3r5r4%44321>p061p0?1p0C1pS6I1pQJK1").
Proof. intros M a.
intros Z8 Ha Hn. unfold L5.u64_at. change (word_to_le_bytes 8 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0 : byte) 8).
apply rdn_zeros; [lia| cbn; lia|]. intros i Hi. apply Z8. cbn in Hi. lia.
Qed.
Lemma u32_of_zeros : ltac2:(TCodec.tc2 tcn__PmCertKitG "Q3'R7yR0%211'9y8%511%311p051'C&Q4r2r1+4%43321&Q<z%2216&Q;r3%2217&Q@+2+R0%3221%:251&Q1vR3r5r4%44321>p061p0?1p0C1pS6I1pQJK1").
Proof. intros M a.
intros Z8 Ha Hn. unfold L5.u32_at. change (word_to_le_bytes 4 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0 : byte) 4).
apply rdn_zeros; [lia| cbn; lia|]. intros i Hi. apply Z8. cbn in Hi. lia.
Qed.
Lemma u8_of_zeros : ltac2:(TCodec.tc2 tcn__PmCertKitG "Q3'R7yR0%211'9y8%511%311p051'C&Q4r2r1+1%43321&Q<z%2216&Q;r3%2217&Q@+2+R0%3221%:251&Q3vR3r5r4%44321>p061p0?1p0C1pS6I1pQJK1").
Proof. intros M a.
intros Z8 Ha Hn. unfold L5.u8_at. change [Z_to_bv 8 0] with (repeat (Z_to_bv 8 0 : byte) 1).
apply rdn_zeros; [lia| cbn; lia|]. intros i Hi. apply Z8. cbn in Hi. lia.
Qed.
Lemma rdn_img : ltac2:(TCodec.tc2 tcn__PmCertKitG "QH'R7yR0%211'9y8%511%311p051'C'7&Q0r5r4r3%43321&Q<z%2214r6%4217&Q;&Q?%11:%32<1%9216r7&Q@+2+R0%3221%?251'?'6%11L%O11&Q8vR3r:&R6%12Q6>%54431F(0%11Q5q0Q91%94815J%>3;51p0@1p0G1p0M1p0Q01p0Q41pSHQ:1pS6Q<1pSBQ=1pSLQ>1pQJQ@1").
Proof. intros M lo hi a k.
intros IC Ha Hlo Hk Hhi. apply (L5C.rdn_agree segs (fun _ => None) M k a Ha ltac:(lia)). intros i Hi. apply IC. lia.
Qed.
Lemma lw_run : ltac2:(TCodec.tc2 tcn__PmCertKitG "TA'Q5&Ky5'R7yR0%211%5241'9y8%611%311p061'CyQ0%;11%<1=y<%>11'6%11:'?%>17&DvR3&R6r7%22F1%5241(1r6%22@1%;3:41'2&E%119(4%@3421';'J%221K%Q111&Fr8%211(:(G(I(<r5%4532HD1+4%74=Q721%H2=1%Q13=:1&A(R5z(=%33QH21%Q73Q<A1%611&Q<r;%2271&Q=&Q;r<%221A&Q@+2+R0%3221%8251&Q6r?r:%3221%QE2R9Q3%QJ3R921'>r9%D2I1%B22;%4221&R8%12R5G%E2;1%J2O1%H22A%:221%RC1R7&Q8rA%92R=K%M2Q01%R72RK1u4%64R:521%R62R?G%R?3921'7&5%12RMQ8%RC3317'@'N&Q7rFrErC%RF2S:1rD&Q:%11RJ%8576431&Q9r1%239I1%QE29R4%RO2SC1%>5=3197%@3S271qTFSE1%C2SF1p0E1p0J1p0Q51p0Q<1p0QB1p0QI1p0R31p0R71p0R?1p0S11p0S71pS>SD1pS:SL1pSFSH1pT6SK1pT4SL1pS4SN1pT2T11pQJT31pQLT91pS@T@1").
Proof. intros fx R M pc W rd rs imm a0 bs.
intros HF HE HD Hrd Hpc Hpc4 Hrs Ha0 Ha RB Hl.
pose proof (AX2S.bytes_le_to_Z_bound bs) as Hb. rewrite Hl in Hb. cbn in Hb.
exists (v_lw (Z_to_bv 64 (bytes_le_to_Z bs))).
eapply mst_step; [reflexivity| | apply mst_refl].
rewrite (step_lw segs R (Z_to_bv 64 pc) M (seg_rom segs) W rd rs imm bs (Z_to_bv 64 (bytes_le_to_Z bs)) HF HE HD).
- rewrite (bv_eqb_neq rd 0%bv Hrd). f_equal. f_equal. unfold v_addi. rewrite L5.unsigned_lit by lia. reflexivity.
- unfold v_addi. rewrite Hrs, L5.unsigned_lit by lia. exact RB.
- rewrite L5.unsigned_lit by lia. reflexivity.
Qed.
Lemma lbu_img_run : ltac2:(TCodec.tc2 tcn__PmCertKitG "T='Q5&Ky5'R7yR0%211%5241'9y8%611%311p061'CyQ0%;11%<1=y<%>11'?%<15&DvR3&R6r7%22D1%5241(1r6%22>1%;3:41'2&E%119(4%@3421';'J%221I%O11&Fr8%211(:(G(Hr5%352=GC1+4%64<Q421%G2<1%Q03<91&A(R5z(=%33QE21%Q63Q9@1%611&Q<r;%2271&Q=&Q;r<%221A&Q@+2+R0%3221%8251&Q6r?r:%3221%QD2R6Q2%QI3R621'>r9%D2I1%B22;%4221&R8%12R2G%E2;1%J2O1%H22A%:221'6%11R?%RB11&Q8rA%;2R<M%O2Q21%R82RJ1u1%64R;521(3(8%11RJ%33RKL1%R;2=1%RD3=61'N&Q7rDrC%RE2S7@rB&Q:%11RI%7565431&Q9&R9%12S:QG%RM2S?1%43:Q=1%QG2JR6%S02SB1%?5>31;9%A3S391p0C1p0Q41p0Q;1p0QA1p0QH1p0R21p0R61p0R>1p0RO1p0S51pS<SJ1pS:SH1pSFSD1pT6SG1pT4SH1pS4SJ1pT2SM1pQJSO1pQLT51pS@T<1").
Proof. intros fx R M pc W rd rs imm a0 b.
intros HF HE HD Hrd Hpc Hpc4 Hrs Ha0 Ha RB.
eapply mst_step; [reflexivity| | apply mst_refl].
rewrite (step_lbu segs R (Z_to_bv 64 pc) M (seg_rom segs) W rd rs imm b HF HE HD).
- rewrite (bv_eqb_neq rd 0%bv Hrd). f_equal. f_equal. unfold v_addi. rewrite L5.unsigned_lit by lia. reflexivity.
- unfold v_addi. rewrite Hrs, L5.unsigned_lit by lia. exact RB.
Qed.
Lemma zeros_sub : ltac2:(TCodec.tc2 tcn__PmCertKitG "O'R7yR0%211'9y8%511%311p051'C&Q4r5r4r3%43321&Q<%1253&Q;%1265r6%3219%6231r8%=31<;p031p091p0<1pT0B1pS8C1pSND1pS6E1pQJG1").
Proof. intros M a n a' n'. intros Z0 H1 H2 i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply Z0. lia. Qed.
End G.
Lemma nodup_swap : ltac2:(TCodec.tc2 tcn__PmCertKitG "C'C'6%112'R4(3r3r2r1%43821%53941%72:1r4%83<16%93=81%;2>1p051pSJ>1pS<A1pS6B1").
Proof. intros a b l.
intros H. inversion H as [|x1 l1 N1 ND1]; subst. inversion ND1 as [|x2 l2 N2 ND2]; subst.
constructor.
- intros E. inversion E as [|? ? ? E']; subst; [apply N1; constructor| apply N2; exact E'].
- constructor; [intros E; apply N1; constructor; exact E| exact ND2].
Qed.
End PMCG.
