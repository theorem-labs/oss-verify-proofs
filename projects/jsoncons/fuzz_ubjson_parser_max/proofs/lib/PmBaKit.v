(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AsanPlanSoundSums HeapIface
L5Defs L5Core L5CoreKit PmLayout PmModel PmModelFacts PmStatics PmSpecs PmSrcSMemmove PmParKit.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBaKit () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Core.L5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5CoreKit.L5K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmParKit.PMPK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSrcSMemmove.PMCP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0B"; "0CPY"; "1None"; "1Some"; "1app"; "1cons"; "1fst"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1snd"; "2and"; "2eq"]; ["2ex"; "2not"; "2or"; "3lt"; "4nth"; "5Z"; "0L"; "6bvmap"; "0M"; "0M'"; "0M3"; "0P0"; "0R"; "0R3"; "7msteps"; "8credit"]; ["8credit_ok"; "8debit"; "8heap_layout"; "8hl_b_overhead"; "8hl_k_per_malloc"; "9agree_on"; ":CS"; ";defined"; ";ra_ok"; ";u32_at"; ";u64_at"; ";u8_at"; ";writable"; "<CHUNK"; "<MAX_DEPTH"; "<PST"]; ["<VLong"; "<mode_bottom"; "<p_done"; "<p_k"; "<p_src"; "<p_tb"; "<p_tg"; "<parser_at"; "<pot_parser"; "<pot_text"; "<ps_mode"; "<pst"; "<pstate"; "<pstate_at"; "<pstate_ok"; "<sr_qc"]; ["<stack_shape"; "<vec_at"; "<vstr"; "=dkr"; ">T3"; ">T4"; ">credit_keep"; ">credit_le"; ">ec_at"; "?copy1_spec"; "@FPState"; "@getr"; "@mkst"; "@rdn"; "@seg_rom"; "Amem_grows"]; ["BIn"; "Cadd"; "Cle"; "Clt"; "Cmodulo"; "Cmul"; "Cof_nat"; "Cpow"; "0a"; "0a'"; "0b"; "0b'"; "0bs"; "0c"; "0cr"; "0cr0"]; ["0d'"; "0dst"; "0fx"; "0i"; "0k"; "0k'"; "0m'"; "0n"; "0o"; "0ois"; "0op"; "0p"; "0pc"; "0r"; "0s"; "0s'"]; ["0segs"; "0src"; "DZ_to_bv"; "Dbv"; "0stk"; "0stk'"; "0v"; "0x"]]).
Module PMBK.
Section G.
Variable segs : list Segment.
Variable A : pm_addrs.
Lemma rdn_copy : ltac2:(TCodec.tc2 tcn__PmBaKit "RE'SCyR0%211'<y8%511%311p051':'E&RBzr2%3221&RAr3&RFr4%211%5241&RG+2+R0%3221%>251%?2>:r6%;11%>2;1%C216'>r1%F2E1&RCr8%C11%3251%7251&A'?r;&SB%L28N%22Q:1%411(3%11Q9%83Q931%:11p0<1pV8Q91r9%Q411%D2F1%H2F1r<%Q:25Q<%@2QH1%311%D3QE?1p061pV8QD1'9%11QJ%QM11&R=vS@r:r7%L2R41%54431C%N2R6Q5%746Q01E%Q23931p0=1p0I1p0Q?1p0QD1p0QF1p0R21pUDR71pUBR81pV@R:1pQDR<1pQBR=1").
Proof. intros M M'.
induction n as [|n IH]; intros a a' Ha Hn Ha' Hn' D C; [reflexivity|].
cbn [rdn]. pose proof (C 0 ltac:(lia)) as C0. rewrite !Z.add_0_r in C0. rewrite C0.
pose proof (D 0 ltac:(lia)) as D0. rewrite Z.add_0_r in D0.
destruct (M (Z_to_bv 64 a)) as [b0|] eqn:E0; [|exfalso; apply D0; reflexivity].
rewrite (L5C.add1_lit a), (L5C.add1_lit a').
rewrite (IH (a + 1) (a' + 1)); [reflexivity|lia|lia|lia|lia| |].
- intros i Hi. replace (a + 1 + i) with (a + (i + 1)) by lia. apply D. lia.
- intros i Hi. replace (a + 1 + i) with (a + (i + 1)) by lia. replace (a' + 1 + i) with (a' + (i + 1)) by lia. apply C. lia.
Qed.
Lemma u64_copy : ltac2:(TCodec.tc2 tcn__PmBaKit "R5'SCyR0%211'<y8%511%311p051pW@62'E&RBzr3%3221&RAr4+8%3221&RG+2+R0%3221%<251%=2<8r5%;219%@215&Q7r9r7%3321>'>r1%G2F1&RC%123C%5231'?r;&SBr2%K2=1%32Q91%511r<r:%Q0216%82Q>1%411%<3Q;61p0>1pV8Q:1&Q:vS@%241@JIr8%443BL1p031p071p0M1p0Q21p0Q61p0Q81p0QB1pW>QG1pUDQH1pUBQI1pQDQK1pQBQM1").
Proof. intros M M' a a' v. intros H1 H2 H3 H4 D C U. unfold L5.u64_at in *. rewrite (rdn_copy M M' 8 a a'); [exact U|lia|lia|lia|lia|exact D|exact C]. Qed.
Lemma u32_copy : ltac2:(TCodec.tc2 tcn__PmBaKit "R5'SCyR0%211'<y8%511%311p051pW@62'E&RBzr3%3221&RAr4+4%3221&RG+2+R0%3221%<251%=2<8r5%;219%@215&Q7r9r7%3321>'>r1%G2F1&RC%123C%5231'?r;&SBr2%K2=1%32Q91%511r<r:%Q0216%82Q>1%411%<3Q;61p0>1pV8Q:1&Q9vS@%241@JIr8%443BL1p031p071p0M1p0Q21p0Q61p0Q81p0QB1pW>QG1pUDQH1pUBQI1pQDQK1pQBQM1").
Proof. intros M M' a a' v. intros H1 H2 H3 H4 D C U. unfold L5.u32_at in *. rewrite (rdn_copy M M' 4 a a'); [exact U|lia|lia|lia|lia|exact D|exact C]. Qed.
Lemma u8_copy : ltac2:(TCodec.tc2 tcn__PmBaKit "R5'SCyR0%211'<y8%511%311p051pW@62'E&RBzr3%3221&RAr4+1%3221&RG+2+R0%3221%<251%=2<8r5%;219%@215&Q7r9r7%3321>'>r1%G2F1&RC%123C%5231'?r;&SBr2%K2=1%32Q91%511r<r:%Q0216%82Q>1%411%<3Q;61p0>1pV8Q:1&Q;vS@%241@JIr8%443BL1p031p071p0M1p0Q21p0Q61p0Q81p0QB1pW>QG1pUDQH1pUBQI1pQDQK1pQBQM1").
Proof. intros M M' a a' v. intros H1 H2 H3 H4 D C U. unfold L5.u8_at in *. rewrite (rdn_copy M M' 1 a a'); [exact U|lia|lia|lia|lia|exact D|exact C]. Qed.
Lemma pstate_copy : ltac2:(TCodec.tc2 tcn__PmBaKit "R6'SCyR0%211'<y8%511%311p051pW@62'E'QL&RBzr3%3221&RAr4+Q0%3221&RG+2+R0%3221%<251%=2<8r5%;219%@215&Q7r9r7%3321>'>r1%G2F1&RC%123C%5231'?r;&SBr2%K2=1%32Q:1%511r<r:%Q0216%82Q?1%411%<3Q<61p0>1pV8Q;1&QMvS@%241@JIr8%443BL1p031p071p0M1p0Q21p0Q61p0Q81p0QB1pW@QG1pUDQI1pUBQJ1pQDQL1pQBQN1").
Proof. intros M M' a a' x.
intros H1 H2 H3 H4 D C (P0 & P8 & P16 & P24).
assert (Cs : forall o n, 0 <= o -> o + n <= 32 -> forall i, 0 <= i < n -> M' (Z_to_bv 64 (a' + o + i)) = M (Z_to_bv 64 (a + o + i))).
{ intros o n Ho Hn i Hi. rewrite <- !Z.add_assoc. apply C. lia. }
split; [apply (u32_copy M M' a a'); [lia|lia|lia|lia| apply (L5.defined_sub M a 32); [exact D|lia|lia]| intros i Hi; apply C; lia| exact P0]|].
split; [apply (u64_copy M M' (a + 8) (a' + 8)); [lia|lia|lia|lia| apply (L5.defined_sub M a 32); [exact D|lia|lia]| apply (Cs 8 8); lia| exact P8]|].
split; [apply (u8_copy M M' (a + 16) (a' + 16)); [lia|lia|lia|lia| apply (L5.defined_sub M a 32); [exact D|lia|lia]| apply (Cs 16 1); lia| exact P16]|].
apply (u64_copy M M' (a + 24) (a' + 24)); [lia|lia|lia|lia| apply (L5.defined_sub M a 32); [exact D|lia|lia]| apply (Cs 24 8); lia| exact P24].
Qed.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmBaKit "S@'SCyR0%211'<y8%511%311p051'E'9'QL%211&R1vS@&R4&R5r7r5r4r3r2%9887654321&RC&RF&8%12?6%311&RG+2%221;%8241&RBz%221A&RAr8+H%3221+R0%<2;1%9231%:296r9&RE+Q0%B2A:%3221%=251%A219&Q5r=r<r;+8%544321r>+@%G261%943815r?r:%Q52QC1%Q711%D2C1%?459=1&Q7%Q72Q6?%H2G1%339B1&Q:r@%Q52<B%Q@2QNE%QB11%O2N1%Q92D1%Q:21Q0%84R0761&QMrA%QH2R6N%QJ11%Q72Q61%QA2H1%64R751Q1rB&5(6(;%11R?%33R@Q81%53RAQ41%R@8R?R>R=7=FQ11p091p0A1p0K1p0Q01p0Q71p0Q<1p0QC1p0QK1p0QM1p0R51p0R91p0RC1pULRO1pW:RO1pV:S31pUFS41pW>S51pQDS71pQBS81")) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable M' : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable v : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable b : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SECT) 4%nat 0%nat).
Variable stk : ltac:(sec_ty2 constr:(SECT) 5%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SECT) 6%nat 0%nat).
Lemma vec_push : ltac:(sec_stmt2 constr:(SECT) 7%nat 0%nat).
Proof.
intros (V0 & V8 & V16 & Hk & Hlen & Hal & DB & _ & _ & EL) Hlt Hv Hv' Hb Hb' AG0 AG16 AGS D' C8 PC.
unfold PM.vec_at. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1.
split; [apply (L5C.u64_at_agree segs M M'); [exact AG0|lia|lia|exact V0]|].
split; [replace (b + 32 * (Z.of_nat (length stk) + 1)) with (b + 32 * Z.of_nat (length stk) + 32) by lia; exact C8|].
split; [apply (L5C.u64_at_agree segs M M'); [exact AG16|lia|lia|exact V16]|].
split; [exact Hk|]. split; [lia|]. split; [exact Hal|]. split; [exact D'|]. split; [exact I|]. split; [exact I|].
intros i Hi.
destruct (Nat.lt_ge_cases i (length stk)) as [Lt|Ge].
- rewrite app_nth1 by exact Lt. apply (PMF.pstate_at_agree segs M M'); [lia|lia| |apply EL; exact Lt].
apply (L5C.agree_on_sub M M' b (32 * Z.of_nat (length stk))); [exact AGS|lia|lia].
- assert (E : i = length stk) by lia. subst i. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth]. exact PC.
Qed.
End S.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmBaKit "T?'SCyR0%211'<y8%511%311p051'E'9'QL%211&R1vS@&R4&R5r8r6r5r4r3%9887654321'?&RF&8%12?6%311&RG+2%221;%83F41&RB+:%22@1z%421C&RAr9&RE+Q0%=2<H%3221%6251+R0%A2@1%>231%?2<Mr7r:+1%>221%H2G1%>2=1%A261%G21:&RD+@%22Q91%Q43QB1H&Q:r?r>%34QA21Ir@+8%M251r=%Q82Q71%N2M1%Q12E1%Q221O%<4QJ861rA%Q52:Ar;%Q72>J%QA2Q@1%Q72Q61%Q:241%D4R2761&Q7rBr<%Q?2GQ2%QI2QH1%Q?2Q>1%63541'>r1%QJ2QG1&RC%R02QOC%QF2QE1%3251%7251rE&SBr2%QN2Q61%32S21%511rFrC%R3216%82S71%411%RD3S461p0=1pV8S41&QMrD%R;2QBC%34S321QD%R=2Q0R0&5(6(;%11S;%33S<QG1%53S=Q?1%S<8S;S:S9I:QL71p091p0>1p0Q51p0Q=1p0QF1p0R01p0R51p0R:1p0RC1p0RE1p0S01p0S31p0S71p0SA1p4SO1pULSN1pW:SN1pV:T21pUFT31pW>T41pQDT61pQBT71")) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable M' : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable v : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable b : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SECT) 4%nat 0%nat).
Variable stk : ltac:(sec_ty2 constr:(SECT) 5%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SECT) 6%nat 0%nat).
Variable B : ltac:(sec_ty2 constr:(SECT) 7%nat 0%nat).
Lemma vec_grow : ltac:(sec_stmt2 constr:(SECT) 8%nat 0%nat).
Proof.
intros (V0 & V8 & V16 & Hk & Hlen & Hal & DB & _ & _ & EL) HL Hk10 Hb Hb' HB HB' HBal C0 C8 C16 D' CP PC.
assert (P2 : 2 ^ (k + 1) = 2 * 2 ^ k) by (rewrite Z.pow_add_r by lia; lia).
unfold PM.vec_at. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1.
split; [exact C0|].
split; [rewrite HL; replace (B + 32 * (2 ^ k + 1)) with (B + 32 * 2 ^ k + 32) by lia; exact C8|].
split; [exact C16|].
split; [lia|]. split; [rewrite HL, P2; pose proof (PM.pow2_pos k ltac:(lia)); lia|]. split; [exact HBal|].
split; [exact D'|]. split; [exact I|]. split; [exact I|].
intros i Hi.
destruct (Nat.lt_ge_cases i (length stk)) as [Lt|Ge].
- rewrite app_nth1 by exact Lt. apply (pstate_copy M M' (b + 32 * Z.of_nat i) (B + 32 * Z.of_nat i)); [lia|lia|lia|lia| | |apply EL; exact Lt].
+ apply (L5.defined_sub M b (32 * 2 ^ k) _ 32 DB); lia.
+ intros j Hj. replace (B + 32 * Z.of_nat i + j) with (B + (32 * Z.of_nat i + j)) by lia.
replace (b + 32 * Z.of_nat i + j) with (b + (32 * Z.of_nat i + j)) by lia. apply CP. lia.
- assert (E : i = length stk) by lia. subst i. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth]. rewrite HL. exact PC.
Qed.
End S.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmBaKit "TB'SCyR0%211'<y8%511%311p051'E'QK'9'QL%211&QGvS@v0&R4&R5r:r8r7r6%9887654321&RBzr9%3221&RA+\0%22;1&RG+2+R0%3221%;251&Q5r=r<r;+8%544321r>+9%@261+3%:44921r?+@%E2<1+ZH%?44921&R3r@%J2<>%34281?rA+[8%N2;1+H%844721&Q;%Q229F%24Q@71J'B'?%13QIHQ9+1%33QKJ1%5231&Q9rCrB+<%Q>221%54QL41Q1'>%QE2QDN&Q>%QC21<%QH2Q11%5241&R1rErD%QI21L%48R7R5R431Q7Q<QArGrF&QO&QD%11D%311&Q=%Q:47621'R2&QE%11:(Q@r3r2r1%43321%Q63861rLrKr4%QG43271p051pVHS41pV@S51pULS61rH(Q?&QB%11Q0%J1Q1%E1Q2&QF%11Q4%79Q45QA431Q@R0R3%S;8S:S9S8S79Q2Q11p0;1p0M1p0Q61p0Q<1p0QC1p0QJ1p0R11p0R51p0R;1p0R@1p0RF1p0RL1p0S31p0S<1p0SA1pW<SL1pV<T11pUHT21pV2T31pV>T41pVNT41pVDT61pVFT71pQDT91pQBT:1")) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable M' : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable op : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable ois : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SECT) 4%nat 0%nat).
Variable m' : ltac:(sec_ty2 constr:(SECT) 5%nat 0%nat).
Variable d' : ltac:(sec_ty2 constr:(SECT) 6%nat 0%nat).
Variable b' : ltac:(sec_ty2 constr:(SECT) 7%nat 0%nat).
Variable k' : ltac:(sec_ty2 constr:(SECT) 8%nat 0%nat).
Variable stk' : ltac:(sec_ty2 constr:(SECT) 9%nat 0%nat).
Lemma parser_upd : ltac:(sec_stmt2 constr:(SECT) 10%nat 0%nat).
Proof.
intros (H0 & D & _ & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & _ & TB & VEC & B1 & B2 & B3) Ho Ho' AG1 AG9 AG2 DK8 DK360
C8 Hm C12 Hd VEC' DKC AGT.
destruct SRC as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & G1 & G2 & G3 & G4 & DC & _ & _).
cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk].
assert (AG4 : forall a n, op + 16 <= a -> a + n <= op + 360 -> L5C.agree_on M M' a n) by (intros a n X1 X2; eapply L5C.agree_on_sub; [exact AG2|lia|lia]).
split; [apply (L5C.u64_at_agree segs M M'); [exact AG1|lia|lia|exact H0]|].
split. { intros i Hi. destruct (Z_lt_le_dec i 8) as [X|X]; [rewrite AG1 by lia; apply D; lia|].
destruct (Z_lt_le_dec i 16) as [Y|Y]; [apply DK8; [lia| apply D; lia]|].
destruct (Z_lt_le_dec i 360) as [Y2|Y2]; [rewrite AG2 by lia; apply D; lia| apply DK360; [lia| apply D; lia]]. }
split; [exact I|]. split; [exact C8|].
split; [apply (L5C.u8_at_agree segs M M'); [eapply L5C.agree_on_sub; [exact AG9|lia|lia]|lia|lia|exact H9]|].
split; [exact C12|].
split; [apply (L5C.u8_at_agree segs M M'); [apply AG4; lia|lia|lia|exact H16]|].
split; [apply (PMF.u32_at_agree segs M M'); [apply AG4; lia|lia|lia|exact H20]|].
split. { apply (PMF.nullis_at_agree segs A M M'); [lia| lia| apply AG4; lia| exact NI]. }
split.
{ split; [apply (L5C.u64_at_agree segs M M'); [apply AG4; lia|lia|lia|exact F1]|].
split; [apply (L5C.u64_at_agree segs M M'); [apply AG4; lia|lia|lia|exact F2]|].
split. { apply (L5C.defined_agree M M'); [apply AG4; lia| exact F3]. }
split; [apply (L5C.u64_at_agree segs M M'); [apply AG4; lia|lia|lia|exact F4]|].
split; [apply (L5C.u64_at_agree segs M M'); [apply AG4; lia|lia|lia|exact F5]|].
split; [apply (L5C.u64_at_agree segs M M'); [apply AG4; lia|lia|lia|exact F6]|].
split; [apply (L5C.u64_at_agree segs M M'); [apply AG4; lia|lia|lia|exact F7]|].
split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
split; [apply (PMPK.defined_dkr M M' _ _ DKC DC)|]. split; exact I. }
split; [apply (PMF.u32_at_agree segs M M'); [apply AG4; lia|lia|lia|exact H320]|].
split; [apply (L5C.u64_at_agree segs M M'); [apply AG4; lia|lia|lia|exact H328]|]. split; [exact I|].
split. { apply (PMPK.vstr_at_keep segs M M'); [lia| lia| apply AG4; lia| exact AGT| exact TB]. }
split; [exact VEC'|].
split; [exact Hm|]. split; [exact B2| exact Hd].
Qed.
End S.
Lemma rdn_nth : ltac2:(TCodec.tc2 tcn__PmBaKit "R3'SCyR0%211'<y8%511%311p051':'E'9%116&RBzr2%3221&RAr3&RFr4%211%5241&RG+2+R0%3221%>251&Q7r6r5%<11%433<1'?%N1F&R=vS@r7&SB%12Q59%54431;(4%12NF%:3931&Cr1r8%3221r:%N1Q2%Q1241%=2QA1%411&D%@2QAQ8%24QAQ8B1%?2QB1%H3QB51p0;1pV8QB1p0A1p0M1p0Q31p0Q?1pUJQD1pUBQG1pV@QI1pQBQK1").
Proof. intros M.
induction n as [|n IH]; intros a bs Ha Hn D RD i Hi; [lia|].
cbn [rdn] in RD. pose proof (D 0 ltac:(lia)) as D0. rewrite Z.add_0_r in D0.
destruct (M (Z_to_bv 64 a)) as [b0|] eqn:E0; [|exfalso; apply D0; reflexivity].
rewrite (L5C.add1_lit a) in RD.
destruct (rdn segs M (Z_to_bv 64 (a + 1)) n) as [rest|] eqn:ER; [|discriminate]. injection RD as <-.
destruct i as [|i].
- rewrite Z.add_0_r. exact E0.
- cbn [nth]. replace (a + Z.of_nat (S i)) with ((a + 1) + Z.of_nat i) by lia.
apply (IH (a + 1) rest); [lia|lia| |exact ER|lia]. intros j Hj. replace (a + 1 + j) with (a + (j + 1)) by lia. apply D. lia.
Qed.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom segs)).
Lemma copy_run_eq : ltac2:(TCodec.tc2 tcn__PmBaKit "UF'E&R9vS@r1%3221'R:&Gy5'SCyR0%211%5241'<y8%611%311p061'?&R;r6&SB&RFu:%211%42A1%7261r4%72B1%;3B31r7u;%:11%<2I1%?241%A3H17r8u<%@11%B2O1%E241%G3N1=r9u1%F11%H2Q51%K241%M3Q41C&Q8r5%211&RB+1%221Gzr:%5221&RC&RAr;%221B&RG+2+QO%3221%8251%?2<7r<%:219%<215'Br>%>215r=%G221%A228%I215%7231&Q<r@r?%34R>218&Q7rA%2314='@'>'N&R<rFrErH%R72RB1rD&R>%11RL%8576431r2%R=2RHC%;5:21RO4%=3S141&R?%129S2%QD2QAS3+R0%Q<2Q;1%QA2S61%E241&A%QJ2C<rC%QE2E1%QG2?1%K241%611r3%RO2S:1%RJ11rG%113%S63S831p071p0?1pUBSJ1%Q:3SH>Q9rB%R52SJ1%Q92H1%R62Q6O%S<2SG1%?11%R92Q6Q2%S?2SJ1%Q<11%SD3SF41p081pV8T71':&R@&Q6%233T81%SG1Q<%SI2T61%SL2SD1%SM2J2%SO3T621p061pV8:1%T12QCSK%T02T;Q7%T43T;21%R1241%R22@1%R32M1%R42O1%R52QE1%R62QH1qQFT<1%R92T=1qQLTC1%R;2TD1p0R=1p0RA1p0RF1p0RO1p0S31p0S51p0S?1p0SC1p0SG1p0SK1p0T21p0T91p0T@1pVLU=1pV@U>1pW4U?1pV4U@1pQBU11pQJU71pV6U>1p6U@1pVJUE1").
Proof. intros pc CPY fx R M dst src n r.
intros H10 H11 H12 H1 RA Hn Hd Hdn Hs Hsn AP W D.
destruct (PMCP.rdn_of_defined segs M (Z.to_nat n) src Hs ltac:(lia)) as (bs & RD & LEN). { rewrite Z2Nat.id by lia. exact D. }
destruct (CPY fx M (Z_to_bv 64 dst) (Z_to_bv 64 src) n bs R (Z_to_bv 64 r) Hn LEN
ltac:(rewrite LEN; exact RD)
ltac:(rewrite LEN; replace (Z_to_bv 64 dst) with (Z_to_bv 64 (dst + 0)) by (f_equal; lia); apply W; lia)
ltac:(rewrite !L5.unsigned_lit by lia; lia) ltac:(rewrite L5.unsigned_lit by lia; lia) ltac:(rewrite L5.unsigned_lit by lia; lia)
(L5K.ret_ok_lit r RA) H1 H10 H11 H12) as (R3 & MS & KO & A10).
exists R3, (wbytes M (Z_to_bv 64 dst) bs). split; [exact MS|]. split; [apply wbytes_grows|].
split. { intros a Ha Hout. apply PMCP.wbytes_out; [lia| rewrite LEN; lia| exact Ha| rewrite LEN, Z2Nat.id by lia; exact Hout]. }
split. { pose proof (PMCP.wbytes_defined M dst bs Hd ltac:(rewrite LEN; lia)) as X. rewrite LEN, Z2Nat.id in X by lia. exact X. }
split.
{ intros i Hi. rewrite <- (Z2Nat.id i) by lia.
replace (Z_to_bv 64 (dst + Z.of_nat (Z.to_nat i))) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 dst) + Z.of_nat (Z.to_nat i)))
by (rewrite L5.unsigned_lit by lia; reflexivity).
rewrite AX2S.wbytes_nth; [| rewrite L5.unsigned_lit by lia; rewrite LEN, Z2Nat.id by lia; lia| rewrite LEN; lia].
symmetry. apply (rdn_nth M (Z.to_nat n) src bs Hs ltac:(rewrite Z2Nat.id by lia; lia) ltac:(rewrite Z2Nat.id by lia; exact D) RD). lia. }
split; [intros i Hi; apply (L5K.kept_ok_index R R3 i KO Hi)| exact A10].
Qed.
Lemma ec_agree : ltac2:(TCodec.tc2 tcn__PmBaKit "Q9'SCyR0%211'<y8%511%311p051'E&Q5r5r4r3+@%544321&RBz%2216&RA%1296&RG+2+R0%3221%9251&R8vS@r8r6%45321CBr7%655413Ep031p091p0A1p0E1pULL1pW>M1pVBN1pQDQ01pQBQ11").
Proof. intros M M' o v c.
intros AG H1 H2 (E0 & E8 & ED). split; [|split].
- apply (PMF.u32_at_agree segs M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact E0].
- apply (L5C.u64_at_agree segs M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact E8].
- apply (L5C.defined_agree M M' o 16 AG ED).
Qed.
End G.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmBaKit "Q6'9'QL%211&R0r2%211&RB&RF&8r3%2291%411&Q>%7221&QN%116&A&QA&QJr4%211%411%611&5r6(6r5(;%11K%43L31%73M61%L11p0:1p0B1p0E1p0N1pULQ31pW:Q31")) (only parsing).
Variables (stk : list PM.pstate).
Variable c : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Lemma stack_shape_push : ltac:(sec_stmt2 constr:(SECT) 2%nat 0%nat).
Proof.
intros (H1 & H2 & H3 & H4 & H5) HL Hc Hm. unfold PM.stack_shape. rewrite length_app. cbn [length].
split; [lia|]. split; [rewrite Nat2Z.inj_add; cbn; lia|].
split; [rewrite app_nth1 by lia; exact H3|].
split.
- intros i Hi. destruct (Nat.lt_ge_cases i (length stk)) as [Lt|Ge].
+ rewrite app_nth1 by exact Lt. apply H4. lia.
+ assert (E : i = length stk) by lia. subst i. rewrite app_nth2 by lia. rewrite Nat.sub_diag. exact Hm.
- intros i Hi. destruct (Nat.lt_ge_cases i (length stk)) as [Lt|Ge].
+ rewrite app_nth1 by exact Lt. apply H5. exact Lt.
+ assert (E : i = length stk) by lia. subst i. rewrite app_nth2 by lia. rewrite Nat.sub_diag. exact Hc.
Qed.
End S.
Lemma grow_credit : ltac2:(TCodec.tc2 tcn__PmBaKit "QN'Q2&O'QK&R6r5r4r3&QHr6r2%3221%847651'?'E&QC%116&RA%31;+1%3221%83751'R2&QE%11A%21C%=3421&QF%11F%21H%A3@21&RBz%B1H%3221r:&Q1r;r9&RE+Q0&RG+2r7%M11%L21J%5241%8271%<3;:1r8%Q:2=Q9%Q?4@321p0B1p0G1p0L1p0Q21p0Q<1pW0QF1pVNQG1pQHQI1pUNQJ1pV0QK1pQ>QM1").
Proof. intros L cr0 cr P0 s s'.
unfold PMSP.credit_keep, PM.pot_parser, PM.credit_add, PM.pot_stack, debit. cbn [fst snd].
intros (C1 & C2) Ek Et Eg Hk. rewrite Ek, Et, Eg.
assert (P : 2 ^ (PM.p_k s + 1 + 1) = 2 * 2 ^ (PM.p_k s + 1)) by (rewrite Z.pow_add_r by lia; lia).
rewrite P. split; lia.
Qed.
Lemma grow_credit_ok : ltac2:(TCodec.tc2 tcn__PmBaKit "R;'Q2&O'QK&R7r2r4%3221&R6r5r3&QHr6%2218%645841'>&RBz&QC%119%4231+:%6231%8231&Q4r8%211%;2:1&Q3r9%211%?2>1&7'E&QIr:&QE%11I&QF%11K%63531%93881%J2I1&=r;r7%:11%912%>3421%63@@1%Q22Q11&Q0r<&RE+Q0&RG+2&RA%Q81Q1+1%3221%6251%9281%<3;L1p0>1p0G1p0Q31p0Q81p0Q=1p0QG1p0QO1pVNR41pQHR61pUNR71pV0R81pQ>R:1").
Proof. intros L cr0 cr P0 s.
unfold PMSP.credit_le, PMSP.credit_keep, PM.pot_parser, PM.credit_add, PM.pot_stack, credit_ok. cbn [fst snd].
intros (L1 & L2) (C1 & C2) Hk HK HB T1 T2.
assert (P : 2 ^ (PM.p_k s + 1 + 1) <= 2 ^ 12) by (apply Z.pow_le_mono_r; lia).
assert (P' : 2 ^ (PM.p_k s + 1 + 1) = 2 * 2 ^ (PM.p_k s + 1)) by (rewrite Z.pow_add_r by lia; lia).
assert (Q : hl_k_per_malloc L <= hl_k_per_malloc L * (11 - PM.p_k s)) by (rewrite <- (Z.mul_1_r (hl_k_per_malloc L)) at 1; apply Z.mul_le_mono_nonneg_l; lia).
assert (Q2 : hl_b_overhead L <= (11 - PM.p_k s) * hl_b_overhead L) by (rewrite <- (Z.mul_1_l (hl_b_overhead L)) at 1; apply Z.mul_le_mono_nonneg_r; lia).
split; lia.
Qed.
End PMBK.
