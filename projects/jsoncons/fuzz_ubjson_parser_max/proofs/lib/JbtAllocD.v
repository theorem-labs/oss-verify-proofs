(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac JbtLeaf JbtPoison.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtAllocD () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtLeaf."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtPoison."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2I"; "2and"; "2eq"; "2or"; "3Z"; "4bvmap"; "0M"; "5Wn"; "5apart"; "5cell"; "5wr"; "6msteps"; "7art_tsd"; "8art_layout"; "9getr"]; ["9mkst"; "9regupd"; ":loaded_segments"; ";add"; ";div"; ";le"; ";lt"; ";min"; ";mul"; ";pow"; ";sub"; "0ab"; "0c"; "0ctx"; "0fx"; "0key"]; ["0mb"; "0mbs"; "0mc"; "0mr"; "0n"; "0regs"; "0rom"; "0rs"; "0rz"; "0sp"; "<BV"; "<Z_to_bv"; "<bv"; "0t"; "0tp"; "0tsd"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_alloc_d2a_fn := (ltac2:(TCodec.tc2 tcn__JbtAllocD "W?&6y5'Q<yR0%211%5241'0y8%611%311p061'5'3&?r?(Q:+2(1%33A21%6251&Q;r<%22C1%;3C41r@+4%;3I19%>231r9%92J1%B3J31rA+9%B3Q01@%E231r=%@2Q11%I3Q131rB+C%I3Q71G%L231&C%128F%H2Q91%Q13Q941&E+Q0%221H&F&I+R0%22Q41%42F1+Vb\P0%=218%:21B'2+1%=21E%>2FM%4221%D2HO+RPP0%B221z%D21L%E22Q0%C2Q1@%<221&;&BrK&JrI%221L%64541M&=rLrFrErDrC%6654321Q=+TP0%Q7213%Q<252%Q621Q3&9rM%A21Q;+QW`e0+8%543Q>21rN%F21Q@rJ+RH%I221%;44QD17rO%L21QF&H%12;7%QN2N1%A44QJ1=rQ0%Q221QL+TH%R32Q31%F43QO1BrQ1%Q721R1+Rg@%R82Q81+H%L44R521&:rQ4%R=2G6u8%45QB321Q?rQ5%RA2QC:%RB21Q0%85QF315QCrQ6%RE2QA>+@%RG221%=5QK41:QHrQ7%RJ2Q;C%QO4QN21B'<&@vNrQ9+ZYP0%SL3T81SJ/01T8rQ8%756521;&A%T13T?RFSO+ZYP4%T33T?1T1/01T?%53;41%T12TBG%732T41+:%T93TG1T7%S?2QKQ8+S@%SA221%T82TI1%>3751+;%T@3TN1T>+`0%T=2TN1%C3531+<%TE3U31TC%SK2R<S;%TB2U31%H3531+=%TJ3U81TH%T02RLQ@%TG2U81%M3531+>%TO3U=1TM+RPP1%TL2U=1%Q23531+ZYRH%U43U@1U2/01U@&8%S=2QHRJ%24QOQ:1Q6%S?2QJR5+`YQD%54R2321%64R31Q2F%TB2Q3S0%84R521C%TD2Q5QNrQ3%TF2R:1%SH21R7%TH2SJ1%>4R;651%QM5QLC@1R1%QO3SNQG1p0R11p0R51p0R;1p0R@1p0RF1p0RM1p0S31p0S:1p0SA1p0SH1p0SK1p0SN1p0T61p0T>1p0T?1p0T@1p0TD1p0TG1p0TK1p0U11p0U51p0U;1p0U?1p0UH1p0V01p0V81pR8VE1pR2VF1pR6VG1pRLVH1pQLVI1pS0VJ1pR0VK1pRNVL1pRBVM1pR@VN1pR:VO1pRDW01pR>W21p@W31pR<W91")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2a_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2a_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2a_fn) 2%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2a_fn) 3%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2a_fn) 4%nat 0%nat).
Variable rs : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2a_fn) 5%nat 0%nat).
Variable rz : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2a_fn) 6%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2a_fn) 7%nat 0%nat).
Variable key : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2a_fn) 8%nat 0%nat).
Variable tsd : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2a_fn) 9%nat 0%nat).
Variable ctx : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2a_fn) 10%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2a_fn) 11%nat 0%nat).
Variable mc : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2a_fn) 12%nat 0%nat).
Variable mb : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2a_fn) 13%nat 0%nat).
Variable mr : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2a_fn) 14%nat 0%nat).
Lemma art_alloc_d2a_fn : ltac:(sec_stmt2 constr:(SEC_T_art_alloc_d2a_fn) 15%nat 0%nat).
Proof using Type regs M rom sp n rs rz tp key tsd ctx t mc mb mr.
intros H2 H4 H9 H19 Hsp Hsp' IMG Hn Hprim Hrz Hmc Hmb Hmr W TSD Ht Ht' A1 A2 A3 A4 A5
Cmc Cmb Cmr Wts.
pose proof TSD as (_ & _ & _ & _ & _ & R).
stepn (ltac:(oF' 0x52400%Z)) (ltac:(oD' 0x52400%Z)).
zcall (art_thread_stats_fn _ _ _ _ sp tp key tsd ctx t).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (Cmc' : cellA X (t + 2800) 8 mc) by (unfold apart in *; recell Cmc);
assert (Cmb' : cellA X (t + 2800 + 8) 8 mb) by (unfold apart in *; recell Cmb);
assert (Cmr' : cellA X (t + 2800 + 16) 8 mr) by (unfold apart in *; recell Cmr);
assert (Wts' : wrA X (t + 2800) 24) by (repeat apply wr_Wn; exact Wts) end.
zld (ltac:(oF' 0x52404%Z)) (ltac:(oD' 0x52404%Z)) (t + 2800 + 16) Cmr'.
zld (ltac:(oF' 0x52408%Z)) (ltac:(oD' 0x52408%Z)) (t + 2800) Cmc'.
zld (ltac:(oF' 0x5240c%Z)) (ltac:(oD' 0x5240c%Z)) (t + 2800 + 8) Cmb'.
zstep (ltac:(oF' 0x52410%Z)) (ltac:(oD' 0x52410%Z)). zstep (ltac:(oF' 0x52414%Z)) (ltac:(oD' 0x52414%Z)). zstep (ltac:(oF' 0x52418%Z)) (ltac:(oD' 0x52418%Z)). zstep (ltac:(oF' 0x5241c%Z)) (ltac:(oD' 0x5241c%Z)). zstep (ltac:(oF' 0x52420%Z)) (ltac:(oD' 0x52420%Z)). zstep (ltac:(oF' 0x52424%Z)) (ltac:(oD' 0x52424%Z)).
zsd (ltac:(oF' 0x52428%Z)) (ltac:(oD' 0x52428%Z)) (t + 2800) (mc + 1) ltac:(rewok Wts').
zsd (ltac:(oF' 0x5242c%Z)) (ltac:(oD' 0x5242c%Z)) (t + 2800 + 8) (mb + n) ltac:(rewok Wts').
zsd (ltac:(oF' 0x52430%Z)) (ltac:(oD' 0x52430%Z)) (t + 2800 + 16) (mr + (rs + rz - n)) ltac:(rewok Wts').
zbtk (ltac:(oF' 0x52434%Z)) (ltac:(oD' 0x52434%Z)).
zstep (ltac:(oF' 0x52450%Z)) (ltac:(oD' 0x52450%Z)). zstep (ltac:(oF' 0x52454%Z)) (ltac:(oD' 0x52454%Z)).
zret.
Qed.
End SE.
#[using="Type"] Lemma art_alloc_d2b_small_fn : ltac2:(TCodec.tc2 tcn__JbtAllocD "R:&6y5'Q<yR0%211%5241'0y8%611%311p061'5'3&?r5(Q:+;(1%33A21%6251&Q;+`0%22C1%;3C41r6+C%;3I19%>231&Cr3r2%3221%<2M1%E3M61'2&E+1r4%:219%4231%522C%7221'<&B&@vNr8+ZYRH%Q13Q=1O/01Q=r7%756521K&A&D%J2Q8A+O%L221+Q0%5221%Q72QH1%83>Q:1+ZYZ4%Q?3QK1Q=/01QK%D5C41>Q8%G3F>1p0I1p0Q21p0Q=1pRBQJ1pR@QK1pR>QM1p@QN1pR<R41").
Proof.
intros regs M rom rs rz H11 H19 Hs.
zbft (ltac:(oF' 0x52458%Z)) (ltac:(oD' 0x52458%Z)).
zstep (ltac:(oF' 0x5245c%Z)) (ltac:(oD' 0x5245c%Z)).
stepn (ltac:(oF' 0x52460%Z)) (ltac:(oD' 0x52460%Z)). rwH. rewrite art_zb_srli by lia. change (2 ^ 5) with 32.
stepn (ltac:(oF' 0x52464%Z)) (ltac:(oD' 0x52464%Z)).
zret.
Qed.
#[using="Type"] Lemma art_alloc_d2b_big : ltac2:(TCodec.tc2 tcn__JbtAllocD "R2&6y5'Q<yR0%211%5241'0y8%611%311p061'5'3&?r5(Q:+;(1%33A21%6251&Q;+`0%22C1%;3C41r6+C%;3I19%>231&Cr3r2%3221%<2M1%E3M61'2&E+`1r4%:219%4231+RPP0%6231%8231'<&B&@vNr8+ZYRH%Q23Q>1Q0/01Q>r7%756521L+ZYS8%Q73QC1Q5/01QC%;5:915Q0%>3=51p0@1p0J1p0Q51pRBQB1pR@QC1pR>QE1p@QF1pR<QL1").
Proof.
intros regs M rom rs rz H11 H19 Hs.
zbtk (ltac:(oF' 0x52458%Z)) (ltac:(oD' 0x52458%Z)). apply mst_refl.
Qed.
Section SE.
Local Abbreviation SEC_T_art_alloc_d2c_fn := (ltac2:(TCodec.tc2 tcn__JbtAllocD "VI&6y5'Q<yR0%211%5241'0y8%611%311p061'5'3&?r:(Q:+2(1%33A21%6251&Q;r7%22C1%;3C41r;+9%;3I19%>231r6%92J1%B3J31r<+:%B3Q01@%E231&Cr4+Rg@%3221+S@%5221%E2Q61%N3Q681r=+;%N3Q<1L%Q1231%Q33Q;1Br>+D%Q33QA1Q1%Q6231r8%B2Q71%Q22QC1%Q;3QC41&Ez%221K&F+T0%J2B1&I+R0%22Q@1%6241+Vb\P0%;21C'2+1%>21K+Q8%:2QH1%>2N1%6241%C26Q<+QD%E2Q>1%:231+TP0%H21QA%Q>2Q62%G21B%K2JQ8%I2Q9D%A221rCrA%QE221%Q12Q01%O22J%G221&:&BrGr@%QM21QK%QN21QJ&H+8%221=%R2241u8r?%<5;:321&;rH%R82DR6%R921R5rB%<2;1%R<231%74C61=&9%R?25R=%R@21R<%B2AN%RB221%541CHQJ'4%RE2Q2Q9+RPP0%R2221%R32QIQ5%5221rKrI%RL21L%Q45Q331JQK&>rL%211rM+QWXaH+Q<%S4221u4%Q=5Q<521QJrN%S826QO+UN%QA5Q@3251'<&@vNrQ0+ZYZ4%T43T@1T2/01T@rO%756521<&A%T93TGRCT7+ZY\D%T;3TG1T9/01TG%53;41rJ%SK2L1%T;2TL1%934SO1%T=2TNE%;32SE1+<%TE3U31TC&G%12Q9RG%TC2U41%A3641+=%TK3U91TI+QTjo8%TH2U91%F3531%TO3U;3TM/01U;&8%T>2R7T<%T?21T;%RA2R@QE%TA221%TB2RGS@%64R@Q121%Q85Q7:81Q=%Q:3RKQ21p0Q<1p0QA1p0QH1p0QL1p0R11p0R81p0R?1p0RH1p0S61p0S=1p0SA1p0SD1p0SG1p0SL1p0T41p0T71p0T?1p0TC1p0TL1p0U21p0U?1p0UG1pR4V41pRLV51pQJV61pRBV71pR:V81pQHV91pRDV:1pR>V<1p@V=1pR<VC1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2c_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2c_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2c_fn) 2%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2c_fn) 3%nat 0%nat).
Variable ab : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2c_fn) 4%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2c_fn) 5%nat 0%nat).
Variable rz : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2c_fn) 6%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2c_fn) 7%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2c_fn) 8%nat 0%nat).
Variable mbs : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2c_fn) 9%nat 0%nat).
Lemma art_alloc_d2c_fn : ltac:(sec_stmt2 constr:(SEC_T_art_alloc_d2c_fn) 10%nat 0%nat).
Proof using Type regs M rom sp ab n rz c t mbs.
intros H2 H9 H10 H11 H20 Hsp Hsp' IMG Hn Hc Ht Ht' Hmbs Hub Cmbs Wmbs A1 Timg Ccf L Cmax Cfb.
pose proof L as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
stepn (ltac:(oF' 0x52544%Z)) (ltac:(oD' 0x52544%Z)). rwH. rewrite art_zb_slli by lia. change (2 ^ 3) with 8.
zstep (ltac:(oF' 0x52548%Z)) (ltac:(oD' 0x52548%Z)).
zld (ltac:(oF' 0x5254c%Z)) (ltac:(oD' 0x5254c%Z)) (t + 2800 + 112 + 8 * c) Cmbs.
zstep (ltac:(oF' 0x52550%Z)) (ltac:(oD' 0x52550%Z)).
zsd (ltac:(oF' 0x52554%Z)) (ltac:(oD' 0x52554%Z)) (t + 2800 + 112 + 8 * c) (mbs + 1) ltac:(rewok Wmbs).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (Ccf' : cellA X (sp + 8) 8 1) by (unfold apart in *; recell Ccf);
assert (G40' : cellA X 0x134398 8 0x13a238) by (unfold apart in *; recell G40);
assert (Cmax' : cellA X (0x13a238 + 44) 4 4096) by (unfold apart in *; recell Cmax);
assert (G68' : cellA X 0x1343c0 8 0x1363b0) by (unfold apart in *; recell G68);
assert (Crm' : cellA X 0x1363b0 8 0x126be8) by (unfold apart in *; recell Crm);
assert (Cfb' : cellA X (0x13a238 + 52) 4 190) by (unfold apart in *; recell Cfb) end.
zld (ltac:(oF' 0x52558%Z)) (ltac:(oD' 0x52558%Z)) (sp + 8) Ccf'.
zbft (ltac:(oF' 0x5255c%Z)) (ltac:(oD' 0x5255c%Z)).
zstep (ltac:(oF' 0x52560%Z)) (ltac:(oD' 0x52560%Z)). zld (ltac:(oF' 0x52564%Z)) (ltac:(oD' 0x52564%Z)) 0x134398 G40'.
zlw (ltac:(oF' 0x52568%Z)) (ltac:(oD' 0x52568%Z)) (0x13a238 + 44) Cmax'.
zbft (ltac:(oF' 0x5256c%Z)) (ltac:(oD' 0x5256c%Z)).
zstep (ltac:(oF' 0x52570%Z)) (ltac:(oD' 0x52570%Z)).
destruct (Z.lt_ge_cases n 4096) as [Sm|Bg].
- zbtk (ltac:(oF' 0x52574%Z)) (ltac:(oD' 0x52574%Z)).
zstep (ltac:(oF' 0x5257c%Z)) (ltac:(oD' 0x5257c%Z)). zld (ltac:(oF' 0x52580%Z)) (ltac:(oD' 0x52580%Z)) 0x1343c0 G68'. zld (ltac:(oF' 0x52584%Z)) (ltac:(oD' 0x52584%Z)) 0x1363b0 Crm'.
zlw (ltac:(oF' 0x52588%Z)) (ltac:(oD' 0x52588%Z)) (0x13a238 + 52) Cfb'.
zstep (ltac:(oF' 0x5258c%Z)) (ltac:(oD' 0x5258c%Z)).
stepjr (ltac:(oF' 0x52590%Z)) (ltac:(oD' 0x52590%Z)) (0x126be8 : bv 64)%bv ltac:(gres; bveq).
zret.
- zbft (ltac:(oF' 0x52574%Z)) (ltac:(oD' 0x52574%Z)).
zstep (ltac:(oF' 0x52578%Z)) (ltac:(oD' 0x52578%Z)).
zstep (ltac:(oF' 0x5257c%Z)) (ltac:(oD' 0x5257c%Z)). zld (ltac:(oF' 0x52580%Z)) (ltac:(oD' 0x52580%Z)) 0x1343c0 G68'. zld (ltac:(oF' 0x52584%Z)) (ltac:(oD' 0x52584%Z)) 0x1363b0 Crm'.
zlw (ltac:(oF' 0x52588%Z)) (ltac:(oD' 0x52588%Z)) (0x13a238 + 52) Cfb'.
zstep (ltac:(oF' 0x5258c%Z)) (ltac:(oD' 0x5258c%Z)).
stepjr (ltac:(oF' 0x52590%Z)) (ltac:(oD' 0x52590%Z)) (0x126be8 : bv 64)%bv ltac:(gres; bveq).
zret.
Qed.
End SE.
End FPX.
