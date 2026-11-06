(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib
ArtMem ArtRegs ArtAtomics ArtTac JatCachePop JatCombAlloc.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatCASec () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatCachePop."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatCombAlloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2I"; "2and"; "2eq"; "2ex"; "3Z"; "4bvmap"; "0M"; "5cell"; "5wr"; "6msteps"; "7ret_ok"; "8art_pop_kept"; "9art_ca_frame"; ":getr"; ":mkst"]; [":regupd"; ";loaded_segments"; "<add"; "<le"; "<lt"; "<pow"; "<sub"; "0fx"; "0ia"; "0r"; "0raw"; "0regs"; "0regs'"; "0rom"; "0s"; "0s0v"]; ["0s1v"; "0s2v"; "0s3v"; "0s4v"; "0sp"; "=BV"; "=Z_to_bv"; "=bv"; "=bv_unsigned"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_ca_sec_pre_fn := (ltac2:(TCodec.tc2 tcn__JatCASec "TK&6y5'Q7yR0%211%5241'0y8%611%311p061'5'3&>r6(Q5+2(1%33A21%6251&Q6r3%22C1%;3C41r7+:%;3I19%>231%@3H16r8+<%@3N1>%C231%E3M1;r9+=%E3Q31C%H231+8%C2Q41%L3Q431&C+Q@%221C&D&E+R0%22O1%42C1'2+RPP0%721K+Q8%82Q51%:2N1%6241z%@21G&Br:+TP0%3221%B21?&9&Ar>&Fr<%221J%64541K':&?vGr@+ZhiL%QL3R81QJ/01R8r?%756521=&@+1%R23R@1R0+Zho4%R43R@1R2/01R@%63<41r=%E21Q=%R42RE1%:34R71%R;3RIQDR9%<321QD%Q22IQ>%R92RJ1%?33R41+;%RA3RO1R?+e@%Q82O1%R?2S01%E3641r;%RB2S31%H33R81+>%RJ3S81RH%K331=+?%RM3S;1RK%RI2S:QK%O3421+Zi`D%S13S=1RO/01S=&=&Q8%S72Q;Q3%22SB1%S92Q=L%42SD1+9%S:3SH1S8%S=2QA1%82SH1+B%S>3SL1S<%SA2QE1%<2SL1+C%SB3T01S@%SE2QI1%@2T01+D%SF3T41SD%SI2QM1%D2T41%F8QKQBCA=951%R25R1KH1R8%R43R:QL1p0R61p0R>1p0RD1p0RG1p0RO1p0S51p0S91p0SA1p0SG1p0SM1pQNT:1pQBT;1pR:T<1pQLT>1p@T?1pQHTE1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ca_sec_pre_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ca_sec_pre_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ca_sec_pre_fn) 2%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_ca_sec_pre_fn) 3%nat 0%nat).
Variable ia : ltac:(sec_ty2 constr:(SEC_T_art_ca_sec_pre_fn) 4%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SEC_T_art_ca_sec_pre_fn) 5%nat 0%nat).
Lemma art_ca_sec_pre_fn : ltac:(sec_stmt2 constr:(SEC_T_art_ca_sec_pre_fn) 6%nat 0%nat).
Proof using Type regs M rom sp ia s.
intros H2 H10 H12 H13 Hsp Hsp' Hs Hia Hia' W.
zstep (ltac:(oF' 0x5633c%Z)) (ltac:(oD' 0x5633c%Z)).
zsd (ltac:(oF' 0x56340%Z)) (ltac:(oD' 0x56340%Z)) (sp - 8) (U (getr regs 1)) ltac:(rewok W).
zsd (ltac:(oF' 0x56344%Z)) (ltac:(oD' 0x56344%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W).
zsd (ltac:(oF' 0x56348%Z)) (ltac:(oD' 0x56348%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W).
zsd (ltac:(oF' 0x5634c%Z)) (ltac:(oD' 0x5634c%Z)) (sp - 32) (U (getr regs 18)) ltac:(rewok W).
zsd (ltac:(oF' 0x56350%Z)) (ltac:(oD' 0x56350%Z)) (sp - 40) (U (getr regs 19)) ltac:(rewok W).
zsd (ltac:(oF' 0x56354%Z)) (ltac:(oD' 0x56354%Z)) (sp - 48) (U (getr regs 20)) ltac:(rewok W).
zstep (ltac:(oF' 0x56358%Z)) (ltac:(oD' 0x56358%Z)).
zstep (ltac:(oF' 0x5635c%Z)) (ltac:(oD' 0x5635c%Z)).
zstep (ltac:(oF' 0x56360%Z)) (ltac:(oD' 0x56360%Z)).
zbtk (ltac:(oF' 0x56364%Z)) (ltac:(oD' 0x56364%Z)).
zstep (ltac:(oF' 0x56388%Z)) (ltac:(oD' 0x56388%Z)).
zstep (ltac:(oF' 0x5638c%Z)) (ltac:(oD' 0x5638c%Z)).
zbtk (ltac:(oF' 0x56390%Z)) (ltac:(oD' 0x56390%Z)).
zstep (ltac:(oF' 0x563b0%Z)) (ltac:(oD' 0x563b0%Z)).
zbft (ltac:(oF' 0x563b4%Z)) (ltac:(oD' 0x563b4%Z)).
zbtk (ltac:(oF' 0x563b8%Z)) (ltac:(oD' 0x563b8%Z)).
zstep (ltac:(oF' 0x563d0%Z)) (ltac:(oD' 0x563d0%Z)). zstep (ltac:(oF' 0x563d4%Z)) (ltac:(oD' 0x563d4%Z)). zstep (ltac:(oF' 0x563d8%Z)) (ltac:(oD' 0x563d8%Z)). zstep (ltac:(oF' 0x563dc%Z)) (ltac:(oD' 0x563dc%Z)).
stepn (ltac:(oF' 0x563e0%Z)) (ltac:(oD' 0x563e0%Z)).
zret.
Qed.
End SE.
#[local] Ltac post_kept :=
intros r Hr; unfold art_pop_kept in Hr; destruct Hr as (?&?&?&?&?&?&?&?&?); gres; try reflexivity;
repeat (rewrite getr_other by (assumption || (symmetry; assumption) || reg_neq_tac)); reflexivity.
#[using="Type"] Lemma art_ca_sec_post : ltac2:(TCodec.tc2 tcn__JatCASec "U5&6y5'Q7yR0%211%5241'0y8%611%311p061'5'3&>r:(Q5+8(1%33A21%6251&Q6%12B5%:3B31r;+2%:3H18%=231r8%82I1%A3I31&Czr9%3221&D&B+Q@%22G1&E+R0%22@1%7241&8&Ar=+Q8%;2G1u8&Q8%12Q>Q3%8576431&;%11Mr?+Q0%D2;1%>5=319Q1r@r>+H%I221%C5B41>Q6rA+@%M2;1%G5F31BQ:rB%Q02:QC%J5I21EQ=rC%L5K18GQ?'4'2':&?vGrF+Zho4%QO3R;1QM/01R;rErD%8576321r1%:591B43%<3Q:31+:%R83RF1R6%R;251%R<2=2%R>3RF21%R>28R2%QI2GQH%R92RJ1%RB3RJ31+1%RA3RO1R?%RD2>1%RF3RN1Q0%RF2@RA%R@2S1Q6%RI3S121+9%RH3S61RF%RK2E1%RE2S6Q@%RN3S621+B%RM3S;1RK%S02J1%RJ2S;QI%S33S;21+C%S23S@1S0%S52O1%RO2S@QI%S83S@21+D%S73SE1S5%S:2Q41%S42SER<%S=3SE21%SH1SI&<%11Q9r3r2%SB221rH%SD213%SF3SN31p071pQD:1%QM2<1%QN2B1%QO2H1%R02N1%R12Q41%R22Q81%R32Q=1%R42QB1%R52QH1qQJT91%R82T:1p0R:1p0R=1p0RA1p0RF1p0RL1p0S11p0S41p0S>1p0SG1p0SL1p0T41pR8T@1pR6TA1pR4TB1pR2TC1pR0TD1pQFTL1pR:TF1pQLTH1p@TI1pQHTO1").
Proof.
intros regs M rom sp raw s0v s1v s2v s3v s4v H8 H2 Hsp Hsp' Cra Hret C0 C1 C2 C3 C4.
eexists. split.
- zstep (ltac:(oF' 0x563e4%Z)) (ltac:(oD' 0x563e4%Z)).
zstep (ltac:(oF' 0x563e8%Z)) (ltac:(oD' 0x563e8%Z)).
zbft (ltac:(oF' 0x563ec%Z)) (ltac:(oD' 0x563ec%Z)).
stepn (ltac:(oF' 0x563f0%Z)) (ltac:(oD' 0x563f0%Z)).
zld (ltac:(oF' 0x56540%Z)) (ltac:(oD' 0x56540%Z)) (sp + 40) Cra. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x56544%Z)) (ltac:(oD' 0x56544%Z)) (sp + 32) C0.
zld (ltac:(oF' 0x56548%Z)) (ltac:(oD' 0x56548%Z)) (sp + 24) C1.
zld (ltac:(oF' 0x5654c%Z)) (ltac:(oD' 0x5654c%Z)) (sp + 16) C2.
zld (ltac:(oF' 0x56550%Z)) (ltac:(oD' 0x56550%Z)) (sp + 8) C3.
zld (ltac:(oF' 0x56554%Z)) (ltac:(oD' 0x56554%Z)) sp C4.
zstep (ltac:(oF' 0x56558%Z)) (ltac:(oD' 0x56558%Z)).
stepret (ltac:(oF' 0x5655c%Z)) (ltac:(oD' 0x5655c%Z)) raw ltac:(rwH; reflexivity).
apply mst_refl.
- repeat (split; [gres; reflexivity|]). post_kept.
Qed.
End FPX.
