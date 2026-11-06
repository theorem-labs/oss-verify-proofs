(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac RefMemcpyLib MemsetLib As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac JbtLeaf JbtAllocG JbtPoison ArtRuns ArtRunsMem JbtFp Jb0IntMemset JbtFree1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtFxInit () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFxInit."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.MemsetLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1cons"; "1nat"; "1nil"; "1option"; "2I"; "2and"; "2eq"; "2ex"; "3Z"; "4bvmap"; "0M"; "5Wf"; "5cell"; "5wok"; "5wr"]; ["6msteps"; "7ret_ok"; "8art_ia_k1"; "8art_ia_k2"; "8art_ia_k3"; "8art_ia_k4"; "8art_ia_mem"; "9cbyte"; "9ms_agree"; ":getr"; ":mkst"; ";loaded_segments"; "<In"; "=add"; "=le"; "=lt"]; ["=of_nat"; "=pow"; "=sub"; "0X"; "0a"; "0fx"; "0i"; "0k"; "0r"; "0raw"; "0regs"; "0regs'"; "0ret"; "0rom"; "0sp"; ">BV"]; [">Z_to_bv"; ">bv"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Definition art_ia_k1 : nat := Z.to_nat 40.
Definition art_ia_k2 : nat := Z.to_nat 0x40000.
Definition art_ia_k3 : nat := Z.to_nat 0xd80.
Definition art_ia_k4 : nat := Z.to_nat 0x40248.
Lemma art_ia_k1_Z : ltac2:(TCodec.tc2 tcn__JbtFxInit "7'7'9&Q0&B%211+Q8%63521"). Proof. unfold art_ia_k1. apply Z2Nat.id. lia. Qed.
Lemma art_ia_k2_Z : ltac2:(TCodec.tc2 tcn__JbtFxInit "7'7'9&Q0&C%211+XPP0%63521"). Proof. unfold art_ia_k2. apply Z2Nat.id. lia. Qed.
Lemma art_ia_k3_Z : ltac2:(TCodec.tc2 tcn__JbtFxInit "7'7'9&Q0&D%211+S\0%63521"). Proof. unfold art_ia_k3. apply Z2Nat.id. lia. Qed.
Lemma art_ia_k4_Z : ltac2:(TCodec.tc2 tcn__JbtFxInit "7'7'9&Q0&E%211+XPb8%63521"). Proof. unfold art_ia_k4. apply Z2Nat.id. lia. Qed.
Global Opaque art_ia_k1 art_ia_k2 art_ia_k3 art_ia_k4.
Lemma art_cbyte0 : ltac2:(TCodec.tc2 tcn__JbtFxInit "<'7'QAy8%211&G&Q@yR0z%3221%511%5283%;3821").
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Definition art_ia_mem (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
Wn 1 (Wn 1 (Wn 8 (Wn 8
(Wf (Wf (Wf (Wn 1 (Wf
(Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18))) (sp - 40) (U (getr regs 19)))
0x1cc4c8 256)
0x1bec48 art_ia_k1 0) 0x13dc40 0) 0x13dc48 art_ia_k2 0) 0x17dc80 art_ia_k3 0) 0x17ea00 art_ia_k4 0)
0x17ea00 4096) 0x17ea08 0x17ea10) 0x1cc4c8 1) 0x1cc4c9 0.
Section FPX. Context {fx : PropExec.FPState}.
#[using="Type"] Lemma art_int_memset0 : ltac2:(TCodec.tc2 tcn__JbtFxInit "S:'QAyR0%211'4y8%511%311p051'9'2&:y5%221:&>&Kr6r4r3%544321&Nzr5%3221&O&M&Q0%115%32<1&Q1+2+R0%3221%9251&A%11B'7&I(Q?+:(5%33M21%52J1&Q@r8%22Q;1%:3Q;41r7+;%;3Q519%=231%82QAN%@3QA21+<%@3Q:1>%B2;1r9%O11%?2QH1%G3QH41+1%G3QA1E%I261%K3QL1C'8'6'@&JvQ5r;+a[^H%Q13R51O/01R5r?r>%8576321r1r:&<r=r<%34821QL%?5>6518%A3R481%Q?28Q;%Q:2RC6%QB3RC21&H%12C<%H231%I271qRHR>1%L2R?1p0N1p0Q31p0Q;1p0QB1p0QN1p0R11p0R<1p0RA1pRJS21pRFRI1pR@RM1pR:RO1pRLS11pR8S21").
Proof.
intros X rom a k regs ret OK Ha Hk Hret H10 H11 H12 H1.
pose proof (int_memset_run X (Z_to_bv 64 a) (Z_to_bv 64 0) ret (Z.of_nat k) rom ltac:(lia) ltac:(rewrite art_u_lit by lia; lia)) as T.
rewrite Nat2Z.id in T. specialize (T OK Hret regs H10 H11 H12 H1 ltac:(rewrite art_u_lit by lia; lia)).
rewrite art_cbyte0 in T. exact T.
Qed.
Ltac zmemset0 D K EK RET Wb rnew HK :=
match goal with |- msteps _ (mkst ?R _ ?X ?rom) _ =>
let RUN := fresh "RUN" in let A10 := fresh "A10" in
destruct (art_int_memset0 X rom D K R RET ltac:(apply (wr_wok _ _ _ _ Wb); rewrite ?EK; lia) ltac:(lia) ltac:(rewrite EK; lia)
ltac:(unfold ret_ok; bveq)
ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; rewrite EK; reflexivity) ltac:(gres; bveq)) as (rnew & RUN & A10 & HK);
eapply msteps_trans; [exact RUN|]; clear RUN
end.
Ltac zkeep HK rnew i V := let E := fresh "E" in assert (E : getr rnew i = V) by (rewrite (ms_agree_getr _ _ i HK) by (cbv; intuition discriminate); gres; rwH; reflexivity).
Section SE.
Local Abbreviation SEC_T_art_ia_init_run := (ltac2:(TCodec.tc2 tcn__JbtFxInit "U@&:y5'QAyR0%211%5241'4y8%611%311p061'9'7&Ir5(Q?+1(5%33A21%6251r2%93A21&Ar3%211r7+2%<3J1:%?231&Q@%12K7%C3K31&N+Q@r4%3221&O&Q1+R0%22=1%42J1&M+Vb\P0%221:r6%=221&?&Kr:&Q2%12IA%54431B&=r;+QiaV8u4z%55:4321r<+4%>4=261r=+QWgR0+`TQ@%B4A321r>+QV`l0u8+QiaW0%A5F4321r?+TP0%D5I2451'8'6'@&JvQ5rB+`dfH%R13R=1QO/01R=rAr@%8576321r1&F%145FA9%<5;3B15%>3Q:51+:%R<3RJ1R:%R?271%R02RJO%RB3RJ21%RB2:R=%RD3RL1J%RD2<R6%R52ROQ1%RG3RO21%S21S3&L(1+3%RI3S71RG%RJ3S8Q>RH+8%RL3S:1RJ+9%RN3S<1RL+B%S03S>1RN+C%S23S@1S0+D%S43SB1S2+E%S63SD1S4+F%S83SF1S6+G%S:3SH1S8+H%S<3SJ1S:+I%S>3SL1S<+J%S@3SN1S>+K%SB3T01S@(3%11O%N3Q031%O3Q161%Q03Q291%Q13Q3<1%Q23Q4?1%Q33Q5B1%Q43Q6E1%Q53Q7H1%Q63Q8K1%Q73Q9N1%Q83Q:Q11%Q93Q;Q41%Q:3Q<Q71%Q;3Q=Q91%Q=3Q>QM1%T62SLSOrD%T821T1%T:3TB31p051pRBQD1%R?2QF1%R@2QJ1%RA2QM1%RB2R31qRHTH1%RE2TI1p0RG1p0RK1p0S11p0S61p0S:1p0SA1p0SH1p0SN1p0T41p0T91p0TA1p0TE1pRNU01pRDU81pRLU31pHU41pRFU:1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ia_init_run) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ia_init_run) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ia_init_run) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_ia_init_run) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_ia_init_run) 4%nat 0%nat).
Lemma art_ia_init_run : ltac:(sec_stmt2 constr:(SEC_T_art_ia_init_run) 5%nat 0%nat).
Proof using Type regs M rom raw sp.
intros H1 Hret H2 Hsp Hsp' IMG W Cw Ww Wbss Cps1 Cps2.
pose proof art_ia_k1_Z as K1. pose proof art_ia_k2_Z as K2. pose proof art_ia_k3_Z as K3. pose proof art_ia_k4_Z as K4.
eassert (RUN0a : msteps ASEGS (mkst regs (0x852d8 : word) M rom) _).
{
zstep (ltac:(oF' 0x852d8%Z)) (ltac:(oD' 0x852d8%Z)).
zsd (ltac:(oF' 0x852dc%Z)) (ltac:(oD' 0x852dc%Z)) (sp - 8) (U raw) ltac:(rewok W).
zsd (ltac:(oF' 0x852e0%Z)) (ltac:(oD' 0x852e0%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W).
zsd (ltac:(oF' 0x852e4%Z)) (ltac:(oD' 0x852e4%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W).
zsd (ltac:(oF' 0x852e8%Z)) (ltac:(oD' 0x852e8%Z)) (sp - 32) (U (getr regs 18)) ltac:(rewok W).
zsd (ltac:(oF' 0x852ec%Z)) (ltac:(oD' 0x852ec%Z)) (sp - 40) (U (getr regs 19)) ltac:(rewok W).
zstep (ltac:(oF' 0x852f0%Z)) (ltac:(oD' 0x852f0%Z)). zstep (ltac:(oF' 0x852f4%Z)) (ltac:(oD' 0x852f4%Z)).
destruct (cell4_split M 0x1cc4c8 0 ltac:(lia) ltac:(lia) ltac:(lia) Cw) as (Cb0 & Cb1 & Cb2).
change (0 mod 256) with 0 in Cb0.
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cb0' : cellA X 0x1cc4c8 1 0) by (recell Cb0) end.
zlb (ltac:(oF' 0x852f8%Z)) (ltac:(oD' 0x852f8%Z)) 0x1cc4c8 Cb0'.
stepfence (ltac:(oF' 0x852fc%Z)) (ltac:(oD' 0x852fc%Z)).
zbft (ltac:(oF' 0x85300%Z)) (ltac:(oD' 0x85300%Z)).
zstep (ltac:(oF' 0x85304%Z)) (ltac:(oD' 0x85304%Z)). zstep (ltac:(oF' 0x85308%Z)) (ltac:(oD' 0x85308%Z)). zstep (ltac:(oF' 0x8530c%Z)) (ltac:(oD' 0x8530c%Z)).
stepn (ltac:(oF' 0x85310%Z)) (ltac:(oD' 0x85310%Z)). rwH. zclosed 0x1cc4c8.
stepn (ltac:(oF' 0x85314%Z)) (ltac:(oD' 0x85314%Z)). rwH. zclosed 1.
stepn (ltac:(oF' 0x85318%Z)) (ltac:(oD' 0x85318%Z)). rwH. zclosed 8.
stepn (ltac:(oF' 0x8531c%Z)) (ltac:(oD' 0x8531c%Z)). rwH. zclosed 65280.
stepn (ltac:(oF' 0x85320%Z)) (ltac:(oD' 0x85320%Z)). rwH. zclosed 256.
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cw' : cellA X 0x1cc4c8 4 0) by (recell Cw); assert (Ww' : wokA X 0x1cc4c8 4) by (rewok Ww) end.
zcas6 (ltac:(oF' 0x85324%Z)) (ltac:(oD' 0x85324%Z)) (ltac:(oF' 0x85328%Z)) (ltac:(oD' 0x85328%Z)) (ltac:(oF' 0x8532c%Z)) (ltac:(oD' 0x8532c%Z)) (ltac:(oF' 0x85330%Z)) (ltac:(oD' 0x85330%Z)) (ltac:(oF' 0x85334%Z)) (ltac:(oD' 0x85334%Z)) (ltac:(oF' 0x85338%Z)) (ltac:(oD' 0x85338%Z)) 0x1cc4c8 0 256 256 256 Cw' Ww'.
zbft (ltac:(oF' 0x8533c%Z)) (ltac:(oD' 0x8533c%Z)).
stepn (ltac:(oF' 0x85340%Z)) (ltac:(oD' 0x85340%Z)). rwH. zclosed 0.
stepn (ltac:(oF' 0x85344%Z)) (ltac:(oD' 0x85344%Z)). rwH. zclosed 0.
zbft (ltac:(oF' 0x85348%Z)) (ltac:(oD' 0x85348%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (Cw1 : cellA X 0x1cc4c8 4 256) by (apply cell_Wn_hit; lia);
destruct (cell4_split X 0x1cc4c8 256 ltac:(lia) ltac:(lia) ltac:(lia) Cw1) as (Cl0 & _ & Cl2) end.
change (256 mod 256) with 0 in Cl0. change (256 / 65536) with 0 in Cl2.
zlb (ltac:(oF' 0x8534c%Z)) (ltac:(oD' 0x8534c%Z)) 0x1cc4c8 Cl0.
zbft (ltac:(oF' 0x85350%Z)) (ltac:(oD' 0x85350%Z)).
zstep (ltac:(oF' 0x85354%Z)) (ltac:(oD' 0x85354%Z)). zstep (ltac:(oF' 0x85358%Z)) (ltac:(oD' 0x85358%Z)). zstep (ltac:(oF' 0x8535c%Z)) (ltac:(oD' 0x8535c%Z)).
stepn (ltac:(oF' 0x85360%Z)) (ltac:(oD' 0x85360%Z)). rwH. zclosed 0x81008.
zstep (ltac:(oF' 0x85364%Z)) (ltac:(oD' 0x85364%Z)). zstep (ltac:(oF' 0x85368%Z)) (ltac:(oD' 0x85368%Z)). zstep (ltac:(oF' 0x8536c%Z)) (ltac:(oD' 0x8536c%Z)).
stepn (ltac:(oF' 0x85370%Z)) (ltac:(oD' 0x85370%Z)).
apply mst_refl. }
match type of RUN0a with msteps _ _ (mkst ?R _ ?X _) => assert (Wb0 : wrA X 0x13dc40 0x81030) by zwr;
destruct (art_int_memset0 X rom 0x1bec48 art_ia_k1 R (0x85374 : bv 64)%bv ltac:(apply (wr_wok _ _ _ _ Wb0); rewrite ?art_ia_k1_Z; lia) ltac:(lia) ltac:(rewrite art_ia_k1_Z; lia) ltac:(unfold ret_ok; bveq)
ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; rewrite art_ia_k1_Z; reflexivity) ltac:(gres; bveq)) as (r1 & RUN0b & _ & HK1) end.
zkeep HK1 r1 (2%bv : reg) (Z_to_bv 64 (sp + -48)). zkeep HK1 r1 (8%bv : reg) (Z_to_bv 64 0x1cc4c8). zkeep HK1 r1 (9%bv : reg) (Z_to_bv 64 0x13dc40).
match type of RUN0b with msteps _ _ ?S1 => eassert (RUN1a : msteps ASEGS S1 _) end.
{
zsb (ltac:(oF' 0x85374%Z)) (ltac:(oD' 0x85374%Z)) 0x13dc40 0 ltac:(zwok').
zstep (ltac:(oF' 0x85378%Z)) (ltac:(oD' 0x85378%Z)). zstep (ltac:(oF' 0x8537c%Z)) (ltac:(oD' 0x8537c%Z)). zstep (ltac:(oF' 0x85380%Z)) (ltac:(oD' 0x85380%Z)). zstep (ltac:(oF' 0x85384%Z)) (ltac:(oD' 0x85384%Z)).
stepn (ltac:(oF' 0x85388%Z)) (ltac:(oD' 0x85388%Z)).
apply mst_refl. }
match type of RUN1a with msteps _ _ (mkst ?R _ ?X _) => assert (Wb1 : wrA X 0x13dc40 0x81030) by zwr;
destruct (art_int_memset0 X rom 0x13dc48 art_ia_k2 R (0x8538c : bv 64)%bv ltac:(apply (wr_wok _ _ _ _ Wb1); rewrite ?art_ia_k2_Z; lia) ltac:(lia) ltac:(rewrite art_ia_k2_Z; lia) ltac:(unfold ret_ok; bveq)
ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; rewrite art_ia_k2_Z; reflexivity) ltac:(gres; bveq)) as (r2 & RUN1b & _ & HK2) end.
zkeep HK2 r2 (2%bv : reg) (Z_to_bv 64 (sp + -48)). zkeep HK2 r2 (8%bv : reg) (Z_to_bv 64 0x1cc4c8). zkeep HK2 r2 (9%bv : reg) (Z_to_bv 64 0x13dc40).
zkeep HK2 r2 (19%bv : reg) (Z_to_bv 64 262144).
match type of RUN1b with msteps _ _ ?S1 => eassert (RUN2a : msteps ASEGS S1 _) end.
{
stepn (ltac:(oF' 0x8538c%Z)) (ltac:(oD' 0x8538c%Z)). rwH. zclosed 0x40040.
zstep (ltac:(oF' 0x85390%Z)) (ltac:(oD' 0x85390%Z)). zstep (ltac:(oF' 0x85394%Z)) (ltac:(oD' 0x85394%Z)).
stepn (ltac:(oF' 0x85398%Z)) (ltac:(oD' 0x85398%Z)). rwH. zclosed 0xd80.
zstep (ltac:(oF' 0x8539c%Z)) (ltac:(oD' 0x8539c%Z)).
stepn (ltac:(oF' 0x853a0%Z)) (ltac:(oD' 0x853a0%Z)).
apply mst_refl. }
match type of RUN2a with msteps _ _ (mkst ?R _ ?X _) => assert (Wb2 : wrA X 0x13dc40 0x81030) by zwr;
destruct (art_int_memset0 X rom 0x17dc80 art_ia_k3 R (0x853a4 : bv 64)%bv ltac:(apply (wr_wok _ _ _ _ Wb2); rewrite ?art_ia_k3_Z; lia) ltac:(lia) ltac:(rewrite art_ia_k3_Z; lia) ltac:(unfold ret_ok; bveq)
ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; rewrite art_ia_k3_Z; reflexivity) ltac:(gres; bveq)) as (r3 & RUN2b & _ & HK3) end.
zkeep HK3 r3 (2%bv : reg) (Z_to_bv 64 (sp + -48)). zkeep HK3 r3 (8%bv : reg) (Z_to_bv 64 0x1cc4c8). zkeep HK3 r3 (9%bv : reg) (Z_to_bv 64 0x13dc40).
zkeep HK3 r3 (19%bv : reg) (Z_to_bv 64 262144).
match type of RUN2b with msteps _ _ ?S1 => eassert (RUN3a : msteps ASEGS S1 _) end.
{
zstep (ltac:(oF' 0x853a4%Z)) (ltac:(oD' 0x853a4%Z)).
stepn (ltac:(oF' 0x853a8%Z)) (ltac:(oD' 0x853a8%Z)). rwH. zclosed 0x40dc0.
zstep (ltac:(oF' 0x853ac%Z)) (ltac:(oD' 0x853ac%Z)).
stepn (ltac:(oF' 0x853b0%Z)) (ltac:(oD' 0x853b0%Z)). rwH. zclosed 0x40248.
zstep (ltac:(oF' 0x853b4%Z)) (ltac:(oD' 0x853b4%Z)).
stepn (ltac:(oF' 0x853b8%Z)) (ltac:(oD' 0x853b8%Z)).
apply mst_refl. }
match type of RUN3a with msteps _ _ (mkst ?R _ ?X _) => assert (Wb3 : wrA X 0x13dc40 0x81030) by zwr;
destruct (art_int_memset0 X rom 0x17ea00 art_ia_k4 R (0x853bc : bv 64)%bv ltac:(apply (wr_wok _ _ _ _ Wb3); rewrite ?art_ia_k4_Z; lia) ltac:(lia) ltac:(rewrite art_ia_k4_Z; lia) ltac:(unfold ret_ok; bveq)
ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; rewrite art_ia_k4_Z; reflexivity) ltac:(gres; bveq)) as (r4 & RUN3b & _ & HK4) end.
zkeep HK4 r4 (2%bv : reg) (Z_to_bv 64 (sp + -48)). zkeep HK4 r4 (8%bv : reg) (Z_to_bv 64 0x1cc4c8). zkeep HK4 r4 (9%bv : reg) (Z_to_bv 64 0x13dc40).
zkeep HK4 r4 (18%bv : reg) (Z_to_bv 64 266240).
eexists. split.
{ eapply msteps_trans; [exact RUN0a|]. eapply msteps_trans; [exact RUN0b|]. eapply msteps_trans; [exact RUN1a|]. eapply msteps_trans; [exact RUN1b|]. eapply msteps_trans; [exact RUN2a|]. eapply msteps_trans; [exact RUN2b|]. eapply msteps_trans; [exact RUN3a|]. eapply msteps_trans; [exact RUN3b|].
zstep (ltac:(oF' 0x853bc%Z)) (ltac:(oD' 0x853bc%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cps1' : cellA X 0x134380 8 0x1cc4e0) by zcell; assert (Cps2' : cellA X 0x1cc4e0 8 4096) by zcell end.
zld (ltac:(oF' 0x853c0%Z)) (ltac:(oD' 0x853c0%Z)) 0x134380 Cps1'.
zld (ltac:(oF' 0x853c4%Z)) (ltac:(oD' 0x853c4%Z)) 0x1cc4e0 Cps2'.
zbtk (ltac:(oF' 0x853c8%Z)) (ltac:(oD' 0x853c8%Z)).
zstep (ltac:(oF' 0x853d4%Z)) (ltac:(oD' 0x853d4%Z)).
stepn (ltac:(oF' 0x853d8%Z)) (ltac:(oD' 0x853d8%Z)). rwH. zclosed 0x40dd0.
zstep (ltac:(oF' 0x853dc%Z)) (ltac:(oD' 0x853dc%Z)). zstep (ltac:(oF' 0x853e0%Z)) (ltac:(oD' 0x853e0%Z)).
zsd (ltac:(oF' 0x853e4%Z)) (ltac:(oD' 0x853e4%Z)) 0x17ea00 4096 ltac:(zwok').
zsd (ltac:(oF' 0x853e8%Z)) (ltac:(oD' 0x853e8%Z)) 0x17ea08 0x17ea10 ltac:(zwok').
stepfence (ltac:(oF' 0x853ec%Z)) (ltac:(oD' 0x853ec%Z)).
zsb (ltac:(oF' 0x853f0%Z)) (ltac:(oD' 0x853f0%Z)) 0x1cc4c8 1 ltac:(zwok').
stepfence (ltac:(oF' 0x853f4%Z)) (ltac:(oD' 0x853f4%Z)).
zsb (ltac:(oF' 0x853f8%Z)) (ltac:(oD' 0x853f8%Z)) 0x1cc4c9 0 ltac:(zwok').
zstep (ltac:(oF' 0x853fc%Z)) (ltac:(oD' 0x853fc%Z)). zstep (ltac:(oF' 0x85400%Z)) (ltac:(oD' 0x85400%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (Cra : cellA X (sp - 8) 8 (U raw)) by zcell; assert (Cs0 : cellA X (sp - 16) 8 (U (getr regs 8))) by zcell;
assert (Cs1 : cellA X (sp - 24) 8 (U (getr regs 9))) by zcell; assert (Cs2 : cellA X (sp - 32) 8 (U (getr regs 18))) by zcell;
assert (Cs3 : cellA X (sp - 40) 8 (U (getr regs 19))) by zcell end.
zld (ltac:(oF' 0x85404%Z)) (ltac:(oD' 0x85404%Z)) (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x85408%Z)) (ltac:(oD' 0x85408%Z)) (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x8540c%Z)) (ltac:(oD' 0x8540c%Z)) (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x85410%Z)) (ltac:(oD' 0x85410%Z)) (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x85414%Z)) (ltac:(oD' 0x85414%Z)) (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
zstep (ltac:(oF' 0x85418%Z)) (ltac:(oD' 0x85418%Z)).
stepret (ltac:(oF' 0x8541c%Z)) (ltac:(oD' 0x8541c%Z)) raw ltac:(gres; reflexivity).
apply art_msteps_of_eq. apply art_mkst_eq; [reflexivity | reflexivity | unfold art_ia_mem; zmem_eq]. }
split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|].
intros r Hr. cbn [In] in Hr.
repeat (destruct Hr as [<-|Hr]; [repeat first [ progress gres | match goal with HK : ms_agree _ ?ri |- context [getr ?ri ?q] => rewrite (ms_agree_getr _ _ q HK) by (cbv; intuition discriminate) end ]; reflexivity|]).
destruct Hr.
Qed.
End SE.
#[using="Type"] Lemma art_cell8_zero : ltac2:(TCodec.tc2 tcn__JbtFxInit "QA'QAyR0%211'4y8%511%311p051'9&Nzr1%3221&O&Mr2+8%3221&Q1+2+R0%3221%9251'6%;2=8%22=1'7r6&Q@r5%@21?%32N1%511(0%62NH%22N1%:3N41p0<1pR>N1&=&Kr4u8%453>21Q1p061p0G1p0Q21pR:Q71pHQ91").
Proof.
intros M a Ha Ha' B. unfold cell.
assert (E : forall (n : nat) j, 0 <= j -> j + Z.of_nat n <= 8 -> rdn ASEGS M (Z_to_bv 64 (a + j)) n = Some (repeat (Z_to_bv 8 0) n)).
{ induction n as [|n IH]; intros j Hj Hn; [reflexivity|]. cbn [rdn repeat]. rewrite (B j) by lia.
replace ((Z_to_bv 64 (a + j) + 1)%bv : word) with (Z_to_bv 64 (a + (j + 1)) : word).
2:{ apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (bv_unsigned (1 : bv 64)%bv) with 1.
rewrite (Z.mod_small (a + j)) by lia. rewrite !Z.mod_small by lia. lia. }
rewrite IH by lia. reflexivity. }
specialize (E 8%nat 0 ltac:(lia) ltac:(cbn; lia)). rewrite Z.add_0_r in E. rewrite E. reflexivity.
Qed.
Section SE.
Local Abbreviation SEC_T_art_ia_run := (forall regs (M rom : word -> option byte) (raw : word) (sp : Z) (ia : bool), getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> 48 <= sp -> sp < 2 ^ 64 -> 0x693000 + 48 <= sp ->
wrA M (sp - 48) 48 -> cellA M 0x1cc4c8 4 (if ia then 1 else 0) -> wrA M 0x1cc4c8 4 -> wrA M 0x13dc40 0x81030 ->
cellA M 0x134380 8 0x1cc4e0 -> cellA M 0x1cc4e0 8 4096 ->
(ia = true -> forall k, 0 <= k < 2 ^ 15 -> cellA M (0x13dc48 + 8 * k) 8 0) ->
exists regs' (M' : word -> option byte),
msteps ASEGS (mkst regs (0x852d8 : word) M rom) (mkst regs' raw M' rom)
/\ getr regs' 10 = Z_to_bv 64 0x13dc40 /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp
/\ (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r)
/\ mem_grows M M' /\ art_agree [(sp - 48, 48); (0x13dc40, 0x81030); (0x1cc4c8, 4)] M M'
/\ cellA M' 0x1cc4c8 4 1 /\ (forall k, 0 <= k < 2 ^ 15 -> cellA M' (0x13dc48 + 8 * k) 8 0)) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ia_run) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ia_run) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ia_run) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_ia_run) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_ia_run) 4%nat 0%nat).
Variable ia : ltac:(sec_ty2 constr:(SEC_T_art_ia_run) 5%nat 0%nat).
Lemma art_ia_run : ltac:(sec_stmt2 constr:(SEC_T_art_ia_run) 6%nat 0%nat).
Proof using Type regs M rom raw sp ia.
intros H1 Hret H2 Hsp Hsp' IMG W Cw Ww Wbss Cps1 Cps2 L1.
destruct ia.
-
destruct (cell4_split M 0x1cc4c8 1 ltac:(lia) ltac:(lia) ltac:(lia) Cw) as (Cb0 & _ & _). change (1 mod 256) with 1 in Cb0.
pose proof (art_int_alloc_fn regs M rom raw sp H1 Hret H2 Hsp Hsp' IMG W Cb0) as RUN.
eexists. eexists. split; [exact RUN|].
split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
split. { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
split; [zgrows|].
split. { eapply art_agree_sub; [zagree|]. intros z Hz Hout. cbn [art_out app fst snd] in Hout |- *. repeat split; lia. }
split; [recell Cw|].
intros k Hk. specialize (L1 eq_refl k Hk). recell L1.
-
destruct (art_ia_init_run regs M rom raw sp H1 Hret H2 Hsp Hsp' IMG W Cw Ww Wbss Cps1 Cps2) as (regs' & RUN & P10 & P1 & P2 & PK).
pose proof art_ia_k1_Z as K1. pose proof art_ia_k2_Z as K2. pose proof art_ia_k3_Z as K3. pose proof art_ia_k4_Z as K4.
exists regs', (art_ia_mem M sp raw regs). split; [exact RUN|]. split; [exact P10|]. split; [exact P1|]. split; [exact P2|]. split; [exact PK|].
split; [unfold art_ia_mem; zgrows|].
split. { eapply art_agree_sub; [unfold art_ia_mem; zagree|]. intros z Hz Hout. cbn [art_out app fst snd] in Hout |- *. rewrite ?K1, ?K2, ?K3, ?K4. repeat split; lia. }
split.
+
change (cellA (art_ia_mem M sp raw regs) 0x1cc4c8 4 (1 + 256 * 0 + 65536 * 0)).
apply cell4_join; [lia|lia|lia|lia|lia| | | ].
* unfold art_ia_mem. zcell.
* unfold art_ia_mem. zcell.
* unfold art_ia_mem. do 2 (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]).
do 2 (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]).
do 3 (apply cell_Wf_other; [lia|lia|lia|cbn; lia|unfold apart; cbn; lia|]).
apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|].
apply cell_Wf_other; [lia|lia|lia|cbn; lia|unfold apart; cbn; lia|].
match goal with |- cellA ?X _ _ _ => assert (Cw1 : cellA X 0x1cc4c8 4 256) by (apply cell_Wn_hit; lia);
destruct (cell4_split X 0x1cc4c8 256 ltac:(lia) ltac:(lia) ltac:(lia) Cw1) as (_ & _ & Cl2) end.
change (256 / 65536) with 0 in Cl2. exact Cl2.
+ intros k Hk. unfold art_ia_mem.
do 4 (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]).
do 2 (apply cell_Wf_other; [lia|lia|lia|cbn; lia|unfold apart; cbn; lia|]).
apply art_cell8_zero; [lia|lia|]. intros i Hi. replace (0x13dc48 + 8 * k + i) with (0x13dc48 + (8 * k + i)) by lia. apply Wf_inside; lia.
Qed.
End SE.
End FPX.
