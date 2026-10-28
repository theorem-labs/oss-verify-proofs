(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import Utf8.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 YI06 UI5b YI09 YI08 YI0r UI1w UN3b UN3c UI55.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 YI00 UI5c YI0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI01 YI6c YI67 UN0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI02 YI03 YI0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0e YO03
YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI4l YI5a UI2v UI5d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UIZc UIZd UI4n UI4o UI4p UI4q UI4r UI4s UI4t UI4u UI4v.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Hypothesis FWRITE : fwrite_spec ubs0_msyms MR ubs0_A_fwrite.
Lemma rn_case_split : forall lo m hi, rn_case API lo m -> rn_case API (m + 1) hi -> rn_case API lo hi.
Proof using.
intros lo m hi H1 H2 L A regs mem md cfgp g pgct rattr W H sgct loops gvals f pga Npg S GCT bq HPRE Hid Ha0 Hcal Hclo Hchi cvals Hcfg Hcrd Hobj Hwfn Hfile Hgin Hfin HSK Hroom Hsp47 Hpal HRq HRM HH Hra Hal16 Hstk0 Hceil H63 Hstw Htp Herr Hac HSTKv HASv HGSv HRSv HDv HFv Hg0 Hg1 Hg16 HFBv HWSv Hf0 Hf1 Hf16 Hsg_r Hat_r Hlp_r E HE HX HY HE2 HE10 HE33 HE38 HE35 HE39 Hspw Hsg L2 A2 regs2 md2 res Hid2 Hres10 Hnz Hres16 b1 b2 Hbl2 Hblc Hwr HRq2 Hfin2 Hq10 HE2' Hbin2 Hb0 Hb1 Hwr' Hgc regs3 Hd10 Hrf Henvblk WR Hranges Hoff Hgf Hgin2 Hgranges Hglen HE36 HE37 HWr HHr HLr HAr regs4 ms2 HJ3 HSKc HS Hk.
destruct (Z_le_gt_dec sgct m) as [Hle | Hgt].
- exact (H1 L A regs mem md cfgp g pgct rattr W H sgct loops gvals f pga Npg S GCT bq HPRE Hid Ha0 Hcal Hclo Hchi Hcfg Hcrd Hobj Hwfn Hfile Hgin Hfin HSK Hroom Hsp47 Hpal HRq HRM HH Hra Hal16 Hstk0 Hceil H63 Hstw Htp Herr Hac HSTKv HASv HGSv HRSv HDv HFv Hg0 Hg1 Hg16 HFBv HWSv Hf0 Hf1 Hf16 Hsg_r Hat_r Hlp_r HE HX HY HE2 HE10 HE33 HE38 HE35 HE39 Hspw Hsg L2 A2 regs2 md2 res Hid2 Hres10 Hnz Hres16 b1 b2 Hbl2 Hblc Hwr HRq2 Hfin2 Hq10 HE2' Hbin2 Hb0 Hb1 Hwr' Hgc regs3 Hd10 Hrf Henvblk WR Hranges Hoff Hgf Hgin2 Hgranges Hglen HE36 HE37 HWr HHr HLr HAr regs4 ms2 HJ3 HSKc HS ltac:(lia)).
- exact (H2 L A regs mem md cfgp g pgct rattr W H sgct loops gvals f pga Npg S GCT bq HPRE Hid Ha0 Hcal Hclo Hchi Hcfg Hcrd Hobj Hwfn Hfile Hgin Hfin HSK Hroom Hsp47 Hpal HRq HRM HH Hra Hal16 Hstk0 Hceil H63 Hstw Htp Herr Hac HSTKv HASv HGSv HRSv HDv HFv Hg0 Hg1 Hg16 HFBv HWSv Hf0 Hf1 Hf16 Hsg_r Hat_r Hlp_r HE HX HY HE2 HE10 HE33 HE38 HE35 HE39 Hspw Hsg L2 A2 regs2 md2 res Hid2 Hres10 Hnz Hres16 b1 b2 Hbl2 Hblc Hwr HRq2 Hfin2 Hq10 HE2' Hbin2 Hb0 Hb1 Hwr' Hgc regs3 Hd10 Hrf Henvblk WR Hranges Hoff Hgf Hgin2 Hgranges Hglen HE36 HE37 HWr HHr HLr HAr regs4 ms2 HJ3 HSKc HS ltac:(lia)).
Qed.
Ltac case_of c := first [exact (c API IMG FWRITE) | exact (c API IMG) | exact (c API)].
Lemma rawnew_x_all : rn_case API 0 256.
Proof using FWRITE IMG.
apply (rn_case_split 0 0 256); [case_of rawnew_x_c0|].
apply (rn_case_split 1 1 256); [case_of rawnew_x_c1|].
apply (rn_case_split 2 2 256); [case_of rawnew_x_c2|].
apply (rn_case_split 3 4 256); [case_of rawnew_x_c3|].
apply (rn_case_split 5 8 256); [case_of rawnew_x_c4|].
apply (rn_case_split 9 16 256); [case_of rawnew_x_c5|].
apply (rn_case_split 17 32 256); [case_of rawnew_x_c6|].
apply (rn_case_split 33 64 256); [case_of rawnew_x_c7|].
apply (rn_case_split 65 128 256); [case_of rawnew_x_c8|].
case_of rawnew_x_c9.
Qed.
End S.
End t.
