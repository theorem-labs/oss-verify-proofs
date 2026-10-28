(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac ITree Nodes Decode SysStep Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel F_fmt_fp_lib.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Stdio_kit2 () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_atC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC56Stdlib6ZArith6BinInt1Z6of_natC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_wfC5ARocqVerifyHarness?AgentSubmission3Lib5Cells;cells_bytesI47Corelib4Init5Logic2eq00C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC47Corelib4Init5Logic8eq_ind_rK47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes6lengthC5ARocqVerifyHarness?AgentSubmission3Lib5CellsBcells_bytes_lengthC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsK47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes3nat00C46Stdlib5Lists4List9app_nil_rC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission6Common<F_fmt_fp_lib2zbC5ARocqVerifyHarness?AgentSubmission3Lib5Image:ro_bytes_bC56Stdlib6ZArith6BinInt1Z2leC5ARocqVerifyHarness?AgentSubmission4Spec6Prelim7zlengthC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission6Common<F_fmt_fp_lib9zb_lengthC5ARocqVerifyHarness?AgentSubmission3Lib5Image>ro_cells_imageC5ARocqVerifyHarness?AgentSubmission3Lib7SysStepAro_cells_bytes_atC47Corelib4Init9Datatypes3appI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma rw_cells_recast3 : forall m A cs cs', rw_cells bsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells bsegs m A cs'.
Proof.
ltac2:(KReplay.run1 (kr_t_Stdio_kit2 ()) ["CANSEC1"] "h01Hh11lh21Ah31Bh41Eh51Rh61Wh72W'h82csh93cs'h:1mh;1np;1p;4p;3p;6p;2p10000p4p710g000MR0p4p710p8g000ij14Tg001Nj1=Tg001lj1<Tg002Oj1ATg0031j1@Tg003Qj49Tg004Gj48Tg005>j15Tg0067j11Tg006Wj12Tg007Nj10Tg008Hj37Tg008bj46Tg009Wj6;Tg00:5j4?Tg00:Pj2:Tg00;0j2>TP0j6CTg00<1j4BTg00<cR0f2R1f1R2f0R3CBp=3g00=X#4#4#4R4#4#4#4#=#<%=4#<R4#A[g00>=g00>[#@R5P0f3R6P1P2C9g00?PR7P0f4R8P6P1C8%51#19386%21%@4R9%06%0837P0f7R:f6R;P8C9[[P3P0P;f5R<P8C8P7%2<P0P:P;%0<C6f8R<%5;#173:%2;%0:%0<R;579P0f;R7f:R=P<C9[[[P3%2:P0P=f9R:P;C6%5:#1937=%2:%0=%07R=579P0f>R:f=R;P7C8%57R<#193:;%27P0P:P;P=C6P2P9f<R;#0R>P0f?R0P:P3C6X19P6P=P3E;C?g00?kR61:4=%13930:X;6R?P9P>1:43#1930:X19P6%5;P?P11:4>1>;8E;P=P3E;P<1>72ECC?W4W7W5W3W6P2P3O2n2001000000120000000W0P2P3O2n2001000000121000000W0X95W8W2W:o"). Qed.

(* [comment removed for export] *)
Lemma fmt_bytes_at : forall m A f, mem_inv bsegs m -> ro_bytes_b bsegs A (zb f) = true -> 0 <= A -> A + zlength f <= 2^64 ->
  bytes_at bsegs m A (zb f).
Proof.
ltac2:(KReplay.run1 (kr_t_Stdio_kit2 ()) ["CANSEC1"] "h01Bh14__x1h24__x2h31Ah42H0h52H1h62MIh72RBh87__arithh94__ffh:8__varmaph;5__with<4cstrh=1fh>1lh?1mh@1np;1p;2p;3p;4p;7p;8p;6p;5g00@JR0p4p710g000MR1p4p710p8g000ij11Tg001Nj1=Tg001lj19Tg002Oj1ATg0031j18Tg00@hj2VTg00A\j14Tg00BWj3GTg008Hj3:Tg00CPj20Tg00Clj2@Tg00Ddj22Tg00EAj1;Tg00E_j2^Tg00:Pj27Tg00F<j2WTg00G1j15Tg00GQj3UTg0067j13Tg00H1j1RTg00HVj2QTg00I4j1NTg00IRj4FTg00J0j1ETg00JNj1DTg00K9j2<Tg00K\j3CTg00L?j2HTg00Lbj3BTg00MEj4ITg00N0j7JTg00NTj1KTg00O6j8LTg00OZj2MTg00P<j2?Tg00PVj2OTg00QBj3PTg00Qaj4>Tg00RSj1STg009Wj6TTg00SUj8]Tg00TRj5\Tg007Nj1[Tg008bj46Tg00UTj3XTP0j2YTP1j6ZTg00=XR1#1R0#1#1R2#1#1#1R3#=R4#9%=2#9R2#A[g00>=R5%85g00<cR6f2R7'Vg00V1R8f1R9#49G67g00VQR:3:g00W1R;f3R<'0f4R=1@5<'2%;0R>%;3'^R3'0P6f6R?f5R@g00>[RA%4=RB,72RC/WB%5A3URAP6P?P@PBP<P7P9g00?kR<175=RBf0RD#3,2?/03X@<%RB%3B,0;g00WORB#5%8BP51Q57P9%N5CF%E5%D5RBg00X;R<g00XZREPEg00Y:RFPBP<PEPEPFP51<511<505C5g00YZ1H5>=B54CIg00ZAFJR4%KEP4GL1MBFPDP71?8:1OD7=:8:dAP5;9C>b9b:b;X15X2512D9/031297/03[^15^25PD175?#3f7R5P7O3b8b<PC%S=ETG]D\P6P?P@%[AC6%82RA%4@R@%525X2P6f8P5PDC6X>APDP@1Y2@EZP6P5P?P@C6PDb0b0W5W4W7W6W=W3W?o"). Qed.

End CANSEC1.
Ltac forall_range := repeat (apply Forall_cons; [lia|]); apply Forall_nil.
