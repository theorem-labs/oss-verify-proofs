(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk AsanPopFree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__AsanPopFreeAsanKB0 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPopFree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPopFreeAsanKB0."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1nat"; "1option"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "3Z"; "4fetch_word"; "4store_ok"; "5bvmap"; "6PW0"; "6PW1"]; ["6PW2"; "6PW3"; "6PW4"; "6PW5"; "6PW6"; "6PW7"; "6pf_mem"; "6popfree_spec"; "7asan_popfree_head"; "7asanreflect_fx"; "8msteps"; "9getr"; "9mkst"; ":loaded_segments"; ";add"; ";div"]; [";le"; ";lt"; ";mul"; ";of_nat"; ";pow"; ";sub"; ";to_nat"; "0c"; "0d"; "0e"; "0i"; "0m"; "0mem"; "0n"; "0r"; "0regs"]; ["0regs'"; "0rom"; "0s"; "<BV"; "<Z_to_bv"; "<bv"]]).
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
#[local] Notation ASEGS0 := AsanUbsan.M.loaded_segments (only parsing).
Definition asan_popfree_head : Z := 0x57320.
Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Lemma PF0 : ltac2:(TCodec.tc2 tcn__AsanPopFreeAsanKB0 "A'7'3'QEyQ0%211%411&;&M&QDyR0&H%3221%6251(0&>%22;1%@3;41"). Proof. vm_refl. Qed.
Lemma PF1 : ltac2:(TCodec.tc2 tcn__AsanPopFreeAsanKB0 "D'7'3'QEyQ0%211%411&;&M&QDyR0&N&H+4%3221%6251%9281(0&?%22>1%C3>41"). Proof. vm_refl. Qed.
Lemma PF2 : ltac2:(TCodec.tc2 tcn__AsanPopFreeAsanKB0 "D'7'3'QEyQ0%211%411&;&M&QDyR0&N&H+8%3221%6251%9281(0&@%22>1%C3>41"). Proof. vm_refl. Qed.
Lemma PF3 : ltac2:(TCodec.tc2 tcn__AsanPopFreeAsanKB0 "D'7'3'QEyQ0%211%411&;&M&QDyR0&N&H+<%3221%6251%9281(0&A%22>1%C3>41"). Proof. vm_refl. Qed.
Lemma PF4 : ltac2:(TCodec.tc2 tcn__AsanPopFreeAsanKB0 "D'7'3'QEyQ0%211%411&;&M&QDyR0&N&H+@%3221%6251%9281(0&B%22>1%C3>41"). Proof. vm_refl. Qed.
Lemma PF5 : ltac2:(TCodec.tc2 tcn__AsanPopFreeAsanKB0 "D'7'3'QEyQ0%211%411&;&M&QDyR0&N&H+D%3221%6251%9281(0&C%22>1%C3>41"). Proof. vm_refl. Qed.
Lemma PF6 : ltac2:(TCodec.tc2 tcn__AsanPopFreeAsanKB0 "D'7'3'QEyQ0%211%411&;&M&QDyR0&N&H+H%3221%6251%9281(0&D%22>1%C3>41"). Proof. vm_refl. Qed.
Lemma PF7 : ltac2:(TCodec.tc2 tcn__AsanPopFreeAsanKB0 "D'7'3'QEyQ0%211%411&;&M&QDyR0&N&H+L%3221%6251%9281(0&E%22>1%C3>41"). Proof. vm_refl. Qed.
Theorem asan_popfree_spec : ltac2:(TCodec.tc2 tcn__AsanPopFreeAsanKB0 "5&G&I&M&H%43321").
Proof.
apply popfree_spec_of_code; [unfold asan_popfree_head; lia | exact PF0 | exact PF1 | exact PF2 | exact PF3 | exact PF4 | exact PF5 | exact PF6 | exact PF7].
Qed.
Theorem asan_popfree_loop_run : ltac2:(TCodec.tc2 tcn__AsanPopFreeAsanKB0 "V?&=y5'QEyR0%211%5241'3y8%611%311p061':'7&Kr8(QC+:(5%33A21%6251&QDr5%22C1%;3C41r9+;%;3I19%>231%@3H16r:+<%@3N1>%C231%E3M1;r;+E%E3Q31C%H231%J3Q21@r<+C%J3Q81H%M231%O3Q71E&Q0z%221A&Q1r7%22?1&Q2+4%221Q6%921C&Q4+2+R0%3221%;2C1%?2>D&Nr>&Q5r@%22I1r=%@221%7261%E21;'2r2%K2J1r3&Q3%114%?231rD%?2>1%L2K1%Q3241'1&<&MrGrA%Q32Q21%H2:1r4%L221%R52RF1%94871B(4%R@3<21p0>1p0G1pRHJ1pRBRE1'8'6'J&L&IrF&H%RD2S51rE%655421Nr1+Q0%QA261%RJ2S;1&FrBrC&Q6r?%QF213%311%76=6Q2QG51%C5B<91Q;%E3Q6>1%S<2>S7%S62SG7%S?3SG21%S?2AS2%S92SJ=%SB3SJ21%SB2DS0%R>2<R1%R52Q=1%S>2SO1%SG3SO41%SG2IS0%SA2T2R6%SJ3T221%SJ2LRN%SL3T41>+>%SK3T91SI%SN2Q01&O+1%R@2J1%RM21R@%RD2QL1+@%6221%SO2T@1%T83T@91+?%T73TE1T5%T:2Q<1%S62S5Q5%RK2Q91%T62TG1%T?3TG41%TJ1TK&9%TB32QCT<%211%TD34RJT1%411%TF36RJH%611%TH38R=>%811r6%TJ21TBrK%TL21TD%TN3U631p061p091p0<1p0?1pRNC1%R>2E1%R?2M1%R@2Q:1%RA2Q=1%RB2QA1%RC2QG1%RD2QK1%RE2QO1qS2UC1%RH2UD1p0RJ1p0SG1p0T11p0T21p0T41p0T:1p0T?1p0TC1p0TG1p0TM1p0U31p0U91p0U?1pRLUL1pS6UM1pR@UN1pRDUO1pRFV01pS4V21pRJV31pS0V91").
Proof.
apply (popfree_loop_run ASEGS0 asan_popfree_head); [unfold asan_popfree_head; lia | exact PF0 | exact PF1 | exact PF2 | exact PF3 | exact PF4 | exact PF5 | exact PF6 | exact PF7].
Qed.
