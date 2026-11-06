(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MemsetLib As0StepLib
ArtMem ArtRegs ArtAtomics ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import muslA.Ja0SumsMemset_code muslA.Ja0SumsMemset.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import JatPoison.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatPoisonRun () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatPoison."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatPoisonRun.FPX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2I"; "2and"; "2eq"; "2ex"; "3Z"; "4bvmap"; "0M"; "5Wf"; "5apart"; "5wr"; "6msteps"; "7ret_ok"; "8SB"; "8art_layout"; "8art_poison_frame"]; ["8kHighMemBeg"; "8kHighMemEnd"; "9art_poison_kept"; ":getr"; ":mkst"; ";loaded_segments"; "<add"; "<div"; "<le"; "<lt"; "<modulo"; "<pow"; "<sub"; "<to_nat"; "0fx"; "0n"]; ["0p"; "0r"; "0raw"; "0regs"; "0regs'"; "0rom"; "0sp"; "=BV"; "=Z_to_bv"; "=bv"; "=bv_unsigned"; "0v"]]).
Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Section FPX. Context {fx : PropExec.FPState}.
Definition art_poison_kept (r : reg) : Prop :=
r <> 5%bv /\ r <> 6%bv /\ r <> 7%bv /\ r <> 10%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv /\ r <> 15%bv /\ r <> 16%bv
/\ r <> 17%bv /\ r <> 28%bv.
Section SE.
Local Abbreviation SEC_T_art_poison_hi_run := (ltac2:(TCodec.tc2 tcn__JatPoisonRun "W4&6y5'Q9yR0%211%5241'0y8%611%311p061'5'3&Cr8(Q7+1(1%33A21%6251r5%93A21&<r6%211r:+2%<3J1:%?231&Q8%12K7%C3K31r;+:%C3Q11A%F231%H3Q016r<+;%H3Q61F%K231%M3Q51;r=+<%M3Q;1K%Q0231%Q23Q:1@&H+R0%221H&I&K%12J4%32E1&:&Er?&L%12E:%54431;&9%42C=+QVXR0+Q`P0%443@21r>%921B+QibQ8+X0%943E21&>rB%211&@%K21B&Fr@%221E&A%421QO%Q1231&JrA+8%3221z%R:3R;21%Q824@'2%Q:24B%Q82CF%3221rC%RA3RB18&GrE%221=+RPP0%Q@221p061rJ&=rF%921D%M231%QC4QB519'4';&DvNrM+_X_0%S13S=1RO/01S=rLrK%8576321r1&8&?rI&Q:%12SGF%S<3SJQ8S:%S?2>1%42SJ1+9%S@3SN1S>%SC2B1%82SN1+B%SD3T21SB%SG2F1%<2T21+C%SH3T61SF%SK2J1%@2T61+D%SL3T:1SJ%SO2N1%D2T:1+E%T03T>1SN%T32Q21%H2T>1%K9Q0JHEA=951rH%QF21R1%R:2Q@1&MrG%QJ21R5%311%Q44851QD%Q?5Q>Q6QG1Q8%QA3S5Q81%T@2Q8SK%T12TK9%TC3TK21%TC2Q;T>%TE3TM1QM%TE2Q=T7%T62U0Q;%TH3U021%TH2Q@Q:%TJ3U21Q:%TJ2QBQ8%TL3U41Q8%TL2QDQ6%TN3U61Q6%TN2QFQ4%U03U81Q4%U02QHQ2%U23U:1Q2%U22QJQ0%U43U<1Q0%U?1U@&B%11QNr3r2%U9221rO%U;213%U=3UE31p071pR4:1%S42<1%S52?1%S62B1%S72E1%S82H1%S92K1%S:2N1%S;2Q21%S<2Q51%S=2Q91qR:V11%RM2V21p0RO1p0S61p0S?1p0SD1p0SF1p0SG1p0SN1p0T51p0T81p0T<1p0TB1p0TH1p0TO1p0U41p0U81p0U>1p0UD1p0UJ1p0V21p0V61pRHVA1pR0VB1pR2VC1pR>VD1pR6VL1pR<VG1p@VH1pR8VN1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_poison_hi_run) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_poison_hi_run) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_poison_hi_run) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_poison_hi_run) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_poison_hi_run) 4%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_art_poison_hi_run) 5%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_poison_hi_run) 6%nat 0%nat).
Variable v : ltac:(sec_ty2 constr:(SEC_T_art_poison_hi_run) 7%nat 0%nat).
Theorem art_poison_hi_run : ltac:(sec_stmt2 constr:(SEC_T_art_poison_hi_run) 8%nat 0%nat).
Proof using Type regs M rom raw sp p n v.
intros H1 Hret H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo Hhi Hp8 Hn8 Hn Hv Hthr Wsh.
pose proof (art_poison_hi_fn regs M rom raw sp p n v H1 H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo Hhi Hp8 Hn8 Hn Hv Hthr) as RUN1.
unfold kHighMemBeg, kHighMemEnd, SB in *.
match type of RUN1 with msteps _ _ (mkst ?R1 _ ?M1 _) =>
assert (OK : store_ok ASEGS M1 (Z_to_bv 64 (2147450880 + p / 8)) (Z.to_nat (n / 8)) = true)
by (unfold art_poison_frame; apply wr_wok with (a := 2147450880 + p / 8) (n := n / 8); [|lia|lia]; repeat apply wr_Wn; exact Wsh);
destruct (memset_summary M1 (Z_to_bv 64 (2147450880 + p / 8)) (Z_to_bv 64 v) raw (n / 8) rom
ltac:(lia) ltac:(rewrite art_u_lit by lia; lia) OK Hret R1
ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; reflexivity))
as (r2 & RUN2 & P10 & AG)
end.
exists r2. split.
{ eapply msteps_trans; [exact RUN1|]. unfold Wf. rewrite cbyte_cbz in RUN2. unfold cbz in RUN2. rewrite art_u_lit in RUN2 by lia.
replace (v mod 256) with v in RUN2 by (symmetry; apply Z.mod_small; lia).
replace (Z_to_bv 64 ms_base) with (0x124db0 : bv 64)%bv in RUN2 by (apply bv_eq; vm_compute; reflexivity). exact RUN2. }
assert (K : forall r : reg, ~ In r ms_clob -> getr r2 r = getr _ r) by exact AG.
cbn [ms_clob In] in K.
zsplit;
try (rewrite K by (intuition discriminate); gres; first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity | f_equal; lia]).
intros r Hr. unfold art_poison_kept in Hr. destruct Hr as (?&?&?&?&?&?&?&?&?&?&?&?).
rewrite K by (intuition congruence). kept_solve.
Qed.
End SE.
End FPX.
