(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare L5Defs L5Core FPSteps.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmParStep () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.DecodeC."; "LinuxProcessSemantics.Riscv.Fpu."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1O"; "1Some"; "1bool"; "1cons"; "1false"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "2I"; "2and"; "2eq"; "2ex"; "2not"]; ["2or"; "3lt"; "4Z"; "5MachineOk"; "5fetch_word"; "5is_ecall"; "5machine_result"; "5machine_state"; "5step"; "6decode_any"; "7rmode"; "7rmode_of_field"; "8FC_D"; "8FC_S"; "8FMT_D"; "8FMT_S"]; ["8FMV_F_X"; "8Fcvt"; "8Fmv"; "8Load"; "8SZ1"; "8fcvt_ty"; "8ffmt"; "8instr"; "9bvmap"; "0M"; "0R"; ":msteps"; ";defined"; ";u8_at"; "<FPState"; "<getr"]; ["<mkFP"; "<mkst"; "<rdn"; "<regupd"; "<seg_rom"; "<v_addi"; "=add"; "=le"; "=lt"; "=of_nat"; "=pow"; "0W"; "0a"; "0a0"; "0b"; "0cs'"]; ["0dst"; "0fmt"; "0fr'"; "0fx"; "0fx'"; "0imm"; "0k"; "0md"; "0mem"; "0pc"; "0rd"; "0regs"; "0rm"; "0rom"; "0rs"; "0rs1"]; ["0segs"; "0src"; ">BV"; ">Z_to_bv"; ">bv"; ">bv_signed"; ">bv_unsigned"; "0v"; "0w"; "0x"]]).
Module PMPX.
Section Steps.
Variable segs : list Segment.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom segs)).
Lemma rdn1_of_defined : ltac2:(TCodec.tc2 tcn__PmParStep "Q7'RDyR0%211'8y8%511%311p051'B&Q<r2r1+1%43321'>'='5%11<%?11&QBvR@r4&RCr3%22G1u1%746521(1(3(7%11I%33JD1%52?1%B3?71qSNM1%E2N1p0G1pSJM1pRDO1").
Proof. intros M a.
intros D. pose proof (D 0 ltac:(lia)) as D0. rewrite Z.add_0_r in D0. cbn [rdn].
destruct (M (Z_to_bv 64 a)) as [b|] eqn:E; [|congruence]. exists b. reflexivity.
Qed.
Lemma lbu_run : ltac2:(TCodec.tc2 tcn__PmParStep "TB'Q>&Q8y5'RDyR0%211%5241'8y8%611%311p061'ByQ0%;11%<1=y<%>11'=%<15&DvR@&RCr6%22D1%5241(1r5%22>1%;3:41'2&E%119(4%@3421':'Q7%221I%O11&Ir7%211(9(Q3(Q4r4%352=GC1+4%64<Q421%G2<1%Q03<91&?(RBz(;%33QE21%Q63Q9@1%611&QGr:%2271&QH&QFr;%221A&QJ+2+R0%3221%8251&Q?r>r9%3221%QD2R6Q2%QI3R621'<r8%D2I1%B22;%4221&RE%12R2G%E2;1%J2O1%H22A%:221&Q<r@%82R9J%L2O1+1%53421'>r1%Q52Q:1+X0%Q4231%F231&Q=rBr<r=%F2RG1%Q:231%64RD51;'Q;&QArDrCrA%RI2S;1&QD%11RL%75653>1&QCr?%RO2SAG%33921%QI29R8%S22SD1%>5=31E8%@3S581%Q?2B1%Q@2J1qSNSA1%Q12SB1p0Q31p0Q:1p0QA1p0QG1p0QN1p0R81p0R<1p0RD1p0S51p0S;1pSLSM1pT<SI1pTNSL1pTFSM1pSHSO1pTDT21pRDT41pRFT:1pT8TA1").
Proof. intros fx R M pc W rd rs imm a0.
intros HF HE HD Hrd Hpc Hpc4 Hrs Ha0 Ha D.
destruct (rdn1_of_defined M _ D) as (b & RB).
exists (bv_unsigned b). pose proof (bv_unsigned_in_range 8 b) as Bb. change (bv_modulus 8) with 256 in Bb.
split; [exact Bb|]. split. { unfold L5.u8_at. rewrite RB. rewrite Z_to_bv_bv_unsigned. reflexivity. }
eapply mst_step; [reflexivity| | apply mst_refl].
rewrite (step_lbu segs R (Z_to_bv 64 pc) M (seg_rom segs) W rd rs imm b HF HE HD).
- rewrite (bv_eqb_neq rd 0%bv Hrd). f_equal. f_equal. unfold v_addi. rewrite L5.unsigned_lit by lia. reflexivity.
- unfold v_addi. rewrite Hrs, L5.unsigned_lit by lia. exact RB.
Qed.
Lemma fmv_fx_run : ltac2:(TCodec.tc2 tcn__PmParStep "S5'Q>&Q8y5'RDyR0%211%5241'8y8%611%311p061'ByQ0%;11'Q6%=1>'=%;14&DvR@&RCr5%22C1%5241(1r4%22=1%;3:41'2&E%119(4%@3421':'Q7%221H%N11&Ir6%211(9(Q2(Q0r3%342GC1+4%64<Q321%G2<1%Q03<91'@(O%Q33Q5=1(N%Q53Q7?1%5231&QGzr9%3221&QH&QFr:%221A&QJ+2+R0%3221%8251'>'Q;&QAr?r>r<%QF2R71r=&QD%11QJ%8576431r1%D27Q3%QM2R>1%<53:175%>3R051qT:RE1%A2RF1p0C1p0M1p0Q21p0Q91p0QJ1p0R01pTNR=1pTFR>1pT4R@1pSHRB1pTDRE1pRDRG1pRFRM1pT8S41").
Proof. intros fx R M pc W fmt rd rs.
intros HF HE HD Hfmt Hpc Hpc4.
assert (NPC : v_addi (Z_to_bv 64 pc) 4 = Z_to_bv 64 (pc + 4)).
{ unfold v_addi. rewrite L5.unsigned_lit by lia. reflexivity. }
destruct Hfmt as [->| ->].
- pose proof (fp_step_fmv_w_x fx segs R (Z_to_bv 64 pc) M (seg_rom segs) W rd rs HF HE HD) as ST. rewrite NPC in ST.
exists (mkFP (bvmap_set rd (nan_box (low32 (getr R rs))) (@fp_regs fx)) (@fp_csr fx)). eapply mst_step; [reflexivity| exact ST| apply mst_refl].
- pose proof (fp_step_fmv_d_x fx segs R (Z_to_bv 64 pc) M (seg_rom segs) W rd rs HF HE HD) as ST. rewrite NPC in ST.
exists (mkFP (bvmap_set rd (getr R rs) (@fp_regs fx)) (@fp_csr fx)). eapply mst_step; [reflexivity| exact ST| apply mst_refl].
Qed.
Lemma fp_resolve_static : ltac2:(TCodec.tc2 tcn__PmParStep "M'RDy3%211'B&QG&RFr2%2261+4%5221'>'J'='8%113&Kr4%<2@1r3%4221(1r1%22;1%;3941qT@=1%?2>1p0A1pUDH1pTJJ1").
Proof. intros rm x.
intros Hrm. unfold rmode_of_field. pose proof (bv_unsigned_in_range _ rm) as Hr.
destruct (Z.eqb_spec (bv_unsigned rm) 7) as [E|NE]; [lia|].
unfold rmode_of_Z.
destruct (Z.eqb_spec (bv_unsigned rm) 0); [eexists; reflexivity|].
destruct (Z.eqb_spec (bv_unsigned rm) 1); [eexists; reflexivity|].
destruct (Z.eqb_spec (bv_unsigned rm) 2); [eexists; reflexivity|].
destruct (Z.eqb_spec (bv_unsigned rm) 3); [eexists; reflexivity|].
destruct (Z.eqb_spec (bv_unsigned rm) 4); [eexists; reflexivity|].
exfalso. lia.
Qed.
Lemma fcvt_f_static_step : ltac2:(TCodec.tc2 tcn__PmParStep "S9'Q>&Q8y5'RDyR0%211%5241'8y8%611%311p061yQ0%:11'Q5%<1=y3%>11'=%<16&DvR@r9%3221(1r6%22=1%93841'2&Er7%211(4%?3521':'Q7'B%3221%O11&Ir8%211(9(Q1r5r4r3%45AF321+4%74>=21%J2=1%Q13=:1'@(M%Q43Q8>1(L%Q63Q:@1%5231&QG&RF%12Q<@%321='>'F'G%211&H&QArBrAr@r?r>%6554321%82QE1(C(Q@r2r1%3221&QE%12;Q1%?53=1;:%82C1%R23C:1qT0R81%H2R91qT6RA1%J2RB1p0L1p0Q11p0Q81p0QK1p0R21pTJR=1pU0R@1pTFRA1pU4RC1pT2RD1pUBRF1pTLRI1pTBRJ1pTDS11pTHS11pT8S81").
Proof.
intros fx regs pc mem rom w dst src rd rs1 rm Hf He Hd Hdst Hrm.
destruct fx as [fr cs]. cbn [fp_csr] in *.
destruct (fp_resolve_static rm (Z.land (Z.shiftr (bv_unsigned cs) 5) 7) Hrm) as [md Hmd].
fp_pipeline Hf He Hd. rewrite Hmd. cbv beta iota.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct Hdst as [-> | ->]; destruct src; cbv beta iota;
repeat match goal with
| |- context [let '(_, _) := ?p in _] => destruct p as [?v ?fl]; cbv beta iota
end;
try (destruct (is_x0 rs1); cbv beta iota);
repeat match goal with
| |- context [let '(_, _) := ?p in _] => destruct p as [?v ?fl]; cbv beta iota
end;
rewrite b_npc4;
(eexists _, _; reflexivity).
Qed.
Lemma fcvt_f_run : ltac2:(TCodec.tc2 tcn__PmParStep "S>'Q>&Q8y5'RDyR0%211%5241'8y8%611%311p061'ByQ0%;11'Q5%=1>y3%?11'=%=16&DvR@&RCr7%22E1%5241(1r6%22?1%;3:41'2&E%119(4%@3421':'Q7%221J%Q011&Ir8%211(9(Q1r5r4r3%45HD321+4%74=Q621%H2=1%Q13=:1'@(M%Q43Q8>1(L%Q63Q:@1%5231&QG&RF%12Q<@%321=zr<%6221&QH&QFr=%221D&QJ+2+R0%3221%8251'>'Q;&QArBrAr?%QJ2R=1r@&QD%11QN%8576431r1%D27Q6%R12RD1%<53:175%>3R451qT:RK1%A2RL1p0C1p0M1p0Q11p0Q61p0Q=1p0QO1p0R51pTJRB1pTNRE1pTFRF1pU4RH1pT2RI1pSHRK1pTDRN1pRDS01pRFS61pT8S=1").
Proof. intros fx R M pc W dst src rd rs rm.
intros HF HE HD Hdst Hrm Hpc Hpc4.
assert (NPC : v_addi (Z_to_bv 64 pc) 4 = Z_to_bv 64 (pc + 4)).
{ unfold v_addi. rewrite L5.unsigned_lit by lia. reflexivity. }
destruct (fcvt_f_static_step fx R (Z_to_bv 64 pc) M (seg_rom segs) W dst src rd rs rm HF HE HD Hdst Hrm) as (fr' & cs' & ST).
rewrite NPC in ST. exists (mkFP fr' cs'). eapply mst_step; [reflexivity| exact ST| apply mst_refl].
Qed.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Lemma regupd_other_idx : ltac2:(TCodec.tc2 tcn__PmParStep "Q8&Q8y5'RDyR0%211%5241'6&?'=r2r3%33521%511&AuQ0%2251r5%4213&Q?&QCr7&RC&QIr6%211%42H1r4%83721%61<%82L1%<231%=2;2%H3L21p0@1p0C1p0G1pU@Q01pT>O1pTFQ01pRFQ21").
Proof. intros R rd k v.
intros NE Hk Hr. apply getr_other. intros E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
change (bv_modulus 5) with 32 in E. rewrite !Z.mod_small in E by lia. lia.
Qed.
Lemma regupd_same_idx : ltac2:(TCodec.tc2 tcn__PmParStep "O&Q8y5'RDyR0%211%5241'6'<&A(0r2%3221uQ0%5231%7231'=&Q?&QCr4&RC&QIr3%211%42F1%7361>%9212%;3F1@p0=1pU@H1pTFG1pRFI1").
Proof. intros R rd v.
intros Hr. apply getr_same. intros E. apply (f_equal bv_unsigned) in E. rewrite Z_to_bv_unsigned in E. unfold bv_wrap in E.
change (bv_modulus 5) with 32 in E. rewrite Z.mod_small in E by lia. change (bv_unsigned (0%bv : bv 5)) with 0 in E. lia.
Qed.
End Steps.
End PMPX.
