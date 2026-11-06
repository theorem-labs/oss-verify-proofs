(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__FPSteps () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.DecodeC."; "LinuxProcessSemantics.Riscv.Fpu."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.FPSteps."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1false"; "1list"; "1option"; "1pair"; "1prod"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "2or"; "3Z"; "4Z_to_le_bytes"; "4le_bytes_to_word"]; ["5Segment"; "6MachineOk"; "6fetch_word"; "6is_ecall"; "6machine_result"; "6machine_state"; "6step"; "6store_ok"; "6word_to_le_bytes"; "7decode_any"; "8fflags"; "8fflags_bits"; "8rmode"; "8rmode_of_field"; "9CSR_RS"; "9CsrI"]; ["9FC_D"; "9FC_S"; "9FLoad"; "9FMT_D"; "9FMT_S"; "9FMV_F_X"; "9FStore"; "9Fari"; "9Fcvt"; "9Fmv"; "9Fsgnj"; "9fariop"; "9fcvt_ty"; "9ffmt"; "9fsgnop"; "9instr"]; [":bvmap"; ":bvmap_set"; ";low32"; ";nan_box"; ";reg_get"; ";slice_set"; "<wbytes"; "=frm_zero"; ">FPState"; ">fp_csr"; ">fp_regs"; ">fx0"; ">getr"; ">mkFP"; ">mkst"; ">rdn"]; [">v_addi"; "?land"; "?le"; "?lor"; "?lt"; "?pow"; "?shiftr"; "0a"; "0b"; "0bs"; "0cs'"; "0dst"; "0f"; "0fl"; "0fmt"; "0fr'"]; ["0fx"; "0imm"; "0md"; "0mem"; "0n"; "0op"; "0pc"; "0rd"; "0regs"; "0rm"; "0rom"; "0rs"; "0rs1"; "0rs2"; "0segs"; "0src"]; ["@BV"; "@Z_to_bv"; "@bv"; "@bv_extract"; "@bv_signed"; "@bv_unsigned"; "0uimm"; "0v"; "0w"; "0z"]]).
Definition frm_zero (f : bv 32) : Prop :=
Z.land (Z.shiftr (bv_unsigned f) 5) 7 = 0%Z.
Lemma fp_frm_zero_fx0 : ltac2:(TCodec.tc2 tcn__FPSteps "5&QG&QI&QK%211%411").
Proof. reflexivity. Qed.
Lemma fp_fflags_bits_range : ltac2:(TCodec.tc2 tcn__FPSteps "='J'9&R2z&Kr1%211%5241&R4+Q0%2241%:241pTL<1").
Proof.
intros [nv dz of uf nx]. unfold fflags_bits. cbn [fl_nx fl_uf fl_of fl_dz fl_nv].
destruct nv, dz, of, uf, nx; vm_compute; split; congruence.
Qed.
Lemma fp_u32_range : ltac2:(TCodec.tc2 tcn__FPSteps "B'S2yQ0%211'9&R2z&S5r1%2271%5241&R4&R5+2+Q0%3221%5271%=271pTJ?1").
Proof. intros f. pose proof (bv_unsigned_in_range _ f) as H. unfold bv_modulus in H. exact H. Qed.
Lemma fp_Z_land_range_l : ltac2:(TCodec.tc2 tcn__FPSteps "I'=&R2zr3%3221'9&R4&R5+2r4%3221%5281%7281&R1%125;%>2=1r5%:291%<241%>241p081p0A1pTBF1pT@G1pU:H1").
Proof.
intros n a b Hn Ha. split; [apply Z.land_nonneg; lia|].
apply Z_bounded_by_bits; [lia| apply Z.land_nonneg; lia |].
intros k Hk. rewrite Z.land_spec. rewrite (Z_testbit_high n a k) by lia. reflexivity.
Qed.
Lemma fp_Z_lor_range : ltac2:(TCodec.tc2 tcn__FPSteps "N'=&R2zr3%3221'9&R4&R5+2r4%3221%5281%7281r5%7261%92<1%;2<1&R3%1259%B2A1r6%>2=1%@241%B241p081p0=1p0F1pTBK1pT@L1pU:M1").
Proof.
intros n a b Hn Ha Hb. split; [apply Z.lor_nonneg; lia|].
apply Z_bounded_by_bits; [lia| apply Z.lor_nonneg; lia |].
intros k Hk. rewrite Z.lor_spec.
rewrite (Z_testbit_high n a k) by lia. rewrite (Z_testbit_high n b k) by lia. reflexivity.
Qed.
Lemma fp_u_Z2bv32 : ltac2:(TCodec.tc2 tcn__FPSteps "G'='9&R2zr1%3221&R4&R5+2+Q0%3221%5271%;271':&S5yQ0&S1r2%2231%5241%73D13p091pVDF1").
Proof.
intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact Hz.
Qed.
Lemma fp_frm_zero_accrue : ltac2:(TCodec.tc2 tcn__FPSteps "L'S2yQ0%211'='9&R2zr1%3221&R4+Q0%2241%8241&QGr3%211&S1&R3&S5r4%22C1%4217%62E1%:11p091p0=1pTBG1pTJI1").
Proof.
intros f b Hb Hf. unfold frm_zero in *.
pose proof (fp_u32_range f) as Hr.
rewrite fp_u_Z2bv32 by (apply (fp_Z_lor_range 32); lia).
rewrite Z.shiftr_lor. rewrite (Z.shiftr_div_pow2 b 5) by lia.
rewrite (Z.div_small b (2^5)) by lia. rewrite Z.lor_0_r. exact Hf.
Qed.
Lemma fp_frm_zero_slice0_5 : ltac2:(TCodec.tc2 tcn__FPSteps "A'S2yQ0%211yR0%411&QGr2%211&QEr3z+5%443216%811p071pV@;1pTJ>1").
Proof.
intros f v Hf. unfold frm_zero, slice_set in *.
pose proof (fp_u32_range f) as Hr.
change (Z.shiftl (Z.ones 5) 0) with 31%Z.
rewrite Z.shiftl_0_r.
assert (H1 : (0 <= Z.land (bv_unsigned f) (Z.lnot 31) < 2^32)%Z)
by (apply fp_Z_land_range_l; lia).
assert (H2 : (0 <= Z.land (bv_unsigned v) 31 < 2^32)%Z).
{ split; [apply Z.land_nonneg; right; lia|].
rewrite Z.land_comm. apply (proj2 (fp_Z_land_range_l 32 31 (bv_unsigned v) ltac:(lia) ltac:(lia))). }
rewrite fp_u_Z2bv32 by (apply (fp_Z_lor_range 32); lia).
rewrite Z.shiftr_lor, !Z.shiftr_land.
change (Z.shiftr (Z.lnot 31) 5) with (-1)%Z. change (Z.shiftr 31 5) with 0%Z.
rewrite Z.land_m1_r, Z.land_0_r, Z.lor_0_r. exact Hf.
Qed.
Lemma fp_resolve_rm : ltac2:(TCodec.tc2 tcn__FPSteps "Q<'S2y3%211yQ0%411&QGr1%211'<&R2&S5r3%22;1+4%5221':'=+7%33261%;251';'L'4%112&Mr5%@2I1&R1&R6r4%D2K1+5%4221%621@%:281(0%12?N%F3>31qU6A1%C2B1p0E1p0Q21pTJQ61pUDQ91").
Proof.
intros rm f Hf Hrm. unfold rmode_of_field. rewrite Hf.
pose proof (bv_unsigned_in_range _ rm) as Hr.
destruct (Z.eqb_spec (bv_unsigned rm) 7) as [E|NE].
- exists RNE. reflexivity.
- unfold rmode_of_Z.
destruct (Z.eqb_spec (bv_unsigned rm) 0); [eexists; reflexivity|].
destruct (Z.eqb_spec (bv_unsigned rm) 1); [eexists; reflexivity|].
destruct (Z.eqb_spec (bv_unsigned rm) 2); [eexists; reflexivity|].
destruct (Z.eqb_spec (bv_unsigned rm) 3); [eexists; reflexivity|].
destruct (Z.eqb_spec (bv_unsigned rm) 4); [eexists; reflexivity|].
exfalso. lia.
Qed.
Ltac fp_pipeline Hfetch Hecall Hdecode :=
unfold RiscvSemantics.step, RiscvSemantics.step_accesses;
cbn [ms_pc ms_pc_val mkst];
rewrite Hfetch;
cbv beta iota;
unfold RiscvSemantics.drop_access_report,
RiscvSemantics.decode_exec_accesses;
rewrite Hecall;
cbv beta iota;
rewrite Hdecode;
cbv beta iota zeta delta
[RiscvSemantics.interp_eff_accesses
RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
Sem.exec Sem.load_val Sem.store_val Sem.exec_csr
Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv
Sem.fget Sem.fset Sem.with_fregs Sem.with_fcsr Sem.fread Sem.fwrite
Sem.accrue Sem.resolve_rm Sem.frm_of
Sem.inval_resv Sem.w0 Sem.w1
Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
RiscvSemantics.access_value RiscvSemantics.drop_access_report
ms_regs ms_fregs ms_fcsr ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom mkst fp_regs fp_csr];
rewrite ?bv_eqb0_is_x0.
Lemma fp_step_fld : ltac2:(TCodec.tc2 tcn__FPSteps "SD'QH'3'@%211&Q@y5'S2yR0%211%5241'4y8%611%311p061yQ0%:11%;1<y<%=11%C18':%<16&Br;r9%3221(0r6%22=1%93841'1&Cr7%211(2%?3521'6'Q?'=%3221%O11&Ir8%211(5(Q2(Q3r5%342@E1+4%64=<21%I2<1%Q03<91&R0&QLr=%221H&S4%12Q9O%6231%Q83QE1=%QD1Q:&QOr?r<u8%4432Q71%Q92Q@D%Q@3721'D'E%211&Fr@&QNrAr>%352>1F=%6251(A(QM&QAr:&S3w&?%11QK%44RA3RA1&QJ%11>%95RFRC831&QI%11A%=231%Q92BQ=%E52Q01Q8O%A2J1%R=3JC1p0N1p0Q71p0Q@1p0R21p0R91pTDRD1pT@S11pU4RG1pUHRJ1pU@RK1pVBRM1pUFS01pU8S11pU>S81pUBS81pUNS?1pU2SC1").
Proof.
intros fx segs regs pc mem rom w rd rs imm a bs Hf He Hd Ha Hr.
fp_pipeline Hf He Hd.
unfold getr in Ha; rewrite ?bv_eqb0_is_x0 in Ha.
rewrite ov_rdn, b_addsext, Ha, Hr. cbv beta iota.
cbn [fp_regs fp_csr]. rewrite b_npc4. reflexivity.
Qed.
Lemma fp_step_flw : ltac2:(TCodec.tc2 tcn__FPSteps "SF'QH'3'@%211&Q@y5'S2yR0%211%5241'4y8%611%311p061yQ0%:11%;1<y<%=11%C18':%<16&Br;r9%3221(0r6%22=1%93841'1&Cr7%211(2%?3521'6'Q?'=%3221%O11&Ir8%211(5(Q2(Q4r5%342@E1+4%64=<21%I2<1%Q03<91&R0&QLr=%221H&S4%12Q9O%6231%Q83QE1=%QD1Q:&QOr?r<u4%4432Q71%Q92Q@D%Q@3721'D'E%211&Fr@&QNrAr>%352>1F=%6251(A(QM&QAr:&QC&S3w&?%11QL%44RB3R:1%611&QJ%11@%;5RHRE:31&QI%11C%?231%Q;2DQ?%G52Q21Q:Q1%C2L1%R?3LE1p0Q01p0Q91p0QB1p0R41p0R;1pTDRF1pT@S31pU4RI1pUHRL1pU@RM1pVBRO1pUFS21pU8S31pU>S:1pUBS:1pUNSA1pU2SE1").
Proof.
intros fx segs regs pc mem rom w rd rs imm a bs Hf He Hd Ha Hr.
fp_pipeline Hf He Hd.
unfold getr in Ha; rewrite ?bv_eqb0_is_x0 in Ha.
rewrite ov_rdn, b_addsext, Ha, Hr. cbv beta iota.
cbn [fp_regs fp_csr]. rewrite b_npc4. reflexivity.
Qed.
Lemma fp_step_fsd : ltac2:(TCodec.tc2 tcn__FPSteps "S;'QH'3'@%211&Q@y5'S2yR0%211%5241'4y8%611%311p061yQ0%:11%;1<y<%=11':%;15&Br:r8%3221(0r5%22<1%93841'1&Cr6%211(2%?3521'6'Q?'=%3221%N11&Ir7%211(5(Q6(Q3r4%342@E1+4%64=<21%I2<1%Q03<91&R0&QLr<%221>&S4%12Q8O%6231%Q83QD1=&Gr>r;u8%4432Q61(7%Q?3Q521'D'E%211&Fr?&QNr@r=%352>1E=%6251(A%J24N&QF&H&QD&QJ%11:%321QM%52F1%73Q0QG1%?5>J91I%;2D1%R63D=1p0H1p0Q01p0Q91p0QK1p0R21pT@RH1pU4R>1pULRA1pUJRB1pVBRD1pUFRG1pU8RH1pU>RO1pUBRO1pUNS61pU2S:1").
Proof.
intros fx segs regs pc mem rom w rs1 rs2 imm a Hf He Hd Ha Hok.
fp_pipeline Hf He Hd.
unfold getr in Ha; rewrite ?bv_eqb0_is_x0 in Ha.
rewrite b_addsext, Ha, Hok. cbv beta iota.
rewrite write_to_mem_wbytes, b_npc4. destruct fx; reflexivity.
Qed.
Lemma fp_step_fsw : ltac2:(TCodec.tc2 tcn__FPSteps "S?'QH'3'@%211&Q@y5'S2yR0%211%5241'4y8%611%311p061yQ0%:11%;1<y<%=11':%;15&Br:r8%3221(0r5%22<1%93841'1&Cr6%211(2%?3521'6'Q?'=%3221%N11&Ir7%211(5(Q6(Q4r4%342@E1+4%64=<21%I2<1%Q03<91&R0&QLr<%221>&S4%12Q8O%6231%Q83QD1=&Gr>r;u4%4432Q61(7%Q?3Q521'D'E%211&Fr?&QNr@r=%352>1E=%6251(A%J24N&QF&>&S5&QB&QD&QJ%11<%321QO%511%72R:1%92J1%;3Q4QK1%C5BN=1M%?2H1%R:3HA1p0L1p0Q41p0Q=1p0QO1p0R61pT@RL1pU4RB1pULRE1pUJRF1pVBRH1pUFRK1pU8RL1pU>S31pUBS31pUNS:1pU2S>1").
Proof.
intros fx segs regs pc mem rom w rs1 rs2 imm a Hf He Hd Ha Hok.
fp_pipeline Hf He Hd.
unfold getr in Ha; rewrite ?bv_eqb0_is_x0 in Ha.
rewrite b_addsext, Ha, Hok. cbv beta iota.
rewrite write_to_mem_wbytes, b_npc4. destruct fx; reflexivity.
Qed.
Lemma fp_step_fmv_x_d : forall (fx : FPState) segs regs pc mem rom w rd rs1,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Fmv FMV_X_F FMT_D rd rs1, 4%Z) ->
RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
MachineOk (@mkst fx (if bv_eqb rd 0 then regs else regupd regs rd (reg_get (@fp_regs fx) rs1))
(v_addi pc 4) mem rom).
Proof.
intros fx segs regs pc mem rom w rd rs1 Hf He Hd.
fp_pipeline Hf He Hd.
destruct (is_x0 rd); cbv beta iota; rewrite b_npc4; destruct fx; reflexivity.
Qed.
Lemma fp_step_fmv_x_w : forall (fx : FPState) segs regs pc mem rom w rd rs1,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Fmv FMV_X_F FMT_S rd rs1, 4%Z) ->
RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
MachineOk (@mkst fx (if bv_eqb rd 0 then regs
else regupd regs rd (sext 64 (low32 (reg_get (@fp_regs fx) rs1))))
(v_addi pc 4) mem rom).
Proof.
intros fx segs regs pc mem rom w rd rs1 Hf He Hd.
fp_pipeline Hf He Hd.
destruct (is_x0 rd); cbv beta iota; rewrite b_npc4; destruct fx; reflexivity.
Qed.
Lemma fp_step_fmv_d_x : ltac2:(TCodec.tc2 tcn__FPSteps "RK'QH'3'@%211&Q@y5'S2yR0%211%5241'4y8%611%311p061yQ0%:11%;1<':%913&Br8r6%3221(0r3%22:1%93841'1&Cr4%211(2%?3521'6'Q?'=%3221%L11&Ir5%211(5(Q9(Q5(Q3%3421@E+4%64=<21%I2<1%Q03<91'D'E%211&Fr;&QNr<r:r9r7%55432Q81%8271(A(QM&QA&QL%129Q5&QJ%11<%55R1QNN31&QI%11?%9231&R0%12@L%D53B1QG@%>2I1%QL3I@1p0M1p0Q?1p0QF1pUJR11pU@R21pVBR41pUFR71pU8R81pU>R?1pUBR?1pUNRF1pU2RJ1").
Proof.
intros fx segs regs pc mem rom w rd rs1 Hf He Hd.
fp_pipeline Hf He Hd. unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs1); cbv beta iota; cbn [fp_regs fp_csr]; rewrite b_npc4; reflexivity.
Qed.
Lemma fp_step_fmv_w_x : ltac2:(TCodec.tc2 tcn__FPSteps "RO'QH'3'@%211&Q@y5'S2yR0%211%5241'4y8%611%311p061yQ0%:11%;1<':%913&Br8r6%3221(0r3%22:1%93841'1&Cr4%211(2%?3521'6'Q?'=%3221%L11&Ir5%211(5(Q9(Q5(Q4%3421@E+4%64=<21%I2<1%Q03<91'D'E%211&Fr;&QNr<r:r9r7%55432Q81%8271(A(QM&QA&QC&QB&QL%12;Q7%311%511&QJ%11@%95R5R2Q231&QI%11C%=231&R0%12DQ0%H53F1QKD%B2M1%R03MD1p0Q11p0QC1p0QJ1pUJR51pU@R61pVBR81pUFR;1pU8R<1pU>RC1pUBRC1pUNRJ1pU2RN1").
Proof.
intros fx segs regs pc mem rom w rd rs1 Hf He Hd.
fp_pipeline Hf He Hd. unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs1); cbv beta iota; cbn [fp_regs fp_csr]; rewrite b_npc4; reflexivity.
Qed.
Lemma fp_step_fsgnj : ltac2:(TCodec.tc2 tcn__FPSteps "RO'QH'3'@%211&Q@y5'S2yR0%211%5241'4y8%611%311p061yQ0%:11'Q>'Q=%=1>':%;15&Br;r9%3221(0r6%22<1%93841'1&Cr7%211(2%?3521'6'Q?'=%3221%N11&Ir8%211(5(Q:r5r4r3%45AF321+4%74>=21%J2=1%Q13=:1';'D'E%211&Fr?&QNr@r>r=r<%554321Q:%8271(A(QMr1&QI%11:%4231&R0%12;H%?53=1;QD%92D1%QI3D;1qU0R51%I2R61p0K1p0Q>1p0QE1pULR01pUJR11pU@R21pTNR41pU<R61pVBR81pUFR;1pU8R<1pU>RC1pUBRC1pUNRJ1pU2RN1").
Proof.
intros fx segs regs pc mem rom w op fmt rd rs1 rs2 Hf He Hd.
destruct fmt; eexists; fp_pipeline Hf He Hd; cbn [fp_regs fp_csr]; rewrite b_npc4; reflexivity.
Qed.
Lemma fp_step_fari : ltac2:(TCodec.tc2 tcn__FPSteps "SF'QH'3'@%211&Q@y5'S2yR0%211%5241'4y8%611%311p061yQ0%:11'Q;'Q=%=1>y3%?11':%=17&Br<r:%3221(0r7%22>1%93841'1&Cr8%211(2%?3521'6'Q?'=%3221%Q011&Ir9%211(5(Q7r6r5r4r3%56BG4321+4%84?>21%K2>1%Q23>;1&QG&QIr@%211%411'<&R2&S5%12Q=@%321=+7%Q>3L31%7231';'9r1%@11'D'E%211&FrC&QNrDrBrAr?%55432I1%8271(A(QMr2%221A&R0%129Q6%=53;1Q19%72B1%R83B91%H2F1qTFR@1%K2RA1qU0RI1%M2RJ1p0O1p0Q81p0Q>1p0R21p0R91pUDRD1pULRG1pUJRH1pU@RI1pTNRK1pU<RM1pVBRO1pUFS21pU8S31pU>S:1pUBS:1pUNSA1pU2SE1").
Proof.
intros fx segs regs pc mem rom w op fmt rd rs1 rs2 rm Hf He Hd Hz Hrm.
destruct (fp_resolve_rm rm _ Hz Hrm) as [md Hmd].
destruct fx as [fr cs]. cbn [fp_csr] in *.
assert (Hacc : forall fl, frm_zero (Z_to_bv 32 (Z.lor (bv_unsigned cs) (fflags_bits fl))))
by (intros fl; apply fp_frm_zero_accrue; [apply fp_fflags_bits_range | exact Hz]).
fp_pipeline Hf He Hd. rewrite Hmd. cbv beta iota.
repeat match goal with
| |- context [let '(_, _) := ?p in _] => destruct p as [?v ?fl]; cbv beta iota
end.
destruct fmt; cbv beta iota; rewrite b_npc4;
(eexists _, _; split; [apply Hacc | reflexivity]).
Qed.
Lemma fp_step_fcvt_to_f : ltac2:(TCodec.tc2 tcn__FPSteps "SI'QH'3'@%211&Q@y5'S2yR0%211%5241'4y8%611%311p061yQ0%:11'Q<%<1=y3%>11':%<16&Br;r9%3221(0r6%22=1%93841'1&Cr7%211(2%?3521'6'Q?'=%3221%O11&Ir8%211(5(Q8r5r4r3%45AF321+4%74>=21%J2=1%Q13=:1'<(Q1%Q43Q8>1(Q0%Q63Q:@1%5231&QG&QIr@%211%411&R2&S5%12QAQ8%321B+7%QB3Q031%A231';'9r1%?11'D'E%211&FrC&QNrDrBrAr?%55432H1%8271(A(QMr2%221A&R0%129Q;%=53;1Q09%72B1%R<3B91%H2F1qTFRC1%K2RD1qU0RL1%M2RM1p0O1p0Q71p0Q=1p0QD1p0R71p0R>1pUDRI1pUJRL1pU@RM1pV0RO1pTHS01pVBS21pUFS51pU8S61pU>S=1pUBS=1pUNSD1pU2SH1").
Proof.
intros fx segs regs pc mem rom w dst src rd rs1 rm Hf He Hd Hdst Hz Hrm.
destruct (fp_resolve_rm rm _ Hz Hrm) as [md Hmd].
destruct fx as [fr cs]. cbn [fp_csr] in *.
assert (Hacc : forall fl, frm_zero (Z_to_bv 32 (Z.lor (bv_unsigned cs) (fflags_bits fl))))
by (intros fl; apply fp_frm_zero_accrue; [apply fp_fflags_bits_range | exact Hz]).
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
(eexists _, _; split; [ | reflexivity ]; first [apply Hacc | exact Hz]).
Qed.
Lemma fp_step_fcvt_to_x : forall (fx : FPState) segs regs pc mem rom w dst src rd rs1 (rm : bv 3),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Fcvt dst src rd rs1 rm, 4%Z) ->
(dst = FC_W \/ dst = FC_WU \/ dst = FC_L \/ dst = FC_LU) ->
(src = FC_S \/ src = FC_D) ->
frm_zero (@fp_csr fx) ->
(bv_unsigned rm <= 4 \/ bv_unsigned rm = 7)%Z ->
exists (v : word) cs',
frm_zero cs' /\
RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
MachineOk (@mkst (mkFP (@fp_regs fx) cs') (if bv_eqb rd 0 then regs else regupd regs rd v)
(v_addi pc 4) mem rom).
Proof.
intros fx segs regs pc mem rom w dst src rd rs1 rm Hf He Hd Hdst Hsrc Hz Hrm.
destruct (fp_resolve_rm rm _ Hz Hrm) as [md Hmd].
destruct fx as [fr cs]. cbn [fp_csr fp_regs] in *.
assert (Hacc : forall fl, frm_zero (Z_to_bv 32 (Z.lor (bv_unsigned cs) (fflags_bits fl))))
by (intros fl; apply fp_frm_zero_accrue; [apply fp_fflags_bits_range | exact Hz]).
fp_pipeline Hf He Hd. rewrite Hmd. cbv beta iota.
destruct Hdst as [-> | [-> | [-> | ->]]]; destruct Hsrc as [-> | ->]; cbv beta iota;
repeat match goal with
| |- context [let '(_, _) := ?p in _] => destruct p as [?v ?fl]; cbv beta iota
end;
(destruct (is_x0 rd); cbv beta iota; rewrite b_npc4;
[ exists (Z_to_bv 64 0); eexists; split; [ apply Hacc | reflexivity ]
| eexists _, _; split; [ apply Hacc | reflexivity ] ]).
Qed.
Lemma fp_step_fcmp : forall (fx : FPState) segs regs pc mem rom w op fmt rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Fcmp op fmt rd rs1 rs2, 4%Z) ->
frm_zero (@fp_csr fx) ->
exists (b : bool) cs',
frm_zero cs' /\
RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
MachineOk (@mkst (mkFP (@fp_regs fx) cs')
(if bv_eqb rd 0 then regs else regupd regs rd (if b then Z_to_bv 64 1 else Z_to_bv 64 0))
(v_addi pc 4) mem rom).
Proof.
intros fx segs regs pc mem rom w op fmt rd rs1 rs2 Hf He Hd Hz.
destruct fx as [fr cs]. cbn [fp_csr fp_regs] in *.
assert (Hacc : forall fl, frm_zero (Z_to_bv 32 (Z.lor (bv_unsigned cs) (fflags_bits fl))))
by (intros fl; apply fp_frm_zero_accrue; [apply fp_fflags_bits_range | exact Hz]).
fp_pipeline Hf He Hd.
repeat match goal with
| |- context [let '(_, _) := ?p in _] => destruct p as [?v ?fl]; cbv beta iota
end.
destruct (is_x0 rd);
[ exists true; eexists; split; [ apply Hacc | rewrite b_npc4; reflexivity ]
| exists v; destruct v; cbv beta iota; rewrite b_npc4;
(eexists; split; [ apply Hacc | reflexivity ]) ].
Qed.
Lemma fp_step_frrm : forall (fx : FPState) segs regs pc mem rom w rd,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Csr CSR_RS rd 0 2, 4%Z) ->
frm_zero (@fp_csr fx) ->
RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
MachineOk (@mkst fx (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 0))
(v_addi pc 4) mem rom).
Proof.
intros fx segs regs pc mem rom w rd Hf He Hd Hz.
destruct fx as [fr cs]. cbn [fp_csr] in Hz. unfold frm_zero in Hz.
fp_pipeline Hf He Hd.
change (csr_slice 2) with (Some (5%Z, 3%Z)). cbv beta iota.
unfold slice_get. change (Z.ones 3) with 7%Z. rewrite Hz.
change (is_x0 0) with true. cbv beta iota.
destruct (is_x0 rd); cbv beta iota; rewrite b_npc4; reflexivity.
Qed.
Lemma fp_step_csrsi_fflags : ltac2:(TCodec.tc2 tcn__FPSteps "S7'QH'3'@%211&Q@y5'S2yR0%211%5241'4y8%611%311p061yQ0%:11%;1<':%913&Br7r5%3221(0r2%22:1%93841'1&Cr3%211(2%?3521'6'Q?'=%3221%L11&Ir4%211(5(O(N(S0z(8%33Q;21y<+1%63214%9484F1+4%<4CB21%O2B1%Q63B?1&QG&QIr;%211%411';'9r1%811'D'E%211&Fr<&QNr=r:r9r8%554A321%8271(A(QM&QJ%119%321B&R0%12;O%>53J1;:%82C1%R53C:1%I2G1qTFR91%L2R:1p0N1p0Q41p0QL1p0R31pV>R>1pVBR@1pUFRC1pU8RD1pU>RK1pUBRK1pUNS21pU2S61").
Proof.
intros fx segs regs pc mem rom w uimm Hf He Hd Hz.
destruct fx as [fr cs]. cbn [fp_csr fp_regs] in *.
destruct (Z.eqb (bv_unsigned uimm) 0) eqn:Eu.
- exists cs. split; [exact Hz|].
fp_pipeline Hf He Hd. rewrite Eu.
change (csr_slice 1) with (Some (0%Z, 5%Z)). cbv beta iota.
change (is_x0 0) with true. cbv beta iota. rewrite b_npc4. reflexivity.
- exists (slice_set cs 0 5 (bv_or (slice_get cs 0 5) (zext 64 uimm))).
split; [apply fp_frm_zero_slice0_5; exact Hz|].
fp_pipeline Hf He Hd. rewrite Eu.
change (csr_slice 1) with (Some (0%Z, 5%Z)). cbv beta iota.
change (is_x0 0) with true. cbv beta iota. rewrite b_npc4. reflexivity.
Qed.
