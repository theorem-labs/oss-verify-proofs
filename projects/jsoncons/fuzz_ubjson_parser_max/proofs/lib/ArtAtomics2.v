(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac ArtAtomics.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__ArtAtomics2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.DecodeC."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtAtomics."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1false"; "1list"; "1option"; "1pair"; "1prod"; "1true"; "2I"; "2eq"; "3Z"; "4bytes_le_to_Z"; "5Segment"; "6MachineOk"; "6fetch_word"; "6is_ecall"]; ["6machine_result"; "6machine_state"; "6step"; "6store_ok"; "6word_to_le_bytes"; "7decode_any"; "8AD"; "8ALU_ADD"; "8AMO_ADD"; "8AW"; "8Amo"; "8OpImm"; "8instr"; "9bv_eqb"; "9bvmap"; ":mkstr"]; [";wbytes"; "<getr"; "<mkst"; "<rdn"; "<regupd"; "<v_add"; "<v_addi"; "<v_lw"; "=lt"; "=modulo"; "=pow"; "0a"; "0aq"; "0bs"; "0fx"; "0imm"]; ["0mem"; "0old"; "0pc"; "0r"; "0rd"; "0regs"; "0rl"; "0rom"; "0rs"; "0rs1"; "0rs2"; "0segs"; ">BV"; ">bv"; ">bv_signed"; ">bv_unsigned"]; ["0v"; "0w"]]).
Section FPX. Context {fx : PropExec.FPState}.
#[local] Ltac amo_unfold :=
cbv beta iota zeta delta
[RiscvSemantics.interp_eff_accesses RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ negb Sem.is_x0
Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv Sem.inval_resv Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom ms_fregs ms_fcsr mkstr mkst].
Lemma art_step_amoadd_d_rd : ltac2:(TCodec.tc2 tcn__ArtAtomics2 "T<'3'<%211&Ny5'QMyR0%211%5241'4y8%611%311p061yQ0%:11'1%<1=%B17'9%;15&>r?r=%3221(0r:%22<1%93841&?r;%211(2%>3A21'6'L':%3221%M11&Er<%211(5(J(H(Fr9r8r7%6754CG321+4%94@?21%K2?1%Q23?<1&M(QLz(8%33QF21%53QGQ11%Q93Q<1L&Q1rB%221Q5%Q=3QI1A&Q9&QO%12QME+8%4221%QC3Q21>%QN1QE&Q3rEu8%342=QA1%QC2QJL%QJ3621&;%11Q0%QM3Q<1=rF%E21QK%R03R<1QE&CrH%241=QO<(7%R53R821'@'A%211&BrI&Q2vQ>rG%352<1@H%6251(=&Q4rA%23A1QN&Q6%128QF&Q0r>&D&Q5%12R5RF%32Q41%63N51%B5A:81Q7%>2G1%RO3G@1p0K1p0Q11p0Q51p0Q91p0QA1p0QH1p0QM1p0R51p0RJ1p0S01pRLS;1pS4SG1pT2SH1pRHSI1pSFS@1pSDSA1pS:SB1pS>SD1pRJSE1pT4SG1pS@SJ1pS2SK1pS6T21pS<T21pSHT91").
Proof.
intros segs regs pc mem rom w aq rl rd rs1 rs2 a v old bs Hf He Hd Hrd Ha Hal Hread Hv Hrs2 Hok.
step_pipeline Hf He Hd.
unfold getr in Ha, Hrs2; rewrite ?bv_eqb0_is_x0 in Ha, Hrs2.
rewrite Ha, Hrs2.
unfold amo_aligned. cbn [amo_bytes]. rewrite Hal. rewrite Z.eqb_refl.
amo_unfold.
assert (Hz : bv_extract 0 64 old = old).
{ apply bv_eq. rewrite bv_extract_unsigned, Z.shiftr_0_r. apply bv_wrap_bv_unsigned. }
rewrite ov_rdn, Hread; cbv beta iota.
rewrite (le_word_v _ _ Hv), Hz.
rewrite Hok; cbv beta iota.
unfold bv_eqb in Hrd. change (bv_unsigned (0%bv : bv 5)) with 0%Z in Hrd. rewrite Hrd. cbv beta iota.
rewrite ?write_to_mem_wbytes, ?b_npc4, <- alu_add.
reflexivity.
Qed.
Lemma art_step_amoadd_w_rd : ltac2:(TCodec.tc2 tcn__ArtAtomics2 "TE'3'<%211&Ny5'QMyR0%211%5241'4y8%611%311p061yQ0%:11'1%<1=%B17'9%;15&>r?r=%3221(0r:%22<1%93841&?r;%211(2%>3A21'6'L':%3221%M11&Er<%211(5(J(H(Ir9r8r7%6754CG321+4%94@?21%K2?1%Q23?<1&M(QLz(8%33QF21%53QGQ11%Q93Q<1L&Q1rB%221Q5%Q=3QI1A&Q9&QO%12QME%321B%QB3Q11=%QM1QD&Q3rEu4%342<Q@1%QB2QIK%QI3621&;%11O%QL3Q;1<&Q8%?2R;QG&Q:+2+Q0%3221%6251rGr>%L221%R73RC1QB&CrIrF%34216E(7%R=3R@21'@'A%211&BrJ&Q2vQ>rH%352=1B<%6251(=&Q4&Q7%11RG%33CQA1&Q6%129QO&Q0&D&Q5%12RNM%32Q=1%53Q0S11%B5A971K%>2G1%S73G@1p0K1p0Q21p0Q71p0Q?1p0QC1p0QK1p0R11p0R61p0R>1p0S31p0S91pRLSD1pS4T01pT2T11pRHT21pSFSI1pSDSJ1pS:SK1pS>SM1pRJSN1pT4T01pS@T31pS2T41pS6T;1pS<T;1pSHTB1").
Proof.
intros segs regs pc mem rom w aq rl rd rs1 rs2 a v old bs Hf He Hd Hrd Ha Hal Hread Hv Hold Hrs2 Hok.
step_pipeline Hf He Hd.
unfold getr in Ha, Hrs2; rewrite ?bv_eqb0_is_x0 in Ha, Hrs2. rewrite Ha, Hrs2.
unfold amo_aligned. cbn [amo_bytes]. rewrite Hal, Z.eqb_refl. amo_unfold.
rewrite ov_rdn, Hread; cbv beta iota.
rewrite (le_word_v _ _ Hv).
rewrite Hok; cbv beta iota.
unfold bv_eqb in Hrd. change (bv_unsigned (0%bv : bv 5)) with 0%Z in Hrd. rewrite Hrd. cbv beta iota.
rewrite ?write_to_mem_wbytes, ?b_npc4, b_lw_val.
assert (Hb : Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD (bv_extract 0 32 old) (low32 v))) = word_to_le_bytes 4 (v_add old v)).
{ cbn [amo_val]. unfold low32, word_to_le_bytes, v_add.
rewrite bv_add_unsigned, !bv_extract_unsigned, !Z.shiftr_0_r, Z_to_bv_unsigned.
rewrite (bv_wrap_small 32 (bv_unsigned old)) by (pose proof (u64_range old); change (bv_modulus 32) with 4294967296%Z; lia).
rewrite Z_to_le_bytes_wrap by (cbn; lia).
rewrite <- (Z_to_le_bytes_wrap 4 32 (bv_wrap 64 _)) by (cbn; lia).
rewrite <- (Z_to_le_bytes_wrap 4 32 (bv_unsigned old + bv_wrap 32 (bv_unsigned v))) by (cbn; lia).
f_equal. unfold bv_wrap.
change (bv_modulus 64) with (4294967296 * 4294967296)%Z. change (bv_modulus 32) with 4294967296%Z.
apply art_mod32_helper. }
rewrite Hb. reflexivity.
Qed.
#[local] Ltac step_pipeline_r Hfetch Hecall Hdecode :=
unfold RiscvSemantics.step, RiscvSemantics.step_accesses;
cbn [ms_pc ms_pc_val mkstr];
rewrite Hfetch; cbv beta iota;
unfold RiscvSemantics.drop_access_report, RiscvSemantics.decode_exec_accesses;
rewrite Hecall; cbv beta iota;
rewrite Hdecode;
cbv beta iota zeta delta
[RiscvSemantics.interp_eff_accesses RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
Sem.exec Sem.load_val Sem.store_val Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv Sem.inval_resv Sem.w0 Sem.w1
Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom ms_fregs ms_fcsr mkstr];
rewrite ?bv_eqb0_is_x0.
Lemma art_step_opimm_r : forall segs regs pc mem rom w op rd rs (imm : bv 12) r,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (OpImm op rd rs imm, 4%Z) ->
RiscvSemantics.step segs (mkstr regs pc mem rom r) =
MachineOk (mkstr (if bv_eqb rd 0 then regs else regupd regs rd (alu64 op (getr regs rs) (sext 64 imm))) (v_addi pc 4) mem rom r).
Proof.
intros segs regs pc mem rom w op rd rs imm r Hf He Hd.
step_pipeline_r Hf He Hd.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs); destruct (is_x0 rd); cbv beta iota; rewrite ?b_npc4; reflexivity.
Qed.
Lemma art_step_addi_r : ltac2:(TCodec.tc2 tcn__ArtAtomics2 "S3'3'<%211&Ny5'QMyR0%211%5241'4y8%611%311p061yQ0%:11%;1<y<%=11%:1<'9%<16&>r:r8%3221(0r5%22=1%93841'1&?r6%211(2%?3521'6'L':%3221%O11&Er7%211(5(K(Gr4%342@E1+4%64=<21%I2<1%Q03<91&M(QLz(8%33QE21%53QF@1%Q73M1I'@'A%211&Br>&OvQ>r=r<r;%564321Q?Q;%8271(=&Q4&Q6&Q1%129Q2&QN%12QMQ>%5231%73=QH1%72=Q0%A6@21=QKQG%;2F1%R03F=1p0J1p0Q21p0QD1p0QK1pS8R61pS0R81pSBR;1pS:R<1pT4R>1pS@RA1pS2RB1pS6RI1pS<RI1pSHS01").
Proof. intros * Hf He Hd Hrd. rewrite (art_step_opimm_r _ _ _ _ _ _ _ _ _ _ r Hf He Hd), Hrd, alu_addi. reflexivity. Qed.
End FPX.
