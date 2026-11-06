(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__ArtAtomics () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.DecodeC."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtAtomics.FPX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1bool"; "1false"; "1list"; "1option"; "1pair"; "1prod"; "1true"; "2I"; "2eq"; "3Z"; "4bytes_le_to_Z"; "5Segment"; "6MachineOk"; "6fetch_word"]; ["6is_ecall"; "6machine_result"; "6machine_state"; "6step"; "6store_ok"; "6word_to_le_bytes"; "7decode_any"; "8AD"; "8ALU_AND"; "8ALU_OR"; "8ALU_XOR"; "8AMO_ADD"; "8AW"; "8Amo"; "8Branch"; "8Lr"]; ["8Op"; "8Sc"; "8branch_cond"; "8instr"; "9bv_eqb"; "9bvmap"; ":branch_taken"; ";mkstr"; "<wbytes"; "=btgt"; "=getr"; "=mkst"; "=rdn"; "=regupd"; "=v_add"; "=v_addi"]; ["=v_and"; "=v_lw"; "=v_or"; "=v_xor"; ">add"; ">lt"; ">modulo"; ">mul"; ">pow"; "0a"; "0aq"; "0b"; "0bs"; "0c"; "0fx"; "0imm"]; ["0mem"; "0old"; "0pc"; "0r"; "0rd"; "0regs"; "0rl"; "0rom"; "0rs1"; "0rs2"; "0segs"; "?BV"; "?Z_to_bv"; "?bv"; "?bv_signed"; "?bv_unsigned"]; ["0v"; "0w"]]).
Lemma art_mod32_helper : ltac2:(TCodec.tc2 tcn__ArtAtomics "B';':&QF&QDr2r1+TPPPPP0%5221%5241%7213%7265&QG%1266%;231%<218%>3?61pSH@1pSDA1").
Proof.
intros a b. rewrite Z.add_mod_idemp_r by lia.
set (x := (a + b)%Z). set (MM := (4294967296 * 4294967296)%Z).
rewrite (Z.div_mod x MM) at 1 by lia.
replace (MM * (x / MM))%Z with ((4294967296 * (x / MM)) * 4294967296)%Z by (unfold MM; lia).
rewrite Z.add_comm, Z.mod_add by lia. reflexivity.
Qed.
Section FPX. Context {fx : PropExec.FPState}.
Lemma art_step_amoadd_d_x0 : ltac2:(TCodec.tc2 tcn__ArtAtomics "T4'4'=%211&Q5y5'R=yR0%211%5241'5y8%611%311p061yQ0%:11'2%<1=%B17':%;15&?r>r<%3221(1r9%22<1%93841&@r:%211(3%>3A21'7'Q3';%3221%M11&Fr;%211(6(M(K(G(R;z(9%33Q=21r8r7%9787FJ321+4%<4CB21%N2B1%Q53B?1&Q:r@%221Q1%Q93QE19&QF&R?%12QI=+8%4221%Q?3N1C%QJ1QA&Q<rCu8%342=Q=1r6%Q@2QG1%QG3731&<%11I%QJ3Q91>rD%F21QH%QM3R91QB&DrF%241>QL=(8%R23R521'A'B%211&CrG&Q;vQNrE%352<1@I%6251(>&Q?%125Q=&Q8r=&E&Q>%12QOR@%32Q21%63K51%?5>H81Q5%;2D1%RI3D=1p0H1p0N1p0Q21p0Q61p0Q?1p0QF1p0QK1p0RC1p0RI1pSJS41pT4S@1pU2SA1pSDSB1pTDS91pTBS:1pT>S<1pSFS=1pU4S?1pT@SB1pT2SC1pT6SJ1pT<SJ1pTFT11").
Proof.
intros segs regs pc mem rom w aq rl rs1 rs2 a v old bs Hf He Hd Ha Hal Hread Hv Hrs2 Hok.
step_pipeline Hf He Hd.
unfold getr in Ha, Hrs2; rewrite ?bv_eqb0_is_x0 in Ha, Hrs2.
rewrite Ha, Hrs2.
unfold amo_aligned. cbn [amo_bytes]. rewrite Hal. rewrite Z.eqb_refl.
cbv beta iota zeta delta
[RiscvSemantics.interp_eff_accesses RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ negb Sem.is_x0
Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv Sem.inval_resv Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom ms_fregs ms_fcsr mkst].
assert (Hz : bv_extract 0 64 old = old).
{ apply bv_eq. rewrite bv_extract_unsigned, Z.shiftr_0_r. apply bv_wrap_bv_unsigned. }
rewrite ov_rdn, Hread; cbv beta iota.
rewrite (le_word_v _ _ Hv), Hz.
rewrite Hok; cbv beta iota.
replace (bv_unsigned (0%bv : bv 5) =? 0)%Z with true by reflexivity. cbv beta iota.
rewrite ?write_to_mem_wbytes, ?b_npc4, <- alu_add.
reflexivity.
Qed.
Definition mkstr (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (r : option word) : machine_state :=
{| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := None; ms_resv := r; ms_fcsr := fp_csr;
ms_mem := mem; ms_rom := rom |}.
Lemma mkstr_none : ltac2:(TCodec.tc2 tcn__ArtAtomics "M&Q5y5'R=yR0%211%5241'5y8%611%311p061':'B&Q7r4r3r2r1(0%11?%7565431&Q;vQN%2519876%=3<41pT@?1pT2@1pT6G1pT<G1").
Proof. reflexivity. Qed.
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
Lemma art_step_op_r : forall segs regs pc mem rom w op rd rs1 rs2 r,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op op rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkstr regs pc mem rom r) =
MachineOk (mkstr (if bv_eqb rd 0 then regs else regupd regs rd (alu64 op (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom r).
Proof.
intros segs regs pc mem rom w op rd rs1 rs2 r Hf He Hd.
step_pipeline_r Hf He Hd.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs1); destruct (is_x0 rs2); destruct (is_x0 rd); cbv beta iota; rewrite ?b_npc4; reflexivity.
Qed.
Lemma art_step_and_r : ltac2:(TCodec.tc2 tcn__ArtAtomics "S0'4'=%211&Q5y5'R=yR0%211%5241'5y8%611%311p061yQ0%:11%;1<%81:':%:14&?r:r8%3221(1r5%22;1%93841'2&@r6%211(3%?3521'7'Q3';%3221%M11&Fr7%211(6(Q0(Hr4%342@E1+4%64=<21%I2<1%Q03<91&Q4(R;z(9%33QC21%53QD@1%Q73M1I'A'B%211&Cr>&Q7r=r<r;%45321Q>Q:%7261(>&Q=&Q@&Q:%129Q1%22:Q<%4221%63<QF1&Q?%12=O%@531=QJQF%;2E1%QO3E=1p0I1p0Q11p0QC1p0QJ1pT8R51pTDR71pTBR81pT:R91pU4R;1pT@R>1pT2R?1pT6RF1pT<RF1pTFRM1").
Proof. intros * Hf He Hd Hrd. rewrite (art_step_op_r _ _ _ _ _ _ _ _ _ _ r Hf He Hd), Hrd, alu_and. reflexivity. Qed.
Lemma art_step_xor_r : ltac2:(TCodec.tc2 tcn__ArtAtomics "S0'4'=%211&Q5y5'R=yR0%211%5241'5y8%611%311p061yQ0%:11%;1<%81:':%:14&?r:r8%3221(1r5%22;1%93841'2&@r6%211(3%?3521'7'Q3';%3221%M11&Fr7%211(6(Q0(Jr4%342@E1+4%64=<21%I2<1%Q03<91&Q4(R;z(9%33QC21%53QD@1%Q73M1I'A'B%211&Cr>&Q7r=r<r;%45321Q>Q:%7261(>&Q=&QC&Q:%129Q1%22:Q<%4221%63<QF1&Q?%12=O%@531=QJQF%;2E1%QO3E=1p0I1p0Q11p0QC1p0QJ1pT8R51pTDR71pTBR81pT:R91pU4R;1pT@R>1pT2R?1pT6RF1pT<RF1pTFRM1").
Proof. intros * Hf He Hd Hrd. rewrite (art_step_op_r _ _ _ _ _ _ _ _ _ _ r Hf He Hd), Hrd, alu_xor. reflexivity. Qed.
Lemma art_step_or_r : ltac2:(TCodec.tc2 tcn__ArtAtomics "S0'4'=%211&Q5y5'R=yR0%211%5241'5y8%611%311p061yQ0%:11%;1<%81:':%:14&?r:r8%3221(1r5%22;1%93841'2&@r6%211(3%?3521'7'Q3';%3221%M11&Fr7%211(6(Q0(Ir4%342@E1+4%64=<21%I2<1%Q03<91&Q4(R;z(9%33QC21%53QD@1%Q73M1I'A'B%211&Cr>&Q7r=r<r;%45321Q>Q:%7261(>&Q=&QB&Q:%129Q1%22:Q<%4221%63<QF1&Q?%12=O%@531=QJQF%;2E1%QO3E=1p0I1p0Q11p0QC1p0QJ1pT8R51pTDR71pTBR81pT:R91pU4R;1pT@R>1pT2R?1pT6RF1pT<RF1pTFRM1").
Proof. intros * Hf He Hd Hrd. rewrite (art_step_op_r _ _ _ _ _ _ _ _ _ _ r Hf He Hd), Hrd, alu_or. reflexivity. Qed.
Lemma art_step_branch_tk_r : ltac2:(TCodec.tc2 tcn__ArtAtomics "RO'4'=%211&Q5y5'R=yR0%211%5241'5y8%611%311p061yQ0%:11'Q2%<1=y=%>11%;1=':%=17&?r;r9%3221(1r6%22>1%93841'2&@r7%211(3%?3521'7'Q3';%3221%Q011&Fr8%211(6(Nr5r4%34@E21+4%64=<21%I2<1%Q03<91&Q6&Q:r=%221H%322N%53@21(8%Q83N21'A'B%211&Cr?&Q7r>r<%352>1Q>G%6251(>&Q9&R>%12QIQ?%32D1%:5918QEN%62?1%QJ3?81p0C1p0L1p0Q>1p0QE1pT8R01pT0R21pTDR51pTBR61pSLR81pU4R:1pT@R=1pT2R>1pT6RE1pT<RE1pTFRL1").
Proof.
intros segs regs pc mem rom w c rs1 rs2 imm r Hfetch Hecall Hdecode Hc.
step_pipeline_r Hfetch Hecall Hdecode.
unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
destruct (is_x0 rs1); destruct (is_x0 rs2); cbv beta iota; rewrite Hc; cbv beta iota; rewrite b_addsext; reflexivity.
Qed.
Lemma art_step_branch_ft_r : ltac2:(TCodec.tc2 tcn__ArtAtomics "RL'4'=%211&Q5y5'R=yR0%211%5241'5y8%611%311p061yQ0%:11'Q2%<1=y=%>11%;1=':%=17&?r;r9%3221(1r6%22>1%93841'2&@r7%211(3%?3521'7'Q3';%3221%Q011&Fr8%211(6(Nr5r4%34@E21+4%64=<21%I2<1%Q03<91&Q6&Q:r=%221H%322N%53@21%Q73M1I'A'B%211&Cr?&Q7r>r<%352=1Q=F%6251(>&Q?%12AG%85716QBK%42=1%QG3=61p0A1p0I1p0Q;1p0QB1pT8QM1pT0QO1pTDR21pTBR31pSLR51pU4R71pT@R:1pT2R;1pT6RB1pT<RB1pTFRI1").
Proof.
intros segs regs pc mem rom w c rs1 rs2 imm r Hfetch Hecall Hdecode Hc.
step_pipeline_r Hfetch Hecall Hdecode.
unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
destruct (is_x0 rs1); destruct (is_x0 rs2); cbv beta iota; rewrite Hc; cbv beta iota; rewrite ?b_npc4; reflexivity.
Qed.
Lemma art_step_lr_w : ltac2:(TCodec.tc2 tcn__ArtAtomics "SK'4'=%211&Q5y5'R=yR0%211%5241'5y8%611%311p061yQ0%:11'2%<1=%B17%:1<':%<16&?r>r<%3221(1r9%22=1%93841&@r:%211(3%>3B21'7'Q3';%3221%N11&Fr;%211(6(O(Lr8r7%453AE21+4%74>=21%I2=1%Q03=:1&Q4(R;z(9%33QE21%53QFO1%Q73Q;1J&Q:rA%221Q3%Q;3QH1A&QF&R?%12QLQ7%321B%Q@3O1=%QL1QC&Q<rDu4%342<Q:1%Q@2QHQ?%QG3621&<%11Q>%QJ3Q91<'A'B%211&CrF&Q7rErCrB%453A21QM%7261(>&Q=&QA%11QN%339R71&Q?%12IQ?%R72RJR9%>542<;1%92C1%R@3C;1p0G1p0K1p0Q31p0Q91p0Q>1p0QF1p0R91p0R?1pT8RJ1pU2S71pSJRM1pSDS91pTBS01pT:S11pT>S31pSFS41pU4S61pT@S91pT2S:1pT6SA1pT<SA1pTFSH1").
Proof.
intros segs regs pc mem rom w aq rl rd rs1 a bs v r Hf He Hd Hrd Ha Hal Hread Hv.
step_pipeline_r Hf He Hd.
unfold getr in Ha; rewrite ?bv_eqb0_is_x0 in Ha. rewrite Ha.
unfold amo_aligned. cbn [amo_bytes]. rewrite Hal, Z.eqb_refl.
cbv beta iota zeta delta
[RiscvSemantics.interp_eff_accesses RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ negb Sem.is_x0
Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv Sem.inval_resv Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom ms_fregs ms_fcsr mkstr].
rewrite ov_rdn, Hread; cbv beta iota.
rewrite (le_word_v _ _ Hv), b_lw_val, ?b_npc4.
unfold bv_eqb in Hrd. change (bv_unsigned (0%bv : bv 5)) with 0%Z in Hrd. rewrite Hrd. cbv beta iota.
reflexivity.
Qed.
#[local] Ltac amo_unfold :=
cbv beta iota zeta delta
[RiscvSemantics.interp_eff_accesses RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ negb Sem.is_x0
Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv Sem.inval_resv Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom ms_fregs ms_fcsr mkstr mkst].
Lemma art_step_lr_d : ltac2:(TCodec.tc2 tcn__ArtAtomics "SJ'4'=%211&Q5y5'R=yR0%211%5241'5y8%611%311p061yQ0%:11'2%<1=%B17%:1<':%<16&?r>r<%3221(1r9%22=1%93841&@r:%211(3%>3B21'7'Q3';%3221%N11&Fr;%211(6(O(Gr8r7%453AE21+4%74>=21%I2=1%Q03=:1&Q4(R;z(9%33QE21%53QFO1%Q73Q;1J&Q:rA%221Q3%Q;3QH1A&QF&R?%12QLQ7+8%4221%QA3Q01>%QM1QD&Q<rDu8%342=Q;1%QA2QIQ@%QH3621&<%11Q?%QK3Q:1='A'B%211&CrF&Q7rErCrB%453A21QN%7261(>&Q=%137R6QN&Q?%12GQ>%R62RIR8%<542:91%72A1%R?3A91p0E1p0I1p0Q11p0Q81p0Q=1p0QE1p0R81p0R>1pT8RI1pU2S61pSJRL1pSDS81pTBRO1pT:S01pT>S21pSFS31pU4S51pT@S81pT2S91pT6S@1pT<S@1pTFSG1").
Proof.
intros segs regs pc mem rom w aq rl rd rs1 a bs v r Hf He Hd Hrd Ha Hal Hread Hv.
assert (Hz : bv_extract 0 64 v = v).
{ apply bv_eq. rewrite bv_extract_unsigned, Z.shiftr_0_r. apply bv_wrap_bv_unsigned. }
step_pipeline_r Hf He Hd.
unfold getr in Ha; rewrite ?bv_eqb0_is_x0 in Ha. rewrite Ha.
unfold amo_aligned. cbn [amo_bytes]. rewrite Hal, Z.eqb_refl. amo_unfold.
rewrite ov_rdn, Hread; cbv beta iota.
rewrite (le_word_v _ _ Hv), Hz, ?b_npc4.
unfold bv_eqb in Hrd. change (bv_unsigned (0%bv : bv 5)) with 0%Z in Hrd. rewrite Hrd. cbv beta iota.
reflexivity.
Qed.
Lemma art_step_sc_w_ok : ltac2:(TCodec.tc2 tcn__ArtAtomics "SM'4'=%211&Q5y5'R=yR0%211%5241'5y8%611%311p061yQ0%:11'2%<1=':%:14&?r=r;%3221(1r8%22;1%93841&@r9%211(3%>3@21'7'Q3';%3221%L11&Fr:%211(6(Q1(Lr7r6r5%564BF321+4%84?>21%J2>1%Q13>;1&Q4(R;z(9%33QD21%53QEQ01%Q83Q:1K&Q:r@%221Q4%Q<3QG1A&QF&R?%12QKE%321B%QA3Q01=rB%:21Q8%QD3QO1J&DrDrAu4%4432Q>1(8%QK3QM21'A'B%211&CrE&Q7rC%QM2R>Q>%35>2B=1%6251(>&Q;vQN&Q=&R<%12RGQ7%33FR91&Q?%12<Q@&Q8&E%12IR6%33Q0QM1%<5;751L%>2G1%RE3G@1p0K1p0Q31p0Q71p0Q=1p0QB1p0QJ1p0R>1p0RD1pU2S91pSDS:1pTDS11pTBS21pT:S31pT>S51pSFS61pU4S81pT@S;1pT2S<1pT6SC1pT<SC1pTFSJ1").
Proof.
intros segs regs pc mem rom w aq rl rd rs1 rs2 a v Hf He Hd Hrd Ha Hal Hv Hok.
step_pipeline_r Hf He Hd.
unfold getr in Ha, Hv; rewrite ?bv_eqb0_is_x0 in Ha, Hv. rewrite Ha, Hv.
unfold amo_aligned. cbn [amo_bytes]. rewrite Hal, !Z.eqb_refl. amo_unfold.
rewrite Hok; cbv beta iota.
rewrite ?write_to_mem_wbytes, ?store_bytes_low32, ?b_npc4.
unfold bv_eqb in Hrd. change (bv_unsigned (0%bv : bv 5)) with 0%Z in Hrd. rewrite Hrd. cbv beta iota.
reflexivity.
Qed.
Lemma art_step_sc_d_ok : ltac2:(TCodec.tc2 tcn__ArtAtomics "SN'4'=%211&Q5y5'R=yR0%211%5241'5y8%611%311p061yQ0%:11'2%<1=':%:14&?r=r;%3221(1r8%22;1%93841&@r9%211(3%>3@21'7'Q3';%3221%L11&Fr:%211(6(Q1(Gr7r6r5%564BF321+4%84?>21%J2>1%Q13>;1&Q4(R;z(9%33QD21%53QEQ01%Q83Q:1K&Q:r@%221Q4%Q<3QG1A&QF&R?%12QKE+8%4221%QB3Q11>rB%;21Q9%QE3R01K&DrDrAu8%4432Q?1(8%QL3QN21'A'B%211&CrE&Q7rC%QN2R?Q?%35>2B=1%6251(>&Q;vQN&Q=&R<%12RHQ8%33FR:1&Q?%12<QA&Q8&E%12IR7%33Q0QN1%<5;751L%>2G1%RF3G@1p0K1p0Q31p0Q71p0Q>1p0QC1p0QK1p0R?1p0RE1pU2S:1pSDS;1pTDS21pTBS31pT:S41pT>S61pSFS71pU4S91pT@S<1pT2S=1pT6SD1pT<SD1pTFSK1").
Proof.
intros segs regs pc mem rom w aq rl rd rs1 rs2 a v Hf He Hd Hrd Ha Hal Hv Hok.
step_pipeline_r Hf He Hd.
unfold getr in Ha, Hv; rewrite ?bv_eqb0_is_x0 in Ha, Hv. rewrite Ha, Hv.
unfold amo_aligned. cbn [amo_bytes]. rewrite Hal, !Z.eqb_refl. amo_unfold.
rewrite Hok; cbv beta iota.
rewrite ?write_to_mem_wbytes, ?b_npc4.
unfold bv_eqb in Hrd. change (bv_unsigned (0%bv : bv 5)) with 0%Z in Hrd. rewrite Hrd. cbv beta iota.
reflexivity.
Qed.
Lemma art_step_amoadd_w_x0 : ltac2:(TCodec.tc2 tcn__ArtAtomics "T<'4'=%211&Q5y5'R=yR0%211%5241'5y8%611%311p061yQ0%:11'2%<1=%B17':%;15&?r>r<%3221(1r9%22<1%93841&@r:%211(3%>3A21'7'Q3';%3221%M11&Fr;%211(6(M(K(L(R;z(9%33Q=21r8r7%9787FJ321+4%<4CB21%N2B1%Q53B?1&Q:r@%221Q1%Q93QE19&QF&R?%12QI=%321;%Q>3M1B%QI1Q@&Q<rCu4%342<Q<1r6%Q?2QF1%QF3731&<%11H%QI3Q81=&QE%@2R8QD&QH+2+Q0%3221%6251rEr=%M221%R43R@1Q?&DrGrD%34216F(8%R:3R=21'A'B%211&CrH&Q;vQNrF%352=1B<%6251(>&Q?%125QE&Q8&E&Q>%12RGI%32Q:1%53LRJ1%>5=H71G%:2C1%S03C<1p0G1p0N1p0Q31p0Q;1p0Q?1p0QH1p0QN1p0R31p0RK1p0S11pSJS<1pT4SH1pU2SI1pSDSJ1pTDSA1pTBSB1pT>SD1pSFSE1pU4SG1pT@SJ1pT2SK1pT6T21pT<T21pTFT91").
Proof.
intros segs regs pc mem rom w aq rl rs1 rs2 a v old bs Hf He Hd Ha Hal Hread Hv Hold Hrs2 Hok.
step_pipeline Hf He Hd.
unfold getr in Ha, Hrs2; rewrite ?bv_eqb0_is_x0 in Ha, Hrs2. rewrite Ha, Hrs2.
unfold amo_aligned. cbn [amo_bytes]. rewrite Hal, Z.eqb_refl. amo_unfold.
rewrite ov_rdn, Hread; cbv beta iota.
rewrite (le_word_v _ _ Hv).
rewrite Hok; cbv beta iota.
replace (bv_unsigned (0%bv : bv 5) =? 0)%Z with true by reflexivity. cbv beta iota.
rewrite ?write_to_mem_wbytes, ?b_npc4.
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
End FPX.
