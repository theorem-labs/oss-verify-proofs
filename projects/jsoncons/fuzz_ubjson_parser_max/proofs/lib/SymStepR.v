(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec SeqExec.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__SymStepR () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.DecodeC."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymStepR."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymStepR.FPX_1."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1bool"; "1false"; "1list"; "1option"; "1pair"; "1prod"; "1true"; "2eq"; "3Z"; "4Segment"; "5MachineOk"; "5fetch_word"; "5is_ecall"; "5machine_result"]; ["5machine_state"; "5ms_svc_pending"; "5step"; "5store_ok"; "5word_to_le_bytes"; "6decode_any"; "7Branch"; "7Fence"; "7FenceI"; "7Store"; "7branch_cond"; "7instr"; "7msize"; "8bvmap"; "9branch_taken"; ":wbytes"]; [";btgt"; ";getr"; ";mkst"; ";v_addi"; "=mkstR"; "<mkstR"; "<msize_bytes"; "<resv_inval_w"; "0a"; "0b"; "0c"; "0d"; "0e"; "0fx"; "0imm"; "0mem"]; ["0pc"; "0regs"; "0rom"; "0rs1"; "0rs2"; "0rv"; "0segs"; ">bv"; ">bv_signed"; "0sz"; "0w"]]).
Section FPX_1. Context {fx : PropExec.FPState}.
Definition mkstR (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (rv : option word)
: machine_state :=
{| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := None; ms_resv := rv; ms_fcsr := fp_csr;
ms_mem := mem; ms_rom := rom |}.
Lemma mkstR_None : ltac2:(TCodec.tc2 tcn__SymStepR "M&My5'QGyR0%211%5241'5y8%611%311p061'9'@&Q4r4r3r2r1(0%11?%7565431&Q2vQ=%2519876%=3<41pS6?1pS0@1pS2G1pS4G1").
Proof. reflexivity. Qed.
Lemma mkstR_svc : ltac2:(TCodec.tc2 tcn__SymStepR "N&My5'QGyR0%211%5241'5y8%611%311p061%517'9&A&Q4r5r4r3r2r1%6554321%811(0%11C%<3=31pS<>1pS6@1pS0A1pS2H1pS4H1").
Proof. reflexivity. Qed.
Definition resv_inval_w (rv : option word) (a : word) : option word :=
match rv with
| Some r => if Z.eqb (bv_unsigned r) (bv_unsigned a) then None else rv
| None => None
end.
Definition load_result (sz : msize) (sx : bool) (bs : list byte) : word :=
match sz with
| SZ1 => if sx then sext 64 (bv_extract 0 8 (le_bytes_to_word bs))
else zext 64 (bv_extract 0 8 (le_bytes_to_word bs))
| SZ2 => if sx then sext 64 (bv_extract 0 16 (le_bytes_to_word bs))
else zext 64 (bv_extract 0 16 (le_bytes_to_word bs))
| SZ4 => if sx then sext 64 (bv_extract 0 32 (le_bytes_to_word bs))
else zext 64 (bv_extract 0 32 (le_bytes_to_word bs))
| SZ8 => bv_extract 0 64 (le_bytes_to_word bs)
end.
Definition eff_sx (sz : msize) (sx : bool) : bool :=
match sz with SZ8 => false | _ => sx end.
Definition msize_bytes (sz : msize) : nat :=
match sz with SZ1 => 1 | SZ2 => 2 | SZ4 => 4 | SZ8 => 8 end.
Definition amo_msize (wd : awidth) : msize := match wd with AW => SZ4 | AD => SZ8 end.
Definition amo_nbytes (wd : awidth) : nat := match wd with AW => 4%nat | AD => 8%nat end.
Definition amo_store_bytes (op : amoop) (wd : awidth) (bs : list byte) (src : word) : list byte :=
match wd with
| AW => Z_to_le_bytes 4 (bv_unsigned (amo_val op (bv_extract 0 32 (le_bytes_to_word bs)) (low32 src)))
| AD => Z_to_le_bytes 8 (bv_unsigned (amo_val op (bv_extract 0 64 (le_bytes_to_word bs)) src))
end.
End FPX_1.
Ltac stepR_pipeline Hfetch Hecall Hdecode :=
unfold mkstR;
step_pipeline Hfetch Hecall Hdecode;
cbv beta iota zeta delta [amo_aligned amo_bytes ms_fregs ms_fcsr];
rewrite ?bv_eqb0_is_x0.
Section FPX_2. Context {fx : PropExec.FPState}.
Lemma stepR_opimm_gen : forall segs regs pc mem rom rv w op rd rs (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (OpImm op rd rs imm, 4%Z) ->
RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
MachineOk (mkstR (if bv_eqb rd 0 then regs
else regupd regs rd (alu64 op (getr regs rs) (sext 64 imm)))
(v_addi pc 4) mem rom rv).
Proof.
intros segs regs pc mem rom rv w op rd rs imm Hfetch Hecall Hdecode.
stepR_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
destruct (is_x0 rs); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.
Lemma stepR_shiftimm_gen : forall segs regs pc mem rom rv w op rd rs (sh : bv 6),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (ShiftImm op rd rs sh, 4%Z) ->
RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
MachineOk (mkstR (if bv_eqb rd 0 then regs
else regupd regs rd (alu64 op (getr regs rs) (zext 64 sh)))
(v_addi pc 4) mem rom rv).
Proof.
intros segs regs pc mem rom rv w op rd rs sh Hfetch Hecall Hdecode.
stepR_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
destruct (is_x0 rs); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.
Lemma stepR_op_gen : forall segs regs pc mem rom rv w op rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op op rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
MachineOk (mkstR (if bv_eqb rd 0 then regs
else regupd regs rd (alu64 op (getr regs rs1) (getr regs rs2)))
(v_addi pc 4) mem rom rv).
Proof.
intros segs regs pc mem rom rv w op rd rs1 rs2 Hfetch Hecall Hdecode.
stepR_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
destruct (is_x0 rs1); cbv beta iota;
destruct (is_x0 rs2); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.
Lemma stepR_opimm32_gen : forall segs regs pc mem rom rv w rd rs (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (OpImm32 rd rs imm, 4%Z) ->
RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
MachineOk (mkstR (if bv_eqb rd 0 then regs
else regupd regs rd (sext 64 (alu32 ALU_ADD (low32 (getr regs rs)) (sext 32 imm))))
(v_addi pc 4) mem rom rv).
Proof.
intros segs regs pc mem rom rv w rd rs imm Hfetch Hecall Hdecode.
stepR_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
destruct (is_x0 rs); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.
Lemma stepR_shiftimm32_gen : forall segs regs pc mem rom rv w op rd rs (sh : bv 5),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (ShiftImm32 op rd rs sh, 4%Z) ->
RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
MachineOk (mkstR (if bv_eqb rd 0 then regs
else regupd regs rd (sext 64 (alu32 op (low32 (getr regs rs)) (zext 32 sh))))
(v_addi pc 4) mem rom rv).
Proof.
intros segs regs pc mem rom rv w op rd rs sh Hfetch Hecall Hdecode.
stepR_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
destruct (is_x0 rs); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.
Lemma stepR_op32_gen : forall segs regs pc mem rom rv w op rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op32 op rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
MachineOk (mkstR (if bv_eqb rd 0 then regs
else regupd regs rd (sext 64 (alu32 op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
(v_addi pc 4) mem rom rv).
Proof.
intros segs regs pc mem rom rv w op rd rs1 rs2 Hfetch Hecall Hdecode.
stepR_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
destruct (is_x0 rs1); cbv beta iota;
destruct (is_x0 rs2); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.
Lemma stepR_mul_gen : forall segs regs pc mem rom rv w op rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Mul op rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
MachineOk (mkstR (if bv_eqb rd 0 then regs
else regupd regs rd (mul_div op (getr regs rs1) (getr regs rs2)))
(v_addi pc 4) mem rom rv).
Proof.
intros segs regs pc mem rom rv w op rd rs1 rs2 Hfetch Hecall Hdecode.
stepR_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
destruct (is_x0 rs1); cbv beta iota;
destruct (is_x0 rs2); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.
Lemma stepR_mul32_gen : forall segs regs pc mem rom rv w op rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Mul32 op rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
MachineOk (mkstR (if bv_eqb rd 0 then regs
else regupd regs rd (sext 64 (mul_div op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
(v_addi pc 4) mem rom rv).
Proof.
intros segs regs pc mem rom rv w op rd rs1 rs2 Hfetch Hecall Hdecode.
stepR_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
destruct (is_x0 rs1); cbv beta iota;
destruct (is_x0 rs2); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.
Lemma stepR_lui : forall segs regs pc mem rom rv w rd (imm : bv 20),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Lui rd imm, 4%Z) ->
RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (v_lui (Z.shiftl (bv_signed imm) 12)))
(v_addi pc 4) mem rom rv).
Proof.
intros segs regs pc mem rom rv w rd imm Hfetch Hecall Hdecode.
stepR_pipeline Hfetch Hecall Hdecode. unfold regupd.
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4, ?b_lui; reflexivity.
Qed.
Lemma stepR_auipc : forall segs regs pc mem rom rv w rd (imm : bv 20),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Auipc rd imm, 4%Z) ->
RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (v_auipc pc (Z.shiftl (bv_signed imm) 12)))
(v_addi pc 4) mem rom rv).
Proof.
intros segs regs pc mem rom rv w rd imm Hfetch Hecall Hdecode.
stepR_pipeline Hfetch Hecall Hdecode. unfold regupd.
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4, ?b_auipc; reflexivity.
Qed.
Lemma stepR_jal_link : forall segs regs pc mem rom rv w rd (imm : bv 21),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Jal rd imm, 4%Z) ->
RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
(btgt pc (bv_signed imm)) mem rom rv).
Proof.
intros segs regs pc mem rom rv w rd imm Hfetch Hecall Hdecode.
stepR_pipeline Hfetch Hecall Hdecode. unfold regupd.
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4, ?b_addsext;
reflexivity.
Qed.
Lemma stepR_jalr : forall segs regs pc mem rom rv w rd rs1 (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Jalr rd rs1 imm, 4%Z) ->
RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
(v_jalr (getr regs rs1) (bv_signed imm)) mem rom rv).
Proof.
intros segs regs pc mem rom rv w rd rs1 imm Hfetch Hecall Hdecode.
stepR_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd, v_jalr.
destruct (is_x0 rs1); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4, ?b_jalr; reflexivity.
Qed.
Lemma stepR_branch_tk_gen : ltac2:(TCodec.tc2 tcn__SymStepR "S1'4';%211&My5'QGyR0%211%5241'5y8%611%311p061%517yQ0%;11'J%=1>y=%?11'9%=16&=r;r9%3221(1r5%22=1%93841'2&>r6%211(3%?3521'7'K':%3221%Q011&Er7%211(6(Fr4r3%34@E21+4%64=<21%I2<1%Q03<91&N&Q1r=%221H%322N%53@21(8%Q83N21'?'@%211&Br?&Q5vQ=r>r<r:%5643@2Q@1%8271(<&Q0&QH%12QJQA%32F1%<6;:19QG8%62A1%QL3A81p0E1p0N1p0Q@1p0QG1pRNR21pS:R51pS8R61pRFR81pSFR:1pS<R=1pS6R?1pS0R@1pS2RG1pS4RG1pS>RN1").
Proof.
intros segs regs pc mem rom rv w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
stepR_pipeline Hfetch Hecall Hdecode.
unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
destruct (is_x0 rs1); destruct (is_x0 rs2);
cbv beta iota; rewrite Hc; cbv beta iota;
rewrite b_addsext; reflexivity.
Qed.
Lemma stepR_branch_ft_gen : ltac2:(TCodec.tc2 tcn__SymStepR "RN'4';%211&My5'QGyR0%211%5241'5y8%611%311p061%517yQ0%;11'J%=1>y=%?11'9%=16&=r;r9%3221(1r5%22=1%93841'2&>r6%211(3%?3521'7'K':%3221%Q011&Er7%211(6(Fr4r3%34@E21+4%64=<21%I2<1%Q03<91&N&Q1r=%221H%322N%53@21%Q73M1I'?'@%211&Br?&Q5vQ=r>r<r:%5643?2Q?1%8271(<&Q3%12CI%:69817QD6%42?1%QI3?61p0C1p0K1p0Q=1p0QD1pRNQO1pS:R21pS8R31pRFR51pSFR71pS<R:1pS6R<1pS0R=1pS2RD1pS4RD1pS>RK1").
Proof.
intros segs regs pc mem rom rv w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
stepR_pipeline Hfetch Hecall Hdecode.
unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
destruct (is_x0 rs1); destruct (is_x0 rs2);
cbv beta iota; rewrite Hc; cbv beta iota;
rewrite b_npc4; reflexivity.
Qed.
Lemma stepR_fence : ltac2:(TCodec.tc2 tcn__SymStepR "RG'4';%211&My5'QGyR0%211%5241'5y8%611%311p061%517yQ0%;11y4%=11%>1?'9%<15&=r<r:%3221(1r6%22<1%93841'2&>r7%211(3%?3521'7'K':%3221%O11&Er8%211(6(Gr5r4r3%45AF321+4%74>=21%J2=1%Q13=:1'?'@%211&Br?&Q5vQ=r>r=r;%56432Q91Q8%8271(<&Q3%126B%:6981Q>6Q=%42?1%QC3?61p0C1p0Q61p0Q=1pRJQH1pRHQI1pRFQK1pRDQL1pRBQM1pSFR01pS<R31pS6R51pS0R61pS2R=1pS4R=1pS>RD1").
Proof.
intros segs regs pc mem rom rv w a b c d e Hfetch Hecall Hdecode.
stepR_pipeline Hfetch Hecall Hdecode. rewrite b_npc4. reflexivity.
Qed.
Lemma stepR_fencei : ltac2:(TCodec.tc2 tcn__SymStepR "RC'4';%211&My5'QGyR0%211%5241'5y8%611%311p061%517yQ0%;11%<1=y<%>11'9%<15&=r:r8%3221(1r4%22<1%93841'2&>r5%211(3%?3521'7'K':%3221%O11&Er6%211(6(Hr3%23?D1+4%54<;21%H2;1%O3;81'?'@%211&Br=&Q5vQ=r<r;r9%56432Q71Q6%8271(<&Q3%126B%:6981Q<6Q;%42?1%QA3?61p0C1p0Q41p0Q;1pRFQF1pRDQI1pRBQJ1pSFQL1pS<QO1pS6R11pS0R21pS2R91pS4R91pS>R@1").
Proof.
intros segs regs pc mem rom rv w a b c Hfetch Hecall Hdecode.
stepR_pipeline Hfetch Hecall Hdecode. rewrite b_npc4. reflexivity.
Qed.
Lemma stepR_load : forall segs regs pc mem rom rv w sz sx rd rs (imm : bv 12) bs,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load sz sx rd rs imm, 4%Z) ->
rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) (msize_bytes sz) = Some bs ->
RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (load_result sz sx bs))
(v_addi pc 4) mem rom rv).
Proof.
intros segs regs pc mem rom rv w sz sx rd rs imm bs Hfetch Hecall Hdecode Hread.
stepR_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
destruct sz; cbn [msize_bytes] in Hread; cbv beta iota delta [load_val];
rewrite ov_rdn, b_addsext, Hread; cbv beta iota; rewrite b_npc4;
destruct sx; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.
Lemma stepR_store : ltac2:(TCodec.tc2 tcn__SymStepR "S?'4';%211&My5'QGyR0%211%5241'5y8%611%311p061%517yQ0%;11'L%=1>y<%?11'9%=16&=r;r9%3221(1r5%22=1%93841'2&>r6%211(3%?3521'7'K':%3221%Q011&Er7%211(6(Ir4r3%34@E21+4%64=<21%I2<1%Q03<91&Cr>&Q3&Q1r=%221J&QH%12Q:>%6231&Q6%11E%;4:Q931(8%Q>3Q421'?'@%211&Br?&Q5vQ=r<r:%463FC2QE1%7261(<%H2FN&O%I2KQ7%G2R0QG%L221&Dr8%H11%O2Q1QG%4221%93?61&Q7%12@8%D6CQ6=3R51%?2I1%R:3IA1p0M1p0Q<1p0QN1p0R51pRNR@1pS:RC1pS8RD1pSDRF1pSFRH1pS<RK1pS6RM1pS0RN1pS2S51pS4S51pS>S<1").
Proof.
intros segs regs pc mem rom rv w sz rs1 rs2 imm Hfetch Hecall Hdecode Hok.
assert (Hsb : forall u : word,
Z_to_le_bytes 1%nat (bv_unsigned (bv_extract 0 8 u)) = word_to_le_bytes 1 u).
{ intro u. unfold word_to_le_bytes. cbn [Z_to_le_bytes].
f_equal. apply bv_eq.
rewrite !Z_to_bv_unsigned, bv_extract_unsigned, Z.shiftr_0_r.
apply bv_wrap_bv_wrap. lia. }
stepR_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
rewrite !b_addsext.
destruct sz; cbn [msize_bytes] in Hok |- *; cbv beta iota delta [store_val];
rewrite Hok; cbv beta iota;
rewrite write_to_mem_wbytes, ?Hsb, ?store_bytes_low16, ?store_bytes_low32, b_npc4;
(destruct rv as [r|]; cbv beta iota; [|reflexivity]);
unfold resv_inval_w;
match goal with |- context [Z.eqb ?x ?y] => destruct (Z.eqb x y); cbv beta iota; reflexivity end.
Qed.
Lemma stepR_lr : forall segs regs pc mem rom rv w wd aq rl rd rs bs,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Lr wd aq rl rd rs, 4%Z) ->
(bv_unsigned (getr regs rs) mod amo_bytes wd = 0)%Z ->
rdn segs mem (getr regs rs) (amo_nbytes wd) = Some bs ->
RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (load_result (amo_msize wd) true bs))
(v_addi pc 4) mem rom (Some (getr regs rs))).
Proof.
intros segs regs pc mem rom rv w wd aq rl rd rs bs Hfetch Hecall Hdecode Hal Hread.
stepR_pipeline Hfetch Hecall Hdecode.
change (if is_x0 rs then Z_to_bv 64 0 else reg_get regs rs) with (getr regs rs).
unfold amo_bytes in Hal.
destruct wd; rewrite Hal; change (negb (0 =? 0)%Z) with false; cbv beta iota;
cbn [amo_nbytes] in Hread; rewrite ov_rdn, Hread; cbv beta iota;
rewrite b_npc4; unfold regupd;
destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.
Lemma stepR_sc_ok : forall segs regs pc mem rom w wd aq rl rd rs1 rs2 r,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Sc wd aq rl rd rs1 rs2, 4%Z) ->
(bv_unsigned (getr regs rs1) mod amo_bytes wd = 0)%Z ->
r = getr regs rs1 ->
RiscvSemantics.store_ok segs mem (getr regs rs1) (amo_nbytes wd) = true ->
RiscvSemantics.step segs (mkstR regs pc mem rom (Some r)) =
MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 0)) (v_addi pc 4)
(wbytes mem (getr regs rs1) (word_to_le_bytes (amo_nbytes wd) (getr regs rs2))) rom None).
Proof.
intros segs regs pc mem rom w wd aq rl rd rs1 rs2 r Hfetch Hecall Hdecode Hal Hr Hok.
stepR_pipeline Hfetch Hecall Hdecode.
change (if is_x0 rs1 then Z_to_bv 64 0 else reg_get regs rs1) with (getr regs rs1).
change (if is_x0 rs2 then Z_to_bv 64 0 else reg_get regs rs2) with (getr regs rs2).
unfold amo_bytes in Hal.
destruct wd; rewrite Hal; change (negb (0 =? 0)%Z) with false; cbv beta iota;
subst r; rewrite Z.eqb_refl; cbv beta iota;
cbn [amo_nbytes] in Hok |- *; rewrite Hok; cbv beta iota;
rewrite write_to_mem_wbytes, ?store_bytes_low32, b_npc4;
unfold regupd, word_to_le_bytes;
destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.
Lemma stepR_amo : forall segs regs pc mem rom rv w op wd aq rl rd rs1 rs2 bs,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Amo op wd aq rl rd rs1 rs2, 4%Z) ->
(bv_unsigned (getr regs rs1) mod amo_bytes wd = 0)%Z ->
rdn segs mem (getr regs rs1) (amo_nbytes wd) = Some bs ->
RiscvSemantics.store_ok segs mem (getr regs rs1) (amo_nbytes wd) = true ->
RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (load_result (amo_msize wd) true bs))
(v_addi pc 4)
(wbytes mem (getr regs rs1) (amo_store_bytes op wd bs (getr regs rs2)))
rom (resv_inval_w rv (getr regs rs1))).
Proof.
intros segs regs pc mem rom rv w op wd aq rl rd rs1 rs2 bs Hfetch Hecall Hdecode Hal Hread Hok.
stepR_pipeline Hfetch Hecall Hdecode.
change (if is_x0 rs1 then Z_to_bv 64 0 else reg_get regs rs1) with (getr regs rs1).
change (if is_x0 rs2 then Z_to_bv 64 0 else reg_get regs rs2) with (getr regs rs2).
unfold amo_bytes in Hal.
destruct wd; rewrite Hal; change (negb (0 =? 0)%Z) with false; cbv beta iota;
cbn [amo_nbytes] in Hread, Hok |- *; rewrite ov_rdn, Hread; cbv beta iota;
rewrite Hok; cbv beta iota;
rewrite write_to_mem_wbytes, b_npc4; unfold regupd, amo_store_bytes;
(destruct rv as [r|]; cbv beta iota);
unfold resv_inval_w;
try match goal with |- context [Z.eqb (bv_unsigned r) ?y] =>
destruct (Z.eqb (bv_unsigned r) y); cbv beta iota end;
destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.
End FPX_2.
